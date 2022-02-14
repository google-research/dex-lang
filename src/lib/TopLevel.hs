-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module TopLevel (
  EvalConfig (..), Topper, runTopperM,
  evalSourceBlock, evalSourceBlockRepl,
  evalFile, evalSourceText, initTopState, TopStateEx (..),
  evalSourceBlockIO, loadCache, storeCache, clearCache) where

import Data.Functor
import Control.Exception (throwIO, catch)
import Control.Monad.Writer.Strict  hiding (pass)
import Control.Monad.State.Strict
import Control.Monad.Reader
import qualified Data.ByteString as BS
import Data.Text.Prettyprint.Doc
import Data.Store (Store (..), encode, decode)
import Data.List (partition)
import qualified Data.Map.Strict as M
import qualified Data.Set        as S
import GHC.Generics (Generic (..))
import System.FilePath
import System.Directory
import System.IO (stderr, hPutStrLn)
import System.IO.Error (isDoesNotExistError)

import Paths_dex  (getDataFileName)

import Err
import MTL1
import Logging
import LLVMExec
import PPrint (pprintCanonicalized)
import Util (measureSeconds, File (..), readFileWithHash)
import Serialize (HasPtrs (..), pprintVal, getDexString, takePtrSnapshot, restorePtrSnapshot)

import Name
import Parser
import Syntax
import Builder
import Type
import SourceRename
import Inference
import Simplify
import Imp
import JIT

-- === top-level monad ===

data EvalConfig = EvalConfig
  { backendName :: Backend
  , libPath     :: Maybe FilePath
  , preludeFile :: Maybe FilePath
  , logFile     :: Maybe FilePath }

class Monad m => ConfigReader m where
  getConfig :: m EvalConfig

data PassCtx = PassCtx
  { requiresBench :: Bool }

initPassCtx :: PassCtx
initPassCtx = PassCtx False

class Monad m => PassCtxReader m where
  getPassCtx :: m PassCtx
  withPassCtx :: PassCtx -> m a -> m a

type TopLogger m = (MonadIO m, MonadLogger [Output] m)

class ( forall n. Fallible (m n)
      , forall n. MonadLogger [Output] (m n)
      , forall n. Catchable (m n)
      , forall n. ConfigReader (m n)
      , forall n. PassCtxReader (m n)
      , forall n. MonadIO (m n)  -- TODO: something more restricted here
      , TopBuilder m )
      => Topper m

newtype TopperM (n::S) a = TopperM
  { runTopperM' :: TopBuilderT (ReaderT (PassCtx, EvalConfig) (LoggerT [Output] IO)) n a }
    deriving ( Functor, Applicative, Monad, MonadIO, MonadFail
             , Fallible, EnvReader, ScopeReader, Catchable)

-- Hides the `n` parameter as an existential
data TopStateEx where
  TopStateEx :: Distinct n => Env n -> TopStateEx

runTopperM :: EvalConfig -> TopStateEx
           -> (forall n. Mut n => TopperM n a)
           -> IO (a, TopStateEx)
runTopperM opts (TopStateEx env) cont = do
  let maybeLogFile = logFile opts
  (Abs frag (LiftE result), _) <- runLogger maybeLogFile \l -> runLoggerT l $
    flip runReaderT (initPassCtx, opts) $
      runTopBuilderT env $ runTopperM' do
        localTopBuilder $ LiftE <$> cont
  return (result, extendTopEnv env frag)

extendTopEnv :: Distinct n => Env n -> TopEnvFrag n l -> TopStateEx
extendTopEnv env frag = do
  refreshAbsPure (toScope env) (Abs frag UnitE) \_ frag' UnitE ->
    TopStateEx $ extendOutMap env frag'

initTopState :: TopStateEx
initTopState = TopStateEx emptyOutMap

-- ======

evalSourceBlockIO :: EvalConfig -> TopStateEx -> SourceBlock -> IO (Result, TopStateEx)
evalSourceBlockIO opts env block = runTopperM opts env $ evalSourceBlockRepl block

-- Used for the top-level source file (rather than imported modules)
evalSourceText :: (Topper m, Mut n) => String -> m n [(SourceBlock, Result)]
evalSourceText source = do
  let (UModule mname deps sourceBlocks) = parseUModule Main source
  mapM_ ensureModuleLoaded deps
  results <- mapM (evalSourceBlock mname) sourceBlocks
  return $ zip sourceBlocks results

catchLogsAndErrs :: (Topper m, Mut n) => m n a -> m n (Except a, [Output])
catchLogsAndErrs m = do
  maybeLogFile <- logFile <$> getConfig
  runLogger maybeLogFile \l -> withLogger l $
    catchErrExcept m

-- Module imports have to be handled differently in the repl because we don't
-- know ahead of time which modules will be needed.
evalSourceBlockRepl :: (Topper m, Mut n) => SourceBlock -> m n Result
evalSourceBlockRepl block = do
  case block of
    SourceBlock _ _ _ _ (ImportModule name) -> do
      -- TODO: clear source map and synth candidates before calling this
      ensureModuleLoaded name
    _ -> return ()
  evalSourceBlock Main block

-- XXX: This ensures that a module and its transitive dependencies are loaded,
-- (which will require evaluating them if they're not in the cache) but it
-- doesn't bring the names and instances into scope. The modules are "loaded"
-- but not yet "imported".
ensureModuleLoaded :: (Topper m, Mut n) => ModuleSourceName -> m n ()
ensureModuleLoaded moduleSourceName = do
  -- TODO: think about where import errors should be handled
  depsRequired <- findDepsTransitively moduleSourceName
  forM_ depsRequired \md -> do
    evaluated <- evalPartiallyParsedUModuleCached md
    bindModule (umppName md) evaluated

evalSourceBlock :: (Topper m, Mut n)
                => ModuleSourceName -> SourceBlock -> m n Result
evalSourceBlock mname block = do
  result <- withCompileTime do
     (maybeErr, logs) <- catchLogsAndErrs $
       withPassCtx (PassCtx $ blockRequiresBench block) $
         evalSourceBlock' mname block
     return $ Result logs maybeErr
  case resultErrs result of
    Failure _ -> case sbContents block of
      EvalUDecl decl -> emitSourceMap $ uDeclErrSourceMap mname decl
      _ -> return ()
    _ -> return ()
  return $ filterLogs block $ addResultCtx block result

evalSourceBlock' :: (Topper m, Mut n) => ModuleSourceName -> SourceBlock -> m n ()
evalSourceBlock' mname block = case sbContents block of
  EvalUDecl decl -> execUDecl mname decl
  Command cmd expr -> case cmd of
    EvalExpr fmt -> do
      val <- evalUExpr expr
      case fmt of
        Printed -> do
          s <- pprintVal val
          logTop $ TextOut s
        RenderHtml -> do
          -- TODO: check types before we get here
          s <- getDexString val
          logTop $ HtmlOut s
    ExportFun _ -> error "not implemented"
    --   f <- evalUModuleVal v m
    --   void $ traverseLiterals f \val -> case val of
    --     PtrLit _ _ -> throw CompilerErr $
    --       "Can't export functions with captured pointers (not implemented)."
    --     _ -> return $ Con $ Lit val
    --   logTop $ ExportedFun name f
    GetType -> do  -- TODO: don't actually evaluate it
      val <- evalUExpr expr
      ty <- getType val
      logTop $ TextOut $ pprintCanonicalized ty
  DeclareForeign fname (UAnnBinder b uty) -> do
    ty <- evalUType uty
    asFFIFunType ty >>= \case
      Nothing -> throw TypeErr
        "FFI functions must be n-ary first order functions with the IO effect"
      Just (impFunTy, naryPiTy) -> do
        -- TODO: query linking stuff and check the function is actually available
        let hint = getNameHint b
        vImp  <- emitImpFunBinding hint $ FFIFunction impFunTy fname
        vCore <- emitBinding hint (AtomNameBinding $ FFIFunBound naryPiTy vImp)
        UBindSource sourceName <- return b
        emitSourceMap $ SourceMap $
          M.singleton sourceName [ModuleVar mname (Just $ UAtomVar vCore)]
  GetNameType v -> do
    ty <- sourceNameType v
    logTop $ TextOut $ pprintCanonicalized ty
  ImportModule moduleName -> importModule moduleName
  QueryEnv query -> void $ runEnvQuery query $> UnitE
  ProseBlock _ -> return ()
  CommentLine  -> return ()
  EmptyLines   -> return ()
  UnParseable _ s -> throw ParseErr s

runEnvQuery :: Topper m => EnvQuery -> m n ()
runEnvQuery query = do
  env <- unsafeGetEnv
  case query of
    DumpSubst -> logTop $ TextOut $ pprint $ env
    InternalNameInfo name ->
      case lookupSubstFragRaw (fromRecSubst $ envDefs $ topEnv env) name of
        Nothing -> throw UnboundVarErr $ pprint name
        Just (WithColor binding) ->
          logTop $ TextOut $ pprint binding
    SourceNameInfo name -> do
      lookupSourceMap name >>= \case
        Nothing -> throw UnboundVarErr $ pprint name
        Just uvar -> do
          logTop $ TextOut $ pprint uvar
          info <- case uvar of
            UAtomVar    v' -> pprint <$> lookupEnv v'
            UTyConVar   v' -> pprint <$> lookupEnv v'
            UDataConVar v' -> pprint <$> lookupEnv v'
            UClassVar   v' -> pprint <$> lookupEnv v'
            UMethodVar  v' -> pprint <$> lookupEnv v'
          logTop $ TextOut $ "Binding:\n" ++ info

blockRequiresBench :: SourceBlock -> Bool
blockRequiresBench block = case sbLogLevel block of
  PrintBench _ -> True
  _            -> False

filterLogs :: SourceBlock -> Result -> Result
filterLogs block (Result outs err) = let
  (logOuts, requiredOuts) = partition isLogInfo outs
  outs' = requiredOuts ++ processLogs (sbLogLevel block) logOuts
  in Result outs' err

-- returns a toposorted list of the module's transitive dependencies (including
-- the module itself) excluding those provided in the set of already known
-- modules.
findDepsTransitively
  :: forall m n. (Topper m, Mut n)
  => ModuleSourceName -> m n [UModulePartialParse]
findDepsTransitively initialModuleName = do
  alreadyLoaded <- M.keysSet . fromLoadedModules <$> withEnv (envLoadedModules . topEnv)
  flip evalStateT alreadyLoaded $ execWriterT $ go initialModuleName
  where
    go :: ModuleSourceName -> WriterT [UModulePartialParse]
                                (StateT (S.Set ModuleSourceName) (m n)) ()
    go name = do
      alreadyVisited <- S.member name <$> get
      unless alreadyVisited do
        modify $ S.insert name
        config <- lift $ lift $ getConfig
        source <- loadModuleSource config name
        deps <- lift $ lift $ parseUModuleDepsCached name source
        mapM_ go deps
        tell [UModulePartialParse name deps source]

-- What would it look like to abstract away pattern used here and in
-- `evalPartiallyParsedUModuleCached`? We still want case-by-case control over
-- keys, eviction policy, etc. Maybe some a type class for caches that implement
-- query/extend, with `extend` being where the eviction happens?
parseUModuleDepsCached :: (Mut n, TopBuilder m)
                       => ModuleSourceName -> File -> m n [ModuleSourceName]
parseUModuleDepsCached Main file = return $ parseUModuleDeps Main file
parseUModuleDepsCached name file = do
  cache <- parsedDeps <$> getCache
  let req = fHash file
  case M.lookup name cache of
    Just (cachedReq, result) | cachedReq == req -> return result
    _ -> do
      let result = parseUModuleDeps name file
      extendCache $ mempty { parsedDeps = M.singleton name (req, result) }
      return result

evalPartiallyParsedUModuleCached
  :: (Topper m, Mut n)
  => UModulePartialParse -> m n (ModuleName n)
evalPartiallyParsedUModuleCached md@(UModulePartialParse name deps source) = do
  case name of
    Main -> evalPartiallyParsedUModule md  -- Don't cache main
    _ -> do
      LiftE cache <- withEnv $ LiftE . moduleEvaluations . envCache . topEnv
      -- TODO: we know that these are sufficient to determine the result of
      -- module evaluation, but maybe we should actually restrict the
      -- environment we pass to `evalUModule` so that it can't possibly depend
      -- on anything else.
      directDeps <- forM deps \dep -> do
        lookupLoadedModule dep >>= \case
          Just depVal -> return depVal
          Nothing -> throw CompilerErr $ pprint dep ++ " isn't loaded"
      let req = (fHash source, directDeps)
      case M.lookup name cache of
        Just (cachedReq, result) | cachedReq == req -> return result
        _ -> do
          liftIO $ hPutStrLn stderr $ "Compiling " ++ pprint name
          result <- evalPartiallyParsedUModule md
          extendCache $ mempty { moduleEvaluations = M.singleton name (req, result) }
          return result

-- Assumes all module dependencies have been loaded already
evalPartiallyParsedUModule
  :: (Topper m, Mut n)
  => UModulePartialParse -> m n (ModuleName n)
evalPartiallyParsedUModule partiallyParsed = do
  let name = umppName partiallyParsed
  let uModule = finishUModuleParse partiallyParsed
  evaluated <- evalUModule uModule
  emitBinding (getNameHint name) $ ModuleBinding evaluated

-- Assumes all module dependencies have been loaded already
evalUModule :: (Topper m  ,Mut n) => UModule -> m n (Module n)
evalUModule (UModule name _ blocks) = do
  Abs topFrag UnitE <- localTopBuilder $ mapM_ (evalSourceBlock' name) blocks >> return UnitE
  TopEnvFrag envFrag (PartialTopEnvFrag cache loadedModules moduleEnv) <- return topFrag
  ModuleEnv (ImportStatus directDeps transDeps) sm scs objs _ <- return moduleEnv
  let fragToReEmit = TopEnvFrag envFrag $ PartialTopEnvFrag cache loadedModules mempty
  let evaluatedModule = Module name directDeps transDeps sm scs objs
  emitEnv $ Abs fragToReEmit evaluatedModule

importModule :: (Mut n, TopBuilder m, Fallible1 m) => ModuleSourceName -> m n ()
importModule name = do
  lookupLoadedModule name >>= \case
    Nothing -> throw ModuleImportErr $ "Couldn't import " ++ pprint name
    Just name' -> do
      Module _ _ transImports' _ _ _ <- lookupModule name'
      let importStatus = ImportStatus (S.singleton name') (S.singleton name' <> transImports')
      emitLocalModuleEnv $ mempty { envImportStatus = importStatus }

evalFile :: (Topper m, Mut n) => FilePath -> m n [(SourceBlock, Result)]
evalFile fname = evalSourceText =<< (liftIO $ readFile fname)

processLogs :: LogLevel -> [Output] -> [Output]
processLogs logLevel logs = case logLevel of
  LogAll -> logs
  LogNothing -> []
  LogPasses passes -> flip filter logs \case
                        PassInfo pass _ | pass `elem` passes -> True
                                        | otherwise          -> False
                        _ -> False
  PrintEvalTime -> [BenchResult "" compileTime runTime benchStats]
    where (compileTime, runTime, benchStats) = timesFromLogs logs
  PrintBench benchName -> [BenchResult benchName compileTime runTime benchStats]
    where (compileTime, runTime, benchStats) = timesFromLogs logs

timesFromLogs :: [Output] -> (Double, Double, Maybe BenchStats)
timesFromLogs logs = (totalTime - totalEvalTime, singleEvalTime, benchStats)
  where
    (totalEvalTime, singleEvalTime, benchStats) =
      case [(t, stats) | EvalTime t stats <- logs] of
        []           -> (0.0  , 0.0, Nothing)
        [(t, stats)] -> (total, t  , stats)
          where total = maybe t snd stats
        _            -> error "Expect at most one result"
    totalTime = case [tTotal | TotalTime tTotal <- logs] of
        []  -> 0.0
        [t] -> t
        _   -> error "Expect at most one result"

isLogInfo :: Output -> Bool
isLogInfo out = case out of
  PassInfo _ _ -> True
  MiscLog  _   -> True
  EvalTime _ _ -> True
  TotalTime _  -> True
  _ -> False

evalUType :: (Topper m, Mut n) => UType VoidS -> m n (Type n)
evalUType ty = do
  logTop $ PassInfo Parse $ pprint ty
  renamed <- logPass RenamePass $ renameSourceNamesUExpr ty
  checkPass TypePass $ checkTopUType renamed

evalUExpr :: (Topper m, Mut n) => UExpr VoidS -> m n (Atom n)
evalUExpr expr = do
  logTop $ PassInfo Parse $ pprint expr
  renamed <- logPass RenamePass $ renameSourceNamesUExpr expr
  typed <- checkPass TypePass $ inferTopUExpr renamed
  evalBlock typed

evalBlock :: (Topper m, Mut n) => Block n -> m n (Atom n)
evalBlock typed = do
  synthed <- checkPass SynthPass $ synthTopBlock typed
  SimplifiedBlock simp recon <- checkPass SimpPass $ simplifyTopBlock synthed
  result <- evalBackend simp
  applyRecon recon result

execUDecl :: (Topper m, Mut n) => ModuleSourceName -> UDecl VoidS VoidS -> m n ()
execUDecl mname decl = do
  logTop $ PassInfo Parse $ pprint decl
  Abs renamedDecl sourceMap <- logPass RenamePass $ renameSourceNamesTopUDecl mname decl
  inferenceResult <- checkPass TypePass $ inferTopUDecl renamedDecl sourceMap
  case inferenceResult of
    UDeclResultWorkRemaining block declAbs -> do
      result <- evalBlock block
      result' <- case declAbs of
        Abs (ULet NoInlineLet (UPatAnn p _) _) _ ->
          compileTopLevelFun (getNameHint p) result
        _ -> return result
      emitSourceMap =<< applyUDeclAbs declAbs result'
    UDeclResultDone sourceMap' -> emitSourceMap sourceMap'

compileTopLevelFun :: (Topper m, Mut n) => NameHint -> Atom n -> m n (Atom n)
compileTopLevelFun hint f = do
  ty <- getType f
  naryPi <- asFirstOrderFunction ty >>= \case
    Nothing -> throw TypeErr "@noinline functions must be first-order"
    Just naryPi -> return naryPi
  fSimp <- simplifyTopFunction naryPi f
  fImp <- toImpStandaloneFunction fSimp
  fSimpName <- emitBinding hint $ AtomNameBinding $ SimpLamBound naryPi fSimp
  fImpName <- emitImpFunBinding hint fImp
  extendImpCache fSimpName fImpName
  -- TODO: this is a hack! We need a better story for C/LLVM names.
  let cFunName = pprint fImpName
  fObj <- toCFunction cFunName fImp
  extendObjCache fImpName fObj
  return $ Var fSimpName

toCFunction :: (Topper m, Mut n) => SourceName -> ImpFunction n -> m n (CFun n)
toCFunction fname f = do
  (deps, m) <- impToLLVM fname f
  objFile <- liftIO $ exportObjectFileVal deps m fname
  objFileName <- emitObjFile (getNameHint fname) objFile
  return $ CFun fname objFileName

-- TODO: there's no guarantee this name isn't already taken. Need a better story
-- for C/LLVM function names
mainFuncName :: SourceName
mainFuncName = "entryFun"

evalLLVM :: (Topper m, Mut n) => Block n -> m n (Atom n)
evalLLVM block = do
  backend <- backendName <$> getConfig
  bench   <- requiresBench <$> getPassCtx
  (blockAbs, ptrVals) <- abstractPtrLiterals block
  let (cc, needsSync) = case backend of LLVMCUDA -> (EntryFun CUDARequired   , True )
                                        _        -> (EntryFun CUDANotRequired, False)
  ImpFunctionWithRecon impFun reconAtom <- checkPass ImpPass $
                                             toImpFunction backend cc blockAbs
  (_, llvmAST) <- impToLLVM mainFuncName impFun
  let IFunType _ _ resultTypes = impFunType impFun
  let llvmEvaluate = if bench then compileAndBench needsSync else compileAndEval
  logger  <- getLogger
  objFileNames <- getAllRequiredObjectFiles
  objFiles <- forM objFileNames  \objFileName -> do
    ObjectFileBinding objFile <- lookupEnv objFileName
    return objFile
  resultVals <- liftIO $ llvmEvaluate logger objFiles
                  llvmAST mainFuncName ptrVals resultTypes
  resultValsNoPtrs <- mapM litValToPointerlessAtom resultVals
  applyNaryAbs reconAtom $ map SubstVal resultValsNoPtrs

evalBackend :: (Topper m, Mut n) => Block n -> m n (Atom n)
evalBackend (AtomicBlock result) = return result
evalBackend block = do
  backend <- backendName <$> getConfig
  let eval = case backend of
               MLIR        -> error "TODO"
               LLVM        -> evalLLVM
               LLVMMC      -> evalLLVM
               LLVMCUDA    -> evalLLVM
               Interpreter -> error "TODO"
  eval block

withCompileTime :: MonadIO m => m Result -> m Result
withCompileTime m = do
  (Result outs err, t) <- measureSeconds m
  return $ Result (outs ++ [TotalTime t]) err

checkPass :: (Topper m, Pretty (e n), CheckableE e)
          => PassName -> m n (e n) -> m n (e n)
checkPass name cont = do
  result <- logPass name do
    result <- cont
    return result
  logTop $ MiscLog $ "Running checks"
  checkTypesM result
  logTop $ MiscLog $ "Checks passed"
  return result

addResultCtx :: SourceBlock -> Result -> Result
addResultCtx block (Result outs errs) =
  Result outs (addSrcTextContext (sbOffset block) (sbText block) errs)

logTop :: TopLogger m => Output -> m ()
logTop x = logIO [x]

logPass :: Topper m => Pretty a => PassName -> m n a -> m n a
logPass passName cont = do
  logTop $ PassInfo passName $ "=== " <> pprint passName <> " ==="
  logTop $ MiscLog $ "Starting "++ pprint passName
  result <- cont
  logTop $ PassInfo passName $ "=== Result ===\n" <> pprint result
  return result

loadModuleSource :: MonadIO m => EvalConfig -> ModuleSourceName -> m File
loadModuleSource config moduleName = do
  fullPath <- case moduleName of
    OrdinaryModule moduleName' -> findFullPath $ moduleName' ++ ".dx"
    Prelude -> case preludeFile config of
      Nothing -> findFullPath "prelude.dx"
      Just path -> return path
    Main -> error "shouldn't be trying to load the source for main"
  readFileWithHash fullPath
  where
    findFullPath :: MonadIO m => FilePath -> m FilePath
    findFullPath fname = case libPath config of
      Nothing -> liftIO $ getDataFileName $ "lib/" ++ fname
      Just path -> return $ path </> fname

-- === saving cache to disk ===

-- None of this is safe in the presence of multiple processes trying to interact
-- with the cache. But we plan to fix that by using an actual database.

loadCache :: MonadIO m => m TopStateEx
loadCache = liftIO do
  cachePath <- getCachePath
  cacheExists <- doesFileExist cachePath
  if cacheExists
    then do
      decoded <- decode <$> BS.readFile cachePath
      case decoded of
        Right result -> restorePtrSnapshots result
        _            -> removeFile cachePath >> return initTopState
    else return initTopState

storeCache :: MonadIO m => TopStateEx -> m ()
storeCache env = liftIO do
  cachePath <- getCachePath
  createDirectoryIfMissing True =<< getCacheDir
  envToStore <- snapshotPtrs $ stripEnvForSerialization env
  BS.writeFile cachePath $ encode envToStore

getCacheDir :: MonadIO m => m FilePath
getCacheDir = liftIO $ getXdgDirectory XdgCache "dex"

getCachePath :: MonadIO m => m FilePath
getCachePath = liftIO do
  cacheDir <- getCacheDir
  return $ cacheDir </> "dex.cache"

clearCache :: MonadIO m => m ()
clearCache = liftIO do
  cachePath <- getCachePath
  removeFile cachePath `catch` \e -> unless (isDoesNotExistError e) (throwIO e)

-- TODO: real garbage collection (maybe leave it till after we have a
-- database-backed cache and we can do it incrementally)
stripEnvForSerialization :: TopStateEx -> TopStateEx
stripEnvForSerialization (TopStateEx (Env (TopEnv _ (RecSubst defs) cache _) _)) =
  collectGarbage (RecSubstFrag defs) cache \d@(RecSubstFrag defs') cache' -> do
    let scope = Scope $ toScopeFrag d
    TopStateEx $ Env (TopEnv scope (RecSubst defs') cache' mempty) emptyModuleEnv

snapshotPtrs :: MonadIO m => TopStateEx -> m TopStateEx
snapshotPtrs s = traverseBindingsTopStateEx s \case
  PtrBinding (PtrLitVal ty p) ->
    liftIO $ PtrBinding . PtrSnapshot ty <$> takePtrSnapshot ty p
  PtrBinding (PtrSnapshot _ _) -> error "shouldn't have snapshots"
  b -> return b

restorePtrSnapshots :: MonadIO m => TopStateEx -> m TopStateEx
restorePtrSnapshots s = traverseBindingsTopStateEx s \case
  PtrBinding (PtrSnapshot ty snapshot) ->
    liftIO $ PtrBinding . PtrLitVal ty <$> restorePtrSnapshot snapshot
  PtrBinding (PtrLitVal _ _) -> error "shouldn't have lit vals"
  b -> return b

traverseBindingsTopStateEx
  :: Monad m => TopStateEx -> (forall c n. Binding c n -> m (Binding c n)) -> m TopStateEx
traverseBindingsTopStateEx (TopStateEx (Env tenv menv)) f = do
  defs <- traverseSubstFrag f $ fromRecSubst $ envDefs tenv
  return $ TopStateEx (Env (tenv {envDefs = RecSubst defs}) menv)

-- -- === instances ===

instance PassCtxReader (TopperM n) where
  getPassCtx = TopperM $ asks fst
  withPassCtx ctx cont = TopperM $
    liftTopBuilderTWith (local \(_, config) -> (ctx, config)) $
      runTopperM' cont

instance ConfigReader (TopperM n) where
  getConfig = TopperM $ asks snd

instance (Monad1 m, ConfigReader (m n)) => ConfigReader (StateT1 s m n) where
  getConfig = lift11 getConfig

instance Topper TopperM

instance TopBuilder TopperM where
  -- Log bindings as they are emitted
  emitBinding hint binding = do
    name <- TopperM $ emitBinding hint binding
    logTop $ MiscLog $ "=== Top name ===\n" ++ pprint name ++ " =\n"
                      ++ pprint binding ++ "\n===\n"
    return name

  emitEnv env = TopperM $ emitEnv env
  emitNamelessEnv env = TopperM $ emitNamelessEnv env
  localTopBuilder cont = TopperM $ localTopBuilder $ runTopperM' cont

instance Store TopStateEx

instance MonadLogger [Output] (TopperM n) where
  getLogger = TopperM $ lift1 $ lift $ getLogger
  withLogger l cont =
    TopperM $ liftTopBuilderTWith (withLogger l) (runTopperM' cont)

instance Generic TopStateEx where
  type Rep TopStateEx = Rep (Env UnsafeS)
  from (TopStateEx topState) = from (unsafeCoerceE topState :: Env UnsafeS)
  to rep = do
    case fabricateDistinctEvidence :: DistinctEvidence UnsafeS of
      Distinct -> TopStateEx (to rep :: Env UnsafeS)

instance HasPtrs TopStateEx where
  -- TODO: rather than implementing HasPtrs for safer names, let's just switch
  --       to using names for pointers.
  traversePtrs _ s = pure s
