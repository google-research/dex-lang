-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module TopLevel (
  EvalConfig (..), Topper, TopperM, runTopperM,
  evalSourceBlock, evalSourceBlockRepl, OptLevel (..),
  evalSourceText, TopStateEx (..), LibPath (..),
  evalSourceBlockIO, initTopState, loadCache, storeCache, clearCache,
  ensureModuleLoaded, importModule, printCodegen,
  loadObject, toCFunction, packageLLVMCallable,
  simpOptimizations, loweredOptimizations, compileTopLevelFun) where

import Data.Functor
import Data.Maybe (catMaybes)
import Control.Exception (throwIO, catch)
import Control.Monad.Writer.Strict  hiding (pass)
import Control.Monad.State.Strict
import Control.Monad.Reader
import qualified Data.ByteString as BS
import Data.Text (Text)
import Data.Text.Prettyprint.Doc
import Data.Store (encode, decode)
import Data.String (fromString)
import Data.List (partition)
import qualified Data.Map.Strict as M
import qualified Data.Set        as S
import Foreign.Ptr
import Foreign.C.String
import GHC.Generics (Generic (..))
import System.FilePath
import System.Directory
import System.IO (stderr, hPutStrLn, Handle)
import System.IO.Error (isDoesNotExistError)

import LLVM.Link
import LLVM.Compile
import qualified LLVM.AST

import AbstractSyntax
import Builder
import CheckType ( CheckableE (..), asFFIFunType, checkHasType, checkExtends)
#ifdef DEX_DEBUG
import CheckType (checkTypesM)
#endif
import Core
import ConcreteSyntax
import CheapReduction
import Err
import IRVariants
import Imp
import ImpToLLVM
import Inference
import Inline
import Logging
import Lower
import MTL1
import Subst
import Name
import OccAnalysis
import Optimize
import PPrint (pprintCanonicalized)
import Paths_dex  (getDataFileName)
import QueryType
import Runtime
import Serialize (takePtrSnapshot, restorePtrSnapshot)
import Simplify
import SourceRename
import Types.Core
import Types.Imp
import Types.Misc
import Types.Primitives
import Types.Source
import Util ( Tree (..), measureSeconds, File (..), readFileWithHash)

-- === top-level monad ===

data LibPath = LibDirectory FilePath | LibBuiltinPath

data EvalConfig = EvalConfig
  { backendName   :: Backend
  , libPaths      :: [LibPath]
  , preludeFile   :: Maybe FilePath
  , logFileName   :: Maybe FilePath
  , logFile       :: Maybe Handle
  , optLevel      :: OptLevel
  , printBackend  :: PrintBackend }

class Monad m => ConfigReader m where
  getConfig :: m EvalConfig

data PassCtx = PassCtx
  { requiresBench :: BenchRequirement
  , shouldLogPass :: PassName -> Bool
  }

initPassCtx :: PassCtx
initPassCtx = PassCtx NoBench (const True)

class Monad m => PassCtxReader m where
  getPassCtx :: m PassCtx
  withPassCtx :: PassCtx -> m a -> m a

class Monad m => RuntimeEnvReader m where
  getRuntimeEnv :: m RuntimeEnv

type TopLogger m = (MonadIO m, MonadLogger [Output] m)

class ( forall n. Fallible (m n)
      , forall n. MonadLogger [Output] (m n)
      , forall n. Catchable (m n)
      , forall n. ConfigReader (m n)
      , forall n. PassCtxReader (m n)
      , forall n. RuntimeEnvReader (m n)
      , forall n. MonadIO (m n)  -- TODO: something more restricted here
      , TopBuilder m )
      => Topper m

data TopperReaderData = TopperReaderData
  { topperPassCtx    :: PassCtx
  , topperEvalConfig :: EvalConfig
  , topperRuntimeEnv :: RuntimeEnv }

newtype TopperM (n::S) a = TopperM
  { runTopperM'
    :: TopBuilderT (ReaderT TopperReaderData (LoggerT [Output] IO)) n a }
    deriving ( Functor, Applicative, Monad, MonadIO, MonadFail
             , Fallible, EnvReader, ScopeReader, Catchable)

-- Hides the `n` parameter as an existential
data TopStateEx where
  TopStateEx :: Distinct n => Env n -> RuntimeEnv -> TopStateEx

-- Hides the `n` parameter as an existential
data TopSerializedStateEx where
  TopSerializedStateEx :: Distinct n => SerializedEnv n -> TopSerializedStateEx

runTopperM
  :: EvalConfig -> TopStateEx
  -> (forall n. Mut n => TopperM n a)
  -> IO (a, TopStateEx)
runTopperM opts (TopStateEx env rtEnv) cont = do
  let maybeLogFile = logFile opts
  (Abs frag (LiftE result), _) <- runLogger maybeLogFile \l -> runLoggerT l $
    flip runReaderT (TopperReaderData initPassCtx opts rtEnv) $
      runTopBuilderT env $ runTopperM' do
        localTopBuilder $ LiftE <$> cont
  return (result, extendTopEnv env rtEnv frag)

extendTopEnv :: Distinct n => Env n -> RuntimeEnv -> TopEnvFrag n l -> TopStateEx
extendTopEnv env rtEnv frag = do
  refreshAbsPure (toScope env) (Abs frag UnitE) \_ frag' UnitE ->
    TopStateEx (extendOutMap env frag') rtEnv

initTopState :: IO TopStateEx
initTopState = do
  dyvarStores <- allocateDynamicVarKeyPtrs
  return $ TopStateEx emptyOutMap dyvarStores

allocateDynamicVarKeyPtrs :: IO DynamicVarKeyPtrs
allocateDynamicVarKeyPtrs = do
  ptr <- createTLSKey
  return [(OutStreamDyvar, castPtr ptr)]

-- ======

evalSourceBlockIO
  :: EvalConfig -> TopStateEx -> SourceBlock -> IO (Result, TopStateEx)
evalSourceBlockIO opts env block =
  runTopperM opts env $ evalSourceBlockRepl block

-- Used for the top-level source file (rather than imported modules)
evalSourceText
  :: (Topper m, Mut n)
  => Text -> (SourceBlock -> IO ()) -> (Result -> IO Bool)
  -> m n [(SourceBlock, Result)]
evalSourceText source beginCallback endCallback = do
  let (UModule mname deps sbs) = parseUModule Main source
  mapM_ ensureModuleLoaded deps
  evalSourceBlocks mname sbs
  where
    evalSourceBlocks mname = \case
      [] -> return []
      (sb:rest) -> do
        liftIO $ beginCallback sb
        result <- evalSourceBlock mname sb
        liftIO (endCallback result) >>= \case
          False -> return [(sb, result)]
          True  -> ((sb, result):) <$> evalSourceBlocks mname rest

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
    SourceBlock _ _ _ _ (Misc (ImportModule name)) -> do
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
    updateTopEnv $ UpdateLoadedModules (umppName md) evaluated
{-# SCC ensureModuleLoaded #-}

evalSourceBlock
  :: (Topper m, Mut n) => ModuleSourceName -> SourceBlock -> m n Result
evalSourceBlock mname block = do
  result <- withCompileTime do
     (maybeErr, logs) <- catchLogsAndErrs do
       benchReq <- getBenchRequirement block
       withPassCtx (PassCtx benchReq (passLogFilter $ sbLogLevel block)) $
         evalSourceBlock' mname block
     return $ Result logs maybeErr
  case resultErrs result of
    Failure _ -> case sbContents block of
      TopDecl decl -> do
        case runFallibleM (parseDecl decl) of
          Success decl' -> emitSourceMap $ uDeclErrSourceMap mname decl'
          Failure _ -> return ()
      _ -> return ()
    _ -> return ()
  return $ filterLogs block $ addResultCtx block result
{-# SCC evalSourceBlock #-}

evalSourceBlock'
  :: (Topper m, Mut n) => ModuleSourceName -> SourceBlock -> m n ()
evalSourceBlock' mname block = case sbContents block of
  TopDecl decl -> parseDecl decl >>= execUDecl mname
  Command cmd expr' -> do
   expr <- parseExpr expr'
   case cmd of
    -- TODO: we should filter the top-level emissions we produce in this path
    -- we want cache entries but we don't want dead names.
    EvalExpr fmt -> when (mname == Main) case fmt of
      Printed maybeExplicitBackend -> do
        printMode <- case maybeExplicitBackend of
          Just backend -> return backend
          Nothing -> printBackend <$> getConfig
        case printMode of
          PrintHaskell -> do
            val <- evalUExpr expr
            logTop $ TextOut $ pprint val
          PrintCodegen -> do
            stringVal <- evalUExpr $ addShowAny expr
            s <- getDexString stringVal
            logTop $ TextOut s
      RenderHtml -> do
        stringVal <- evalUExpr $ addTypeAnn expr (referTo "String")
        s <- getDexString stringVal
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
      ty <- cheapNormalize =<< getType val
      logTop $ TextOut $ pprintCanonicalized ty
  DeclareForeign fname dexName cTy -> do
    let b = fromString dexName :: UBinder (AtomNameC CoreIR) VoidS VoidS
    ty <- evalUType =<< parseExpr cTy
    asFFIFunType ty >>= \case
      Nothing -> throw TypeErr
        "FFI functions must be n-ary first order functions with the IO effect"
      Just (impFunTy, naryPiTy) -> do
        -- TODO: query linking stuff and check the function is actually available
        let hint = getNameHint b
        fTop  <- emitBinding hint $ TopFunBinding $ FFITopFun fname impFunTy
        vCore <- emitBinding hint $ AtomNameBinding $ FFIFunBound naryPiTy fTop
        UBindSource sourceName <- return b
        emitSourceMap $ SourceMap $
          M.singleton sourceName [ModuleVar mname (Just $ UAtomVar vCore)]
  DeclareCustomLinearization fname zeros g -> do
    expr <- parseExpr g
    lookupSourceMap fname >>= \case
      Nothing -> throw UnboundVarErr $ pprint fname
      Just (UAtomVar fname') -> do
        lookupCustomRules fname' >>= \case
          Nothing -> return ()
          Just _  -> throw TypeErr
            $ pprint fname ++ " already has a custom linearization"
        lookupAtomName fname' >>= \case
          NoinlineFun _ _ -> return ()
          _ -> throw TypeErr "Custom linearizations only apply to @noinline functions"
        -- We do some special casing to avoid instantiating polymorphic functions.
        impl <- case expr of
          WithSrcE _ (UVar _) ->
            renameSourceNamesUExpr expr >>= \case
              WithSrcE _ (UVar (InternalName _ (UAtomVar v))) -> return $ Var v
              _ -> error "Expected a variable"
          _ -> evalUExpr expr
        fType <- getType fname'
        (nimplicit, nexplicit, linFunTy) <- liftExceptEnvReaderM $ getLinearizationType zeros fType
        impl `checkHasType` linFunTy >>= \case
          Failure _ -> do
            implTy <- getType impl
            throw TypeErr $ unlines
              [ "Expected the custom linearization to have type:" , "" , pprint linFunTy , ""
              , "but it has type:" , "" , pprint implTy]
          Success () -> return ()
        updateTopEnv $ AddCustomRule fname' $ CustomLinearize nimplicit nexplicit zeros impl
      Just _ -> throw TypeErr
        $ "Custom linearization can only be defined for functions"
  UnParseable _ s -> throw ParseErr s
  Misc m -> case m of
    GetNameType v -> do
      ty <- cheapNormalize =<< sourceNameType v
      logTop $ TextOut $ pprintCanonicalized ty
    ImportModule moduleName -> importModule moduleName
    QueryEnv query -> void $ runEnvQuery query $> UnitE
    ProseBlock _ -> return ()
    CommentLine  -> return ()
    EmptyLines   -> return ()
  where
    addTypeAnn :: UExpr n -> UExpr n -> UExpr n
    addTypeAnn e = WithSrcE Nothing . UTypeAnn e
    addShowAny :: UExpr n -> UExpr n
    addShowAny e = WithSrcE Nothing $ UApp (referTo "show_any") [e] []
    referTo :: SourceName -> UExpr n
    referTo = WithSrcE Nothing . UVar . SourceName

runEnvQuery :: Topper m => EnvQuery -> m n ()
runEnvQuery query = do
  env <- unsafeGetEnv
  case query of
    DumpSubst -> logTop $ TextOut $ pprint $ env
    InternalNameInfo name ->
      case lookupSubstFragRaw (fromRecSubst $ envDefs $ topEnv env) name of
        Nothing      -> throw UnboundVarErr $ pprint name
        Just binding -> logTop $ TextOut $ pprint binding
    SourceNameInfo name -> do
      lookupSourceMap name >>= \case
        Nothing -> throw UnboundVarErr $ pprint name
        Just uvar -> do
          logTop $ TextOut $ pprint uvar
          info <- case uvar of
            UAtomVar     v' -> pprint <$> lookupEnv v'
            UTyConVar    v' -> pprint <$> lookupEnv v'
            UDataConVar  v' -> pprint <$> lookupEnv v'
            UClassVar    v' -> pprint <$> lookupEnv v'
            UMethodVar   v' -> pprint <$> lookupEnv v'
            UEffectVar   v' -> pprint <$> lookupEnv v'
            UEffectOpVar v' -> pprint <$> lookupEnv v'
            UPunVar v' -> do
              val <- lookupEnv v'
              return $ pprint val ++ "\n(type constructor and data constructor share the same name)"
          logTop $ TextOut $ "Binding:\n" ++ info

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
  alreadyLoaded <- M.keysSet . fromLoadedModules
    <$> withEnv (envLoadedModules . topEnv)
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
parseUModuleDepsCached
  :: (Mut n, TopBuilder m) => ModuleSourceName -> File -> m n [ModuleSourceName]
parseUModuleDepsCached Main file = return $ parseUModuleDeps Main file
parseUModuleDepsCached name file = do
  cache <- parsedDeps <$> getCache
  let req = fHash file
  case M.lookup name cache of
    Just (cachedReq, result) | cachedReq == req -> return result
    _ -> do
      let result = parseUModuleDeps name file
      updateTopEnv $ ExtendCache $ mempty { parsedDeps = M.singleton name (req, result) }
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
          updateTopEnv $ ExtendCache $ mempty {
            moduleEvaluations = M.singleton name (req, result) }
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
  TopEnvFrag envFrag moduleEnvFrag otherUpdates <- return topFrag
  ModuleEnv (ImportStatus directDeps transDeps) sm scs <- return moduleEnvFrag
  let fragToReEmit = TopEnvFrag envFrag mempty otherUpdates
  let evaluatedModule = Module name directDeps transDeps sm scs
  emitEnv $ Abs fragToReEmit evaluatedModule

importModule :: (Mut n, TopBuilder m, Fallible1 m) => ModuleSourceName -> m n ()
importModule name = do
  lookupLoadedModule name >>= \case
    Nothing -> throw ModuleImportErr $ "Couldn't import " ++ pprint name
    Just name' -> do
      Module _ _ transImports' _ _ <- lookupModule name'
      let importStatus = ImportStatus (S.singleton name')
            (S.singleton name' <> transImports')
      emitLocalModuleEnv $ mempty { envImportStatus = importStatus }
{-# SCC importModule #-}

passLogFilter :: LogLevel -> PassName -> Bool
passLogFilter = \case
  LogAll           -> const True
  LogNothing       -> const False
  LogPasses passes -> (`elem` passes)
  PrintEvalTime    -> const False
  PrintBench _     -> const False

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

evalUType :: (Topper m, Mut n) => UType VoidS -> m n (CType n)
evalUType ty = do
  logTop $ PassInfo Parse $ pprint ty
  renamed <- logPass RenamePass $ renameSourceNamesUExpr ty
  checkPass TypePass $ checkTopUType renamed

evalUExpr :: (Topper m, Mut n) => UExpr VoidS -> m n (CAtom n)
evalUExpr expr = do
  logTop $ PassInfo Parse $ pprint expr
  renamed <- logPass RenamePass $ renameSourceNamesUExpr expr
  typed <- checkPass TypePass $ inferTopUExpr renamed
  evalBlock typed
{-# SCC evalUExpr #-}

whenOpt :: Topper m => a -> (a -> m n a) -> m n a
whenOpt x act = getConfig <&> optLevel >>= \case
  NoOptimize -> return x
  Optimize   -> act x

evalBlock :: (Topper m, Mut n) => CBlock n -> m n (CAtom n)
evalBlock typed = do
  -- Be careful when adding new compilation passes here.  If you do, be sure to
  -- also check compileTopLevelFun, below, and Export.prepareFunctionForExport.
  -- In most cases it should be easiest to add new passes to simpOptimizations or
  -- loweredOptimizations, below, because those are reused in all three places.
  checkEffects Pure typed
  synthed <- checkPass SynthPass $ synthTopE typed
  simplifiedBlock <- checkPass SimpPass $ simplifyTopBlock synthed
  SimplifiedBlock simp recon <- return simplifiedBlock
  checkEffects Pure simp
  NullaryLamExpr opt <- simpOptimizations $ NullaryLamExpr simp
  checkEffects Pure opt
  simpResult <- case opt of
    AtomicBlock result -> return result
    _ -> do
      lowered <- checkPass LowerPass $ lowerFullySequential $ NullaryLamExpr opt
      checkEffects (OneEffect InitEffect) (NullaryDestLamApp lowered)
      NullaryDestLamExpr lOpt <- loweredOptimizations lowered
      checkEffects (OneEffect InitEffect) lOpt
      cc <- getEntryFunCC
      impOpt <- checkPass ImpPass $ toImpFunction cc (NullaryDestLamExpr lOpt)
      llvmOpt <- packageLLVMCallable impOpt
      resultVals <- liftIO $ callEntryFun llvmOpt []
      resultTy <- getDestBlockType lOpt
      repValAtom =<< repValFromFlatList resultTy resultVals
  applyReconTop recon simpResult
{-# SCC evalBlock #-}

simpOptimizations :: Topper m => SLam n -> m n (SLam n)
simpOptimizations simp = do
  analyzed <- whenOpt simp $ checkPass OccAnalysisPass . analyzeOccurrences
  inlined <- whenOpt analyzed $ checkPass InlinePass . inlineBindings
  analyzed2 <- whenOpt inlined $ checkPass OccAnalysisPass . analyzeOccurrences
  inlined2 <- whenOpt analyzed2 $ checkPass InlinePass . inlineBindings
  whenOpt inlined2 $ checkPass OptPass . optimize

loweredOptimizations :: Topper m => DestLamExpr SimpIR n -> m n (DestLamExpr SimpIR n)
loweredOptimizations lowered = do
  lopt <- whenOpt lowered $ checkPass LowerOptPass .
    (dceTopDest >=> hoistLoopInvariantDest)
  whenOpt lopt \lo -> do
    (vo, errs) <- vectorizeLoops 64 lo
    l <- getFilteredLogger
    logFiltered l VectPass $ return [TextOut $ pprint errs]
    checkPass VectPass $ return vo

loweredOptimizationsNoDest :: Topper m => SLam n -> m n (SLam n)
loweredOptimizationsNoDest lowered = do
  lopt <- whenOpt lowered $ checkPass LowerOptPass .
    (dceTop >=> hoistLoopInvariant)
  -- TODO Add a NoDest entry point for vectorization and add it here
  return lopt

evalSpecializations :: (Topper m, Mut n) => [TopFunName n] -> m n ()
evalSpecializations fs = do
  fSimps <- toposortAnnVars <$> catMaybes <$> forM fs \f -> lookupTopFun f >>= \case
    DexTopFun _ _ simp Waiting -> return $ Just (f, simp)
    _ -> return Nothing
  forM_ fSimps \(f, simp) -> do
    -- Prevents infinite loop in case compiling `v` ends up requiring `v`
    -- (even without recursion in Dex itself this is possible via the
    -- specialization cache)
    updateTopEnv $ UpdateTopFunEvalStatus f Running
    imp <- compileTopLevelFun StandardCC simp
    objName <- toCFunction (getNameHint f) imp >>= emitObjFile
    void $ loadObject objName
    updateTopEnv $ UpdateTopFunEvalStatus f (Finished $ TopFunLowerings objName)

evalDictSpecializations :: (Topper m, Mut n) => [SpecDictName n] -> m n ()
evalDictSpecializations ds = do
  -- TODO Do we have to do these in order, like evalSpecializations, or are they
  -- independent enough not to need it?
  -- TODO Do we need to gate the status of these, too?
  forM_ ds \dName -> do
    SpecializedDict _ (Just fs) <- lookupSpecDict dName
    fs' <- forM fs \lam -> do
      opt <- simpOptimizations lam
      lowered <- checkPass LowerPass $ lowerFullySequentialNoDest opt
      loweredOptimizationsNoDest lowered
    updateTopEnv $ LowerDictSpecialization dName fs'
  return ()

execUDecl
  :: (Topper m, Mut n) => ModuleSourceName -> UTopDecl VoidS VoidS -> m n ()
execUDecl mname decl = do
  logTop $ PassInfo Parse $ pprint decl
  Abs renamedDecl sourceMap <-
    logPass RenamePass $ renameSourceNamesTopUDecl mname decl
  inferenceResult <- checkPass TypePass $ inferTopUDecl renamedDecl sourceMap
  case inferenceResult of
    UDeclResultBindName ann block (Abs b sm) -> do
      result <- evalBlock block
      case ann of
        NoInlineLet -> do
          fTy <- getType result
          f <- emitBinding (getNameHint b) $ AtomNameBinding $ NoinlineFun fTy result
          applyRename (b@>f) sm >>= emitSourceMap
        _ -> do
          v <- emitTopLet (getNameHint b) ann (Atom result)
          applyRename (b@>v) sm >>= emitSourceMap
    UDeclResultBindPattern hint block (Abs bs sm) -> do
      result <- evalBlock block
      xs <- unpackTelescope bs result
      vs <- forM xs \x -> emitTopLet hint PlainLet (Atom x)
      applyRename (bs@@>vs) sm >>= emitSourceMap
    UDeclResultDone sourceMap' -> emitSourceMap sourceMap'
{-# SCC execUDecl #-}

compileTopLevelFun :: (Topper m, Mut n)
  => CallingConvention -> SLam n -> m n (ImpFunction n)
compileTopLevelFun cc fSimp = do
  fOpt <- simpOptimizations fSimp
  fLower <- checkPass LowerPass $ lowerFullySequential fOpt
  flOpt <- loweredOptimizations fLower
  checkPass ImpPass $ toImpFunction cc flOpt
{-# SCC compileTopLevelFun #-}

printCodegen :: (Topper m, Mut n) => CAtom n -> m n String
printCodegen x = do
  block <- liftBuilder $ buildBlock do
    emitExpr $ PrimOp $ MiscOp $ ShowAny $ sink x
  getDexString =<< evalBlock block

loadObject :: (Topper m, Mut n) => FunObjCodeName n -> m n NativeFunction
loadObject fname =
  lookupLoadedObject fname >>= \case
    Just p -> return p
    Nothing -> do
      f <- lookupFunObjCode fname >>= loadObjectContent
      updateTopEnv $ UpdateLoadedObjects fname f
      return f

loadObjectContent :: (Topper m, Mut n) => CFunction n -> m n NativeFunction
loadObjectContent CFunction{objectCode, linkerNames} = do
  (LinktimeNames funNames ptrNames) <- return linkerNames
  funVals <- forM funNames \name -> nativeFunPtr <$> loadObject name
  ptrVals <- forM ptrNames \name -> snd <$> lookupPtrName name
  dyvarStores <- getRuntimeEnv
  liftIO $ linkFunObjCode objectCode dyvarStores $ LinktimeVals funVals ptrVals

linkFunObjCode
  :: FunObjCode -> DynamicVarKeyPtrs -> LinktimeVals -> IO NativeFunction
linkFunObjCode objCode dyvarStores (LinktimeVals funVals ptrVals) = do
  let (WithCNameInterface code mainFunName reqFuns reqPtrs dtors) = objCode
  let linkMap =   zip reqFuns (map castFunPtrToPtr funVals)
               <> zip reqPtrs ptrVals
               <> dynamicVarLinkMap dyvarStores
  l <- createLinker
  addExplicitLinkMap l linkMap
  addObjectFile l code
  ptr <- getFunctionPointer l mainFunName
  dtorPtrs <- mapM (getFunctionPointer l) dtors
  let destructor :: IO () = do
        mapM_ callDtor dtorPtrs
        destroyLinker l
  return $ NativeFunction ptr destructor

toCFunction :: (Topper m, Mut n) => NameHint -> ImpFunction n -> m n (CFunction n)
toCFunction nameHint impFun = do
  logger <- getFilteredLogger
  (closedImpFun, reqFuns, reqPtrNames) <- abstractLinktimeObjects impFun
  obj <- impToLLVM logger nameHint closedImpFun >>= compileToObjCode
  reqObjNames <- mapM funNameToObj reqFuns
  return $ CFunction nameHint obj (LinktimeNames reqObjNames reqPtrNames)

getLLVMOptLevel :: EvalConfig -> LLVMOptLevel
getLLVMOptLevel cfg = case optLevel cfg of
  NoOptimize -> OptALittle
  Optimize   -> OptAggressively

getEntryFunCC :: Topper m => m n CallingConvention
getEntryFunCC = getConfig <&> backendName <&> \case
    LLVMCUDA -> EntryFunCC CUDARequired
    _        -> EntryFunCC CUDANotRequired

packageLLVMCallable :: forall n m. (Topper m, Mut n)
  => ImpFunction n -> m n LLVMCallable
packageLLVMCallable impFun = do
  nativeFun <- toCFunction "main" impFun >>= loadObjectContent
  benchRequired <- requiresBench <$> getPassCtx
  logger <- getFilteredLogger
  let IFunType _ _ resultTypes = impFunType impFun
  return LLVMCallable{..}
{-# SCC packageLLVMCallable #-}

compileToObjCode :: Topper m => WithCNameInterface LLVM.AST.Module -> m n FunObjCode
compileToObjCode astWithNames = forM astWithNames \ast -> do
  logger  <- getFilteredLogger
  opt <- getLLVMOptLevel <$> getConfig
  liftIO $ compileLLVM logger opt ast (cniMainFunName astWithNames)

funNameToObj
  :: (EnvReader m, Fallible1 m) => ImpFunName n -> m n (FunObjCodeName n)
funNameToObj v = do
  lookupEnv v >>= \case
    TopFunBinding (DexTopFun _ _ _ (Finished impl)) -> return $ topFunObjCode impl
    b -> error $ "couldn't find object cache entry for " ++ pprint v ++ "\ngot:\n" ++ pprint b

withCompileTime :: MonadIO m => m Result -> m Result
withCompileTime m = do
  (Result outs err, t) <- measureSeconds m
  return $ Result (outs ++ [TotalTime t]) err

checkPass :: (Topper m, Pretty (e n), CheckableE r e)
          => PassName -> m n (e n) -> m n (e n)
checkPass name cont = do
  result <- logPass name do
    result <- cont
    return result
#ifdef DEX_DEBUG
  logTop $ MiscLog $ "Running checks"
  checkTypesM result
  logTop $ MiscLog $ "Checks passed"
#else
  logTop $ MiscLog $ "Checks skipped (not a debug build)"
#endif
  return result

checkEffects :: (Topper m, HasEffectsE e r, IRRep r) => EffectRow r n -> e n -> m n ()
checkEffects allowedEffs e = do
  actualEffs <- getEffects e
  checkExtends allowedEffs actualEffs

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
  {-# SCC logPassPrinting #-} logTop $ PassInfo passName
    $ "=== Result ===\n" <> pprint result
  return result

loadModuleSource
  :: (MonadIO m, Fallible m) => EvalConfig -> ModuleSourceName -> m File
loadModuleSource config moduleName = do
  fullPath <- case moduleName of
    OrdinaryModule moduleName' -> findFullPath $ moduleName' ++ ".dx"
    Prelude -> case preludeFile config of
      Nothing -> findFullPath "prelude.dx"
      Just path -> return path
    Main -> error "shouldn't be trying to load the source for main"
  readFileWithHash fullPath
  where
    findFullPath :: (MonadIO m, Fallible m) => String -> m FilePath
    findFullPath fname = do
      fsPaths <- liftIO $ traverse resolveBuiltinPath $ libPaths config
      liftIO (findFile fsPaths fname) >>= \case
        Just fpath -> return fpath
        Nothing    -> throw ModuleImportErr $ unlines
          [ "Couldn't find a source file for module " ++
            (case moduleName of
               OrdinaryModule n -> n; Prelude -> "prelude"; Main -> error "")
          , "Hint: Consider extending --lib-path?"
          ]

    resolveBuiltinPath = \case
      LibBuiltinPath   -> liftIO $ getDataFileName "lib"
      LibDirectory dir -> return dir
{-# SCC loadModuleSource #-}

getBenchRequirement :: Topper m => SourceBlock -> m n BenchRequirement
getBenchRequirement block = case sbLogLevel block of
  PrintBench _ -> do
    backend <- backendName <$> getConfig
    let needsSync = case backend of LLVMCUDA -> True
                                    _        -> False
    return $ DoBench needsSync
  _ -> return NoBench

getDexString :: (MonadIO1 m, EnvReader m, Fallible1 m) => Val CoreIR n -> m n String
getDexString val = do
  -- TODO: use a `ByteString` instead of `String`
  SimpInCore (LiftSimp _ (RepValAtom (RepVal _ tree))) <- return val
  Branch [Leaf (IIdxRepVal n), Leaf (IPtrVar ptrName _)] <- return tree
  PtrBinding (CPU, Scalar Word8Type) (PtrLitVal ptr) <- lookupEnv ptrName
  liftIO $ peekCStringLen (castPtr ptr, fromIntegral n)

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
        Right result -> fromSerializedEnv result
        _            -> removeFile cachePath >> initTopState
    else initTopState
{-# SCC loadCache #-}

storeCache :: MonadIO m => TopStateEx -> m ()
storeCache env = liftIO do
  cachePath <- getCachePath
  createDirectoryIfMissing True =<< getCacheDir
  TopSerializedStateEx sEnv <- toSerializedEnv env
  BS.writeFile cachePath $ encode sEnv

snapshotPtrs :: MonadIO m => RecSubst Binding n -> m (RecSubst Binding n)
snapshotPtrs bindings = RecSubst <$> traverseSubstFrag
  (\case
      PtrBinding ty p -> liftIO $ PtrBinding ty <$> takePtrSnapshot ty p
      b -> return b)
  (fromRecSubst bindings)

traverseBindingsTopStateEx
  :: Monad m => TopStateEx
  -> (forall c n. Binding c n -> m (Binding c n)) -> m TopStateEx
traverseBindingsTopStateEx (TopStateEx (Env tenv menv) dyvars) f = do
  defs <- traverseSubstFrag f $ fromRecSubst $ envDefs tenv
  return $ TopStateEx (Env (tenv {envDefs = RecSubst defs}) menv) dyvars

fromSerializedEnv :: forall n m. MonadIO m => SerializedEnv n -> m TopStateEx
fromSerializedEnv (SerializedEnv defs rules cache) = do
  Distinct <- return (fabricateDistinctEvidence :: DistinctEvidence n)
  dyvarStores <- liftIO allocateDynamicVarKeyPtrs
  let topEnv = Env (TopEnv defs rules cache mempty mempty) mempty
  restorePtrSnapshots $ TopStateEx topEnv dyvarStores

toSerializedEnv :: MonadIO m => TopStateEx -> m TopSerializedStateEx
toSerializedEnv (TopStateEx (Env (TopEnv (RecSubst defs) (CustomRules rules) cache _ _) _) _) = do
  collectGarbage (RecSubstFrag defs) (PairE (CustomRules rules) cache)
    \defsFrag'@(RecSubstFrag defs') (PairE (CustomRules rules') cache') -> do
      let liveNames = toNameSet $ toScopeFrag defsFrag'
      let rules'' = CustomRules
           $ M.filterWithKey (\k _ -> k `isInNameSet` liveNames) rules'
      defs'' <- snapshotPtrs (RecSubst defs')
      return $ TopSerializedStateEx $ SerializedEnv defs'' rules'' cache'

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

restorePtrSnapshots :: MonadIO m => TopStateEx -> m TopStateEx
restorePtrSnapshots s = traverseBindingsTopStateEx s \case
  PtrBinding ty p  -> liftIO $ PtrBinding ty <$> restorePtrSnapshot p
  b -> return b

getFilteredLogger :: Topper m => m n PassLogger
getFilteredLogger = do
  shouldLog <- shouldLogPass <$> getPassCtx
  logger  <- getLogger
  return $ FilteredLogger shouldLog logger

-- === instances ===

instance PassCtxReader (TopperM n) where
  getPassCtx = TopperM $ asks topperPassCtx
  withPassCtx ctx cont = TopperM $
    liftTopBuilderTWith (local \r -> r {topperPassCtx = ctx}) $
      runTopperM' cont

instance RuntimeEnvReader (TopperM n) where
  getRuntimeEnv = TopperM $ asks topperRuntimeEnv

instance ConfigReader (TopperM n) where
  getConfig = TopperM $ asks topperEvalConfig

instance (Monad1 m, ConfigReader (m n)) => ConfigReader (StateT1 s m n) where
  getConfig = lift11 getConfig

instance Topper TopperM

instance TopBuilder TopperM where
  emitBinding = emitBindingDefault
  emitEnv (Abs frag result) = do
    result' `PairE` ListE fNames `PairE` ListE dictNames <- TopperM $ emitEnv $
      Abs frag $ result `PairE` ListE (boundNamesList frag) `PairE` ListE (boundNamesList frag)
    evalSpecializations fNames
    evalDictSpecializations dictNames
    return result'
  emitNamelessEnv env = TopperM $ emitNamelessEnv env
  localTopBuilder cont = TopperM $ localTopBuilder $ runTopperM' cont

instance MonadLogger [Output] (TopperM n) where
  getLogger = TopperM $ lift1 $ lift $ getLogger
  withLogger l cont =
    TopperM $ liftTopBuilderTWith (withLogger l) (runTopperM' cont)

instance Generic TopStateEx where
  type Rep TopStateEx = Rep (Env UnsafeS, RuntimeEnv)
  from (TopStateEx env rtEnv) = from ((unsafeCoerceE env :: Env UnsafeS), rtEnv)
  to rep = do
    case fabricateDistinctEvidence :: DistinctEvidence UnsafeS of
      Distinct -> uncurry TopStateEx (to rep :: (Env UnsafeS, RuntimeEnv))

getLinearizationType :: SymbolicZeros -> CType n -> EnvReaderT Except n (Int, Int, CType n)
getLinearizationType zeros = \case
  Pi (CorePiType ExplicitApp bs Pure resultTy) -> do
    (numIs, numEs) <- getNumImplicits $ fst $ unzipExpls bs
    refreshAbs (Abs bs resultTy) \bs' resultTy' -> do
      PairB _ bsE <- return $ splitNestAt numIs bs'
      let explicitArgTys = nestToList (\b -> sink $ binderType b) bsE
      argTanTys <- forM explicitArgTys \t -> maybeTangentType t >>= \case
        Just tty -> case zeros of
          InstantiateZeros -> return tty
          SymbolicZeros    -> symbolicTangentTy tty
        Nothing  -> throw TypeErr $ "No tangent type for: " ++ pprint t
      resultTanTy <- maybeTangentType resultTy' >>= \case
        Just rtt -> return rtt
        Nothing  -> throw TypeErr $ "No tangent type for: " ++ pprint resultTy'
      tanFunTy <- Pi <$> nonDepPiType argTanTys Pure resultTanTy
      let fullTy = CorePiType ExplicitApp bs' Pure (PairTy resultTy' tanFunTy)
      return (numIs, numEs, Pi fullTy)
  _ -> throw TypeErr $ "Can't define a custom linearization for implicit or impure functions"
  where
    getNumImplicits :: Fallible m => [Explicitness] -> m (Int, Int)
    getNumImplicits = \case
      [] -> return (0, 0)
      expl:expls -> do
        (ni, ne) <- getNumImplicits expls
        case expl of
          Inferred _ _ -> return (ni + 1, ne)
          Explicit -> case ni of
            0 -> return (0, ne + 1)
            _ -> throw TypeErr "All implicit args must precede implicit args"
