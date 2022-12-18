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
  evalSourceBlockIO, loadCache, storeCache, clearCache,
  ensureModuleLoaded, importModule,
  loadObject, toCFunction) where

import Data.Foldable (toList)
import Data.Functor
import Control.Category ((>>>))
import Control.Exception (throwIO, catch)
import Control.Monad.Writer.Strict  hiding (pass)
import Control.Monad.State.Strict
import Control.Monad.Reader
import qualified Data.ByteString as BS
import Data.Text (Text)
import Data.Text.Prettyprint.Doc
import Data.Store (encode, decode)
import Data.List (partition)
import qualified Data.Map.Strict as M
import qualified Data.Set        as S
import Foreign.Ptr
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
import CheckType ( CheckableE (..), asFFIFunType, checkHasType
                 , asSpecializableFunction)
#ifdef DEX_DEBUG
import CheckType (checkTypesM)
#endif
import Core
import Err
import IRVariants
import Imp
import ImpToLLVM
import Inference
import Inline
import Logging
import Lower
import MTL1
import Name
import OccAnalysis
import Optimize
import PPrint (pprintCanonicalized)
import Paths_dex  (getDataFileName)
import QueryType
import Runtime
import Serialize ( HasPtrs (..), pprintVal, getDexString
                 , takePtrSnapshot, restorePtrSnapshot)
import Simplify
import SourceRename
import Types.Core
import Types.Imp
import Types.Misc
import Types.Primitives
import Types.Source
import Util (measureSeconds, File (..), readFileWithHash)

-- === top-level monad ===

data LibPath = LibDirectory FilePath | LibBuiltinPath

data EvalConfig = EvalConfig
  { backendName   :: Backend
  , libPaths      :: [LibPath]
  , preludeFile   :: Maybe FilePath
  , logFileName   :: Maybe FilePath
  , logFile       :: Maybe Handle
  , optLevel      :: OptLevel }

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
  let (UModule mname deps sourceBlocks) = parseUModule Main source
  mapM_ ensureModuleLoaded deps
  evalSourceBlocks mname sourceBlocks
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
    SourceBlockP _ _ _ _ (Misc (ImportModule name)) -> do
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
      EvalUDecl decl -> emitSourceMap $ uDeclErrSourceMap mname decl
      _ -> return ()
    _ -> return ()
  return $ filterLogs block $ addResultCtx block result
{-# SCC evalSourceBlock #-}

evalSourceBlock'
  :: (Topper m, Mut n) => ModuleSourceName -> SourceBlock -> m n ()
evalSourceBlock' mname block = case sbContents block of
  EvalUDecl decl -> execUDecl mname decl
  Command cmd expr -> case cmd of
    -- TODO: we should filter the top-level emissions we produce in this path
    -- we want cache entries but we don't want dead names.
    EvalExpr fmt -> when (mname == Main) do
      annExpr <- case fmt of
        Printed -> return expr
        RenderHtml -> return $ addTypeAnn expr $ referTo "String"
      val <- evalUExpr annExpr
      case fmt of
        Printed -> do
          s <- pprintVal val
          logTop $ TextOut s
        RenderHtml -> do
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
        vCore <- emitBinding hint
          $ AtomNameBinding $ TopFunBound naryPiTy $ FFITopFun vImp
        UBindSource sourceName <- return b
        emitSourceMap $ SourceMap $
          M.singleton sourceName [ModuleVar mname (Just $ UAtomVar vCore)]
  DeclareCustomLinearization fname zeros expr -> do
    lookupSourceMap fname >>= \case
      Nothing -> throw UnboundVarErr $ pprint fname
      Just (UAtomVar fname') -> do
        lookupCustomRules fname' >>= \case
          Nothing -> return ()
          Just _  -> throw TypeErr
            $ pprint fname ++ " already has a custom linearization"
        -- We do some special casing to avoid instantiating polymorphic functions.
        impl <- case expr of
          WithSrcE _ (UVar _) ->
            renameSourceNamesUExpr expr >>= \case
              WithSrcE _ (UVar (InternalName _ (UAtomVar v))) -> return $ Var v
              _ -> error "Expected a variable"
          _ -> evalUExpr expr
        fType <- getType fname'
        (nimplicit, linFunTy) <- liftExcept . runFallibleM =<< liftEnvReaderT
          (getLinearizationType fType REmpty [] fType)
        impl `checkHasType` linFunTy >>= \case
          Failure _ -> do
            implTy <- getType impl
            throw TypeErr $ unlines
              [ "Expected the custom linearization to have type:"
              , ""
              , pprint linFunTy
              , ""
              , "but it has type:"
              , ""
              , pprint implTy
              ]
          Success () -> return ()
        emitAtomRules fname' $ CustomLinearize nimplicit zeros impl
      Just _ -> throw TypeErr
        $ "Custom linearization can only be defined for functions"
    where
      getLinearizationType :: CType n -> RNest (PiBinder CoreIR) n l
                           -> [CType l] -> CType l
                           -> EnvReaderT FallibleM l (Int, CType n)
      getLinearizationType fullTy implicitArgs revArgTys = \case
        Pi (PiType pbinder@(PiBinder binder a arr) eff b') -> do
          unless (eff == Pure) $ throw TypeErr $
            "Custom linearization can only be defined for pure functions" ++ but
          let implicit = do
                unless (null revArgTys) $ throw TypeErr $
                  "To define a custom linearization, all implicit and class " ++
                  "arguments of a function have to precede all explicit " ++
                  "arguments. However, the type of " ++ pprint fname ++
                  "is:\n\n" ++ pprint fullTy
                refreshAbs (Abs pbinder b') \pbinder' b'' ->
                  getLinearizationType
                    fullTy (RNest implicitArgs pbinder') [] b''
          case arr of
            ClassArrow -> implicit
            ImplicitArrow -> implicit
            PlainArrow -> do
              b <- case hoist binder b' of
                HoistSuccess b -> return b
                HoistFailure _ -> throw TypeErr $
                  "Custom linearization cannot be defined for dependent " ++
                  "functions" ++ but
              getLinearizationType fullTy implicitArgs (a:revArgTys) b
            LinArrow -> throw NotImplementedErr "Unexpected linear arrow"
        resultTy -> do
          when (null revArgTys) $ throw TypeErr $
            "Custom linearization can only be defined for functions" ++ but
          resultTyTan <- maybeTangentType resultTy >>= \case
            Just rtt -> return rtt
            Nothing  -> throw TypeErr $ unlines
              [ "The type of the result of " ++ pprint fname ++ " is:"
              , ""
              , "  " ++ pprint resultTy
              , ""
              , "but it does not have a well-defined tangent space."
              ]
          tangentWrapper <- case zeros of
            InstantiateZeros -> return id
            SymbolicZeros -> do
              lookupSourceMap "SymbolicTangent" >>= \case
                Nothing -> throw UnboundVarErr $
                  "Can't define a custom linearization with symbolic zeros: " ++
                  "the SymbolicTangent type is not in scope."
                Just (UTyConVar symTanName) -> do
                  TyConBinding dataDefName _ <- lookupEnv symTanName
                  return \elTy -> TypeCon "SymbolicTangent" dataDefName
                    $ DataDefParams [(PlainArrow, elTy)]
                Just _ -> throw TypeErr
                  "SymbolicTangent should name a `data` type"
          let prependTangent linTail ty =
                maybeTangentType ty >>= \case
                  Just tty -> tangentWrapper tty --> linTail
                  Nothing  -> throw TypeErr $ unlines
                    [ "The type of one of the arguments of " ++ pprint fname ++
                      " is:"
                    , ""
                    , "  " ++ pprint ty
                    , ""
                    , "but it doesn't have a well-defined tangent space."
                    ]
          tanFunTy <- foldM prependTangent resultTyTan revArgTys
          (nestLength $ unRNest implicitArgs,) . prependImplicit implicitArgs
            <$> foldM (flip (-->)) (PairTy resultTy tanFunTy) revArgTys
        where
          but = ", but " ++ pprint fname ++ " has type " ++ pprint fullTy
          prependImplicit :: RNest (PiBinder CoreIR) n l -> CType l -> CType n
          prependImplicit is ty = case is of
            REmpty -> ty
            RNest is' i -> prependImplicit is' $ Pi $ PiType i Pure ty
  UnParseable _ s -> throw ParseErr s
  BadSyntax e -> throwErrs e
  Misc m -> case m of
    GetNameType v -> do
      ty <- sourceNameType v
      logTop $ TextOut $ pprintCanonicalized ty
    ImportModule moduleName -> importModule moduleName
    QueryEnv query -> void $ runEnvQuery query $> UnitE
    ProseBlock _ -> return ()
    CommentLine  -> return ()
    EmptyLines   -> return ()
  where
    addTypeAnn :: UExpr n -> UExpr n -> UExpr n
    addTypeAnn e = WithSrcE Nothing . UTypeAnn e
    referTo :: SourceName -> UExpr VoidS
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
            UHandlerVar  v' -> pprint <$> lookupEnv v'
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
          extendCache $ mempty {
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
  Abs topFrag UnitE <-
    localTopBuilder $ mapM_ (evalSourceBlock' name) blocks >> return UnitE
  TopEnvFrag envFrag moduleEnvFrag <- return topFrag
  ModuleEnv (ImportStatus directDeps transDeps) sm scs _ <-
    return $ fragLocalModuleEnv moduleEnvFrag
  let fragToReEmit = TopEnvFrag envFrag $ moduleEnvFrag {
        fragLocalModuleEnv = mempty }
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
  eopt <- checkPass EarlyOptPass $ earlyOptimize typed
  synthed <- checkPass SynthPass $ synthTopBlock eopt
  simplifiedBlock <- checkPass SimpPass $ simplifyTopBlock synthed
  SimplifiedBlock simp recon <- return simplifiedBlock
  analyzed <- whenOpt simp $ checkPass OccAnalysisPass . analyzeOccurrences
  inlined <- whenOpt analyzed $ checkPass InlinePass . inlineBindings
  opt <- whenOpt inlined $ checkPass OptPass . optimize
  result <- case opt of
    AtomicBlock result -> return result
    _ -> do
      lowered <- checkPass LowerPass $ lowerFullySequential opt
      lopt <- whenOpt lowered $ checkPass LowerOptPass .
        (dceDestBlock >=> hoistLoopInvariantDest)
      vopt <- whenOpt lopt \lo -> do
        (vo, errs) <- vectorizeLoops 64 lo
        l <- getFilteredLogger
        logFiltered l VectPass $ return [TextOut $ pprint errs]
        checkPass VectPass $ return vo
      evalLLVM vopt
  applyRecon recon (injectIRE result)
{-# SCC evalBlock #-}

evalSpecializations :: (Topper m, Mut n) => [CAtomName n] -> [SpecDictName n] -> m n ()
evalSpecializations vs sdVs = do
  forM_ vs \v -> do
    lookupAtomName v >>= \case
      TopFunBound _ (SpecializedTopFun (AppSpecialization _ _)) ->
        queryImpCache v >>= \case
          Nothing -> compileTopLevelFun v
          Just _ -> return ()
      _ -> return ()
  forM_ sdVs \d -> do
    SpecializedDictBinding (SpecializedDict absDict@(Abs bs _) Nothing) <- lookupEnv d
    methods <- forM [minBound..maxBound] \method -> do
      ty <- liftEnvReaderM $ ixMethodType method absDict
      lamExpr <- liftBuilder $ buildNaryLamExprFromPi ty \allArgs -> do
        let (extraArgs, methodArgs) = splitAt (nestLength bs) (toList allArgs)
        dict <- applyNaryAbs (sink absDict) extraArgs
        let actualArgs = case method of Size -> []  -- size is thunked
                                        _    -> map Var methodArgs
        methodImpl <- emitExpr $ ProjMethod dict (fromEnum method)
        naryApp methodImpl actualArgs
      simplifyTopFunction lamExpr
    finishSpecializedDict d methods

ixMethodType :: IxMethod -> Abstracted (Dict CoreIR) n -> EnvReaderM n (NaryPiType CoreIR n)
ixMethodType method absDict = do
  refreshAbs absDict \extraArgBs dict -> do
    let extraArgBs' = fmapNest (plainPiBinder . (\(b:>ty) -> b :> unsafeCoerceIRE ty)) extraArgBs
    getType (ProjMethod dict (fromEnum method)) >>= \case
      Pi (PiType b _ resultTy) -> do
        let allBs = extraArgBs' >>> Nest b Empty
        return $ NaryPiType allBs Pure resultTy
      -- non-function methods are thunked
      ty -> do
        Abs unitBinder ty' <- toConstAbs ty
        let unitPiBinder = PiBinder unitBinder UnitTy PlainArrow
        let allBs = extraArgBs' >>> Nest unitPiBinder Empty
        return $ NaryPiType allBs Pure ty'

execUDecl
  :: (Topper m, Mut n) => ModuleSourceName -> UDecl VoidS VoidS -> m n ()
execUDecl mname decl = do
  logTop $ PassInfo Parse $ pprint decl
  Abs renamedDecl sourceMap <-
    logPass RenamePass $ renameSourceNamesTopUDecl mname decl
  inferenceResult <- checkPass TypePass $ inferTopUDecl renamedDecl sourceMap
  case inferenceResult of
    UDeclResultWorkRemaining block declAbs -> do
      result <- evalBlock block
      result' <- case declAbs of
        Abs (ULet NoInlineLet (UPatAnn p _) _) _ -> do
          ty <- getType result
          asSpecializableFunction ty >>= \case
            Just (n, fty) -> do
              f <- emitBinding (getNameHint p) $
                AtomNameBinding $ TopFunBound fty $ AwaitingSpecializationArgsTopFun n result
              -- warm up cache if it's already sufficiently specialized
              -- (this is actually here as a workaround for some sort of
              -- caching/linking bug that occurs when we deserialize compilation
              -- artifacts).
              when (n == 0) do
                let s = AppSpecialization f (Abs Empty (ListE []))
                void $ emitSpecialization s
              return $ Var f
            Nothing -> throw TypeErr $
              "Not a valid @noinline function type: " ++ pprint ty
        _ -> return result
      emitSourceMap =<< applyUDeclAbs declAbs result'
    UDeclResultDone sourceMap' -> emitSourceMap sourceMap'
{-# SCC execUDecl #-}

compileTopLevelFun :: (Topper m, Mut n) => CAtomName n -> m n ()
compileTopLevelFun fname = do
  fCore <- specializedFunCoreDefinition fname
  fSimp <- simplifyTopFunction fCore
  fImp <- toImpFunction StandardCC fSimp
  fImpName <- emitImpFunBinding (getNameHint fname) fImp
  extendImpCache fname fImpName
  fObj <- toCFunction (getNameHint fImpName) fImp
  extendObjCache fImpName fObj
  void $ loadObject fObj
{-# SCC compileTopLevelFun #-}

loadObject :: (Topper m, Mut n) => FunObjCodeName n -> m n NativeFunction
loadObject fname =
  lookupLoadedObject fname >>= \case
    Just p -> return p
    Nothing -> do
      (objCode, LinktimeNames funNames ptrNames) <- lookupFunObjCode fname
      funVals <- forM funNames \name -> nativeFunPtr <$> loadObject name
      ptrVals <- forM ptrNames \name -> snd <$> lookupPtrName name
      dyvarStores <- getRuntimeEnv
      f <- liftIO $ linkFunObjCode objCode dyvarStores
        $ LinktimeVals funVals ptrVals
      extendLoadedObjects fname f
      return f

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

specializedFunCoreDefinition
  :: (MonadFail1 m, EnvReader m) => CAtomName n -> m n (LamExpr CoreIR n)
specializedFunCoreDefinition fname = do
  TopFunBound ty (SpecializedTopFun s) <- lookupAtomName fname
  case s of
    AppSpecialization f abStaticArgs@(Abs bs _) -> do
      f' <- forceDeferredInlining f
      liftBuilder $ buildNaryLamExprFromPi ty \allArgs -> do
        let (extraArgs, originalArgs) = splitAt (nestLength bs) (toList allArgs)
        ListE staticArgs' <- applyNaryAbs (sink abStaticArgs) extraArgs
        naryApp (sink f') $ staticArgs' <> map Var originalArgs

-- This is needed to avoid an infinite loop. Otherwise, in simplifyTopFunction,
-- where we eta-expand and try to simplify `App f args`, we would see `f` as a
-- "noinline" function and defer its simplification.
forceDeferredInlining :: EnvReader m => CAtomName n -> m n (CAtom n)
forceDeferredInlining v =
  lookupAtomName v >>= \case
    TopFunBound _ (AwaitingSpecializationArgsTopFun _ f) -> return f
    _ -> return $ Var v

toCFunction
  :: (Topper m, Mut n) => NameHint -> ImpFunction n -> m n (FunObjCodeName n)
toCFunction nameHint impFun = do
  logger  <- getFilteredLogger
  (closedImpFun, reqFuns, reqPtrNames) <- abstractLinktimeObjects impFun
  obj <- impToLLVM logger nameHint closedImpFun >>= compileToObjCode
  reqObjNames <- mapM impNameToObj reqFuns
  emitObjFile nameHint obj (LinktimeNames reqObjNames reqPtrNames)

getLLVMOptLevel :: EvalConfig -> LLVMOptLevel
getLLVMOptLevel cfg = case optLevel cfg of
  NoOptimize -> OptALittle
  Optimize   -> OptAggressively

evalLLVM :: forall n m. (Topper m, Mut n) => DestBlock n -> m n (SAtom n)
evalLLVM block = do
  backend <- backendName <$> getConfig
  logger  <- getFilteredLogger
  let (cc, _needsSync) =
        case backend of LLVMCUDA -> (EntryFunCC CUDARequired   , True )
                        _        -> (EntryFunCC CUDANotRequired, False)
  impFun <- checkPass ImpPass $ blockToImpFunction backend cc block
  let IFunType _ _ resultTypes = impFunType impFun
  (closedImpFun, reqFuns, reqPtrNames) <- abstractLinktimeObjects impFun
  obj <- impToLLVM logger "main" closedImpFun >>= compileToObjCode
  reqFunPtrs  <- forM reqFuns impNameToPtr
  reqDataPtrs <- forM reqPtrNames \v -> snd <$> lookupPtrName v
  dyvarStores <- getRuntimeEnv
  benchRequired <- requiresBench <$> getPassCtx
  nativeFun <- liftIO $ linkFunObjCode obj dyvarStores
    $ LinktimeVals reqFunPtrs reqDataPtrs
  resultVals <-
    liftIO $ callNativeFun nativeFun benchRequired logger [] resultTypes
  resultTy <- getDestBlockType block
  result <- repValFromFlatList resultTy resultVals
  Var <$> emitBinding "data" (AtomNameBinding $ TopDataBound result)
{-# SCC evalLLVM #-}

compileToObjCode
  :: Topper m => WithCNameInterface LLVM.AST.Module -> m n FunObjCode
compileToObjCode astWithNames = forM astWithNames \ast -> do
  logger  <- getFilteredLogger
  opt <- getLLVMOptLevel <$> getConfig
  liftIO $ compileLLVM logger opt ast (cniMainFunName astWithNames)

impNameToPtr :: (Topper m, Mut n) => ImpFunName n -> m n (FunPtr ())
impNameToPtr v = nativeFunPtr <$> (loadObject =<< impNameToObj v)

impNameToObj
  :: (EnvReader m, Fallible1 m) => ImpFunName n -> m n (FunObjCodeName n)
impNameToObj v = do
  queryObjCache v >>= \case
    Just v' -> return v'
    Nothing -> throw CompilerErr
      $ "Expected to find an object cache entry for: " ++ pprint v

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
#ifdef DEX_DEBUG
  logTop $ MiscLog $ "Running checks"
  let allowedEffs = case name of
                      LowerPass    -> OneEffect InitEffect
                      LowerOptPass -> OneEffect InitEffect
                      VectPass     -> OneEffect InitEffect
                      _            -> mempty
  {-# SCC afterPassTypecheck #-} (liftExcept =<<) $ liftEnvReaderT $
    withAllowedEffects allowedEffs $ checkTypesM result
  logTop $ MiscLog $ "Checks passed"
#else
  logTop $ MiscLog $ "Checks skipped (not a debug build)"
#endif
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
  collectGarbage (RecSubstFrag defs) ruleFreeVars cache
    \defsFrag'@(RecSubstFrag defs') cache' -> do
      let liveNames = toNameSet $ toScopeFrag defsFrag'
      let rules' = unsafeCoerceE $ CustomRules
           $ M.filterWithKey (\k _ -> k `isInNameSet` liveNames) rules
      defs'' <- snapshotPtrs (RecSubst defs')
      return $ TopSerializedStateEx $ SerializedEnv defs'' rules' cache'
  where
    ruleFreeVars v = case M.lookup v rules of
      Nothing -> mempty
      Just r  -> freeVarsE r

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
    result' `PairE` ListE names `PairE` ListE dictNames <- TopperM $ emitEnv $
      Abs frag $ result
         `PairE` ListE (boundNamesList frag)
         `PairE` ListE (boundNamesList frag)
    evalSpecializations names dictNames
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

instance HasPtrs TopStateEx where
  -- TODO: rather than implementing HasPtrs for safer names, let's just switch
  --       to using names for pointers.
  traversePtrs _ s = pure s
