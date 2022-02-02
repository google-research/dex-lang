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
  EvalConfig (..),
  evalSourceBlock, evalFile, MonadInterblock (..), InterblockM,
  evalSourceText, runInterblockM, execInterblockM, initTopState, TopStateEx (..),
  evalInterblockM, evalSourceBlockIO) where

import Data.Functor
import Control.Monad.State.Strict
import Control.Monad.Catch
import Control.Monad.Reader
import Data.Text.Prettyprint.Doc
import Data.Store (Store)
import Data.List (partition)
import qualified Data.Map.Strict as M
import GHC.Generics (Generic (..))
import System.FilePath

import Paths_dex  (getDataFileName)

import Err
import Logging
import LLVMExec
import PPrint()
import Util (measureSeconds, onFst, onSnd)
import Serialize (HasPtrs (..), pprintVal, getDexString)

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

-- === shared effects ===

data EvalConfig = EvalConfig
  { backendName :: Backend
  , libPath     :: Maybe FilePath
  , logFile     :: Maybe FilePath }

class Monad m => ConfigReader m where
  getConfig :: m EvalConfig

-- === monad for wiring together the source blocks ===

-- Hides the `n` parameter as an existential
data TopStateEx where
  TopStateEx :: Distinct n => Env n -> TopStateEx

class (ConfigReader m, MonadIO m) => MonadInterblock m where
  getTopStateEx :: m TopStateEx
  setTopStateEx :: TopStateEx -> m ()

  getImportStatus :: ModuleName -> m (Maybe ModuleImportStatus)
  setImportStatus :: ModuleName -> ModuleImportStatus -> m ()

newtype InterblockM a = InterblockM
  { runInterblockM' :: ReaderT EvalConfig (StateT (ModulesImported, TopStateEx) IO) a }
    deriving (Functor, Applicative, Monad, MonadIO, MonadMask, MonadThrow, MonadCatch)

runInterblockM :: EvalConfig -> TopStateEx -> InterblockM a -> IO (a, TopStateEx)
runInterblockM opts env m = do
  (ans, (_, finalState)) <- runStateT (runReaderT (runInterblockM' m) opts) (mempty, env)
  return (ans, finalState)

evalInterblockM :: EvalConfig -> TopStateEx -> InterblockM a -> IO a
evalInterblockM opts env m = fst <$> runInterblockM opts env m

execInterblockM :: EvalConfig -> TopStateEx -> InterblockM a -> IO TopStateEx
execInterblockM opts env m = snd <$> runInterblockM opts env m

-- === monad for wiring together the passes within each source block ===

class ( forall n. Fallible (m n)
      , forall n. MonadLogger [Output] (m n)
      , forall n. ConfigReader (m n)
      , forall n. MonadIO (m n)  -- TODO: something more restricted here
      , EnvReader m
      , TopBuilder m )
      => MonadPasses (m::MonadKind1) where
  logPass :: Pretty a => PassName -> m n a -> m n a
  requireBenchmark :: m n Bool

type RequiresBench = Bool
type PassCtx = (RequiresBench, Maybe PassName, EvalConfig)

newtype PassesM (n::S) a = PassesM
  { runPassesM' :: TopBuilderT (ReaderT PassCtx (LoggerT [Output] IO)) n a }
    deriving ( Functor, Applicative, Monad, MonadIO, MonadFail
             , Fallible, EnvReader, ScopeReader)

type ModulesImported = M.Map ModuleName ModuleImportStatus

data ModuleImportStatus = CurrentlyImporting | FullyImported  deriving Generic

runPassesM :: Distinct n => Bool -> EvalConfig -> Env n -> PassesM n a -> IO (Except a, [Output])
runPassesM bench opts env m = do
  let maybeLogFile = logFile opts
  runLogger maybeLogFile \l ->
    catchIOExcept $ runLoggerT l $
      runReaderT (runTopBuilderT env $ runPassesM' m) (bench, Nothing, opts)

-- ======

initTopState :: TopStateEx
initTopState = TopStateEx emptyOutMap

evalSourceBlockIO :: EvalConfig -> TopStateEx -> SourceBlock -> IO (Result, Maybe TopStateEx)
evalSourceBlockIO opts env block = do
  (ans, env') <- runInterblockM opts env $ evalSourceBlock block
  return (ans, Just env')

evalSourceText :: MonadInterblock m => String -> m [(SourceBlock, Result)]
evalSourceText source = do
  let sourceBlocks = parseProg source
  results <- mapM evalSourceBlock sourceBlocks
  return $ zip sourceBlocks results

liftPassesM :: MonadInterblock m
            => Bool
            -> (forall n. Mut n => PassesM n ())
            -> m Result
liftPassesM bench m = do
  opts <- getConfig
  TopStateEx env <- getTopStateEx
  (result, outs) <- liftIO $ runPassesM bench opts env do
    localTopBuilder $ m >> return UnitE
  case result of
    Success (Abs bindingsFrag UnitE) -> do
      setTopStateEx $ runEnvReaderM env do
        liftM fromLiftE $ refreshAbs (Abs bindingsFrag UnitE)
          \bindingsFrag' UnitE ->
            return $ LiftE $ TopStateEx $ extendOutMap env bindingsFrag'
      return $ Result outs (Success ())
    Failure errs -> do
      return $ Result outs (Failure errs)

evalSourceBlock :: MonadInterblock m => SourceBlock -> m Result
evalSourceBlock (SourceBlock _ _ _ _ (ImportModule moduleName)) = do
  moduleStatus <- getImportStatus moduleName
  case moduleStatus of
    Just CurrentlyImporting -> return $ Result [] $
      throw MiscErr $ "Circular import detected: " ++ pprint moduleName
    Just FullyImported -> return emptyResult
    Nothing -> do
      fullPath <- findModulePath moduleName
      source <- liftIO $ readFile fullPath
      setImportStatus moduleName CurrentlyImporting
      results <- mapM evalSourceBlock $ parseProg source
      setImportStatus moduleName FullyImported
      return $ summarizeModuleResults results
evalSourceBlock block = do
  result <- withCompileTime $ liftPassesM (requiresBench block) $ evalSourceBlock' block
  return $ filterLogs block $ addResultCtx block $ result

evalSourceBlock' :: (Mut n, MonadPasses m) => SourceBlock -> m n ()
evalSourceBlock' block = case sbContents block of
  EvalUDecl decl ->
    execUDecl decl
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
      logTop $ TextOut $ pprint ty
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
        emitSourceMap $ SourceMap $ M.singleton sourceName (UAtomVar vCore)
  GetNameType v -> do
    ty <- sourceNameType v
    logTop $ TextOut $ pprint ty
  ImportModule _ -> error "should be handled at the inter-block level"
  QueryEnv query -> void $ runEnvQuery query $> UnitE
  ProseBlock _ -> return ()
  CommentLine  -> return ()
  EmptyLines   -> return ()
  UnParseable _ s -> throw ParseErr s

runEnvQuery :: MonadPasses m => EnvQuery -> m n ()
runEnvQuery query = do
  env <- unsafeGetEnv
  case query of
    DumpSubst -> logTop $ TextOut $ pprint $ env
    InternalNameInfo name ->
      case lookupSubstFragRaw (fromRecSubst $ getNameEnv env) name of
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

requiresBench :: SourceBlock -> Bool
requiresBench block = case sbLogLevel block of
  PrintBench _ -> True
  _            -> False

filterLogs :: SourceBlock -> Result -> Result
filterLogs block (Result outs err) = let
  (logOuts, requiredOuts) = partition isLogInfo outs
  outs' = requiredOuts ++ processLogs (sbLogLevel block) logOuts
  in Result outs' err

summarizeModuleResults :: [Result] -> Result
summarizeModuleResults results =
  case [err | Result _ (Failure err) <- results] of
    [] -> Result allOuts $ Success ()
    errs -> Result allOuts $ throw ModuleImportErr $ foldMap pprint errs
  where allOuts = foldMap resultOutputs results

emptyResult :: Result
emptyResult = Result [] (Success ())

evalFile :: MonadInterblock m => FilePath -> m [(SourceBlock, Result)]
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

evalUType :: (Mut n, MonadPasses m) => UType VoidS -> m n (Type n)
evalUType ty = do
  logTop $ PassInfo Parse $ pprint ty
  renamed <- logPass RenamePass $ renameSourceNamesUExpr ty
  checkPass TypePass $ checkTopUType renamed

evalUExpr :: (Mut n, MonadPasses m) => UExpr VoidS -> m n (Atom n)
evalUExpr expr = do
  logTop $ PassInfo Parse $ pprint expr
  renamed <- logPass RenamePass $ renameSourceNamesUExpr expr
  typed <- checkPass TypePass $ inferTopUExpr renamed
  evalBlock typed

evalBlock :: (Mut n, MonadPasses m) => Block n -> m n (Atom n)
evalBlock typed = do
  synthed <- checkPass SynthPass $ synthTopBlock typed
  SimplifiedBlock simp recon <- checkPass SimpPass $ simplifyTopBlock synthed
  result <- evalBackend simp
  applyRecon recon result

execUDecl :: (Mut n, MonadPasses m) => UDecl VoidS VoidS -> m n ()
execUDecl decl = do
  logTop $ PassInfo Parse $ pprint decl
  Abs renamedDecl sourceMap <- logPass RenamePass $ renameSourceNamesUDecl decl
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

compileTopLevelFun :: (Mut n, MonadPasses m) => NameHint -> Atom n -> m n (Atom n)
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

toCFunction :: (Mut n, MonadPasses m) => SourceName -> ImpFunction n -> m n (CFun n)
toCFunction fname f = do
  (deps, m) <- impToLLVM fname f
  objFile <- liftIO $ exportObjectFileVal deps m fname
  objFileName <- emitObjFile (getNameHint fname) objFile
  return $ CFun fname objFileName

emitObjFile :: (Mut n, TopBuilder m) => NameHint -> ObjectFile n -> m n (ObjectFileName n)
emitObjFile hint objFile = do
  v <- emitBinding hint $ ObjectFileBinding objFile
  emitNamelessEnv $ TopEnvFrag emptyOutFrag mempty mempty mempty (eMapSingleton v UnitE)
  return v

-- TODO: there's no guarantee this name isn't already taken. Need a better story
-- for C/LLVM function names
mainFuncName :: SourceName
mainFuncName = "entryFun"

evalLLVM :: (Mut n, MonadPasses m) => Block n -> m n (Atom n)
evalLLVM block = do
  backend <- backendName <$> getConfig
  bench   <- requireBenchmark
  (blockAbs, ptrVals) <- abstractPtrLiterals block
  let (cc, needsSync) = case backend of LLVMCUDA -> (EntryFun CUDARequired   , True )
                                        _        -> (EntryFun CUDANotRequired, False)
  ImpFunctionWithRecon impFun reconAtom <- checkPass ImpPass $
                                             toImpFunction backend cc blockAbs
  (_, llvmAST) <- impToLLVM mainFuncName impFun
  let IFunType _ _ resultTypes = impFunType impFun
  let llvmEvaluate = if bench then compileAndBench needsSync else compileAndEval
  logger  <- getLogger
  objFileNames <- withEnv getObjFiles
  objFiles <- forM (eMapToList objFileNames) \(objFileName, UnitE) -> do
    ObjectFileBinding objFile <- lookupEnv objFileName
    return objFile
  resultVals <- liftIO $ llvmEvaluate logger objFiles
                  llvmAST mainFuncName ptrVals resultTypes
  resultValsNoPtrs <- mapM litValToPointerlessAtom resultVals
  applyNaryAbs reconAtom $ map SubstVal resultValsNoPtrs

evalBackend :: (Mut n, MonadPasses m) => Block n -> m n (Atom n)
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

withCompileTime :: MonadInterblock m => m Result -> m Result
withCompileTime m = do
  (Result outs err, t) <- measureSeconds m
  return $ Result (outs ++ [TotalTime t]) err

checkPass :: (MonadPasses m, Pretty (e n), CheckableE e)
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

logTop :: MonadPasses m => Output -> m n ()
logTop x = logIO [x]

findModulePath :: MonadInterblock m => ModuleName -> m FilePath
findModulePath moduleName = do
  let fname = moduleName ++ ".dx"
  specifiedPath <- libPath <$> getConfig
  case specifiedPath of
    Nothing -> liftIO $ getDataFileName $ "lib/" ++ fname
    Just path -> return $ path </> fname

-- === instances ===

instance ConfigReader (PassesM n) where
  getConfig = PassesM $ asks \(_, _, cfg) -> cfg

instance TopBuilder PassesM where
  -- Log bindings as they are emitted
  emitBinding hint binding = do
    name <- PassesM $ emitBinding hint binding
    logTop $ MiscLog $ "=== Top name ===\n" ++ pprint name ++ " =\n"
                      ++ pprint binding ++ "\n===\n"
    return name

  emitEnv env = PassesM $ emitEnv env
  emitNamelessEnv env = PassesM $ emitNamelessEnv env
  localTopBuilder cont = PassesM $ localTopBuilder $ runPassesM' cont

instance MonadPasses PassesM where
  requireBenchmark = PassesM $ asks \(bench, _, _) -> bench
  logPass passName cont = do
    logTop $ PassInfo passName $ "=== " <> pprint passName <> " ==="
    logTop $ MiscLog $ "Starting "++ pprint passName
    result <- PassesM $ local (\(bench, _, ctx) -> (bench, Just passName, ctx)) $
                runPassesM' cont
    logTop $ PassInfo passName $ "=== Result ===\n" <> pprint result
    return result

instance MonadLogger [Output] (PassesM n) where
  getLogger = PassesM $ lift1 $ lift $ getLogger

instance ConfigReader InterblockM where
  getConfig = InterblockM ask

instance MonadInterblock InterblockM where
  getTopStateEx = InterblockM $ gets snd
  setTopStateEx s = InterblockM $ modify $ onSnd $ const s

  getImportStatus name = InterblockM $ gets $ M.lookup name . fst
  setImportStatus name status = InterblockM $ modify $ onFst $ M.insert name status

instance Store ModuleImportStatus

instance Store TopStateEx

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
