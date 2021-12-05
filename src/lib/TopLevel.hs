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
import Control.Monad.Reader
import Data.Text.Prettyprint.Doc
import Data.Store (Store)
import Data.List (partition)
import qualified Data.Map.Strict as M
import GHC.Generics (Generic (..))
import System.FilePath
import System.Console.Haskeline -- for MonadException

import Paths_dex  (getDataFileName)

import Err
import Logging
import LLVMExec
import PPrint()
import Util (measureSeconds, onFst, onSnd)
import Serialize (HasPtrs (..), pprintVal, getDexString)

#if DEX_LLVM_VERSION == HEAD
import Data.Foldable
import MLIR.Lower
import MLIR.Eval
#endif

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
    deriving (Functor, Applicative, Monad, MonadIO, MonadException)

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
  requireBenchmark :: m n Bool

newtype PassesM (n::S) a = PassesM
  { runPassesM' :: TopBuilderT (ReaderT (Bool, EvalConfig) (LoggerT [Output] IO)) n a }
    deriving ( Functor, Applicative, Monad, MonadIO, MonadFail
             , Fallible, TopBuilder, EnvReader, ScopeReader)

type ModulesImported = M.Map ModuleName ModuleImportStatus

data ModuleImportStatus = CurrentlyImporting | FullyImported  deriving Generic

runPassesM :: Distinct n => Bool -> EvalConfig -> Env n -> PassesM n a -> IO (Except a, [Output])
runPassesM bench opts env m = do
  let maybeLogFile = logFile opts
  runLogger maybeLogFile \l ->
    catchIOExcept $ runLoggerT l $
      runReaderT (runTopBuilderT env $ runPassesM' m) (bench, opts)

-- ======

initTopState :: TopStateEx
initTopState = TopStateEx emptyOutMap

evalSourceBlockIO :: EvalConfig -> TopStateEx -> SourceBlock -> IO (Result, Maybe TopStateEx)
evalSourceBlockIO opts env block = do
  (ans, env') <- runInterblockM opts env $ evalSourceBlock block
  if mayUpdateTopState block
    then return (ans, Just env')
    -- This case in an opimization for the cache. It lets us indicate that the
    -- state hasn't changed.
    else return (ans, Nothing)

evalSourceText :: MonadInterblock m => String -> m [(SourceBlock, Result)]
evalSourceText source = do
  let sourceBlocks = parseProg source
  results <- mapM evalSourceBlock sourceBlocks
  return $ zip sourceBlocks results

liftPassesM :: MonadInterblock m
            => Bool -> Bool -- TODO: one bool is bad enough. but two!
            -> (forall n. Mut n => PassesM n ())
            -> m Result
liftPassesM mayUpdateState bench m = do
  opts <- getConfig
  TopStateEx env <- getTopStateEx
  (result, outs) <- liftIO $ runPassesM bench opts env do
    Immut <- return $ toImmutEvidence env
    localTopBuilder $ m >> return UnitE
  case result of
    Success (DistinctAbs bindingsFrag UnitE) -> do
      when mayUpdateState $
        setTopStateEx $ TopStateEx $ extendOutMap env bindingsFrag
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
  result <- withCompileTime $
              liftPassesM (mayUpdateTopState block) (requiresBench block) $
                evalSourceBlock' block
  return $ filterLogs block $ addResultCtx block $ result

evalSourceBlock' :: (Mut n, MonadPasses m) => SourceBlock -> m n ()
evalSourceBlock' block = case sbContents block of
  RunModule m -> execUModule m
  Command cmd (v, m) -> case cmd of
    EvalExpr fmt -> do
      execUModule m
      val <- lookupAtomSourceName v
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
      execUModule m
      val <- lookupAtomSourceName v
      ty <- getType val
      logTop $ TextOut $ pprint ty
  GetNameType v -> do
    ty <- sourceNameType v
    logTop $ TextOut $ pprint ty
  ImportModule _ -> error "should be handled at the inter-block level"
  QueryEnv query -> void $ liftImmut $ runEnvQuery query $> UnitE
  ProseBlock _ -> return ()
  CommentLine  -> return ()
  EmptyLines   -> return ()
  UnParseable _ s -> throw ParseErr s

runEnvQuery :: (Immut n, MonadPasses m) => EnvQuery -> m n ()
runEnvQuery query = do
  DB bindings <- getDB
  case query of
    DumpSubst -> logTop $ TextOut $ pprint $ bindings
    InternalNameInfo name ->
      case lookupSubstFragRaw (fromRecSubst $ getNameEnv bindings) name of
        Nothing -> throw UnboundVarErr $ pprint name
        Just (WithColor _ binding) ->
          logTop $ TextOut $ pprint binding
    SourceNameInfo name -> do
      let SourceMap sourceMap = getSourceMap bindings
      case M.lookup name sourceMap of
        Nothing -> throw UnboundVarErr $ pprint name
        Just (WithColor c name') -> do
          binding <- withNameColorRep c $ lookupEnv name'
          logTop $ TextOut $ "Internal name: " ++ pprint name'
          logTop $ TextOut $ "Binding:\n"      ++ pprint binding

requiresBench :: SourceBlock -> Bool
requiresBench block = case sbLogLevel block of
  PrintBench _ -> True
  _            -> False

mayUpdateTopState :: SourceBlock -> Bool
mayUpdateTopState block = case sbContents block of
  RunModule _     -> True
  ImportModule _  -> True
  Command _ _     -> False
  GetNameType _   -> False
  ProseBlock _    -> False
  QueryEnv _      -> False
  CommentLine     -> False
  EmptyLines      -> False
  UnParseable _ _ -> False

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


lookupAtomSourceName :: (Fallible1 m, EnvReader m) => SourceName -> m n (Atom n)
lookupAtomSourceName v =
  lookupSourceMap AtomNameRep v >>= \case
    Nothing -> throw UnboundVarErr $ pprint v
    Just v' -> do
      lookupAtomName v' >>= \case
        LetBound (DeclBinding _ _ (Atom atom)) -> return atom
        _ -> throw TypeErr $ "Not an atom name: " ++ pprint v

execUModule :: (Mut n, MonadPasses m) => SourceUModule -> m n ()
execUModule m = do
  bs <- liftImmut $ evalUModule m
  void $ emitEnv bs

-- TODO: extract only the relevant part of the env we can check for module-level
-- unbound vars and upstream errors here. This should catch all unbound variable
-- errors, but there could still be internal shadowing errors.
evalUModule :: (Immut n, MonadPasses m) => SourceUModule -> m n (EvaluatedModule n)
evalUModule sourceModule = do
  DB bindings <- getDB
  let (Env _ _ sourceMap _) = bindings
  logPass Parse sourceModule
  renamed <- renameSourceNames (toScope bindings) sourceMap sourceModule
  logPass RenamePass renamed
  typed <- liftExcept $ inferModule bindings renamed
  checkPass TypePass typed
  synthed <- liftExcept $ synthModule bindings typed
  checkPass SynthPass synthed
  let defunctionalized = simplifyModule bindings synthed
  checkPass SimpPass defunctionalized
  case defunctionalized of
    Module _ Empty result-> return result
    _ -> do
      let (block, recon) = splitSimpModule bindings defunctionalized
      fromDistinctAbs <$> localTopBuilder do
        -- TODO: the evaluation pass gets to emit top bindings because it
        -- creates bindings for pointer literals. But should we just do it this
        -- way for all the passes?
        result <- evalBackend $ sink block
        evaluated <- applyDataResults (sink recon) result
        checkPass ResultPass $ Module Evaluated Empty evaluated
        emitEnv evaluated

-- TODO: Use the common part of LLVMExec for this too (setting up pipes, benchmarking, ...)
-- TODO: Standalone functions --- use the env!
_evalMLIR :: MonadPasses m => Block n -> m n (Atom n)
#if DEX_LLVM_VERSION == HEAD
_evalMLIR block' = do
  -- This is a little silly, but simplification likes to leave inlinable
  -- let-bindings (they just construct atoms) in the block.
  let block = inlineTraverse block'
  let (moduleOp, recon@(Abs bs _)) = coreToMLIR block
  liftIO $ do
    let resultTypes = toList bs <&> binderAnn <&> \case BaseTy bt -> bt; _ -> error "Expected a base type"
    resultVals <- evalModule moduleOp [] resultTypes
    return $ applyNaryAbs recon $ Con . Lit <$> resultVals
  where
    inlineTraverse :: Block -> Block
    inlineTraverse block = fst $ flip runSubstBuilder mempty $ traverseBlock substTraversalDef block
#else
_evalMLIR = error "Dex built without support for MLIR"
#endif

evalLLVM :: (Mut n, MonadPasses m) => Block n -> m n (Atom n)
evalLLVM block = do
  backend <- backendName <$> getConfig
  bench   <- requireBenchmark
  logger  <- getLogger
  (blockAbs, ptrVals) <- abstractPtrLiterals block
  let funcName = "entryFun"
  let (cc, needsSync) = case backend of LLVMCUDA -> (EntryFun CUDARequired   , True )
                                        _        -> (EntryFun CUDANotRequired, False)
  (mainFunc, impModuleUnoptimized, reconAtom) <-
    toImpModule backend cc funcName Nothing blockAbs
  -- TODO: toImpModule might generate invalid Imp code, because GPU allocations
  --       were not lifted from the kernels just yet. We should split the Imp IR
  --       into different levels so that we can check the output here!
  checkPass ImpPass impModuleUnoptimized
  let impModule = case backend of
                    -- LLVMCUDA -> liftCUDAAllocations impModuleUnoptimized
                    _        -> impModuleUnoptimized
  -- checkPass ImpPass impModule
  llvmAST <- liftIO $ impToLLVM logger impModule
  let IFunType _ _ resultTypes = impFunType $ mainFunc
  let llvmEvaluate = if bench then compileAndBench needsSync else compileAndEval
  resultVals <- liftIO $ llvmEvaluate logger llvmAST funcName ptrVals resultTypes
  resultValsNoPtrs <- mapM litValToPointerlessAtom resultVals
  applyNaryAbs reconAtom $ map SubstVal resultValsNoPtrs

evalBackend :: (Mut n, MonadPasses m) => Block n -> m n (Atom n)
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
          => PassName -> e n -> m n ()
checkPass name x = do
  logPass name x
  addContext ("Checking :\n" ++ pprint x) $ checkTypes x
  logTop $ MiscLog $ pprint name ++ " checks passed"

logPass :: (MonadPasses m, Pretty a) => PassName -> a -> m n ()
logPass passName x = logTop $ PassInfo passName $ pprint x

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
  getConfig = PassesM $ asks \(_, cfg) -> cfg

instance MonadPasses PassesM where
  requireBenchmark = PassesM $ asks \(bench, _) -> bench

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
