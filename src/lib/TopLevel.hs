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
-- disabling because some safer-names stuff lives under a preprocessor flag
{-# OPTIONS_GHC -Wno-unused-imports #-}

module TopLevel (
  EvalConfig (..),
  evalSourceBlock, evalFile, MonadInterblock (..), InterblockM,
  evalSourceText, runInterblockM, execInterblockM, initTopState, TopStateEx,
  evalInterblockM, lookupSourceName, evalSourceBlockIO) where

import Data.Functor
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Except hiding (Except)
import Data.Text.Prettyprint.Doc
import Data.String
import Data.List (partition)
import qualified Data.Map.Strict as M
import Data.Store (Store)
import GHC.Generics (Generic)
import System.FilePath
import System.Console.Haskeline -- for MonadException

import Paths_dex  (getDataFileName)

import Err
import Syntax as D
import Builder
import Env
import SourceRename
import Type
import Interpreter
import Simplify
import Serialize
import Imp
import Imp.Optimize
import JIT
import Logging
import LLVMExec
import PPrint()
import Util (measureSeconds, onFst, onSnd)
import Optimize
import Parallelize

#if DEX_LLVM_VERSION == HEAD
import Data.Foldable
import MLIR.Lower
import MLIR.Eval
#endif

import SaferNames.Bridge

import qualified SaferNames.Name                 as S
import qualified SaferNames.Parser               as S
import qualified SaferNames.Syntax               as S
import qualified SaferNames.Type                 as S
import qualified SaferNames.ResolveImplicitNames as S
import qualified SaferNames.SourceRename         as S
import qualified SaferNames.Inference            as S

-- === shared effects ===

data EvalConfig = EvalConfig
  { backendName :: Backend
  , libPath     :: Maybe FilePath
  , logFile     :: Maybe FilePath }

class Monad m => ConfigReader m where
  getConfig :: m EvalConfig

-- === monad for wiring together the source blocks ===

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
      , forall n. MonadIO (m n) )
      => MonadPasses (m::S.MonadKind1) where
  requireBenchmark :: m n Bool
  getTopState :: m n (S.DistinctWitness n, JointTopState n)

newtype PassesM (n::S.S) a = PassesM
  { runPassesM' :: ReaderT (Bool, EvalConfig, (S.DistinctWitness n, JointTopState n))
                     (LoggerT [Output] IO) a }
    deriving (Functor, Applicative, Monad, MonadIO, MonadFail, Fallible)

type ModulesImported = M.Map ModuleName ModuleImportStatus

data ModuleImportStatus = CurrentlyImporting | FullyImported  deriving Generic

runPassesM :: S.Distinct n => Bool -> EvalConfig -> JointTopState n -> PassesM n a -> IO (Except a, [Output])
runPassesM bench opts env m = do
  let maybeLogFile = logFile opts
  runLogger maybeLogFile \l ->
    catchIOExcept $ runLoggerT l $ runReaderT (runPassesM' m) $
      (bench, opts, (S.Distinct, env))

-- ======

initTopState :: TopStateEx
initTopState = emptyTopStateEx

evalSourceBlockIO :: EvalConfig -> TopStateEx -> S.SourceBlock -> IO (Result, Maybe TopStateEx)
evalSourceBlockIO opts env block = do
  (ans, env') <- runInterblockM opts env $ evalSourceBlock block
  if mayUpdateTopState block
    then return (ans, Just env')
    -- This case in an opimization for the cache. It lets us indicate that the
    -- state hasn't changed.
    else return (ans, Nothing)

evalSourceText :: MonadInterblock m => String -> m [(S.SourceBlock, Result)]
evalSourceText source = do
  let sourceBlocks = S.parseProg source
  results <- mapM evalSourceBlock  sourceBlocks
  return $ zip sourceBlocks results

liftPassesM :: MonadInterblock m => Bool -> (forall n. PassesM n a) -> m (Except a, [Output])
liftPassesM bench m = do
  opts <- getConfig
  TopStateEx env <- getTopStateEx
  liftIO $ runPassesM bench opts env m

liftPassesM_ :: MonadInterblock m => Bool -> (forall n. PassesM n ()) -> m Result
liftPassesM_ bench m = do
  (maybeAns, outs) <- liftPassesM bench m
  return $ Result outs maybeAns

evalSourceBlock :: MonadInterblock m => S.SourceBlock -> m Result
evalSourceBlock block = do
  result <- withCompileTime $ evalSourceBlock' block
  return $ filterLogs block $ addResultCtx block $ result

evalSourceBlock' :: MonadInterblock m => S.SourceBlock -> m Result
evalSourceBlock' block = case S.sbContents block of
  S.RunModule m -> do
    (maybeEvaluatedModule, outs) <- liftPassesM (requiresBench block) $ evalUModule m
    case maybeEvaluatedModule of
      Failure err -> return $ Result outs $ Failure err
      Success evaluatedModule -> do
        TopStateEx curState <- getTopStateEx
        setTopStateEx $ extendTopStateD curState evaluatedModule
        return $ Result outs $ Success ()
  S.Command cmd (v, m) -> liftPassesM_ (requiresBench block) case cmd of
    EvalExpr fmt -> do
      val <- evalUModuleVal v m
      case fmt of
        Printed -> do
          s <- liftIO $ pprintVal val
          logTop $ TextOut s
        RenderHtml -> do
          -- TODO: check types before we get here
          s <- liftIO $ getDexString val
          logTop $ HtmlOut s
    ExportFun name -> do
      f <- evalUModuleVal v m
      void $ traverseLiterals f \val -> case val of
        PtrLit _ _ -> throw CompilerErr $
          "Can't export functions with captured pointers (not implemented)."
        _ -> return $ Con $ Lit val
      logTop $ ExportedFun name f
    GetType -> do  -- TODO: don't actually evaluate it
      val <- evalUModuleVal v m
      logTop $ TextOut $ pprint $ getType val
  S.GetNameType v -> liftPassesM_ False do
    (S.Distinct, topState) <- getTopState
    let bindings = topStateS topState
    case S.runBindingsReaderT bindings $ S.sourceNameType v of
      Success ty -> logTop $ TextOut $ pprint ty
      Failure errs -> throwErrs errs
  S.ImportModule moduleName -> do
    moduleStatus <- getImportStatus moduleName
    case moduleStatus of
      Just CurrentlyImporting -> liftPassesM_ False $ throw MiscErr $
        "Circular import detected: " ++ pprint moduleName
      Just FullyImported -> return emptyResult
      Nothing -> do
        fullPath <- findModulePath moduleName
        source <- liftIO $ readFile fullPath
        setImportStatus moduleName CurrentlyImporting
        results <- mapM evalSourceBlock $ S.parseProg source
        setImportStatus moduleName FullyImported
        return $ summarizeModuleResults results
  S.QueryEnv query -> liftPassesM_ False $ runEnvQuery query
  S.ProseBlock _ -> return emptyResult
  S.CommentLine  -> return emptyResult
  S.EmptyLines   -> return emptyResult
  S.UnParseable _ s -> liftPassesM_ False (throw ParseErr s)

runEnvQuery :: MonadPasses m => S.EnvQuery -> m n ()
runEnvQuery query = do
  (_, curState) <- getTopState
  let bindings = topStateS curState
  case query of
    S.DumpEnv -> logTop $ TextOut $ pprint $ curState
    S.InternalNameInfo name ->
      case S.lookupEnvFragRaw (S.fromRecEnv $ S.getBindings bindings) name of
        Nothing -> throw UnboundVarErr $ pprint name
        Just (S.EnvVal _ binding) ->
          logTop $ TextOut $ pprint binding
    S.SourceNameInfo name -> do
      let S.SourceMap sourceMap = S.getSourceMap bindings
      case M.lookup name sourceMap of
        Nothing -> throw UnboundVarErr $ pprint name
        Just (S.EnvVal _ name') -> do
          let binding = S.lookupBindingsPure bindings name'
          logTop $ TextOut $ "Internal name: " ++ pprint name'
          logTop $ TextOut $ "Binding:\n"      ++ pprint binding

requiresBench :: S.SourceBlock -> Bool
requiresBench block = case S.sbLogLevel block of
  PrintBench _ -> True
  _            -> False

mayUpdateTopState :: S.SourceBlock -> Bool
mayUpdateTopState block = case S.sbContents block of
  S.RunModule _     -> True
  S.ImportModule _  -> True
  S.Command _ _     -> False
  S.GetNameType _   -> False
  S.ProseBlock _    -> False
  S.QueryEnv _      -> False
  S.CommentLine     -> False
  S.EmptyLines      -> False
  S.UnParseable _ _ -> False

filterLogs :: S.SourceBlock -> Result -> Result
filterLogs block (Result outs err) = let
  (logOuts, requiredOuts) = partition isLogInfo outs
  outs' = requiredOuts ++ processLogs (S.sbLogLevel block) logOuts
  in Result outs' err

summarizeModuleResults :: [Result] -> Result
summarizeModuleResults results =
  case [err | Result _ (Failure err) <- results] of
    [] -> Result allOuts $ Success ()
    errs -> Result allOuts $ throw ModuleImportErr $ foldMap pprint errs
  where allOuts = foldMap resultOutputs results

emptyResult :: Result
emptyResult = Result [] (Success ())

evalFile :: MonadInterblock m => FilePath -> m [(S.SourceBlock, Result)]
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

evalUModuleVal :: MonadPasses m => S.SourceName -> S.SourceUModule -> m n Atom
evalUModuleVal v m = do
   evaluated <- evalUModule m
   (S.Distinct, env) <- getTopState
   let finalState = extendTopStateD env evaluated
   result <- lookupSourceName finalState v
   case result of
     AtomBinderInfo _ (LetBound _ (Atom atom)) -> return atom
     _ -> throw TypeErr $ "Not an atom name: " ++ pprint v

lookupSourceName :: Fallible m => TopStateEx -> SourceName -> m AnyBinderInfo
lookupSourceName (TopStateEx topState) v =
  let D.TopState bindings _ (SourceMap sourceMap) = topStateD topState
  in case M.lookup v sourceMap of
    Just name ->
      case envLookup bindings name of
        Just info -> return info
        _ -> throw CompilerErr $ pprint name
    _ -> throw UnboundVarErr $ pprint v

-- TODO: extract only the relevant part of the env we can check for module-level
-- unbound vars and upstream errors here. This should catch all unbound variable
-- errors, but there could still be internal shadowing errors.
evalUModule :: MonadPasses m => S.SourceUModule -> m n EvaluatedModule
evalUModule sourceModule = do
  (S.Distinct, topState) <- getTopState
  let D.TopState bindingsD _ _ = topStateD topState
  let bindingsS@(S.Bindings _ _ sourceMapS _) = topStateS topState
  logPass Parse sourceModule
  renamed <- S.renameSourceNames (S.toScope bindingsS) sourceMapS sourceModule
  logPass RenamePass renamed
  typed <- liftExcept $ S.inferModule bindingsS renamed
  checkPassS TypePass typed
  synthed <- liftExcept $ S.synthModule bindingsS typed
  checkPassS SynthPass synthed
  let typedUnsafe = fromSafe topState synthed
  checkPass TypePass typedUnsafe
  let defunctionalized = simplifyModule bindingsD typedUnsafe
  checkPass SimpPass defunctionalized
  -- disabling due to a substitution bug that occurs in flipY in diagram.dx
  -- (safe-names version should catch it)
  -- let stdOptimized = optimizeModule defunctionalized
  let stdOptimized = defunctionalized
  -- Apply backend specific optimizations
  backend <- backendName <$> getConfig
  let optimized = case backend of
                    LLVMCUDA -> parallelizeModule stdOptimized
                    LLVMMC   -> parallelizeModule stdOptimized
                    _        -> stdOptimized
  checkPass OptimPass optimized
  case optimized of
    Module _ Empty result->
      return result
    _ -> do
      let (block, rest) = splitSimpModule bindingsD optimized
      result <- evalBackend block
      evaluated <- liftIO $ evalModuleInterp mempty $ applyAbs rest result
      checkPass ResultPass $ Module Evaluated Empty evaluated
      return evaluated

-- TODO: Use the common part of LLVMExec for this too (setting up pipes, benchmarking, ...)
-- TODO: Standalone functions --- use the env!
evalMLIR :: MonadPasses m => Block -> m n Atom
#if DEX_LLVM_VERSION == HEAD
evalMLIR block' = do
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
evalMLIR = error "Dex built without support for MLIR"
#endif

evalLLVM :: MonadPasses m => Block -> m n Atom
evalLLVM block = do
  (S.Distinct, topState) <- getTopState
  let env = topBindings $ topStateD topState
  backend <- backendName <$> getConfig
  bench   <- requireBenchmark
  logger  <- getLogger
  let (ptrBinders, ptrVals, block') = abstractPtrLiterals block
  let funcName = "entryFun"
  let mainName = Name TopFunctionName (fromString funcName) 0
  let (cc, needsSync) = case backend of LLVMCUDA -> (EntryFun CUDARequired   , True )
                                        _        -> (EntryFun CUDANotRequired, False)
  let (mainFunc, impModuleUnoptimized, reconAtom) =
        toImpModule env backend cc mainName ptrBinders Nothing block'
  -- TODO: toImpModule might generate invalid Imp code, because GPU allocations
  --       were not lifted from the kernels just yet. We should split the Imp IR
  --       into different levels so that we can check the output here!
  --checkPass ImpPass impModuleUnoptimized
  let impModule = case backend of
                    LLVMCUDA -> liftCUDAAllocations impModuleUnoptimized
                    _        -> impModuleUnoptimized
  checkPass ImpPass impModule
  llvmAST <- liftIO $ impToLLVM logger impModule
  let IFunType _ _ resultTypes = impFunType $ mainFunc
  let llvmEvaluate = if bench then compileAndBench needsSync else compileAndEval
  resultVals <- liftM (map (Con . Lit)) $ liftIO $
    llvmEvaluate logger llvmAST funcName ptrVals resultTypes
  return $ applyNaryAbs reconAtom resultVals

evalBackend :: MonadPasses m => Block -> m n Atom
evalBackend block = do
  backend <- backendName <$> getConfig
  let eval = case backend of
               MLIR        -> evalMLIR
               LLVM        -> evalLLVM
               LLVMMC      -> evalLLVM
               LLVMCUDA    -> evalLLVM
               Interpreter -> error "TODO"
  eval block


withCompileTime :: MonadInterblock m => m Result -> m Result
withCompileTime m = do
  (Result outs err, t) <- measureSeconds m
  return $ Result (outs ++ [TotalTime t]) err

checkPassS :: (MonadPasses m, Pretty (e n), S.CheckableE e) => PassName -> e n -> m n ()
checkPassS name x = do
  (S.Distinct, topState) <- getTopState
  let bindingsS = topStateS topState
  logPass name x
  liftExcept $ addContext ("Checking :\n" ++ pprint x) $
    S.runBindingsReaderT bindingsS $ S.checkTypes x
  logTop $ MiscLog $ pprint name ++ " checks passed"

checkPass :: (MonadPasses m, Pretty a, Checkable a) => PassName -> a -> m n ()
checkPass name x = do
  (S.Distinct, topState) <- getTopState
  let scope = topBindings $ topStateD topState
  logPass name x
  liftExcept $ checkValid scope x
  logTop $ MiscLog $ pprint name ++ " checks passed"

logPass :: (MonadPasses m, Pretty a) => PassName -> a -> m n ()
logPass passName x = logTop $ PassInfo passName $ pprint x

addResultCtx :: S.SourceBlock -> Result -> Result
addResultCtx block (Result outs errs) =
  Result outs (addSrcTextContext (S.sbOffset block) (S.sbText block) errs)

logTop :: MonadPasses m => Output -> m n ()
logTop x = logIO [x]

abstractPtrLiterals :: Block -> ([IBinder], [LitVal], Block)
abstractPtrLiterals block = flip evalState mempty $ do
  block' <- traverseLiterals block \val -> case val of
    PtrLit ty ptr -> do
      ptrName <- gets $ M.lookup (ty, ptr) . fst
      case ptrName of
        Just v -> return $ Var $ v :> getType (Con $ Lit val)
        Nothing -> do
          (varMap, usedNames) <- get
          let name = genFresh (Name AbstractedPtrName "ptr" 0) usedNames
          put ( varMap    <> M.insert (ty, ptr) name varMap
              , usedNames <> (name @> ()))
          return $ Var $ name :> BaseTy (PtrType ty)
    _ -> return $ Con $ Lit val
  valsAndNames <- gets $ M.toAscList . fst
  let impBinders = [Bind (name :> PtrType ty) | ((ty, _), name) <- valsAndNames]
  let vals = map (uncurry PtrLit . fst) valsAndNames
  return (impBinders, vals, block')

class HasTraversal a where
  traverseCore :: (MonadBuilder m, MonadReader SubstEnv m) => TraversalDef m -> a -> m a

instance HasTraversal Block where
  traverseCore = traverseBlock

instance HasTraversal Atom where
  traverseCore = traverseAtom

traverseLiterals :: (HasTraversal e, Monad m) => e -> (LitVal -> m Atom) -> m e
traverseLiterals block f =
    liftM fst $ runSubstBuilderT mempty mempty $ traverseCore def block
  where
    def = (traverseDecl def, traverseExpr def, traverseAtomLiterals)
    traverseAtomLiterals atom = case atom of
      Con (Lit x) -> lift $ lift $ f x
      _ -> traverseAtom def atom

findModulePath :: MonadInterblock m => ModuleName -> m FilePath
findModulePath moduleName = do
  let fname = moduleName ++ ".dx"
  specifiedPath <- libPath <$> getConfig
  case specifiedPath of
    Nothing -> liftIO $ getDataFileName $ "lib/" ++ fname
    Just path -> return $ path </> fname

-- === instances ===

instance ConfigReader (PassesM n) where
  getConfig = PassesM $ asks \(_, cfg, _) -> cfg

instance MonadPasses PassesM where
  requireBenchmark = PassesM $ asks \(bench, _, _) -> bench
  getTopState      = PassesM $ asks \(_    , _, s) -> s

instance MonadLogger [Output] (PassesM n) where
  getLogger = PassesM $ lift $ getLogger

instance ConfigReader InterblockM where
  getConfig = InterblockM ask

instance MonadInterblock InterblockM where
  getTopStateEx = InterblockM $ gets snd
  setTopStateEx s = InterblockM $ modify $ onSnd $ const s

  getImportStatus name = InterblockM $ gets $ M.lookup name . fst
  setImportStatus name status = InterblockM $ modify $ onFst $ M.insert name status

instance Store ModuleImportStatus
