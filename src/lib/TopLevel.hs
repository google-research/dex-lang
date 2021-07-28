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

module TopLevel (
  EvalConfig (..), TopState (..), initTopState,
  evalSourceBlock, evalFile, MonadInterblock, InterblockM,
  evalSourceText, runInterblockM, execInterblockM,
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

import Paths_dex  (getDataFileName)

import Err
import Syntax
import Builder
import Env
import SourceRename
import Type
import Inference
import Interpreter
import Simplify
import Serialize
import Imp
import Imp.Optimize
import JIT
import Logging
import LLVMExec
import PPrint()
import Parser
import Util (highlightRegion, measureSeconds)
import Optimize
import Parallelize

#if DEX_LLVM_VERSION == HEAD
import Data.Foldable
import MLIR.Lower
import MLIR.Eval
#endif

-- === monad for wiring together the source blocks ===

-- import qualified SaferNames.Syntax as S

type MonadInterblock m = ( MonadReader EvalConfig m
                         , MonadState TopState m
                         , MonadIO m )

data TopState = TopState
  { topBindings        :: Bindings
  , topSynthCandidates :: SynthCandidates
  , topSourceMap       :: SourceMap
  , modulesImported    :: ModulesImported }
    deriving Generic

initTopState :: TopState
initTopState = TopState mempty mempty mempty mempty

data EvalConfig = EvalConfig
  { backendName :: Backend
  , libPath     :: Maybe FilePath
  , logFile     :: Maybe FilePath }

type InterblockM = ReaderT EvalConfig (StateT TopState IO)

runInterblockM :: EvalConfig -> TopState -> InterblockM a -> IO (a, TopState)
runInterblockM opts env m = runStateT (runReaderT m opts) env

evalInterblockM :: EvalConfig -> TopState -> InterblockM a -> IO a
evalInterblockM opts env m = evalStateT (runReaderT m opts) env

execInterblockM :: EvalConfig -> TopState -> InterblockM a -> IO TopState
execInterblockM opts env m = execStateT (runReaderT m opts) env

-- === monad for wiring together the passes within each source block ===

type MonadPasses m = ( MonadReader TopPassEnv m
                     , MonadErr m
                     , MonadLogger [Output] m
                     , MonadIO m )

data TopPassEnv = TopPassEnv
  { topState   :: TopState
  , benchmark  :: Bool
  , evalConfig :: EvalConfig }

newtype PassesM a = PassesM (ReaderT TopPassEnv (LoggerT [Output] IO) a)
                            deriving (Functor, Applicative, Monad, MonadIO)

type ModulesImported = M.Map ModuleName ModuleImportStatus

data ModuleImportStatus = CurrentlyImporting | FullyImported  deriving Generic

runPassesM :: Bool -> EvalConfig -> TopState -> PassesM a -> IO (Except a, [Output])
runPassesM bench opts env (PassesM m) = do
  let maybeLogFile = logFile opts
  let passEnv = TopPassEnv env bench opts
  runLogger maybeLogFile \l ->
     runExceptT $ catchIOExcept $ runLoggerT l $ runReaderT m passEnv

-- ======

evalSourceBlockIO :: EvalConfig -> TopState -> SourceBlock -> IO (Result, Maybe TopState)
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
  results <- mapM evalSourceBlock  sourceBlocks
  return $ zip sourceBlocks results

extendTopState :: EvaluatedModule -> TopState -> TopState
extendTopState m (TopState scope scs sourceMap imported) =
  -- ensure the internal bindings are fresh wrt top bindings
  let EvaluatedModule bindings' scs' sourceMap' = subst (mempty, scope) m
  in TopState (scope <> bindings') (scs <> scs') (sourceMap <> sourceMap') imported

liftPassesM :: MonadInterblock m => Bool -> PassesM a -> m (Except a, [Output])
liftPassesM bench m = do
  opts <- ask
  env <- get
  liftIO $ runPassesM bench opts env m

liftPassesM_ :: MonadInterblock m => Bool -> PassesM () -> m Result
liftPassesM_ bench m = do
  (maybeAns, outs) <- liftPassesM bench m
  return $ Result outs maybeAns

evalSourceBlock :: MonadInterblock m => SourceBlock -> m Result
evalSourceBlock block = do
  result <- withCompileTime $ evalSourceBlock' block
  return $ filterLogs block $ addResultCtx block $ result

evalSourceBlock' :: MonadInterblock m => SourceBlock -> m Result
evalSourceBlock' block = case sbContents block of
  RunModule m -> do
    (maybeEvaluatedModule, outs) <- liftPassesM (requiresBench block) $ evalUModule m
    case maybeEvaluatedModule of
      Left err -> return $ Result outs $ Left err
      Right evaluatedModule -> do
        modify $ extendTopState evaluatedModule
        return $ Result outs $ Right ()
  Command cmd (v, m) -> liftPassesM_ (requiresBench block) case cmd of
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
  GetNameType v -> liftPassesM_ False do
    SourceMap m <- asks $ topSourceMap . topState
    case M.lookup v m of
      Nothing -> throw UnboundVarErr $ pprint v
      Just v' -> do
        bindings <- asks $ topBindings . topState
        case envLookup bindings v' of
          Just (AtomBinderInfo ty _) -> do
            logTop (TextOut $ pprint ty)
          _ -> throw CompilerErr $ pprint v
  ImportModule moduleName -> do
    currentlyImported <- gets modulesImported
    case M.lookup moduleName currentlyImported of
      Just CurrentlyImporting -> liftPassesM_ False $ throw MiscErr $
        "Circular import detected: " ++ pprint moduleName
      Just FullyImported -> return emptyResult
      Nothing -> do
        fullPath <- findModulePath moduleName
        source <- liftIO $ readFile fullPath
        setImportStatus moduleName CurrentlyImporting
        results <- mapM evalSourceBlock $ parseProg source
        setImportStatus moduleName FullyImported
        return $ summarizeModuleResults results
  ProseBlock _ -> return emptyResult
  CommentLine  -> return emptyResult
  EmptyLines   -> return emptyResult
  UnParseable _ s -> liftPassesM_ False (throw ParseErr s)

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
  case [err | Result _ (Left err) <- results] of
    [] -> Result allOuts $ Right ()
    errs -> Result allOuts $ throw ModuleImportErr $ foldMap pprint errs
  where allOuts = foldMap resultOutputs results

emptyResult :: Result
emptyResult = Result [] (Right ())

setImportStatus :: MonadInterblock m => ModuleName -> ModuleImportStatus -> m ()
setImportStatus name status =
  modify \s -> s { modulesImported = M.insert name status $ modulesImported s }

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

evalUModuleVal :: MonadPasses m => SourceName -> SourceUModule -> m Atom
evalUModuleVal v m = do
   evaluated <- evalUModule m
   env <- asks topState
   result <- lookupSourceName (extendTopState evaluated env) v
   case result of
     AtomBinderInfo _ (LetBound _ (Atom atom)) -> return atom
     _ -> throw TypeErr $ "Not an atom name: " ++ pprint v

lookupSourceName :: MonadErr m => TopState -> SourceName -> m AnyBinderInfo
lookupSourceName (TopState bindings _ (SourceMap sourceMap) _) v =
  case M.lookup v sourceMap of
    Just name ->
      case envLookup bindings name of
        Just info -> return info
        _ -> throw CompilerErr $ pprint name
    _ -> throw UnboundVarErr $ pprint v

-- TODO: extract only the relevant part of the env we can check for module-level
-- unbound vars and upstream errors here. This should catch all unbound variable
-- errors, but there could still be internal shadowing errors.
evalUModule :: MonadPasses m => SourceUModule -> m EvaluatedModule
evalUModule sourceModule = do
  TopState bindings synthCandidates sourceMap _ <- asks topState
  logPass Parse sourceModule
  renamed <- renameSourceNames bindings sourceMap sourceModule
  logPass RenamePass renamed
  typed <- liftEither $ inferModule bindings renamed
  -- This is a (hopefully) no-op pass. It's here as a sanity check to test the
  -- safer names system while we're staging it in.
  typed' <- roundtripSaferNamesPass bindings typed
  checkPass TypePass typed'
  synthed <- liftEither $ synthModule bindings synthCandidates typed'
  -- TODO: check that the type of module exports doesn't change from here on
  checkPass SynthPass synthed
  let defunctionalized = simplifyModule bindings synthed
  checkPass SimpPass defunctionalized
  let stdOptimized = optimizeModule defunctionalized
  -- Apply backend specific optimizations
  backend <- asks (backendName . evalConfig)
  let optimized = case backend of
                    LLVMCUDA -> parallelizeModule stdOptimized
                    LLVMMC   -> parallelizeModule stdOptimized
                    _        -> stdOptimized
  checkPass OptimPass optimized
  case optimized of
    Module _ Empty result->
      return result
    _ -> do
      let (block, rest) = splitSimpModule bindings optimized
      result <- evalBackend block
      evaluated <- liftIO $ evalModuleInterp mempty $ applyAbs rest result
      checkPass ResultPass $ Module Evaluated Empty evaluated
      return evaluated

roundtripSaferNamesPass :: MonadError Err m => Bindings -> Module -> m Module
roundtripSaferNamesPass _ m = return m
-- roundtripSaferNamesPass env (Module ir decls bindings) = do
--   let env' = toSafeBindings env
--   let decls' = toSafeB decls
--   _ <- liftEither $ S.checkTypes env' $ S.Block S.UnitTy decls' (S.Atom S.UnitVal)
--   return $ Module ir (fromSafeB decls') bindings

-- TODO: Use the common part of LLVMExec for this too (setting up pipes, benchmarking, ...)
-- TODO: Standalone functions --- use the env!
evalMLIR :: MonadPasses m => Block -> m Atom
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

evalLLVM :: MonadPasses m => Block -> m Atom
evalLLVM block = do
  TopState env _ _ _ <- asks topState
  backend <- asks (backendName . evalConfig)
  bench   <- asks benchmark
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

evalBackend :: MonadPasses m => Block -> m Atom
evalBackend block = do
  backend <- asks (backendName . evalConfig)
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

checkPass :: (MonadPasses m, Pretty a, Checkable a) => PassName -> a -> m ()
checkPass name x = do
  scope <- topBindings <$> topState <$> ask
  logPass name x
  liftEither $ checkValid scope x
  logTop $ MiscLog $ pprint name ++ " checks passed"

logPass :: (MonadPasses m, Pretty a) => PassName -> a -> m ()
logPass passName x = logTop $ PassInfo passName $ pprint x


addResultCtx :: SourceBlock -> Result -> Result
addResultCtx block (Result outs maybeErr) = case maybeErr of
  Left err -> Result outs $ Left $ addCtx block err
  Right () -> Result outs $ Right ()

addCtx :: SourceBlock -> Err -> Err
addCtx block err@(Err e src s) = case src of
  Nothing -> err
  Just (start, stop) ->
    Err e Nothing $ s ++ "\n\n" ++ ctx
    where n = sbOffset block
          ctx = highlightRegion (start - n, stop - n) (sbText block)

logTop :: MonadPasses m => Output -> m ()
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
  specifiedPath <- asks libPath
  case specifiedPath of
    Nothing -> liftIO $ getDataFileName $ "lib/" ++ fname
    Just path -> return $ path </> fname

-- === instances ===

instance HasPtrs TopState where
  traversePtrs f (TopState bindings synthCandidates sourceMap status) =
    TopState <$> traverse (traversePtrs f) bindings
             <*> pure synthCandidates
             <*> pure sourceMap
             <*> pure status

instance Store TopState
instance Store ModuleImportStatus

instance MonadReader TopPassEnv PassesM where
  ask = PassesM ask
  local f (PassesM m) = PassesM $ local f m

instance MonadError Err PassesM where
  throwError err = liftEitherIO $ throwError err
  catchError (PassesM m) f = do
    env <- ask
    l <- getLogger
    result <- runExceptT $ catchIOExcept $ runLoggerT l $ runReaderT m env
    case result of
      Left e -> f e
      Right x -> return x

instance MonadLogger [Output] PassesM where
  getLogger = PassesM $ lift $ getLogger
