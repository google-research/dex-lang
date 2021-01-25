-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveGeneric #-}

module TopLevel (evalSourceBlock, evalDecl, evalSource, evalFile,
                 initTopState, EvalConfig (..), TopState (..)) where

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

import Preamble
import Core
import Base

import Inference
import Interpreter
import Simplify
import Serialize
import Imp
import Imp.Optimize
import JIT
import Logging
import LLVMExec
import Parser
import Util (highlightRegion, measureSeconds)
import Optimize
import Parallelize

data EvalConfig = EvalConfig
  { backendName :: Backend
  , libPath     :: Maybe FilePath
  , logFile     :: Maybe FilePath
  }

data TopPassEnv = TopPassEnv
  { logService :: Logger [Output]
  , benchmark  :: Bool
  , evalConfig :: EvalConfig }

type TopPassM a = ReaderT TopPassEnv IO a

data ModuleImportStatus = CurrentlyImporting | FullyImported  deriving Generic

data TopState = TopState
  { topEnv          :: TopEnv ()
  , modulesImported :: M.Map ModuleName ModuleImportStatus}
    deriving Generic

initTopState :: TopState
initTopState = undefined -- TopState initBindings mempty

evalDecl :: EvalConfig -> SourceBlock -> StateT TopState IO Result
evalDecl opts block = do
  env <- get
  (env', ans) <- liftIO $ evalSourceBlock opts env $ block
  put $ env <> env'
  return ans

evalFile :: EvalConfig -> FilePath -> StateT TopState IO [(SourceBlock, Result)]
evalFile opts fname = do
  evalSource opts =<< (liftIO $ readFile fname)

evalSource :: EvalConfig -> FilePath -> StateT TopState IO [(SourceBlock, Result)]
evalSource opts source = do
  let sourceBlocks = parseProg source
  results <- mapM (evalDecl opts) sourceBlocks
  return $ zip sourceBlocks results

-- TODO: handle errors due to upstream modules failing
evalSourceBlock :: EvalConfig -> TopState -> SourceBlock -> IO (TopState, Result)
evalSourceBlock opts env block = do
  let bench = case sbLogLevel block of PrintBench _ -> True; _ -> False
  (ans, outs) <- runTopPassM bench opts $ withCompileTime $ evalSourceBlockM env block
  let (logOuts, requiredOuts) = partition isLogInfo outs
  let outs' = requiredOuts ++ processLogs (sbLogLevel block) logOuts
  case ans of
    Left err   -> return (mempty, Result outs' (Left (addCtx block err)))
    Right env' -> return (env'  , Result outs' (Right ()))

runTopPassM :: Bool -> EvalConfig -> TopPassM a -> IO (Except a, [Output])
runTopPassM bench opts m = runLogger (logFile opts) \logger ->
  runExceptT $ catchIOExcept $ runReaderT m $ TopPassEnv logger bench opts

evalSourceBlockM :: TopState -> SourceBlock -> TopPassM TopState
evalSourceBlockM topState@(TopState env _) block = case sbContents block of
  RunModule m -> do
    newEnv <- evalUModule env m
    return $ mempty { topEnv = newEnv }
  Command cmd (v, m) -> mempty <$ case cmd of
    EvalExpr fmt -> do
      val <- evalUModuleVal env v m
      case fmt of
        Printed -> do
          s <- liftIO $ pprintVal val
          logTop $ TextOut s
        RenderHtml -> do
          -- TODO: check types before we get here
          s <- liftIO $ getDexString val
          logTop $ HtmlOut s
    ExportFun name -> do
      f <- evalUModuleVal env v m
      void $ traverseLiterals f \val -> case val of
        PtrLit _ _ -> liftEitherIO $ throw CompilerErr $
          "Can't export functions with captured pointers (not implemented)."
        _ -> return $ Con $ Lit val
      logTop $ ExportedFun name f
    GetType -> do  -- TODO: don't actually evaluate it
      val <- evalUModuleVal env v m
      logTop $ TextOut $ pprint $ getType (topBindings env) val
  GetNameType v ->
    case envLookup (topSourceSubst env) v of
      Just val -> do
        let ty = getType (topBindings env) val
        logTop (TextOut $ pprint ty)
        return mempty
      _ -> liftEitherIO $ throw UnboundVarErr $ pprint v
  ImportModule moduleName ->
    case M.lookup moduleName $ modulesImported topState of
      Just CurrentlyImporting -> liftEitherIO $ throw MiscErr $
        "Circular import detected: " ++ pprint moduleName
      Just FullyImported -> return mempty
      Nothing -> do
        fullPath <- findModulePath moduleName
        source <- liftIO $ readFile fullPath
        newTopState <- evalSourceBlocks
                       (topState <> moduleStatus moduleName CurrentlyImporting) $
                       parseProg source
        return $ newTopState <> moduleStatus moduleName FullyImported
  UnParseable _ s -> liftEitherIO $ throw ParseErr s
  _               -> return mempty

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

evalSourceBlocks :: TopState -> [SourceBlock] -> TopPassM TopState
evalSourceBlocks env blocks = catFoldM evalSourceBlockM env blocks

evalUModuleVal :: TopEnv () -> SourceName -> UModule -> TopPassM (Atom ())
evalUModuleVal env v m = do
  env' <- evalUModule env m
  return $ topSourceSubst (env <> env') ! v

-- TODO: extract only the relevant part of the env we can check for module-level
-- unbound vars and upstream errors here. This should catch all unbound variable
-- errors, but there could still be internal shadowing errors.
evalUModule :: TopEnv () -> UModule -> TopPassM (TopEnv ())
evalUModule env untyped = do
  logPass Parse untyped
  typed <- liftEitherIO $ inferModule env untyped
  checkPass TypePass typed
  synthed <- liftEitherIO $ synthModule env typed
  -- TODO: check that the type of module exports doesn't change from here on
  checkPass SynthPass synthed
  let defunctionalized = simplifyModule env synthed
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
    -- Module _ Empty newBindings -> return newBindings
    _ -> do
      let (block, rest) = splitSimpModule env optimized
      result <- evalBackend env block
      newBindings <- liftIO $ evalModuleInterp mempty $ applyAbs rest result
      checkPass ResultPass $ Module Evaluated Empty newBindings
      return newBindings

evalBackend :: Bindings () -> Block () -> TopPassM (Atom ())
evalBackend = undefined
-- evalBackend env block = do
--   backend <- asks (backendName . evalConfig)
--   bench   <- asks benchmark
--   logger  <- asks logService
--   let (ptrBinders, ptrVals, block') = abstractPtrLiterals block
--   let funcName = "entryFun"
--   let mainName = Name TopFunctionName (fromString funcName) 0
--   let (cc, needsSync) = case backend of LLVMCUDA -> (EntryFun CUDARequired   , True )
--                                         _        -> (EntryFun CUDANotRequired, False)
--   let (mainFunc, impModuleUnoptimized, reconAtom) =
--         toImpModule env backend cc mainName ptrBinders Nothing block'
--   -- TODO: toImpModule might generate invalid Imp code, because GPU allocations
--   --       were not lifted from the kernels just yet. We should split the Imp IR
--   --       into different levels so that we can check the output here!
--   --checkPass ImpPass impModuleUnoptimized
--   let impModule = case backend of
--                     LLVMCUDA -> liftCUDAAllocations impModuleUnoptimized
--                     _        -> impModuleUnoptimized
--   checkPass ImpPass impModule
--   llvmAST <- liftIO $ impToLLVM logger impModule
--   let IFunType _ _ resultTypes = impFunType $ mainFunc
--   let llvmEvaluate = if bench then compileAndBench needsSync else compileAndEval
--   resultVals <- liftM (map (Con . Lit)) $ liftIO $
--     llvmEvaluate logger llvmAST funcName ptrVals resultTypes
--   return $ applyNaryAbs reconAtom resultVals

withCompileTime :: TopPassM a -> TopPassM a
withCompileTime m = do
  (ans, t) <- measureSeconds m
  logTop $ TotalTime t
  return ans

checkPass :: Pretty a => PassName -> a -> TopPassM ()
checkPass = undefined
-- checkPass name x = do
--   logPass name x
--   liftEitherIO $ checkValid x
--   logTop $ MiscLog $ pprint name ++ " checks passed"

logPass :: Pretty a => PassName -> a -> TopPassM ()
logPass passName x = logTop $ PassInfo passName $ pprint x

addCtx :: SourceBlock -> Err -> Err
addCtx block err@(Err e src s) = case src of
  Nothing -> err
  Just (start, stop) ->
    Err e Nothing $ s ++ "\n\n" ++ ctx
    where n = sbOffset block
          ctx = highlightRegion (start - n, stop - n) (sbText block)

logTop :: Output -> TopPassM ()
logTop x = do
  logger <- asks logService
  logThis logger [x]

abstractPtrLiterals :: Block () -> ([IBinder], [LitVal], Block ())
abstractPtrLiterals = undefined
-- abstractPtrLiterals block = flip evalState mempty $ do
--   block' <- traverseLiterals block \val -> case val of
--     PtrLit ty ptr -> do
--       ptrName <- gets $ M.lookup (ty, ptr) . fst
--       case ptrName of
--         Just v -> return $ Var $ Occ v $ getType (Con $ Lit val)
--         Nothing -> do
--           (varMap, usedNames) <- get
--           let name = genFresh (Name AbstractedPtrName "ptr" 0) usedNames
--           put ( varMap    <> M.insert (ty, ptr) name varMap
--               , usedNames <> (name @> ()))
--           return $ Var $ Occ name $ BaseTy (PtrType ty)
--     _ -> return $ Con $ Lit val
--   valsAndNames <- gets $ M.toAscList . fst
--   let impBinders = [(name , PtrType ty) | ((ty, _), name) <- valsAndNames]
--   let vals = map (uncurry PtrLit . fst) valsAndNames
--   return (impBinders, vals, block')

class HasTraversal e where
  traverseCore :: (MonadBuilder o m, MonadReader (Subst i o) m)
               => TraversalDef i o m -> e i -> m (e o)

instance HasTraversal Block where
  traverseCore = traverseBlock

instance HasTraversal Atom where
  traverseCore = traverseAtom

traverseLiterals :: forall i o m e. (HasTraversal e, Monad m)
                 => e i -> (LitVal -> m (Atom o)) -> m (e o)
traverseLiterals = undefined
-- traverseLiterals block f =
--     liftM fst $ flip runSubstBuilderT mempty $ traverseCore def block
--   where
--     def :: TraversalDef i o (SubstBuilderT i o m)
--     def = (traverseDecl def, traverseExpr def, traverseAtomLiterals)

--     traverseAtomLiterals :: Atom i -> (SubstBuilderT i o m) (Atom o)
--     traverseAtomLiterals atom = case atom of
--       Con (Lit x) -> lift $ lift $ f x
--       _ -> traverseAtom def atom

findModulePath :: ModuleName -> TopPassM FilePath
findModulePath moduleName = do
  let fname = moduleName ++ ".dx"
  specifiedPath <- asks (libPath . evalConfig)
  case specifiedPath of
    Nothing -> liftIO $ getDataFileName $ "lib/" ++ fname
    Just path -> return $ path </> fname

instance Semigroup TopState where
  (TopState env ms) <> (TopState env' ms') =
    -- Data.Map is left-biased so we flip the order
    TopState (env <> env') (ms' <> ms)

instance Monoid TopState where
  mempty = TopState mempty mempty

moduleStatus :: ModuleName -> ModuleImportStatus -> TopState
moduleStatus name status = mempty { modulesImported = M.singleton name status}

instance Store TopState
instance Store ModuleImportStatus
