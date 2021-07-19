-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveGeneric #-}

module TopLevel (evalSourceBlock, evalDecl, evalSource, evalFile,
                 EvalConfig (..), TopEnv (..)) where

import Control.Exception (throwIO)
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Except hiding (Except)
import qualified Data.Map.Strict as M
import Data.Text.Prettyprint.Doc
import Data.String
import Data.List (partition)
import qualified Data.Map.Strict as M
import Data.Store (Store)
import GHC.Generics (Generic)
import System.FilePath

import Debug.Trace

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
import PPrint
import Parser
import Util (highlightRegion, measureSeconds)
import Optimize
import Parallelize

-- import qualified SaferNames.Syntax as S

-- import SaferNames.Bridge

data EvalConfig = EvalConfig
  { backendName :: Backend
  , libPath     :: Maybe FilePath
  , logFile     :: Maybe FilePath
  }

data TopPassEnv = TopPassEnv
  { logService :: Logger [Output]
  , benchmark  :: Bool
  , evalConfig :: EvalConfig
  , topEnv     :: TopEnv }
type TopPassM a = ReaderT TopPassEnv IO a

data TopEnv = TopEnv
  { topBindings        :: Bindings
  , topSynthCandidates :: SynthCandidates
  , topSourceMap       :: SourceMap
  , modulesImported :: M.Map ModuleName ModuleImportStatus}
    deriving Generic

data ModuleImportStatus = CurrentlyImporting | FullyImported  deriving Generic

runTopPassM :: Bool -> EvalConfig -> TopEnv -> TopPassM a -> IO (Except a, [Output])
runTopPassM bench opts env m = runLogger (logFile opts) \logger ->
  runExceptT $ catchIOExcept $ runReaderT m $ TopPassEnv logger bench opts env

evalDecl :: EvalConfig -> SourceBlock -> StateT TopEnv IO Result
evalDecl opts block = do
  env <- get
  (m, ans) <- liftIO $ evalSourceBlock opts env $ block
  extendTopEnv m
  return ans

extendTopEnv :: MonadState TopEnv m => EvaluatedModule -> m ()
extendTopEnv m = do
  TopEnv scope scs sourceMap imported <- get
  -- ensure the internal bindings are fresh wrt top bindings
  let EvaluatedModule bindings' scs' sourceMap' = subst (mempty, scope) m
  put $ TopEnv (scope <> bindings') (scs <> scs') (sourceMap <> sourceMap') imported

evalFile :: EvalConfig -> FilePath -> StateT TopEnv IO [(SourceBlock, Result)]
evalFile opts fname = do
  evalSource opts =<< (liftIO $ readFile fname)

evalSource :: EvalConfig -> FilePath -> StateT TopEnv IO [(SourceBlock, Result)]
evalSource opts source = do
  let sourceBlocks = parseProg source
  results <- mapM (evalDecl opts) sourceBlocks
  return $ zip sourceBlocks results

-- TODO: handle errors due to upstream modules failing
evalSourceBlock :: EvalConfig -> TopEnv -> SourceBlock -> IO (EvaluatedModule, Result)
evalSourceBlock opts env block = do
  let bench = case sbLogLevel block of PrintBench _ -> True; _ -> False
  (ans, outs) <- runTopPassM bench opts env $ withCompileTime $ evalSourceBlockM block
  let (logOuts, requiredOuts) = partition isLogInfo outs
  let outs' = requiredOuts ++ processLogs (sbLogLevel block) logOuts
  case ans of
    Left  err       -> return (emptyEvaluatedModule, Result outs' (Left (addCtx block err)))
    Right evaluated -> return (evaluated           , Result outs' (Right ()))

-- evalSourceBlocks :: TopEnv -> [SourceBlock] -> TopPassM TopEnv
-- evalSourceBlocks = catFoldM (\env sb -> withCtx sb $ evalSourceBlockM env sb)
--   where
--     withCtx :: SourceBlock -> TopPassM a -> TopPassM a
--     withCtx sb m = do
--       topPassEnv <- ask
--       maybeResult <- runExceptT $ catchIOExcept $ runReaderT m topPassEnv
--       case maybeResult of
--         Left  err -> liftIO $ throwIO $ addCtx sb err
--         Right ans -> return ans

evalSourceBlockM :: SourceBlock -> TopPassM EvaluatedModule
evalSourceBlockM block = case sbContents block of
  RunModule m -> evalUModule m
  Command cmd (v, m) -> emptyEvaluatedModule <$ case cmd of
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
        PtrLit _ _ -> liftEitherIO $ throw CompilerErr $
          "Can't export functions with captured pointers (not implemented)."
        _ -> return $ Con $ Lit val
      logTop $ ExportedFun name f
    GetType -> do  -- TODO: don't actually evaluate it
      val <- evalUModuleVal v m
      logTop $ TextOut $ pprint $ getType val
  -- GetNameType v -> do
  --   bindings <- asks $ topBindings . topEnv
  --   case envLookup bindings v of
  --     Just (AtomBinderInfo ty _) -> logTop (TextOut $ pprint ty) >> return mempty
  --     _                          -> liftEitherIO $ throw UnboundVarErr $ pprint v
  -- ImportModule moduleName ->
  --   case M.lookup moduleName $ modulesImported env of
  --     Just CurrentlyImporting -> liftEitherIO $ throw MiscErr $
  --       "Circular import detected: " ++ pprint moduleName
  --     Just FullyImported -> return mempty
  --     Nothing -> do
  --       fullPath <- findModulePath moduleName
  --       source <- liftIO $ readFile fullPath
  --       newTopEnv <- evalSourceBlocks
  --                      (env <> moduleStatus moduleName CurrentlyImporting)
  --                      (parseProg source)
  --       return $ newTopEnv <> moduleStatus moduleName FullyImported
  ProseBlock _ -> return emptyEvaluatedModule
  CommentLine  -> return emptyEvaluatedModule
  EmptyLines   -> return emptyEvaluatedModule
  UnParseable _ s -> liftEitherIO $ throw ParseErr s

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

evalUModuleVal :: SourceName -> SourceUModule -> TopPassM Val
evalUModuleVal v m = do
  TopEnv bindings _ sourceMap _ <- asks topEnv
  EvaluatedModule bindings' _ sourceMap' <- evalUModule m
  liftEitherIO $ lookupSourceName (bindings<>bindings') (sourceMap<>sourceMap') v

lookupSourceName :: MonadErr m => Bindings -> SourceMap -> SourceName -> m Val
lookupSourceName bindings (SourceMap sourceMap) v =
  case M.lookup v sourceMap of
    Just name ->
      case envLookup bindings name of
        Just (AtomBinderInfo _ (LetBound _ (Atom atom))) -> return atom
        _ -> throw CompilerErr $ pprint name
    _ -> throw UnboundVarErr $ pprint v

-- TODO: extract only the relevant part of the env we can check for module-level
-- unbound vars and upstream errors here. This should catch all unbound variable
-- errors, but there could still be internal shadowing errors.
evalUModule :: SourceUModule -> TopPassM EvaluatedModule
evalUModule sourceModule = do
  TopEnv bindings synthCandidates sourceMap _ <- asks topEnv
  logPass Parse sourceModule
  renamed <- liftEitherIO $ renameSourceNames bindings sourceMap sourceModule
  logPass RenamePass renamed
  typed <- liftEitherIO $ inferModule bindings renamed
  -- This is a (hopefully) no-op pass. It's here as a sanity check to test the
  -- safer names system while we're staging it in.
  typed' <- liftEitherIO $ roundtripSaferNamesPass bindings typed
  checkPass TypePass typed'
  synthed <- liftEitherIO $ synthModule bindings synthCandidates typed'
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
      traceM $ "====================="
      traceM $ pprint block
      traceM $ "====================="
      result <- evalBackend bindings block
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

evalBackend :: Bindings -> Block -> TopPassM Atom
evalBackend env block = do
  backend <- asks (backendName . evalConfig)
  bench   <- asks benchmark
  logger  <- asks logService
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
  traceM $ "====================="
  traceM $ pprint impModule
  traceM $ "====================="
  checkPass ImpPass impModule
  llvmAST <- liftIO $ impToLLVM logger impModule
  let IFunType _ _ resultTypes = impFunType $ mainFunc
  let llvmEvaluate = if bench then compileAndBench needsSync else compileAndEval
  resultVals <- liftM (map (Con . Lit)) $ liftIO $
    llvmEvaluate logger llvmAST funcName ptrVals resultTypes
  return $ applyNaryAbs reconAtom resultVals

withCompileTime :: TopPassM a -> TopPassM a
withCompileTime m = do
  (ans, t) <- measureSeconds m
  logTop $ TotalTime t
  return ans

checkPass :: (Pretty a, Checkable a) => PassName -> a -> TopPassM ()
checkPass name x = do
  scope <- asks $ topBindings . topEnv
  logPass name x
  liftEitherIO $ checkValid scope x
  logTop $ MiscLog $ pprint name ++ " checks passed"

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

findModulePath :: ModuleName -> TopPassM FilePath
findModulePath moduleName = do
  let fname = moduleName ++ ".dx"
  specifiedPath <- asks (libPath . evalConfig)
  case specifiedPath of
    Nothing -> liftIO $ getDataFileName $ "lib/" ++ fname
    Just path -> return $ path </> fname

instance Semigroup TopEnv where
  (TopEnv env sm scs ms) <> (TopEnv env' sm' scs' ms') =
    -- Data.Map is left-biased so we flip the order
    TopEnv (env <> env') (sm <> sm') (scs <> scs') (ms' <> ms)

instance Monoid TopEnv where
  mempty = TopEnv mempty mempty mempty mempty

moduleStatus :: ModuleName -> ModuleImportStatus -> TopEnv
moduleStatus name status = mempty { modulesImported = M.singleton name status}

instance HasPtrs TopEnv where
  traversePtrs f (TopEnv bindings synthCandidates sourceMap status) =
    TopEnv <$> traverse (traversePtrs f) bindings
           <*> pure synthCandidates
           <*> pure sourceMap
           <*> pure status

instance Store TopEnv
instance Store ModuleImportStatus
