-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module TopLevel (runTopLevel, MonadTopBuilder (..), evalSourceText, evalFile,
                 TopLevel, evalSourceBlock, EvalConfig (..),
                 unsafeEvalSourceBlock, unsafeGetTopBindings, TopBuilderT (..),
                 initTopBindings, unsafeRunTopLevel) where

import Control.Monad.Reader
import System.Console.Haskeline  -- for MonadException
import Control.Monad.State.Strict
import Control.Monad.Except hiding (Except)
import Data.Foldable (fold)
import Data.Text.Prettyprint.Doc
import Data.String
import Data.List (partition)
import qualified Data.Map.Strict as M
import Data.Store (Store)
import GHC.Generics (Generic)
import System.FilePath
import Unsafe.Coerce

import Paths_dex  (getDataFileName)

import Prelude hiding ((.), id)
import Control.Category

import Syntax
import Builder
import Cat
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
import Type

import Env

import SaferNames.Name
import SaferNames.Bridge
import SaferNames.Syntax

import qualified SaferNames.LazyMap as LM

import qualified            Syntax as D
import qualified            Env    as D

import qualified SaferNames.Syntax as S
import qualified SaferNames.Name   as S

data EvalConfig = EvalConfig
  { backendName :: Backend
  , libPath     :: Maybe FilePath
  , logFile     :: Maybe FilePath }

type TopLevel n = TopBuilderT n (ReaderT EvalConfig (StateT ModuleStatuses IO))

initTopBindings :: TopBindings VoidScope
initTopBindings =
  TopBindings mempty (RecEnv voidScopeEnv) mempty (voidScopeEnv, mempty)

newtype TopBuilderT (n::S) (m :: * -> *) a = UnsafeMakeTopBuilderT
  { unsafeRunTopBuilderT :: StateT (TopBindings n) m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail, MonadException)

runTopBuilderT :: Monad m => (forall n. TopBuilderT n m a) -> m a
runTopBuilderT (UnsafeMakeTopBuilderT m) = evalStateT m initTopBindings

runTopLevel :: EvalConfig -> (forall n. TopLevel n a) -> IO a
runTopLevel opts m =
  flip evalStateT mempty $ flip runReaderT opts $ runTopBuilderT m

unsafeRunTopLevel :: EvalConfig -> UnsafeTopBindings -> TopLevel n a -> IO (a, UnsafeTopBindings)
unsafeRunTopLevel = undefined

-- === wiring together the source blocks ===

class Monad m => MonadTopBuilder n m | m -> n where
  extendTopBindingsM :: EvaluatedModule n -> m ()
  -- This CPS version isn't really any safer than just having
  -- `m (TopBindings n)`, but the idea is to encourage ourselves to only use
  -- the bindings in a limited scope. Eventually we might add the necessary
  -- foralls to make it actually safe.
  withTopBindings :: (TopBindings n -> m a) -> m a
  getSourceNameMap :: m (SourceNameMap n)

type MonadInterBlock n m =
       ( MonadTopBuilder n m
       , MonadIO m
       , MonadState ModuleStatuses m
       , MonadReader EvalConfig m)

type ModuleStatuses = M.Map ModuleName ModuleImportStatus

data ModuleImportStatus = CurrentlyImporting | FullyImported  deriving Generic

unsafeEvalSourceBlock :: EvalConfig -> UnsafeTopBindings -> SourceBlock
                      -> IO (UnsafeTopBindings, Result)
unsafeEvalSourceBlock = undefined

evalSourceBlock :: MonadInterBlock n m => SourceBlock -> m Result
evalSourceBlock block = case sbContents block of
  ImportModule moduleName -> do
    moduleStatus <- M.lookup moduleName <$> get
    case moduleStatus of
      Just CurrentlyImporting -> return $ Result [] $ throw MiscErr $
        "Circular import detected: " ++ pprint moduleName
      Just FullyImported -> return $ Result [] (Right ())
      Nothing -> do
        fullPath <- findModulePath moduleName
        source <- liftIO $ readFile fullPath
        modify $ M.insert moduleName CurrentlyImporting
        result <- evalSourceBlocks $ parseProg source
        modify $ M.insert moduleName FullyImported
        return result
  _ -> do
    opts <- ask
    withTopBindings \bindings -> do
      let passEnv = PassEnv
            { peEvalConfig = opts
            , peBindings = bindings
            , peLogService = error "not set"  -- TODO: something better
            , peBenchmark = case sbLogLevel block of PrintBench _ -> True; _ -> False }
      (ans, outs) <- liftIO $ runTopPassM passEnv $ evalSourceBlock' $ sbContents block
      let outs' = processLogs (sbLogLevel block) outs
      case ans of
        Left err   -> return $ Result outs' (Left (addCtx block err))
        Right evaluated -> do
          extendTopBindingsM evaluated
          return $ Result outs' (Right ())

evalSourceBlocks :: MonadInterBlock n m => [SourceBlock] -> m Result
evalSourceBlocks blocks = fold <$> mapM evalSourceBlock blocks

evalFile :: MonadInterBlock n m => FilePath -> m [(SourceBlock, Result)]
evalFile fname = evalSourceText =<< (liftIO $ readFile fname)

evalSourceText :: MonadInterBlock n m => String -> m [(SourceBlock, Result)]
evalSourceText source = do
  let sourceBlocks = parseProg source
  results <- mapM evalSourceBlock sourceBlocks
  return $ zip sourceBlocks results

processLogs :: LogLevel -> [Output] -> [Output]
processLogs logLevel outs = requiredOuts ++ processLogs' logLevel logOuts
  where (logOuts, requiredOuts) = partition isLogInfo outs

processLogs' :: LogLevel -> [Output] -> [Output]
processLogs' logLevel logs = case logLevel of
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

addCtx :: SourceBlock -> Err -> Err
addCtx block err@(Err e src s) = case src of
  Nothing -> err
  Just (start, stop) ->
    Err e Nothing $ s ++ "\n\n" ++ ctx
    where n = sbOffset block
          ctx = highlightRegion (start - n, stop - n) (sbText block)

findModulePath :: MonadInterBlock n m => ModuleName -> m FilePath
findModulePath moduleName = do
  let fname = moduleName ++ ".dx"
  specifiedPath <- libPath <$> ask
  case specifiedPath of
    Nothing -> liftIO $ getDataFileName $ "lib/" ++ fname
    Just path -> return $ path </> fname


-- === wiring together the passes for each source block ===

type MonadPasses n m =
  ( MonadReader (PassEnv n) m
  , MonadError Err m
  , MonadIO m )

type MonadPassesM n m = ReaderT (PassEnv n) ((ExceptT Err) IO)

data PassEnv n = PassEnv
  { peEvalConfig   :: EvalConfig
  , peBindings   :: TopBindings n
  , peLogService :: Logger [Output]
  , peBenchmark  :: Bool }

runTopPassM :: PassEnv n -> MonadPassesM n m a -> IO (Except a, [Output])
runTopPassM passEnv m = runLogger (logFile $ peEvalConfig passEnv) \logger ->
  runExceptT $ flip runReaderT (passEnv { peLogService = logger}) m

evalSourceBlock' :: MonadPasses n m => SourceBlock' -> m (EvaluatedModule n)
evalSourceBlock' block = withCompileTime $ case block of
  RunModule m -> do
    newBindings <- evalUModule m
    curBindings <- asks peBindings
    let SEvaluatedModule m' = toSafeETop curBindings $ DEvaluatedModule newBindings
    return m'
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
        _ -> return $ D.Con $ Lit val
      logTop $ ExportedFun name f
    GetType -> do  -- TODO: don't actually evaluate it
      val <- evalUModuleVal v m
      logTop $ TextOut $ pprint $ getType val
  GetNameType v -> emptyEvaluatedModule <$ do
    dBindings  <- asks (dBindings . peBindings)
    case D.envLookup dBindings (v D.:>()) of
      Just (ty, _) -> logTop (TextOut $ pprint ty)
      _            -> liftEitherIO $ throw UnboundVarErr $ pprint v
  UnParseable _ s -> emptyEvaluatedModule <$ throw ParseErr s
  _               -> return emptyEvaluatedModule

evalUModuleVal :: MonadPasses n m => D.Name -> UModule -> m D.Val
evalUModuleVal v m = do
  env  <- asks $ dBindings . peBindings
  env' <- evalUModule m
  return $ lookupBindings (env <> env') (v D.:> ())

lookupBindings :: D.Bindings -> D.VarP ann -> D.Atom
lookupBindings scope v = x
  where (_, D.LetBound PlainLet (D.Atom x)) = scope ! v

evalUModule :: MonadPasses n m => UModule -> m D.Bindings
evalUModule untyped = do
  env <- asks $ dBindings . peBindings
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
  backend <- asks (backendName . peEvalConfig)
  let optimized = case backend of
                    LLVMCUDA -> parallelizeModule stdOptimized
                    LLVMMC   -> parallelizeModule stdOptimized
                    _        -> stdOptimized
  checkPass OptimPass optimized
  case optimized of
    D.Module _ D.Empty newBindings -> return newBindings
    _ -> do
      let (block, rest) = splitSimpModule env optimized
      result <- evalBackend block
      newBindings <- liftIO $ evalModuleInterp mempty $ applyAbs rest result
      checkPass ResultPass $ D.Module Evaluated D.Empty newBindings
      return newBindings

evalBackend :: MonadPasses n m => D.Block -> m D.Atom
evalBackend block = do
  env     <- asks (dBindings . peBindings)
  backend <- asks (backendName . peEvalConfig)
  bench   <- asks peBenchmark
  logger  <- asks peLogService
  let (ptrBinders, ptrVals, block') = abstractPtrLiterals block
  let funcName = "entryFun"
  let mainName = D.Name TopFunctionName (fromString funcName) 0
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
  resultVals <- liftM (map (D.Con . Lit)) $ liftIO $
    llvmEvaluate logger llvmAST funcName ptrVals resultTypes
  return $ applyNaryAbs reconAtom resultVals

withCompileTime :: MonadPasses n m => m a -> m a
withCompileTime m = do
  (ans, t) <- measureSeconds m
  logTop $ TotalTime t
  return ans

checkPass :: (Pretty a, Checkable a) => MonadPasses n m => PassName -> a -> m ()
checkPass name x = do
  logPass name x
  liftEither $ checkValid x
  logTop $ MiscLog $ pprint name ++ " checks passed"

logPass :: MonadPasses n m => Pretty a => PassName -> a -> m ()
logPass passName x = logTop $ PassInfo passName $ pprint x

logTop :: MonadPasses n m => Output -> m ()
logTop x = do
  logger <- asks peLogService
  logThis logger [x]

abstractPtrLiterals :: D.Block -> ([D.IBinder], [LitVal], D.Block)
abstractPtrLiterals block = flip evalState mempty $ do
  block' <- traverseLiterals block \val -> case val of
    PtrLit ty ptr -> do
      ptrName <- gets $ M.lookup (ty, ptr) . fst
      case ptrName of
        Just v -> return $ D.Var $ v D.:> getType (D.Con $ Lit val)
        Nothing -> do
          (varMap, usedNames) <- get
          let name = genFresh (D.Name AbstractedPtrName "ptr" 0) usedNames
          put ( varMap    <> M.insert (ty, ptr) name varMap
              , usedNames <> (name D.@> ()))
          return $ D.Var $ name D.:> D.BaseTy (PtrType ty)
    _ -> return $ D.Con $ Lit val
  valsAndNames <- gets $ M.toAscList . fst
  let impBinders = [Bind (name D.:> PtrType ty) | ((ty, _), name) <- valsAndNames]
  let vals = map (uncurry PtrLit . fst) valsAndNames
  return (impBinders, vals, block')

class HasTraversal a where
  traverseCore :: (MonadBuilder m, MonadReader D.SubstEnv m) => TraversalDef m -> a -> m a

instance HasTraversal D.Block where
  traverseCore = traverseBlock

instance HasTraversal D.Atom where
  traverseCore = traverseAtom

traverseLiterals :: (HasTraversal e, Monad m) => e -> (D.LitVal -> m D.Atom) -> m e
traverseLiterals block f =
    liftM fst $ flip runSubstBuilderT mempty $ traverseCore def block
  where
    def = (traverseDecl def, traverseExpr def, traverseAtomLiterals)
    traverseAtomLiterals atom = case atom of
      D.Con (Lit x) -> lift $ lift $ f x
      _ -> traverseAtom def atom

-- === instances ===

instance Monad m => MonadTopBuilder n (TopBuilderT n m) where
  extendTopBindingsM evaluatedModule = UnsafeMakeTopBuilderT do
    bindings <- get
    bindings' <- extendTopBindings bindings evaluatedModule unsafeCoerce
    put bindings'

  withTopBindings cont = UnsafeMakeTopBuilderT get >>= cont

  getSourceNameMap = UnsafeMakeTopBuilderT $ gets topSourceMap

instance MonadState s m => MonadState s (TopBuilderT n m) where
  get = UnsafeMakeTopBuilderT $ lift get
  put x = UnsafeMakeTopBuilderT $ lift $ put x

instance MonadReader r m => MonadReader r (TopBuilderT n m) where
  ask = UnsafeMakeTopBuilderT ask
  local f (UnsafeMakeTopBuilderT m) = UnsafeMakeTopBuilderT $ local f m

unsafeGetTopBindings :: MonadTopBuilder n m => m (UnsafeTopBindings)
unsafeGetTopBindings = undefined
