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
                 TopLevel, evalSourceBlock, EvalOpts (..)) where

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
import Name
import HigherKinded
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
import qualified LazyMap as LM

data EvalOpts = EvalOpts
  { backendName :: Backend
  , libPath     :: Maybe FilePath
  , logFile     :: Maybe FilePath }

type TopLevel n = TopBuilderT n (ReaderT EvalOpts (StateT ModuleStatuses IO))

newtype TopBuilderT n (m :: * -> *) a = UnsafeMakeTopBuilderT
  { unsafeRunTopBuilderT :: StateT (Bindings n, SourceNameMap n) m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail, MonadException)

runTopBuilderT :: Monad m => (forall n. TopBuilderT n m a) -> m a
runTopBuilderT (UnsafeMakeTopBuilderT m) = evalStateT m (emptyBindings, SourceNameMap mempty)

runTopLevel :: EvalOpts -> (forall n. TopLevel n a) -> IO a
runTopLevel opts m =
  flip evalStateT mempty $ flip runReaderT opts $ runTopBuilderT m

-- === wiring together the source blocks ===

class Monad m => MonadTopBuilder n m | m -> n where
  extendTopBindings :: HasNames e => WithBindings e n -> m (e n)
  extendSourceNameMap :: SourceNameMap n -> m ()
  withTopBindings :: (Bindings n -> m a) -> m a
  getSourceNameMap :: m (SourceNameMap n)

type MonadInterBlock n m =
       ( MonadTopBuilder n m
       , MonadIO m
       , MonadState ModuleStatuses m
       , MonadReader EvalOpts m)

type ModuleStatuses = M.Map ModuleName ModuleImportStatus

data ModuleImportStatus = CurrentlyImporting | FullyImported  deriving Generic

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
      sourceMap <- getSourceNameMap
      let passEnv = PassEnv
            { peEvalOpts = opts
            , peSourceMap = sourceMap
            , peBindings = bindings
            , peLogService = error "not set"  -- TODO: something better
            , peBenchmark = case sbLogLevel block of PrintBench _ -> True; _ -> False }
      (ans, outs) <- liftIO $ runTopPassM passEnv $ evalSourceBlock' $ sbContents block
      let outs' = processLogs (sbLogLevel block) outs
      case ans of
        Left err   -> return $ Result outs' (Left (addCtx block err))
        Right evaluated -> do
          sourceMapFrag <- extendTopBindings evaluated
          extendSourceNameMap sourceMapFrag
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
  { peEvalOpts   :: EvalOpts
  , peSourceMap  :: SourceNameMap n
  , peBindings   :: Bindings n
  , peLogService :: Logger [Output]
  , peBenchmark  :: Bool }

runTopPassM :: PassEnv n -> MonadPassesM n m a -> IO (Except a, [Output])
runTopPassM passEnv m = runLogger (logFile $ peEvalOpts passEnv) \logger ->
  runExceptT $ flip runReaderT (passEnv { peLogService = logger}) m

evalSourceBlock' :: MonadPasses n m => SourceBlock' -> m (EvaluatedModule n)
evalSourceBlock' block = withCompileTime $ case block of
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
--     ExportFun name -> do
--       f <- evalUModuleVal bindings v m
--       void $ traverseLiterals f \val -> case val of
--         PtrLit _ _ -> liftEitherIO $ throw CompilerErr $
--           "Can't export functions with captured pointers (not implemented)."
--         _ -> return $ Con $ Lit val
--       logTop $ ExportedFun name f
    GetType -> do  -- TODO: don't actually evaluate it
      val <- evalUModuleVal v m
      logTop $ TextOut $ pprint $ getType val
  -- GetNameType v -> emptyEvaluatedModule <$ do
  --   bindings  <- asks peBindings
  --   sourceMap <- asks peSourceMap
  --   case M.lookup v (fromSourceNameMap sourceMap) of
  --     Just v' -> logTop $ TextOut $ pprint $ fstH $ scopeLookup bindings v'
  --     Nothing -> throw UnboundVarErr $ pprint v
  UnParseable _ s -> emptyEvaluatedModule <$ throw ParseErr s
  _               -> return emptyEvaluatedModule

evalUModuleVal :: MonadPasses n m => Name SourceNS -> SourceModule -> m (Val n)
evalUModuleVal v m = do
  bindings  <- asks peBindings
  evaluated <- evalUModule m
  let scope = asScopeFrag bindings
  case freshenAbs scope evaluated of
    FreshAbs ext frag sourceMap -> do
      let bindings' = extendRecEnv ext bindings frag
      let Just v' = M.lookup v $ fromSourceNameMap sourceMap
      let TypedBinderInfo _ (LetBound PlainLet (Atom x)) =
            envLookup (fromRecEnvFrag bindings') v'
      case lowerNames scope (asScopeFrag frag) x of
        Nothing -> throw LeakedVarErr ""
        Just x' -> return x'

-- TODO: track source locations and try to give better error messages
renameSourceModule :: MonadPasses n m => SourceModule -> m (UModule n)
renameSourceModule decl = do
  sourceMap <- asks peSourceMap
  bindings  <- asks peBindings
  let scope = asScopeFrag bindings
  let t = newNameTraversal $ lookupSourceName sourceMap
  liftEither $ traverseFreeNamesBinders scope t decl >>= \case
    Fresh _ decl' renamer ->
      return $ UModule decl' $ renameEnvFragAsSourceMap renamer

-- This is a sketchy because it mean that `EnvFrag a n l` isn't truly
-- contravariant in `l`.
renameEnvFragAsSourceMap :: RenameEnvFrag SourceNS SourceNS n -> SourceNameMap n
renameEnvFragAsSourceMap (UnsafeMakeEnvFrag frag) =
  SourceNameMap $ M.fromList [(SourceName k, v) | (k, v) <- LM.assocs frag]

lookupSourceName :: SourceNameMap n -> Name SourceNS -> Except (Name n)
lookupSourceName = undefined

evalUModule :: MonadPasses n m => SourceModule -> m (EvaluatedModule n)
evalUModule sourceMod = do
  logPass Parse sourceMod
  bindings  <- asks peBindings
  renamed <- renameSourceModule sourceMod
  typed <- inferModule bindings renamed
  checkPass TypePass typed
  synthed <- synthModule bindings typed
  -- TODO: check that the type of module exports doesn't change from here on
  checkPass SynthPass synthed
  let defunctionalized = simplifyModule bindings synthed
  checkPass SimpPass defunctionalized
  let stdOptimized = optimizeModule bindings defunctionalized
  -- Apply backend specific optimizations
  backend <- asks $ backendName . peEvalOpts
  let optimized = case backend of
                    LLVMCUDA -> parallelizeModule bindings stdOptimized
                    LLVMMC   -> parallelizeModule bindings stdOptimized
                    _        -> stdOptimized
  checkPass OptimPass optimized
  case optimized of
    Module _ Empty newBindings newSourceMap ->
      return $ Abs newBindings newSourceMap
    _ -> do
      let (block, rest) = splitSimpModule bindings optimized
      result <- evalBackend block
      evalModuleInterp bindings $ scopelessApplyAbs rest result

evalBackend :: MonadPasses n m => Block n -> m (Atom n)
evalBackend block = do
  backend <- asks $ backendName . peEvalOpts
  bench   <- asks peBenchmark
  logger  <- asks peLogService
  let (absBlock,  ptrVals) = abstractPtrLiterals block
  let (cc, needsSync) = case backend of LLVMCUDA -> (EntryFun CUDARequired   , True )
                                        _        -> (EntryFun CUDANotRequired, False)
  bindings <- asks peBindings
  let (impModuleUnoptimized, reconAtom) =
         toImpModule bindings backend cc Nothing absBlock
  -- TODO: toImpModule might generate invalid Imp code, because GPU allocations
  --       were not lifted from the kernels just yet. We should split the Imp IR
  --       into different levels so that we can check the output here!
  --checkPass ImpPass impModuleUnoptimized
  let impModule = case backend of
                    LLVMCUDA -> liftCUDAAllocations impModuleUnoptimized
                    _        -> impModuleUnoptimized
  checkPass ImpPass impModule
  llvmAST <- liftIO $ impToLLVM logger impModule
  let Just (IFunType _ _ resultTypes) = impModuleMainFunType impModule
  let llvmEvaluate = if bench then compileAndBench needsSync else compileAndEval
  resultVals <- liftM (map (Con . Lit)) $ liftIO $
    llvmEvaluate logger llvmAST llvmMainFuncName ptrVals resultTypes
  return $ scopelessApplyNaryAbs reconAtom resultVals

withCompileTime :: MonadPasses n m => m a -> m a
withCompileTime m = do
  (ans, t) <- measureSeconds m
  logTop $ TotalTime t
  return ans

checkPass :: (Pretty a, Checkable a) => MonadPasses n m => PassName -> a -> m ()
checkPass name x = do
  logPass name x
  checkValid x
  logTop $ MiscLog $ pprint name ++ " checks passed"

logPass :: MonadPasses n m => Pretty a => PassName -> a -> m ()
logPass passName x = logTop $ PassInfo passName $ pprint x

logTop :: MonadPasses n m => Output -> m ()
logTop x = do
  logger <- asks peLogService
  logThis logger [x]

abstractPtrLiterals :: Block n -> (Abs IBinderList Block n, [LitVal])
abstractPtrLiterals block = undefined
-- abstractPtrLiterals block = flip evalState mempty $ do
--   block' <- traverseLiterals block \val -> case val of
--     PtrLit ty ptr -> do
--       ptrName <- gets $ M.lookup (ty, ptr) . fst
--       case ptrName of
--         Just v -> return $ Var $ v :> getType (Con $ Lit val)
--         Nothing -> do
--           (varMap, usedNames) <- get
--           let name = genFresh (Name AbstractedPtrName "ptr" 0) usedNames
--           put ( varMap    <> M.insert (ty, ptr) name varMap
--               , usedNames <> (name @> ()))
--           return $ Var $ name :> BaseTy (PtrType ty)
--     _ -> return $ Con $ Lit val
--   valsAndNames <- gets $ M.toAscList . fst
--   let impBinders = [Bind (name :> PtrType ty) | ((ty, _), name) <- valsAndNames]
--   let vals = map (uncurry PtrLit . fst) valsAndNames
--   return (impBinders, vals, block')

-- -- class HasTraversal a where
-- --   traverseCore :: (MonadBuilder m, MonadReader SubstEnv m) => TraversalDef m -> a -> m a

-- -- instance HasTraversal Block where
-- --   traverseCore = traverseBlock

-- -- instance HasTraversal Atom where
-- --   traverseCore = traverseAtom

-- -- traverseLiterals :: (HasTraversal e, Monad m) => e -> (LitVal -> m Atom) -> m e
-- -- traverseLiterals block f =
-- --     liftM fst $ flip runSubstBuilderT mempty $ traverseCore def block
-- --   where
-- --     def = (traverseDecl def, traverseExpr def, traverseAtomLiterals)
-- --     traverseAtomLiterals atom = case atom of
-- --       Con (Lit x) -> lift $ lift $ f x
-- --       _ -> traverseAtom def atom

-- -- instance Semigroup (TopEnv n) where
-- --   (TopEnv env ms) <> (TopEnv env' ms') =
-- --     -- Data.Map is left-biased so we flip the order
-- --     TopEnv (env <> env') (ms' <> ms)

-- -- instance Monoid (TopEnv n) where
-- --   mempty = TopEnv mempty mempty

-- -- moduleStatus :: ModuleName -> ModuleImportStatus -> TopEnv n
-- -- moduleStatus name status = mempty { modulesImported = M.singleton name status}

-- -- instance HasPtrs (TopEnv n) where
-- --   traversePtrs f (TopEnv bindings status) =
-- --     TopEnv <$> traverse (traversePtrs f) bindings <*> pure status

-- -- instance Store (TopEnv n)
-- -- instance Store ModuleImportStatus

-- === instances ===

unsafeCoerceBindings :: Bindings n -> Bindings l
unsafeCoerceBindings = unsafeCoerce

instance Monad m => MonadTopBuilder n (TopBuilderT n m) where
  extendTopBindings ab = UnsafeMakeTopBuilderT do
    bindings <- gets fst
    case freshenAbs (asScopeFrag bindings) ab of
      FreshAbs ext frag body -> do
        let bindings' = extendRecEnv ext bindings frag
        modify (\(_,m) -> (unsafeCoerceBindings bindings', m))
        return $ unsafeCoerceNames body

  extendSourceNameMap m = UnsafeMakeTopBuilderT $ modify \(b, m') -> (b, m' <> m)
  withTopBindings cont = UnsafeMakeTopBuilderT (gets fst) >>= cont
  getSourceNameMap = UnsafeMakeTopBuilderT $ gets snd

instance MonadState s m => MonadState s (TopBuilderT n m) where
  get = undefined
  put = undefined

instance MonadReader r m => MonadReader r (TopBuilderT n m) where
  ask = UnsafeMakeTopBuilderT ask
  local f (UnsafeMakeTopBuilderT m) = UnsafeMakeTopBuilderT $ local f m

