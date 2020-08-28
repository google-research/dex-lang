-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module TopLevel (evalSourceBlock, EvalConfig (..), initializeBackend,
                 Backend (..)) where

import Control.Concurrent.MVar
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except hiding (Except)
import Data.Text.Prettyprint.Doc
import Foreign.Ptr
import Data.List (partition)
import Data.Maybe (fromJust, fromMaybe)
import Data.Time.Clock (getCurrentTime, diffUTCTime)

import Array
import Syntax
import Cat
import Env
import Embed
import Type
import Inference
import Simplify
import Serialize
import Imp
import Interpreter
import JIT
import Logging
import LLVMExec
import PPrint
import Parser
import Util (highlightRegion)
import CUDA

data Backend = LLVM | LLVMCUDA | LLVMMC | Interp | JAX  deriving (Show, Eq)
data EvalConfig = EvalConfig
  { backendName :: Backend
  , preludeFile :: FilePath
  , logFile     :: Maybe FilePath
  , evalEngine  :: BackendEngine
  , logService  :: Logger [Output] }

data LLVMEngineKind = Serial | Multicore | CUDA
data BackendEngine = LLVMEngine LLVMEngineKind LLVMEngine
                   -- | JaxServer JaxServer
                   | InterpEngine

type LLVMEngine = MVar (Env (Ptr ()))
-- type JaxServer = PipeServer ( (JaxFunction, [JVar]) -> ([JVar], String)
--                            ,( [JVar] -> [Array]
--                            ,( Array -> ()  -- for debugging
--                            ,())))

type TopPassM a = ReaderT EvalConfig IO a

-- TODO: handle errors due to upstream modules failing
evalSourceBlock :: EvalConfig -> TopEnv -> SourceBlock -> IO (TopEnv, Result)
evalSourceBlock opts env block = do
  (ans, outs) <- runTopPassM opts $ withCompileTime $ evalSourceBlockM env block
  let (logOuts, requiredOuts) = partition isLogInfo outs
  let outs' = requiredOuts ++ processLogs (sbLogLevel block) logOuts
  case ans of
    Left err   -> return (mempty, Result outs' (Left (addCtx block err)))
    Right env' -> return (env'  , Result outs' (Right ()))

runTopPassM :: EvalConfig -> TopPassM a -> IO (Except a, [Output])
runTopPassM opts m = runLogger (logFile opts) $ \logger ->
  runExceptT $ catchIOExcept $ runReaderT m $ opts {logService = logger}

evalSourceBlockM :: TopEnv -> SourceBlock -> TopPassM TopEnv
evalSourceBlockM env block = case sbContents block of
  RunModule m -> evalUModule env m
  Command cmd (v, m) -> mempty <$ case cmd of
    EvalExpr fmt -> do
      val <- evalUModuleVal env v m
      logPass ImpPass (pprint val)
      case fmt of
        Printed -> do
          logTop $ TextOut $ pprintVal val
        Heatmap color -> logTop $ valToHeatmap color val
        Scatter -> logTop $ valToScatter val
    GetType -> do  -- TODO: don't actually evaluate it
      val <- evalUModuleVal env v m
      logTop $ TextOut $ pprint $ getType val
    Dump DexObject fname -> do
      val <- evalUModuleVal env v m
      liftIO $ writeFile fname $ pprintVal val
    Dump DexBinaryObject fname -> do
      val <- evalUModuleVal env v m
      liftIO $ dumpDataFile fname val
  GetNameType v -> case envLookup env (v:>()) of
    Just (ty, _) -> logTop (TextOut $ pprint ty) >> return mempty
    _            -> liftEitherIO $ throw UnboundVarErr $ pprint v
  IncludeSourceFile fname -> do
    source <- liftIO $ readFile fname
    evalSourceBlocks env $ parseProg source
  LoadData pat DexObject fname -> do
    source <- liftIO $ readFile fname
    let val = ignoreExcept $ parseData source
    evalUModule env $ UModule $ toNest [ULet PlainLet pat val]
  -- LoadData pat DexBinaryObject fname -> do
  --   val <- liftIO $ loadDataFile fname
  --   -- TODO: handle patterns and type annotations in binder
  --   let (WithSrc _ (PatBind b), _) = pat
  --   let outEnv = b @> val
  --   return $ TopEnv mempty outEnv
  UnParseable _ s -> liftEitherIO $ throw ParseErr s
  _               -> return mempty

processLogs :: LogLevel -> [Output] -> [Output]
processLogs logLevel logs = case logLevel of
  LogAll -> logs
  LogNothing -> []
  LogPasses passes -> flip filter logs $ \l -> case l of
                        PassInfo pass _ | pass `elem` passes -> True
                                        | otherwise          -> False
  PrintEvalTime -> [BenchResult "" compileTime runTime]
    where (compileTime, runTime) = timesFromLogs logs
  PrintBench benchName -> [BenchResult benchName compileTime runTime]
    where (compileTime, runTime) = timesFromLogs logs

timesFromLogs :: [Output] -> (Double, Double)
timesFromLogs logs = (totalTime - evalTime, evalTime)
  where
    evalTime  = case [tEval | EvalTime tEval <- logs] of
                  []  -> 0.0
                  [t] -> t
                  _   -> error "Expect at most one result"
    totalTime = case [tTotal | TotalTime tTotal <- logs] of
                  []  -> 0.0
                  [t] -> t
                  _   -> error "Expect at most one result"

isLogInfo :: Output -> Bool
isLogInfo out = case out of
  PassInfo _ _ -> True
  MiscLog  _   -> True
  EvalTime _   -> True
  TotalTime _  -> True
  _ -> False

evalSourceBlocks :: TopEnv -> [SourceBlock] -> TopPassM TopEnv
evalSourceBlocks env blocks = catFoldM evalSourceBlockM env blocks

evalUModuleVal :: TopEnv -> Name -> UModule -> TopPassM Val
evalUModuleVal env v m = do
  env' <- evalUModule env m
  let val = lookupBindings (env <> env') (v:>())
  backend <- asks evalEngine
  liftIO $ substArrayLiterals backend val

lookupBindings :: Scope -> VarP ann -> Atom
lookupBindings scope v = reduceAtom scope x
  where (_, LetBound PlainLet (Atom x)) = scope ! v

-- TODO: extract only the relevant part of the env we can check for module-level
-- unbound vars and upstream errors here. This should catch all unbound variable
-- errors, but there could still be internal shadowing errors.
evalUModule :: TopEnv -> UModule -> TopPassM TopEnv
evalUModule env untyped = do
  -- TODO: it's handy to log the env, but we need to filter out just the
  --       relevant part (transitive closure of free vars)
  -- logTop $ MiscLog $ "\n" ++ pprint env
  logPass Parse untyped
  typed <- liftEitherIO $ inferModule env untyped
  checkPass TypePass typed
  synthed <- liftEitherIO $ synthModule env typed
  -- TODO: check that the type of module exports doesn't change from here on
  checkPass SynthPass synthed
  evalModule env synthed

evalModule :: TopEnv -> Module -> TopPassM TopEnv
evalModule bindings normalized = do
  let defunctionalized = simplifyModule bindings normalized
  checkPass SimpPass defunctionalized
  evaluated <- evalSimplified defunctionalized evalBackend
  checkPass ResultPass evaluated
  Module Evaluated Empty newBindings <- return evaluated
  return newBindings

initializeBackend :: Backend -> IO BackendEngine
initializeBackend backend = case backend of
  LLVM     -> LLVMEngine Serial    <$> newMVar mempty
  LLVMMC   -> LLVMEngine Multicore <$> newMVar mempty
  LLVMCUDA -> if hasCUDA
                then LLVMEngine CUDA <$> newMVar mempty
                else error "Dex built without CUDA support"
  -- JAX      -> JaxServer  <$> startPipeServer "python3" ["misc/py/jax_call.py"]
  _ -> error "Not implemented"

arrayVars :: Subst a => a -> [Var]
arrayVars x = foldMap go $ envPairs (freeVars x)
  where go :: (Name, (Type, BinderInfo)) -> [Var]
        go (v@(GlobalArrayName _), (ty, _)) = [v :> ty]
        go _ = []

evalBackend :: Block -> TopPassM Atom
evalBackend block = do
  backend <- asks evalEngine
  logger  <- asks logService
  let inVars = arrayVars block
  case backend of
    LLVMEngine kind llvmEnv -> do
      (llvmFunc, impAtom, impOutVars) <- case kind of
        Serial -> do
          let (impFunction, impAtom) = toImpFunction (map Bind inVars, block)
          let (ImpFunction outVars _ _) = impFunction
          checkPass ImpPass impFunction
          return $ (impToLLVM impFunction, impAtom, outVars)
        Multicore -> do
          let (mdImpFunction, impAtom) = toMDImpFunction (map Bind inVars, block)
          let (MDImpFunction outVars _ _) = mdImpFunction
          return $ (mdImpToMulticore mdImpFunction, impAtom, outVars)
        CUDA      -> do
          let (mdImpFunction, impAtom) = toMDImpFunction (map Bind inVars, block)
          logPass ImpPass mdImpFunction
          let (MDImpFunction outVars _ _) = mdImpFunction
          ptxFunction <- liftIO $ traverse compileKernel mdImpFunction
          return $ (mdImpToCUDA ptxFunction, impAtom, outVars)
      resultAtom <- liftIO $ modifyMVar llvmEnv $ \env -> do
        let inPtrs = fmap (env !) inVars
        outPtrs <- callLLVM logger llvmFunc inPtrs
        let (GlobalArrayName i) = fromMaybe (GlobalArrayName 0) $ envMaxName env
        let outNames = GlobalArrayName <$> [i+1..]
        let env' = foldMap varAsEnv $ zipWith (:>) outNames outPtrs
        let substEnv = foldMap mkSubstEnv $ zip outNames impOutVars
        return (env <> env', subst (substEnv, mempty) impAtom)
      -- resultAtom is ill typed because it might contain pointers to scalar arrays
      -- in place of scalars. We fix it up by loading from each of those arrays in here.
      let scalarVars = filter isScalarRef $ envAsVars $ fmap fst $ freeVars resultAtom
      scalarArrs <- liftIO $ requestArrays backend scalarVars
      let scalarVals = fmap (Con . Lit . fromJust . scalarFromArray) scalarArrs
      let scalarSubstEnv = foldMap (uncurry (@>)) $ zip scalarVars scalarVals
      return $ subst (scalarSubstEnv, mempty) resultAtom
      where
        mkSubstEnv :: (Name, Binder) -> SubstEnv
        mkSubstEnv (outName, impVar) = impVar @> (Var $ (outName :> binderType impVar))

        isScalarRef (_ :> ArrayTy (BaseTy _)) = True
        isScalarRef _ = False

        compileKernel :: ImpKernel -> IO PTXKernel
        compileKernel k = do
          let llvmKernel = impKernelToLLVM k
          compilePTX logger llvmKernel
    -- JaxServer server -> do
    --   -- callPipeServer (psPop (psPop server)) $ arrayFromScalar (IntLit 123)
    --   let jfun = toJaxFunction (inVars, block)
    --   checkPass JAXPass jfun
    --   let jfunSimp = simplifyJaxFunction jfun
    --   checkPass JAXSimpPass jfunSimp
    --   let jfunDCE = dceJaxFunction jfunSimp
    --   checkPass JAXSimpPass jfunDCE
    --   let inVars' = map (fmap typeToJType) inVars
    --   (outVars, jaxprDump) <- callPipeServer server (jfunDCE, inVars')
    --   logPass JaxprAndHLO jaxprDump
    --   let outVars' = map (fmap jTypeToType) outVars
    --   return $ reStructureArrays (getType block) $ map Var outVars'
    InterpEngine -> return $ evalBlock mempty block

requestArrays :: BackendEngine -> [Var] -> IO [Array]
requestArrays _ [] = return []
requestArrays backend vs = case backend of
  LLVMEngine kind env -> do
    env' <- readMVar env
    forM vs $ \v@(_ :> ArrayTy ty) -> do
      let arrTy@(size, _) = typeToArrayType ty
      case envLookup env' v of
        Just ref -> do
          hostRef <- case (kind, ty) of
            (CUDA     , _       ) -> loadCUDAArray ref (fromIntegral $ size * sizeOf b)
              where b = scalarTableBaseType ty
            (Multicore, _       ) -> return ref
            (Serial   , _       ) -> return ref
          loadArray (ArrayRef arrTy hostRef)
        Nothing  -> error "Array lookup failed"
  -- JaxServer server -> do
  --   let vs' = map (fmap typeToJType) vs
  --   callPipeServer (psPop server) vs'
  _ -> error "Not implemented"

substArrayLiterals :: (Subst a, HasType a) => BackendEngine -> a -> IO a
substArrayLiterals backend x = do
  -- We first need to substitute the arrays used in the types. Our atom types
  -- are monotonic, so it's enough to ask for the arrays used in the type of the
  -- atom as a whole, without worrying about types hidden within the atom.
  x' <- substArrayLiterals' backend (arrayVars (getType x)) x
  substArrayLiterals' backend (arrayVars x') x'

substArrayLiterals' :: Subst a => BackendEngine -> [Var] -> a -> IO a
substArrayLiterals' backend vs x = do
  arrays <- requestArrays backend vs
  let arrayAtoms = [Con $ ArrayLit ty arr | (_:>ty, arr) <- zip vs arrays]
  return $ subst (newEnv vs arrayAtoms, mempty) x

withCompileTime :: TopPassM a -> TopPassM a
withCompileTime m = do
  t1 <- liftIO $ getCurrentTime
  ans <- m
  t2 <- liftIO $ getCurrentTime
  logTop $ TotalTime $ realToFrac $ t2 `diffUTCTime` t1
  return ans

checkPass :: (Pretty a, Checkable a) => PassName -> a -> TopPassM ()
checkPass name x = do
  logPass name x
  liftEitherIO $ checkValid x
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
