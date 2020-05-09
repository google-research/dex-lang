-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module TopLevel (evalBlock, EvalConfig (..), initializeBackend,
                 Backend (..)) where

import Control.Concurrent.MVar
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except hiding (Except)
import Data.Foldable (toList)
import Data.String
import Data.Text.Prettyprint.Doc

import Array
import Syntax
import Cat
import Env
import Type
import Inference
import Normalize
import Simplify
import Serialize
import Imp
import Flops
import Interpreter
import JIT
import Logging
import LLVMExec
import PPrint
import Parser
import PipeRPC
import Record
import Subst
import JAX
import Util (highlightRegion)

data Backend = LLVM | Interp | JAX
data EvalConfig = EvalConfig
  { backendName :: Backend
  , preludeFile :: FilePath
  , logAll      :: Bool  -- TODO:  logFile :: Maybe FilePath
  , evalEngine  :: BackendEngine
  , logService  :: Logger [Output] }

data BackendEngine = LLVMEngine LLVMEngine
                   | JaxServer JaxServer
                   | InterpEngine

type LLVMEngine = MVar (Env ArrayRef)
type JaxServer = PipeServer ( (JaxFunction, [JVar]) -> [JVar]
                           ,( [JVar] -> [Array]
                           ,( Array -> ()  -- for debugging
                           ,())))

type TopPassM a = ReaderT EvalConfig IO a

-- TODO: handle errors due to upstream modules failing
evalBlock :: EvalConfig -> TopEnv -> SourceBlock -> IO (TopEnv, Result)
evalBlock opts env block = do
  (ans, outs) <- runTopPassM opts $ evalSourceBlock env block
  let outs' = filter (keepOutput block) outs
  case ans of
    Left err   -> return (mempty, Result outs' (Left (addCtx block err)))
    Right env' -> return (env'  , Result outs' (Right ()))

runTopPassM :: EvalConfig -> TopPassM a -> IO (Except a, [Output])
runTopPassM opts m = runLogger $ \logger ->
  runExceptT $ catchIOExcept $ runReaderT m $ opts {logService = logger}

evalSourceBlock :: TopEnv -> SourceBlock -> TopPassM TopEnv
evalSourceBlock env@(TopEnv (typeEnv, _) _ _) block = case sbContents block of
  RunModule m -> evalModule env m
  Command cmd (v, m) -> mempty <$ case cmd of
    EvalExpr fmt -> do
      val <- evalModuleVal env v m
      case fmt of
        Printed -> do
          s <- liftIO $ pprintVal val
          logTop $ TextOut s
        Heatmap -> logTop $ valToHeatmap val
        Scatter -> logTop $ valToScatter val
    GetType -> do  -- TODO: don't actually evaluate it
      val <- evalModuleVal env v m
      logTop $ TextOut $ pprint $ getType val
    Dump DexObject fname -> do
      val <- evalModuleVal env v m
      s <- liftIO $ pprintVal val
      liftIO $ writeFile fname s
    Dump DexBinaryObject fname -> do
      val <- evalModuleVal env v m
      liftIO $ dumpDataFile fname val
    ShowPasses -> void $ evalModule env m
    ShowPass _ -> void $ evalModule env m
    TimeIt     -> void $ evalModule env m
  GetNameType v -> case envLookup typeEnv v of
    Just (L ty) -> logTop (TextOut $ pprint ty) >> return mempty
    _           -> liftEitherIO $ throw UnboundVarErr $ pprint v
  IncludeSourceFile fname -> do
    source <- liftIO $ readFile fname
    evalSourceBlocks env $ parseProg source
  LoadData p DexObject fname -> do
    source <- liftIO $ readFile fname
    let val = ignoreExcept $ parseData source
    let decl = LetMono p val
    let outVars = map (\(v:>ty) -> v:>L ty) $ toList p
    evalModule env $ Module (sbId block) ([], outVars) [decl]
  LoadData p DexBinaryObject fname -> do
    val <- liftIO $ loadDataFile fname
    -- TODO: handle patterns and type annotations in binder
    let (RecLeaf b) = p
    let outEnv = b @> L val
    return $ TopEnv (substEnvType outEnv, mempty) outEnv mempty
  RuleDef ann@(LinearizationDef v) ~(Forall [] [] ty) ~(FTLam [] [] expr) -> do
    let v' = fromString (pprint v ++ "!lin") :> ty  -- TODO: name it properly
    let imports = map (uncurry (:>)) $ envPairs $ freeVars ann <> freeVars ty <> freeVars expr
    let m = Module (sbId block) (imports, [fmap L v']) [LetMono (RecLeaf v') expr]
    env' <- evalModule env m
    return $ env' <> TopEnv mempty mempty ((v:>()) @> Var v')
  UnParseable _ s -> liftEitherIO $ throw ParseErr s
  _               -> return mempty

keepOutput :: SourceBlock -> Output -> Bool
keepOutput block output = case output of
  PassInfo name _ -> case sbContents block of
    Command (ShowPasses)     _ -> True
    Command (ShowPass name') _ -> name == name'
    Command (TimeIt)         _ -> name == LLVMEval
    _                          -> False
  MiscLog _ -> case sbContents block of
    Command (ShowPasses) _ -> True
    _                      -> False
  _ -> True

evalSourceBlocks :: TopEnv -> [SourceBlock] -> TopPassM TopEnv
evalSourceBlocks env blocks =
  liftM snd $ flip runCatT env $ flip mapM_ blocks $ \block -> do
    env' <- look
    env'' <- lift $ evalSourceBlock env' block
    extend env''

evalModuleVal :: TopEnv -> Var -> FModule -> TopPassM Val
evalModuleVal env v m = do
  env' <- evalModule env m
  let (TopEnv _ simpEnv _) = env <> env'
  let (L val) = simpEnv ! v
  let val' = subst (simpEnv, mempty) val
  backend <- asks evalEngine
  liftIO $ substArrayLiterals backend val'

-- TODO: extract only the relevant part of the env we can check for module-level
-- unbound vars and upstream errors here. This should catch all unbound variable
-- errors, but there could still be internal shadowing errors.
evalModule :: TopEnv -> FModule -> TopPassM TopEnv
evalModule (TopEnv infEnv simpEnv ruleEnv) untyped = do
  logPass Parse untyped
  (typed, infEnv') <- typePass infEnv untyped
  checkPass TypePass typed
  let normalized = normalizeModule typed
  checkPass NormPass normalized
  let (defunctionalized, simpEnv') = simplifyModule simpEnv ruleEnv normalized
  checkPass SimpPass defunctionalized
  let (Module _ (_, outVars) dfExpr) = defunctionalized
  case dfExpr of
    Atom UnitVal -> do
      return $ TopEnv infEnv' simpEnv' mempty
    _ -> do
      ~(TupVal results) <- evalBackend dfExpr
      let simpEnv'' = subst (newLEnv outVars results, mempty) simpEnv'
      return $ TopEnv infEnv' simpEnv'' mempty

initializeBackend :: Backend -> IO BackendEngine
initializeBackend backend = case backend of
  LLVM -> liftM LLVMEngine $ newMVar mempty
  JAX  -> liftM JaxServer $ startPipeServer "python3" ["misc/py/jax_call.py"]
  _ -> error "Not implemented"

evalBackend :: Expr -> TopPassM Atom
evalBackend expr = do
  backend <- asks evalEngine
  logger  <- asks logService
  let inVars = arrayVars expr
  case backend of
    LLVMEngine engine -> do
      let impFunction = toImpFunction (inVars, expr)
      checkPass ImpPass impFunction
      logPass Flops $ impFunctionFlops impFunction
      let llvmFunc = impToLLVM impFunction
      outVars <- liftIO $ execLLVM logger engine llvmFunc inVars
      return $ reStructureArrays (getType expr) $ map Var outVars
    JaxServer server -> do
      -- callPipeServer (psPop (psPop server)) $ arrayFromScalar (IntLit 123)
      let jfun = toJaxFunction (inVars, expr)
      checkPass JAXPass jfun
      let inVars' = map (fmap typeToJType) inVars
      outVars <- callPipeServer server (jfun, inVars')
      let outVars' = map (fmap jTypeToType) outVars
      return $ reStructureArrays (getType expr) $ map Var outVars'
    InterpEngine -> return $ evalExpr mempty expr

requestArrays :: BackendEngine -> [Var] -> IO [Array]
requestArrays _ [] = return []
requestArrays backend vs = case backend of
  LLVMEngine env -> do
    env' <- readMVar env
    forM vs $ \v -> do
      case envLookup env' v of
        Just ref -> loadArray ref
        Nothing -> error "Array lookup failed"
  JaxServer server -> do
    let vs' = map (fmap typeToJType) vs
    callPipeServer (psPop server) vs'
  _ -> error "Not implemented"

arrayVars :: HasVars a => a -> [Var]
arrayVars x = [v:>ty | (v@(Name ArrayName _ _), L ty) <- envPairs (freeVars x)]

substArrayLiterals :: (HasVars a, Subst a) => BackendEngine -> a -> IO a
substArrayLiterals backend x = do
  let vs = arrayVars x
  arrays <- requestArrays backend vs
  let arrayAtoms = map (Con . ArrayLit) arrays
  return $ subst (newLEnv vs arrayAtoms, mempty) x

-- TODO: think carefully about whether this is thread-safe
execLLVM :: Logger [Output] -> LLVMEngine -> LLVMFunction -> [Var] -> IO [Var]
execLLVM logger envRef fun@(LLVMFunction outTys _ _) inVars = do
  modifyMVar envRef $ \env -> do
    outRefs <- mapM newArrayRef outTys
    let inRefs = flip map inVars $ \v ->
                   case envLookup env v of
                     Just ref -> ref
                     Nothing  -> error "Array lookup failed"
    let (outNames, env') = nameItems (Name ArrayName "arr" 0) env outRefs
    let outVars = zipWith (\v (b,shape) -> v :> ArrayTy b shape) outNames outTys
    callLLVM logger fun outRefs inRefs
    return (env <> env', outVars)

-- TODO: check here for upstream errors
typePass :: TopInfEnv -> FModule -> TopPassM (FModule, TopInfEnv)
typePass env m = do
  (typed, envOut) <- liftEitherIO $ inferModule env m
  liftEitherIO $ checkValid typed
  return (typed, envOut)

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
