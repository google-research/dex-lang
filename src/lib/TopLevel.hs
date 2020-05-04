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
import Control.Exception hiding (throw)
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer.Strict  hiding (pass)
import Control.Monad.Except hiding (Except)
import Data.Foldable (toList)
import Data.String
import Data.Text.Prettyprint.Doc
import Data.Time.Clock (getCurrentTime, diffUTCTime)

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
import LLVMExec
import PPrint
import Parser
import Record
import Subst
import Util (highlightRegion)

data Backend = LLVM | Interp | JAX
data EvalConfig = EvalConfig
  { backendName :: Backend
  , preludeFile :: FilePath
  , logAll      :: Bool
  , evalEngine  :: BackendEngine }

data BackendEngine = LLVMEngine LLVMEngine
                   | InterpEngine

type LLVMEngine = MVar (Env ArrayRef)

type TopPassM a = ReaderT EvalConfig (ExceptT Err (WriterT [Output] IO)) a
type Pass a b = a -> TopPassM b

-- TODO: handle errors due to upstream modules failing
evalBlock :: EvalConfig -> TopEnv -> SourceBlock -> IO (TopEnv, Result)
evalBlock opts env block = do
  (ans, outs) <- runTopPassM opts $ addErrSrc block $ evalSourceBlock env block
  case ans of
    Left err   -> return (mempty, Result outs (Left err))
    Right env' -> return (env'  , Result outs (Right ()))

runTopPassM :: EvalConfig -> TopPassM a -> IO (Except a, [Output])
runTopPassM opts m = runWriterT $ runExceptT $ runReaderT m opts

evalSourceBlock :: TopEnv -> SourceBlock -> TopPassM TopEnv
evalSourceBlock env@(TopEnv (typeEnv, _) _ _) block = case sbContents block of
  RunModule m -> filterOutputs (const False) $ evalModule env m
  Command cmd (v, m) -> mempty <$ case cmd of
    EvalExpr fmt -> do
      val <- evalModuleVal env v m
      case fmt of
        Printed -> do
          s <- liftIOTop $ pprintVal val
          tell [TextOut s]
        Heatmap -> tell [valToHeatmap val]
        Scatter -> tell [valToScatter val]
    GetType -> do  -- TODO: don't actually evaluate it
      val <- evalModuleVal env v m
      tell [TextOut $ pprint (getType val)]
    Dump DexObject fname -> do
      val <- evalModuleVal env v m
      s <- liftIOTop $ pprintVal val
      liftIOTop $ writeFile fname s
    Dump DexBinaryObject fname -> do
      val <- evalModuleVal env v m
      liftIOTop $ dumpDataFile fname val
    ShowPasses -> runWithFilter $ \case PassInfo _ _ _ -> True;            _ -> False
    ShowPass s -> runWithFilter $ \case PassInfo s' _ _ | s == s' -> True; _ -> False
    TimeIt     -> runWithFilter $ \case PassInfo LLVMEval _ _ -> True;     _ -> False
    where
      runWithFilter :: (Output -> Bool) -> TopPassM ()
      runWithFilter f = liftM (const mempty) $ filterOutputs f $ evalModule env m
  GetNameType v -> case envLookup typeEnv v of
    Just (L ty) -> tell [TextOut $ pprint ty] >> return mempty
    _           -> throw UnboundVarErr $ pprint v
  IncludeSourceFile fname -> do
    source <- liftIOTop $ readFile fname
    evalSourceBlocks env $ parseProg source
  LoadData p DexObject fname -> do
    source <- liftIOTop $ readFile fname
    let val = ignoreExcept $ parseData source
    let decl = LetMono p val
    let outVars = map (\(v:>ty) -> v:>L ty) $ toList p
    filterOutputs (const False) $ evalModule env $
      Module (sbId block) ([], outVars) [decl]
  LoadData p DexBinaryObject fname -> do
    val <- liftIOTop $ loadDataFile fname
    -- TODO: handle patterns and type annotations in binder
    let (RecLeaf b) = p
    let outEnv = b @> L val
    return $ TopEnv (substEnvType outEnv, mempty) outEnv mempty
  RuleDef ann@(LinearizationDef v) ~(Forall [] [] ty) ~(FTLam [] [] expr) -> do
    let v' = fromString (pprint v ++ "!lin") :> ty  -- TODO: name it properly
    let imports = map (uncurry (:>)) $ envPairs $ freeVars ann <> freeVars ty <> freeVars expr
    let m = Module (sbId block) (imports, [fmap L v']) [LetMono (RecLeaf v') expr]
    env' <- filterOutputs (const False) $ evalModule env m
    return $ env' <> TopEnv mempty mempty ((v:>()) @> Var v')
  UnParseable _ s -> throw ParseErr s
  _               -> return mempty

evalSourceBlocks :: TopEnv -> [SourceBlock] -> TopPassM TopEnv
evalSourceBlocks env blocks =
  liftM snd $ flip runCatT env $ flip mapM_ blocks $ \block -> do
    env' <- look
    env'' <- lift $ evalSourceBlock env' block
    extend env''

evalModuleVal :: TopEnv -> Var -> FModule -> TopPassM Val
evalModuleVal env v m = do
  env' <- filterOutputs (const False) $ evalModule env m
  let (TopEnv _ simpEnv _) = env <> env'
  let (L val) = simpEnv ! v
  let val' = subst (simpEnv, mempty) val
  backend <- asks evalEngine
  liftIO $ substArrayLiterals backend val'

 -- TODO: extract only the relevant part of the env we can check for module-level
-- unbound vars and upstream errors here. This should catch all unbound variable
-- errors, but there could still be internal shadowing errors.
evalModule :: TopEnv -> Pass FModule TopEnv
evalModule (TopEnv infEnv simpEnv ruleEnv) untyped = do
  tell [PassInfo Parse "" (pprint untyped)]
  (typed, infEnv') <- typePass infEnv untyped
  normalized <- normalizePass typed
  (defunctionalized, simpEnv') <- simpPass simpEnv ruleEnv normalized
  let (Module _ (_, outVars) dfExpr) = defunctionalized
  case dfExpr of
    Atom UnitVal -> do
      return $ TopEnv infEnv' simpEnv' mempty
    _ -> do
      ~(TupVal results) <- evalBackend dfExpr
      let simpEnv'' = subst (newLEnv outVars results, mempty) simpEnv'
      return $ TopEnv infEnv' simpEnv'' mempty

evalBackend :: Pass Expr Atom
evalBackend expr = do
  backend <- asks evalEngine
  case backend of
    LLVMEngine engine -> do
      let inVars = arrayVars expr
      impFunction <- impPass (inVars, expr)
      countFlops impFunction
      let llvmFunc = impToLLVM impFunction
      (outVars, logs) <- liftIO $ execLLVM engine llvmFunc inVars
      tell logs
      return $ reStructureArrays (getType expr) $ map Var outVars
    InterpEngine -> return $ evalExpr mempty expr

arrayVars :: HasVars a => a -> [Var]
arrayVars x = [v:>ty | (v@(Name ArrayName _ _), L ty) <- envPairs (freeVars x)]

initializeBackend :: Backend -> IO BackendEngine
initializeBackend backend = case backend of
  LLVM -> liftM LLVMEngine $ newMVar mempty
  _ -> error "Not implemented"

substArrayLiterals :: (HasVars a, Subst a) => BackendEngine -> a -> IO a
substArrayLiterals backend x = do
  let vs = arrayVars x
  arrays <- requestArrays backend vs
  let arrayAtoms = map (Con . ArrayLit) arrays
  return $ subst (newLEnv vs arrayAtoms, mempty) x

-- TODO: think carefully about whether this is thread-safe
execLLVM :: LLVMEngine -> LLVMFunction -> [Var] -> IO ([Var], [Output])
execLLVM envRef fun@(LLVMFunction outTys _ _) inVars = do
  modifyMVar envRef $ \env -> do
    outRefs <- mapM newArrayRef outTys
    let inRefs = flip map inVars $ \v ->
                   case envLookup env v of
                     Just ref -> ref
                     Nothing  -> error "Array lookup failed"
    let (outNames, env') = nameItems (Name ArrayName "arr" 0) env outRefs
    let outVars = zipWith (\v (b,shape) -> v :> ArrayTy b shape) outNames outTys
    logs <- callLLVM fun outRefs inRefs
    return (env <> env', (outVars, logs))

requestArrays :: BackendEngine -> [Var] -> IO [Array]
requestArrays backend vs = case backend of
  LLVMEngine env -> do
    env' <- readMVar env
    forM vs $ \v -> do
      case envLookup env' v of
        Just ref -> loadArray ref
        Nothing -> error "Array lookup failed"
  _ -> error "Not implemented"

-- TODO: check here for upstream errors
typePass :: TopInfEnv -> Pass FModule (FModule, TopInfEnv)
typePass env m = do
  (typed, envOut) <- liftEither $ inferModule env m
  liftEither $ checkValid typed
  return (typed, envOut)

normalizePass :: Pass FModule Module
normalizePass = namedPass NormPass (return . normalizeModule)

-- TODO: add back logging
simpPass :: SubstEnv -> RuleEnv -> Pass Module (Module, SubstEnv)
simpPass substEnv rulesEnv m = return $ simplifyModule substEnv rulesEnv m

impPass :: Pass ([Var], Expr) ImpFunction
impPass = namedPass ImpPass (return . toImpFunction)

countFlops :: ImpFunction -> TopPassM ()
countFlops f = tell [PassInfo Flops "" (pprint (impFunctionFlops f))]

namedPass :: (Pretty a, Checkable b, Pretty b)
          => PassName -> Pass a b -> Pass a b
namedPass name pass x = do
  let passCtx  = pprint name ++ " pass with input:\n" ++ pprint x
  t1 <- liftIO getCurrentTime
  (ans, s) <- withDebugCtx passCtx $ printedPass (pass x)
  t2 <- liftIO getCurrentTime
  tell [PassInfo name (show (t2 `diffUTCTime` t1)) s]
  let checkCtx = "Checking after " ++ pprint name ++ " pass:\n" ++ pprint ans
  withDebugCtx checkCtx $ liftEither $ checkValid ans
  return ans

printedPass :: Pretty a => TopPassM a -> TopPassM (a, String)
printedPass m = do
  ans <- m
  let s = pprint ans
  -- uncover exceptions by forcing evaluation of printed result
  _ <- liftIO $ evaluate (length s)
  return (ans, s)

filterOutputs :: (Output -> Bool) -> TopPassM a -> TopPassM a
filterOutputs f m = do
  opts <- ask
  if logAll opts
    then m
    else do
      (ans, outs) <- liftIO $ runTopPassM opts m
      tell $ filter f outs
      liftEither ans

asTopPassM :: IO (Except a, [Output]) -> TopPassM a
asTopPassM m = do
  (ans, outs) <- liftIO m
  tell outs
  liftEither ans

withDebugCtx :: String -> TopPassM a -> TopPassM a
withDebugCtx msg m = catchError (catchHardErrors m) $ \e ->
  throwError (addDebugCtx msg e)

addErrSrc :: MonadError Err m => SourceBlock -> m a -> m a
addErrSrc block m = m `catchError` (throwError . addCtx block)

addCtx :: SourceBlock -> Err -> Err
addCtx block err@(Err e src s) = case src of
  Nothing -> err
  Just (start, stop) ->
    Err e Nothing $ s ++ "\n\n" ++ ctx
    where n = sbOffset block
          ctx = highlightRegion (start - n, stop - n) (sbText block)

addDebugCtx :: String -> Err -> Err
addDebugCtx ctx (Err CompilerErr c msg) = Err CompilerErr c msg'
  where msg' = msg ++ "\n=== context ===\n" ++ ctx ++ "\n"
addDebugCtx _ e = e

liftIOTop :: IO a -> TopPassM a
liftIOTop m = catchIOExcept $ (m >>= evaluate) `catch` \e ->
                 throwIO $ Err DataIOErr Nothing (show (e::IOError))

catchHardErrors :: TopPassM a -> TopPassM a
catchHardErrors m = do
  opts <- ask
  asTopPassM $ runTopPassM opts m `catch` asCompilerErr
  where asCompilerErr :: SomeException -> IO (Except a, [Output])
        asCompilerErr e = return (Left $ Err CompilerErr Nothing (show e), [])
