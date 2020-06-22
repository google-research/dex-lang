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
import Data.Maybe (fromJust)

import Array
import Syntax
import Cat
import Env
import Type
import Inference
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
import JAX
import Util (highlightRegion, foldMapM)

data Backend = LLVM | Interp | JAX  deriving (Show, Eq)
data EvalConfig = EvalConfig
  { backendName :: Backend
  , preludeFile :: FilePath
  , logFile     :: Maybe FilePath
  , evalEngine  :: BackendEngine
  , logService  :: Logger [Output] }

data BackendEngine = LLVMEngine LLVMEngine
                   | JaxServer JaxServer
                   | InterpEngine

type LLVMEngine = MVar (Env (Ptr ()))
type JaxServer = PipeServer ( (JaxFunction, [JVar]) -> ([JVar], String)
                           ,( [JVar] -> [Array]
                           ,( Array -> ()  -- for debugging
                           ,())))

type TopPassM a = ReaderT EvalConfig IO a

-- TODO: handle errors due to upstream modules failing
evalSourceBlock :: EvalConfig -> TopEnv -> SourceBlock -> IO (TopEnv, Result)
evalSourceBlock opts env block = do
  (ans, outs) <- runTopPassM opts $ evalSourceBlockM env block
  let outs' = filter (keepOutput block) outs
  case ans of
    Left err   -> return (mempty, Result outs' (Left (addCtx block err)))
    Right env' -> return (env'  , Result outs' (Right ()))

runTopPassM :: EvalConfig -> TopPassM a -> IO (Except a, [Output])
runTopPassM opts m = runLogger (logFile opts) $ \logger ->
  runExceptT $ catchIOExcept $ runReaderT m $ opts {logService = logger}

evalSourceBlockM :: TopEnv -> SourceBlock -> TopPassM TopEnv
evalSourceBlockM env@(TopEnv substEnv) block = case sbContents block of
  RunModule m -> evalUModule env m
  Command cmd (v, m) -> mempty <$ case cmd of
    EvalExpr fmt -> do
      val <- evalUModuleVal env v m
      case fmt of
        Printed -> do
          logTop $ TextOut $ pprintVal val
        Heatmap -> logTop $ valToHeatmap val
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
    ShowPasses -> void $ evalUModule env m
    ShowPass _ -> void $ evalUModule env m
    TimeIt     -> void $ evalUModule env m
  GetNameType v -> case envLookup substEnv (v:>()) of
    Just x -> logTop (TextOut $ pprint (getType x)) >> return mempty
    _      -> liftEitherIO $ throw UnboundVarErr $ pprint v
  IncludeSourceFile fname -> do
    source <- liftIO $ readFile fname
    evalSourceBlocks env $ parseProg source
  LoadData pat DexObject fname -> do
    source <- liftIO $ readFile fname
    let val = ignoreExcept $ parseData source
    let (WithSrc _ (PatBind b), _) = pat
    evalUModule env $ UModule [] [varName b] [ULet pat val]
  LoadData pat DexBinaryObject fname -> do
    val <- liftIO $ loadDataFile fname
    -- TODO: handle patterns and type annotations in binder
    let (WithSrc _ (PatBind b), _) = pat
    let outEnv = b @> val
    return $ TopEnv outEnv
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
evalSourceBlocks env blocks = catFoldM evalSourceBlockM env blocks

evalUModuleVal :: TopEnv -> Name -> UModule -> TopPassM Val
evalUModuleVal env v m = do
  env' <- evalUModule env m
  let (TopEnv simpEnv) = env <> env'
  let val = subst (simpEnv, mempty) $ simpEnv ! (v:>())
  backend <- asks evalEngine
  liftIO $ substArrayLiterals backend val

-- TODO: extract only the relevant part of the env we can check for module-level
-- unbound vars and upstream errors here. This should catch all unbound variable
-- errors, but there could still be internal shadowing errors.
evalUModule :: TopEnv -> UModule -> TopPassM TopEnv
evalUModule env untyped = do
  -- TODO: it's handy to log the env, but we need to filter out just the
  --       relevant part (transitive closure of free vars)
  -- logTop $ MiscLog $ "\n" ++ pprint env
  logPass Parse untyped
  typed <- typePass env untyped
  checkPass TypePass typed
  evalModule env typed

evalModule :: TopEnv -> Module -> TopPassM TopEnv
evalModule (TopEnv simpEnv) normalized = do
  let (defunctionalized, simpEnv') = simplifyModule simpEnv normalized
  checkPass SimpPass defunctionalized
  let (Module _ _ outVars dfExpr) = defunctionalized
  case dfExpr of
    Block [] (Atom UnitVal) -> do
      return $ TopEnv simpEnv'
    _ -> do
      results <- (ignoreExcept . fromConsList) <$> evalBackend dfExpr
      let simpEnv'' = subst (newEnv outVars results, mempty) simpEnv'
      return $ TopEnv simpEnv''

initializeBackend :: Backend -> IO BackendEngine
initializeBackend backend = case backend of
  LLVM -> liftM LLVMEngine $ newMVar mempty
  JAX  -> liftM JaxServer $ startPipeServer "python3" ["misc/py/jax_call.py"]
  _ -> error "Not implemented"

arrayVars :: HasVars a => a -> [Var]
arrayVars x = map (\(v@(Name ArrayName _ _), ty) -> v :> ty) $ envPairs (freeVars x)

evalBackend :: Block -> TopPassM Atom
evalBackend block = do
  backend <- asks evalEngine
  logger  <- asks logService
  let inVars = arrayVars block
  case backend of
    LLVMEngine engine -> do
      let (impFunction, impAtom) = toImpFunction (inVars, block)
      checkPass ImpPass impFunction
      logPass Flops $ impFunctionFlops impFunction
      let llvmFunc = impToLLVM impFunction
      lift $ modifyMVar engine $ \env -> do
        let inPtrs = fmap (env !) inVars
        outPtrs <- callLLVM logger llvmFunc inPtrs
        let (ImpFunction impOutVars _ _) = impFunction
        let (outNames, env') = nameItems (Name ArrayName "arr" 0) env outPtrs
        substEnv <- foldMapM mkSubstEnv $ zip3 outNames impOutVars outPtrs
        return (env <> env', subst (substEnv, mempty) impAtom)
      where
        mkSubstEnv :: (Name, Var, Ptr ()) -> IO SubstEnv
        mkSubstEnv (outName, impVar, outPtr) = case varType impVar of
          ArrayTy (BaseTy b) -> do
            lit <- loadScalar b outPtr
            return $ impVar @> (Con $ Lit $ lit)
          _        -> return $ impVar @> (Var $ (outName :> varType impVar))
        loadScalar :: BaseType -> Ptr () -> IO LitVal
        loadScalar b ptr = fromJust . scalarFromArray <$> (loadArray $ ArrayRef (1, b) ptr)
    JaxServer server -> do
      -- callPipeServer (psPop (psPop server)) $ arrayFromScalar (IntLit 123)
      let jfun = toJaxFunction (inVars, block)
      checkPass JAXPass jfun
      let jfunSimp = simplifyJaxFunction jfun
      checkPass JAXSimpPass jfunSimp
      let jfunDCE = dceJaxFunction jfunSimp
      checkPass JAXSimpPass jfunDCE
      let inVars' = map (fmap typeToJType) inVars
      (outVars, jaxprDump) <- callPipeServer server (jfunDCE, inVars')
      logPass JaxprAndHLO jaxprDump
      let outVars' = map (fmap jTypeToType) outVars
      return $ reStructureArrays (getType block) $ map Var outVars'
    InterpEngine -> return $ evalBlock mempty block


requestArrays :: BackendEngine -> [Var] -> IO [Array]
requestArrays _ [] = return []
requestArrays backend vs = case backend of
  LLVMEngine env -> do
    env' <- readMVar env
    forM vs $ \v@(_ :> ArrayTy ty) -> do
      case envLookup env' v of
        Just ref -> loadArray (ArrayRef (typeToArrayType ty) ref)
        Nothing -> error "Array lookup failed"
  JaxServer server -> do
    let vs' = map (fmap typeToJType) vs
    callPipeServer (psPop server) vs'
  _ -> error "Not implemented"

substArrayLiterals :: (HasVars a, HasType a) => BackendEngine -> a -> IO a
substArrayLiterals backend x = do
  -- We first need to substitute the arrays used in the types. Our atom types
  -- are monotonic, so it's enough to ask for the arrays used in the type of the
  -- atom as a whole, without worrying about types hidden within the atom.
  x' <- substArrayLiterals' backend (arrayVars (getType x)) x
  substArrayLiterals' backend (arrayVars x') x'

substArrayLiterals' :: HasVars a => BackendEngine -> [Var] -> a -> IO a
substArrayLiterals' backend vs x = do
  arrays <- requestArrays backend vs
  let arrayAtoms = [Con $ ArrayLit ty arr | (_:>ty, arr) <- zip vs arrays]
  return $ subst (newEnv vs arrayAtoms, mempty) x

-- TODO: check here for upstream errors
typePass :: TopEnv -> UModule -> TopPassM Module
typePass env m = liftEitherIO $ inferModule env m

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
