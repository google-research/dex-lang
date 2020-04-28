-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}

module TopLevel (evalBlock, EvalOpts (..), Backend (..)) where

import Control.Exception hiding (throw)
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer.Strict  hiding (pass)
import Control.Monad.Except hiding (Except)
import Data.Text.Prettyprint.Doc
import Data.Time.Clock (getCurrentTime, diffUTCTime)

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
import JAX
import JIT
import PPrint
import Parser
import Record
import Subst
import Util (highlightRegion)

data Backend = LLVM | Interp | JAX
data EvalOpts = EvalOpts
  { evalBackend :: Backend
  , preludeFile :: FilePath
  , logAll      :: Bool }

type TopPassM a = ReaderT EvalOpts (ExceptT Err (WriterT [Output] IO)) a
type Pass a b = a -> TopPassM b

-- TODO: handle errors due to upstream modules failing
evalBlock :: EvalOpts -> TopEnv -> SourceBlock -> IO (TopEnv, Result)
evalBlock opts env block = do
  (ans, outs) <- runTopPassM opts $ addErrSrc block $
                   evalSourceBlock env (sbContents block)
  case ans of
    Left err   -> return (mempty, Result outs (Left err))
    Right env' -> return (env'  , Result outs (Right ()))

runTopPassM :: EvalOpts -> TopPassM a -> IO (Except a, [Output])
runTopPassM opts m = runWriterT $ runExceptT $ runReaderT m opts

evalSourceBlock :: TopEnv -> SourceBlock' -> TopPassM TopEnv
evalSourceBlock env block = case block of
  RunModule m -> filterOutputs (const False) $ evalModule env m
  Command cmd (v, m) -> mempty <$ case cmd of
    EvalExpr fmt -> do
      val <- evalModuleVal env v m
      case fmt of
        Printed -> do
          s <- liftIOTop $ pprintVal val
          tell [TextOut s]
        Heatmap -> do
          output <- liftIOTop $ valToHeatmap val
          tell [output]
        Scatter -> do
          output <- liftIOTop $ valToScatter val
          tell [output]
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
  GetNameType v -> case topSubstEnv env `envLookup` v of
    Just (L val) -> tell [TextOut $ pprint (getType val)] >> return mempty
    _            -> throw UnboundVarErr $ pprint v
  IncludeSourceFile fname -> do
    source <- liftIOTop $ readFile fname
    evalSourceBlocks env $ map sbContents $ parseProg source
  LoadData p DexObject fname -> do
    source <- liftIOTop $ readFile fname
    let val = ignoreExcept $ parseData source
    let decl = LetMono p val
    let m = Module (mempty, foldMap lbind p) $ FModBody [decl] mempty
    filterOutputs (const False) $ evalModule env m
  LoadData p DexBinaryObject fname -> do
    val <- liftIOTop $ loadDataFile fname
    -- TODO: handle patterns and type annotations in binder
    let (RecLeaf b) = p
    let outEnv = b @> L val
    return $ TopEnv (substEnvType outEnv) outEnv mempty
  UnParseable _ s -> throw ParseErr s
  _               -> return mempty

evalSourceBlocks :: TopEnv -> [SourceBlock'] -> TopPassM TopEnv
evalSourceBlocks env blocks =
  liftM snd $ flip runCatT env $ flip mapM_ blocks $ \block -> do
    env' <- look
    env'' <- lift $ evalSourceBlock env' block
    extend env''

evalModuleVal :: TopEnv -> Var -> FModule -> TopPassM Val
evalModuleVal env v m = do
  env' <- filterOutputs (const False) $ evalModule env m
  let (L val) = topSubstEnv env' ! v
  return $ subst (topSubstEnv (env <> env'), mempty) val

-- TODO: extract only the relevant part of the env we can check for module-level
-- unbound vars and upstream errors here. This should catch all unbound variable
-- errors, but there could still be internal shadowing errors.
evalModule :: TopEnv -> Pass FModule TopEnv
evalModule env untyped = do
  typed     <- inferTypes env untyped
  optimized <- corePasses env typed
  backend <- asks evalBackend
  case backend of
    LLVM   -> evalJIT env optimized
    JAX    -> evalJAX optimized
    Interp -> evalInterp optimized

-- TODO: check here for upstream errors
inferTypes :: TopEnv -> Pass FModule Module
inferTypes env m =
      tell [PassInfo Parse "" (pprint m)]
  >>  namedPass TypePass (liftEither . inferModule env) m
  >>= namedPass NormPass (return     . normalizeModule)

corePasses :: TopEnv -> Pass Module Module
corePasses env = namedPass SimpPass (return . simplifyModule env)

evalJIT :: TopEnv -> Pass Module TopEnv
evalJIT env = namedPass ImpPass  (return . toImpModule env) >=> evalImp

evalImp :: Pass ImpModule TopEnv
evalImp m = do
  countFlops m
  (result, outs) <- liftIO $ evalModuleJIT m
  tell outs
  return result

evalJAX :: Pass Module TopEnv
evalJAX m = do
  (result, outs) <- liftIO $ evalModuleJAX m
  tell outs
  return result

evalInterp :: Pass Module TopEnv
evalInterp m = do
  (result, outs) <- liftIO $ evalModuleInterp m
  tell outs
  return result

namedPass :: (IsModule a, Pretty a, IsModule b, Pretty b)
          => PassName -> Pass a b -> Pass a b
namedPass name pass x = do
  let passCtx  = pprint name ++ " pass with input:\n" ++ pprint x
  t1 <- liftIO getCurrentTime
  (ans, s) <- withDebugCtx passCtx $ printedPass (pass x)
  t2 <- liftIO getCurrentTime
  tell [PassInfo name (show (t2 `diffUTCTime` t1)) s]
  let checkCtx = "Checking after " ++ pprint name ++ " pass:\n" ++ pprint ans
  withDebugCtx checkCtx $ liftEither $ checkModule ans
  return ans

countFlops :: ImpModule -> TopPassM ()
countFlops (Module _  m) = tell [PassInfo Flops "" (pprint (moduleFlops m))]

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
withDebugCtx msg m = catchError (catchHardErrors m) $ \e -> throwError (addDebugCtx msg e)

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
