-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}

module TopLevel (evalBlock, Backend (..)) where

import Control.Exception hiding (throw)
import Control.Monad.Writer.Strict
import Control.Monad.Except hiding (Except)
import Data.Text.Prettyprint.Doc

import Syntax
import DeShadow
import Env
import Type
import Inference
import Normalize
import Simplify
import Serialize
import Imp
import JIT
import PPrint
import Util (highlightRegion)

data Backend = Jit | Interp
type TopPassM a = ExceptT Err (WriterT [Output] IO) a

-- TODO: handle errors due to upstream modules failing
evalBlock :: Backend -> TopEnv -> SourceBlock -> IO (TopEnv, Result)
evalBlock _ env block = do
  (ans, outs) <- runTopPassM $ addErrSrc block $ evalSourceBlock env (sbContents block)
  case ans of
    Left err   -> return (mempty, Result outs (Left err))
    Right env' -> return (env'  , Result outs (Right ()))

runTopPassM :: TopPassM a -> IO (Except a, [Output])
runTopPassM m = runWriterT $ runExceptT m

evalSourceBlock :: TopEnv -> SourceBlock' -> TopPassM TopEnv
evalSourceBlock env block = case block of
  RunModule m -> filterOutputs (const False) $ evalModule env m
  Command cmd (v, m) -> case cmd of
    EvalExpr fmt -> do
      env' <- filterOutputs (const False) $ evalModule env m
      let (L (Left val)) = env' ! v
      val' <- liftIO $ loadAtomVal val
      tell [ValOut fmt val']
      return mempty
    GetType -> do  -- TODO: don't actually evaluate it
      env' <- filterOutputs (const False) $ evalModule env m
      let (L (Left val)) = env' ! v
      val' <- liftIO $ loadAtomVal val
      tell [TextOut $ pprint (getType val')]
      return mempty
    ShowPasses -> liftM (const mempty) $ filterOutputs f $ evalModule env m
      where f out = case out of PassInfo _ _ -> True; _ -> False
    ShowPass s -> liftM (const mempty) $ filterOutputs f $ evalModule env m
      where f out = case out of PassInfo s' _ | s == s' -> True; _ -> False
    _ -> return mempty -- TODO
  IncludeSourceFile _ -> undefined
  LoadData _ _ _      -> undefined
  UnParseable _ s -> throw ParseErr s
  _               -> return mempty

-- TODO: extract only the relevant part of the env we can check for module-level
-- unbound vars and upstream errors here. This should catch all unbound variable
-- errors, but there could still be internal shadowing errors.
evalModule :: TopEnv -> FModule -> TopPassM TopEnv
evalModule env = inferTypes env >=> evalTyped env

-- TODO: check here for upstream errors
inferTypes :: TopEnv -> FModule -> TopPassM FModule
inferTypes env m = do
  mds   <- asPass "deshadow"       (liftEither . deShadowModule env) m
  typed <- asPass "type inference" (liftEither . inferModule    env) mds
  liftEither $ checkFModule typed
  return typed

evalTyped :: TopEnv -> FModule -> TopPassM TopEnv
evalTyped env m = ($ m) $
      asPass "normalize" (return . normalizeModule env) >=> checkPass ty checkModule
  >=> asPass "simplify"  (return . simplifyPass)        >=> checkPass ty checkModule
  >=> asPass "imp"       (return . toImpModule)         >=> checkPass ty checkImpModule
  >=> asPass "jit" (liftIO . evalModuleJIT)
  where
    (ModuleType _ exports) = moduleType m
    ty = ModuleType mempty exports

checkPass :: (Pretty a, IsModule a) => ModuleType -> (a -> Except ()) -> a -> TopPassM a
checkPass ty f x = withDebugCtx ("Checking: \n" ++ pprint x) $ do
  liftEither (f x)
  let ty' = moduleType x
  when (ty /= ty') $ throw CompilerErr $
      "Wrong module type.\nExpected: " ++ pprint ty
                     ++ "\n  Actual: " ++ pprint ty'
  return x

asPass :: (Pretty a, Pretty b) => String -> (a -> TopPassM b) -> a -> TopPassM b
asPass name f x = do
  let ctx = name ++ " pass with input:\n" ++ pprint x
  (ans, s) <- withDebugCtx ctx $ printedPass (f x)
  tell [PassInfo name s]
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
  (ans, outs) <- liftIO $ runTopPassM m
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

catchHardErrors :: TopPassM a -> TopPassM a
catchHardErrors m = asTopPassM $ runTopPassM m `catch` asCompilerErr
  where asCompilerErr :: SomeException -> IO (Except a, [Output])
        asCompilerErr e = return (Left $ Err CompilerErr Nothing (show e), [])
