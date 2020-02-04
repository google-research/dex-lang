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
import Flops
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
      val' <- liftIO $ loadAtomVal [] val
      tell [ValOut fmt val']
      return mempty
    GetType -> do  -- TODO: don't actually evaluate it
      env' <- filterOutputs (const False) $ evalModule env m
      let (L (Left val)) = env' ! v
      val' <- liftIO $ loadAtomVal [] val
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

inferTypes :: TopEnv -> FModule -> TopPassM FModule
inferTypes env =
      exceptPass "deshadow"       (deShadowModule env)
  >=> exceptPass "type inference" (inferModule    env) >=> checkPass checkFModule

-- TODO return a `ModuleP ()` here, representing a fully-evaluated module
evalTyped :: TopEnv -> FModule -> TopPassM TopEnv
evalTyped env =
      asPass "normalize" (normalizeModule env) >=> checkPass checkModule
  >=> asPass "simplify"  simplifyPass          >=> checkPass checkModule
  >=> asPass "imp" toImpModule                 >=> checkPass checkImpModule
  >=> analysisPass "flops" moduleFlops
  >=> ioPass "jit" evalModuleJIT

checkPass :: (a -> Except ()) -> a -> TopPassM a
checkPass f x = liftEither (f x) >> return x

exceptPass :: Pretty b => String -> (a -> Except b) -> a -> TopPassM b
exceptPass s f x = namedPass s $ liftEither (f x)

asPass :: Pretty b => String -> (a -> b) -> a -> TopPassM b
asPass s f x = namedPass s $ return (f x)

ioPass :: String -> (a -> IO b) -> a -> TopPassM b
ioPass _ f x = liftIO (f x)

analysisPass :: Pretty b => String -> (a -> b) -> a -> TopPassM a
analysisPass name f x = namedPass name (return (f x)) >> return x

namedPass :: Pretty a => String -> TopPassM a -> TopPassM a
namedPass name m = do
  (ans, s) <- asTopPassM $ runTopPassM (printedPass m) `catch` asCompilerErr name
  tell [PassInfo name s]
  return ans

printedPass :: Pretty a => TopPassM a -> TopPassM (a, String)
printedPass m = do
  ans <- m
  let s = pprint ans
  -- uncover exceptions by forcing evaluation of printed result
  _ <- liftIO $ evaluate (length s)
  return (ans, s)

asCompilerErr :: String -> SomeException -> IO (Except a, [Output])
asCompilerErr name e = return (Left $ Err CompilerErr Nothing msg, [])
  where msg = "Error in " ++ name ++ " pass:\n" ++ show e

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

addErrSrc :: MonadError Err m => SourceBlock -> m a -> m a
addErrSrc block m = m `catchError` (throwError . addCtx block)

addCtx :: SourceBlock -> Err -> Err
addCtx block err@(Err e src s) = case src of
  Nothing -> err
  Just (start, stop) ->
    Err e Nothing $ s ++ "\n\n" ++ ctx
    where n = sbOffset block
          ctx = highlightRegion (start - n, stop - n) (sbText block)
