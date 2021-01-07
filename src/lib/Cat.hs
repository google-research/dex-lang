-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module Cat (CatT, MonadCat, runCatT, look, extend, scoped, looks, extendLocal,
            extendR, captureW, asFst, asSnd, capture, asCat, evalCatT, evalCat,
            Cat, runCat, newCatT, catTraverse, evalScoped, execCat, execCatT,
            catFold, catFoldM, catMap, catMapM) where

-- Monad for tracking monoidal state

import Control.Applicative
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Identity
import Control.Monad.Except hiding (Except)

newtype CatT env m a = CatT (StateT (env, env) m a)
  deriving (Functor, Applicative, Monad, MonadTrans, MonadIO, MonadFail, Alternative)

type Cat env = CatT env Identity

class (Monoid env, Monad m) => MonadCat env m | m -> env where
  look   :: m env
  extend :: env -> m ()
  scoped :: m a -> m (a, env)

instance (Monoid env, Monad m) => MonadCat env (CatT env m) where
  look = CatT $ gets fst
  extend x = CatT $ do
    (fullState, localState) <- get
    put (fullState <> x, localState <> x)
  scoped (CatT m) = CatT $ do
    originalState <- get
    put (fst originalState, mempty)
    ans <- m
    newLocalState <- gets snd
    put originalState
    return (ans, newLocalState)

instance MonadCat env m => MonadCat env (StateT s m) where
  look = lift look
  extend x = lift $ extend x
  scoped m = StateT \s -> do
    ((ans, s'), env) <- scoped $ runStateT m s
    return $ ((ans, env), s')

instance MonadCat env m => MonadCat env (ReaderT r m) where
  look = lift look
  extend x = lift $ extend x
  scoped m = do r <- ask
                lift $ scoped $ runReaderT m r

instance (Monoid w, MonadCat env m) => MonadCat env (WriterT w m) where
  look = lift look
  extend x = lift $ extend x
  scoped m = do ((x, w), env) <- lift $ scoped $ runWriterT m
                tell w
                return (x, env)

instance MonadCat env m => MonadCat env (ExceptT e m) where
  look = lift look
  extend x = lift $ extend x
  scoped m = do (xerr, env) <- lift $ scoped $ runExceptT m
                case xerr of
                  Left err -> throwError err
                  Right x  -> return (x, env)

instance (Monoid env, MonadError e m) => MonadError e (CatT env m) where
  throwError = lift . throwError
  catchError m catch = do
    env <- look
    (ans, env') <- lift $ runCatT m env `catchError` (\e -> runCatT (catch e) env)
    extend env'
    return ans

instance (Monoid env, MonadReader r m) => MonadReader r (CatT env m) where
  ask = lift ask
  local f m = do
    env <- look
    (ans, env') <- lift $ local f $ runCatT m env
    extend env'
    return ans

runCatT :: (Monoid env, Monad m) => CatT env m a -> env -> m (a, env)
runCatT (CatT m) initEnv = do
  (ans, (_, newEnv)) <- runStateT m (initEnv, mempty)
  return (ans, newEnv)

evalCatT :: (Monoid env, Monad m) => CatT env m a -> m a
evalCatT m = fst <$> runCatT m mempty

execCatT :: (Monoid env, Monad m) => CatT env m a -> m env
execCatT m = snd <$> runCatT m mempty

newCatT :: (Monoid env, Monad m) => (env -> m (a, env)) -> CatT env m a
newCatT f = do
  env <- look
  (ans, env') <- lift $ f env
  extend env'
  return ans

runCat :: Monoid env => Cat env a -> env -> (a, env)
runCat m env = runIdentity $ runCatT m env

evalCat :: Monoid env => Cat env a -> a
evalCat m = runIdentity $ evalCatT m

execCat :: Monoid env => Cat env a -> env
execCat m = runIdentity $ execCatT m

looks :: (Monoid env, MonadCat env m) => (env -> a) -> m a
looks getter = liftM getter look

evalScoped :: Monoid env => Cat env a -> Cat env a
evalScoped m = fst <$> scoped m

capture :: (Monoid env, MonadCat env m) => m a -> m (a, env)
capture m = do
  (x, env) <- scoped m
  extend env
  return (x, env)

extendLocal :: (Monoid env, MonadCat env m) => env -> m a -> m a
extendLocal x m = do
  ((ans, env), _) <- scoped $ do extend x
                                 scoped m
  extend env
  return ans

-- Not part of the cat monad, but related utils for monoidal envs

catTraverse :: (Monoid menv, MonadReader env m, Traversable f)
                  => (a -> m (b, menv)) -> (menv -> env) -> f a -> menv -> m (f b, menv)
catTraverse f inj xs env = runCatT (traverse (asCat f inj) xs) env

catFoldM :: (Monoid env, Traversable t, Monad m)
        => (env -> a -> m env) -> env -> t a -> m env
catFoldM f env xs = liftM snd $ flip runCatT env $ forM_ xs \x -> do
  cur <- look
  new <- lift $ f cur x
  extend new

catFold :: (Monoid env, Traversable t)
        => (env -> a -> env) -> env -> t a -> env
catFold f env xs = runIdentity $ catFoldM (\e x -> Identity $ f e x) env xs

catMapM :: (Monoid env, Traversable t, Monad m)
        => (env -> a -> m (b, env)) -> env -> t a -> m (t b, env)
catMapM f env xs = flip runCatT env $ forM xs \x -> do
  cur <- look
  (y, new) <- lift $ f cur x
  extend new
  return y

catMap :: (Monoid env, Traversable t)
        => (env -> a -> (b, env)) -> env -> t a -> (t b, env)
catMap f env xs = runIdentity $ catMapM (\e x -> Identity $ f e x) env xs

asCat :: (Monoid menv, MonadReader env m)
      => (a -> m (b, menv)) -> (menv -> env) -> a -> CatT menv m b
asCat f inj x = do
  env' <- look
  (x', env'') <- lift $ local (const $ inj env') (f x)
  extend env''
  return x'

extendR :: (Monoid env, MonadReader env m) => env -> m a -> m a
extendR x m = local (<> x) m

asFst :: Monoid b => a -> (a, b)
asFst x = (x, mempty)

asSnd :: Monoid a => b -> (a, b)
asSnd y = (mempty, y)

captureW :: MonadWriter w m => m a -> m (a, w)
captureW m = censor (const mempty) (listen m)
