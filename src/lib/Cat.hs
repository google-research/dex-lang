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
            extendR, captureW, asFst, asSnd, capture, asCat, evalCatT,
            Cat, runCat, newCatT, catTraverse, catFold) where

-- Monad for tracking monoidal state

import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Identity
import Control.Monad.Except hiding (Except)

newtype CatT env m a = CatT (StateT (env, env) m a)
  deriving (Functor, Applicative, Monad, MonadTrans, MonadIO)

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
    put $ (fst originalState, mempty)
    ans <- m
    newLocalState <- gets snd
    put originalState
    return (ans, newLocalState)

instance MonadCat env m => MonadCat env (StateT s m) where
  look = lift look
  extend x = lift $ extend x
  scoped = undefined -- is this even possible?

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
  scoped = error "TODO"

instance (Monoid env, MonadError e m) => MonadError e (CatT env m) where
  throwError = lift . throwError
  catchError m catch = do
    env <- look
    (ans, env') <- lift $ runCatT m env `catchError` (\e -> runCatT (catch e) env)
    extend env'
    return ans

runCatT :: (Monoid env, Monad m) => CatT env m a -> env -> m (a, env)
runCatT (CatT m) initEnv = do
  (ans, (_, newEnv)) <- runStateT m (initEnv, mempty)
  return (ans, newEnv)

evalCatT :: (Monoid env, Monad m) => CatT env m a -> m a
evalCatT m = liftM fst $ runCatT m mempty

newCatT :: (Monoid env, Monad m) => (env -> m (a, env)) -> CatT env m a
newCatT  f = do
  env <- look
  (ans, env') <- lift $ f env
  extend env'
  return ans

runCat :: Monoid env => Cat env a -> env -> (a, env)
runCat m env = runIdentity $ runCatT m env

looks :: (Monoid env, MonadCat env m) => (env -> a) -> m a
looks getter = liftM getter look

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

catTraverse :: (Monoid env, MonadReader env m, Traversable f)
                  => (a -> m (b, env)) -> f a -> m (f b, env)
catTraverse f xs = do
  env <- ask
  runCatT (traverse (asCat f) xs) env

catFold :: (Monoid env, MonadReader env m, Traversable f)
        => (a -> m env) -> f a -> m env
catFold f xs = liftM snd $ catTraverse (liftM ((,) ()) . f) xs

asCat :: (Monoid env, MonadReader env m)
            => (a -> m (b, env)) -> a -> CatT env m b
asCat f x = do
  env' <- look
  (x', env'') <- lift $ local (const env') (f x)
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
