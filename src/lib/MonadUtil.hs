-- Copyright 2023 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module MonadUtil (
  DefuncState (..), LabelReader (..), SingletonLabel (..), FreshNames (..),
  runFreshNameT, FreshNameT (..)) where

import Control.Monad.Reader
import Control.Monad.State.Strict

-- === Defunctionalized state ===
-- Interface for state whose allowable updates are specified by a data type.
-- Useful for `IncState`, for specifying read-only env components, or
-- generally for specifying certain constraints on updates.

class DefuncState d m | m -> d where
  update :: d -> m ()

class LabelReader (l :: * -> *) m | m -> l where
  getl :: l a -> m a

data SingletonLabel a b where
  It :: SingletonLabel a a

-- === Fresh name monad ===

-- Used for ad-hoc names with no nested binders that don't need to be treated
-- carefully using the whole "foil" name system.

class Monad m => FreshNames a m | m -> a where
  freshName :: m a

newtype FreshNameT m a = FreshNameT { runFreshNameT' :: StateT Int m a }
        deriving (Functor, Applicative, Monad, MonadIO)

instance MonadIO m => FreshNames Int (FreshNameT m) where
  freshName = FreshNameT do
    fresh <- get
    put (fresh + 1)
    return fresh

instance FreshNames a m => FreshNames a (ReaderT r m) where
  freshName = lift freshName

runFreshNameT :: MonadIO m => FreshNameT m a -> m a
runFreshNameT cont = evalStateT (runFreshNameT' cont) 0
