-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module SaferNames.MTL1 (
    MonadTrans11 (..),
    FallibleMonoid1 (..), WriterT1 (..), runWriterT1,
    MaybeT1 (..), runMaybeT1,
  ) where

import Control.Monad.Writer.Strict
import Control.Monad.Trans.Maybe
import Control.Applicative

import SaferNames.Name
import SaferNames.Syntax

class MonadTrans11 (t :: MonadKind1 -> MonadKind1) where
  lift11 :: Monad1 m => m n a -> t m n a

-------------------- WriterT1 --------------------

-- A monoid with a special "sink" element. We expect that
--   mfail <> _ = mfail
-- as well as
--   _ <> mfail = mfail.
class Monoid1 w => FallibleMonoid1 w where
  mfail :: w n

newtype WriterT1 (w :: E) (m :: MonadKind1) (n :: S) (a :: *) =
  WriterT1 { runWriterT1' :: (WriterT (w n) (m n) a) }
  deriving (Functor, Applicative, Monad, MonadWriter (w n))

runWriterT1 :: WriterT1 w m n a -> m n (a, w n)
runWriterT1 = runWriterT . runWriterT1'

instance (AlwaysImmut m, Monoid1 w) => AlwaysImmut (WriterT1 w m) where
  getImmut = lift11 $ getImmut

instance Monoid1 w => MonadTrans11 (WriterT1 w) where
  lift11 = WriterT1 . lift

instance (InjectableE w, Monoid1 w, BindingsReader m) => BindingsReader (WriterT1 w m) where
  getBindings = lift11 getBindings

instance (InjectableE w, Monoid1 w, ScopeReader m) => ScopeReader (WriterT1 w m) where
  getScope = lift11 getScope
  getDistinct = lift11 getDistinct
  liftImmut m = WriterT1 $ WriterT $ fromPairE <$>
    (liftImmut $ (uncurry PairE) <$> (runWriterT $ runWriterT1' m))

instance (InjectableE w, HoistableE w, FallibleMonoid1 w, BindingsExtender m)
         => BindingsExtender (WriterT1 w m) where
  extendBindings frag m = WriterT1 $ WriterT $ do
    (ans, update) <- extendBindings frag (runWriterT $ runWriterT1' m)
    case hoist frag update of
      HoistSuccess topUpdate -> return (ans, topUpdate)
      HoistFailure _ -> return (ans, mfail)

-------------------- MaybeT1 --------------------

newtype MaybeT1 (m :: MonadKind1) (n :: S) (a :: *) =
  MaybeT1 { runMaybeT1' :: (MaybeT (m n) a) }
  deriving (Functor, Applicative, Monad, Alternative)

runMaybeT1 :: MaybeT1 m n a -> m n (Maybe a)
runMaybeT1 = runMaybeT . runMaybeT1'

instance AlwaysImmut m => AlwaysImmut (MaybeT1 m) where
  getImmut = lift11 $ getImmut

instance MonadTrans11 MaybeT1 where
  lift11 = MaybeT1 . lift

instance BindingsReader m => BindingsReader (MaybeT1 m) where
  getBindings = lift11 getBindings

instance ScopeReader m => ScopeReader (MaybeT1 m) where
  getScope = lift11 getScope
  getDistinct = lift11 getDistinct
  liftImmut m = MaybeT1 $ MaybeT $ fromMaybeE <$>
    (liftImmut $ toMaybeE <$> (runMaybeT $ runMaybeT1' m))

instance BindingsExtender m => BindingsExtender (MaybeT1 m) where
  extendBindings frag m = MaybeT1 $ MaybeT $
    extendBindings frag $ runMaybeT $ runMaybeT1' m
