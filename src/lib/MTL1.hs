-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

module MTL1 (
    MonadTrans11 (..), HoistableState (..),
    FallibleMonoid1 (..), WriterT1 (..), runWriterT1,
    StateT1, pattern StateT1, runStateT1, MonadState1,
    MaybeT1 (..), runMaybeT1, ReaderT1 (..), runReaderT1,
    ScopedT1, pattern ScopedT1, runScopedT1
  ) where

import Control.Monad.Reader
import Control.Monad.Writer.Strict
import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe
import Control.Applicative

import Name
import Syntax
import Err

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

instance (SinkableE w, Monoid1 w, EnvReader m) => EnvReader (WriterT1 w m) where
  unsafeGetEnv = lift11 unsafeGetEnv

instance (SinkableE w, Monoid1 w, ScopeReader m) => ScopeReader (WriterT1 w m) where
  unsafeGetScope = lift11 unsafeGetScope
  getDistinct = lift11 getDistinct
  liftImmut m = WriterT1 $ WriterT $ fromPairE <$>
    (liftImmut $ (uncurry PairE) <$> (runWriterT $ runWriterT1' m))

instance (SinkableE w, HoistableE w, FallibleMonoid1 w, EnvExtender m)
         => EnvExtender (WriterT1 w m) where
  extendEnv frag m = WriterT1 $ WriterT $ do
    (ans, update) <- extendEnv frag (runWriterT $ runWriterT1' m)
    case hoist frag update of
      HoistSuccess topUpdate -> return (ans, topUpdate)
      HoistFailure _ -> return (ans, mfail)

-------------------- ReaderT1 --------------------

newtype ReaderT1 (r :: E) (m :: MonadKind1) (n :: S) (a :: *) =
  ReaderT1 { runReaderT1' :: (ReaderT (r n) (m n) a) }
  deriving (Functor, Applicative, Monad, MonadFail, MonadReader (r n))

runReaderT1 :: r n -> ReaderT1 r m n a -> m n a
runReaderT1 r m = runReaderT (runReaderT1' m) r

instance AlwaysImmut m => AlwaysImmut (ReaderT1 r m) where
  getImmut = lift11 $ getImmut

instance MonadTrans11 (ReaderT1 r) where
  lift11 = ReaderT1 . lift

instance (SinkableE r, EnvReader m) => EnvReader (ReaderT1 r m) where
  unsafeGetEnv = lift11 unsafeGetEnv

instance (SinkableE r, ScopeReader m) => ScopeReader (ReaderT1 r m) where
  unsafeGetScope = lift11 unsafeGetScope
  getDistinct = lift11 getDistinct
  liftImmut m = ReaderT1 $ ReaderT \r ->
    liftImmut $ runReaderT (runReaderT1' m) r

instance (SinkableE r, EnvExtender m) => EnvExtender (ReaderT1 r m) where
  extendEnv frag m = ReaderT1 $ ReaderT \r -> do
    extendEnv frag (runReaderT1 (sink r) m)

instance (Monad1 m, Fallible (m n)) => Fallible (ReaderT1 r m n) where
  throwErrs = lift11 . throwErrs
  addErrCtx ctx (ReaderT1 m) = ReaderT1 $ addErrCtx ctx m

-------------------- StateT1 --------------------

newtype StateT1 (s :: E) (m :: MonadKind1) (n :: S) (a :: *) =
  WrapStateT1 { runStateT1' :: (StateT (s n) (m n) a) }
  deriving (Functor, Applicative, Monad, MonadState (s n), MonadFail)

pattern StateT1 :: ((s n) -> m n (a, s n)) -> StateT1 s m n a
pattern StateT1 f = WrapStateT1 (StateT f)

type MonadState1 (e::E) (m::MonadKind1) = forall n. MonadState (e n) (m n)

{-# COMPLETE StateT1 #-}

runStateT1 :: StateT1 s m n a -> s n -> m n (a, s n)
runStateT1 = runStateT . runStateT1'

instance MonadTrans11 (StateT1 s) where
  lift11 = WrapStateT1 . lift

instance (SinkableE s, EnvReader m) => EnvReader (StateT1 s m) where
  unsafeGetEnv = lift11 unsafeGetEnv

instance (SinkableE s, ScopeReader m) => ScopeReader (StateT1 s m) where
  unsafeGetScope = lift11 unsafeGetScope
  getDistinct = lift11 getDistinct
  liftImmut m = StateT1 \s -> fromPairE <$> liftImmut do
    s' <- sinkM s
    uncurry PairE <$> runStateT1 m s'

instance (Monad1 m, Fallible (m n)) => Fallible (StateT1 s m n) where
  throwErrs = lift11 . throwErrs
  addErrCtx ctx (WrapStateT1 m) = WrapStateT1 $ addErrCtx ctx m

instance (Monad1 m, Catchable (m n)) => Catchable (StateT1 s m n) where
  catchErr (WrapStateT1 m) f = WrapStateT1 $ catchErr m (runStateT1' . f)

instance (Monad1 m, CtxReader (m n)) => CtxReader (StateT1 s m n) where
  getErrCtx = lift11 getErrCtx

instance AlwaysImmut m => AlwaysImmut (StateT1 s m) where
  getImmut = lift11 getImmut

class HoistableState (s::E) (m::MonadKind1) where
  hoistState :: BindsNames b => s n -> b n l -> s l -> m n (s n)

instance (SinkableE s, EnvExtender m, HoistableState s m) => EnvExtender (StateT1 s m) where
  extendEnv frag m = StateT1 \s -> do
    (ans, s') <- extendEnv frag $ runStateT1 m (sink s)
    s'' <- hoistState s frag s'
    return (ans, s'')

-------------------- ScopedT1 --------------------

newtype ScopedT1 (s :: E) (m :: MonadKind1) (n :: S) (a :: *) =
  WrapScopedT1 { runScopedT1' :: StateT1 s m n a }
  deriving ( Functor, Applicative, Monad, MonadState (s n), MonadFail
           , MonadTrans11, EnvReader, ScopeReader, AlwaysImmut )

pattern ScopedT1 :: ((s n) -> m n (a, s n)) -> ScopedT1 s m n a
pattern ScopedT1 f = WrapScopedT1 (StateT1 f)

runScopedT1 :: Monad1 m => ScopedT1 s m n a -> s n -> m n a
runScopedT1 m s = fst <$> runStateT1 (runScopedT1' m) s

deriving instance (Monad1 m, Fallible1 m) => Fallible (ScopedT1 s m n)
deriving instance (Monad1 m, Catchable1 m) => Catchable (ScopedT1 s m n)
deriving instance (Monad1 m, CtxReader1 m) => CtxReader (ScopedT1 s m n)

instance (SinkableE s, EnvExtender m) => EnvExtender (ScopedT1 s m) where
  extendEnv frag m = ScopedT1 \s -> do
    ans <- extendEnv frag $ runScopedT1 m (sink s)
    return (ans, s)

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

instance Monad (m n) => MonadFail (MaybeT1 m n) where
  fail s = MaybeT1 (fail s)

instance Monad (m n) => Fallible (MaybeT1 m n) where
  throwErrs _ = empty
  addErrCtx _ cont = cont

instance EnvReader m => EnvReader (MaybeT1 m) where
  unsafeGetEnv = lift11 unsafeGetEnv

instance ScopeReader m => ScopeReader (MaybeT1 m) where
  unsafeGetScope = lift11 unsafeGetScope
  getDistinct = lift11 getDistinct
  liftImmut m = MaybeT1 $ MaybeT $ fromMaybeE <$>
    (liftImmut $ toMaybeE <$> (runMaybeT $ runMaybeT1' m))

instance EnvExtender m => EnvExtender (MaybeT1 m) where
  extendEnv frag m = MaybeT1 $ MaybeT $
    extendEnv frag $ runMaybeT $ runMaybeT1' m
