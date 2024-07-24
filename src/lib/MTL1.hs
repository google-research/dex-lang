-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module MTL1 where

import Control.Monad.Reader
import Control.Monad.Writer.Class
import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe
import Control.Applicative
import Data.Foldable (toList)

import Name
import Err
-- import Types.Top (Env)
import Util (SnocList (..), snoc, emptySnocList)

class MonadTrans11 (t :: MonadKind1 -> MonadKind1) where
  lift11 :: Monad1 m => m n a -> t m n a

-------------------- WriterT1 --------------------

newtype WriterT1 (w :: E) (m :: MonadKind1) (n :: S) (a :: *) =
  WrapWriterT1 { runWriterT1' :: (StateT (w n) (m n) a) }
  deriving ( Functor, Applicative, Monad, MonadFail
           , Fallible, MonadIO)

pattern WriterT1 :: ((w n) -> m n (a, w n)) -> WriterT1 w m n a
pattern WriterT1 f = WrapWriterT1 (StateT f)
{-# COMPLETE WriterT1 #-}

runWriterT1 :: Monoid1 w => WriterT1 w m n a -> m n (a, w n)
runWriterT1 = runWriterT1From mempty
{-# INLINE runWriterT1 #-}

runWriterT1From :: Monoid1 w => w n -> WriterT1 w m n a -> m n (a, w n)
runWriterT1From w m = runStateT (runWriterT1' m) w
{-# INLINE runWriterT1From #-}

instance (Monad1 m, Monoid1 w) => MonadWriter (w n) (WriterT1 w m n) where
  writer (a, w) = WrapWriterT1 $ a <$ modify (<> w)
  {-# INLINE writer #-}
  tell w = WrapWriterT1 $ modify (<> w)
  {-# INLINE tell #-}
  listen (WrapWriterT1 m) = WrapWriterT1 $ do
    cur <- get
    put mempty
    ans <- m
    ext <- get
    put $ cur <> ext
    return (ans, ext)
  {-# INLINE listen #-}
  pass (WrapWriterT1 m) = WrapWriterT1 $ do
    cur <- get
    put mempty
    (ans, f) <- m
    ext <- get
    put $ cur <> f ext
    return ans
  {-# INLINE pass #-}

instance Monoid1 w => MonadTrans11 (WriterT1 w) where
  lift11 = WrapWriterT1 . lift
  {-# INLINE lift11 #-}

instance (SinkableE w, Monoid1 w, ScopeReader m) => ScopeReader (WriterT1 w m) where
  unsafeGetScope = lift11 unsafeGetScope
  {-# INLINE unsafeGetScope #-}
  getDistinct = lift11 getDistinct
  {-# INLINE getDistinct #-}

-------------------- ReaderT1 --------------------

newtype ReaderT1 (r :: E) (m :: MonadKind1) (n :: S) (a :: *) =
  ReaderT1 { runReaderT1' :: (ReaderT (r n) (m n) a) }
  deriving (Functor, Applicative, Monad, MonadFail, MonadReader (r n))

runReaderT1 :: r n -> ReaderT1 r m n a -> m n a
runReaderT1 r m = runReaderT (runReaderT1' m) r
{-# INLINE runReaderT1 #-}

instance MonadTrans11 (ReaderT1 r) where
  lift11 = ReaderT1 . lift
  {-# INLINE lift11 #-}

deriving instance MonadWriter s (m n) => MonadWriter s (ReaderT1 r m n)

deriving instance MonadState s (m n) => MonadState s (ReaderT1 r m n)

instance (Monad1 m, Alternative1 m) => Alternative ((ReaderT1 r m) n) where
  empty = lift11 empty
  {-# INLINE empty #-}
  ReaderT1 (ReaderT m1) <|> ReaderT1 (ReaderT m2) =
    ReaderT1 $ ReaderT \r -> m1 r <|> m2 r
  {-# INLINE (<|>) #-}

instance (SinkableE r, ScopeReader m) => ScopeReader (ReaderT1 r m) where
  unsafeGetScope = lift11 unsafeGetScope
  {-# INLINE unsafeGetScope #-}
  getDistinct = lift11 getDistinct
  {-# INLINE getDistinct #-}

instance (SinkableE r, ScopeExtender m) => ScopeExtender (ReaderT1 r m) where
  refreshAbsScope ab cont = ReaderT1 $ ReaderT \r -> do
    refreshAbsScope ab \b e -> runReaderT1 (sink r) $ cont b e

instance (Monad1 m, Fallible (m n)) => Fallible (ReaderT1 r m n) where
  throwErr = lift11 . throwErr

instance (Monad1 m, Catchable (m n)) => Catchable (ReaderT1 s m n) where
  catchErr (ReaderT1 m) f = ReaderT1 $ catchErr m (runReaderT1' . f)

-------------------- StateT1 --------------------

newtype StateT1 (s :: E) (m :: MonadKind1) (n :: S) (a :: *) =
  WrapStateT1 { runStateT1' :: (StateT (s n) (m n) a) }
  deriving ( Functor, Monad, MonadState (s n)
           , MonadFail, MonadIO)

-- This is entirely standard, but we implement it explicitly to encourage GHC to inline.
instance (Monad (m n), Applicative (m n)) => Applicative (StateT1 s m n) where
  pure = WrapStateT1 . pure
  {-# INLINE pure #-}
  (WrapStateT1 f) <*> (WrapStateT1 x) = WrapStateT1 $ f <*> x
  {-# INLINE (<*>) #-}
  liftA2 f (WrapStateT1 x) (WrapStateT1 y) = WrapStateT1 $ liftA2 f x y
  {-# INLINE liftA2 #-}

pattern StateT1 :: ((s n) -> m n (a, s n)) -> StateT1 s m n a
pattern StateT1 f = WrapStateT1 (StateT f)
{-# COMPLETE StateT1 #-}

type MonadState1 (e::E) (m::MonadKind1) = forall n. MonadState (e n) (m n)

runStateT1 :: StateT1 s m n a -> s n -> m n (a, s n)
runStateT1 = runStateT . runStateT1'
{-# INLINE runStateT1 #-}

evalStateT1 :: Monad1 m => StateT1 s m n a -> s n -> m n a
evalStateT1 m s = fst <$> runStateT1 m s
{-# INLINE evalStateT1 #-}

instance MonadTrans11 (StateT1 s) where
  lift11 = WrapStateT1 . lift
  {-# INLINE lift11 #-}

instance (SinkableE s, ScopeReader m) => ScopeReader (StateT1 s m) where
  unsafeGetScope = lift11 unsafeGetScope
  {-# INLINE unsafeGetScope #-}
  getDistinct = lift11 getDistinct
  {-# INLINE getDistinct #-}

instance (Monad1 m, Fallible (m n)) => Fallible (StateT1 s m n) where
  throwErr = lift11 . throwErr

instance (Monad1 m, Catchable (m n)) => Catchable (StateT1 s m n) where
  catchErr (WrapStateT1 m) f = WrapStateT1 $ catchErr m (runStateT1' . f)

instance (Monad1 m, Alternative1 m) => Alternative ((StateT1 s m) n) where
  empty = lift11 empty
  {-# INLINE empty #-}
  StateT1 m1 <|> StateT1 m2 = StateT1 \s -> m1 s <|> m2 s
  {-# INLINE (<|>) #-}

class HoistableState (s::E) where
  hoistState :: BindsNames b => s n -> b n l -> s l -> s n

instance HoistableState (LiftE a) where
  hoistState _ _ (LiftE x) = LiftE x
  {-# INLINE hoistState #-}

instance HoistableState UnitE where
  hoistState _ _ UnitE = UnitE
  {-# INLINE hoistState #-}

instance Show a => HoistableState (NameMap a) where
  hoistState _ b m = hoistNameMap b m
  {-# INLINE hoistState #-}

-------------------- ScopedT1 --------------------

newtype ScopedT1 (s :: E) (m :: MonadKind1) (n :: S) (a :: *) =
  WrapScopedT1 { runScopedT1' :: StateT1 s m n a }
  deriving ( Functor, Monad, MonadState (s n), MonadFail
           , MonadTrans11, ScopeReader )

-- This is entirely standard, but we implement it explicitly to encourage GHC to inline.
instance (Monad (m n), Applicative (m n)) => Applicative (ScopedT1 s m n) where
  pure = WrapScopedT1 . pure
  {-# INLINE pure #-}
  (WrapScopedT1 f) <*> (WrapScopedT1 x) = WrapScopedT1 $ f <*> x
  {-# INLINE (<*>) #-}
  liftA2 f (WrapScopedT1 x) (WrapScopedT1 y) = WrapScopedT1 $ liftA2 f x y
  {-# INLINE liftA2 #-}

pattern ScopedT1 :: ((s n) -> m n (a, s n)) -> ScopedT1 s m n a
pattern ScopedT1 f = WrapScopedT1 (StateT1 f)
{-# COMPLETE ScopedT1 #-}

runScopedT1 :: Monad1 m => ScopedT1 s m n a -> s n -> m n a
runScopedT1 m s = fst <$> runStateT1 (runScopedT1' m) s
{-# INLINE runScopedT1 #-}

deriving instance (Monad1 m, Fallible1 m) => Fallible (ScopedT1 s m n)
deriving instance (Monad1 m, Catchable1 m) => Catchable (ScopedT1 s m n)

-------------------- MaybeT1 --------------------

newtype MaybeT1 (m :: MonadKind1) (n :: S) (a :: *) =
  MaybeT1 { runMaybeT1' :: (MaybeT (m n) a) }
  deriving (Functor, Applicative, Monad, Alternative)

runMaybeT1 :: MaybeT1 m n a -> m n (Maybe a)
runMaybeT1 = runMaybeT . runMaybeT1'
{-# INLINE runMaybeT1 #-}

instance MonadTrans11 MaybeT1 where
  lift11 = MaybeT1 . lift
  {-# INLINE lift11 #-}

instance Monad (m n) => MonadFail (MaybeT1 m n) where
  fail s = MaybeT1 (fail s)
  {-# INLINE fail #-}

instance Monad (m n) => Fallible (MaybeT1 m n) where
  throwErr _ = empty

instance ScopeReader m => ScopeReader (MaybeT1 m) where
  unsafeGetScope = lift11 unsafeGetScope
  {-# INLINE unsafeGetScope #-}
  getDistinct = lift11 getDistinct
  {-# INLINE getDistinct #-}

-------------------- StreamWriter --------------------

class Monad m => StreamWriter w m | m -> w where
  writeStream :: w -> m ()

newtype StreamWriterT1 (w:: *) (m::MonadKind1) (n::S) (a:: *) =
  StreamWriterT1 { runStreamWriterT1' :: StateT1 (LiftE (SnocList w)) m n a }
  deriving (Functor, Applicative, Monad, MonadFail, MonadIO, ScopeReader)

instance Monad1 m => StreamWriter w (StreamWriterT1 w m n) where
  writeStream w = StreamWriterT1 $ modify (\(LiftE ws) -> LiftE (ws `snoc` w))
  {-# INLINE writeStream #-}

runStreamWriterT1 :: Monad1 m => StreamWriterT1 w m n a -> m n (a, [w])
runStreamWriterT1 m = do
  (ans, LiftE ws) <- runStateT1 (runStreamWriterT1' m) (LiftE emptySnocList)
  return (ans, toList ws)
{-# INLINE runStreamWriterT1 #-}

-------------------- StreamReader --------------------

class Monad m => StreamReader r m | m -> r where
  readStream :: m (Maybe r)

newtype StreamReaderT1 (r:: *) (m::MonadKind1) (n::S) (a:: *) =
  StreamReaderT1 { runStreamReaderT1' :: StateT1 (LiftE [r]) m n a }
  deriving (Functor, Applicative, Monad, MonadFail, MonadIO, ScopeReader, MonadTrans11)

instance Monad1 m => StreamReader r (StreamReaderT1 r m n) where
  readStream = StreamReaderT1 $ state \(LiftE rs) ->
    case rs of
      []       -> (Nothing, LiftE [])
      (r:rest) -> (Just r , LiftE rest)
  {-# INLINE readStream #-}

runStreamReaderT1 :: Monad1 m => [r] -> StreamReaderT1 r m n a -> m n (a, [r])
runStreamReaderT1 rs m = do
  (ans, LiftE rsRemaining) <- runStateT1 (runStreamReaderT1' m) (LiftE rs)
  return (ans, rsRemaining)
{-# INLINE runStreamReaderT1 #-}

