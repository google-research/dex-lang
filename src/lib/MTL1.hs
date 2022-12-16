-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module MTL1 (
    MonadTrans11 (..), HoistableState (..),
    WriterT1, pattern WriterT1, runWriterT1, runWriterT1From,
    StateT1, pattern StateT1, runStateT1, evalStateT1, MonadState1,
    MaybeT1 (..), runMaybeT1, ReaderT1 (..), runReaderT1,
    ScopedT1, pattern ScopedT1, runScopedT1,
    FallibleT1, runFallibleT1,
    runStreamWriterT1, StreamWriter (..), StreamWriterT1 (..),
    runStreamReaderT1, StreamReader (..), StreamReaderT1 (..),
  ) where

import Control.Monad.Reader
import Control.Monad.Writer.Class
import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe
import qualified Control.Monad.Trans.Except as MTE
import Control.Applicative
import Data.Foldable (toList)

import Name
import Err
import Core (EnvReader (..), EnvExtender (..))
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

instance (SinkableE w, Monoid1 w, EnvReader m) => EnvReader (WriterT1 w m) where
  unsafeGetEnv = lift11 unsafeGetEnv
  {-# INLINE unsafeGetEnv #-}

instance (SinkableE w, Monoid1 w, ScopeReader m) => ScopeReader (WriterT1 w m) where
  unsafeGetScope = lift11 unsafeGetScope
  {-# INLINE unsafeGetScope #-}
  getDistinct = lift11 getDistinct
  {-# INLINE getDistinct #-}

instance ( SinkableE w, HoistableE w, Monoid1 w
         , HoistableState w, EnvExtender m)
         => EnvExtender (WriterT1 w m) where
  refreshAbs ab cont = WriterT1 \s -> do
    (ans, Abs b new) <- refreshAbs ab \b e -> do
      (ans, new) <- runWriterT1From (sink s) $ cont b e
      return (ans, Abs b new)
    let new' = hoistState s b new
    return (ans, s <> new')
  {-# INLINE refreshAbs #-}

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

deriving instance MonadState s (m n) => MonadState s (ReaderT1 r m n)

instance (SinkableE r, EnvReader m) => EnvReader (ReaderT1 r m) where
  unsafeGetEnv = lift11 unsafeGetEnv
  {-# INLINE unsafeGetEnv #-}

instance (SinkableE r, ScopeReader m) => ScopeReader (ReaderT1 r m) where
  unsafeGetScope = lift11 unsafeGetScope
  {-# INLINE unsafeGetScope #-}
  getDistinct = lift11 getDistinct
  {-# INLINE getDistinct #-}

instance (SinkableE r, ScopeExtender m) => ScopeExtender (ReaderT1 r m) where
  refreshAbsScope ab cont = ReaderT1 $ ReaderT \r -> do
    refreshAbsScope ab \b e -> runReaderT1 (sink r) $ cont b e

instance (SinkableE r, EnvExtender m) => EnvExtender (ReaderT1 r m) where
  refreshAbs ab cont = ReaderT1 $ ReaderT \r -> do
    refreshAbs ab \b e -> runReaderT1 (sink r) $ cont b e

instance (Monad1 m, Fallible (m n)) => Fallible (ReaderT1 r m n) where
  throwErrs = lift11 . throwErrs
  addErrCtx ctx (ReaderT1 m) = ReaderT1 $ addErrCtx ctx m
  {-# INLINE addErrCtx #-}

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

instance (SinkableE s, EnvReader m) => EnvReader (StateT1 s m) where
  unsafeGetEnv = lift11 unsafeGetEnv
  {-# INLINE unsafeGetEnv #-}

instance (SinkableE s, ScopeReader m) => ScopeReader (StateT1 s m) where
  unsafeGetScope = lift11 unsafeGetScope
  {-# INLINE unsafeGetScope #-}
  getDistinct = lift11 getDistinct
  {-# INLINE getDistinct #-}

instance (Monad1 m, Fallible (m n)) => Fallible (StateT1 s m n) where
  throwErrs = lift11 . throwErrs
  addErrCtx ctx (WrapStateT1 m) = WrapStateT1 $ addErrCtx ctx m
  {-# INLINE addErrCtx #-}

instance (Monad1 m, Catchable (m n)) => Catchable (StateT1 s m n) where
  catchErr (WrapStateT1 m) f = WrapStateT1 $ catchErr m (runStateT1' . f)

instance (Monad1 m, CtxReader (m n)) => CtxReader (StateT1 s m n) where
  getErrCtx = lift11 getErrCtx
  {-# INLINE getErrCtx #-}

class HoistableState (s::E) where
  hoistState :: BindsNames b => s n -> b n l -> s l -> s n

instance (SinkableE s, EnvExtender m, HoistableState s) => EnvExtender (StateT1 s m) where
  refreshAbs ab cont = StateT1 \s -> do
    (ans, Abs b s') <- refreshAbs ab \b e -> do
      (ans, s') <- flip runStateT1 (sink s) $ cont b e
      return (ans, Abs b s')
    let s'' = hoistState s b s'
    return (ans, s'')

instance HoistableState (LiftE a) where
  hoistState _ _ (LiftE x) = LiftE x
  {-# INLINE hoistState #-}

instance HoistableState UnitE where
  hoistState _ _ UnitE = UnitE
  {-# INLINE hoistState #-}

-------------------- ScopedT1 --------------------

newtype ScopedT1 (s :: E) (m :: MonadKind1) (n :: S) (a :: *) =
  WrapScopedT1 { runScopedT1' :: StateT1 s m n a }
  deriving ( Functor, Monad, MonadState (s n), MonadFail
           , MonadTrans11, EnvReader, ScopeReader )

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
deriving instance (Monad1 m, CtxReader1 m) => CtxReader (ScopedT1 s m n)

instance (SinkableE s, EnvExtender m) => EnvExtender (ScopedT1 s m) where
  refreshAbs ab cont = ScopedT1 \s -> do
    ans <- refreshAbs ab \b e -> flip runScopedT1 (sink s) $ cont b e
    return (ans, s)

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
  throwErrs _ = empty
  addErrCtx _ cont = cont
  {-# INLINE addErrCtx #-}

instance EnvReader m => EnvReader (MaybeT1 m) where
  unsafeGetEnv = lift11 unsafeGetEnv
  {-# INLINE unsafeGetEnv #-}

instance ScopeReader m => ScopeReader (MaybeT1 m) where
  unsafeGetScope = lift11 unsafeGetScope
  {-# INLINE unsafeGetScope #-}
  getDistinct = lift11 getDistinct
  {-# INLINE getDistinct #-}

instance EnvExtender m => EnvExtender (MaybeT1 m) where
  refreshAbs ab cont = MaybeT1 $ MaybeT $
    refreshAbs ab \b e -> runMaybeT $ runMaybeT1' $ cont b e

-------------------- FallibleT1 --------------------

newtype FallibleT1 (m::MonadKind1) (n::S) a =
  FallibleT1 { fromFallibleT :: ReaderT ErrCtx (MTE.ExceptT Errs (m n)) a }
  deriving (Functor, Applicative, Monad)

runFallibleT1 :: Monad1 m => FallibleT1 m n a -> m n (Except a)
runFallibleT1 m =
  MTE.runExceptT (runReaderT (fromFallibleT m) mempty) >>= \case
    Right ans -> return $ Success ans
    Left errs -> return $ Failure errs
{-# INLINE runFallibleT1 #-}

instance Monad1 m => MonadFail (FallibleT1 m n) where
  fail s = throw MonadFailErr s
  {-# INLINE fail #-}

instance Monad1 m => Fallible (FallibleT1 m n) where
  throwErrs (Errs errs) = FallibleT1 $ ReaderT \ambientCtx ->
    MTE.throwE $ Errs [Err errTy (ambientCtx <> ctx) s | Err errTy ctx s <- errs]
  addErrCtx ctx (FallibleT1 m) = FallibleT1 $ local (<> ctx) m
  {-# INLINE addErrCtx #-}

instance ScopeReader m => ScopeReader (FallibleT1 m) where
  unsafeGetScope = FallibleT1 $ lift $ lift unsafeGetScope
  {-# INLINE unsafeGetScope #-}
  getDistinct = FallibleT1 $ lift $ lift $ getDistinct
  {-# INLINE getDistinct #-}

instance EnvReader m => EnvReader (FallibleT1 m) where
  unsafeGetEnv = FallibleT1 $ lift $ lift unsafeGetEnv
  {-# INLINE unsafeGetEnv #-}

-------------------- StreamWriter --------------------

class Monad m => StreamWriter w m | m -> w where
  writeStream :: w -> m ()

newtype StreamWriterT1 (w:: *) (m::MonadKind1) (n::S) (a:: *) =
  StreamWriterT1 { runStreamWriterT1' :: StateT1 (LiftE (SnocList w)) m n a }
  deriving (Functor, Applicative, Monad, MonadFail, MonadIO, ScopeReader, EnvReader)

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
  deriving (Functor, Applicative, Monad, MonadFail, MonadIO, ScopeReader, EnvReader)

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
