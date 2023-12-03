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
import Types.Top (Env)
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

instance ( SinkableE w, Monoid1 w
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

deriving instance MonadWriter s (m n) => MonadWriter s (ReaderT1 r m n)

deriving instance MonadState s (m n) => MonadState s (ReaderT1 r m n)

instance (Monad1 m, Alternative1 m) => Alternative ((ReaderT1 r m) n) where
  empty = lift11 empty
  {-# INLINE empty #-}
  ReaderT1 (ReaderT m1) <|> ReaderT1 (ReaderT m2) =
    ReaderT1 $ ReaderT \r -> m1 r <|> m2 r
  {-# INLINE (<|>) #-}


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

instance (SinkableE s, EnvReader m) => EnvReader (StateT1 s m) where
  unsafeGetEnv = lift11 unsafeGetEnv
  {-# INLINE unsafeGetEnv #-}

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

instance Show a => HoistableState (NameMap c a) where
  hoistState _ b m = hoistNameMap b m
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
  throwErr _ = empty

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
  deriving (Functor, Applicative, Monad, MonadFail, MonadIO, ScopeReader, EnvReader, MonadTrans11)

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

-------------------- DiffState --------------------

class MonoidE (d::E) where
  emptyE :: d n
  catE :: d n -> d n -> d n

class MonoidE d => DiffStateE (s::E) (d::E) where
  updateDiffStateE :: Distinct n => Env n -> s n -> d n -> s n

newtype DiffStateT1 (s::E) (d::E) (m::MonadKind1) (n::S) (a:: *) =
  DiffStateT1' { runDiffStateT1'' :: StateT (s n, d n) (m n) a }
  deriving ( Functor, Applicative, Monad, MonadFail, MonadIO
           , Fallible, Catchable)

pattern DiffStateT1 :: ((s n, d n) -> m n (a, (s n, d n))) -> DiffStateT1 s d m n a
pattern DiffStateT1 cont = DiffStateT1' (StateT cont)

diffStateT1
  :: (EnvReader m, DiffStateE s d, MonoidE d)
  => (s n -> m n (a, d n)) -> DiffStateT1 s d m n a
diffStateT1 cont = DiffStateT1 \(s, d) -> do
  (ans, d') <- cont s
  env <- unsafeGetEnv
  Distinct <- getDistinct
  return (ans, (updateDiffStateE env s d', catE d d'))
{-# INLINE diffStateT1 #-}

runDiffStateT1
  :: (EnvReader m, DiffStateE s d, MonoidE d)
  => s n -> DiffStateT1 s d m n a ->  m n (a, d n)
runDiffStateT1 s (DiffStateT1' (StateT cont)) = do
  (ans, (_, d)) <- cont (s, emptyE)
  return (ans, d)
{-# INLINE runDiffStateT1 #-}

class (Monad1 m, MonoidE d)
      => MonadDiffState1 (m::MonadKind1) (s::E) (d::E) | m -> s, m -> d where
  withDiffState :: s n -> m n a -> m n (a, d n)
  updateDiffStateM :: d n -> m n ()
  getDiffState :: m n (s n)

instance (EnvReader m, DiffStateE s d, MonoidE d) => MonadDiffState1 (DiffStateT1 s d m) s d where
  getDiffState = DiffStateT1' $ fst <$> get
  {-# INLINE getDiffState #-}

  withDiffState s cont = DiffStateT1' do
    (sOld, dOld) <- get
    put (s, emptyE)
    ans <- runDiffStateT1'' cont
    (_, dLocal) <- get
    put (sOld, dOld)
    return (ans, dLocal)
  {-# INLINE withDiffState #-}

  updateDiffStateM d = DiffStateT1' do
    (s, d') <- get
    env <- lift unsafeGetEnv
    Distinct <- lift getDistinct
    put (updateDiffStateE env s d, catE d d')
  {-# INLINE updateDiffStateM #-}

instance MonoidE (ListE e) where
  emptyE = mempty
  catE = (<>)

instance MonoidE (RListE e) where
  emptyE = mempty
  catE = (<>)

instance (Monad1 m, Alternative1 m, MonoidE d) => Alternative ((DiffStateT1 s d m) n) where
  empty = DiffStateT1' $ StateT \_ -> empty
  {-# INLINE empty #-}
  DiffStateT1' (StateT m1) <|> DiffStateT1' (StateT m2) = DiffStateT1' $ StateT \s ->
    m1 s <|> m2 s
  {-# INLINE (<|>) #-}

instance (ScopeReader m, MonoidE d) => ScopeReader (DiffStateT1 s d m) where
  unsafeGetScope = lift11 unsafeGetScope
  getDistinct = lift11 getDistinct

instance (EnvReader m, MonoidE d) => EnvReader (DiffStateT1 s d m) where
  unsafeGetEnv = lift11 unsafeGetEnv

instance MonadTrans11 (DiffStateT1 s d) where
  lift11 m = DiffStateT1' $ lift m
  {-# INLINE lift11 #-}
