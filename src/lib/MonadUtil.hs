-- Copyright 2023 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module MonadUtil (
  DefuncState (..), LabelReader (..), SingletonLabel (..), FreshNames (..),
  runFreshNameT, FreshNameT (..), Logger (..), LogLevel (..), getIOLogger, CanSetIOLogger (..),
  IOLoggerT (..), runIOLoggerT, LoggerT (..), runLoggerT,
  IOLogger (..), HasIOLogger (..), captureIOLogs) where

import Control.Monad.Reader
import Control.Monad.State.Strict
import Control.Monad.Writer.Strict
import Data.IORef

import Err

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

-- === Logging monad ===

data IOLogger w = IOLogger { ioLogLevel  :: LogLevel
                           , ioLogAction :: w -> IO () }
data LogLevel = NormalLogLevel | DebugLogLevel

class (Monoid w, Monad m) => Logger w m | m -> w where
  emitLog :: w -> m ()
  getLogLevel :: m LogLevel

newtype IOLoggerT w m a = IOLoggerT { runIOLoggerT' :: ReaderT (IOLogger w) m a }
        deriving (Functor, Applicative, Monad, MonadIO, Fallible, MonadFail, Catchable)

class Monad m => HasIOLogger w m | m -> w where
  getIOLogAction :: Monad m => m (w -> IO ())

class Monad m => CanSetIOLogger w m | m -> w where
  withIOLogAction :: Monad m => (w -> IO ()) -> m a -> m a

instance (Monoid w, MonadIO m) => HasIOLogger w (IOLoggerT w m) where
  getIOLogAction = IOLoggerT $ asks ioLogAction

instance (Monoid w, MonadIO m) => CanSetIOLogger w (IOLoggerT w m) where
  withIOLogAction logger (IOLoggerT m) = IOLoggerT do
    local (\r -> r { ioLogAction = logger }) m

instance (Monoid w, MonadIO m) => Logger w (IOLoggerT w m) where
  emitLog w = do
    logger <- getIOLogAction
    liftIO $ logger w
  getLogLevel = IOLoggerT $ asks ioLogLevel

getIOLogger :: (HasIOLogger w m, Logger w m) => m (IOLogger w)
getIOLogger = IOLogger <$> getLogLevel <*> getIOLogAction

runIOLoggerT :: (Monoid w, MonadIO m) => LogLevel -> (w -> IO ()) -> IOLoggerT w m a -> m a
runIOLoggerT logLevel write cont = runReaderT (runIOLoggerT' cont) (IOLogger logLevel write)

newtype LoggerT w m a = LoggerT { runLoggerT' :: WriterT w m a }
        deriving (Functor, Applicative, Monad, MonadIO)

instance (Monoid w, Monad m) => Logger w (LoggerT w m) where
  emitLog w = LoggerT $ tell w
  getLogLevel = return NormalLogLevel

runLoggerT :: (Monoid w, Monad m) => LoggerT w m a -> m (a, w)
runLoggerT cont = runWriterT (runLoggerT' cont)

captureIOLogs
  :: forall w m a. (Monoid w, MonadIO m, HasIOLogger w m, CanSetIOLogger w m)
  => m a -> m (a, w)
captureIOLogs cont = do
  ref <- liftIO $ newIORef (mempty :: w)
  ans <- withIOLogAction (\w -> modifyIORef ref (<> w)) cont
  w <- liftIO $ readIORef ref
  return (ans, w)

