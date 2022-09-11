-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module Logging (Logger, LoggerT (..), MonadLogger (..), logIO, runLoggerT,
                FilteredLogger (..), logFiltered, logSkippingFilter,
                MonadLogger1, MonadLogger2,
                runLogger, execLogger, logThis, readLog, ) where

import Control.Monad
import Control.Monad.Reader
import Data.Text.Prettyprint.Doc
import Control.Concurrent.MVar
import Prelude hiding (log)
import System.IO

import Err
import Name

data Logger l = Logger (MVar l) (Maybe Handle)

data FilteredLogger k l = FilteredLogger (k -> Bool) (Logger l)

runLogger :: (Monoid l, MonadIO m) => Maybe Handle -> (Logger l -> m a) -> m (a, l)
runLogger logFile m = do
  log <- liftIO $ newMVar mempty
  ans <- m $ Logger log logFile
  logged <- liftIO $ readMVar log
  return (ans, logged)

execLogger :: (Monoid l, MonadIO m) => Maybe Handle -> (Logger l -> m a) -> m a
execLogger logFile m = fst <$> runLogger logFile m

logThis :: (Pretty l, Monoid l, MonadIO m) => Logger l -> l -> m ()
logThis (Logger log maybeLogHandle) x = liftIO $ do
  forM_ maybeLogHandle \h -> do
    hPutStrLn h $ pprint x
    hFlush h
  modifyMVar_ log \cur -> return (cur <> x)

logFiltered :: (Monoid l, MonadIO m, Pretty l) => FilteredLogger k l -> k -> m l -> m ()
logFiltered (FilteredLogger shouldLog logger) k m =
  when (shouldLog k) $ m >>= logThis logger

logSkippingFilter :: (Monoid l, MonadIO m, Pretty l) => FilteredLogger k l -> l -> m ()
logSkippingFilter (FilteredLogger _ logger) = logThis logger

readLog :: MonadIO m => Logger l -> m l
readLog (Logger log _) = liftIO $ readMVar log

-- === monadic interface ===

newtype LoggerT l m a = LoggerT { runLoggerT' :: ReaderT (Logger l) m a }
                        deriving (Functor, Applicative, Monad, MonadTrans,
                                  MonadIO, MonadFail, Fallible, Catchable)

class (Pretty l, Monoid l, Monad m) => MonadLogger l m | m -> l where
  getLogger :: m (Logger l)
  withLogger :: Logger l -> m a -> m a

instance (MonadIO m, Pretty l, Monoid l) => MonadLogger l (LoggerT l m) where
  getLogger = LoggerT ask
  withLogger l m = LoggerT $ local (const l) $ runLoggerT' m

type MonadLogger1 l (m :: MonadKind1) = forall (n::S) . MonadLogger l (m n)
type MonadLogger2 l (m :: MonadKind2) = forall (n1::S) (n2::S) . MonadLogger l (m n1 n2)

logIO :: MonadIO m => MonadLogger l m => l -> m ()
logIO val = do
  logger <- getLogger
  liftIO $ logThis logger val

runLoggerT :: Monoid l => Logger l -> LoggerT l m a -> m a
runLoggerT l (LoggerT m) = runReaderT m l

-- === more instances ===

instance MonadLogger l m => MonadLogger l (ReaderT r m) where
  getLogger = lift getLogger
  withLogger l cont = ReaderT \r -> withLogger l $ runReaderT cont r
