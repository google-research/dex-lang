-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Logging (Logger, runLogger, logThis, readLog) where

import Control.Concurrent.MVar
import Control.Monad.IO.Class

type Logger l = MVar l

runLogger :: (Monoid l, MonadIO m) => (Logger l -> m a) -> m (a, l)
runLogger m = do
  logger <- liftIO $ newMVar mempty
  ans <- m logger
  logged <- liftIO $ readMVar logger
  return (ans, logged)

logThis :: (Monoid l, MonadIO m) => Logger l -> l -> m ()
logThis logger x = liftIO $ do
  cur <- takeMVar logger
  putMVar logger $ cur <> x

readLog :: MonadIO m => Logger l -> m l
readLog logger = liftIO $ readMVar logger
