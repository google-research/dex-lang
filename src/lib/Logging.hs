-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Logging (Logger, runLogger, execLogger, logThis, readLog) where

import Control.Monad
import Control.Monad.IO.Class
import Data.Text.Prettyprint.Doc
import Control.Concurrent.MVar
import Prelude hiding (log)
import System.IO

import PPrint

data Logger l = Logger (MVar l) (Maybe Handle)

runLogger :: (Monoid l, MonadIO m) => Maybe FilePath -> (Logger l -> m a) -> m (a, l)
runLogger maybePath m = do
  log <- liftIO $ newMVar mempty
  logFile <- liftIO $ forM maybePath \path -> openFile path WriteMode
  ans <- m $ Logger log logFile
  logged <- liftIO $ readMVar log
  return (ans, logged)

execLogger :: (Monoid l, MonadIO m) => Maybe FilePath -> (Logger l -> m a) -> m a
execLogger maybePath m = fst <$> runLogger maybePath m

logThis :: (Pretty l, Monoid l, MonadIO m) => Logger l -> l -> m ()
logThis (Logger log maybeLogHandle) x = liftIO $ do
  forM_ maybeLogHandle \h -> do
    hPutStrLn h $ pprint x
    hFlush h
  modifyMVar_ log \cur -> return (cur <> x)

readLog :: MonadIO m => Logger l -> m l
readLog (Logger log _) = liftIO $ readMVar log
