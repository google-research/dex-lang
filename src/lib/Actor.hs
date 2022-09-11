-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Actor (PChan, sendPChan, sendOnly, subChan,
              Actor, runActor, spawn,
              LogServerMsg (..), logServer) where

import Control.Concurrent (Chan, forkIO, newChan, readChan, ThreadId, writeChan)
import Control.Monad.State.Strict

import Util (onFst, onSnd)

-- Micro-actors.

-- In this model, an "actor" is just an IO computation (presumably
-- running on its own Haskell thread) that receives messages on a
-- Control.Concurrent.Chan channel.  The idea is that the actor thread
-- only receives information (or synchronization) from other threads
-- through messages sent on that one channel, and no other thread
-- reads messages from that channel.

-- We start the actor with a two-way view of its input channel so it
-- can subscribe itself to message streams by passing (a send-only
-- view of) it to another actor.
type Actor a = Chan a -> IO ()

-- We also define a send-only channel type, to help ourselves not
-- accidentally read from channels we aren't supposed to.
newtype PChan a = PChan { sendPChan :: a -> IO () }

sendOnly :: Chan a -> PChan a
sendOnly chan = PChan $ \ !x -> writeChan chan x

subChan :: (a -> b) -> PChan b -> PChan a
subChan f chan = PChan (sendPChan chan . f)

-- Synchronously execute an actor.
runActor :: Actor a -> IO ()
runActor actor = newChan >>= actor

-- Asynchronously launch an actor.  Immediately returns permission to
-- kill that actor and to send it messages.
spawn :: Actor a -> IO (ThreadId, PChan a)
spawn actor = do
  chan <- newChan
  tid <- forkIO $ actor chan
  return (tid, sendOnly chan)

-- A log server.  Combines inputs monoidally and pushes incremental
-- updates to subscribers.

data LogServerMsg a = Subscribe (PChan a)
                    | Publish a

logServer :: Monoid a => Actor (LogServerMsg a)
logServer self = flip evalStateT (mempty, []) $ forever $ do
  msg <- liftIO $ readChan self
  case msg of
    Subscribe chan -> do
      curVal <- gets fst
      liftIO $ chan `sendPChan` curVal
      modify $ onSnd (chan:)
    Publish x -> do
      modify $ onFst (<> x)
      subscribers <- gets snd
      mapM_ (liftIO . (`sendPChan` x)) subscribers

