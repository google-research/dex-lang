-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Actor (Actor, Proc, PChan, CanTrap (..), Msg (..),
              runActor, spawn, spawnLink, send,
              receive, receiveF, receiveErr, receiveErrF,
              myChan, subChan, sendFromIO, ServerMsg (..),
              logServer, ReqChan, subscribe) where

import Control.Concurrent
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Exception
import Data.IORef

import Cat
import Util

data Msg a = ErrMsg Proc String | NormalMsg a
data CanTrap = Trap | NoTrap  deriving (Show, Ord, Eq)
newtype PChan a = PChan { sendPChan :: a -> IO () }
data Proc = Proc CanTrap ThreadId (PChan (Proc, String)) -- TODO: Ord instance
data BackChan a = BackChan (IORef [a]) (Chan a)
data ActorConfig m = ActorConfig { selfProc  :: Proc
                                 , selfChan  :: BackChan (Msg m)
                                 , linksPtr  :: IORef [Proc] }

newtype Actor m a = Actor (ReaderT (ActorConfig m) IO a)
  deriving (Functor, Applicative, Monad, MonadIO)

runActor :: Actor msg a -> IO a
runActor (Actor m) = do
  linksRef   <- newIORef []
  chan <- newBackChan
  tid <- myThreadId
  let p = Proc Trap tid (asErrPChan chan)
  runReaderT m (ActorConfig p chan linksRef)

subChan :: (a -> b) -> PChan b -> PChan a
subChan f chan = PChan (sendPChan chan . f)

-- TODO: kill :: Proc -> Actor m ()

spawn :: MonadActor msg m => CanTrap -> Actor msg' () -> m (Proc, PChan msg')
spawn canTrap body = liftIO $ spawnIO canTrap [] body

spawnLink :: MonadActor msg m => CanTrap -> Actor msg' () -> m (Proc, PChan msg')
spawnLink canTrap body = do
  cfg <- actorCfg
  liftIO $ do
    links <- readIORef (linksPtr cfg)
    (child, childChan) <- spawnIO canTrap [selfProc cfg] body
    -- potential bug if we get killed right here, before we've linked the child.
    -- 'mask' from Control.Exception might be a solution
    writeIORef (linksPtr cfg) (child : links)
    return (child, childChan)

spawnIO :: CanTrap -> [Proc] -> Actor msg () -> IO (Proc, PChan msg)
spawnIO canTrap links (Actor m) = do
  linksRef   <- newIORef links
  chan <- newBackChan
  tid <- forkIO $ do
    tid <- myThreadId
    let self = Proc canTrap tid (asErrPChan chan)
    runReaderT m (ActorConfig self chan linksRef)
      `catch` (\e ->
         do linked <- readIORef linksRef
            putStrLn $ "Error:\n" ++ show (e::SomeException)
            mapM_ (cleanup (show (e::SomeException)) self) linked)
  return (Proc canTrap tid (asErrPChan chan), asPChan chan)
  where
   cleanup :: String -> Proc -> Proc -> IO ()
   cleanup s failed (Proc Trap   _ errChan) = sendFromIO errChan (failed, s)
   cleanup _ _      (Proc NoTrap linked  _) = void $ forkIO $ killThread linked

asPChan :: BackChan (Msg a) -> PChan a
asPChan (BackChan _ chan) = PChan (writeChan chan . NormalMsg)

asErrPChan :: BackChan (Msg a) -> PChan (Proc, String)
asErrPChan (BackChan _ chan) = PChan (writeChan chan . uncurry ErrMsg)

send :: MonadActor msg' m => PChan msg -> msg -> m ()
send p x = liftIO (sendFromIO p x)

sendFromIO :: PChan msg -> msg -> IO ()
sendFromIO = sendPChan

myChan :: MonadActor msg m => m (PChan msg)
myChan = do cfg <- actorCfg
            return $ asPChan (selfChan cfg)

-- TODO: make a construct to receive in a loop to avoid repeated linear search
receiveErrF :: MonadActor msg m => (Msg msg -> Maybe a) -> m a
receiveErrF filterFn = do
  cfg <- actorCfg
  liftIO $ find (selfChan cfg) []
  where find chan skipped = do
          x <- readBackChan chan
          case filterFn x of
            Just y -> do pushBackChan chan (reverse skipped)
                         return y
            Nothing -> find chan (x:skipped)

receiveErr :: MonadActor msg m => m (Msg msg)
receiveErr = receiveErrF Just

receiveF :: MonadActor msg m => (msg -> Maybe a) -> m a
receiveF filterFn = receiveErrF (skipErr >=> filterFn)
  where skipErr msg = case msg of NormalMsg x -> Just x
                                  ErrMsg _ _  -> Nothing

receive :: MonadActor msg m => m msg
receive = receiveF Just

newBackChan :: IO (BackChan a)
newBackChan = liftM2 BackChan (newIORef []) newChan

readBackChan :: BackChan a -> IO a
readBackChan (BackChan ptr chan) = do xs <- readIORef ptr
                                      case xs of []     -> readChan chan
                                                 x:rest -> do writeIORef ptr rest
                                                              return x

pushBackChan :: BackChan a -> [a] -> IO ()
pushBackChan (BackChan ptr _) xs = do xs' <- readIORef ptr
                                      writeIORef ptr (xs ++ xs')

class (MonadIO m, Monad m) => MonadActor msg m | m -> msg where
  actorCfg :: m (ActorConfig msg)

instance MonadActor msg (Actor msg) where
  actorCfg = Actor ask

instance MonadActor msg m => MonadActor msg (StateT s m) where
  actorCfg = lift actorCfg

instance MonadActor msg m => MonadActor msg (ReaderT r m) where
  actorCfg = lift actorCfg

instance MonadActor msg m => MonadActor msg (CatT env m) where
  actorCfg = lift actorCfg

-- === ready-made actors for common patterns ===

-- similar to a CPS transformation a ==> (a -> r) -> r
type ReqChan a = PChan (PChan a)

data ServerMsg a = Request (PChan a)
                 | Push a

subscribe :: MonadActor msg m => ReqChan msg -> m ()
subscribe chan = myChan >>= send chan

-- combines inputs monoidally and pushes incremental updates to subscribers
logServer :: Monoid a => Actor (ServerMsg a) ()
logServer = flip evalStateT (mempty, []) $ forever $ do
  msg <- receive
  case msg of
    Request chan -> do
      curVal <- gets fst
      chan `send` curVal
      modify $ onSnd (chan:)
    Push x -> do
      modify $ onFst (<> x)
      subscribers <- gets snd
      mapM_ (`send` x) subscribers

-- TODO: state machine?
