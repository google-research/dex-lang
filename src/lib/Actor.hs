-- Copyright 2023 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module Actor (
  ActorM, Actor (..), launchActor, send, selfMailbox, messageLoop,
  sliceMailbox, SubscribeMsg (..), IncServer, IncServerT, FileWatcher,
  StateServer, flushDiffs, handleSubscribeMsg, subscribe, subscribeIO, sendSync,
  runIncServerT, launchFileWatcher, Mailbox,
  ) where

import Control.Concurrent
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Reader
import Data.IORef
import Data.Text (Text)
import System.Directory (getModificationTime)
import GHC.Generics

import IncState
import MonadUtil
import Util (readFileText)

-- === Actor implementation ===

newtype ActorM msg a = ActorM { runActorM ::  ReaderT (Chan msg) IO a }
  deriving (Functor, Applicative, Monad, MonadIO)

newtype Mailbox a = Mailbox { sendToMailbox :: a -> IO () }

class (MonadIO m) => Actor msg m | m -> msg where
  selfChan :: m (Chan msg)

instance Actor msg (ActorM msg) where
  selfChan = ActorM ask

instance Actor msg m => Actor msg (ReaderT r m) where selfChan = lift $ selfChan
instance Actor msg m => Actor msg (StateT  s m) where selfChan = lift $ selfChan

send :: MonadIO m => Mailbox msg -> msg -> m ()
send chan msg = liftIO $ sendToMailbox chan msg

selfMailbox :: Actor msg m => (a -> msg) -> m (Mailbox a)
selfMailbox asSelfMessage = do
  chan <- selfChan
  return $ Mailbox \msg -> writeChan chan (asSelfMessage msg)

launchActor :: MonadIO m => ActorM msg () -> m (Mailbox msg)
launchActor m = liftIO do
  chan <- newChan
  void $ forkIO $ runReaderT (runActorM m) chan
  return $ Mailbox \msg -> writeChan chan msg

messageLoop :: Actor msg m => (msg -> m ()) -> m ()
messageLoop handleMessage = do
  forever do
    msg <- liftIO . readChan =<< selfChan
    handleMessage msg

sliceMailbox :: (b -> a) -> Mailbox a -> Mailbox b
sliceMailbox f (Mailbox sendMsg) = Mailbox $ sendMsg . f

-- === Promises ===

newtype Promise a = Promise (MVar a)
newtype PromiseSetter a = PromiseSetter (MVar a)

newPromise :: MonadIO m => m (Promise a, PromiseSetter a)
newPromise = do
  v <- liftIO $ newEmptyMVar
  return (Promise v, PromiseSetter v)

waitForPromise :: MonadIO m => Promise a -> m a
waitForPromise (Promise v) = liftIO $ readMVar v

setPromise :: MonadIO m => PromiseSetter a -> a -> m ()
setPromise (PromiseSetter v) x = liftIO $ putMVar v x

-- Message that expects a synchronous reponse
data SyncMsg msg response = SyncMsg msg (PromiseSetter response)

sendSync :: MonadIO m => Mailbox (SyncMsg msg response) -> msg -> m response
sendSync mailbox msg = do
  (result, resultSetter) <- newPromise
  send mailbox (SyncMsg msg resultSetter)
  waitForPromise result


-- === Diff server ===

data IncServerState s = IncServerState
  { subscribers     :: [Mailbox (Delta s)]
  , bufferedUpdates :: Delta s
  , curIncState     :: s }
  deriving (Generic)

class (IncState s, MonadIO m) => IncServer s m | m -> s where
  getIncServerStateRef :: m (IORef (IncServerState s))

data SubscribeMsg s = Subscribe (SyncMsg (Mailbox (Delta s)) s)  deriving (Show)

getIncServerState :: IncServer s m => m (IncServerState s)
getIncServerState = readRef =<< getIncServerStateRef

updateIncServerState :: IncServer s m => (IncServerState s -> IncServerState s) -> m ()
updateIncServerState f = do
  ref <- getIncServerStateRef
  prev <- readRef ref
  writeRef ref $ f prev

handleSubscribeMsg :: IncServer s m => SubscribeMsg s -> m ()
handleSubscribeMsg (Subscribe (SyncMsg newSub response)) = do
  flushDiffs
  updateIncServerState \s -> s { subscribers = newSub : subscribers s }
  curState <- curIncState <$> getIncServerState
  setPromise response curState

flushDiffs :: IncServer s m => m ()
flushDiffs = do
  d <- bufferedUpdates <$> getIncServerState
  updateIncServerState \s -> s { bufferedUpdates = mempty }
  subs <- subscribers <$> getIncServerState
  -- TODO: consider testing for emptiness here
  forM_ subs \sub -> send sub d

type StateServer s = Mailbox (SubscribeMsg s)

subscribe :: (IncState s, Actor msg m) => (Delta s -> msg) -> StateServer s -> m s
subscribe inject server = do
  updateChannel <- selfMailbox inject
  sendSync (sliceMailbox Subscribe server) updateChannel

subscribeIO :: IncState s => StateServer s -> IO (s, Chan (Delta s))
subscribeIO server = do
  chan <- newChan
  let mailbox = Mailbox (writeChan chan)
  s <- sendSync (sliceMailbox Subscribe server) mailbox
  return (s, chan)

newtype IncServerT s m a = IncServerT { runIncServerT' :: ReaderT (Ref (IncServerState s)) m a }
  deriving (Functor, Applicative, Monad, MonadIO, Actor msg, FreshNames name, MonadTrans)

instance (MonadIO m, IncState s) => IncServer s (IncServerT s m) where
  getIncServerStateRef = IncServerT ask

instance (MonadIO m, IncState s, d ~ Delta s) => DefuncState d (IncServerT s m) where
  update d = updateIncServerState \s -> s
    { bufferedUpdates = bufferedUpdates s <> d
    , curIncState     = curIncState     s `applyDiff` d}

instance (MonadIO m, IncState s) => LabelReader (SingletonLabel s) (IncServerT s m) where
  getl It = curIncState <$> getIncServerState

runIncServerT :: (MonadIO m, IncState s) => s -> IncServerT s m a -> m a
runIncServerT s cont = do
  ref <- newRef $ IncServerState [] mempty s
  runReaderT (runIncServerT' cont) ref

-- === Refs ===
-- Just a wrapper around IORef lifted to `MonadIO`

type Ref = IORef

newRef :: MonadIO m => a -> m (Ref a)
newRef = liftIO . newIORef

readRef :: MonadIO m => Ref a -> m a
readRef = liftIO . readIORef

writeRef :: MonadIO m => Ref a -> a -> m ()
writeRef ref val = liftIO $ writeIORef ref val

-- === Clock ===

-- Provides a periodic clock signal. The time interval is in microseconds.
launchClock :: MonadIO m => Int -> Mailbox () -> m ()
launchClock intervalMicroseconds mailbox =
  liftIO $ void $ forkIO $ forever do
    threadDelay intervalMicroseconds
    send mailbox ()

-- === File watcher ===

type SourceFileContents = Text
type FileWatcher = StateServer (Overwritable SourceFileContents)

data FileWatcherMsg =
   ClockSignal_FW ()
 | Subscribe_FW (SubscribeMsg (Overwritable Text))
   deriving (Show)

launchFileWatcher :: MonadIO m => FilePath -> m FileWatcher
launchFileWatcher path = sliceMailbox Subscribe_FW <$> launchActor (fileWatcherImpl path)

fileWatcherImpl :: FilePath -> ActorM FileWatcherMsg ()
fileWatcherImpl path = do
  initContents <- readFileText path
  t0 <- liftIO $ getModificationTime path
  launchClock 100000 =<< selfMailbox ClockSignal_FW
  modTimeRef <- newRef t0
  runIncServerT (Overwritable initContents) $ messageLoop \case
    Subscribe_FW msg -> handleSubscribeMsg msg
    ClockSignal_FW () -> do
      tOld <- readRef modTimeRef
      tNew <- liftIO $ getModificationTime path
      when (tNew /= tOld) do
        newContents <- readFileText path
        update $ OverwriteWith newContents
        flushDiffs
        writeRef modTimeRef tNew

-- === instances ===

instance Show msg => Show (SyncMsg msg response) where
  show (SyncMsg msg _) = show msg

instance Show (Mailbox a) where
  show _ = "mailbox"

deriving instance Actor msg m => Actor msg (FreshNameT m)
