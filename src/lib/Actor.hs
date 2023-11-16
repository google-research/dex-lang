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
  runIncServerT, launchFileWatcher
  ) where

import Control.Concurrent
import Control.Monad
import Control.Monad.State.Strict hiding (get)
import Control.Monad.Reader
import qualified Data.ByteString as BS
import Data.IORef
import Data.Text.Encoding qualified as T
import Data.Text (Text)
import System.Directory (getModificationTime)
import GHC.Generics

import IncState
import MonadUtil

-- === Actor implementation ===

newtype ActorM msg a = ActorM { runActorM ::  ReaderT (Chan msg) IO a }
  deriving (Functor, Applicative, Monad, MonadIO)

newtype Mailbox a = Mailbox { sendToMailbox :: a -> IO () }

class (Show msg, MonadIO m) => Actor msg m | m -> msg where
  selfChan :: m (Chan msg)

instance Show msg => Actor msg (ActorM msg) where
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

data IncServerState s d = IncServerState
  { subscribers     :: [Mailbox d]
  , bufferedUpdates :: d
  , curIncState     :: s }
  deriving (Show, Generic)

class (Monoid d, MonadIO m) => IncServer s d m | m -> s, m -> d where
  getIncServerStateRef :: m (IORef (IncServerState s d))

data SubscribeMsg s d = Subscribe (SyncMsg (Mailbox d) s)  deriving (Show)

getIncServerState :: IncServer s d m => m (IncServerState s d)
getIncServerState = readRef =<< getIncServerStateRef

updateIncServerState :: IncServer s d m => (IncServerState s d -> IncServerState s d) -> m ()
updateIncServerState f = do
  ref <- getIncServerStateRef
  prev <- readRef ref
  writeRef ref $ f prev

handleSubscribeMsg :: IncServer s d m => SubscribeMsg s d -> m ()
handleSubscribeMsg (Subscribe (SyncMsg newSub response)) = do
  flushDiffs
  updateIncServerState \s -> s { subscribers = newSub : subscribers s }
  curState <- curIncState <$> getIncServerState
  setPromise response curState

flushDiffs :: IncServer s d m => m ()
flushDiffs = do
  d <- bufferedUpdates <$> getIncServerState
  updateIncServerState \s -> s { bufferedUpdates = mempty }
  subs <- subscribers <$> getIncServerState
  -- TODO: consider testing for emptiness here
  forM_ subs \sub -> send sub d

type StateServer s d = Mailbox (SubscribeMsg s d)

subscribe :: Actor msg m => (d -> msg) -> StateServer s d -> m s
subscribe inject server = do
  updateChannel <- selfMailbox inject
  sendSync (sliceMailbox Subscribe server) updateChannel

subscribeIO :: StateServer s d -> IO (s, Chan d)
subscribeIO server = do
  chan <- newChan
  let mailbox = Mailbox (writeChan chan)
  s <- sendSync (sliceMailbox Subscribe server) mailbox
  return (s, chan)

newtype IncServerT s d m a = IncServerT { runIncServerT' :: ReaderT (Ref (IncServerState s d)) m a }
  deriving (Functor, Applicative, Monad, MonadIO, Actor msg, FreshNames name, MonadTrans)

instance (MonadIO m, IncState s d) => IncServer s d (IncServerT s d m) where
  getIncServerStateRef = IncServerT ask

instance (MonadIO m, IncState s d) => DefuncState d (IncServerT s d m) where
  update d = updateIncServerState \s -> s
    { bufferedUpdates = bufferedUpdates s <> d
    , curIncState     = curIncState     s `applyDiff` d}

instance (MonadIO m, IncState s d) => LabelReader (SingletonLabel s) (IncServerT s d m) where
  getl It = curIncState <$> getIncServerState

runIncServerT :: (MonadIO m, IncState s d) => s -> IncServerT s d m a -> m a
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
type FileWatcher = StateServer SourceFileContents (Overwrite SourceFileContents)

readFileContents :: MonadIO m => FilePath -> m Text
readFileContents path = liftIO $ T.decodeUtf8 <$> BS.readFile path

data FileWatcherMsg =
   ClockSignal_FW ()
 | Subscribe_FW (SubscribeMsg Text (Overwrite Text))
   deriving (Show)

launchFileWatcher :: MonadIO m => FilePath -> m FileWatcher
launchFileWatcher path = sliceMailbox Subscribe_FW <$> launchActor (fileWatcherImpl path)

fileWatcherImpl :: FilePath -> ActorM FileWatcherMsg ()
fileWatcherImpl path = do
  initContents <- readFileContents path
  t0 <- liftIO $ getModificationTime path
  launchClock 100000 =<< selfMailbox ClockSignal_FW
  modTimeRef <- newRef t0
  runIncServerT initContents $ messageLoop \case
    Subscribe_FW msg -> handleSubscribeMsg msg
    ClockSignal_FW () -> do
      tOld <- readRef modTimeRef
      tNew <- liftIO $ getModificationTime path
      when (tNew /= tOld) do
        newContents <- readFileContents path
        update $ OverwriteWith newContents
        flushDiffs
        writeRef modTimeRef tNew

-- === instances ===

instance Show msg => Show (SyncMsg msg response) where
  show (SyncMsg msg _) = show msg

instance Show (Mailbox a) where
  show _ = "mailbox"

deriving instance Actor msg m => Actor msg (FreshNameT m)
