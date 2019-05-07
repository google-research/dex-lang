{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Actor (Actor, Proc, PChan, CanTrap (..), Msg (..),
              runActor, spawn, spawnLink, send,
              receive, receiveF, receiveErr, receiveErrF,
              myChan, subChan, sendFromIO, ServerMsg (..),
              logServer, ReqChan) where

import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Identity
import Control.Exception
import Data.IORef
import Data.Monoid ((<>))
import qualified Data.Map.Strict as M

import Util

import Control.Concurrent

data Msg a = ErrMsg Proc String | NormalMsg a
data CanTrap = Trap | NoTrap  deriving (Show, Ord, Eq)
newtype PChan a = PChan { sendPChan :: a -> IO () }
data Proc = Proc CanTrap ThreadId  deriving (Show, Ord, Eq)
data BackChan a = BackChan (IORef [a]) (Chan a)
data ActorConfig m = ActorConfig { selfProc  :: Proc
                                 , selfChan  :: BackChan (Msg m)
                                 , linksPtr  :: IORef [Proc] }

newtype Actor m a = Actor (ReaderT (ActorConfig m) IO a)
  deriving (Functor, Applicative, Monad, MonadIO)

runActor :: Actor msg () -> IO ()
runActor (Actor m) = do
  linksRef   <- newIORef []
  chan <- newBackChan
  id <- myThreadId
  let p = (Proc Trap id)
  runReaderT m (ActorConfig p chan linksRef)

subChan :: (a -> b) -> PChan b -> PChan a
subChan f chan = PChan (sendPChan chan . f)

kill :: Proc -> Actor m ()
kill = undefined

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
  id <- forkIO $ do id <- myThreadId
                    let self = Proc canTrap id
                    runReaderT m (ActorConfig self chan linksRef)
                      `onException`
                         (readIORef linksRef >>= mapM (cleanup self))
  return (Proc canTrap id, asPChan chan)
  where
   cleanup :: Proc -> Proc -> IO ()
   cleanup = error "cleanup not yet implemented"

asPChan :: BackChan (Msg a) -> PChan a
asPChan (BackChan _ chan) = PChan (writeChan chan . NormalMsg)

send :: MonadActor msg' m => PChan msg -> msg -> m ()
send p x = liftIO (sendFromIO p x)

sendFromIO :: PChan msg -> msg -> IO ()
sendFromIO = sendPChan

myChan :: MonadActor msg m => m (PChan msg)
myChan = do cfg <- actorCfg
            return $ asPChan (selfChan cfg)

-- TODO: make a construct to receive in a loop to avoid repeated linear search
receiveErrF :: MonadActor msg m => (Msg msg -> Maybe a) -> m a
receiveErrF filter = do cfg <- actorCfg
                        liftIO $ find (selfChan cfg) []
  where find chan skipped = do
          x <- readBackChan chan
          case filter x of
            Just y -> do pushBackChan chan (reverse skipped)
                         return y
            Nothing -> find chan (x:skipped)

receiveErr :: MonadActor msg m => m (Msg msg)
receiveErr = receiveErrF Just

receiveF :: MonadActor msg m => (msg -> Maybe a) -> m a
receiveF filter = receiveErrF (skipErr >=> filter)
  where skipErr msg = case msg of NormalMsg x -> Just x
                                  ErrMsg _ _  -> Nothing

receive :: MonadActor msg m => m msg
receive = receiveF Just

newBackChan :: IO (BackChan a)
newBackChan = liftM2 BackChan (newIORef []) (newChan)

readBackChan :: BackChan a -> IO a
readBackChan (BackChan ptr chan) = do xs <- readIORef ptr
                                      case xs of []     -> readChan chan
                                                 x:rest -> do writeIORef ptr rest
                                                              return x

pushBackChan :: BackChan a -> [a] -> IO ()
pushBackChan (BackChan ptr chan) xs = do xs' <- readIORef ptr
                                         writeIORef ptr (xs ++ xs')

class (MonadIO m, Monad m) => MonadActor msg m | m -> msg where
  actorCfg :: m (ActorConfig msg)

instance MonadActor msg (Actor msg) where
  actorCfg = Actor ask

instance MonadActor msg m => MonadActor msg (StateT s m) where
  actorCfg = lift actorCfg

instance MonadActor msg m => MonadActor msg (ReaderT r m) where
  actorCfg = lift actorCfg

-- === ready-made actors for common patterns ===

-- similar to a CPS transformation a ==> (a -> r) -> r
type ReqChan a = PChan (PChan a)

data ServerMsg a = Request (PChan a)
                 | Push a

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
      mapM_ (flip send x) subscribers

-- TODO: state machine?
