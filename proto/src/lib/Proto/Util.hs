-- Copyright 2025 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd
module Proto.Util ((<&>), liftIO, MonadIO, BS.ByteString,
                   w2c, c2w, module Proto.Util) where

import Control.Monad.IO.Class
import qualified Data.ByteString as BS
import Data.ByteString.Internal (w2c, c2w)
import Data.IORef
import Data.String
import Data.Functor

-- === misc ===

whileJust :: Monad m => m (Maybe a) -> (a -> m b) -> m [b]
whileJust test body = go [] where
  go xs = test >>= \case
    Nothing -> return xs
    Just x -> (:) <$> body x <*> whileJust test body
{-# INLINE whileJust #-}

whenJust :: Monad m => Maybe a -> (a -> m ()) -> m ()
whenJust maybeThing body = case maybeThing of
  Nothing -> return ()
  Just thing -> body thing
{-# INLINE whenJust #-}

-- === bytestrings ===

bs2str :: BS.ByteString -> String
bs2str s = map w2c $ BS.unpack s

str2bs :: String -> BS.ByteString
str2bs = fromString

readFile :: MonadIO m => FilePath -> m BS.ByteString
readFile path = liftIO $ BS.readFile path

-- === refs ===

type Ref = IORef

newRef :: MonadIO m => a -> m (Ref a)
newRef = liftIO . newIORef
{-# INLINE newRef #-}

class Gettable r where
  get :: MonadIO m => r a -> m a

instance Gettable IORef where
  get ref = liftIO $ readIORef ref
  {-# INLINE get #-}

set :: MonadIO m => IORef a -> a -> m ()
set ref = liftIO . writeIORef ref
{-# INLINE set #-}

update :: MonadIO m => IORef a -> (a -> a) -> m ()
update ref f = liftIO $ modifyIORef ref f
{-# INLINE update #-}

-- === LocalRef ===
-- A ref intended to be updated locally and then restored

newtype LocalRef a = LocalRef (Ref a)

newLocalRef :: MonadIO m => a -> m (LocalRef a)
newLocalRef x = LocalRef <$> newRef x
{-# INLINE newLocalRef #-}

instance Gettable LocalRef where
  get (LocalRef ref) = liftIO $ readIORef ref

setLocal :: MonadIO m => LocalRef a -> a -> m r -> m r
setLocal (LocalRef ref) new cont = do
  old <- get ref
  set ref new
  r <- cont
  set ref old
  return r
{-# INLINE setLocal #-}

-- === AppendRef ===
-- A ref to a list that you can only append to

newtype AppendRef a = AppendRef (Ref [a])  -- stored in reverse order

newAppendRef :: MonadIO m => m (AppendRef a)
newAppendRef = AppendRef <$> newRef []

append :: MonadIO m => AppendRef a -> a -> m ()
append (AppendRef ref) x = do
  xs <- liftIO $ readIORef ref
  liftIO $ writeIORef ref (x:xs)
{-# INLINE append #-}

readAppendRef :: MonadIO m => AppendRef a -> m r -> m (r, [a])
readAppendRef (AppendRef ref) cont = do
  prev <- get ref
  set ref []
  ans <- cont
  xsRev <- get ref
  set ref prev
  return (ans, reverse xsRev)
{-# INLINE readAppendRef #-}

-- === stack ===

newtype Stack a = Stack (Ref [a])

newStack :: MonadIO m => [a] -> m (Stack a)
newStack xs = Stack <$> newRef xs

push :: MonadIO m => Stack a -> a -> m ()
push (Stack ref) x = do
  xs <- liftIO $ readIORef ref
  liftIO $ writeIORef ref (x:xs)
{-# INLINE push #-}

pop :: MonadIO m => Stack a -> m (Maybe a)
pop (Stack ref) = do
  get ref >>= \case
    [] -> return Nothing
    x:xs -> do
      set ref xs
      return $ Just x
{-# INLINE pop #-}

peek :: MonadIO m => Stack a -> m (Maybe a)
peek (Stack ref) = do
  get ref >>= \case
    [] -> return Nothing
    x:_ -> do
      return $ Just x
{-# INLINE peek #-}

peekAll :: MonadIO m => Stack a -> m [a]
peekAll (Stack ref) = get ref
{-# INLINE peekAll #-}

-- === free applicative thingy ===

data FA m a where
  Pure :: a -> FA m a
  FMap :: (a -> b) -> m a -> FA m b
  LiftA2 :: (a -> b -> c) -> m a -> m b -> FA m c

class FromFA m where
  fromFA :: FA m a -> m a

newtype FreeApplicative m a = FreeApplicative (m a)

instance FromFA m => Functor (FreeApplicative m) where
  fmap f (FreeApplicative x) = FreeApplicative $ fromFA $ FMap f x

instance FromFA m => Applicative (FreeApplicative m) where
  pure x = FreeApplicative $ fromFA $ Pure x
  liftA2 f (FreeApplicative x) (FreeApplicative y) =
    FreeApplicative $ fromFA $ LiftA2 f x y

runFA :: Applicative m2 => (forall b. m1 b -> m2 b) -> FA m1 a -> m2 a
runFA run = \case
  Pure x -> pure x
  FMap f x -> f <$> run x
  LiftA2 f p1 p2 -> liftA2 f (run p1) (run p2)
