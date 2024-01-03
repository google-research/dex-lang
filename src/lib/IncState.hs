-- Copyright 2023 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module IncState (
  IncState (..), MapEltUpdate (..), MapUpdate (..),
  Overwrite (..), TailUpdate (..), Unchanging (..), Overwritable (..),
  mapUpdateMapWithKey, MonoidState (..), AllOrNothing (..), fmapIncMap,
  IncM, IncVar, liftIncM, runIncM, IncFun, fmapIncVar, incZip2, incUnzip3,
  incUnzip2, incZip3, liftMonoidStateIncM) where

import Control.Monad.State.Strict
import Data.IORef

import Data.Aeson (ToJSON (..))
import qualified Data.Map.Strict as M
import GHC.Generics
import Data.Maybe (fromJust)

-- === incremental computation builder ===

-- We use IO here for IORefs but we could use ST or something else instead
type IncFun a b = a -> IO (b, Delta a -> IO (Delta b))
type IncM = StateT (IO ()) IO
type IncVar a = (a, IORef (Maybe (Delta a)))

liftIncM :: IncVar a -> IncFun a b -> IncM (IncVar b)
liftIncM (x, dxRef) f = do
  (y, df) <- liftIO $ f x
  dyRef <- liftIO $ newIORef Nothing
  addIncAction do
    Just dx <- liftIO $ readIORef dxRef
    dy <- df dx
    liftIO $ writeIORef dyRef (Just dy)
  return (y, dyRef)

-- like LiftIncM but you don't have to bother with the initial values
liftMonoidStateIncM :: IncVar (MonoidState a) -> IO (a -> IO b) -> IncM (IncVar (MonoidState b))
liftMonoidStateIncM v createIncFun = liftIncM v \(MonoidState xInit) -> do
  incFun <- createIncFun
  yInit <- incFun xInit
  return (MonoidState yInit, incFun)

runIncM :: (IncVar a -> IncM (IncVar b)) -> IncFun a b
runIncM f = \x -> do
  dxRef <- newIORef Nothing
  ((y, dyRef), action) <- runStateT (f (x, dxRef)) (return ())
  return (y, \dx -> do
     writeIORef dxRef (Just dx)
     action
     fromJust <$> readIORef dyRef)

fmapIncVar :: IncVar a -> (a -> b) -> (Delta a -> Delta b) -> IncM (IncVar b)
fmapIncVar v f df = liftIncM v \x -> return (f x, \dx -> return $ df dx)

fmapIncMap
  :: forall k a b. Ord k
  => IncVar (M.Map k a) -> (k -> IncVar a -> IncM (IncVar b)) -> IncM (IncVar (M.Map k b))
fmapIncMap v f = liftIncM v \m -> do
  initDfsAndResults <- flip M.traverseWithKey m \k x -> runIncM (f k) x
  let initResults = (fst <$> initDfsAndResults) :: M.Map k b
  let initDfs     = (snd <$> initDfsAndResults) :: M.Map k (Delta a -> IO (Delta b))
  dfsRef <- newIORef initDfs
  return (initResults, deltaComputation dfsRef)
  where
    deltaComputation
      :: IORef (M.Map k (Delta a -> IO (Delta b)))
      -> MapUpdate k a -> IO (MapUpdate k b)
    deltaComputation dfs dxs = MapUpdate <$> do
      flip M.traverseWithKey (mapUpdates dxs) \k -> \case
       Create x -> do
         (y, df) <- runIncM (f k) x
         modifyIORef dfs (M.insert k df)
         return $ Create y
       Replace x -> do
         (y, df) <- runIncM (f k) x
         modifyIORef dfs (M.insert k df)
         return $ Replace y
       Update dx -> do
         df <- fromJust <$> M.lookup k <$> readIORef dfs
         Update <$> df dx
       Delete -> do
         modifyIORef dfs (M.delete k)
         return Delete

incUnzip2 :: IncVar (a, b) -> IncM (IncVar a, IncVar b)
incUnzip2 v = do
  x <- fmapIncVar v (\(x, _) -> x) (\(dx, _ ) -> dx)
  y <- fmapIncVar v (\(_, y) -> y) (\(_ , dy) -> dy)
  return (x, y)

incUnzip3 :: IncVar (a, b, c) -> IncM (IncVar a, IncVar b, IncVar c)
incUnzip3 v = do
  x <- fmapIncVar v (\(x, _, _) -> x) (\(dx, _ , _ ) -> dx)
  y <- fmapIncVar v (\(_, y, _) -> y) (\(_ , dy, _ ) -> dy)
  z <- fmapIncVar v (\(_, _, z) -> z) (\(_ , _ , dz) -> dz)
  return (x, y, z)

zipIncVar :: IncVar a -> IncVar b -> IncM (IncVar (a, b))
zipIncVar (x, dxRef) (y, dyRef) = do
  let xy = (x, y)
  dxyRef <- liftIO $ newIORef Nothing
  addIncAction do
    Just dx <- liftIO $ readIORef dxRef
    Just dy <- liftIO $ readIORef dyRef
    liftIO $ writeIORef dxyRef (Just (dx, dy))
  return (xy, dxyRef)

zipWithIncVar :: IncVar a -> IncVar b -> (a -> b -> c) -> (Delta a -> Delta b -> Delta c) -> IncM (IncVar c)
zipWithIncVar x y f df = do
  xy <- zipIncVar x y
  fmapIncVar xy (uncurry f) (uncurry df)

incZip2 :: IncVar a -> IncVar b -> IncM (IncVar (a, b))
incZip2 x y = zipWithIncVar x y (,) (,)

incZip3 :: IncVar a -> IncVar b -> IncVar c -> IncM (IncVar (a, b, c))
incZip3 x y z = do
  xy <- zipWithIncVar x y (,) (,)
  zipWithIncVar xy z (\(a,b) c -> (a, b, c)) (\(a,b) c -> (a, b, c))

instance (IncState a, IncState b, IncState c) => IncState (a, b, c) where
  type Delta (a, b, c) = (Delta a, Delta b, Delta c)
  applyDiff (x, y, z) (dx, dy, dz) = (applyDiff x dx, applyDiff y dy, applyDiff z dz)

instance (IncState a, IncState b) => IncState (a, b) where
  type Delta (a, b) = (Delta a, Delta b)
  applyDiff (x, y) (dx, dy) = (applyDiff x dx, applyDiff y dy)


addIncAction :: IO () -> IncM ()
addIncAction action = modify \curAction -> curAction >> action

-- === AllOrNothing class ===

class (forall a. IncState (f a)) => AllOrNothing f where
  fmapAllOrNothing :: IncVar (f a) -> (a -> b) -> IncM (IncVar (f b))

instance AllOrNothing Unchanging where
  fmapAllOrNothing v f = fmapIncVar v (\(Unchanging x) -> Unchanging (f x)) (const ())

instance AllOrNothing Overwritable where
  fmapAllOrNothing v f = fmapIncVar v (\(Overwritable x) -> Overwritable (f x)) (fmap f)

-- === Delta type family ===

class Monoid (Delta s) => IncState s where
  type Delta s :: *
  applyDiff :: s -> Delta s -> s

-- === Diff utils ===

data MapEltUpdate s =
   Create s
 | Replace s  -- TODO: should we merge Create/Replace?
 | Update (Delta s)
 | Delete
   deriving (Generic)

newtype MapUpdate k s = MapUpdate { mapUpdates :: M.Map k (MapEltUpdate s) }

mapUpdateMapWithKey
  :: (IncState s, IncState s')
  => MapUpdate k s -> (k -> s -> s') -> (k -> Delta s -> Delta s') -> MapUpdate k s'
mapUpdateMapWithKey (MapUpdate m) fs fd =
  MapUpdate $ flip M.mapWithKey m \k v -> case v of
    Create  s -> Create $ fs k s
    Replace s -> Replace $ fs k s
    Update d  -> Update $ fd k d
    Delete    -> Delete

instance (IncState s, Ord k) => Monoid (MapUpdate k s) where
  mempty = MapUpdate mempty

instance (IncState s, Ord k) => Semigroup (MapUpdate k s) where
  MapUpdate m1 <> MapUpdate m2 = MapUpdate $
    M.mapMaybe id (M.intersectionWith combineElts m1 m2)
      <> M.difference m1 m2
      <> M.difference m2 m1
    where combineElts e1 e2 = case e1 of
            Create s -> case e2 of
              Create _ -> error "shouldn't be creating a node that already exists"
              Replace s' -> Just $ Create s'
              Update d -> Just $ Create (applyDiff s d)
              Delete   -> Nothing
            Replace s -> case e2 of
              Create _ -> error "shouldn't be creating a node that already exists"
              Replace s' -> Just $ Replace s'
              Update d -> Just $ Replace (applyDiff s d)
              Delete   -> Nothing
            Update d -> case e2 of
              Create _ -> error "shouldn't be creating a node that already exists"
              Replace s -> Just $ Replace s
              Update d' -> Just $ Update (d <> d')
              Delete   -> Just $ Delete
            Delete -> case e2 of
              Create s -> Just $ Replace s
              Replace _ -> error "shouldn't be replacing a node that doesn't exist"
              Update _  -> error "shouldn't be updating a node that doesn't exist"
              Delete    -> error "shouldn't be deleting a node that doesn't exist"

instance (IncState s, Ord k) => IncState (M.Map k s) where
  type Delta (M.Map k s) = MapUpdate k s
  applyDiff m (MapUpdate updates) =
          M.mapMaybe id (M.intersectionWith applyEltUpdate m updates)
       <> M.difference m updates
       <> M.mapMaybe applyEltCreation (M.difference updates m)
    where applyEltUpdate s = \case
            Create _ -> error "key already exists"
            Replace s' -> Just s'
            Update d -> Just $ applyDiff s d
            Delete   -> Nothing
          applyEltCreation = \case
            Create s -> Just s
            Replace _ -> error "key doesn't exist yet"
            Update _  -> error "key doesn't exist yet"
            Delete    -> error "key doesn't exist yet"

data TailUpdate a = TailUpdate
  { numDropped :: Int
  , newTail    :: [a] }
  deriving (Show, Generic)

instance Semigroup (TailUpdate a) where
  TailUpdate n1 xs1 <> TailUpdate n2 xs2 =
    let xs1Rem = length xs1 - n2 in
    if xs1Rem >= 0
      then TailUpdate n1 (take xs1Rem xs1 <> xs2) -- n2 clobbered by xs1
      else TailUpdate (n1 - xs1Rem) xs2           -- xs1 clobbered by n2

instance Monoid (TailUpdate a) where
  mempty = TailUpdate 0 []

instance IncState [a] where
  type Delta [a] = TailUpdate a
  applyDiff xs (TailUpdate numDrop ys) = take (length xs - numDrop) xs <> ys

-- Trivial diff that works for any type - just replace the old value with a completely new one.
data Overwrite a = NoChange | OverwriteWith a
  deriving (Show, Eq, Generic, Functor, Foldable, Traversable)
newtype Overwritable a = Overwritable { fromOverwritable :: a } deriving (Show, Eq, Ord)

instance Semigroup (Overwrite a) where
  l <> r = case r of
    OverwriteWith r' -> OverwriteWith r'
    NoChange         -> l

instance Monoid (Overwrite a) where
  mempty = NoChange

instance IncState (Overwritable a) where
  type Delta (Overwritable a) = Overwrite a
  applyDiff s = \case
    NoChange         -> s
    OverwriteWith s' -> Overwritable s'

-- Case when the diff and the state are the same
newtype MonoidState a = MonoidState a

instance Monoid a => IncState (MonoidState a) where
  type Delta (MonoidState a) = a
  applyDiff (MonoidState d) d' = MonoidState $ d <> d'

-- Trivial diff that works for any type - just replace the old value with a completely new one.
newtype Unchanging a = Unchanging { fromUnchanging :: a } deriving (Show, Eq, Ord)

instance IncState (Unchanging a) where
  type Delta (Unchanging a) = ()
  applyDiff s () = s

instance            ToJSON a  => ToJSON (Overwrite a)
instance (ToJSON k, ToJSON s, ToJSON (Delta s)) => ToJSON (MapUpdate k s) where
  toJSON m = toJSON $ M.toList $ mapUpdates m
instance ToJSON a => ToJSON (TailUpdate a)
instance (ToJSON s, ToJSON (Delta s)) => ToJSON (MapEltUpdate s)
