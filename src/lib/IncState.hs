-- Copyright 2023 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module IncState (
  IncState (..), MapEltUpdate (..), MapUpdate (..),
  Overwrite (..), TailUpdate (..), Unchanging (..), Overwritable (..),
  mapUpdateMapWithKey) where

import Data.Aeson (ToJSON, ToJSONKey)
import qualified Data.Map.Strict as M
import GHC.Generics

-- === IncState ===

class Monoid d => IncState s d where
  applyDiff :: s -> d -> s

-- === Diff utils ===

data MapEltUpdate s d =
   Create s
 | Replace s  -- TODO: should we merge Create/Replace?
 | Update d
 | Delete
 deriving (Functor, Show, Generic)

data MapUpdate k s d = MapUpdate { mapUpdates :: M.Map k (MapEltUpdate s d) }
     deriving (Functor, Show, Generic)

mapUpdateMapWithKey :: MapUpdate k s d -> (k -> s -> s') -> (k -> d -> d') -> MapUpdate k s' d'
mapUpdateMapWithKey (MapUpdate m) fs fd =
  MapUpdate $ flip M.mapWithKey m \k v -> case v of
    Create  s -> Create $ fs k s
    Replace s -> Replace $ fs k s
    Update d  -> Update $ fd k d
    Delete    -> Delete

instance (IncState s d, Ord k) => Monoid (MapUpdate k s d) where
  mempty = MapUpdate mempty

instance (IncState s d, Ord k) => Semigroup (MapUpdate k s d) where
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

instance (IncState s d, Ord k) => IncState (M.Map k s) (MapUpdate k s d) where
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

instance IncState [a] (TailUpdate a) where
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

instance IncState (Overwritable a) (Overwrite a) where
  applyDiff s = \case
    NoChange         -> s
    OverwriteWith s' -> Overwritable s'


-- Trivial diff that works for any type - just replace the old value with a completely new one.
newtype Unchanging a = Unchanging { fromUnchanging :: a } deriving (Show, Eq, Ord)

instance IncState (Unchanging a) () where
  applyDiff s () = s

instance            ToJSON a  => ToJSON (Overwrite a)
instance (ToJSON s, ToJSON d, ToJSONKey k) => ToJSON (MapUpdate k s d)
instance ToJSON a => ToJSON (TailUpdate a)
instance (ToJSON s, ToJSON d) => ToJSON (MapEltUpdate s d)
