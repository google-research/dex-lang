-- Copyright 2023 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module IncState (
  IncState (..), MapEltUpdate (..), MapUpdate (..),
  Overwrite (..), TailUpdate (..), mapUpdateMapWithKey) where

import qualified Data.Map.Strict as M
import GHC.Generics

-- === IncState ===

class Monoid d => IncState s d where
  applyDiff :: s -> d -> s

-- === Diff utils ===

data MapEltUpdate v =
   Create v
 | Update v
 | Delete
 deriving (Functor, Show, Generic)

data MapUpdate k v = MapUpdate { mapUpdates :: M.Map k (MapEltUpdate v) }
     deriving (Functor, Show, Generic)

mapUpdateMapWithKey :: MapUpdate k v -> (k -> v -> v') -> MapUpdate k v'
mapUpdateMapWithKey (MapUpdate m) f = MapUpdate $ M.mapWithKey (\k v -> fmap (f k) v) m

instance Ord k => Monoid (MapUpdate k v) where
  mempty = MapUpdate mempty

instance Ord k => Semigroup (MapUpdate k v) where
  MapUpdate m1 <> MapUpdate m2 = MapUpdate $
    M.mapMaybe id (M.intersectionWith combineElts m1 m2)
      <> M.difference m1 m2
      <> M.difference m2 m1
    where combineElts e1 e2 = case e1 of
            Create _ -> case e2 of
              Create _ -> error "shouldn't be creating a node that already exists"
              Update v -> Just $ Create v
              Delete   -> Nothing
            Update _ -> case e2 of
              Create _ -> error "shouldn't be creating a node that already exists"
              Update v -> Just $ Update v
              Delete   -> Just $ Delete
            Delete -> case e2 of
              Create v -> Just $ Update v
              Update _ -> error "shouldn't be updating a node that doesn't exist"
              Delete   -> error "shouldn't be deleting a node that doesn't exist"

instance Ord k => IncState (M.Map k v) (MapUpdate k v) where
  applyDiff m (MapUpdate updates) =
          M.mapMaybe id (M.intersectionWith applyEltUpdate m updates)
       <> M.difference m updates
       <> M.mapMaybe applyEltCreation (M.difference updates m)
    where applyEltUpdate _ = \case
            Create _ -> error "key already exists"
            Update v -> Just v
            Delete   -> Nothing
          applyEltCreation = \case
            Create v -> Just v
            Update _ -> error "key doesn't exist yet"
            Delete   -> error "key doesn't exist yet"

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
data Overwrite a = NoChange | OverwriteWith a  deriving (Show)

instance Semigroup (Overwrite a) where
  l <> r = case r of
    OverwriteWith r' -> OverwriteWith r'
    NoChange         -> l

instance Monoid (Overwrite a) where
  mempty = NoChange

instance IncState a (Overwrite a) where
  applyDiff s = \case
    NoChange         -> s
    OverwriteWith s' -> s'

