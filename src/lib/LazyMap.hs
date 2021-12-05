-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module SaferNames.LazyMap (
  LazyMap, singleton, lookup, assocs, fromList, keysSet,
  forceLazyMap, mapWithKey, newLazyMap) where

import Prelude hiding (lookup)
import qualified Data.Set as S
import qualified Data.Map.Strict as M

-- This implements some of the Data.Map API, but also lets us apply fmap to it
-- lazily without having to traverse every element. For example we might use it
-- on a Name->Atom mapping that we want to temporarily view as a Name->Type
-- mapping using `fmap getType`. Data.Map.Lazy almost has this property but (I
-- think!) it still needs to touch every key, even if you only access a single
-- element of the resulting map. (If that's not true then we should ditch this
-- and use Data.Map.Lazy.) It also gives you O(1) access to its set of keys.
data LazyMap k a = LazyMap
  { keysSet    :: S.Set k    -- set of all keys in the map
  , _mainMap   :: M.Map k a  -- partial mapping from some of the keys to values
  , _fallback  :: k -> a }   -- mapping for keys in `keysSet` but not in `mainMap`

lookup :: Ord k => k -> LazyMap k a -> Maybe a
lookup k (LazyMap keys m f) =
  case M.lookup k m of
    Just x                      -> Just x
    Nothing | k `S.member` keys -> Just $ f k
            | otherwise         -> Nothing

newLazyMap :: Ord k => S.Set k -> (k -> a) -> LazyMap k a
newLazyMap keys f = LazyMap keys mempty f

singleton :: Ord k => k -> a -> LazyMap k a
singleton k v = LazyMap (S.singleton k) (M.singleton k v) neverCalled

assocs :: Ord k => LazyMap k a -> [(k, a)]
assocs m = [(k, lookupNoFailOption k m) | k <- S.toList $ keysSet m]

fromList ::  Ord k => [(k, a)] -> LazyMap k a
fromList kvs = fromMap $ M.fromList kvs

fromMap ::  Ord k => M.Map k a -> LazyMap k a
fromMap m = LazyMap (M.keysSet m) m neverCalled

forceLazyMap :: Ord k => LazyMap k a -> M.Map k a
forceLazyMap m = M.fromList $ assocs m

neverCalled :: k -> v
neverCalled _ = error "This should never be called!"

lookupNoFailOption :: Ord k => k -> LazyMap k v -> v
lookupNoFailOption k m = case lookup k m of
  Just x -> x
  Nothing -> error "failure is not an option"

mapWithKey :: Ord k => (k -> a -> b) -> LazyMap k a -> LazyMap k b
mapWithKey f lm = LazyMap (keysSet lm) mempty \k -> f k $ lookupNoFailOption k lm

-- XXX: left-biased, like Data.Map, but unlike our Subst-like structures.
-- This means it's lazy in the right argument, but the left one is forced.
instance Ord k => Semigroup (LazyMap k a) where
  lm1 <> LazyMap s2 m2 f2 =
    LazyMap (keysSet lm1 <> s2) (forceLazyMap lm1 <> m2) f2

instance Ord k => Monoid (LazyMap k a) where
  mempty = LazyMap mempty mempty  neverCalled

instance Ord k => Functor (LazyMap k) where
  fmap f lm = LazyMap (keysSet lm) mempty \k -> f $ lookupNoFailOption k lm

-- XXX: `foldMap` isn't lazy, unlike `fmap`.
instance Ord k => Foldable (LazyMap k) where
  foldMap f m = foldMap f $ forceLazyMap m

-- XXX: `traverse` isn't lazy, unlike `fmap`.
instance Ord k => Traversable (LazyMap k) where
  traverse f m = fromMap <$> traverse f (forceLazyMap m)
