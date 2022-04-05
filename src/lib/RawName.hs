-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}

module RawName
  ( RawName, NameHint, HasNameHint (..), RawNameMap, noHint
  , rawNameFromHint, rawNamesFromHints, freshRawName, lookup, singleton, restrictKeys
  , keys, elems, mapWithKey, unionWith, difference, intersection
  , fromList, toList, RawName.null
  , member, disjoint, adjust) where

import Prelude hiding (lookup)
import qualified Data.IntMap.Lazy as M
import qualified Data.IntSet as S
import qualified Data.Text as T
import Data.Coerce
import Data.Store
import Data.String
import Data.Text.Prettyprint.Doc  hiding (nest)
import GHC.Generics (Generic)

-- === RawName ===

newtype RawName = RawName Int deriving (Eq, Ord, Generic)

freshRawName :: NameHint -> RawNameMap a -> RawName
freshRawName hint usedNames = RawName nextNum
  where
    nextNum = case M.lookupLT bigInt usedNames of
                Just (i, _)
                  | i < bigInt  -> i + 1
                  | otherwise   -> error "Ran out of numbers!"
                _ -> 0
    bigInt = (10::Int) ^ (9::Int)  -- TODO: consider a real sentinel value

rawNameFromHint :: NameHint -> RawName
rawNameFromHint _ = RawName 0

-- Names are guaranteed to be distinct from each other
rawNamesFromHints :: [NameHint] -> [RawName]
rawNamesFromHints hints = [RawName i | (i, _) <- zip [0..] hints]

-- === name map ===

type RawNameMap a = M.IntMap a

keys :: RawNameMap a -> [RawName]
keys m = coerce $ M.keys m

elems :: RawNameMap a -> [a]
elems m = coerce $ M.elems m

lookup :: RawName -> RawNameMap a -> Maybe a
lookup i m = M.lookup (coerce i) m

singleton :: RawName -> a -> RawNameMap a
singleton i x = M.singleton (coerce i) x

restrictKeys :: RawNameMap a -> [RawName] -> RawNameMap a
restrictKeys m xs = M.restrictKeys m (S.fromList $ coerce xs)

mapWithKey :: (RawName -> a -> b) -> RawNameMap a -> RawNameMap b
mapWithKey f m = M.mapWithKey (coerce f) m

unionWith :: (a -> a -> a) -> RawNameMap a ->  RawNameMap a -> RawNameMap a
unionWith f m1 m2 = M.unionWith (coerce f) m1 m2

difference :: RawNameMap a -> RawNameMap b -> RawNameMap a
difference m1 m2 = M.difference m1 m2

intersection :: RawNameMap a -> RawNameMap b -> RawNameMap a
intersection m1 m2 = M.intersection m1 m2

fromList :: [(RawName, a)] -> RawNameMap a
fromList xs = M.fromList (coerce xs)

toList :: RawNameMap a -> [(RawName, a)]
toList m = coerce $ M.toList m

member :: RawName -> RawNameMap a -> Bool
member i m = M.member (coerce i) m

disjoint :: RawNameMap a -> RawNameMap b -> Bool
disjoint m1 m2 = M.disjoint m1 m2

adjust :: (a -> a) -> RawName -> RawNameMap a -> RawNameMap a
adjust f i m = M.adjust f (coerce i) m

null :: RawNameMap a -> Bool
null = M.null

-- === conversion to/from strings ===

newtype NameHint = NameHint RawName

noHint :: NameHint
noHint = undefined

hint :: String -> NameHint
hint = undefined

class HasNameHint a where
  getNameHint :: a -> NameHint

instance HasNameHint RawName where
  getNameHint name = NameHint name

instance IsString NameHint where
  fromString = undefined

instance HasNameHint String where
  getNameHint = fromString


-- TODO: this needs to be sinkive but it's currently not
-- (needs to figure out acceptable tag strings)
instance Pretty RawName where
  pretty i = pretty (show i)

instance Show RawName where
  show (RawName i) = "v" ++ show i

-- === instances ===

instance Store RawName

