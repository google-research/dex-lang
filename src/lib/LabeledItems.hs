-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module LabeledItems
  ( Label, LabeledItems (..), labeledSingleton, reflectLabels, getLabels
  , withLabels, lookupLabelHead, lookupLabel, ExtLabeledItems (..), prefixExtLabeledItems
  , unzipExtLabeledItems, splitLabeledItems, popLabeledItems
  , pattern NoLabeledItems, pattern NoExt ) where

import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import Data.Hashable
import Data.Foldable (toList)
import Data.Store (Store)
import GHC.Generics

import Util (enumerate)

-- The label for a field in a record or variant.
type Label = String

-- Collection of labeled values of type `a`. Each value has a field label, and
-- multiple values can share the same label. This is the canonical form for
-- the item types in record and variant types as well as for the values in
-- record objects; the order in the concrete syntax of items with different
-- fields is discarded (so both `{b:Z & a:X & a:Y}` and `{a:X & b:Z & a:Y}` map
-- to `M.fromList [("a", NE.fromList [X, Y]), ("b", NE.fromList [Z])]` )
newtype LabeledItems a = LabeledItems { fromLabeledItems :: M.Map Label (NE.NonEmpty a) }
  deriving (Eq, Show, Generic, Functor, Foldable, Traversable)

labeledSingleton :: Label -> a -> LabeledItems a
labeledSingleton label value = LabeledItems $ M.singleton label (value NE.:|[])

reflectLabels :: LabeledItems a -> LabeledItems (Label, Int)
reflectLabels (LabeledItems items) = LabeledItems $
  flip M.mapWithKey items \k xs -> fmap (\(i,_) -> (k,i)) (enumerate xs)

getLabels :: LabeledItems a -> [Label]
getLabels labeledItems = map fst $ toList $ reflectLabels labeledItems

withLabels :: LabeledItems a -> LabeledItems (Label, Int, a)
withLabels (LabeledItems items) = LabeledItems $
  flip M.mapWithKey items \k xs -> fmap (\(i,a) -> (k,i,a)) (enumerate xs)

lookupLabelHead :: LabeledItems a -> Label -> Maybe a
lookupLabelHead (LabeledItems items) l = case M.lookup l items of
  Nothing -> Nothing
  Just (x NE.:| _) -> Just x

lookupLabel :: LabeledItems a -> Label -> [a]
lookupLabel (LabeledItems items) l = case M.lookup l items of
  Just (x NE.:| xs) -> x : xs
  Nothing -> []

instance Semigroup (LabeledItems a) where
  LabeledItems items <> LabeledItems items' =
    LabeledItems $ M.unionWith (<>) items items'

instance Monoid (LabeledItems a) where
  mempty = NoLabeledItems

-- Extensible version of LabeledItems, which allows an optional object in tail
-- position. The items of the tail object will always be interpreted as a
-- "suffix" in the sense that for any field label, the object represented by
-- an ExtLabeledItems contains first the values in the (LabeledItems a) for that
-- field, followed by the values in the (Maybe b) for that field if they exist.
data ExtLabeledItems a b = Ext (LabeledItems a) (Maybe b)
  deriving (Eq, Show, Generic)

-- Adds more items to the front of an ExtLabeledItems.
prefixExtLabeledItems :: LabeledItems a -> ExtLabeledItems a b -> ExtLabeledItems a b
prefixExtLabeledItems items (Ext items' rest) = Ext (items <> items') rest

-- The returned list is parallel to the input LabeledItems, following
-- the sort order of the labels.
unzipExtLabeledItems :: ExtLabeledItems a b -> (ExtLabeledItems () (), [a], Maybe b)
unzipExtLabeledItems (Ext items (Just b)) =
  (Ext ((const ()) <$> items) (Just ()), (toList items), Just b)
unzipExtLabeledItems (Ext items Nothing) =
  (Ext ((const ()) <$> items) Nothing, (toList items), Nothing)

pattern NoLabeledItems :: LabeledItems a
pattern NoLabeledItems <- ((\(LabeledItems items) -> M.null items) -> True)
  where NoLabeledItems = LabeledItems M.empty

pattern NoExt :: LabeledItems a -> ExtLabeledItems a b
pattern NoExt a = Ext a Nothing

splitLabeledItems :: LabeledItems a -> LabeledItems b -> (LabeledItems b, LabeledItems b)
splitLabeledItems (LabeledItems litems) (LabeledItems fullItems) =
  (LabeledItems left, LabeledItems right)
  where
    splitLeft fvs ltys = NE.fromList $ NE.take (length ltys) fvs
    splitRight fvs ltys = NE.nonEmpty $ NE.drop (length ltys) fvs
    left  = M.intersectionWith splitLeft fullItems litems
    right = M.differenceWith splitRight fullItems litems

popLabeledItems :: Label -> LabeledItems b -> Maybe (b, LabeledItems b)
popLabeledItems l items = case lookupLabelHead items l of
  Just val -> Just (val, snd $ splitLabeledItems (labeledSingleton l ()) items)
  Nothing  -> Nothing

-- === instances ===

instance Store a => Store (LabeledItems a)
instance (Store a, Store b) => Store (ExtLabeledItems a b)

instance Hashable a => Hashable (LabeledItems a) where
  -- explicit implementation because `Map.Map` doesn't have a hashable instance
  hashWithSalt salt (LabeledItems items) =
    hashWithSalt salt $ M.toList items

instance (Hashable a, Hashable b) => Hashable (ExtLabeledItems a b)
