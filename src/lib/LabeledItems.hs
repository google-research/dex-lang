-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}

module LabeledItems (
  Label, LabeledItems (..), labeledSingleton, reflectLabels, getLabels,
  withLabels, lookupLabelHead, pattern NoLabeledItems,
  pattern InternalSingletonLabel, pattern Unlabeled,
  ) where

import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M

import Preamble
import Util

-- The label for a field in a record or variant.
type Label = String

-- Collection of labeled values of type `a`. Each value has a field label, and
-- multiple values can share the same label. This is the canonical form for
-- the item types in record and variant types as well as for the values in
-- record objects; the order in the concrete syntax of items with different
-- fields is discarded (so both `{b:Z & a:X & a:Y}` and `{a:X & b:Z & a:Y}` map
-- to `M.fromList [("a", NE.fromList [X, Y]), ("b", NE.fromList [Z])]` )
newtype LabeledItems a = LabeledItems (M.Map Label (NE.NonEmpty a))
  deriving (Eq, Show, Generic, Functor, Foldable, Traversable, Store)

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

instance Semigroup (LabeledItems a) where
  LabeledItems items <> LabeledItems items' =
    LabeledItems $ M.unionWith (<>) items items'

instance Monoid (LabeledItems a) where
  mempty = NoLabeledItems

pattern NoLabeledItems :: LabeledItems a
pattern NoLabeledItems <- ((\(LabeledItems items) -> M.null items) -> True)
  where NoLabeledItems = LabeledItems M.empty

-- An internal label that we can use to treat records and variants as unlabeled
-- internal sum and product types. Note that this is not a valid label in the
-- concrete syntax and will be rejected by the parser (although there wouldn't
-- be any serious problems with overloading a user-written label).
pattern InternalSingletonLabel :: Label
pattern InternalSingletonLabel = "%UNLABELED%"

_getUnlabeled :: LabeledItems a -> Maybe [a]
_getUnlabeled (LabeledItems items) = case length items of
  0 -> Just []
  1 -> NE.toList <$> M.lookup InternalSingletonLabel items
  _ -> Nothing

pattern Unlabeled :: [a] -> LabeledItems a
pattern Unlabeled as <- (_getUnlabeled -> Just as)
  where Unlabeled as = case NE.nonEmpty as of
          Just ne -> LabeledItems (M.singleton InternalSingletonLabel ne)
          Nothing -> NoLabeledItems

