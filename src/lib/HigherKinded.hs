-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module HigherKinded (
  H (..), PairH (..), ListH, LiftH (..), MaybeH,
  UnitH, VoidH, pattern UnitH, fstH, sndH, forMH, forMH_,
  lengthH, mapMH_, fmapH, voidH,
  toListH, nullH, pattern JustH, pattern NothingH,
  PrettyH, PrettyH2, ShowH, ShowH2, EqH, EqH2,
  EitherH (..))
  where

import Data.Text.Prettyprint.Doc
import Data.Store (Store)
import GHC.Exts (Constraint)
import GHC.Generics
import Control.Monad
import Control.Monad.Identity


type PrettyH  e = (forall n.   Pretty (e n))   :: Constraint
type PrettyH2 b = (forall n l. Pretty (b n l)) :: Constraint

type ShowH  e = (forall n.   Show (e n))   :: Constraint
type ShowH2 b = (forall n l. Show (b n l)) :: Constraint

type EqH  e = (forall n.   Eq (e n))   :: Constraint
type EqH2 b = (forall n l. Eq (b n l)) :: Constraint

newtype H f e n = H { fromH :: f (e n) }  deriving (Show, Eq, Generic, Generic1, Store)
data UnitH n = UnitH                      deriving (Show, Eq, Generic, Generic1, Store)
data VoidH n                              deriving (          Generic, Generic1, Store)
data PairH e1 e2 n = PairH (e1 n) (e2 n)  deriving (Show, Eq, Generic, Generic1, Store)
type ListH = H []
type MaybeH = H Maybe
newtype LiftH a n = LiftH { fromLiftH :: a }  deriving (Show, Eq, Generic, Store)

data EitherH e1 e2 n = LeftH (e1 n) | RightH (e2 n)
     deriving (Show, Eq, Generic, Generic1, Store)

pattern JustH :: e n -> MaybeH e n
pattern JustH x = H (Just x)

pattern NothingH :: MaybeH e n
pattern NothingH = H Nothing

fstH :: PairH a b n -> a n
fstH (PairH x _) = x

sndH :: PairH a b n -> b n
sndH (PairH _ x) = x

mapMH :: (Traversable f, Applicative m)
      => (e1 n1 -> m (e2 n2)) -> H f e1 n1 -> m (H f e2 n2)
mapMH f xs = H <$> traverse f (fromH xs)

mapMH_ :: (Traversable f, Applicative m)
       => (e n -> m ()) -> H f e n -> m ()
mapMH_ f xs = void $ mapMH (const (pure UnitH) . f) xs

fmapH :: Traversable f => (e1 n1 -> e2 n2) -> H f e1 n1 -> H f e2 n2
fmapH f xs = runIdentity $ mapMH (return . f) xs

voidH :: Traversable f => H f e n1 -> H f UnitH n2
voidH xs = fmapH (const UnitH) xs

toListH :: Traversable f => H f e n -> [e n]
toListH = undefined

nullH :: Traversable f => H f e n -> Bool
nullH = null . toListH

lengthH :: Traversable f => H f e n -> Int
lengthH xs = length $ toListH xs

forMH_ :: (Traversable f, Applicative m)
       => H f e n -> (e n -> m ()) -> m ()
forMH_ = flip mapMH_

forMH :: (Traversable f, Applicative m)
      => H f e1 n1 -> (e1 n1 -> m (e2 n2))-> m (H f e2 n2)
forMH = flip mapMH

