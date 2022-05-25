-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Interpreter (indices, indicesLimit, applyIntBinOp, applyIntCmpOp, applyFloatBinOp, applyFloatUnOp) where

import Data.Word
import Syntax

indices :: EnvReader m => IxType n -> m n [Atom n]
indicesLimit :: EnvReader m => Int -> IxType n -> m n (Either Word32 [Atom n])

applyIntBinOp :: (forall a. (Num a, Integral a) => a -> a -> a) -> Atom n -> Atom n -> Atom n
applyIntCmpOp :: (forall a. (Eq a, Ord a) => a -> a -> Bool) -> Atom n -> Atom n -> Atom n
applyFloatBinOp :: (forall a. (Num a, Fractional a) => a -> a -> a) -> Atom n -> Atom n -> Atom n
applyFloatUnOp :: (forall a. (Num a, Fractional a) => a -> a) -> Atom n -> Atom n
