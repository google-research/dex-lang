-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module SourceInfo (
  SrcPos, SourceId (..), SrcPosCtx (..), emptySrcPosCtx, fromPos,
  pattern EmptySrcPosCtx) where

import Data.Hashable
import Data.Store (Store (..))
import GHC.Generics (Generic (..))

-- === Core API ===

newtype SourceId = SourceId Int  deriving (Show, Eq, Ord, Generic)

type SrcPos = (Int, Int)

data SrcPosCtx = SrcPosCtx (Maybe SrcPos) (Maybe SourceId)
  deriving (Show, Eq, Generic)

emptySrcPosCtx :: SrcPosCtx
emptySrcPosCtx = SrcPosCtx Nothing Nothing

pattern EmptySrcPosCtx :: SrcPosCtx
pattern EmptySrcPosCtx = SrcPosCtx Nothing Nothing

fromPos :: SrcPos -> SrcPosCtx
fromPos pos = SrcPosCtx (Just pos) Nothing

instance Ord SrcPosCtx where
  compare (SrcPosCtx pos spanId) (SrcPosCtx pos' spanId') =
    case (pos, pos') of
      (Just (l, r), Just (l', r')) -> compare (l, r', spanId) (l', r, spanId')
      (Just _, _) -> GT
      (_, Just _) -> LT
      (_, _) -> compare spanId spanId'

instance Hashable SourceId
instance Hashable SrcPosCtx

instance Store SourceId
instance Store SrcPosCtx
