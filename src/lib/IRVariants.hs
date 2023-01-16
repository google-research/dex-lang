-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE AllowAmbiguousTypes #-}

module IRVariants
  ( IR (..), IRPredicate (..), Sat, Sat', HasCore, HasCore', IsLowered, IsLowered'
  , CoreToSimpIR, InferenceIR, IsSimpish, IsSimpish'
  , IRRep (..), IRProxy (..), interpretIR) where

import GHC.Exts (Constraint)
import GHC.Generics (Generic (..))
import Data.Store

data IR =
   CoreIR       -- used after inference and before simplification
 | SimpIR       -- used after simplification
 | SimpToImpIR  -- used during the Simp-to-Imp translation
 | AnyIR        -- used for deserialization only
 deriving (Eq, Ord, Generic, Show, Enum)
instance Store IR

type CoreToSimpIR = CoreIR -- used during the Core-to-Simp translation
data IRFeature =
   DAMOps
 | CoreOps
 | SimpOps

-- TODO: make this a hard distinctions
type InferenceIR = CoreIR  -- used during type inference only

data IRPredicate =
   Is IR
 -- TODO: find a way to make this safe and derive it automatically. For now, we
 -- assert it manually for the valid cases we know about.
 | IsSubsetOf IR
 | HasFeature IRFeature

type Sat (r::IR) (p::IRPredicate) = (Sat' r p ~ True) :: Constraint
type family Sat' (r::IR) (p::IRPredicate) where
  Sat' r (Is r)                              = True
  -- subsets
  Sat' SimpIR (IsSubsetOf SimpToImpIR)       = True
  Sat' SimpIR (IsSubsetOf CoreIR)            = True
  -- DAMOps
  Sat' SimpIR      (HasFeature DAMOps)       = True
  Sat' SimpToImpIR (HasFeature DAMOps)       = True
  -- DAMOps
  Sat' SimpIR      (HasFeature SimpOps)      = True
  Sat' SimpToImpIR (HasFeature SimpOps)      = True
  -- CoreOps
  Sat' CoreIR       (HasFeature CoreOps)     = True
  -- otherwise
  Sat' _ _ = False

type HasCore  (r::IR) = r `Sat`  HasFeature CoreOps
type HasCore' (r::IR) = r `Sat'` HasFeature CoreOps

type IsLowered  r = r `Sat`  HasFeature DAMOps
type IsLowered' r = r `Sat'` HasFeature DAMOps

type IsSimpish  (r::IR) = r `Sat`  HasFeature SimpOps
type IsSimpish' (r::IR) = r `Sat'` HasFeature SimpOps

class IRRep (r::IR) where
  getIRRep :: IR

instance IRRep CoreIR      where getIRRep = CoreIR
instance IRRep SimpIR      where getIRRep = SimpIR
instance IRRep SimpToImpIR where getIRRep = SimpToImpIR

data IRProxy (r::IR) = IRProxy

interpretIR :: IR -> (forall r. IRRep r => IRProxy r -> a) -> a
interpretIR ir cont = case ir of
  CoreIR      -> cont $ IRProxy @CoreIR
  SimpIR      -> cont $ IRProxy @SimpIR
  SimpToImpIR -> cont $ IRProxy @SimpToImpIR
  AnyIR -> error "shouldn't reflect over AnyIR"
