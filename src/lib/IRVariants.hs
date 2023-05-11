-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE AllowAmbiguousTypes #-}

module IRVariants
  ( IR (..), IRPredicate (..), Sat, Sat'
  , CoreToSimpIR, InferenceIR, IRRep (..), IRProxy (..), interpretIR
  , IRsEqual (..), eqIRRep, WhenIR (..)) where

import GHC.Generics (Generic (..))
import Data.Store
import Data.Hashable
import Data.Store.Internal
import Data.Kind

import qualified Unsafe.Coerce as TrulyUnsafe

data IR =
   CoreIR -- used after inference and before simplification
 | SimpIR -- used after simplification
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
  Sat' SimpIR (IsSubsetOf CoreIR)            = True
  -- DAMOps
  Sat' SimpIR      (HasFeature DAMOps)       = True
  -- DAMOps
  Sat' SimpIR      (HasFeature SimpOps)      = True
  -- CoreOps
  Sat' CoreIR       (HasFeature CoreOps)     = True
  -- otherwise
  Sat' _ _ = False

class IRRep (r::IR) where
  getIRRep :: IR

data IRProxy (r::IR) = IRProxy

interpretIR :: IR -> (forall r. IRRep r => IRProxy r -> a) -> a
interpretIR ir cont = case ir of
  CoreIR      -> cont $ IRProxy @CoreIR
  SimpIR      -> cont $ IRProxy @SimpIR

instance IRRep CoreIR where getIRRep = CoreIR
instance IRRep SimpIR where getIRRep = SimpIR

data IRsEqual (r1::IR) (r2::IR) where
  IRsEqual :: IRsEqual r r

eqIRRep :: forall r1 r2. (IRRep r1, IRRep r2) => Maybe (IRsEqual r1 r2)
eqIRRep = if r1Rep == r2Rep
 then Just (TrulyUnsafe.unsafeCoerce (IRsEqual :: IRsEqual r1 r1) :: IRsEqual r1 r2)
 else Nothing
 where r1Rep = getIRRep @r1; r2Rep = getIRRep @r2
{-# INLINE eqIRRep #-}

data WhenIR (r::IR) (r'::IR) (a::Type) where
  WhenIR :: a -> WhenIR r r a

instance (IRRep r, IRRep r', Store e) => Store (WhenIR r r' e) where
  size = VarSize \(WhenIR e) -> getSize e
  peek = case eqIRRep @r @r' of
    Just IRsEqual -> WhenIR <$> peek
    Nothing -> error "impossible"
  poke (WhenIR e) = poke e

instance Hashable a => Hashable (WhenIR r r' a) where
  hashWithSalt salt (WhenIR a) = hashWithSalt salt a

deriving instance Show a => Show (WhenIR r r' a)
deriving instance Eq a => Eq (WhenIR r r' a)
