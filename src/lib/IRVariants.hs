-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module IRVariants
  ( IR (..), IRPredicate (..), Sat, Sat', HasCore, HasCore', IsLowered, IsLowered'
  , unsafeCoerceIRE, unsafeCoerceFromAnyIR, unsafeCoerceIRB, injectIRE
  , injectFromCore, injectFromSimp
  , CovariantInIR, CoreToSimpIR, InferenceIR, IsSimpish, IsSimpish') where

import GHC.Exts (Constraint)
import Name
import qualified Unsafe.Coerce as TrulyUnsafe

data IR =
   CoreIR       -- used after inference and before simplification
 | SimpIR       -- used after simplification
 | SimpToImpIR  -- used during the Simp-to-Imp translation
 | AnyIR        -- used for deserialization only

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

-- XXX: the intention is that we won't have to use these much
unsafeCoerceIRE :: forall (r'::IR) (r::IR) (e::IR->E) (n::S). e r n -> e r' n
unsafeCoerceIRE = TrulyUnsafe.unsafeCoerce

-- XXX: the intention is that we won't have to use these much
unsafeCoerceFromAnyIR :: forall (r::IR) (e::IR->E) (n::S). e AnyIR n -> e r n
unsafeCoerceFromAnyIR = unsafeCoerceIRE

unsafeCoerceIRB :: forall (r'::IR) (r::IR) (b::IR->B) (n::S) (l::S) . b r n l -> b r' n l
unsafeCoerceIRB = TrulyUnsafe.unsafeCoerce

class CovariantInIR (e::IR->E)
-- For now we're "implementing" this instances manually as needed because we
-- don't actually need very many of them, but we should figure out a more
-- uniform way to do it.

-- This is safe, assuming the constraints have been implemented correctly.
injectIRE :: (CovariantInIR e, r `Sat` IsSubsetOf r') => e r n -> e r' n
injectIRE = unsafeCoerceIRE

injectFromCore :: (CovariantInIR e, HasCore r) => e CoreIR n -> e r n
injectFromCore = unsafeCoerceIRE

injectFromSimp :: (CovariantInIR e, IsSimpish r) => e SimpIR n -> e r n
injectFromSimp = unsafeCoerceIRE
