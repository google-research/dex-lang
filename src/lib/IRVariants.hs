-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module IRVariants
  ( IR (..), IRPredicate (..), Sat, Sat', IsCore, IsCore', IsLowered, IsLowered'
  , unsafeCoerceIRE, unsafeCoerceFromAnyIR, unsafeCoerceIRB, injectIRE
  , CovariantInIR, InferenceIR) where

import GHC.Exts (Constraint)
import Name
import qualified Unsafe.Coerce as TrulyUnsafe

data IR =
   CoreIR       -- used after inference and before simplification
 | SimpIR       -- used after simplification
 | SimpToImpIR  -- only used during the Simp-to-Imp translation
 | AnyIR        -- used for deserialization only

data IRFeature =
  DAMOps

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
  Sat' SimpIR (IsSubsetOf SimpToImpIR)       = True
  Sat' SimpIR (IsSubsetOf CoreIR)            = True
  Sat' SimpIR      (HasFeature DAMOps)       = True
  Sat' SimpToImpIR (HasFeature DAMOps)       = True
  Sat' _ _ = False

type IsCore  r = r `Sat`  Is CoreIR
type IsCore' r = r `Sat'` Is CoreIR
type IsLowered  r = r `Sat`  HasFeature DAMOps
type IsLowered' r = r `Sat'` HasFeature DAMOps

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

