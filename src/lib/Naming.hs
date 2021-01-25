-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}  -- for MTL lifting
{-# LANGUAGE ViewPatterns #-}

module Naming (
  NameStr, Name, Env, HasNames (..), MaySubst (..), Scope,
  Binder (..), Abs (..), lookupSubst, idSubst, SubstVal (..),
  NameReader (..), asDeferred,
  (@>), Nest (..), pattern Empty, Subst, DeferredSubst (..),
  PrettyH (..), NameHint, NaryAbs (..), AnnBinder (..),
  MaySubst, nameHint, forceSubst, freeNames
  ) where

-- module Naming (
--   NameStr, Name, Env, HasNames (..), MaySubst (..), Scope,
--   AlphaEq (..), Abs (..), buildAbs,
--   lookupSubst, idSubst, SubstVal (..), WithNames (..),
--   NameReader (..), NameWriter (..), asDeferred,
--   (@>), Nest (..), pattern Empty, Subst, DeferredSubst (..),
--   PrettyH (..), NameHint, NaryAbs (..), NestedAbs,
--   MaySubst, absNameHint, nameHint, uncurryDS, forceSubst, freeNames,
--   ) where

import qualified Data.Map.Strict as M
import qualified Data.Text as T
import Data.Dynamic
import Data.String
import Data.Store

import Preamble
import HigherKinded

-- === core API ===

type NameStr = T.Text
data RawName = RawName NameStr Int  deriving (Show, Eq, Ord, Generic)
newtype Name (s :: * -> *) (n :: *) = UnsafeMakeName RawName
        deriving (Show, Eq, Ord, Generic, Generic1)

data Binder (s :: * -> *) (n :: *) (i :: *) where
 Ignore           ::             Binder s n n
 UnsafeMakeBinder :: Name s i -> Binder s n i

newtype Subst d i n = UnsafeMakeSubst (Env i (SubstVal d UnitH n))
                      deriving (Show, Generic, Generic1)

data SubstVal d s n = SubstVal (d n)
                    | Rename (Name s n)
                      deriving (Show, Generic, Generic1)

data DeferredSubst d e n where
  Defer :: Subst d i n -> e i -> DeferredSubst d e n

idSubst :: Subst d n n
idSubst = UnsafeMakeSubst mempty

lookupSubst :: Name s i -> Subst d i n -> SubstVal d s n
lookupSubst v (UnsafeMakeSubst subst) = case envLookup v subst of
  Just (SubstVal x) -> SubstVal x
  Just (Rename v')  -> Rename $ unsafeCoerceBindingTy v'
  Nothing           -> Rename $ unsafeCoerceBindingTy $ unsafeCoerceNamespace v

applySubst :: (MaySubst d e, NameReader n m) => Subst d i n -> e i -> m (e n)
applySubst subst x = do
  scope <- getScope
  return $ applySubst' scope subst x

extendSubst :: Binder s i i' -> d n -> Subst d i n -> Subst d i' n
extendSubst (UnsafeMakeBinder v) x (UnsafeMakeSubst subst) = UnsafeMakeSubst $
  unsafeCoerceEnvKeys $ subst <> unsafeCoerceNamespace v @> SubstVal x

extendSubstRename :: Binder s i i' -> Name s n -> Subst d i n -> Subst d i' n
extendSubstRename (UnsafeMakeBinder v) v' (UnsafeMakeSubst subst) = UnsafeMakeSubst $
  unsafeCoerceEnvKeys $ subst <> unsafeCoerceNamespace v @> Rename (unsafeCoerceBindingTy v')

nameHint :: Name s n -> NameHint
nameHint (UnsafeMakeName (RawName s _)) = s

rawName :: Name s n -> RawName
rawName (UnsafeMakeName v) = v

freeNames :: HasNames e => e n -> Scope n
freeNames = freeNames' mempty

type BoundNames n = Scope n
type FreeNames  n = Scope n

class HasNames e where
  freeNames' :: BoundNames n -> e n -> FreeNames n

class BindsNames b where
  freeAndBoundNames :: BoundNames n -> b n i -> (FreeNames n, BoundNames i)

class MaySubstAndRename d b where
  substAndRename :: Scope n -> Subst d i n -> b i h
     -> (forall n'. Scope n' -> Subst d h n' -> b n n' -> a) -> a

class MaySubst d e where
  applySubst' :: Scope n -> Subst d i n -> e i -> e n

instance HasNames (Name s) where
  freeNames' scope v | v `isin` scope = mempty
                     | otherwise      = v @> ()

instance HasNames s => BindsNames (Binder s) where
  freeAndBoundNames = undefined

instance (BindsNames binder, HasNames body)
         => HasNames (Abs binder body) where
  freeNames' boundNames (Abs binder body) = let
    (free, boundNames') = freeAndBoundNames boundNames binder
    free' = freeNames' boundNames' body
    in free <> unsafeCoerceEnvKeys free'

instance MaySubst d s => MaySubstAndRename d (Binder s) where
  substAndRename _ _ _ _ = undefined
  -- substAndRename scope subst binder action = case binder of
  --   UnsafeMakeBinder v ann -> let
  --     ann' = applySubst' scope subst ann
  --     UnsafeMakeSubst substEnv = subst
  -- withFreshNameFromScope scope \scope' v' ->
  --     in withFreshName ann' \v' -> let
  --          newSubst = v @> Rename (unsafeCoerceBindingTy v')
  --          b' = UnsafeMakeBinder v' ann'
  --          subst' = UnsafeMakeSubst (unsafeCoerceEnvKeys substEnv <> newSubst)
  --          in action subst' b'

instance (MaySubstAndRename d binder, MaySubst d body)
         => MaySubst d (Abs binder body) where
  applySubst' scope subst (Abs binder body) =
    substAndRename scope subst binder \scope' subst' binder' ->
       Abs binder' $ applySubst' scope' subst' body

class Monad m => NameReader n m | m -> n where
  -- XXX: don't try to smuggle out some names in `a`!
  withFreshName :: NameHint -> s n -> (Binder s n n -> Name s n -> m a) -> m a
  lookupName :: Name s n -> m (s n)
  getScope :: m (Scope n)

genFreshRaw :: NameHint -> Scope n -> RawName
genFreshRaw tag (Env m) = RawName tag nextNum
  where nextNum = case M.lookupLT (RawName tag maxBound) m of
                    Just (RawName tag' i, ()) | tag' == tag -> i + 1
                    _ -> 0

unsafeCoerceNamespace :: Name s n -> Name s n'
unsafeCoerceNamespace = undefined

unsafeCoerceBindingTy :: Name s n -> Name s' n
unsafeCoerceBindingTy = undefined

unsafeCoerceNames :: HasNames e => e i -> e o
unsafeCoerceNames = undefined

unsafeCoerceEnvKeys :: Env n a -> Env n' a
unsafeCoerceEnvKeys = undefined

-- === convenience layer (uses safe API only) ===

data Abs (binder :: * -> * -> *) (body :: * -> *) (n :: *) where
  Abs :: binder n i -> body i -> Abs binder body n

data AnnBinder (s :: * -> *) (ann :: * -> *) (n :: *) (i :: *) =
  (:>) (Binder s n i) (ann n)
  deriving (Show, Generic, Generic1)

asDeferred :: e n -> DeferredSubst d e n
asDeferred x = Defer idSubst x

forceSubst :: (NameReader n m, MaySubst d e) => DeferredSubst d e n -> m (e n)
forceSubst (Defer subst expr) = applySubst subst expr

type NameHint = NameStr

data Nest (binders :: * -> * -> * ) (n :: *) (i :: *) where
 Nest  :: binders n h -> Nest binders h i -> Nest binders n i
 Empty ::                                    Nest binders n n

instance MaySubstAndRename d binders => MaySubstAndRename d (Nest binders) where
  substAndRename _ _ _ _ = undefined
  -- substAndRename subst nest action = case nest of
  --   Nest b rest ->
  --     substAndRename subst b \subst' b' ->
  --       substAndRename subst' rest \subst'' rest' ->
  --         action subst'' $ Nest b' rest'
  --   Empty -> action subst Empty

data NaryAbs s e n = UnsafeMakeNaryAbs [Maybe (Name s n)] (e n)
                     deriving (Show, Generic)

-- === name-value mappings ===

newtype Env n a = Env (M.Map RawName a)
        deriving (Show, Generic, Functor, Foldable, Traversable)
type Scope n = Env n ()

envLookup :: Name s n -> Env n a -> Maybe a
envLookup v (Env m) = M.lookup (rawName v) m

infixr 7 @>
(@>) :: Name s n -> a -> Env n a
v @> x = Env $ M.singleton (rawName v) x

isin :: Name s n -> Env n a -> Bool
isin v env = case envLookup v env of
  Just _  -> True
  Nothing -> False

-- -- === instances ===

-- instance Pretty (Name n) where pretty = prettyH
-- instance PrettyH Name    where
--   prettyH = undefined

instance Semigroup (Env n a) where
  Env m <> Env m' = Env (m' <> m)

instance Monoid (Env n a) where
  mempty = Env mempty
  mappend = (<>)

-- instance (HasNames   e1, HasNames   e2) => HasNames   (PairH e1 e2)
-- instance (AlphaEq    e1, AlphaEq    e2) => AlphaEq    (PairH e1 e2)
-- instance (MaySubst b e1, MaySubst b e2) => MaySubst b (PairH e1 e2)

-- instance HasNames UnitH
-- instance AlphaEq  UnitH
-- instance FromName b => MaySubst b UnitH

-- instance HasNames      SourceNameSubst
-- instance AlphaEq       SourceNameSubst
-- instance MaySubst Name SourceNameSubst

-- instance (Traversable f, HasNames   e) => HasNames   (H f e)
-- instance (Traversable f, AlphaEq    e) => AlphaEq    (H f e)
-- instance (Traversable f, MaySubst b e) => MaySubst b (H f e)

instance Store RawName
instance Store (Name s n)
-- instance Store (e n) => Store (Abs s e n)
instance Store (e n) => Store (NaryAbs s e n)
instance Store a => Store (Env n a)
instance Store (s n) => Store (Binder s n i) --

instance Show (Binder s n i) where
  show = undefined

instance Generic (Binder s n i) where
  to = undefined
  from = undefined

instance
  (forall i. Store (b n i), Store (e n)) => Store (Abs b e n) where
  size = undefined
  poke = undefined
  peek = undefined

deriving instance
  ((forall i. Show (binders n i)), (forall i. Show (body i)))
  => Show (Abs binders body n)

deriving instance (forall i i'. Show (binders i i')) => Show (Nest binders n i)

instance (forall i i'. Store (binders i i')) => Store (Nest binders n i) where
  size = undefined
  poke = undefined
  peek = undefined

-- deriving instance ((forall i. Generic (binders n i)), (forall i. Store
--                    (binders n i))) => Store (Nest binders n i)

-- instance (HasNames ann, HasNames (abs UnitH), HasNames body) => HasNames (Nest ann abs body) where
--   freeNames' = undefined

-- instance (AlphaEq ann, AlphaEq (abs UnitH), AlphaEq body) => AlphaEq (Nest ann abs body) where
--   alphaEq' = undefined

-- instance (MaySubst b ann, MaySubst b (abs UnitH), MaySubst b body) => MaySubst b (Nest ann abs body) where
--   applySubst' = undefined

-- -- === generic instances ===

-- class HasNamesG e where
--   freeNamesG :: Scope n -> e n -> Scope n
-- instance HasNamesG U1 where
--   freeNamesG _ _ = mempty
-- instance HasNamesG V1 where
--   freeNamesG _ _ = error "not possible"
-- instance HasNamesG a => HasNamesG (M1 i c a) where
--   freeNamesG scope (M1 x) = freeNamesG scope x
-- instance HasNamesG (K1 i a) where
--   freeNamesG _ (K1 _) = mempty
-- instance HasNames e => HasNamesG (Rec1 e) where
--   freeNamesG scope (Rec1 x) = freeNames' scope x
-- instance (HasNamesG e1, HasNamesG e2) => HasNamesG (e1 :*: e2) where
--   freeNamesG scope (x :*: y) = freeNamesG scope x <> freeNamesG scope y
-- instance (HasNamesG e1, HasNamesG e2) => HasNamesG (e1 :+: e2) where
--   freeNamesG scope x = case x of
--     L1 x' -> freeNamesG scope x'
--     R1 x' -> freeNamesG scope x'
-- instance (Foldable f, HasNamesG g) => HasNamesG (f :.: g) where
--   freeNamesG scope (Comp1 xs) = foldMap (freeNamesG scope) xs


-- class MaySubstG b e where
--   applySubstG :: (Scope n, Subst b i n) -> e i -> e n
-- instance MaySubstG b U1 where
--   applySubstG _ U1 = U1
-- instance MaySubstG b V1 where
--   applySubstG _ _ = error "not possible"
-- instance MaySubstG b a => MaySubstG b (M1 i c a) where
--   applySubstG env (M1 x) = M1 $ applySubstG env x
-- instance MaySubstG b (K1 i a) where
--   applySubstG _ (K1 x) = K1 x
-- instance MaySubst b e => MaySubstG b (Rec1 e) where
--   applySubstG env (Rec1 x) = Rec1 $ applySubst' env x
-- instance (MaySubstG b e1, MaySubstG b e2) => MaySubstG b (e1 :*: e2) where
--   applySubstG env (x :*: y) =   applySubstG env x
--                                     :*: applySubstG env y
-- instance (MaySubstG b e1, MaySubstG b e2) => MaySubstG b (e1 :+: e2) where
--   applySubstG env x = case x of
--     L1 x' -> L1 $ applySubstG env x'
--     R1 x' -> R1 $ applySubstG env x'
-- instance (Foldable f, Functor f, MaySubstG b g) => MaySubstG b (f :.: g) where
--   applySubstG env (Comp1 xs) = Comp1 $ fmap (applySubstG env) xs


-- class AlphaEqG e where
--   alphaEqG :: (Scope n, NameSubst i1 n, NameSubst i2 n)
--            -> e i1 -> e i2 -> Bool
-- instance AlphaEqG U1 where
--   alphaEqG _ _ _ = True
-- instance AlphaEqG V1 where
--   alphaEqG _ _ _ = error "not possible"
-- instance AlphaEqG a => AlphaEqG (M1 i c a) where
--   alphaEqG ctx (M1 x1) (M1 x2) = alphaEqG ctx x1 x2
-- instance Eq a => AlphaEqG (K1 i a) where
--   alphaEqG ctx (K1 x1) (K1 x2) = x1 == x2
-- instance AlphaEq e => AlphaEqG (Rec1 e) where
--   alphaEqG (scope, s1, s2) (Rec1 x1) (Rec1 x2) =
--     alphaEq' scope (Defer s1 x1) (Defer s2 x2)
-- instance (AlphaEqG e1, AlphaEqG e2) => AlphaEqG (e1 :*: e2) where
--   alphaEqG ctx (x1 :*: y1) (x2 :*: y2) = alphaEqG ctx x1 x2 && alphaEqG ctx y1 y2
-- instance (AlphaEqG e1, AlphaEqG e2) => AlphaEqG (e1 :+: e2) where
--   alphaEqG ctx x1 x2 = case (x1, x2) of
--     (L1 y1, L1 y2) -> alphaEqG ctx y1 y2
--     (R1 y1, R1 y2) -> alphaEqG ctx y1 y2
--     _ -> False
-- -- not sure how to handle this case. Needs some sort of zippable class.
-- instance (Foldable f, AlphaEqG g) => AlphaEqG (f :.: g) where
--   alphaEqG = undefined -- ctx (Comp1 xs1) (Comp1 xs2) = undefined

