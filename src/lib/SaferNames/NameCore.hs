-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}

module SaferNames.NameCore (
  S (..), C (..), RawName, Name (..), withFresh, inject, injectNamesR, projectName,
  NameBinder (..), ScopeFrag (..), Scope, singletonScope, (<.>),
  EnvFrag (..), Env, singletonEnv, emptyEnv, envAsScope, lookupEnv, lookupEnvFrag,
  E, B, V, InjectableE (..), InjectableB (..), InjectableV,
  InjectionCoercion, Nest (..),
  unsafeCoerceE, unsafeCoerceB, getRawName, getNameColorRep, absurdNameFunction, fmapEnvFrag,
  toEnvPairs, fromEnvPairs, EnvPair (..), withNameColorRep, withSubscopeDistinct,
  GenericE (..), GenericB (..), WrapE (..), WrapB (..), EnvVal (..),
  NameColorRep (..), NameColor (..), EqNameColor (..), eqNameColorRep, tryAsColor,
  Distinct, DistinctEvidence (..), withDistinctEvidence, getDistinctEvidence,
  Ext, ExtEvidence (..), withExtEvidence', getExtEvidence, scopeFragToExtEvidence,
  NameHint (..)) where

import Prelude hiding (id, (.))
import Control.Category
import Data.Foldable (fold)
import Data.Text.Prettyprint.Doc  hiding (nest)
import Data.Kind (Type)
import Unsafe.Coerce
import qualified Data.Map  as M
import qualified Data.Set  as S
import Data.Store (Store (..))
import Data.String
import GHC.Generics (Generic (..))

import qualified Env as D

-- `S` is the kind of "scope parameters". It's only ever used as a phantom type.
-- It represents a list of names, given by the value of the singleton type
-- `Scope n` (`n::S`). Names are tagged with a scope parameter, and a name of
-- type `Name n` has an underlying raw name that must occur in the corresponding
-- `Scope n`. (A detail: `Scope n` actually only carries a *set* of names, not
-- a list, because that's all we need at runtime. But it's important to remember
-- that it conceptually represents a list. For example, a `Scope n` and a `NameSet
-- m` that happen to represent the same set of names can't necessarily be
-- considered equal.) Types of kind `S` are mostly created existentially through
-- rank-2 polymorphism, rather than using the constructors in the data
-- definition. For example: magicallyCreateFreshS :: (forall (n::S). a) -> a
-- magicallyCreateFreshS x = x -- where does `n` come from? magic!

-- We also have `:=>:` to represent differences between scopes with a common
-- prefix. A `Scope (n:=>:l)` means that
--   1. `Scope n` is a prefix of `Scope l`
--   2. `Scope (n:=>:l)` is the list of names by which `l` extends `n`.

--      x    y    z    x    w    x
--     \-----------------/\--------/
--              n           n:=>:l
--     \---------------------------/
--                    l

-- Note that `l` is not necessarily a *fresh* extension: in the example above, x
-- appears in `n:=>:l` even though it already appeared, twice, in `n`.
-- We have separate proof objects, `Ext n l` and `Distinct n` to provide
-- evidence of freshness.

-- There are also special scopes, `VoidS` and `UnitS`, representing the
-- empty list and a singleton list with a particular special name. These are
-- useful in the same way that the ordinary types `Void` and `()` are useful.

data S = (:=>:) S S
       | VoidS
       | UnsafeS

-- Name "color" ("type", "kind", etc. already taken)
data C =
    AtomNameC
  | DataDefNameC
  | TyConNameC
  | DataConNameC
  | ClassNameC
  | SuperclassNameC
  | MethodNameC

type E = S -> *       -- expression-y things, covariant in the S param
type B = S -> S -> *  -- binder-y things, covariant in the first param and
                      -- contravariant in the second. These are things like
                      -- `Binder n l` or `Decl n l`, that bind the names in
                      -- `ScopeFrag n l`, extending `n` to `l`. Their free
                      -- name are in `Scope n`. We sometimes call `n` the
                      -- "outside scope" and "l" the "inside scope".
type V = C -> E       -- value-y things that we might look up in an environment
                      -- with a `Name c n`, parameterized by the name's color.

newtype ScopeFrag (n::S) (l::S) = UnsafeMakeScope (S.Set RawName)
type Scope = ScopeFrag VoidS :: S -> *

instance Category ScopeFrag where
  id = UnsafeMakeScope mempty
  UnsafeMakeScope s2 . UnsafeMakeScope s1 = UnsafeMakeScope $ s1 <> s2

singletonScope :: NameBinder s i i' -> ScopeFrag i i'
singletonScope (UnsafeMakeBinder (UnsafeMakeName _ v)) =
  UnsafeMakeScope (S.singleton v)

absurdNameFunction :: Name v VoidS -> a
absurdNameFunction _ = error "Void names shouldn't exist"

-- TODO: we reuse the old `Name` to make use of the GlobalName name space while
-- we're using both the old and new systems together.
-- TODO: something like this instead:
--    type Tag = T.Text
--    data RawName = RawName Tag Int deriving (Show, Eq, Ord)
type RawName = D.Name

data Name (c::C)  -- Name color
          (n::S)  -- Scope parameter
  where UnsafeMakeName :: NameColorRep c -> RawName -> Name c n

data NameBinder (c::C)  -- name color
                (n::S)  -- scope above the binder
                (l::S)  -- scope under the binder (`l` for "local")
  = UnsafeMakeBinder { nameBinderName :: Name c l }

data NameHint = Hint RawName
              | NoHint

instance IsString NameHint where
  fromString s = Hint $ fromString s

withFresh :: forall n c a. Distinct n
          => NameHint -> NameColorRep c -> Scope n
          -> (forall l. (Ext n l, Distinct l) => NameBinder c n l -> a) -> a
withFresh hint rep (UnsafeMakeScope scope) cont =
  withDistinctEvidence (FabricateDistinctEvidence :: DistinctEvidence UnsafeS) $
    withExtEvidence' (FabricateExtEvidence :: ExtEvidence n UnsafeS) $
      cont $ UnsafeMakeBinder freshName
  where
    freshName :: Name c UnsafeS
    freshName = UnsafeMakeName rep $ freshRawName (D.nameTag rawNameHint) scope

    rawNameHint :: RawName
    rawNameHint = case hint of
      Hint v -> v
      NoHint -> "v"

freshRawName :: D.Tag -> S.Set RawName -> RawName
freshRawName tag usedNames = D.Name D.GenName tag nextNum
  where
    nextNum = case S.lookupLT (D.Name D.GenName tag bigInt) usedNames of
                Just (D.Name D.GenName tag' i)
                  | tag' /= tag -> 0
                  | i < bigInt  -> i + 1
                  | otherwise   -> error "Ran out of numbers!"
                _ -> 0
    bigInt = (10::Int) ^ (9::Int)  -- TODO: consider a real sentinel value

projectName :: ScopeFrag n l -> Name s l -> Either (Name s n) (Name s (n:=>:l))
projectName (UnsafeMakeScope scope) (UnsafeMakeName rep rawName)
  | S.member rawName scope = Right $ UnsafeMakeName rep rawName
  | otherwise              = Left  $ UnsafeMakeName rep rawName

-- proves that the names in n are distinct
class Distinct (n::S)
-- data version of Distinct
data DistinctEvidence (n::S) = FabricateDistinctEvidence

instance Distinct VoidS

getDistinctEvidence :: Distinct n => DistinctEvidence n
getDistinctEvidence = FabricateDistinctEvidence

withDistinctEvidence :: forall n a. DistinctEvidence n -> (Distinct n => a) -> a
withDistinctEvidence _ cont = fromWrapWithDistinct
 ( unsafeCoerce ( WrapWithDistinct cont :: WrapWithDistinct n     a
                                      ) :: WrapWithDistinct VoidS a)

newtype WrapWithDistinct n r =
  WrapWithDistinct { fromWrapWithDistinct :: Distinct n => r }


withSubscopeDistinct :: forall n l a.
                        Distinct l
                     => ExtEvidence n l -> ((Ext n l, Distinct n) => a) -> a
withSubscopeDistinct ext cont =
  withExtEvidence' ext $
    withDistinctEvidence (FabricateDistinctEvidence :: DistinctEvidence n) $
      cont

-- useful for printing etc.
getRawName :: Name c n -> RawName
getRawName (UnsafeMakeName _ rawName) = rawName

getNameColorRep :: Name c n -> NameColorRep c
getNameColorRep (UnsafeMakeName rep _) = rep

-- === variant of Generic suited for E-kind and B-kind things ===

class GenericE (e::E) where
  type RepE e :: S -> Type
  fromE :: e n -> RepE e n
  toE   :: RepE e n -> e n

class GenericB (b::B) where
  type RepB b :: S -> S -> Type
  fromB :: b n l -> RepB b n l
  toB   :: RepB b n l -> b n l

newtype WrapE (e::E) (n::S) = WrapE { fromWrapE :: e n }
newtype WrapB (b::B) (n::S) (l::S) = WrapB { fromWrapB :: b n l}

instance (GenericE e, Generic (RepE e n)) => Generic (WrapE e n) where
  type Rep (WrapE e n) = Rep (RepE e n)
  from e = from $ fromE $ fromWrapE e
  to e = WrapE $ toE $ to e

instance (GenericB b, Generic (RepB b n l)) => Generic (WrapB b n l) where
  type Rep (WrapB b n l) = Rep (RepB b n l)
  from b = from $ fromB $ fromWrapB b
  to b = WrapB $ toB $ to b

-- === injections ===

-- Note [Injections]

-- `Ext n l` is proof that `l` extends `n` (not necessarily freshly:
-- `Distinct l` is still needed to further prove that). Unlike `ScopeFrag`
-- (which is also proof) it doesn't actually carry any data, so we can unsafely
-- create one from nothing when we need to.
class Ext (n::S) (l::S)

instance Ext (n::S) (n::S)

getExtEvidence :: Ext n l => ExtEvidence n l
getExtEvidence = FabricateExtEvidence

-- We give this one a ' because the more general one defined in Name is the
-- version we usually want to use.
withExtEvidence' :: forall n l a. ExtEvidence n l -> (Ext n l => a) -> a
withExtEvidence' _ cont = fromWrapWithExt
 ( unsafeCoerce ( WrapWithExt cont :: WrapWithExt n     l     a
                                 ) :: WrapWithExt VoidS VoidS a)

newtype WrapWithExt n l r =
  WrapWithExt { fromWrapWithExt :: Ext n l => r }

data ExtEvidence (n::S) (l::S) = FabricateExtEvidence

instance Category ExtEvidence where
  id = FabricateExtEvidence
  -- Unfortunately, we can't write the class version of this transitivity axiom
  -- because the intermediate type would be ambiguous.
  FabricateExtEvidence . FabricateExtEvidence = FabricateExtEvidence

scopeFragToExtEvidence :: ScopeFrag n l -> ExtEvidence n l
scopeFragToExtEvidence _ = FabricateExtEvidence

inject :: (InjectableE e, Distinct l, Ext n l) => e n -> e l
inject x = unsafeCoerceE x

injectNamesR :: InjectableE e => e (n:=>:l) -> e l
injectNamesR = unsafeCoerceE

class InjectableE (e::E) where
  injectionProofE :: InjectionCoercion n l -> e n -> e l

  default injectionProofE :: (GenericE e, InjectableE (RepE e))
                          => InjectionCoercion n l -> e n -> e l
  injectionProofE free x = toE $ injectionProofE free $ fromE x

class InjectableB (b::B) where
  injectionProofB :: InjectionCoercion n n' -> b n l
                  -> (forall l'. InjectionCoercion l l' -> b n' l' -> a)
                  -> a
  default injectionProofB :: (GenericB b, InjectableB (RepB b))
                          => InjectionCoercion n n' -> b n l
                          -> (forall l'. InjectionCoercion l l' -> b n' l' -> a)
                          -> a
  injectionProofB fresh b cont =
    injectionProofB fresh (fromB b) \fresh' b' -> cont fresh' $ toB b'

-- previously we just had the alias
-- `type InjectableV v = forall c. NameColor c => InjectableE (v c)`
-- but GHC seemed to have trouble figuring out superclasses etc. so
-- we're making it an explicit class instead
class (forall c. NameColor c => InjectableE (v c))
      => InjectableV (v::V)

data InjectionCoercion (n::S) (l::S) where
  InjectionCoercion :: (forall s. Name s n -> Name s l) -> InjectionCoercion n l

instance InjectableV Name
instance InjectableE (Name c) where
  injectionProofE (InjectionCoercion f) name = f name

-- This is the unsafely-implemented base case. Here's why it's valid. Let's say
-- the name of the binder is x. The scopes are related like this:
--   l  = n  ++ [x]
--   l' = n' ++ [x]
-- We're given an injection from n to n' and we want to produce an injection
-- from l to l'. Any name in l must be either:
--   (1) x itself, in which case it's also in l'
--   (2) in n, in which case it can be injected to n'. The only issue would be
--       if it were shadowed by x, but it can't be because then we'd be in case (1).
instance InjectableB (NameBinder s) where
  injectionProofB  _ (UnsafeMakeBinder b) cont =
    cont (InjectionCoercion unsafeCoerceE) (UnsafeMakeBinder b)

instance InjectableE DistinctEvidence where
  injectionProofE _ _ = FabricateDistinctEvidence

instance InjectableE (ExtEvidence n) where
  injectionProofE _ _ = FabricateExtEvidence

-- === environments ===

-- The `Env` type is purely an optimization. We could do everything using
-- the safe API by defining:
--    type Env v i o = (ScopeFrag i, forall s. Name s i -> v s o)
-- Instead, we use this unsafely-implemented data type for efficiency, to avoid
-- long chains of case analyses as we extend environments one name at a time.

data EnvFrag
  (v ::V)  -- env payload, as a function of the name's color
  (i ::S)  -- starting scope parameter for names we can look up in this env
  (i'::S)  -- ending   scope parameter for names we can look up in this env
  (o ::S)  -- scope parameter for the values stored in the env
  = UnsafeMakeEnv
      (M.Map RawName (EnvVal v o))
      (S.Set RawName)  -- cached name set as an optimization, to avoid the O(n)
                       -- map-to-set conversion
  deriving (Generic)
deriving instance (forall c. Show (v c o)) => Show (EnvFrag v i i' o)

type Env v i o = EnvFrag v VoidS i o

lookupEnv :: Env v i o -> Name s i -> v s o
lookupEnv (UnsafeMakeEnv m _) (UnsafeMakeName rep rawName) =
  case M.lookup rawName m of
    Nothing -> error "Env lookup failed (this should never happen)"
    Just d -> fromEnvVal rep d

lookupEnvFrag :: EnvFrag v i i' o -> Name s (i:=>:i') -> v s o
lookupEnvFrag (UnsafeMakeEnv m _) (UnsafeMakeName rep rawName) =
  case M.lookup rawName m of
    Nothing -> error "Env lookup failed (this should never happen)"
    Just d -> fromEnvVal rep d

emptyEnv :: EnvFrag v i i o
emptyEnv = UnsafeMakeEnv mempty mempty

singletonEnv :: NameBinder c i i' -> v c o -> EnvFrag v i i' o
singletonEnv (UnsafeMakeBinder (UnsafeMakeName rep name)) x =
  UnsafeMakeEnv (M.singleton name $ EnvVal rep x) (S.singleton name)

infixl 1 <.>
(<.>) :: EnvFrag v i1 i2 o -> EnvFrag v i2 i3 o -> EnvFrag v i1 i3 o
(<.>) (UnsafeMakeEnv m1 s1) (UnsafeMakeEnv m2 s2) =
  UnsafeMakeEnv (m2 <> m1) (s2 <> s1)  -- flipped because Data.Map uses a left-biased `<>`

fmapEnvFrag :: InjectableV v
            => (forall c. NameColor c => Name c (i:=>:i') -> v c o -> v' c o')
            -> EnvFrag v i i' o -> EnvFrag v' i i' o'
fmapEnvFrag f (UnsafeMakeEnv m s) = UnsafeMakeEnv m' s
  where m' = flip M.mapWithKey m \k (EnvVal rep val) ->
               withNameColorRep rep $
                 EnvVal rep $ f (UnsafeMakeName rep k) val

envAsScope :: EnvFrag v i i' o -> ScopeFrag i i'
envAsScope (UnsafeMakeEnv _ s) = UnsafeMakeScope s

-- === iterating through env pairs ===

data EnvPair (v::V) (o::S) (i::S) (i'::S) where
  EnvPair :: NameColor c => NameBinder c i i' -> v c o -> EnvPair v o i i'

toEnvPairs :: forall v i i' o . EnvFrag v i i' o -> Nest (EnvPair v o) i i'
toEnvPairs (UnsafeMakeEnv m _) =
  go $ M.elems $ M.mapWithKey mkPair m
  where
    mkPair :: RawName -> EnvVal v o -> EnvPair v o UnsafeS UnsafeS
    mkPair rawName (EnvVal rep v) =
      withNameColorRep rep $
        EnvPair (UnsafeMakeBinder $ UnsafeMakeName rep rawName) v

    go :: [EnvPair v o UnsafeS UnsafeS] -> Nest (EnvPair v o) i i'
    go [] = unsafeCoerceB Empty
    go (EnvPair b val : rest) = Nest (EnvPair (unsafeCoerceB b) val) $ go rest

fromEnvPairs :: Nest (EnvPair v o) i i' -> EnvFrag v i i' o
fromEnvPairs Empty = emptyEnv
fromEnvPairs (Nest (EnvPair b v) rest) =
  singletonEnv b v <.> fromEnvPairs rest

data Nest (binder::B) (n::S) (l::S) where
  Nest  :: binder n h -> Nest binder h l -> Nest binder n l
  Empty ::                                  Nest binder n n

instance Category (Nest b) where
  id = Empty
  nest' . nest = case nest of
    Empty -> nest'
    Nest b rest -> Nest b $ rest >>> nest'

-- === handling the dynamic/heterogeneous stuff for Env ===

data EnvVal (v::V) (n::S) where
  EnvVal :: NameColorRep c -> v c n -> EnvVal v n

deriving instance (forall c. Show (v c n)) => Show (EnvVal v n)

fromEnvVal ::  NameColorRep c -> EnvVal v o -> v c o
fromEnvVal rep (EnvVal rep' val) =
  case eqNameColorRep rep rep' of
    Just EqNameColor -> val
    _ -> error "type mismatch"

data NameColorRep (c::C) where
  AtomNameRep       :: NameColorRep AtomNameC
  DataDefNameRep    :: NameColorRep DataDefNameC
  TyConNameRep      :: NameColorRep TyConNameC
  DataConNameRep    :: NameColorRep DataConNameC
  ClassNameRep      :: NameColorRep ClassNameC
  SuperclassNameRep :: NameColorRep SuperclassNameC
  MethodNameRep     :: NameColorRep MethodNameC

deriving instance Show (NameColorRep c)
deriving instance Eq   (NameColorRep c)

data DynamicColor
   atomNameVal
   dataDefNameVal
   tyConNameVal
   dataConNameVal
   classNameVal
   superclassNameVal
   methodNameVal
 =
   AtomNameVal       atomNameVal
 | DataDefNameVal    dataDefNameVal
 | TyConNameVal      tyConNameVal
 | DataConNameVal    dataConNameVal
 | ClassNameVal      classNameVal
 | SuperclassNameVal superclassNameVal
 | MethodNameVal     methodNameVal
   deriving (Show, Generic)

data EqNameColor (c1::C) (c2::C) where
  EqNameColor :: EqNameColor c c

eqNameColorRep :: NameColorRep c1 -> NameColorRep c2 -> Maybe (EqNameColor c1 c2)
eqNameColorRep rep1 rep2 = case (rep1, rep2) of
  (AtomNameRep      , AtomNameRep      ) -> Just EqNameColor
  (DataDefNameRep   , DataDefNameRep   ) -> Just EqNameColor
  (TyConNameRep     , TyConNameRep     ) -> Just EqNameColor
  (DataConNameRep   , DataConNameRep   ) -> Just EqNameColor
  (ClassNameRep     , ClassNameRep     ) -> Just EqNameColor
  (SuperclassNameRep, SuperclassNameRep) -> Just EqNameColor
  (MethodNameRep    , MethodNameRep    ) -> Just EqNameColor
  _ -> Nothing

-- gets the NameColorRep implicitly, like Typeable
class NameColor c where nameColorRep :: NameColorRep c
instance NameColor AtomNameC       where nameColorRep = AtomNameRep
instance NameColor DataDefNameC    where nameColorRep = DataDefNameRep
instance NameColor TyConNameC      where nameColorRep = TyConNameRep
instance NameColor DataConNameC    where nameColorRep = DataConNameRep
instance NameColor ClassNameC      where nameColorRep = ClassNameRep
instance NameColor SuperclassNameC where nameColorRep = SuperclassNameRep
instance NameColor MethodNameC     where nameColorRep = MethodNameRep

tryAsColor :: forall (v::V) (c1::C) (c2::C) (n::S).
              (NameColor c1, NameColor c2) => v c1 n -> Maybe (v c2 n)
tryAsColor x = case eqNameColorRep (nameColorRep :: NameColorRep c1)
                                   (nameColorRep :: NameColorRep c2) of
  Just EqNameColor -> Just x
  Nothing -> Nothing

withNameColorRep :: NameColorRep c -> (NameColor c => a) -> a
withNameColorRep rep cont = case rep of
  AtomNameRep       -> cont
  DataDefNameRep    -> cont
  TyConNameRep      -> cont
  DataConNameRep    -> cont
  ClassNameRep      -> cont
  SuperclassNameRep -> cont
  MethodNameRep     -> cont

-- === instances ===

instance Show (NameBinder s n l) where
  show (UnsafeMakeBinder v) = show v

instance Pretty (Name s n) where
  pretty (UnsafeMakeName _ name) = pretty name

instance Pretty (NameBinder s n l) where
  pretty (UnsafeMakeBinder name) = pretty name

instance (forall c. Pretty (v c n)) => Pretty (EnvVal v n) where
  pretty (EnvVal _ val) = pretty val

instance Pretty (NameColorRep c) where
  pretty rep = pretty (show rep)

instance Eq (Name s n) where
  UnsafeMakeName _ rawName == UnsafeMakeName _ rawName' = rawName == rawName'

instance Ord (Name s n) where
  compare (UnsafeMakeName _ name) (UnsafeMakeName _ name') = compare name name'

instance Show (Name s n) where
  show (UnsafeMakeName _ rawName) = show rawName

instance InjectableV v => InjectableE (EnvFrag v i i') where
  injectionProofE fresh m = fmapEnvFrag (\(UnsafeMakeName _ _) v -> injectionProofE fresh v) m

-- === unsafe coercions ===

-- Sometimes we need to break the glass. But at least these are slightly safer
-- than raw `unsafeCoerce` because at the checks the kind

unsafeCoerceE :: forall (e::E) i o . e i -> e o
unsafeCoerceE = unsafeCoerce

unsafeCoerceB :: forall (b::B) n l n' l' . b n l -> b n' l'
unsafeCoerceB = unsafeCoerce

-- === instances ===

instance (forall n' l'. Show (b n' l')) => Show (Nest b n l) where
  show Empty = ""
  show (Nest b rest) = "(Nest " <> show b <> " in " <> show rest <> ")"

instance (forall (n'::S) (l'::S). Pretty (b n' l')) => Pretty (Nest b n l) where
  pretty Empty = ""
  pretty (Nest b rest) = "(Nest " <> pretty b <> " in " <> pretty rest <> ")"

instance InjectableB b => InjectableB (Nest b) where
  injectionProofB fresh Empty cont = cont fresh Empty
  injectionProofB fresh (Nest b rest) cont =
    injectionProofB fresh b \fresh' b' ->
      injectionProofB fresh' rest \fresh'' rest' ->
        cont fresh'' (Nest b' rest')

instance (forall c n. Pretty (v c n)) => Pretty (EnvFrag v i i' o) where
  pretty (UnsafeMakeEnv m _) =
    fold [ pretty v <+> "@>" <+> pretty x <> hardline
         | (v, EnvVal _ x) <- M.toList m ]

instance (Generic (b UnsafeS UnsafeS)) => Generic (Nest b n l) where
  type Rep (Nest b n l) = Rep [b UnsafeS UnsafeS]
  from = from . listFromNest
    where
      listFromNest :: Nest b n' l' -> [b UnsafeS UnsafeS]
      listFromNest nest = case nest of
        Empty -> []
        Nest b rest -> unsafeCoerceB b : listFromNest rest

  to = listToNest . to
    where
      listToNest :: [b UnsafeS UnsafeS] -> Nest b n l
      listToNest l = case l of
        [] -> unsafeCoerceB Empty
        b:rest -> Nest (unsafeCoerceB b) $ listToNest rest

instance NameColor c => Generic (NameColorRep c) where
  type Rep (NameColorRep c) = Rep ()
  from _ = from ()
  to   _ = nameColorRep

instance NameColor c => Generic (Name c n) where
  type Rep (Name c n) = Rep RawName
  from (UnsafeMakeName _ rawName) = from rawName
  to name = UnsafeMakeName nameColorRep rawName
    where rawName = to name

instance NameColor c => Generic (NameBinder c n l) where
  type Rep (NameBinder c n l) = Rep (Name c l)
  from (UnsafeMakeBinder v) = from v
  to v = UnsafeMakeBinder $ to v

instance (forall c. NameColor c => Store (v c n)) => Generic (EnvVal v n) where
  type Rep (EnvVal v n) = Rep (DynamicColor (v AtomNameC       n)
                                            (v DataDefNameC    n)
                                            (v TyConNameC      n)
                                            (v DataConNameC    n)
                                            (v ClassNameC      n)
                                            (v SuperclassNameC n)
                                            (v MethodNameC     n))
  from (EnvVal rep val) = case rep of
    AtomNameRep       -> from $ AtomNameVal       val
    DataDefNameRep    -> from $ DataDefNameVal    val
    TyConNameRep      -> from $ TyConNameVal      val
    DataConNameRep    -> from $ DataConNameVal    val
    ClassNameRep      -> from $ ClassNameVal      val
    SuperclassNameRep -> from $ SuperclassNameVal val
    MethodNameRep     -> from $ MethodNameVal     val

  to genRep = case to genRep of
    (AtomNameVal       val) -> EnvVal AtomNameRep       val
    (DataDefNameVal    val) -> EnvVal DataDefNameRep    val
    (TyConNameVal      val) -> EnvVal TyConNameRep      val
    (DataConNameVal    val) -> EnvVal DataConNameRep    val
    (ClassNameVal      val) -> EnvVal ClassNameRep      val
    (SuperclassNameVal val) -> EnvVal SuperclassNameRep val
    (MethodNameVal     val) -> EnvVal MethodNameRep     val

instance (forall c. NameColor c => Store (v c n)) => Store (EnvVal v n)
instance InjectableV v => InjectableE (EnvVal v) where
  injectionProofE = undefined

instance ( forall c. NameColor c => Store (v c o)
         , forall c. NameColor c => Generic (v c o))
         => Store (EnvFrag v i i' o) where

instance NameColor c => Store (Name c n)
instance NameColor c => Store (NameBinder c n l)
instance NameColor c => Store (NameColorRep c)
instance ( Store   (b UnsafeS UnsafeS)
         , Generic (b UnsafeS UnsafeS) ) => Store (Nest b n l)

instance
  ( Store a0, Store a1, Store a2, Store a3
  , Store a4, Store a5, Store a6)
  => Store (DynamicColor a0 a1 a2 a3 a4 a5 a6)

-- === notes ===

{-

Note [Injections]

When we inline an expression, we lift it into a larger (deeper) scope,
containing more in-scope variables. For example, when we turn this:

  let foo = \x. \y. x + y + z
  in \y. foo y

into this:

  \y. (\x. \y. x + y + z) y

The expression `\x. x + z + y`, initially in the scope `[z]`, gets injected into
the scope `[z, y]`. For expression-like things, the injection is valid if we
know that (1) that the new scope contains distinct names, and (2) it extends the
old scope. These are the `Distinct l` and `Ext n l` conditions in `inject`.
Note that the expression may end up with internal binders shadowing the new vars
in scope, shadows, like the inner `y` above, and that's fine.

But not everything with an expression-like kind `E` (`S -> *`) is injectable.
For example, a type like `Name n -> Bool` can't be coerced to a `Name l -> Bool`
when `l` is an extension of `n`. It's the usual covariance/contravariance issue
with subtyping. So we have a further type class, `InjectableE`, which asserts
that a type is covariant in the name space parameter. To prove it, we implement the
`injectionProofE` method (which is never actually called at runtime), which
must produce an injection `e n -> e l` given an injection
`forall s. Name s n -> Name s l`.

The typeclass should obey `injectionProofE (InjectionCoercion id) = id`
Otherwise you could just give an `injectableE` instance for `Name n -> Bool`
as `injectionProofE _ _ = const True`.

-}
