-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleInstances #-}

module SaferNames.NameCore (
  S (..), RawName, Name (..), withFresh, injectNames, projectName,
  NameBinder (..),
  NameSet (..), singletonNameSet, emptyNameSetFrag, emptyNameSet, extendNameSet, concatNameSets,
  NameMap (..), singletonNameMap, emptyNameMap, nameMapNames,
  lookupNameMap, extendNameMap,  concatNameMaps,
  Distinct, E, B, InjectableE (..), InjectableB (..), InjectableV, ObservablyFresh,
  unsafeCoerceE, unsafeCoerceB, withNameClasses, getRawName) where

import Prelude hiding (id, (.))
import Data.Text.Prettyprint.Doc  hiding (nest)
import Data.Type.Equality
import Type.Reflection
import Unsafe.Coerce
import qualified Data.Map  as M
import qualified Data.Set  as S
import GHC.Exts (Constraint)

import qualified Env as D

-- `S` is the kind of "scope parameters". It's only ever used as a phantom type.
-- It represents a list of names, given by the value of the singleton type
-- `NameSet n` (`n::S`). Names are tagged with a scope parameter, and a name of
-- type `Name n` has an underlying raw name that must occur in the corresponding
-- `Scope n`. (A detail: `NameSet n` actually only carries a *set* of names, not
-- a list, because that's all we need at runtime. But it's important to remember
-- that it conceptually represents a list. For example, a `NameSet n` and a `NameSet
-- m` that happen to represent the same set of names can't necessarily be
-- considered equal.) Types of kind `S` are mostly created existentially through
-- rank-2 polymorphism, rather than using the constructors in the data
-- definition. For example: magicallyCreateFreshS :: (forall (n::S). a) -> a
-- magicallyCreateFreshS x = x -- where does `n` come from? magic!

-- We also have `:=>:` to represent differences between scopes with a common
-- prefix. A `NameSet (n:=>:l)` means that
--   1. `NameSet n` is a prefix of `NameSet l`
--   2. `NameSet (n:=>:l)` is the list of names by which `l` extends `n`.

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
       | UnsafeMakeS
       | UnsafeMakeDistinctS

type E = S -> *       -- expression-y things, covariant in the S param
type B = S -> S -> *  -- binder-y things, covariant in the first param and
                      -- contravariant in the second. These are things like
                      -- `Binder n l` or `Decl n l`, that bind the names in
                      -- `NameSet (n:=>:l)`, extending `n` to `l`. Their free
                      -- name are in `NameSet n`. We sometimes call `n` the
                      -- "outside scope" and "l" the "inside scope".

newtype NameSet (n::S) = UnsafeMakeNameSet (S.Set RawName)

emptyNameSetFrag :: NameSet (n:=>:n)
emptyNameSetFrag = UnsafeMakeNameSet mempty

emptyNameSet :: NameSet VoidS
emptyNameSet = UnsafeMakeNameSet mempty

singletonNameSet :: NameBinder s i i' -> NameSet (i:=>:i')
singletonNameSet (UnsafeMakeBinder (UnsafeMakeName v)) =
  UnsafeMakeNameSet (S.singleton v)

extendNameSet :: NameSet n -> NameSet (n:=>:l) -> NameSet l
extendNameSet (UnsafeMakeNameSet s1) (UnsafeMakeNameSet s2) =
  UnsafeMakeNameSet (s1 <> s2)

concatNameSets :: NameSet (n1:=>:n2) -> NameSet (n2:=>:n3) -> NameSet (n1:=>:n3)
concatNameSets (UnsafeMakeNameSet s1) (UnsafeMakeNameSet s2) =
  UnsafeMakeNameSet (s1 <> s2)

-- TODO: we reuse the old `Name` to make use of the GlobalName name space while
-- we're using both the old and new systems together.
-- TODO: something like this instead:
--    type Tag = T.Text
--    data RawName = RawName Tag Int deriving (Show, Eq, Ord)
type RawName = D.Name

data Name
  (s::E)  -- Static information associated with the name. An example is
          -- BinderInfo in Core, which includes type information, the flavor of
          -- arrow if it's a lambda-bound variable, and the actual rhs of the
          -- let binding if it's let-bound. These things may contain free
          -- variables themselves, so `s` takes a scope parameter.
  (n::S)  -- Scope parameter
  where
    UnsafeMakeName :: (InjectableE s, Typeable s) => RawName -> Name s n

data NameBinder (s::E)  -- static information for the name this binds (note
                        -- that `NameBinder` doesn't actually carry this data)
                (n::S)  -- scope above the binder
                (l::S)  -- scope under the binder (`l` for "local")
  = UnsafeMakeBinder { nameBinderName :: Name s l }

withFresh :: InjectableE s => Typeable s => Distinct n => NameSet n
          -> (forall l. Distinct l => NameBinder s n l -> a) -> a
withFresh (UnsafeMakeNameSet scope) cont =
  cont @UnsafeMakeDistinctS $ UnsafeMakeBinder freshName
  where freshName = UnsafeMakeName $ freshRawName "v" scope

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

projectName :: NameSet (n:=>:l) -> Name s l -> Either (Name s n) (Name s (n:=>:l))
projectName (UnsafeMakeNameSet scope) (UnsafeMakeName rawName)
  | S.member rawName scope = Right $ UnsafeMakeName rawName
  | otherwise              = Left  $ UnsafeMakeName rawName

-- proves that the names in n are distinct
class Distinct (n::S)
instance Distinct VoidS
instance Distinct UnsafeMakeDistinctS

withNameClasses :: Name s n -> ((InjectableE s, Typeable s) => r) -> r
withNameClasses (UnsafeMakeName _) cont = cont

-- useful for printing etc.
getRawName :: Name s n -> RawName
getRawName (UnsafeMakeName rawName) = rawName

-- === injections ===

-- When we inline an expression, we lift it into a larger (deeper) scope,
-- containing more in-scope variables. For example, when we turn this:
--   let foo = \x. x + z
--   in \y. foo y
-- into this:
--   \y. (\x. x + z) y
-- The expression `\x. x + z`, initially in the scope `[z]`, gets injected into
-- the scope `[z, y]`. To prove that we can do the injection as an coercion,
-- it's sufficient to know (1) that the new scope contains distinct names, and
-- (2) it extends the old scope. These are the `Distinct l` and
-- `NameSet (n:=>:l)` conditions below.

injectNames :: InjectableE e => Distinct l => NameSet (n:=>:l) -> e n -> e l
injectNames _ x = unsafeCoerceE x

-- `injectNames` is the only function we actualy use in practice. The rest of
-- this section is just about proving that it's valid to use `injectNames`, by
-- offering tools to implement `Injectable` instances.

-- To prove that a data type is injectable by coercion, we have to show that
-- it's injectable without using coercion. `injectionProof` is never actually
-- called at run time, but it should still be implemented to prove that it's
-- possible. This isn't watertight. For example, you could write
-- `injectionProof = injectNames` and it'd still type check!
-- In this module we only implement the base case instances (unsafely).
-- See Name and Syntax for more interesting ones.
class InjectableE (e::E) where
  injectionProofE :: ObservablyFresh n l -> e n -> e l

class InjectableB (b::B) where
  injectionProofB :: ObservablyFresh n n' -> b n l
                  -> (forall l'. ObservablyFresh l l' -> b n' l' -> a)
                  -> a

type InjectableV v = (forall s. InjectableE s => InjectableE (v s)) :: Constraint

-- an `ObservablyFresh n l` means that scope `l` is a superset of scope `n` that
-- doesn't shadow any of the names exposed by `n`.
data ObservablyFresh (n::S) (l::S) = UnsafeMakeObservablyFresh

-- This is the unsafe base case. The instances defined in Syntax are the ones we
-- actually implement safely.
instance InjectableE (Name s) where
  injectionProofE _ name = unsafeCoerceE name

-- Here's the reasoning informally. Let's say `x` is the name of the binder.
-- The scopes are related like this:
--   l  = n  ++ [x]
--   l' = n' ++ [x]
-- if n' is observably fresh wrt n then l' is observably fresh wrt l. This is because every
-- exposed name in l' is either
--   (1) x itself, which is exposed in both l and l', thus l' doesn't shadow it, or
--   (2) a name other than x exposed by n', which we know is observably fresh
--       wrt n and thus also observably fresh wrt n++[x]
instance InjectableB (NameBinder s) where
  injectionProofB  _ b cont = cont UnsafeMakeObservablyFresh $ unsafeCoerceB b


instance InjectableV v => InjectableE (NameMap v i) where
  injectionProofE fresh m =
    fmapNameMap (\(UnsafeMakeName _) v -> injectionProofE fresh v) m

-- === environments ===

-- The `NameMap` type is purely an optimization. We could do everything using
-- the safe API by defining:
--    type NameMap v i o = (NameSet i, forall s. Name s i -> v s o)
-- Instead, we use this unsafely-implemented data type for efficiency, to avoid
-- long chains of case analyses as we extend environments one name at a time.

data NameMap
  (v::E -> E)  -- env payload, as a function of the static data type (Note [NameMap payload])
  (i::S)       -- scope parameter for names we can look up in this env
  (o::S)       -- scope parameter for the values stored in the env
  = UnsafeMakeNameMap
      (M.Map RawName (EnvVal v o))
      (S.Set RawName)  -- cached name set as an optimization, to avoid the O(n)
                       -- map-to-set conversion

lookupNameMap :: NameMap v i o -> Name s i -> v s o
lookupNameMap (UnsafeMakeNameMap m _) name@(UnsafeMakeName rawName) =
  case M.lookup rawName m of
    Nothing -> error "Env lookup failed (this should never happen)"
    Just d -> fromEnvVal name d

emptyNameMap :: NameMap v (i:=>:i) o
emptyNameMap = UnsafeMakeNameMap mempty mempty

singletonNameMap :: NameBinder s i i' -> v s o -> NameMap v (i:=>:i') o
singletonNameMap (UnsafeMakeBinder (UnsafeMakeName name)) x =
  UnsafeMakeNameMap (M.singleton name $ toEnvVal x) (S.singleton name)

concatNameMaps :: NameMap v (i1:=>:i2) o
               -> NameMap v (i2:=>:i3) o
               -> NameMap v (i1:=>:i3) o
concatNameMaps (UnsafeMakeNameMap m1 s1) (UnsafeMakeNameMap m2 s2) =
  UnsafeMakeNameMap (m2 <> m1) (s2 <> s1)  -- flipped because Data.Map uses a left-biased `<>`

extendNameMap :: NameMap v i o -> NameMap v (i:=>:i') o -> NameMap v i' o
extendNameMap (UnsafeMakeNameMap m1 s1) (UnsafeMakeNameMap m2 s2) =
  UnsafeMakeNameMap (m2 <> m1) (s2 <> s1)

fmapNameMap :: (forall s. Name s i -> v s o -> v' s o') -> NameMap v i o -> NameMap v' i o'
fmapNameMap f (UnsafeMakeNameMap m s) = UnsafeMakeNameMap m' s
  where m' = flip M.mapWithKey m \k (EnvVal rep val) ->
               withTypeable rep $ toEnvVal $ f (UnsafeMakeName k) val

nameMapNames :: NameMap v i o -> NameSet i
nameMapNames (UnsafeMakeNameMap _ s) = UnsafeMakeNameSet s

-- === handling the dynamic/heterogeneous stuff for Env ===

data EnvVal (v::E->E) (n::S) where
  EnvVal :: InjectableE s => TypeRep s -> v s n -> EnvVal v n

fromEnvVal :: forall s i v o. Typeable s => Name s i -> EnvVal v o -> v s o
fromEnvVal name (EnvVal rep val) =
  case eqTypeRep rep (repFromName name) of
    Just HRefl -> val
    _ -> error "type mismatch"

repFromName :: Typeable s => Name s i -> TypeRep s
repFromName _ = typeRep

toEnvVal :: InjectableE s => Typeable s => v s n -> EnvVal v n
toEnvVal v = EnvVal typeRep v

-- === instances ===

instance Show (NameBinder s n l) where
  show (UnsafeMakeBinder v) = show v

instance Pretty (Name s n) where
  pretty (UnsafeMakeName name) = pretty name

instance Pretty (NameBinder s n l) where
  pretty (UnsafeMakeBinder (UnsafeMakeName name)) = pretty name

instance Eq (Name s n) where
  UnsafeMakeName rawName == UnsafeMakeName rawName' = rawName == rawName'

instance Ord (Name s n) where
  compare (UnsafeMakeName name) (UnsafeMakeName name')= compare name name'

instance Show (Name s n) where
  show (UnsafeMakeName rawName) = show rawName


-- === unsafe coercions ===

-- Sometimes we need to break the glass. But at least these are slightly safer
-- than raw `unsafeCoerce` because at the checks the kind

unsafeCoerceE :: forall (e::E) i o . e i -> e o
unsafeCoerceE = unsafeCoerce

unsafeCoerceB :: forall (b::B) n l n' l' . b n l -> b n' l'
unsafeCoerceB = unsafeCoerce

-- === notes ===

{-

Note [NameMap payload]

The "payload" parameter of a `NameMap` has kind `E->E`, making the payload a
function of the queried name's static data parameter. Type-level functions are
limited, and we really only care about only two instantiations of v:: E -> E.

First, there's the identity map, `IdE :: E -> E``, which is used by Scope in
Name.hs. It just says that if you have a Name s n you can query the scope to get
a (newtype-wrapped) `s n`. For example, in the core IR we have
`Name TypedBinderInfo n` for ordinary let/lambda-bound names, and
`Name DataDef n` for data definitions. You can query a `Scope n` with a
`Name TypedBinderInfo n` to get a `TypedBinderInfo n` or with a
`Name DataDef n` to get a `DataDef n`.

Second, there's SubstVal which plays a GADT trick to check whether a name's
static data parameter matches a particular type, say, `TypedBinderInfo`, in
which case you get, say, an Atom, or else it doesn't, in which case you merely
get a new name.

-}
