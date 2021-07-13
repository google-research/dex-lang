-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module SaferNames.NameCore (
  S (..), RawName, Name (..), withFresh, injectNames, projectName,
  NameBinder (..),
  NameSet (..), singletonNameSet, emptyNameSetFrag, emptyNameSet, extendNameSet, concatNameSets,
  NameMap (..), singletonNameMap, emptyNameMap, nameMapNames,
  lookupNameMap, extendNameMap,  concatNameMaps,
  Distinct, E, B, InjectableE (..), InjectableB (..), Injection (..),
  liftMutableScope, runMutableScopeT, MutableScopeMonadT,
  unsafeCoerceE, unsafeCoerceB) where

import Prelude hiding (id, (.))
import Control.Monad.State
import Data.Text.Prettyprint.Doc  hiding (nest)
import Data.Type.Equality
import Type.Reflection
import Unsafe.Coerce
import qualified Data.Map  as M
import qualified Data.Set  as S

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

data Name (s::E)  -- static information associated with name
          (n::S)  -- scope parameter
  where
    UnsafeMakeName :: Typeable s => RawName -> Name s n

data NameBinder (s::E)  -- static information for the name this binds (note
                        -- that `NameBinder` doesn't actually carry this data)
                (n::S)  -- scope the binder lives in
                (l::S)  -- scope within the binder's scope
  = UnsafeMakeBinder { nameBinderName :: Name s l }

withFresh :: Typeable s => Distinct n => NameSet n
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
instance Distinct (n:=>:UnsafeMakeDistinctS)

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
-- `(InjectableB b, b)` conditions below.

data Injection (n::S) (l::S) where
  Injection :: Distinct l => NameSet (n:=>:l) -> Injection n l

injectNames :: InjectableE e => Injection n l -> e n -> e l
injectNames _ x = unsafeCoerceE x

-- `injectNames` is the only function we actualy use in practice. The rest of
-- this section is just about proving that it's valid to use `injectNames`, by
-- offering tools to implement `Injectable` instances.

-- To prove that a data type is injectable by coercion, we have to show that
-- it's injectable without using coercion. `injectionProof` is never actually
-- called at run time, but it should still be implemented to prove that it's
-- possible. This isn't watertight. For example, you could write
-- `injectionProof = injectNames` and it'd still type check!
class InjectableE (e::E) where
  injectionProofE :: ObservablyFresh n l -> e n -> e l

class InjectableB (b::B) where
  injectionProofB :: ObservablyFresh n n' -> b n l
                  -> (forall l'. ObservablyFresh l l' -> b n' l' -> a)
                  -> a

-- an `ObservablyFresh n l` means that scope `l` is a superset of scope `n` that
-- doesn't shadow any of the names exposed by `n`.
data ObservablyFresh (n::S) (l::S) = UnsafeMakeObservablyFresh

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

instance (forall s. InjectableE s => InjectableE (v s)) => InjectableE (NameMap v i) where
  injectionProofE = undefined

-- === monad for updating scope parameters in-place ===

-- This is the unsafe implementation underlying the Builder monad. We want to be
-- able to emit decls without having to update the scope paramter. For example,
-- we want a function like this:
--
--     emitMul :: Builder m => Atom n -> Atom n -> m n (Atom n)
--
-- Instead of this:
--
--     emitMulAwkwardly :: ScopeReader m => Atom n -> Atom n
--                      -> (forall l. Distinct l => Atom l -> m a)
--                      -> m a
--
-- The idea is to think of functions like `emitMul` as updating their scope
-- parameter "in-place". After emitting the decl, the scope parameter `n`
-- contains the newly created name, and all expressions like `Expr n` get
-- implicitly injected into this new scope. But to ensure this is valid,
-- we need to make sure that anything with the the `n` scope parameter is
-- actually injectable. We can't allow access to a `NameMap v n o`, for example
-- (Though we can have a `NameMap v i n`, since `n` is used positively.)
-- The monad transformer in this section, `MutableScopeMonadT`, enforces that
-- invariant. Scope-changing computations are lifted into the monad using
-- higher-rank functions to ensure that values with the scope parameter `n`
-- can't leak in either direction except through a channel guarded with a
-- `InjectableE` constraint.


newtype MutableScopeMonadT (stored :: S -> *) (m :: * -> *) (n :: S) (a :: *) =
  UnsafeMutableScopeMonad (StateT (S.Set RawName, stored UnsafeMakeS) m a)
  deriving (Functor, Applicative, Monad)

data FreshStoreVal (stored :: S -> *) (e :: E) (n :: S) where
  FreshStoreVal :: Injection n l -> stored l -> e l -> FreshStoreVal stored e n

liftMutableScope
  :: (InjectableE e, InjectableE e', Monad m)
  => e n
  -> (forall n'. stored n' -> e n' -> m (FreshStoreVal stored e' n'))
  -> MutableScopeMonadT stored m n (e' n)
liftMutableScope e cont =
  UnsafeMutableScopeMonad $ StateT \(names, s) ->
    cont (unsafeCoerceE s) (unsafeCoerceE e) >>= \case
      FreshStoreVal (Injection (UnsafeMakeNameSet names')) s' e' ->
        return (unsafeCoerceE e', (names <> names', unsafeCoerceE s'))

runMutableScopeT
  :: (InjectableE e, InjectableE e', Monad m)
  => stored n
  -> e n
  -> (forall n'. e n' -> MutableScopeMonadT stored m n' (e' n'))
  -> m (FreshStoreVal stored e' n)
runMutableScopeT s e cont =
  case cont (unsafeCoerceE e) of
    UnsafeMutableScopeMonad (StateT f) -> do
      (e', (names, s')) <- f (mempty, unsafeCoerceE s)
      let inj = Injection (UnsafeMakeNameSet names)
      return $ FreshStoreVal inj (unsafeCoerceE @UnsafeMakeDistinctS s') (unsafeCoerceE e')

-- === environments ===

-- The `NameMap` type is purely an optimization. We could do everything using
-- the safe API by defining:
--    type NameMap v i o = (NameSet i, forall s. Name s i -> v s o)
-- Instead, we use this unsafely-implemented data type for efficiency, to avoid
-- long chains of case analyses as we extend environments one name at a time.

data NameMap
  (v::E -> E)  -- env payload, as a function of the static data type
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

nameMapNames :: NameMap v i o -> NameSet i
nameMapNames (UnsafeMakeNameMap _ s) = UnsafeMakeNameSet s

-- === handling the dynamic/heterogeneous stuff for Env ===

data EnvVal (v::E->E) (n::S) where
  EnvVal :: TypeRep s -> v s n -> EnvVal v n

fromEnvVal :: forall s i v o. Typeable s => Name s i -> EnvVal v o -> v s o
fromEnvVal name (EnvVal rep val) =
  case eqTypeRep rep (repFromName name) of
    Just HRefl -> val
    _ -> error "type mismatch"

repFromName :: Typeable s => Name s i -> TypeRep s
repFromName _ = typeRep

toEnvVal :: Typeable s => v s n -> EnvVal v n
toEnvVal v = EnvVal typeRep v

-- === instances ===

instance Show (NameBinder s n l) where
  show (UnsafeMakeBinder v) = show v

instance Pretty (Name s n) where
  pretty (UnsafeMakeName name) = pretty name

instance Pretty (NameBinder s n l) where
  pretty _ = "TODO"

instance Eq (Name s n) where
  UnsafeMakeName rawName == UnsafeMakeName rawName' = rawName == rawName'

instance Ord (Name s n) where
  compare (UnsafeMakeName name) (UnsafeMakeName name')= compare name name'

instance Show (Name s n) where
  show (UnsafeMakeName rawName) = show rawName


-- === unsafe coercions ===

-- Sometimes we need to break the glass. But at least these are slightly safer
-- than raw `unsafeCoerce` because at the checks the kind

unsafeCoerceE :: forall o (e::E) i . e i -> e o
unsafeCoerceE = unsafeCoerce

unsafeCoerceB :: forall n' l' (b::B) n l . b n l -> b n' l'
unsafeCoerceB = unsafeCoerce
