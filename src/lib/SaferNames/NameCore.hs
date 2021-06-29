-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleInstances #-}

module SaferNames.NameCore (
  S (..), RawName, Name (..), Env  (..), (!), (<>>), (<.>),
  emptyEnv, withFresh, PlainBinder (..), injectName,
  FreshExt, E, B, unsafeCoerceE, unsafeCoerceB, envSingleton, lookupEnvFrag,
  fmapEnv) where

import Prelude hiding (id, (.))
import Data.Text.Prettyprint.Doc  hiding (nest)
import Data.Type.Equality
import Control.Category
import Type.Reflection
import Unsafe.Coerce
import qualified Data.Set  as S

import qualified SaferNames.LazyMap as LM
import qualified Env as D

-- `S` is the kind of "scope parameters". It's only ever used as a phantom type.
-- It represents a list of names, given by the value of the singleton type
-- `Scope n` (`n::S`). Names are tagged with a scope parameter, and a name of
-- type `Name n` has an underlying raw name that must occur in the corresponding
-- `Scope n`. (A detail: `Scope n` actually only carries a *set* of names, not a
-- list, because that's all we need at runtime. But it's important to remember
-- that it conceptually represents a list. For example, a `Scope n` and a
-- `Scope m` that happen to represent the same set of names can't necessarily be
-- considered equal.) Types of kind `S` are mostly created existentially through
-- rank-2 polymorphism, rather than using the constructors in the data
-- definition. For example:
--   magicallyCreateFreshS :: (forall (n::S). a) -> a
--   magicallyCreateFreshS x = x   -- where does `n` come from? magic!

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
-- appears in `n:=>:l` even though it already appeared, twice, in `n`. We have a
-- separate type `FreshExt n l` values of which prove that `l` is a fresh
-- extension of `n`. Without a `FreshExt n l` we merely know that `n` is a
-- prefix of `l.

-- There are also special scopes, `VoidScope` and `UnitScope`, representing the
-- empty list and a singleton list with a particular special name. These are
-- useful in the same way that the ordinary types `Void` and `()` are useful.

data S = (:=>:) S S
       | UnsafeS

type E = S -> *       -- expression-y things, covariant in the S param
type B = S -> S -> *  -- binder-y things, covariant in the first param and
                      -- contravariant in the second. These are things like
                      -- `Binder n l` or `Decl n l`, that bind the names in
                      -- `Scope (n:=>:l)`, extending `n` to `l`. Their free name
                      -- are in `Scope n`. We sometimes call `n` the "outside
                      -- scope" and "l" the "inside scope".

-- TODO: we reuse the old `Name` to make use of the GlobalName name space while
-- we're using both the old and new systems together.
-- TODO: something like this instead:
--    type Tag = T.Text
--    data RawName = RawName Tag Int deriving (Show, Eq, Ord)
type RawName = D.Name

-- invariant: the raw name in `Name s` is contained in the list in the `Scope s`
newtype Name (s::E)  -- static information associated with name
             (n::S)  -- scope parameter
  = UnsafeMakeName RawName
  deriving (Show, Eq, Ord)

newtype Env (v::E -> E)  -- env payload, as a function of the static data type
            (i::S)       -- scope parameter for names we can look up in this env
            (o::S)       -- scope parameter for the values stored in the env
  = UnsafeMakeEnv (LM.LazyMap RawName (EnvVal v o))


data PlainBinder (s::E)  -- static information for the name this binds (note
                         -- that `PlainBinder` doesn't actually carry this data)
                 (n::S)  -- scope the binder lives in
                 (l::S)  -- scope within the binder's scope
  where
    UnsafeMakeBinder :: RawName -> PlainBinder s n l
    Ignore           :: PlainBinder s n n

-- A `FreshExt n l` means that `l` extends `n` with only fresh names
data FreshExt (n::S) (l::S) = UnsafeMakeFreshExt

instance Category FreshExt where
  id    = UnsafeMakeFreshExt
  _ . _ = UnsafeMakeFreshExt

withFresh :: Env v n o -> (forall l. FreshExt n l -> PlainBinder s n l -> Name s l -> a) -> a
withFresh (UnsafeMakeEnv scope) cont =
  cont UnsafeMakeFreshExt (UnsafeMakeBinder freshName) (UnsafeMakeName freshName)
  where freshName = freshRawName "v" (LM.keysSet scope)

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

envSingleton :: Typeable v => Typeable s => PlainBinder s i i' -> v s o -> Env v (i:=>:i') o
envSingleton b x = case b of
  Ignore -> emptyEnv
  UnsafeMakeBinder name ->
    UnsafeMakeEnv $ LM.singleton name $ toEnvVal x

infixl 1 <.>
(<.>) :: Env v (i1:=>:i2) o -> Env v (i2:=>:i3) o -> Env v (i1:=>:i3) o
(<.>) (UnsafeMakeEnv m1) (UnsafeMakeEnv m2) = UnsafeMakeEnv (m2 <> m1)

infixl 1 <>>

(<>>) :: Env v n o -> Env v (n:=>:l) o -> Env v l o
(<>>) (UnsafeMakeEnv m1) (UnsafeMakeEnv m2) = UnsafeMakeEnv (m2 <> m1)

(!) :: Typeable v => Typeable s => Env v n o -> Name s n -> v s o
(!) (UnsafeMakeEnv m) name@(UnsafeMakeName rawName) =
  case LM.lookup rawName m of
    Nothing -> error "Env lookup failed (this should never happen)"
    Just d -> fromEnvVal name d

lookupEnvFrag :: Typeable v => Typeable s
              => Env v (i:=>:i') o -> Name s i' -> Either (Name s i) (v s o)
lookupEnvFrag (UnsafeMakeEnv m) (UnsafeMakeName rawName) =
  case LM.lookup rawName m of
    Nothing -> Left $ UnsafeMakeName rawName
    Just x  -> Right $ fromEnvVal (UnsafeMakeName rawName) x

injectName :: FreshExt n l -> Name s n -> Name s l
injectName _ (UnsafeMakeName name) = UnsafeMakeName name

fmapEnv :: (Typeable v, Typeable v')
        => (forall s. Name s i -> v s o -> v' s o')
        -> Env v i o -> Env v' i o'
fmapEnv f (UnsafeMakeEnv m) =
  UnsafeMakeEnv $ flip LM.mapWithKey m $ \rawName (EnvVal rep val)->
    EnvVal rep $ f (UnsafeMakeName rawName) val

emptyEnv :: Env v (n:=>:n) o
emptyEnv = UnsafeMakeEnv mempty

-- slightly safer than raw `unsafeCoerce` because at least it checks the kind
unsafeCoerceE :: forall (e::E) i o . e i -> e o
unsafeCoerceE = unsafeCoerce

unsafeCoerceB :: forall (b::B) n l n' l' . b n l -> b n' l'
unsafeCoerceB = unsafeCoerce

-- === handling the dynamic/heterogeneous stuff ===

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

instance Show (PlainBinder s n l) where
  show Ignore = "_"
  show (UnsafeMakeBinder v) = show v

instance Pretty (Name s n) where
  pretty (UnsafeMakeName name) = pretty name

instance Pretty (PlainBinder s n l) where
  pretty _ = "TODO"

