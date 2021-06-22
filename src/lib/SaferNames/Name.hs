-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}

module SaferNames.Name (
  S (..), RawName, Name (..), Env  (..), (<>>), (<.>),
  emptyEnv, envLookup, envAsScope, withFresh,
  PlainBinder (..), Scope, FreshExt, NameTraversal (..),
  extendNameTraversal, injectNameTraversal, extendInjectNameTraversal,
  RenameTraversal, voidScopeEnv,
  E, B, HasNamesE (..), HasNamesB (..), unsafeCoerceE, unsafeCoerceB,
  NameSet, fmapNames, foldMapNames, freeNames, (@>), (@@>),
  freshenAbs, freshenBinder, extendRecEnv,
  projectName, injectNameL, injectNameR, projectNamesL, injectNamesL, injectEnvNamesL,
  Abs (..), FreshAbs (..), Nest (..), NestPair (..),PlainBinderList, envMapWithKey,
  AnnBinderP (..), AnnBinderListP (..), EnvE (..), RecEnv (..), RecEnvFrag (..),
  AlphaEq (..), UnitE (..), VoidE, PairE (..), MaybeE (..), ListE (..),
  EitherE (..), LiftE (..), emptyFreshExt, composeFreshExt, idRenamer,
  EqE, EqB, FreshBinder (..), lookupNameTraversal, extendScope) where

import Control.Monad.Identity
import Control.Monad.Writer.Strict
import qualified Data.Set        as S
import Unsafe.Coerce
import Data.Text.Prettyprint.Doc  hiding (nest)
import GHC.Exts (Constraint)

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
       | UnitScope
       | VoidScope

-- TODO: we reuse the old `Name` to make use of the GlobalName name space while
-- we're using both the old and new systems together.
-- TODO: something like this instead:
--    type Tag = T.Text
--    data RawName = RawName Tag Int deriving (Show, Eq, Ord)
type RawName = D.Name

-- invariant: the raw name in `Name s` is contained in the list in the `Scope s`
newtype Name (n::S) = UnsafeMakeName RawName
                      deriving (Show, Eq, Ord)

newtype Env (n::S) (a:: *) = UnsafeMakeEnv (LM.LazyMap RawName a)
                             deriving (Functor, Foldable, Traversable)
type Scope n = Env n ()

emptyEnv :: Env (n:=>:n) a
emptyEnv = UnsafeMakeEnv mempty

voidScopeEnv :: Env VoidScope a
voidScopeEnv = UnsafeMakeEnv mempty

infixl 1 <.>
(<.>) :: Env (n1:=>:n2) a -> Env (n2:=>:n3) a -> Env (n1:=>:n3) a
(<.>) (UnsafeMakeEnv m1) (UnsafeMakeEnv m2) = UnsafeMakeEnv (m2 <> m1)

infixl 1 <>>
(<>>) :: Env n a -> Env (n:=>:l) a -> Env l a
(<>>) (UnsafeMakeEnv m1) (UnsafeMakeEnv m2) = UnsafeMakeEnv (m2 <> m1)

envLookup :: Env n a -> Name n -> a
envLookup (UnsafeMakeEnv m) (UnsafeMakeName name) =
  case LM.lookup name m of
    Just x -> x
    Nothing -> error "Env lookup should never fail"

envAsScope :: Env n a -> Scope n
envAsScope (UnsafeMakeEnv m) = UnsafeMakeEnv $ LM.constLazyMap (LM.keysSet m) ()

projectName :: Scope (n:=>:l) -> Name l -> Either (Name n) (Name (n:=>:l))
projectName (UnsafeMakeEnv m) (UnsafeMakeName name) =
  case LM.lookup name m of
    Nothing -> Left  $ UnsafeMakeName name
    Just () -> Right $ UnsafeMakeName name

injectNameL :: FreshExt n l -> Name n -> Name l
injectNameL _ (UnsafeMakeName name) = UnsafeMakeName name

injectNameR :: Name (n:=>:l) -> Name l
injectNameR (UnsafeMakeName name) = UnsafeMakeName name

data PlainBinder (n::S) (l::S) where
  UnsafeMakeBinder :: RawName -> PlainBinder n l
  Ignore           :: PlainBinder n n

type E = S -> *       -- expression-y things, covariant in the S param
type B = S -> S -> *  -- binder-y things, covariant in the first param and
                      -- contravariant in the second. These are things like
                      -- `Binder n l` or `Decl n l`, that bind the names in
                      -- `Scope (n:=>:l)`, extending `n` to `l`. Their free name
                      -- are in `Scope n`. We sometimes call `n` the "outside
                      -- scope" and "l" the "inside scope".

-- A `FreshExt n l` means that `l` extends `n` with only fresh names
data FreshExt (n::S) (l::S) = UnsafeMakeExt

emptyFreshExt :: FreshExt n n
emptyFreshExt = UnsafeMakeExt

composeFreshExt :: FreshExt n h -> FreshExt h l -> FreshExt n l
composeFreshExt _ _ = UnsafeMakeExt

data NameTraversal (e::E) (m:: * -> *) (i::S) (o::S) where
  NameTraversal :: (Name i -> m (e o))
                -> Env (i:=>:i') (Name o)
                -> NameTraversal e m i' o

type RenameTraversal = NameTraversal Name

-- traverses free names, possibly renaming bound ones as needed
class HasNamesE (e::E) where
  traverseNamesE :: Monad m => Scope o -> RenameTraversal m i o -> e i -> m (e o)

-- A fresh binder, hiding its new output scope and exposing a renaming
-- env that can give you those names. Used mainly for the result of
-- `traverseNamesB` and similar. Given a `b i i' `, and a substitution
-- `Name i -> Name o`, you can produce a `FreshBinder b o i' `.
data FreshBinder (b::B) (o::S) (i'::S) where
  FreshBinder :: FreshExt o o' -> b o o' -> Env i' (Name o')
              -> FreshBinder b o i'

class HasNamesB (b::B) where
  traverseNamesB :: Monad m => Scope o -> RenameTraversal m i o
                       -> b i i'
                       -> m (FreshBinder b o (i:=>:i'))
  boundScope :: b n l -> Scope (n:=>:l)

-- slightly safer than raw `unsafeCoerce` because at least it checks the kind
unsafeCoerceE :: forall (e::E) i o . e i -> e o
unsafeCoerceE = unsafeCoerce

unsafeCoerceB :: forall (b::B) n l n' l' . b n l -> b n' l'
unsafeCoerceB = unsafeCoerce

withFresh :: Scope n -> (forall l. FreshExt n l -> PlainBinder n l -> Name l -> a) -> a
withFresh (UnsafeMakeEnv scope) cont =
  cont UnsafeMakeExt (UnsafeMakeBinder freshName) (UnsafeMakeName freshName)
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

unitName :: Name UnitScope
unitName = UnsafeMakeName "TheName"

unitScope :: Scope UnitScope
unitScope = UnsafeMakeEnv $ LM.singleton unitRawName ()
  where UnsafeMakeName unitRawName = unitName

envMapWithKey :: (Name i -> a -> b) -> Env i a -> Env i b
envMapWithKey f (UnsafeMakeEnv m) = UnsafeMakeEnv $ LM.mapWithKey f' m
  where f' rawName = f $ UnsafeMakeName rawName

envPairs :: Env (n:=>:l) a -> (PlainBinderList n l, [a])
envPairs (UnsafeMakeEnv m) = do
  let (names, vals) = unzip $ LM.assocs m
  (unsafeMakePlainBinderList names, vals)

unsafeMakePlainBinderList :: [RawName] -> PlainBinderList n l
unsafeMakePlainBinderList names = case names of
  [] -> unsafeCoerceB Empty
  (name:rest) -> Nest (UnsafeMakeBinder name) $ unsafeMakePlainBinderList rest

-- === specialized traversals ===

type NameSet n = S.Set (Name n)

fmapNames :: HasNamesE e => Scope b -> (Name a -> Name b) -> e a -> e b
fmapNames scope f e = runIdentity $ traverseNamesE scope t e
  where t = newNameTraversal (pure . f)

foldMapNames :: (HasNamesE e, Monoid a) => (Name n -> a) -> e n -> a
foldMapNames f e =
  execWriter $ traverseNamesE unitScope t e
  where t = newNameTraversal \name -> tell (f name) >> return unitName

freeNames :: HasNamesE e => e n -> NameSet n
freeNames e = foldMapNames S.singleton e

-- should be equivalent to `\ext -> fmapNames (injectName ext)`
injectNamesL :: HasNamesE e => FreshExt n l -> e n -> e l
injectNamesL _ = unsafeCoerceE

-- TODO: consider returning one of the `Name (n:=>:l)` names found in the
-- `Nothing` case, or even the full set.
projectNamesL :: HasNamesE e => Scope n -> Scope (n:=>:l) -> e l -> Maybe (e n)
projectNamesL scope scopeFragment e = traverseNamesE scope t e
  where t = newNameTraversal \name -> case projectName scopeFragment name of
                                        Left name' -> Just name'
                                        Right _    -> Nothing

-- === common scoping patterns ===

data Abs (binder::B) (body::E) (n::S) where
  Abs :: binder n l -> body l -> Abs binder body n

data FreshAbs (binder::B) (body::E) (n::S) where
  FreshAbs :: FreshExt n l -> binder n l -> body l -> FreshAbs binder body n

data NestPair (b1::B) (b2::B) (n::S) (l::S) where
  NestPair :: b1 n l -> b2 l l' -> NestPair b1 b2 n l'

data Nest (binder::B) (n::S) (l::S) where
  Nest  :: binder n h -> Nest binder h l -> Nest binder n l
  Empty ::                                  Nest binder n n

type PlainBinderList = Nest PlainBinder

infixl 7 :>
data AnnBinderP (b::B) (ann ::E) (n::S) (l::S) =
  (:>) (b n l) (ann n)
  deriving (Show)

infixl 7 :>>
-- The length of the annotation list should match the depth of the nest
data AnnBinderListP (b::B) (ann::E) (n::S) (l::S) =
  (:>>) (Nest b n l) [ann n]

-- === environment variants ===

-- covariant in `o`, contravariant in `i`.
newtype EnvE (e::E) (i::S) (o::S) = EnvE { fromEnvE :: Env i (e o) }

-- covariant in `n`
newtype RecEnv (e::E) (n::S) = RecEnv { fromRecEnv :: Env n (e n) }

-- covariant in `n`, contravariant in `l`
newtype RecEnvFrag (e::E) (n::S) (l::S) = RecEnvFrag { fromRecEnvFrag :: Env (n:=>:l) (e l)}

-- === various E-kind and B-kind versions of standard containers and classes ===

type PrettyE  e = (forall (n::S)       . Pretty (e n  )) :: Constraint
type PrettyB b  = (forall (n::S) (l::S). Pretty (b n l)) :: Constraint

type ShowE e = (forall (n::S)       . Show (e n  )) :: Constraint
type ShowB b = (forall (n::S) (l::S). Show (b n l)) :: Constraint

type EqE e = (forall (n::S)       . Eq (e n  )) :: Constraint
type EqB b = (forall (n::S) (l::S). Eq (b n l)) :: Constraint

data UnitE (n::S) = UnitE deriving (Show, Eq)
data VoidE (n::S)

data PairE (e1::E) (e2::E) (n::S) = PairE (e1 n) (e2 n)
     deriving (Show, Eq)

data EitherE (e1::E) (e2::E) (n::S) = LeftE (e1 n) | RightE (e2 n)
     deriving (Show, Eq)

data MaybeE (e::E) (n::S) = JustE (e n) | NothingE
     deriving (Show, Eq)

data ListE (e::E) (n::S) = ListE { fromListE :: [e n] }
     deriving (Show, Eq)

data LiftE (a:: *) (n::S) = LiftE { fromLiftE :: a }
     deriving (Show, Eq)

-- === various convenience utilities ===

class HasNamesE e => AlphaEq (e::E) where
  alphaEq :: Scope n -> e n -> e n -> Bool

infixr 7 @>
-- really, at most one name
class HasNamesB b => BindsOneName (b::B) where
  (@>) :: b n l -> a -> Env (n:=>:l) a

infixr 7 @@>
class HasNamesB b => BindsNameList (b::B) where
  (@@>) :: b n l -> [a] -> Env (n:=>:l) a

newNameTraversal :: (Name i -> m (e o)) -> NameTraversal e m i o
newNameTraversal f = NameTraversal f emptyEnv

idNameTraversal :: Monad m => NameTraversal Name m n n
idNameTraversal = newNameTraversal pure

extendNameTraversal :: NameTraversal e m i o -> Env (i:=>:i') (Name o)
                    -> NameTraversal e m i' o
extendNameTraversal (NameTraversal f env) env' = NameTraversal f (env <.> env')

injectNameTraversal :: HasNamesE e => FreshExt o o' -> NameTraversal e m i o
                    -> NameTraversal e m i o'
injectNameTraversal = unsafeCoerce

extendInjectNameTraversal :: HasNamesE e
                          => FreshExt o o' -> Env (i:=>:i') (Name o')
                          -> NameTraversal e m i  o
                          -> NameTraversal e m i' o'
extendInjectNameTraversal ext renamer t =
  extendNameTraversal (injectNameTraversal ext t) renamer

idRenamer :: HasNamesB b => b n l -> Env (n:=>:l) (Name l)
idRenamer b = envMapWithKey (\name _ -> injectNameR name) $ boundScope b

-- variant with the common extension built in
withTraverseNamesB
  :: (HasNamesB b, Monad m)
  =>                              Scope  o  -> RenameTraversal m  i  o  -> b i i'
  -> (forall o'. FreshExt o o' -> Scope  o' -> RenameTraversal m  i' o' -> b o o' -> m a)
  -> m a
withTraverseNamesB s t b cont = do
  traverseNamesB s t b >>= \case
    FreshBinder ext b' renamer -> do
      let t' = extendInjectNameTraversal ext renamer t
      let s' = extendScope s b'
      cont ext s' t' b'

lookupNameTraversal :: Monad m => NameTraversal e m i o -> Name i
                    -> m (Either (e o) (Name o))
lookupNameTraversal (NameTraversal f env) name =
  case projectName (envAsScope env) name of
      Left  name' -> Left <$> f name'
      Right name' -> return $ Right $ envLookup env name'

extendScope :: HasNamesB b => Scope n -> b n l -> Scope l
extendScope s b = s <>> boundScope b

freshenAbs :: (HasNamesB b, HasNamesE e) => Scope n -> Abs b e n -> FreshAbs b e n
freshenAbs s (Abs b body) =
  case freshenBinder s b of
    FreshBinder ext b' renamer -> do
      let s' = extendScope s b'
      let t = extendInjectNameTraversal ext renamer idNameTraversal
      let body' = runIdentity $ traverseNamesE s' t body
      FreshAbs ext b' body'

freshenBinder :: HasNamesB b => Scope n -> b n l -> FreshBinder b n (n:=>:l)
freshenBinder s b = runIdentity $ traverseNamesB s idNameTraversal b

extendRecEnv :: HasNamesE e => FreshExt n l -> RecEnv e n -> RecEnvFrag e n l -> RecEnv e l
extendRecEnv ext (RecEnv env) (RecEnvFrag frag) = let
  env' = injectEnvNamesL ext env
  in RecEnv $ env' <>> frag

injectEnvNamesL :: HasNamesE e => FreshExt n l -> Env i (e n) -> Env i (e l)
injectEnvNamesL ext env = fromEnvE $ injectNamesL ext $ EnvE env

-- === instances ===

instance HasNamesE Name where
  traverseNamesE _ t name =
    lookupNameTraversal t name >>= \case
      Left  name' -> return name'
      Right name' -> return name'

instance (HasNamesB b, HasNamesE e) => HasNamesE (Abs b e) where
  traverseNamesE s t (Abs b body) = do
    withTraverseNamesB s t b \_ s' t' b' ->
      Abs b' <$> traverseNamesE s' t' body

instance HasNamesB PlainBinder where
  traverseNamesB s _ b = case b of
    Ignore -> return $ FreshBinder emptyFreshExt Ignore emptyEnv
    UnsafeMakeBinder _ ->
      withFresh s \ext b' name' ->
        return $ FreshBinder ext b' (b@>name')
  boundScope b = b @> ()

instance BindsOneName PlainBinder where
  (@>) b x = case b of
    Ignore -> emptyEnv
    UnsafeMakeBinder name -> UnsafeMakeEnv $ LM.singleton name x

instance BindsOneName b => BindsNameList (Nest b) where
  (@@>) Empty [] = emptyEnv
  (@@>) (Nest b rest) (x:xs) = b@>x <.> rest@@>xs
  (@@>) _ _ = error "length mismatch"

instance (HasNamesB b1, HasNamesB b2) => HasNamesB (NestPair b1 b2) where
  traverseNamesB s t (NestPair b1 b2) =
    traverseNamesB s t b1 >>= \case
        FreshBinder ext b1' renamer -> do
          let t' = extendInjectNameTraversal ext renamer t
          let s' = extendScope s b1'
          traverseNamesB s' t' b2 >>= \case
            FreshBinder ext' b2' renamer' -> do
              let ext'' = composeFreshExt ext ext'
              let renamerInjected = fromEnvE $ injectNamesL ext' $ EnvE renamer
              let renamer'' = renamerInjected <.> renamer'
              return $ FreshBinder ext'' (NestPair b1' b2') renamer''

  boundScope (NestPair b1 b2) = boundScope b1 <.> boundScope b2

instance HasNamesB b => HasNamesB (Nest b) where
  traverseNamesB s t nest = case nest of
    Empty -> return $ FreshBinder emptyFreshExt Empty emptyEnv
    Nest b rest ->
      traverseNamesB s t (NestPair b rest) >>= \case
        FreshBinder ext (NestPair b' rest') renamer ->
          return $ FreshBinder ext (Nest b' rest') renamer

  boundScope nest = case nest of
    Empty -> emptyEnv
    Nest b rest -> boundScope b <.> boundScope rest

instance HasNamesE e => HasNamesE (EnvE e i) where
  traverseNamesE s t (EnvE env) = EnvE <$> traverse (traverseNamesE s t) env

instance HasNamesE e => HasNamesB (RecEnvFrag e) where
  traverseNamesB s t (RecEnvFrag env) = do
    let (bs, vals) = envPairs env
    traverseNamesB s t bs >>= \case
      FreshBinder ext bs' renamer -> do
        let t' = extendInjectNameTraversal ext renamer t
        let s' = extendScope s bs'
        vals' <- mapM (traverseNamesE s' t') vals
        let env' = RecEnvFrag $ bs' @@> vals'
        return $ FreshBinder ext env' renamer

  boundScope (RecEnvFrag env) = envAsScope env

instance (HasNamesE e1, HasNamesE e2) => HasNamesE (PairE e1 e2) where
  traverseNamesE s env (PairE x y) =
    PairE <$> traverseNamesE s env x <*> traverseNamesE s env y

instance Show (PlainBinder n l) where
  show Ignore = "_"
  show (UnsafeMakeBinder v) = show v

instance (forall n' l. Show (b n' l), forall n'. Show (body n')) => Show (Abs b body n) where
  show (Abs b body) = "(Abs " <> show b <> " " <> show body <> ")"

instance (forall n' l'. Show (b n' l')) => Show (Nest b n l) where
  show Empty = ""
  show (Nest b rest) = "(Nest " <> show b <> " in " <> show rest <> ")"

instance (HasNamesB b, HasNamesE ann) => HasNamesB (AnnBinderP b ann) where
  traverseNamesB s t (b:>ann) = do
    ann' <- traverseNamesE s t ann
    traverseNamesB s t b >>= \case
      FreshBinder ext b' renamer -> return $ FreshBinder ext (b':>ann') renamer

  boundScope (b:>_) = boundScope b

instance (BindsOneName b, HasNamesE ann) => BindsOneName (AnnBinderP b ann) where
  (b:>_) @> x = b @> x

instance Pretty (Name n) where
  pretty (UnsafeMakeName name) = pretty name

instance Pretty (PlainBinder n l) where
  pretty _ = "TODO"

instance (PrettyB b, PrettyE ann) => Pretty (AnnBinderP b ann n l) where
  pretty _ = "TODO"

instance (PrettyB b) => Pretty (Nest b n l) where
  pretty _ = "TODO"

instance (PrettyB b, PrettyE e) => Pretty (Abs b e n) where
  pretty _ = "TODO"

instance (ShowB b, ShowE ann) => Show (AnnBinderListP b ann n l) where
  show _ = "TODO"
