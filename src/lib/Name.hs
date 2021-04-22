-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PolyKinds #-}

module Name (
  S (..), Tag, RawName (..), Name (..), Env  (..), (>->),
  injectNameL, injectNameR, emptyEnv, partitionName, envLookup, envAsScope,
  PlainBinder (..), Scope, RenameEnv, Disjoint, NameTraversal (..), E,
  B, HasNames (..), Fresh (..), BindsNames (..), unsafeCoerceE, unsafeCoerceB,
  NameSet, projectName, projectNames, fmapNames, foldMapNames, freeNames,
  injectNamesL, Abs (..), Nest (..), NestPair (..), PlainBinderList,
  AnnBinderP (..), AnnBinderListP (..), EnvE (..), RecEnv (..), RecEnvFrag (..),
  BuilderPT (..), MonadBuilderP (..), WithDeclsP (..), runBuilderPT,
  unsafeMakeDecls, AlphaEq (..), SourceName, fmapFresh,
  UnitE (..), EmptyNest, PairE (..), MaybeE (..), ListE (..),
  EitherE (..), ListE (..), LiftE (..), emptyDisjoint,
  pattern SourceName, pattern SourceBinder) where

import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer.Strict
import qualified Data.Map.Strict as M
import qualified Data.Set        as S
import Data.String
import qualified Data.Text as T
import Unsafe.Coerce
import Data.Store (Store)
import Data.Text.Prettyprint.Doc  hiding (nest)
import GHC.Generics hiding (S)
import GHC.Exts (Constraint)

import qualified LazyMap as LM

-- name scope kind
data S = (:-:) S S        -- concatenation of scopes
       | UnsafeMakeScope  -- used to supply existential scopes
       | EmptyScope
       | SourceScope      -- contains everything

type Tag = T.Text
data RawName = RawName Tag Int deriving (Show, Eq, Ord)

data Name (n::S) = UnsafeMakeName RawName  deriving (Show, Eq, Ord)

data Env (s::S) (a:: *) = UnsafeMakeEnv  (LM.LazyMap RawName a)

infixl 1 >->
(>->) :: Env s1 a -> Env s2 a -> Env (s1 :-: s2) a
(>->) = undefined

injectNameL :: Disjoint a b -> Name a -> Name (a:-:b)
injectNameL _ (UnsafeMakeName rawName) = UnsafeMakeName rawName

injectNameR :: Name b -> Name (a:-:b)
injectNameR (UnsafeMakeName rawName) = UnsafeMakeName rawName

emptyEnv :: Env EmptyScope a
emptyEnv = undefined

partitionName :: Scope b -> Name (a:-:b) -> Either (Name a) (Name b)
partitionName = undefined

envLookup :: Env n a -> Name n -> a
envLookup = undefined

envAsScope :: Env n a -> Scope n
envAsScope = undefined

data PlainBinder (n::S) (l::S) where
  UnsafeMakeBinder :: RawName -> PlainBinder n l
  Ignore           :: PlainBinder n EmptyScope

-- Invariant: `Scope s` has a single inhabitant.
type Scope s = Env s ()

type RenameEnv i o = Env i (Name o)

-- invariant: the existence of a `Disjoint a b` means that the `Scope a` and
-- `Scope b` don't share any names
data Disjoint (a::S) (b::S) = UnsafeMakeDisjoint

emptyDisjoint :: Disjoint a EmptyScope
emptyDisjoint = UnsafeMakeDisjoint

data NameTraversal m i o where
  NameTraversal :: (Name i -> m (Name o)) -> RenameEnv i' o
                -> NameTraversal m (i:-:i') o

type E = S -> *       -- expression-y things, covariant in the S param
type B = S -> S -> *  -- binder-y things, covariant in the first param and
                      -- contravariant in the second

-- traverses free names, possibly renaming bound ones as needed
class HasNames (e::E) where
  traverseNames :: Monad m => Scope o -> NameTraversal m i o -> e i -> m (e o)

data Fresh (b::B) (n::S) (l::S) where
  Fresh :: Disjoint n l' -> b n l' -> RenameEnv l l' -> Fresh b n l

class BindsNames (b::B) where
  traverseNamesBinders :: Monad m => Scope o -> NameTraversal m i o -> b i l -> m (Fresh b o l)
  boundScope :: b n l -> Scope l

-- slightly safer than raw `unsafeCoerce` because it requires `HasNames`
unsafeCoerceE :: HasNames e => e i -> e o
unsafeCoerceE = unsafeCoerce

unsafeCoerceB :: BindsNames b => b n l -> b n' l'
unsafeCoerceB = unsafeCoerce

withFresh :: Scope n -> (forall l. Disjoint n l -> PlainBinder n l -> Name l -> a) -> a
withFresh (UnsafeMakeEnv scope) cont =
  cont UnsafeMakeDisjoint (UnsafeMakeBinder freshName) (UnsafeMakeName freshName)
  where freshName = freshRawName "v" (LM.keysSet scope)

freshRawName :: Tag -> S.Set RawName -> RawName
freshRawName tag usedNames = RawName tag nextNum
  where
    nextNum = case S.lookupLT (RawName tag bigInt) usedNames of
                Just (RawName tag' i)
                  | tag' /= tag -> 0
                  | i < bigInt  -> i + 1
                  | otherwise   -> error "Ran out of numbers!"
                Nothing -> 0
    bigInt = (10::Int) ^ (9::Int)  -- TODO: consider a real sentinel value

-- === specialized traversals ===

type NameSet n = S.Set (Name n)

projectName :: Scope l -> Name (n:-:l) -> Maybe (Name n)
projectName = undefined

projectNames :: HasNames e => Scope l -> e (n:-:l) -> Maybe (e n)
projectNames = undefined

fmapNames :: HasNames e => Scope b -> (Name a -> Name b) -> e a -> e b
fmapNames = undefined

foldMapNames :: (HasNames e, Monoid a) => (Name n -> a) -> e n -> a
foldMapNames f e = undefined
  -- execWriter $ traverseNames unitScope t e
  -- where t = newNameTraversal \name -> tell (f name) >> return unitName

freeNames :: HasNames e => e n -> NameSet n
freeNames e = undefined -- foldMapNames S.singleton e

-- `injectNamesL` should behave like this:
--    injectNamesL x = fmapNames (liftName d) x
-- `unsafeCoerce` is an optimization, and it should behave the same, up to alpha
-- renaming.
injectNamesL :: HasNames e => Disjoint n l -> e n -> e (n:-:l)
injectNamesL _ x = unsafeCoerceE x

injectNamesR :: HasNames e => e l -> e (n:-:l)
injectNamesR x = unsafeCoerceE x

-- === common scoping patterns ===

data Abs (binder::B) (body::E) (n::S) where
  Abs :: binder n l -> body (n:-:l) -> Abs binder body n

data Nest (binder::B) (n::S) (l::S) where
 Nest  :: binder n h -> Nest binder (n:-:h) i -> Nest binder n (h:-:i)
 Empty ::                                        Nest binder n EmptyScope

data NestPair (b1::B) (b2::B) n l where
  NestPair :: b1 n l -> b2 l l' -> NestPair b1 b2 n l'

type PlainBinderList = Nest PlainBinder

infixl 7 :>
data AnnBinderP     (b::B) (ann ::E) (n::S) (l::S) = (:>) (b n l) (ann n) deriving (Show)
data AnnBinderListP (b::B) (ann ::E) (n::S) (l::S) = (:>>) (Nest b n l) [ann n]

-- === environment variants ===

newtype EnvE (e::E) (i::S) (o::S) = EnvE { fromEnvE :: Env i (e o) }

newtype RecEnv (e::E) (n::S) = RecEnv { fromRecEnv :: Env n (e n) }

newtype RecEnvFrag (e::E) (n::S) (l::S) = RecEnvFrag { fromRecEnvFrag :: Env l (e (n:-:l))}

-- === various E-kind and B-kind versions of standard containers ===

type PrettyE  e = (forall (n::S)       . Pretty (e n  )) :: Constraint
type PrettyB b  = (forall (n::S) (l::S). Pretty (b n l)) :: Constraint

type ShowE e = (forall (n::S)       . Show (e n  )) :: Constraint
type ShowB b = (forall (n::S) (l::S). Show (b n l)) :: Constraint

type EqE e = (forall (n::S)       . Eq (e n  )) :: Constraint
type EqB b = (forall (n::S) (l::S). Eq (b n l)) :: Constraint

data UnitE (n::S) = UnitH deriving (Show, Eq, Generic, Generic1, Store)
data VoidE (n::S)          deriving (          Generic, Generic1, Store)

data PairE (e1::E) (e2::E) (n::S) = PairE (e1 n) (e2 n)
     deriving (Show, Eq, Generic, Generic1, Store)

data EitherE (e1::E) (e2::E) (n::S) = LeftE (e1 n) | RightE (e2 n)
     deriving (Show, Eq, Generic, Generic1, Store)

data MaybeE (e::E) (n::S) = JustE (e n) | NothingE
     deriving (Show, Eq, Generic, Generic1, Store)

data ListE (e::E) (n::S) = ListE { fromListE :: [e n] }
     deriving (Show, Eq, Generic, Generic1, Store)

data LiftE (a:: *) (n::S) = LiftE { fromLiftE :: a }
     deriving (Show, Eq, Generic, Generic1, Store)

-- === various convenience utilities ===

class HasNames e => AlphaEq (e::E) where
  alphaEq :: Scope n -> e n -> e n -> Bool

infixr 7 @>
-- really, at most one name
class BindsNames b => BindsOneName (b::B) where
  (@>) :: b n l  -> a -> Env l a

infixr 7 @@>
class BindsNames b => BindsNameList (b::B) where
  (@@>) :: b n l -> [a] -> Env l a

type EmptyNest (b::B) = Abs (Nest b) UnitE :: E

extendScope :: BindsNames b => Scope n -> b n l -> Scope (n:-:l)
extendScope scope b = scope >-> boundScope b

injectLNameTraversal :: Disjoint o o' -> NameTraversal m i o -> NameTraversal m i (o:-:o')
injectLNameTraversal = unsafeCoerce

-- XXX: the coercion is here because GHC doesn't know about the associativity of `:-:`.
-- Can we do something better with explicit reassociation functions?
extendNameTraversal :: NameTraversal m i o -> RenameEnv i' o -> NameTraversal m (i:-:i') o
extendNameTraversal (NameTraversal f env) env' =
  unsafeCoerce $ NameTraversal f $ env >-> env'

extendInjectLNameTraversal :: Disjoint o o' -> NameTraversal m i o
                           -> RenameEnv i' o' -> NameTraversal m (i:-:i') (o:-:o')
extendInjectLNameTraversal d t env =
  extendNameTraversal (injectLNameTraversal d t) (injectEnvNamesR env)

-- variant with the common extension built in
withTraverseNamesBinders
  :: (BindsNames b, Monad m)
  =>             Scope  o       -> NameTraversal m  i        o       -> b i i'
  -> (forall o'. Scope (o:-:o') -> NameTraversal m (i:-:i') (o:-:o') -> b o o' -> m a)
  -> m a
withTraverseNamesBinders s t b cont =
  traverseNamesBinders s t b >>= \case
    Fresh d b' renamer -> do
      let t' = extendInjectLNameTraversal d t renamer
      let s' = extendScope s b'
      cont s' t' b'

injectEnvNamesL :: HasNames e => Disjoint a b -> Env i (e a) -> Env i (e (a:-:b))
injectEnvNamesL d env = fromEnvE $ injectNamesL d $ EnvE env

injectEnvNamesR :: HasNames e => Env i (e b) -> Env i (e (a:-:b))
injectEnvNamesR env = fromEnvE $ injectNamesR $ EnvE env

fmapFresh :: (forall o'. b1 o o' -> b2 o o') -> Fresh b1 o i -> Fresh b2 o i
fmapFresh f (Fresh ext b renamer) = Fresh ext (f b) renamer

-- === source names, which don't obey any special invariants ===

data SourceNS where
type RawSourceName = Tag

type SourceName = Name SourceScope

pattern SourceBinder :: SourceName -> PlainBinder SourceScope SourceScope
pattern SourceBinder name <- ((\(UnsafeMakeBinder name) -> SourceName name) -> name)
  where SourceBinder (UnsafeMakeName name) = UnsafeMakeBinder name

pattern SourceName :: RawName -> SourceName
pattern SourceName name = UnsafeMakeName name

getRawSourceName :: SourceName -> RawSourceName
getRawSourceName (UnsafeMakeName (RawName name 0)) = name
getRawSourceName (UnsafeMakeName (RawName _ _)) =
  error "nonzero counter for a source name shouldn't happen"

fromRawSourceName :: RawSourceName -> SourceName
fromRawSourceName name = UnsafeMakeName (RawName name 0)

toNest :: BindsNames b => [b SourceScope SourceScope] -> Nest b SourceScope SourceScope
toNest [] = unsafeCoerceB Empty
toNest (b:bs) = unsafeCoerceB $ Nest b $ unsafeCoerceB $ toNest bs

fromNest :: Nest b SourceScope SourceScope -> [b SourceScope SourceScope]
fromNest = undefined

-- This is safe because there are no restrictions on source names.
-- The inteded use is for printing
coerceToSourceScopeE :: HasNames e => e n -> e SourceScope
coerceToSourceScopeE = unsafeCoerce

coerceToSourceScopeB :: BindsNames b => b n l -> b SourceScope SourceScope
coerceToSourceScopeB = unsafeCoerce

-- === monad that updates scopes "in place" ===

-- XXX: it should only gives you access to things that are covariant in `n`.

newtype BuilderPT d m n a =
  UnsafeBuilderPT (StateT (RecEnv d n, [Name n]) m a)
  deriving (Functor, Applicative, Monad)

-- TODO: consider making this the fundamental `MonadBuilder` emit operation:
--   emitGeneral :: (BindsNames b, MonadBuilder m b n, HasNames e)
--               => Abs b e -> m (e n)
-- The challenge is figuring how how to handle the in-scope binding data.
-- Maybe if we have names parameterized by their static payloads we'll
-- be able to handle scope payloads automatically.
class (HasNames d, Monad m) => MonadBuilderP d n m | m -> d, m -> n where
  riskyGetBindings :: m (RecEnv d n)
  emitGeneral :: d n -> m (Name n)
  -- TODO: more foralls
  scopedGeneral :: HasNames e => m (e n) -> m (WithDeclsP d e n)

type WithDeclsP d = Abs (Nest (AnnBinderP PlainBinder d))

-- TODO: more foralls
runBuilderPT :: (HasNames d, Monad m)
                  => RecEnv d n -> BuilderPT d m n (e n) -> m (WithDeclsP d e n)
runBuilderPT bindings (UnsafeBuilderPT m) = undefined
-- runBuilderPT bindings (UnsafeBuilderPT m) = do
--   (result, (bindings, orderedNames)) <- runStateT m (bindings, [])
--   return $ Abs (unsafeMakeDecls bindings orderedNames) result

-- instance (HasNames d, Monad m) => MonadBuilderP d n (BuilderPT d m n) where
--   riskyGetBindings = UnsafeBuilderPT $ gets fst
--   emitGeneral ann = UnsafeBuilderPT do
--     (bindings, orderedNames) <- get
--     withFresh (boundScope bindings) \_ b name -> do
--       let bindings' = unsafeCoerceE $ RecEnv $ fromRecEnvFrag bindings >-> b @> ann
--       let orderedNames' = orderedNames <> [unsafeCoerceE name]
--       put (bindings', orderedNames')
--       return $ unsafeCoerceE name
--   scopedGeneral = undefined

-- Not actually unsafe exactly. It's more that if you have a list `[b n n]` then
-- you're in already in unsafe land.
unsafeMakeDecls :: HasNames d => RecEnv d n -> [Name n] -> Nest (AnnBinderP PlainBinder d) n n
unsafeMakeDecls = undefined
-- unsafeToNest [] = Empty
-- unsafeToNest (b:rest) = Nest b $ unsafeToNest rest

instance MonadBuilderP d n m => MonadBuilderP d n (ReaderT r m) where
  riskyGetBindings = undefined
  emitGeneral = undefined
  scopedGeneral = undefined

-- === instances ===

instance HasNames Name where
  traverseNames _ (NameTraversal f env) name =
    case partitionName (envAsScope env) name of
      Left  name' -> f name'
      Right name' -> return $ envLookup env name'

instance (BindsNames b, HasNames e) => HasNames (Abs b e) where
  traverseNames s t (Abs b body) = do
    withTraverseNamesBinders s t b \s' t' b' ->
      Abs b' <$> traverseNames s' t' body

instance BindsNames PlainBinder where
  traverseNamesBinders s _ b = return $ case b of
    Ignore -> Fresh emptyDisjoint Ignore emptyEnv
    UnsafeMakeBinder _ -> withFresh s \d b' name' ->
                            Fresh d b' (b@>name')
  boundScope b = b @> ()

instance (BindsNames b1, BindsNames b2) => BindsNames (NestPair b1 b2) where
  traverseNamesBinders s _ b = undefined
  boundScope b = undefined

instance BindsOneName PlainBinder where
  (@>) b x = case b of
    Ignore -> emptyEnv
    UnsafeMakeBinder name -> UnsafeMakeEnv $ LM.singleton name x

instance BindsOneName b => BindsNameList (Nest b) where
  (@@>) Empty [] = emptyEnv
  (@@>) (Nest b rest) (x:xs) = b@>x >-> (rest@@>xs)
  (@@>) _ _ = error "length mismatch"

instance BindsNames b => BindsNames (Nest b) where
  traverseNamesBinders s t nest = case nest of
    Empty -> return $ Fresh emptyDisjoint Empty emptyEnv
    -- Nest b rest -> do
    --   traverseNamesBinders s t b >>= \case
    --     Fresh d b' renamer -> do
    --       let t' = extendInjectLNameTraversal d t renamer
    --       let s' = extendScope s b'
    --       traverseNamesBinders s' t' rest >>= \case
    --         Fresh d' rest' renamer' -> do
    --           let renamer'' = injectLEnvNames d' renamer >-> renamer'
    --           return $ Fresh (d >-> d') (Nest b' rest') renamer''

  boundScope nest = case nest of
    -- Empty -> emptyEnv
    Nest b rest -> boundScope b >-> boundScope rest

instance HasNames e => BindsNames (RecEnvFrag e) where
  traverseNamesBinders s t (RecEnvFrag frag) = undefined
    -- traverseNamesBinders s t frag >>= \case
    --   Fresh d frag' renamer -> do
    --     let t' = extendInjectLNameTraversal d t renamer
    --     let s' = extendScope s frag'
    --     frag'' <- injectLM fromEnvE $ traverseNames s' t' $ EnvE frag'
    --     return $ Fresh d (RecEnvFrag frag'') renamer

  boundScope (RecEnvFrag frag) = envAsScope frag

instance HasNames e => HasNames (EnvE e i) where
  traverseNames s traversal (EnvE frag) = undefined
    -- EnvE <$> traverseEnvFrag (traverseNames s traversal) frag

instance (HasNames e1, HasNames e2) => HasNames (PairE e1 e2) where
  traverseNames s env (PairE x y) =
    PairE <$> traverseNames s env x <*> traverseNames s env y

instance IsString RawName where
  fromString s = RawName (fromString s) 0

instance Show (PlainBinder n l) where
  show Ignore = "_"
  show (UnsafeMakeBinder v) = show v

instance (forall n' l. Show (b n' l), forall n'. Show (body n')) => Show (Abs b body n) where
  show (Abs b body) = "(Abs " <> show b <> " " <> show body <> ")"

instance (forall n' l'. Show (b n' l')) => Show (Nest b n l) where
  show Empty = ""
  show (Nest b rest) = "(Nest " <> show b <> " in " <> show rest <> ")"

instance (BindsNames b, HasNames ann) => BindsNames (AnnBinderP b ann) where
  traverseNamesBinders s t (b:>ann) = do
    ann' <- traverseNames s t ann
    traverseNamesBinders s t b >>= \case
      Fresh d b' frag -> return $ Fresh d (b':>ann') frag

  boundScope (b:>_) = boundScope b

instance (BindsOneName b, HasNames ann) => BindsOneName (AnnBinderP b ann) where
  (b:>_) @> x = b @> x

instance Pretty (Name n) where
  pretty name = pretty $ show name

instance Pretty (PlainBinder n l) where
  pretty = undefined

instance (PrettyB b, PrettyE ann) => Pretty (AnnBinderP b ann n l) where
  pretty = undefined

instance (PrettyB b) => Pretty (Nest b n l) where
  pretty _ = undefined --  pretty $ toList xs

instance (PrettyB b, PrettyE e) => Pretty (Abs b e n) where
  pretty _ = undefined
