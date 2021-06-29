-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module SaferNames.Name (
  Name (..), RawName, S (..), Env (..), (!), (<>>), (<.>), PlainBinder (..),
  Scope, ScopeFrag, FreshExt, NameTraversal (..),
  E, B, HasNamesE (..), HasNamesB (..), BindsOneName (..), (@@>), injectNames,
  Abs (..), FreshAbs (..), Nest (..), NestPair (..),PlainBinderList,
  AnnBinderP (..), AnnBinderListP (..), newNameTraversal, idNameTraversal,
  UnitE (..), VoidE, PairE (..), MaybeE (..), ListE (..),
  EitherE (..), LiftE (..), EqE, EqB, fromConstAbs, PrettyE, PrettyB, ShowE, ShowB,
  SubstReader (..), SubstReaderT, SubstReaderM, runSubstReaderT, runSubstReaderM,
  ScopeReader (..), ScopeReaderT, ScopeReaderM, runScopeReaderT, runScopeReaderM,
  MonadKind1, MonadKind2, Monad1, Monad2, MonadErr1, MonadErr2, MonadFail1, MonadFail2,
  idSubst, applySubst, applyAbs, applyNaryAbs, extendSubst, lookupBinding,
  ZipSubstEnv (..), MonadZipSubst (..), alphaEqTraversable,
  checkAlphaEq, AlphaEq, AlphaEqE (..), AlphaEqB, IdE (..), ConstE (..),
  EmptyAbs, pattern EmptyAbs, SubstVal (..), SubstE (..), SubstB (..)) where

import Control.Monad.Except hiding (Except)
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.Writer.Strict
import Data.Dynamic
import Data.Text.Prettyprint.Doc  hiding (nest)
import GHC.Exts (Constraint)

import SaferNames.NameCore
import Err

-- === common scoping patterns ===

-- Env with the payload associated with the particular name
type Scope     (n::S)        = Env IdE n n         :: *
type ScopeFrag (n::S) (l::S) = Env IdE (n:=>:l) l  :: *

data Abs (binder::B) (body::E) (n::S) where
  Abs :: binder n l -> body l -> Abs binder body n

data FreshAbs (binder::B) (body::E) (n::S) where
  FreshAbs :: FreshExt n l -> binder n l -> body l -> FreshAbs binder body n

data NestPair (b1::B) (b2::B) (n::S) (l::S) where
  NestPair :: b1 n l -> b2 l l' -> NestPair b1 b2 n l'

data Nest (binder::B) (n::S) (l::S) where
  Nest  :: binder n h -> Nest binder h l -> Nest binder n l
  Empty ::                                  Nest binder n n

type PlainBinderList s = Nest (PlainBinder s)

type EmptyAbs b = Abs b UnitE :: E
pattern EmptyAbs :: b n l -> EmptyAbs b n
pattern EmptyAbs bs = Abs bs UnitE

infixl 7 :>
data AnnBinderP (b::B) (ann ::E) (n::S) (l::S) =
  (:>) (b n l) (ann n)
  deriving (Show)

infixl 7 :>>
-- The length of the annotation list should match the depth of the nest
data AnnBinderListP (b::B) (ann::E) (n::S) (l::S) =
  (:>>) (Nest b n l) [ann n]

-- === type classes for traversing names ===

data NameTraversal m i o where
  NameTraversal :: (forall s. Name s i -> m (Name s o)) -- monadic function for free vars
                -> Env Name (i:=>:i') o                 -- renaming local vars
                -> NameTraversal m i' o

class HasNamesE (e::E) where
  traverseNamesE :: Monad m => Scope o -> NameTraversal m i o -> e i -> m (e o)

class HasNamesB (b::B) where
  traverseNamesB :: Scope o
                 -> NameTraversal m i o
                 -> b i i'
                 -> (forall o'. Scope o' -> NameTraversal m i' o' -> b o o' -> m a)
                 -> m a

newNameTraversal :: (forall s. Name s i -> m (Name s o)) -> NameTraversal  m i o
newNameTraversal f = NameTraversal f emptyEnv

idNameTraversal :: Monad m => NameTraversal m n n
idNameTraversal = newNameTraversal pure

lookupNameTraversal :: Typeable s => Monad m
                    => NameTraversal m i o -> Name s i -> m (Name s o)
lookupNameTraversal (NameTraversal f env) name =
  case lookupEnvFrag env name of
      Left  name' -> f name'
      Right name' -> return name'

-- === type class for substitutions ===

-- Only alllows non-trivial substitution with names that match the parameter
-- `sMatch`. For example, this lets us substitute ordinary variables in Core
-- with Atoms, while ensuring that things like data def names only get renamed.
data SubstVal (sMatch::E) (atom::E) (s::E) (n::S) where
  SubstVal :: atom n   -> SubstVal s      atom s n
  Rename   :: Name s n -> SubstVal sMatch atom s n

class SubstE (v::E->E) (e::E) where
  substE :: SubstReader v m => e i -> m i o (e o)

class SubstB (v::E->E) (b::B) where
  substB :: SubstReader v  m
         => b i i'
         -> (forall o'. b o o' -> m i' o' a)
         -> m i o a

idRenameEnv :: Scope n -> Env Name n n
idRenameEnv scope = fmapEnv (\name _ -> name) scope

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

-- The identity function at `E`
newtype IdE (e::E) (n::S) = IdE { fromIdE :: e n }

-- The constant function at `E`
newtype ConstE (const::E) (ignored::E) (n::S) = ConstE (const n)

-- === various convenience utilities ===

infixr 7 @>
class BindsOneName (b::B) (s::E) | b -> s where
  (@>) :: b i i' -> v s o -> Env v (i:=>:i') o

infixr 7 @@>
(@@>) :: Typeable v => Typeable s
      => PlainBinderList s i i' -> [v s o] -> Env v (i:=>:i') o
(@@>) Empty [] = emptyEnv
(@@>) (Nest b rest) (x:xs) = envSingleton b x <.> rest@@>xs
(@@>) _ _ = error "length mismatch"

-- should be equivalent to `\ext -> fmapNames (injectName ext)`
injectNames :: HasNamesE e => FreshExt n l -> e n -> e l
injectNames _ = unsafeCoerceE

fromConstAbs :: ScopeReader m => MonadErr1 m
             => HasNamesB b => HasNamesE e => Abs b e n -> m n (e n)
fromConstAbs = undefined

idSubst :: Typeable e => Typeable s => Scope n -> Env (SubstVal s e) n n
idSubst scope = fmapEnv (\name _ -> Rename name) scope

applySubst :: ScopeReader m => SubstE v e => Env v i o -> e i -> m o (e o)
applySubst env x = do
  scope <- askScope
  return $ runSubstReaderM scope env $ substE x

applyAbs :: Typeable s => Typeable val
         => ScopeReader m
         => BindsOneName b s => SubstE (SubstVal s val) e
         => Abs b e n -> val n -> m n (e n)
applyAbs (Abs b body) x = do
  scope <- askScope
  applySubst (idSubst scope <>> (b@>SubstVal x)) body

-- TODO: do it more efficiently, without repeated passes via `applyAbs`
applyNaryAbs :: Typeable s => Typeable val
             => ScopeReader m
             => BindsOneName b s
             => SubstE (SubstVal s val) e
             => SubstB (SubstVal s val) b
             => Abs (Nest b) e n -> [val n] -> m n (e n)
applyNaryAbs (Abs Empty body) [] = return body
applyNaryAbs (Abs (Nest b bs) body) (x:xs) = do
  ab <- applyAbs (Abs b (Abs bs body)) x
  applyNaryAbs ab xs
applyNaryAbs _ _ = error "wrong number of arguments"

-- === versions of monad constraints with scope params ===

type MonadKind  =           * -> *
type MonadKind1 =      S -> * -> *
type MonadKind2 = S -> S -> * -> *

type Monad1 (m :: MonadKind1) = forall (n::S)        . Monad (m n  )
type Monad2 (m :: MonadKind2) = forall (n::S) (l::S) . Monad (m n l)

type MonadErr1 (m :: MonadKind1) = forall (n::S)        . MonadErr (m n  )
type MonadErr2 (m :: MonadKind2) = forall (n::S) (l::S) . MonadErr (m n l)

type MonadFail1 (m :: MonadKind1) = forall (n::S)        . MonadFail (m n  )
type MonadFail2 (m :: MonadKind2) = forall (n::S) (l::S) . MonadFail (m n l)

-- === scope reader monad ===

class Monad1 m => ScopeReader (m::MonadKind1) where
  askScope :: m n (Scope n)
  extendScope :: ScopeFrag n l -> m l a -> m n a

type ScopeReader2 (m::MonadKind2) = forall (n::S). ScopeReader (m n)

newtype ScopeReaderT (m:: * -> *) (n::S) (a:: *) =
  ScopeReaderT { runScopeReaderT' :: ReaderT (Scope n) m a}
  deriving (Functor, Applicative, Monad)

type ScopeReaderM = ScopeReaderT Identity

runScopeReaderT :: Monad m => Scope n -> ScopeReaderT m n a -> m a
runScopeReaderT scope m = runReaderT (runScopeReaderT' m) scope

runScopeReaderM :: Scope n -> ScopeReaderM n a -> a
runScopeReaderM scope m = runIdentity $ runScopeReaderT scope m

lookupBinding :: Typeable s => ScopeReader m => Name s n -> m n (s n)
lookupBinding v = fromIdE <$> (!v) <$> askScope

-- === subst monad ===

class ScopeReader2 m => SubstReader (v::E->E) (m::MonadKind2) | m -> v where
  askSubst :: m i o (Env v i o)
  updateSubst :: Env v i' o -> m i' o a -> m i o a

-- we could have `m::MP` but it's more work and we don't need it
newtype SubstReaderT (m:: * -> *) (v::E -> E) (i::S) (o::S) (a:: *) =
  SubstReaderT { runSubstReaderT' :: ReaderT (Scope o, Env v i o) m a }
  deriving (Functor, Applicative, Monad)

type SubstReaderM = SubstReaderT Identity

runSubstReaderT :: Scope o -> Env v i o -> SubstReaderT m v i o a -> m a
runSubstReaderT bindings env m = runReaderT (runSubstReaderT' m) (bindings, env)

runSubstReaderM :: Scope o -> Env v i o -> SubstReaderM v i o a -> a
runSubstReaderM scope env m = runIdentity $ runSubstReaderT scope env m

instance MonadError e m => MonadError e (SubstReaderT m v i o) where
  throwError e = SubstReaderT $ throwError e
  catchError (SubstReaderT m) f = SubstReaderT $ catchError m $ runSubstReaderT' . f

instance MonadFail m => MonadFail (SubstReaderT m v i o) where
  fail s = SubstReaderT $ fail s

instance Monad m => ScopeReader (SubstReaderT m v i)

instance Monad m => SubstReader v (SubstReaderT m v)

extendSubst :: SubstReader v m => Env v (i:=>:i') o -> m i' o a -> m i o a
extendSubst envFrag cont = do
  env <- askSubst
  updateSubst (env <>> envFrag) cont

-- === alpha-renaming-invariant equality checking ===

type AlphaEq e = AlphaEqE e  :: Constraint

checkAlphaEq :: AlphaEqE e => MonadErr1 m => ScopeReader m
             => e n -> e n -> m n ()
checkAlphaEq e1 e2 = do
  scope <- askScope
  liftEither $ runReaderT (runZipSubstM $ alphaEqE e1 e2) (idZipSubstEnv scope)

data ZipSubstEnv i1 i2 o = ZipSubstEnv
  { zSubst1 :: Env Name i1 o
  , zSubst2 :: Env Name i2 o
  , zScope  :: Scope o }

class AlphaEqE (e::E) where
  alphaEqE :: MonadZipSubst m => e i1 -> e i2 -> m i1 i2 o ()

class AlphaEqB (b::B) where
  withAlphaEqB :: MonadZipSubst m => b i1 i1' -> b i2 i2'
               -> (forall o'. m i1' i2' o' a)
               ->             m i1  i2  o  a

-- TODO: consider generalizing this to something that can also handle e.g.
-- unification and type checking with some light reduction
class (forall i1 i2 o. MonadErr (m i1 i2 o))
      => MonadZipSubst (m :: S -> S -> S -> * -> *) where
  askZipSubstEnv :: m i1 i2 o (ZipSubstEnv i1 i2 o)
  withZipSubstEnv :: ZipSubstEnv i1' i2' o'
             -> m i1' i2' o' a
             -> m i1  i2  o  a

newtype ZipSubstM i1 i2 o a =
  ZipSubstM { runZipSubstM :: (ReaderT (ZipSubstEnv i1 i2 o) Except a) }
  deriving (Functor, Applicative, Monad)

instance MonadError Err (ZipSubstM i1 i2 o) where
  throwError e = ZipSubstM $ throwError e
  catchError (ZipSubstM m) f = ZipSubstM $ catchError m $ runZipSubstM . f

instance MonadZipSubst ZipSubstM where
  askZipSubstEnv = ZipSubstM ask
  withZipSubstEnv env (ZipSubstM m) = ZipSubstM $ lift $ runReaderT m env

idZipSubstEnv :: Scope n -> ZipSubstEnv n n n
idZipSubstEnv scope = ZipSubstEnv env env scope
  where env = idRenameEnv scope

alphaEqTraversable :: (AlphaEqE e, Traversable f, Eq (f ()))
                   => MonadZipSubst m
                   => f (e i1) -> f (e i2) -> m i1 i2 o ()
alphaEqTraversable f1 f2 = do
  let (struct1, vals1) = splitTraversable f1
  let (struct2, vals2) = splitTraversable f2
  unless (struct1 == struct2) zipErr
  zipWithM_ alphaEqE vals1 vals2
  where
    splitTraversable :: Traversable f => f a -> (f (), [a])
    splitTraversable xs = runWriter $ forM xs \x -> tell [x]

instance Typeable s => AlphaEqE (Name s) where
  alphaEqE v1 v2 = do
    ZipSubstEnv env1 env2 _ <- askZipSubstEnv
    if env1!v1 == env2!v2
      then return ()
      else zipErr

instance AlphaEqB b => AlphaEqB (Nest b) where
  withAlphaEqB Empty Empty cont = cont
  withAlphaEqB (Nest b1 rest1) (Nest b2 rest2) cont =
    withAlphaEqB b1 b2 $ withAlphaEqB rest1 rest2 $ cont
  withAlphaEqB _ _ _ = zipErr

instance (AlphaEqB b1, AlphaEqB b2) => AlphaEqB (NestPair b1 b2) where
  withAlphaEqB (NestPair a1 b1) (NestPair a2 b2) cont =
    withAlphaEqB a1 a2 $ withAlphaEqB b1 b2 $ cont

instance (AlphaEqB b, AlphaEqE e) => AlphaEqE (Abs b e) where
  alphaEqE (Abs b1 e1) (Abs b2 e2) = withAlphaEqB b1 b2 $ alphaEqE e1 e2

instance AlphaEqE UnitE where
  alphaEqE UnitE UnitE = return ()

instance (AlphaEqE e1, AlphaEqE e2) => AlphaEqE (PairE e1 e2) where
  alphaEqE (PairE a1 b1) (PairE a2 b2) = alphaEqE a1 a2 >> alphaEqE b1 b2

-- === instances ===

instance Typeable s => HasNamesE (Name s) where
  traverseNamesE _ t name = lookupNameTraversal t name

instance (HasNamesB b, HasNamesE e) => HasNamesE (Abs b e) where
  traverseNamesE s t (Abs b body) = do
    traverseNamesB s t b \s' t' b' ->
      Abs b' <$> traverseNamesE s' t' body

instance (SubstB v b, SubstE v e) => SubstE v (Abs b e) where
  substE (Abs b body) = substB b \b' -> Abs b' <$> substE body

instance SubstB v b => SubstB v (Nest b) where
  substB Empty cont = cont Empty
  substB (Nest b r) cont = substB b \b' -> substB r \r' -> cont $ Nest b' r'

instance (HasNamesB b1, HasNamesB b2) => HasNamesB (NestPair b1 b2) where
  traverseNamesB s t (NestPair b1 b2) cont =
    traverseNamesB s t b1 \s' t' b1' ->
      traverseNamesB s' t' b2 \s'' t'' b2' ->
        cont s'' t'' (NestPair b1' b2')

instance HasNamesB b => HasNamesB (Nest b) where
  traverseNamesB s t nest cont = case nest of
    Empty -> cont s t Empty
    Nest b rest ->
      traverseNamesB s t b \s' t' b' ->
        traverseNamesB s' t' rest \s'' t'' rest' ->
          cont s'' t'' $ Nest b' rest'

instance HasNamesE UnitE where
  traverseNamesE _ _ UnitE = return UnitE

instance (HasNamesE e1, HasNamesE e2) => HasNamesE (PairE e1 e2) where
  traverseNamesE s env (PairE x y) =
    PairE <$> traverseNamesE s env x <*> traverseNamesE s env y

instance (forall n' l. Show (b n' l), forall n'. Show (body n')) => Show (Abs b body n) where
  show (Abs b body) = "(Abs " <> show b <> " " <> show body <> ")"

instance (forall n' l'. Show (b n' l')) => Show (Nest b n l) where
  show Empty = ""
  show (Nest b rest) = "(Nest " <> show b <> " in " <> show rest <> ")"

instance (PrettyB b, PrettyE ann) => Pretty (AnnBinderP b ann n l) where
  pretty _ = "TODO"

instance (PrettyB b) => Pretty (Nest b n l) where
  pretty _ = "TODO"

instance (PrettyB b, PrettyE e) => Pretty (Abs b e n) where
  pretty _ = "TODO"

instance (ShowB b, ShowE ann) => Show (AnnBinderListP b ann n l) where
  show _ = "TODO"

instance Pretty a => Pretty (LiftE a n) where
  pretty (LiftE x) = pretty x
