-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE InstanceSigs #-}

module SaferNames.Name (
  Name (..), RawName, S (..), C (..), Env, (<.>), EnvFrag (..), NameBinder (..),
  EnvReader (..), FromName (..), Distinct, DistinctWitness (..),
  Ext, ExtEvidence, ProvesExt (..), withExtEvidence, getExtEvidence, getScopeProxy,
  NameFunction (..), emptyNameFunction, idNameFunction, newNameFunction,
  DistinctAbs (..), WithScope (..),
  extendRenamer, ScopeReader (..), ScopeExtender (..), ScopeGetter (..),
  Scope, ScopeFrag (..), SubstE (..), SubstB (..), SubstV, MonadicVal (..), lookupSustTraversalEnv,
  Inplace, liftInplace, runInplace,
  E, B, V, HasNamesE, HasNamesB, BindsNames (..), RecEnvFrag (..),
  BindsOneName (..), BindsAtMostOneName (..), BindsNameList (..), NameColorRep (..),
  Abs (..), Nest (..), PairB (..), UnitB (..),
  IsVoidS (..), UnitE (..), VoidE, PairE (..), ListE (..), ComposeE (..),
  EitherE (..), LiftE (..), EqE, EqB, OrdE, OrdB,
  EitherB (..), BinderP (..),
  LiftB, pattern LiftB,
  MaybeE, pattern JustE, pattern NothingE, MaybeB, pattern JustB, pattern NothingB,
  fromConstAbs, toConstAbs, PrettyE, PrettyB, ShowE, ShowB,
  runScopeReaderT, runEnvReaderT, ScopeReaderT (..), EnvReaderT (..),
  lookupEnvM, dropSubst, extendEnv,
  MonadKind, MonadKind1, MonadKind2,
  Monad1, Monad2, Fallible1, Fallible2, MonadFail1, MonadFail2,
  ScopeReader2, ScopeExtender2,
  applyAbs, applyNaryAbs, ZipEnvReader (..), alphaEqTraversable,
  checkAlphaEq, AlphaEq, AlphaEqE (..), AlphaEqB (..), AlphaEqV, ConstE (..),
  InjectableE (..), InjectableB (..), InjectableV, InjectionCoercion,
  withFreshM, withFreshLike, inject, injectM, injectMVia, (!), (<>>), emptyEnv, envAsScope,
  EmptyAbs, pattern EmptyAbs, SubstVal (..), lookupEnv,
  NameGen (..), fmapG, NameGenT (..), traverseEnvFrag, forEachNestItem,
  substM, ScopedEnvReader, runScopedEnvReader,
  HasNameHint (..), HasNameColor (..), NameHint (..), NameColor (..),
  GenericE (..), GenericB (..), ColorsEqual (..),
  EitherE1, EitherE2, EitherE3, EitherE4, EitherE5,
  pattern Case0, pattern Case1, pattern Case2, pattern Case3, pattern Case4,
  splitNestAt, nestLength, nestToList, binderAnn,
  OutReaderT (..), OutReader (..), runOutReaderT, getDistinct,
  ExtWitness (..), idExt, injectExt
  ) where

import Prelude hiding (id, (.))
import Control.Category
import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Except hiding (Except)
import Control.Monad.Reader
import Control.Monad.Writer.Strict
import Data.String
import Data.Text.Prettyprint.Doc  hiding (nest)
import GHC.Exts (Constraint)
import GHC.Generics (Generic (..), Rep)
import Data.Store (Store)

import SaferNames.NameCore
import Util (zipErr, onFst, onSnd)
import Err

-- === environments and scopes ===

data NameFunction v i o where
  NameFunction
    :: (forall c. Name c hidden -> v c o)
    -> EnvFrag v hidden i o
    -> NameFunction v i o

newNameFunction :: (forall c. Name c i -> v c o) -> NameFunction v i o
newNameFunction f = NameFunction f emptyEnv

emptyNameFunction :: NameFunction v VoidS o
emptyNameFunction = newNameFunction absurdNameFunction

idNameFunction :: FromName v => NameFunction v n n
idNameFunction = newNameFunction fromName

-- === monadic type classes for reading and extending envs and scopes ===

data WithScope (e::E) (n::S) where
  WithScope :: (Distinct l, Ext l n) => Scope l -> e l -> WithScope e n

instance InjectableE e => InjectableE (WithScope e) where
  injectionProofE (fresh::InjectionCoercion n l) (WithScope (scope::Scope h) e) =
    withExtEvidence (injectionProofE fresh ext) $
      WithScope scope e
    where ext = getExtEvidence :: ExtEvidence h n

-- Similar functionality to ScopeGetter, but suitable for InPlace
class Monad1 m => ScopeReader (m::MonadKind1) where
  getDistinctEvidenceM :: m n (DistinctEvidence n)
  addScope :: InjectableE e => e n -> m n (WithScope e n)

-- Unrestricted scope access
class ScopeReader m => ScopeGetter (m::MonadKind1) where
  getScope :: m n (Scope n)

class ScopeGetter m => ScopeExtender (m::MonadKind1) where
  extendScope :: Distinct l => ScopeFrag n l -> (Ext n l => m l r) -> m n r

class (InjectableV v, Monad2 m) => EnvReader (v::V) (m::MonadKind2) | m -> v where
   getEnv :: m i o (NameFunction v i o)
   withEnv :: NameFunction v i' o -> m i' o a -> m i o a

lookupEnvM :: EnvReader v m => Name c i -> m i o (v c o)
lookupEnvM name = (!name) <$> getEnv

dropSubst :: (EnvReader v m, FromName v) => m o o r -> m i o r
dropSubst cont = withEnv idNameFunction cont

extendEnv :: EnvReader v m => EnvFrag v i i' o -> m i' o r -> m i o r
extendEnv frag cont = do
  newEnv <- (<>>frag) <$> getEnv
  withEnv newEnv cont

-- === extending envs with name-only substitutions ===

class FromName (v::V) where
  fromName :: Name c n -> v c n

instance FromName Name where
  fromName = id

instance FromName (SubstVal c v) where
  fromName = Rename

extendRenamer :: (EnvReader v m, FromName v) => EnvFrag Name i i' o -> m i' o r -> m i o r
extendRenamer frag = extendEnv (fmapEnvFrag (const fromName) frag)

-- === common scoping patterns ===

data Abs (binder::B) (body::E) (n::S) where
  Abs :: binder n l -> body l -> Abs binder body n
deriving instance (ShowB b, ShowE e) => Show (Abs b e n)

data BinderP (b::B) (ann::E) (n::S) (l::S) =
  (:>) (b n l) (ann n)
  deriving (Show, Generic)

type EmptyAbs b = Abs b UnitE :: E
pattern EmptyAbs :: b n l -> EmptyAbs b n
pattern EmptyAbs bs = Abs bs UnitE

-- wraps an EnvFrag as a kind suitable for SubstB instances etc
newtype RecEnvFrag (v::V) n l = RecEnvFrag { fromRecEnvFrag :: EnvFrag v n l l }

-- Proof object that a given scope is void
data IsVoidS n where
  IsVoidS :: IsVoidS VoidS

-- === Injections and projections ===

class ProvesExt (b :: B) where
  toExtEvidence :: b n l -> ExtEvidence n l

  default toExtEvidence :: BindsNames b => b n l -> ExtEvidence n l
  toExtEvidence b = toExtEvidence $ toScopeFrag b

class ProvesExt b => BindsNames (b :: B) where
  toScopeFrag :: b n l -> ScopeFrag n l

  default toScopeFrag :: (GenericB b, BindsNames (RepB b)) => b n l -> ScopeFrag n l
  toScopeFrag b = toScopeFrag $ fromB b

instance ProvesExt ExtEvidence where
  toExtEvidence = id

instance ProvesExt ScopeFrag
instance BindsNames ScopeFrag where
  toScopeFrag s = s

withExtEvidence :: ProvesExt b => b n l -> (Ext n l => a) -> a
withExtEvidence b cont = withExtEvidence' (toExtEvidence b) cont

-- like inject, but uses the ScopeReader monad for its `Distinct` proof
injectM :: (ScopeReader m, Ext n l, InjectableE e) => e n -> m l (e l)
injectM e = do
  Distinct <- getDistinct
  return $ inject e

data ExtWitness (n::S) (l::S) where
  ExtW :: Ext n l => ExtWitness n l

instance ProvesExt ExtWitness where
  toExtEvidence ExtW = getExtEvidence

instance Category ExtWitness where
  id :: forall n. ExtWitness n n
  id = withExtEvidence (id::ExtEvidence n n) ExtW

  (.) :: forall n1 n2 n3. ExtWitness n2 n3 -> ExtWitness n1 n2 -> ExtWitness n1 n3
  (.) ExtW ExtW = withExtEvidence (ext1 >>> ext2) ExtW
     where ext1 = getExtEvidence :: ExtEvidence n1 n2
           ext2 = getExtEvidence :: ExtEvidence n2 n3

idExt :: Monad1 m => m n (ExtWitness n n)
idExt = return id

injectExt :: (ProvesExt ext, Ext n2 n3, ScopeReader m)
          => ext n1 n2 -> m n3 (ExtWitness n1 n3)
injectExt ext = do
  ext' <- injectM $ toExtEvidence ext
  withExtEvidence ext' $
    return ExtW

-- Uses `proxy n2` to provide the type `n2` to use as the intermediate scope.
injectMVia :: forall n1 n2 n3 m proxy e.
              (Ext n1 n2, Ext n2 n3, ScopeReader m, InjectableE e)
           => proxy n2 -> e n1 -> m n3 (e n3)
injectMVia _ e = withExtEvidence (extL >>> extR) $ injectM e
  where extL = getExtEvidence :: ExtEvidence n1 n2
        extR = getExtEvidence :: ExtEvidence n2 n3

getScopeProxy :: Monad (m n) => m n (UnitE n)
getScopeProxy = return UnitE

traverseNames :: forall m v e i o.
                 (Monad m, SubstE v e)
              => Distinct o => Scope o -> (forall c. Name c i -> m (v c o)) -> e i -> m (e o)
traverseNames scope f e = substE (newNameFunction f', scope) e
  where f' :: forall c. Name c i -> MonadicVal m v c o
        f' x = MonadicVal $ f x

fmapNames :: forall v e i o.
             SubstE v e
          => Distinct o => Scope o -> (forall c. Name c i -> v c o) -> e i -> e o
fmapNames scope f e = runIdentity $ traverseNames scope (return . f) e

-- This may become expensive. It traverses the body of the Abs to check for
-- leaked variables.
fromConstAbs :: (ScopeReader m, MonadFail1 m, InjectableB b, BindsNames b, HasNamesE e)
             => Abs b e n -> m n (e n)
fromConstAbs ab = do
  WithScope scope (Abs b e) <- addScope ab
  injectM =<< traverseNames scope (tryProjectName $ toScopeFrag b) e

tryProjectName :: MonadFail m => ScopeFrag n l -> Name c l -> m (Name c n)
tryProjectName names name =
  case projectName names name of
    Left name' -> return name'
    Right _    -> fail $ "Escaped name: " <> pprint name

toConstAbs :: (InjectableE e, ScopeReader m)
           => NameColorRep c -> e n -> m n (Abs (NameBinder c) e n)
toConstAbs rep body = do
  WithScope scope body' <- addScope body
  withFresh "ignore" rep scope \b -> do
    injectM $ Abs b $ inject body'

-- === type classes for traversing names ===

-- composes a monad-kinded type with a V-kinded type
newtype MonadicVal (m::MonadKind) (v::V) (c::C) (n::S) =
  MonadicVal { fromMonadicVal :: (m (v c n)) }

instance InjectableV v => InjectableV (MonadicVal m v)
instance (NameColor c, InjectableV v) => InjectableE (MonadicVal m v c) where
  injectionProofE = undefined

type SubstTraversalEnv (m::MonadKind) (v::V) (i::S) (o::S) =
       (NameFunction (MonadicVal m v) i o, Scope o)

lookupSustTraversalEnv :: SubstTraversalEnv m v i o -> Name c i -> m (v c o)
lookupSustTraversalEnv (env, _) v = fromMonadicVal $ env ! v

class (FromName v, InjectableE e) => SubstE (v::V) (e::E) where
  -- TODO: can't make an alias for these constraints because of impredicativity
  substE :: (Monad m, Distinct o)
         => SubstTraversalEnv m v i o -> e i -> m (e o)

  default substE :: (GenericE e, SubstE v (RepE e))
                 => (Monad m, Distinct o)
                 => SubstTraversalEnv m v i o -> e i -> m (e o)
  substE env e = toE <$> substE env (fromE e)

class (FromName v, InjectableB b) => SubstB (v::V) (b::B) where
  substB :: (Monad m, Distinct o)
         => SubstTraversalEnv m v i o
         -> b i i'
         -> (forall o'. Distinct o' => SubstTraversalEnv m v i' o' -> b o o' -> m a)
         -> m a

  default substB :: (GenericB b, SubstB v (RepB b))
                 => (Monad m, Distinct o)
                 => SubstTraversalEnv m v i o
                 -> b i i'
                 -> (forall o'. Distinct o' => SubstTraversalEnv m v i' o' -> b o o' -> m a)
                 -> m a
  substB env b cont = substB env (fromB b) \env' b' -> cont env' $ toB b'

class ( FromName substVal, InjectableV v
      , forall c. NameColor c => SubstE substVal (v c))
      => SubstV (substVal::V) (v::V)

type HasNamesE = SubstE Name
type HasNamesB = SubstB Name

instance SubstV Name Name where
instance SubstE Name (Name c) where
  substE env name = lookupSustTraversalEnv env name

instance (InjectableV v, FromName v) => SubstB v (NameBinder c) where
  substB (env, scope) b cont = do
    let rep = getNameColorRep $ nameBinderName b
    withFresh (getNameHint b) rep scope \b' -> do
      let env' = inject env <>> b @> (MonadicVal $ return $ fromName $ binderName b')
      let scope' = scope >>> singletonScope b'
      cont (env', scope') b'

substM :: (EnvReader v m, ScopeReader2 m, SubstE v e, FromName v)
       => e i -> m i o (e o)
substM e = do
  env <- getEnv
  WithScope scope env' <- addScope env
  injectM $ fmapNames scope (env'!) e

-- === various E-kind and B-kind versions of standard containers and classes ===

type PrettyE  e = (forall (n::S)       . Pretty (e n  )) :: Constraint
type PrettyB b  = (forall (n::S) (l::S). Pretty (b n l)) :: Constraint

type ShowE e = (forall (n::S)       . Show (e n  )) :: Constraint
type ShowB b = (forall (n::S) (l::S). Show (b n l)) :: Constraint

type EqE e = (forall (n::S)       . Eq (e n  )) :: Constraint
type EqB b = (forall (n::S) (l::S). Eq (b n l)) :: Constraint

type OrdE e = (forall (n::S)       . Ord (e n  )) :: Constraint
type OrdB b = (forall (n::S) (l::S). Ord (b n l)) :: Constraint

data UnitE (n::S) = UnitE
     deriving (Show, Eq, Generic)

data VoidE (n::S)
     deriving (Generic)

data PairE (e1::E) (e2::E) (n::S) = PairE (e1 n) (e2 n)
     deriving (Show, Eq, Generic)

data EitherE (e1::E) (e2::E) (n::S) = LeftE (e1 n) | RightE (e2 n)
     deriving (Show, Eq, Generic)

newtype ListE (e::E) (n::S) = ListE { fromListE :: [e n] }
        deriving (Show, Eq, Generic)

newtype LiftE (a:: *) (n::S) = LiftE { fromLiftE :: a }
        deriving (Show, Eq, Generic)

newtype ComposeE (f :: * -> *) (e::E) (n::S) =
  ComposeE (f (e n))
  deriving (Show, Eq, Generic)

data UnitB (n::S) (l::S) where
  UnitB :: UnitB n n
deriving instance Show (UnitB n l)

data PairB (b1::B) (b2::B) (n::S) (l::S) where
  PairB :: b1 n l' -> b2 l' l -> PairB b1 b2 n l
deriving instance (ShowB b1, ShowB b2) => Show (PairB b1 b2 n l)

data EitherB (b1::B) (b2::B) (n::S) (l::S) =
   LeftB  (b1 n l)
 | RightB (b2 n l)
   deriving (Show, Eq, Generic)

-- The constant function of kind `V`
newtype ConstE (const::E) (ignored::C) (n::S) = ConstE (const n)
        deriving (Show, Eq, Generic)

type MaybeE e = EitherE e UnitE

pattern JustE :: e n -> MaybeE e n
pattern JustE e = LeftE e

pattern NothingE :: MaybeE e n
pattern NothingE = RightE UnitE

type MaybeB b = EitherB b UnitB

pattern JustB :: b n l -> MaybeB b n l
pattern JustB b = LeftB b

-- TODO: this doesn't seem to force n==n, e.g. see where we have to explicitly
-- write `RightB UnitB` in inference rule for instances.
pattern NothingB :: MaybeB b n n
pattern NothingB = RightB UnitB

type LiftB (e::E) = BinderP UnitB e :: B

pattern LiftB :: e n -> LiftB e n n
pattern LiftB e = UnitB :> e

-- -- === various convenience utilities ===

infixr 7 @>
class BindsAtMostOneName (b::B) (c::C) | b -> c where
  (@>) :: b i i' -> v c o -> EnvFrag v i i' o

class BindsAtMostOneName (b::B) (c::C)
  =>  BindsOneName (b::B) (c::C) | b -> c where
  binderName :: b i i' -> Name c i'

instance ProvesExt  (NameBinder c) where
instance BindsNames (NameBinder c) where
  toScopeFrag b = singletonScope b

instance BindsAtMostOneName (NameBinder c) c where
  b @> x = singletonEnv b x

instance BindsOneName (NameBinder c) c where
  binderName = nameBinderName

instance BindsAtMostOneName b c => BindsAtMostOneName (BinderP b ann) c where
  (b:>_) @> x = b @> x

instance BindsOneName b c => BindsOneName (BinderP b ann) c where
  binderName (b:>_) = binderName b

infixr 7 @@>
class BindsNameList (b::B) (c::C) | b -> c where
  (@@>) :: b i i' -> [v c o] -> EnvFrag v i i' o

instance BindsAtMostOneName b c => BindsNameList (Nest b) c where
  (@@>) Empty [] = emptyEnv
  (@@>) (Nest b rest) (x:xs) = b@>x <.> rest@@>xs
  (@@>) _ _ = error "length mismatch"

applySubst :: (ScopeReader m, SubstE v e, InjectableV v, FromName v)
           => EnvFrag v o i o -> e i -> m o (e o)
applySubst substFrag x = do
  let fullSubst = idNameFunction <>> substFrag
  WithScope scope fullSubst' <- addScope fullSubst
  injectM $ fmapNames scope (fullSubst' !) x

applyAbs :: (InjectableV v, FromName v, ScopeReader m, BindsOneName b c, SubstE v e)
         => Abs b e n -> v c n -> m n (e n)
applyAbs (Abs b body) x = applySubst (b@>x) body

applyNaryAbs :: ( InjectableV v, FromName v, ScopeReader m, BindsNameList b c, SubstE v e
                , SubstB v b, InjectableE e)
             => Abs b e n -> [v c n] -> m n (e n)
applyNaryAbs (Abs bs body) xs = applySubst (bs @@> xs) body

infixl 9 !
(!) :: NameFunction v i o -> Name c i -> v c o
(!) (NameFunction f env) name =
  case lookupEnvFragProjected env name of
    Left name' -> f name'
    Right val -> val

infixl 1 <>>
(<>>) :: NameFunction v i o -> EnvFrag v i i' o -> NameFunction v i' o
(<>>) (NameFunction f frag) frag' = NameFunction f $ frag <.> frag'

lookupEnvFragProjected :: EnvFrag v i i' o -> Name c i' -> Either (Name c i) (v c o)
lookupEnvFragProjected m name =
  case projectName (envAsScope m) name of
    Left  name' -> Left name'
    Right name' -> Right $ lookupEnvFrag m name'

forEachNestItem :: Monad m
                => Nest b i i'
                -> (forall ii ii'. b ii ii' -> m (b' ii ii'))
                -> m (Nest b' i i')
forEachNestItem Empty _ = return Empty
forEachNestItem (Nest b rest) f = Nest <$> f b <*> forEachNestItem rest f

-- TODO: make a more general E-kinded Traversable?
traverseEnvFrag :: forall v v' i i' o o' m .
                   Monad m
                => (forall c. NameColor c => v c o -> m (v' c o'))
                -> EnvFrag v i i' o  -> m (EnvFrag v' i i' o')
traverseEnvFrag f frag = liftM fromEnvPairs $
  forEachNestItem (toEnvPairs frag) \(EnvPair b val) ->
    EnvPair b <$> f val

nestLength :: Nest b n l -> Int
nestLength Empty = 0
nestLength (Nest _ rest) = 1 + nestLength rest

nestToList :: (forall n' l'. b n' l' -> a) -> Nest b n l -> [a]
nestToList _ Empty = []
nestToList f (Nest b rest) = f b : nestToList f rest

splitNestAt :: Int -> Nest b n l -> PairB (Nest b) (Nest b) n l
splitNestAt 0 bs = PairB Empty bs
splitNestAt _  Empty = error "split index too high"
splitNestAt n (Nest b rest) =
  case splitNestAt (n-1) rest of
    PairB xs ys -> PairB (Nest b xs) ys

binderAnn :: BinderP b ann n l -> ann n
binderAnn (_:>ann) = ann


data DistinctWitness (n::S) where
  Distinct :: Distinct n => DistinctWitness n

getDistinct :: ScopeReader m => m n (DistinctWitness n)
getDistinct = do
  d <- getDistinctEvidenceM
  return $ withDistinctEvidence d Distinct

-- === versions of monad constraints with scope params ===

type MonadKind  =           * -> *
type MonadKind1 =      S -> * -> *
type MonadKind2 = S -> S -> * -> *

type Monad1 (m :: MonadKind1) = forall (n::S)        . Monad (m n  )
type Monad2 (m :: MonadKind2) = forall (n::S) (l::S) . Monad (m n l)

type Fallible1 (m :: MonadKind1) = forall (n::S)        . Fallible (m n  )
type Fallible2 (m :: MonadKind2) = forall (n::S) (l::S) . Fallible (m n l)

type MonadFail1 (m :: MonadKind1) = forall (n::S)        . MonadFail (m n  )
type MonadFail2 (m :: MonadKind2) = forall (n::S) (l::S) . MonadFail (m n l)

type ScopeReader2      (m::MonadKind2) = forall (n::S). ScopeReader      (m n)
type ScopeExtender2    (m::MonadKind2) = forall (n::S). ScopeExtender    (m n)

-- === subst monad ===

-- Only alllows non-trivial substitution with names that match the parameter
-- `cMatch`. For example, this lets us substitute ordinary variables in Core
-- with Atoms, while ensuring that things like data def names only get renamed.
data SubstVal (cMatch::C) (atom::E) (c::C) (n::S) where
  SubstVal :: atom n   -> SubstVal c      atom c n
  Rename   :: Name c n -> SubstVal cMatch atom c n

withFreshM :: (ScopeGetter m, ScopeExtender m)
           => NameHint
           -> NameColorRep c
           -> (forall o'. (Distinct o', Ext o o')
                          => NameBinder c o o' -> m o' a)
           -> m o a
withFreshM hint rep cont = do
  Distinct <- getDistinct
  m <- getScope
  withFresh hint rep m \b' -> do
    extendScope (singletonScope b') $
      cont b'

withFreshLike
  :: (ScopeGetter m, ScopeExtender m, HasNameHint hint, HasNameColor hint c)
  => hint
  -> (forall o'. NameBinder c o o' -> m o' a)
  -> m o a
withFreshLike hint cont =
  withFreshM (getNameHint hint) (getNameColor hint) cont

data ColorsEqual (a::C) (b::C) where
  ColorsEqual :: ColorsEqual a a
class ColorsNotEqual a b where
  notEqProof :: ColorsEqual a b -> r

instance (ColorsNotEqual cMatch c)
         => (SubstE (SubstVal cMatch atom) (Name c)) where
  substE env name = do
    substVal <- lookupSustTraversalEnv env name
    case substVal of
      Rename name' -> return name'
      SubstVal _ -> notEqProof (ColorsEqual :: ColorsEqual c cMatch)

-- TODO: we can fill out the full (N^2) set of instances if we need to
instance ColorsNotEqual AtomNameC DataDefNameC where notEqProof = \case
instance ColorsNotEqual AtomNameC ClassNameC   where notEqProof = \case

-- === alpha-renaming-invariant equality checking ===

type AlphaEq e = AlphaEqE e  :: Constraint

-- TODO: consider generalizing this to something that can also handle e.g.
-- unification and type checking with some light reduction
class ( forall i1 i2 o. Monad (m i1 i2 o)
      , forall i1 i2 o. Fallible (m i1 i2 o)
      , forall i1 i2 o. MonadFail (m i1 i2 o)
      , forall i1 i2.   ScopeGetter (m i1 i2)
      , forall i1 i2.   ScopeExtender (m i1 i2))
      => ZipEnvReader (m :: S -> S -> S -> * -> *) where
  lookupZipEnvFst :: Name c i1 -> m i1 i2 o (Name c o)
  lookupZipEnvSnd :: Name c i2 -> m i1 i2 o (Name c o)

  extendZipEnvFst :: EnvFrag Name i1 i1' o -> m i1' i2  o r -> m i1 i2 o r
  extendZipEnvSnd :: EnvFrag Name i2 i2' o -> m i1  i2' o r -> m i1 i2 o r

  withEmptyZipEnv :: m o o o a -> m i1 i2 o a

class InjectableE e => AlphaEqE (e::E) where
  alphaEqE :: ZipEnvReader m => e i1 -> e i2 -> m i1 i2 o ()

  default alphaEqE :: (GenericE e, AlphaEqE (RepE e), ZipEnvReader m)
                   => e i1 -> e i2 -> m i1 i2 o ()
  alphaEqE e1 e2 = fromE e1 `alphaEqE` fromE e2

class InjectableB b => AlphaEqB (b::B) where
  withAlphaEqB :: ZipEnvReader m => b i1 i1' -> b i2 i2'
               -> (forall o'. m i1' i2' o' a)
               ->             m i1  i2  o  a

  default withAlphaEqB :: (GenericB b, AlphaEqB (RepB b), ZipEnvReader m)
                       => b i1 i1' -> b i2 i2'
                       -> (forall o'. m i1' i2' o' a)
                       ->             m i1  i2  o  a
  withAlphaEqB b1 b2 cont = withAlphaEqB (fromB b1) (fromB b2) $ cont

class ( InjectableV v
      , forall c. NameColor c => AlphaEqE (v c))
      => AlphaEqV (v::V) where

checkAlphaEq :: (AlphaEqE e, Fallible1 m, ScopeReader m)
             => e n -> e n -> m n ()
checkAlphaEq e1 e2 = do
  WithScope scope (PairE e1' e2') <- addScope $ PairE e1 e2
  liftExcept $
    runScopeReaderT scope $
      flip runReaderT (emptyNameFunction, emptyNameFunction) $ runZipEnvReaderT $
        withEmptyZipEnv $ alphaEqE e1' e2'

instance AlphaEqV Name
instance AlphaEqE (Name c) where
  alphaEqE v1 v2 = do
    v1' <- lookupZipEnvFst v1
    v2' <- lookupZipEnvSnd v2
    unless (v1' == v2') zipErr

instance AlphaEqB (NameBinder c) where
  withAlphaEqB b1 b2 cont = do
    withFreshLike b1 \b -> do
      let v = binderName b
      extendZipEnvFst (b1@>v) $ extendZipEnvSnd (b2@>v) $ cont

alphaEqTraversable :: (AlphaEqE e, Traversable f, Eq (f ()), ZipEnvReader m)
                   => f (e i1) -> f (e i2) -> m i1 i2 o ()
alphaEqTraversable f1 f2 = do
  let (struct1, vals1) = splitTraversable f1
  let (struct2, vals2) = splitTraversable f2
  unless (struct1 == struct2) zipErr
  zipWithM_ alphaEqE vals1 vals2
  where
    splitTraversable :: Traversable f => f a -> (f (), [a])
    splitTraversable xs = runWriter $ forM xs \x -> tell [x]

instance AlphaEqB b => AlphaEqB (Nest b) where
  withAlphaEqB Empty Empty cont = cont
  withAlphaEqB (Nest b1 rest1) (Nest b2 rest2) cont =
    withAlphaEqB b1 b2 $ withAlphaEqB rest1 rest2 $ cont
  withAlphaEqB _ _ _ = zipErr

instance (AlphaEqB b1, AlphaEqB b2) => AlphaEqB (PairB b1 b2) where
  withAlphaEqB (PairB a1 b1) (PairB a2 b2) cont =
    withAlphaEqB a1 a2 $ withAlphaEqB b1 b2 $ cont

instance (AlphaEqB b, AlphaEqE e) => AlphaEqE (Abs b e) where
  alphaEqE (Abs b1 e1) (Abs b2 e2) = withAlphaEqB b1 b2 $ alphaEqE e1 e2

instance (AlphaEqB b, AlphaEqE ann) => AlphaEqB (BinderP b ann) where
  withAlphaEqB (b1:>ann1) (b2:>ann2) cont = do
    alphaEqE ann1 ann2
    withAlphaEqB b1 b2 $ cont

instance AlphaEqE UnitE where
  alphaEqE UnitE UnitE = return ()

instance (AlphaEqE e1, AlphaEqE e2) => AlphaEqE (PairE e1 e2) where
  alphaEqE (PairE a1 b1) (PairE a2 b2) = alphaEqE a1 a2 >> alphaEqE b1 b2

instance (AlphaEqE e1, AlphaEqE e2) => AlphaEqE (EitherE e1 e2) where
  alphaEqE (LeftE  e1) (LeftE  e2) = alphaEqE e1 e2
  alphaEqE (RightE e1) (RightE e2) = alphaEqE e1 e2
  alphaEqE (LeftE  _ ) (RightE _ ) = zipErr
  alphaEqE (RightE _ ) (LeftE  _ ) = zipErr

-- === ScopeReaderT transformer ===

newtype ScopeReaderT (m::MonadKind) (n::S) (a:: *) =
  ScopeReaderT {runScopeReaderT' :: ReaderT (DistinctEvidence n, Scope n) m a}
  deriving (Functor, Applicative, Monad, MonadFail, Fallible)

runScopeReaderT :: Distinct n => Scope n -> ScopeReaderT m n a -> m a
runScopeReaderT scope m =
  flip runReaderT (getDistinctEvidence, scope) $ runScopeReaderT' m

instance Monad m => ScopeReader (ScopeReaderT m) where
  getDistinctEvidenceM = ScopeReaderT $ asks fst
  addScope e = ScopeReaderT do
    (d, scope) <- ask
    withDistinctEvidence d $
      return $ WithScope scope e


instance Monad m => ScopeGetter (ScopeReaderT m) where
  getScope = ScopeReaderT $ asks snd

instance Monad m => ScopeExtender (ScopeReaderT m) where
  extendScope frag m = ScopeReaderT $ withReaderT
    (\(_, scope) -> (getDistinctEvidence, scope >>> frag)) $
        withExtEvidence (toExtEvidence frag) $
          runScopeReaderT' m

-- === EnvReaderT transformer ===

newtype EnvReaderT (v::V) (m::MonadKind1) (i::S) (o::S) (a:: *) =
  EnvReaderT { runEnvReaderT' :: ReaderT (NameFunction v i o) (m o) a }
  deriving (Functor, Applicative, Monad, MonadFail, Fallible)

type ScopedEnvReader (v::V) = EnvReaderT v (ScopeReaderT Identity) :: MonadKind2

runScopedEnvReader :: Distinct o => Scope o -> NameFunction v i o
                   -> ScopedEnvReader v i o a -> a
runScopedEnvReader scope env m =
  runIdentity $ runScopeReaderT scope $ runEnvReaderT env m

runEnvReaderT :: NameFunction v i o -> EnvReaderT v m i o a -> m o a
runEnvReaderT env m = runReaderT (runEnvReaderT' m) env


instance (InjectableV v, Monad1 m) => EnvReader v (EnvReaderT v m) where
  getEnv = EnvReaderT ask
  withEnv newEnv (EnvReaderT cont) = EnvReaderT $ withReaderT (const newEnv) cont

instance ScopeReader m => ScopeReader (EnvReaderT v m i) where
  addScope e = EnvReaderT $ lift $ addScope e
  getDistinctEvidenceM = EnvReaderT $ lift getDistinctEvidenceM

instance ScopeGetter m => ScopeGetter (EnvReaderT v m i) where
  getScope = EnvReaderT $ lift getScope

-- The rest are boilerplate but this one is a bit interesting. When we extend
-- the scope we have to inject the env, `Env i o` into the new scope, to become
-- `Env i oNew `
instance (InjectableV v, ScopeReader m, ScopeExtender m)
         => ScopeExtender (EnvReaderT v m i) where
  extendScope frag m = EnvReaderT $ ReaderT \env ->
    extendScope frag do
      let EnvReaderT (ReaderT cont) = m
      env' <- injectM env
      cont env'

-- === OutReader monad: reads data in the output name space ===

class OutReader (e::E) (m::MonadKind1) | m -> e where
  askOutReader :: m n (e n)
  localOutReader :: e n -> m n a -> m n a

newtype OutReaderT (e::E) (m::MonadKind1) (n::S) (a :: *) =
  OutReaderT { runOutReaderT' :: ReaderT (e n) (m n) a }
  deriving (Functor, Applicative, Monad, MonadFail, Fallible)

runOutReaderT :: e n -> OutReaderT e m n a -> m n a
runOutReaderT env m = flip runReaderT env $ runOutReaderT' m

instance (InjectableE e, ScopeReader m)
         => ScopeReader (OutReaderT e m) where
  addScope e = OutReaderT $ lift $ addScope e
  getDistinctEvidenceM = OutReaderT $ lift getDistinctEvidenceM

instance (InjectableE e, ScopeGetter m)
         => ScopeGetter (OutReaderT e m) where
  getScope = OutReaderT $ lift getScope

instance (InjectableE e, ScopeExtender m)
         => ScopeExtender (OutReaderT e m) where
  extendScope frag m = OutReaderT $ ReaderT \env ->
    extendScope frag do
      let OutReaderT (ReaderT cont) = m
      env' <- injectM env
      cont env'

instance Monad1 m => OutReader e (OutReaderT e m) where
  askOutReader = OutReaderT ask
  localOutReader r (OutReaderT m) = OutReaderT $ local (const r) m

instance OutReader e m => OutReader e (EnvReaderT v m i) where
  askOutReader = EnvReaderT $ ReaderT $ const askOutReader
  localOutReader e (EnvReaderT (ReaderT f)) = EnvReaderT $ ReaderT $ \env ->
    localOutReader e $ f env

-- === ZipEnvReaderT transformer ===

newtype ZipEnvReaderT (m::MonadKind1) (i1::S) (i2::S) (o::S) (a:: *) =
  ZipEnvReaderT { runZipEnvReaderT :: ReaderT (ZipEnv i1 i2 o) (m o) a }
  deriving (Functor, Applicative, Monad, Fallible, MonadFail)

type ZipEnv i1 i2 o = (NameFunction Name i1 o, NameFunction Name i2 o)

instance ScopeReader m => ScopeReader (ZipEnvReaderT m i1 i2) where
  addScope e = ZipEnvReaderT $ lift $ addScope e
  getDistinctEvidenceM = ZipEnvReaderT $ lift getDistinctEvidenceM

instance ScopeGetter m => ScopeGetter (ZipEnvReaderT m i1 i2) where
  getScope = ZipEnvReaderT $ lift getScope

instance (ScopeReader m, ScopeExtender m)
         => ScopeExtender (ZipEnvReaderT m i1 i2) where
  extendScope frag m =
    ZipEnvReaderT $ ReaderT \(env1, env2) -> do
      extendScope frag do
        let ZipEnvReaderT (ReaderT cont) = m
        env1' <- injectM env1
        env2' <- injectM env2
        cont (env1', env2')

instance (Monad1 m, ScopeReader m, ScopeExtender m, Fallible1 m)
         => ZipEnvReader (ZipEnvReaderT m) where

  lookupZipEnvFst v = ZipEnvReaderT $ (!v) <$> fst <$> ask
  lookupZipEnvSnd v = ZipEnvReaderT $ (!v) <$> snd <$> ask

  extendZipEnvFst frag (ZipEnvReaderT cont) = ZipEnvReaderT $ withReaderT (onFst (<>>frag)) cont
  extendZipEnvSnd frag (ZipEnvReaderT cont) = ZipEnvReaderT $ withReaderT (onSnd (<>>frag)) cont

  withEmptyZipEnv (ZipEnvReaderT cont) =
    ZipEnvReaderT $ withReaderT (const (newNameFunction id, newNameFunction id)) cont

-- === monadish thing for computations that produce names ===

class NameGen (m :: E -> S -> *) where
  returnG :: e n -> m e n
  bindG   :: m e n -> (forall l. (Distinct l, Ext n l) => e l -> m e' l) -> m e' n
  getDistinctEvidenceG :: m DistinctEvidence n

fmapG :: NameGen m => (forall l. e1 l -> e2 l) -> m e1 n -> m e2 n
fmapG f e = e `bindG` (returnG . f)

data DistinctAbs (b::B) (e::E) (n::S) where
  DistinctAbs :: Distinct l => b n l -> e l -> DistinctAbs b e n

newtype NameGenT (m::MonadKind1) (e::E) (n::S) =
  NameGenT { runNameGenT :: m n (DistinctAbs ScopeFrag e n) }

instance (ScopeReader m, ScopeExtender m, Monad1 m) => NameGen (NameGenT m) where
  returnG e = NameGenT $ do
    Distinct <- getDistinct
    return (DistinctAbs id e)
  bindG (NameGenT m) f = NameGenT do
    DistinctAbs s  e  <- m
    DistinctAbs s' e' <- extendScope s $ runNameGenT $ f e
    return $ DistinctAbs (s >>> s') e'
  getDistinctEvidenceG = NameGenT do
    Distinct <- getDistinct
    return $ DistinctAbs id getDistinctEvidence

-- === in-place scope updating monad ===

-- [NoteInplaceMonad]

data Inplace (m :: E -> S -> *) (n::S) (a:: *) =
  UnsafeMakeInplace { unsafeRunInplace :: (m (LiftE a) UnsafeS) }

instance NameGen m => Functor (Inplace m n) where
  fmap = liftM

instance NameGen m => Applicative (Inplace m n) where
  pure x = UnsafeMakeInplace (returnG (LiftE x))
  liftA2 = liftM2

instance NameGen m => Monad (Inplace m n) where
  return = pure
  UnsafeMakeInplace m >>= f = UnsafeMakeInplace $
    m `bindG` \(LiftE x) ->
      let UnsafeMakeInplace m' = f x
      in unsafeCoerceE $ m'

-- XXX: this might not be completely safe. For example, the caller might use it
-- to smuggle out a data representation of the `Ext n l`, along with, say, a
-- `Scope l`, and then use it to generate a lookup that will fail. We should
-- think about whether there's a way to plug that hole.
liftInplace :: forall m e n.
               (NameGen m, InjectableE e)
            => (forall l. Ext n l => m e l)
            -> Inplace m n (e n)
liftInplace cont = UnsafeMakeInplace $
  withExtEvidence (FabricateExtEvidence :: ExtEvidence n UnsafeS) $
    cont `bindG` \result ->
    returnG $ LiftE $ unsafeCoerceE result

runInplace :: (NameGen m, InjectableE e)
           => (forall l. (Distinct l, Ext n l) => Inplace m l (e l))
           -> m e n
runInplace cont =
  runInplace' \distinct ext ->
  withDistinctEvidence distinct $ withExtEvidence ext cont

runInplace' :: (NameGen m, InjectableE e)
            => (forall l. DistinctEvidence l -> ExtEvidence n l -> Inplace m l (e l))
            -> m e n
runInplace' cont = unsafeCoerceE $
  unsafeRunInplace (cont FabricateDistinctEvidence FabricateExtEvidence) `bindG` \(LiftE e) ->
  returnG $ unsafeCoerceE e

-- === name hints ===

class HasNameHint a where
  getNameHint :: a -> NameHint

instance HasNameHint (Name s n) where
  getNameHint name = Hint $ getRawName name

instance HasNameHint (NameBinder s n l) where
  getNameHint b = Hint $ getRawName $ binderName b

instance HasNameHint RawName where
  getNameHint = Hint

instance HasNameHint String where
  getNameHint = fromString

-- === getting name colors ===

class HasNameColor a c | a -> c where
  getNameColor :: a -> NameColorRep c

instance HasNameColor (Name c n) c where
  getNameColor = getNameColorRep

instance HasNameColor (NameBinder c n l) c where
  getNameColor b = getNameColorRep $ nameBinderName b

-- === instances ===

instance InjectableV v => InjectableE (NameFunction v i) where
  injectionProofE fresh (NameFunction f m) =
    NameFunction (\name ->
                      withNameColorRep (getNameColorRep name)  $
                        injectionProofE fresh $ f name)
                 (injectionProofE fresh m)

instance InjectableE atom => InjectableV (SubstVal (cMatch::C) (atom::E))
instance InjectableE atom => InjectableE (SubstVal (cMatch::C) (atom::E) (c::C)) where
  injectionProofE fresh substVal = case substVal of
    Rename name  -> Rename   $ injectionProofE fresh name
    SubstVal val -> SubstVal $ injectionProofE fresh val

instance (InjectableB b, InjectableE e) => InjectableE (Abs b e) where
  injectionProofE fresh (Abs b body) =
    injectionProofB fresh b \fresh' b' ->
      Abs b' (injectionProofE fresh' body)

instance (SubstB v b, SubstE v e) => SubstE v (Abs b e) where
  substE env (Abs b body) = do
    substB env b \env' b' -> Abs b' <$> substE env' body

instance (BindsNames b1, BindsNames b2) => ProvesExt  (PairB b1 b2) where
instance (BindsNames b1, BindsNames b2) => BindsNames (PairB b1 b2) where
  toScopeFrag (PairB b1 b2) = toScopeFrag b1 >>> toScopeFrag b2

instance (InjectableB b1, InjectableB b2) => InjectableB (PairB b1 b2) where
  injectionProofB fresh (PairB b1 b2) cont =
    injectionProofB fresh b1 \fresh' b1' ->
      injectionProofB fresh' b2 \fresh'' b2' ->
        cont fresh'' (PairB b1' b2')

instance (SubstB v b1, SubstB v b2) => SubstB v (PairB b1 b2) where
  substB env (PairB b1 b2) cont =
    substB env b1 \env' b1' ->
      substB env' b2 \env'' b2' ->
        cont env'' $ PairB b1' b2'

instance (InjectableB b, InjectableE ann) => InjectableB (BinderP b ann) where
  injectionProofB fresh (b:>ann) cont = do
    let ann' = injectionProofE fresh ann
    injectionProofB fresh b \fresh' b' ->
      cont fresh' $ b':>ann'

instance (SubstB v b, SubstE v ann) => SubstB v (BinderP b ann) where
   substB env (b:>ann) cont = do
     ann' <- substE env ann
     substB env b \env' b' -> do
       cont env' (b':>ann')

instance BindsNames b => ProvesExt  (BinderP b ann) where
instance BindsNames b => BindsNames (BinderP b ann) where
  toScopeFrag (b:>_) = toScopeFrag b

instance BindsNames b => ProvesExt  (Nest b) where
instance BindsNames b => BindsNames (Nest b) where
  toScopeFrag Empty = id
  toScopeFrag (Nest b rest) = toScopeFrag b >>> toScopeFrag rest

instance SubstB v b => SubstB v (Nest b) where
  substB env (Nest b bs) cont =
    substB env b \env' b' ->
      substB env' bs \env'' bs' ->
        cont env'' $ Nest b' bs'
  substB env Empty cont = cont env Empty

instance InjectableE UnitE where
  injectionProofE _ UnitE = UnitE

instance FromName v => SubstE v UnitE where
  substE _ UnitE = return UnitE

instance (Functor f, InjectableE e) => InjectableE (ComposeE f e) where
  injectionProofE fresh (ComposeE xs) = ComposeE $ fmap (injectionProofE fresh) xs

instance (Traversable f, SubstE v e) => SubstE v (ComposeE f e) where
  substE env (ComposeE xs) = ComposeE <$> mapM (substE env) xs

-- alternatively we could use Zippable, but we'd want to be able to derive it
-- (e.g. via generic) for the many-armed cases like PrimOp.
instance (Traversable f, Eq (f ()), AlphaEq e) => AlphaEqE (ComposeE f e) where
  alphaEqE (ComposeE xs) (ComposeE ys) = alphaEqTraversable xs ys

instance InjectableB UnitB where
  injectionProofB fresh UnitB cont = cont fresh UnitB

instance ProvesExt  UnitB where
instance BindsNames UnitB where
  toScopeFrag UnitB = id

instance FromName v => SubstB v UnitB where
  substB env UnitB cont = cont env UnitB

instance InjectableE const => InjectableV (ConstE const)
instance InjectableE const => InjectableE (ConstE const ignored) where
  injectionProofE fresh (ConstE e) = ConstE $ injectionProofE fresh e

instance InjectableE VoidE where
  injectionProofE _ _ = error "impossible"

instance AlphaEqE VoidE where
  alphaEqE _ _ = error "impossible"

instance FromName v => SubstE v VoidE where
  substE _ _ = error "impossible"

instance (InjectableE e1, InjectableE e2) => InjectableE (PairE e1 e2) where
  injectionProofE fresh (PairE e1 e2) =
    PairE (injectionProofE fresh e1) (injectionProofE fresh e2)

instance (SubstE v e1, SubstE v e2) => SubstE v (PairE e1 e2) where
  substE env (PairE x y) =
    PairE <$> substE env x <*> substE env y

instance (InjectableE e1, InjectableE e2) => InjectableE (EitherE e1 e2) where
  injectionProofE fresh (LeftE  e) = LeftE  (injectionProofE fresh e)
  injectionProofE fresh (RightE e) = RightE (injectionProofE fresh e)

instance (SubstE v e1, SubstE v e2) => SubstE v (EitherE e1 e2) where
  substE env (LeftE  x) = LeftE  <$> substE env x
  substE env (RightE x) = RightE <$> substE env x

instance InjectableE e => InjectableE (ListE e) where
  injectionProofE fresh (ListE xs) = ListE $ map (injectionProofE fresh) xs

instance AlphaEqE e => AlphaEqE (ListE e) where
  alphaEqE (ListE xs) (ListE ys)
    | length xs == length ys = mapM_ (uncurry alphaEqE) (zip xs ys)
    | otherwise              = zipErr

instance InjectableE (LiftE a) where
  injectionProofE _ (LiftE x) = LiftE x

instance FromName v => SubstE v (LiftE a) where
  substE _ (LiftE x) = return $ LiftE x

instance Eq a => AlphaEqE (LiftE a) where
  alphaEqE (LiftE x) (LiftE y) = unless (x == y) zipErr

instance SubstE v e => SubstE v (ListE e) where
  substE env (ListE xs) = ListE <$> mapM (substE env) xs

instance (PrettyB b, PrettyE e) => Pretty (Abs b e n) where
  pretty (Abs b body) = "(Abs " <> pretty b <> " " <> pretty body <> ")"

instance Pretty a => Pretty (LiftE a n) where
  pretty (LiftE x) = pretty x

instance Pretty (UnitE n) where
  pretty UnitE = ""

instance ( Generic (b UnsafeS UnsafeS)
         , Generic (body UnsafeS) )
         => Generic (Abs b body n) where
  type Rep (Abs b body n) = Rep (b UnsafeS UnsafeS, body UnsafeS)
  from (Abs b body) = from (unsafeCoerceB b, unsafeCoerceE body)
  to rep = Abs (unsafeCoerceB b) (unsafeCoerceE body)
    where (b, body) = to rep

instance ( Generic (b1 UnsafeS UnsafeS)
         , Generic (b2 UnsafeS UnsafeS) )
         => Generic (PairB b1 b2 n l) where
  type Rep (PairB b1 b2 n l) = Rep (b1 UnsafeS UnsafeS, b2 UnsafeS UnsafeS)
  from (PairB b1 b2) = from (unsafeCoerceB b1, unsafeCoerceB b2)
  to rep = PairB (unsafeCoerceB b1) (unsafeCoerceB b2)
    where (b1, b2) = to rep

instance ( Store   (b UnsafeS UnsafeS), Store   (body UnsafeS)
         , Generic (b UnsafeS UnsafeS), Generic (body UnsafeS) )
         => Store (Abs b body n)
instance ( Store   (b1 UnsafeS UnsafeS), Store   (b2 UnsafeS UnsafeS)
         , Generic (b1 UnsafeS UnsafeS), Generic (b2 UnsafeS UnsafeS) )
         => Store (PairB b1 b2 n l)

instance ProvesExt  (RecEnvFrag v) where
instance BindsNames (RecEnvFrag v) where
  toScopeFrag env = envAsScope $ fromRecEnvFrag env

-- Traversing a recursive set of bindings is a bit tricky because we have to do
-- two passes: first we rename the binders, then we go and subst the payloads.
instance (InjectableV substVal, SubstV substVal v) => SubstB substVal (RecEnvFrag v) where
  substB env (RecEnvFrag recEnv) cont = do
    let pairs = toEnvPairs recEnv
    renameEnvPairBinders env pairs \env' pairs' -> do
      pairs'' <- forEachNestItem  pairs' \(EnvPair b x) -> EnvPair b <$> substE env' x
      cont env' $ RecEnvFrag $ fromEnvPairs pairs''

renameEnvPairBinders
  :: (Distinct o, Monad m, InjectableV v, InjectableV substVal, FromName substVal)
  => SubstTraversalEnv m substVal i o
  -> Nest (EnvPair v ignored) i i'
  -> (forall o'.
         Distinct o'
      => SubstTraversalEnv m substVal i' o'
      -> Nest (EnvPair v ignored) o o'
      -> m a)
  -> m a
renameEnvPairBinders env Empty cont = cont env Empty
renameEnvPairBinders env (Nest (EnvPair b v) rest) cont =
  substB env b \env' b' ->
    renameEnvPairBinders env' rest \env'' rest' ->
      cont env'' (Nest (EnvPair b' v) rest')

instance InjectableV v => InjectableB (RecEnvFrag v) where
  injectionProofB _ _ _ = undefined

instance SubstV substVal v => SubstE substVal (EnvVal v) where
  substE env (EnvVal rep v) = withNameColorRep rep $ EnvVal rep <$> substE env v

instance Store (UnitE n)
instance Store (VoidE n)
instance (Store (e1 n), Store (e2 n)) => Store (PairE   e1 e2 n)
instance (Store (e1 n), Store (e2 n)) => Store (EitherE e1 e2 n)
instance Store (e n) => Store (ListE  e n)
instance Store a => Store (LiftE a n)
instance Store (const n) => Store (ConstE const ignored n)
instance (Store (b n l), Store (ann n)) => Store (BinderP b ann n l)

type EE = EitherE

type EitherE1 e0             = EE e0 VoidE
type EitherE2 e0 e1          = EE e0 (EE e1 VoidE)
type EitherE3 e0 e1 e2       = EE e0 (EE e1 (EE e2 VoidE))
type EitherE4 e0 e1 e2 e3    = EE e0 (EE e1 (EE e2 (EE e3 VoidE)))
type EitherE5 e0 e1 e2 e3 e4 = EE e0 (EE e1 (EE e2 (EE e3 (EE e4 VoidE))))

pattern Case0 :: e0 n -> EE e0 rest n
pattern Case0 e = LeftE e

pattern Case1 :: e1 n -> EE e0 (EE e1 rest) n
pattern Case1 e = RightE (LeftE e)

pattern Case2 :: e2 n -> EE e0 (EE e1 (EE e2 rest)) n
pattern Case2 e = RightE (RightE (LeftE e))

pattern Case3 :: e3 n -> EE e0 (EE e1 (EE e2 (EE e3 rest))) n
pattern Case3 e = RightE (RightE (RightE (LeftE e)))

pattern Case4 :: e4 n ->  EE e0 (EE e1 (EE e2 (EE e3 (EE e4 rest)))) n
pattern Case4 e = RightE (RightE (RightE (RightE (LeftE e))))

-- === notes ===

{-

[NoteInplaceMonad]

The Inplace monad wraps a NameGen monad and hides its ever-changing scope
parameter. Instead it exposes a scope parameter that doesn't change, so we can
have an ordinary Monad instance instead of using bindG/returnG. When the scope
parameter for the underlying NameGen monad is extended, we just implicitly
inject all the existing values into the new name space. This is fine as long as
we enforce two invariants. First, we make sure that the actual underlying
parameter is only updated by fresh extension. This is already guaranteed by
`NameGen`. Second, we only produce values which are covariant in their scope
parameter. We enforce this with the InjectableE constraint to `liftInplace`.
This is the condition that lets us update all the existing values "in place".
Otherwise you could get access to, say, a `Bindings n`. If you then generated a
new name, `Name n`, you'd expect to be able to look it up in the bindings, but
it would fail!

-}
