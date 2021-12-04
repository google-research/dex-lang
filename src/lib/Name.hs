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
{-# LANGUAGE DerivingVia #-}

module Name (
  Name (..), RawName (..), freshRawName,
  S (..), C (..), (<.>), EnvFrag (..), NameBinder (..),
  EnvReader (..), FromName (..), Distinct,
  Ext, ExtEvidence, ProvesExt (..), withExtEvidence, getExtEvidence,
  Env (..), idEnv, idEnvFrag, newEnv, envFromFrag, traverseEnvFrag,
  DistinctAbs (..), WithScope (..),
  extendRenamer, ScopeReader (..), ScopeExtender (..),
  AlwaysImmut (..), AlwaysImmut2,
  Scope (..), ScopeFrag (..), SubstE (..), SubstB (..),
  SubstV, InplaceT, extendInplaceT, extendInplaceTLocal,
  liftBetweenInplaceTs, emitInplaceT,
  extendTrivialInplaceT, getOutMapInplaceT, runInplaceT,
  E, B, V, HasNamesE, HasNamesB, BindsNames (..), HasScope (..), RecEnvFrag (..), RecEnv (..),
  MaterializedEnv (..), lookupTerminalEnvFrag, lookupMaterializedEnv,
  BindsOneName (..), BindsAtMostOneName (..), BindsNameList (..), NameColorRep (..),
  Abs (..), Nest (..), PairB (..), UnitB (..),
  IsVoidS (..), UnitE (..), VoidE, PairE (..), toPairE, fromPairE,
  ListE (..), ComposeE (..),
  EitherE (..), LiftE (..), EqE, EqB, OrdE, OrdB, VoidB,
  EitherB (..), BinderP (..),
  LiftB, pattern LiftB,
  MaybeE, fromMaybeE, toMaybeE, pattern JustE, pattern NothingE, MaybeB,
  pattern JustB, pattern NothingB,
  toConstAbs, PrettyE, PrettyB, ShowE, ShowB,
  runScopeReaderT, runScopeReaderM, runEnvReaderT, ScopeReaderT (..), EnvReaderT (..),
  lookupEnvM, dropSubst, extendEnv, fmapNames,
  MonadKind, MonadKind1, MonadKind2,
  Monad1, Monad2, Fallible1, Fallible2, Catchable1, Catchable2, Monoid1,
  MonadIO1, MonadIO2,
  CtxReader1, CtxReader2, MonadFail1, MonadFail2, Alternative1, Alternative2,
  Searcher1, Searcher2, ScopeReader2, ScopeExtender2,
  applyAbs, applySubst, applyNaryAbs, ZipEnvReader (..), alphaEqTraversable,
  checkAlphaEq, alphaEq, alphaEqPure, alphaElem, nubAlphaEq,
  AlphaEq, AlphaEqE (..), AlphaEqB (..), AlphaEqV, ConstE (..),
  InjectableE (..), InjectableB (..), InjectableV, InjectionCoercion,
  withFreshM, withFreshLike, inject, injectM, (!), (<>>), withManyFresh,
  envFragAsScope, lookupEnvFrag, lookupEnvFragRaw,
  EmptyAbs, pattern EmptyAbs, NaryAbs, SubstVal (..),
  NameGen (..), fmapG, NameGenT (..), fmapNest, forEachNestItem, forEachNestItemM,
  substM, ScopedEnvReader, runScopedEnvReader,
  HasNameHint (..), HasNameColor (..), NameHint (..), NameColor (..),
  GenericE (..), GenericB (..),
  EitherE1, EitherE2, EitherE3, EitherE4, EitherE5, EitherE6,
    pattern Case0, pattern Case1, pattern Case2, pattern Case3, pattern Case4, pattern Case5,
  EitherB1, EitherB2, EitherB3, EitherB4, EitherB5,
    pattern CaseB0, pattern CaseB1, pattern CaseB2, pattern CaseB3, pattern CaseB4,
  splitNestAt, nestLength, nestToList, binderAnn,
  OutReaderT (..), OutReader (..), runOutReaderT,
  ExtWitness (..),
  InFrag (..), InMap (..), OutFrag (..), OutMap (..), ExtOutMap (..),
  toEnvPairs, fromEnvPairs, EnvPair (..), refreshRecEnvFrag,
  substAbsDistinct, refreshAbs,
  hoist, hoistToTop, injectFromTop, fromConstAbs, exchangeBs, HoistableE (..),
  HoistExcept (..), liftHoistExcept, abstractFreeVars, abstractFreeVarsNoAnn,
  WithRenamer (..), ignoreHoistFailure,
  HoistableB (..), HoistableV,
  WrapE (..), EnvVal (..), fromEnvVal,
  DistinctEvidence (..), withSubscopeDistinct, tryAsColor, withFresh,
  unsafeCoerceE, unsafeCoerceB, getRawName, ColorsEqual (..),
  eqNameColorRep, withNameColorRep, injectR, fmapEnvFrag, catRecEnvFrags,
  freeVarsList, isFreeIn, todoInjectableProof,
  locallyMutableInplaceT, locallyImmutableInplaceT, toExtWitness,
  checkEmpty, updateEnvFrag, nameSetToList, toNameSet, absurdExtEvidence,
  Mut, Immut, ImmutEvidence (..), scopeToImmut, withImmutEvidence, toImmutEvidence,
  fabricateDistinctEvidence,
  collectFreeVars, unConsEnv, ConsEnv (..), MonadTrans1 (..), fromDistinctAbs,
  ) where

import Prelude hiding (id, (.))
import Control.Category
import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Except hiding (Except)
import Control.Monad.Reader
import Control.Monad.Writer.Strict
import Control.Monad.State.Strict
import qualified Data.Map.Strict as M
import Data.Functor ((<&>))
import Data.Foldable (fold)
import Data.Maybe (catMaybes)
import Data.Kind (Type)
import Data.String
import Data.Function ((&))
import Data.List (nubBy)
import Data.Text.Prettyprint.Doc  hiding (nest)
import qualified Data.Text as T
import GHC.Exts (Constraint)
import GHC.Generics (Generic (..), Rep)
import Data.Store (Store)

import qualified Unsafe.Coerce as TrulyUnsafe

import Util (zipErr, onFst, onSnd)
import Err

-- === category-like classes for envs, scopes etc ===

data Env v i o where
  Env :: (forall c. Name c hidden -> v c o)
      -> EnvFrag v hidden i o
      -> Env v i o

newEnv :: (forall c. Name c i -> v c o) -> Env v i o
newEnv f = Env f emptyInFrag

envFromFrag :: EnvFrag v VoidS i o -> Env v i o
envFromFrag frag = Env absurdNameFunction frag

idEnv :: FromName v => Env v n n
idEnv = newEnv fromName

idEnvFrag :: (BindsNames b, FromName v) => b n l -> EnvFrag v n l l
idEnvFrag b =
  fmapEnvFrag (\v _ -> fromName $ injectR v) $ scopeFragToEnvFrag (toScopeFrag b)

infixl 9 !
(!) :: Env v i o -> Name c i -> v c o
(!) (Env f env) name =
  case lookupEnvFragProjected env name of
    Left name' -> f name'
    Right val -> val

infixl 1 <.>
(<.>) :: InFrag envFrag => envFrag i1 i2 o -> envFrag i2 i3 o -> envFrag i1 i3 o
(<.>) = catInFrags

infixl 1 <>>
(<>>) :: InMap env envFrag => env i o -> envFrag i i' o -> env i' o
(<>>) = extendInMap

class InFrag (envFrag :: S -> S -> S -> *) where
  emptyInFrag :: envFrag i i o
  catInFrags  :: envFrag i1 i2 o -> envFrag i2 i3 o -> envFrag i1 i3 o

class InMap (env :: S -> S -> *) (envFrag :: S -> S -> S -> *) | env -> envFrag where
  emptyInMap :: env VoidS o
  extendInMap :: env i o -> envFrag i i' o -> env i' o

class (InjectableB scopeFrag, BindsNames scopeFrag) => OutFrag (scopeFrag :: S -> S -> *) where
  emptyOutFrag :: scopeFrag n n
  -- The scope is here because solver subst concatenation needs it
  catOutFrags  :: Distinct n3 => Scope n3 -> scopeFrag n1 n2 -> scopeFrag n2 n3 -> scopeFrag n1 n3

class HasScope scope => OutMap scope where
  emptyOutMap :: scope VoidS

class (OutFrag scopeFrag, OutMap scope)
      => ExtOutMap (scope :: S -> *) (scopeFrag :: S -> S -> *) where
  extendOutMap :: Distinct l => scope n -> scopeFrag n l -> scope l

todoInjectableProof :: a
todoInjectableProof =
  error "This will never be called. But we should really finish these proofs."

instance InMap (Env v) (EnvFrag v) where
  emptyInMap = newEnv absurdNameFunction
  extendInMap (Env f frag) frag' = Env f $ frag <.> frag'

instance InjectableB ScopeFrag where
  injectionProofB _ _ _ = todoInjectableProof

instance OutFrag ScopeFrag where
  emptyOutFrag = id
  catOutFrags _ = (>>>)

instance HasScope Scope where
  toScope = id

instance OutMap Scope where
  emptyOutMap = Scope id

instance ExtOutMap Scope ScopeFrag where
  extendOutMap (Scope scope) frag = Scope $ scope >>> frag

-- outvar version of EnvFrag/Env, where the query name space and the result name
-- space are the same (thus recursive)
newtype RecEnv      (v::V) o    = RecEnv     { fromRecEnv     :: EnvFrag v VoidS o o } deriving Generic
newtype RecEnvFrag  (v::V) o o' = RecEnvFrag { fromRecEnvFrag :: EnvFrag v o o' o'   } deriving Generic

instance InjectableV v => OutFrag (RecEnvFrag v) where
  emptyOutFrag = RecEnvFrag $ emptyInFrag
  catOutFrags _ = catRecEnvFrags

catRecEnvFrags :: (Distinct n3, InjectableV v)
               => RecEnvFrag v n1 n2 -> RecEnvFrag v n2 n3 -> RecEnvFrag v n1 n3
catRecEnvFrags (RecEnvFrag frag1) (RecEnvFrag frag2) = RecEnvFrag $
  withExtEvidence (toExtEvidence (RecEnvFrag frag2)) $
    inject frag1 `catInFrags` frag2

instance HasScope (RecEnv v) where
  toScope (RecEnv envFrag) = Scope $ envFragAsScope envFrag

instance InjectableV v => OutMap (RecEnv v) where
  emptyOutMap = RecEnv emptyInFrag

instance InjectableV v => ExtOutMap (RecEnv v) (RecEnvFrag v) where
  extendOutMap (RecEnv env) (RecEnvFrag frag) = RecEnv $
    withExtEvidence (toExtEvidence (RecEnvFrag frag)) $
      inject env <.> frag

deriving instance (forall c. Show (v c o')) => Show (RecEnvFrag v o o')

-- Like Env, but stores the mapping as data rather than (partially) as a
-- function. Suitable for Show/Store instances.
newtype MaterializedEnv (v::V) (i::S) (o::S) =
  MaterializedEnv { fromMaterializedEnv :: EnvFrag v VoidS i o }
  deriving (Generic)

instance InMap (MaterializedEnv v) (EnvFrag v) where
  emptyInMap = MaterializedEnv emptyInFrag
  extendInMap (MaterializedEnv frag) frag' = MaterializedEnv $ frag <.> frag'

lookupTerminalEnvFrag :: EnvFrag v VoidS i o -> Name c i -> v c o
lookupTerminalEnvFrag frag name =
  case lookupEnvFragProjected frag name of
    Left name' -> absurdNameFunction name'
    Right val -> val

lookupMaterializedEnv :: MaterializedEnv v i o -> Name c i -> v c o
lookupMaterializedEnv (MaterializedEnv frag) name =
  lookupTerminalEnvFrag frag name

instance (InjectableB b, BindsNames b) => OutFrag (Nest b) where
  emptyOutFrag = id
  catOutFrags _ = (>>>)

updateEnvFrag :: Name c i -> v c o -> EnvFrag v VoidS i o -> EnvFrag v VoidS i o
updateEnvFrag (UnsafeMakeName rep v) rhs (UnsafeMakeEnv m) =
  UnsafeMakeEnv $ M.insert v (EnvVal rep rhs) m

-- === monadic type classes for reading and extending envs and scopes ===

data WithScope (e::E) (n::S) where
  WithScope :: (Distinct l, Ext l n) => Scope l -> e l -> WithScope e n

instance InjectableE e => InjectableE (WithScope e) where
  injectionProofE (fresh::InjectionCoercion n l) (WithScope (scope::Scope h) e) =
    withExtEvidence (injectionProofE fresh ext) $
      WithScope scope e
    where ext = getExtEvidence :: ExtEvidence h n

class Monad1 m => AlwaysImmut (m::MonadKind1) where
  getImmut :: m n (ImmutEvidence n)

class Monad1 m => ScopeReader (m::MonadKind1) where
  getScope :: Immut n => m n (Scope n)
  liftImmut :: InjectableE e
            => (forall l. (Immut l, Ext n l, Distinct l) => m l (e l))
            -> m n (e n)
  getDistinct :: m n (DistinctEvidence n)

class ScopeReader m => ScopeExtender (m::MonadKind1) where
  extendScope :: Distinct l => ScopeFrag n l -> (Ext n l => m l r) -> m n r

class (InjectableV v, Monad2 m) => EnvReader (v::V) (m::MonadKind2) | m -> v where
   getEnv :: m i o (Env v i o)
   withEnv :: Env v i' o -> m i' o a -> m i o a

lookupEnvM :: EnvReader v m => Name c i -> m i o (v c o)
lookupEnvM name = (!name) <$> getEnv

dropSubst :: (EnvReader v m, FromName v) => m o o r -> m i o r
dropSubst cont = withEnv idEnv cont

extendEnv :: EnvReader v m => EnvFrag v i i' o -> m i' o r -> m i o r
extendEnv frag cont = do
  env <- (<>>frag) <$> getEnv
  withEnv env cont

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

data Nest (binder::B) (n::S) (l::S) where
  Nest  :: binder n h -> Nest binder h l -> Nest binder n l
  Empty ::                                  Nest binder n n

data BinderP (c::C) (ann::E) (n::S) (l::S) =
  (:>) (NameBinder c n l) (ann n)
  deriving (Show, Generic)

type EmptyAbs b = Abs b UnitE :: E
pattern EmptyAbs :: b n l -> EmptyAbs b n
pattern EmptyAbs bs = Abs bs UnitE

type NaryAbs (c::C) = Abs (Nest (NameBinder c)) :: E -> E

-- Proof object that a given scope is void
data IsVoidS n where
  IsVoidS :: IsVoidS VoidS

-- === Injections and projections ===

class ProvesExt (b :: B) where
  toExtEvidence :: b n l -> ExtEvidence n l

  default toExtEvidence :: BindsNames b => b n l -> ExtEvidence n l
  toExtEvidence b = toExtEvidence $ toScopeFrag b

toExtWitness :: ProvesExt b => b n l -> ExtWitness n l
toExtWitness b = withExtEvidence (toExtEvidence b) ExtW

class ProvesExt b => BindsNames (b :: B) where
  toScopeFrag :: b n l -> ScopeFrag n l

  default toScopeFrag :: (GenericB b, BindsNames (RepB b)) => b n l -> ScopeFrag n l
  toScopeFrag b = toScopeFrag $ fromB b

checkEmpty :: BindsNames b => b n l -> Maybe (UnitB n l)
checkEmpty b =
  let UnsafeMakeScopeFrag frag = toScopeFrag b
  in if null frag
    then Just $ unsafeCoerceB UnitB
    else Nothing

instance ProvesExt ExtEvidence where
  toExtEvidence = id

instance ProvesExt ScopeFrag
instance BindsNames ScopeFrag where
  toScopeFrag s = s

instance HoistableB ScopeFrag where
  freeVarsB _ = mempty

class HasScope (bindings :: S -> *) where
  toScope :: bindings n -> Scope n

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

instance InjectableE (ExtWitness n) where
  injectionProofE :: forall l l'. InjectionCoercion l l' -> ExtWitness n l -> ExtWitness n l'
  injectionProofE fresh ExtW =
    withExtEvidence (injectionProofE fresh (getExtEvidence :: ExtEvidence n l)) ExtW

instance Category ExtWitness where
  id = ExtW
  ExtW . ExtW = ExtW

fmapNames :: (SubstE v e, Distinct o)
          => Scope o -> (forall c. Name c i -> v c o) -> e i -> e o
fmapNames scope f e = substE (scope, newEnv f) e

toConstAbs :: (InjectableE e, ScopeReader m)
           => NameColorRep c -> e n -> m n (Abs (NameBinder c) e n)
toConstAbs rep body = do
  WithScope scope body' <- addScope body
  withFresh "ignore" rep scope \b -> do
    injectM $ Abs b $ inject body'

-- === type classes for traversing names ===

class FromName v => SubstE (v::V) (e::E) where
  -- TODO: can't make an alias for these constraints because of impredicativity
  substE :: Distinct o => (Scope o, Env v i o) -> e i -> e o

  default substE :: (GenericE e, SubstE v (RepE e), Distinct o)
                 => (Scope o, Env v i o) -> e i -> e o
  substE env e = toE $ substE env (fromE e)

class (FromName v, InjectableB b) => SubstB (v::V) (b::B) where
  substB
    :: Distinct o
    => (Scope o, Env v i o)
    -> b i i'
    -> (forall o'. Distinct o' => (Scope o', Env v i' o') -> b o o' -> a)
    -> a

  default substB
    :: (GenericB b, SubstB v (RepB b))
    => Distinct o
    => (Scope o, Env v i o)
    -> b i i'
    -> (forall o'. Distinct o' => (Scope o', Env v i' o') -> b o o' -> a)
    -> a
  substB env b cont =
    substB env (fromB b) \env' b' ->
      cont env' $ toB b'

  substBDistinct
    :: Distinct l
    => (Scope n, Env v n n)
    -> b n l
    -> b n l

  default substBDistinct
    :: (GenericB b, SubstB v (RepB b))
    => Distinct l
    => (Scope n, Env v n n)
    -> b n l
    -> b n l
  substBDistinct env b = toB $ substBDistinct env $ fromB b

class ( FromName substVal, InjectableV v
      , forall c. NameColor c => SubstE substVal (v c))
      => SubstV (substVal::V) (v::V)

type HasNamesE e = (SubstE Name e, HoistableE e)
type HasNamesB = SubstB Name

instance SubstV Name Name where
instance SubstE Name (Name c) where
  substE (_, env) name = env ! name

instance (InjectableV v, FromName v) => SubstB v (NameBinder c) where
  substB (scope, env) b cont = do
    let rep = getNameColor $ nameBinderName b
    withFresh (getNameHint b) rep scope \b' -> do
      let scope' = scope `extendOutMap` toScopeFrag b'
      let env' = inject env <>> b @> (fromName $ binderName b')
      cont (scope', env') b'

  substBDistinct _ b = b

substM :: (EnvReader v m, ScopeReader2 m, InjectableE e, SubstE v e, FromName v)
       => e i -> m i o (e o)
substM e = do
  env <- getEnv
  WithScope scope env' <- addScope env
  injectM $ fmapNames scope (env'!) e

fromConstAbs :: (BindsNames b, HoistableE e) => Abs b e n -> HoistExcept (e n)
fromConstAbs (Abs b e) = hoist b e

-- === expresions carrying distinctness constraints ===

data DistinctAbs (b::B) (e::E) (n::S) where
  DistinctAbs :: Distinct l => b n l -> e l -> DistinctAbs b e n

instance (SubstB v b, SubstE v e) => SubstE v (DistinctAbs b e) where
  substE env (DistinctAbs b e) =
    substB env b \env' b' -> DistinctAbs b' $ substE env' e

instance (HoistableB b, HoistableE e) => HoistableE (DistinctAbs b e) where
  freeVarsE (DistinctAbs b e) = freeVarsE (Abs b e)

fromDistinctAbs :: DistinctAbs b e n -> Abs b e n
fromDistinctAbs (DistinctAbs b e) = Abs b e

-- === various E-kind and B-kind versions of standard containers and classes ===

type PrettyE e = (forall (n::S)       . Pretty (e n  )) :: Constraint
type PrettyB b = (forall (n::S) (l::S). Pretty (b n l)) :: Constraint

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

fromPairE :: PairE e1 e2 n -> (e1 n, e2 n)
fromPairE (PairE x y) = (x, y)

toPairE :: (e1 n, e2 n) -> PairE e1 e2 n
toPairE (x, y) = (PairE x y)

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

data VoidB (n::S) (l::S) deriving (Generic)

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

fromMaybeE :: MaybeE e n -> Maybe (e n)
fromMaybeE (RightE UnitE) = Nothing
fromMaybeE (LeftE e)      = Just e

toMaybeE :: Maybe (e n) -> MaybeE e n
toMaybeE Nothing  = RightE UnitE
toMaybeE (Just e) = LeftE e

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

data LiftB (e::E) (n::S) (l::S) where
  LiftB :: e n -> LiftB e n n

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

-- -- === various convenience utilities ===

infixr 7 @>
class BindsAtMostOneName (b::B) (c::C) | b -> c where
  (@>) :: b i i' -> v c o -> EnvFrag v i i' o

class BindsAtMostOneName (b::B) (c::C)
  =>  BindsOneName (b::B) (c::C) | b -> c where
  binderName :: b i i' -> Name c i'

instance ProvesExt  (NameBinder c) where

instance BindsAtMostOneName (NameBinder c) c where
  b @> x = singletonEnv b x

instance BindsOneName (NameBinder c) c where
  binderName = nameBinderName

instance BindsAtMostOneName (BinderP c ann) c where
  (b:>_) @> x = b @> x

instance BindsOneName (BinderP c ann) c where
  binderName (b:>_) = binderName b

infixr 7 @@>
class BindsNameList (b::B) (c::C) | b -> c where
  (@@>) :: b i i' -> [v c o] -> EnvFrag v i i' o

instance BindsAtMostOneName b c => BindsNameList (Nest b) c where
  (@@>) Empty [] = emptyInFrag
  (@@>) (Nest b rest) (x:xs) = b@>x <.> rest@@>xs
  (@@>) _ _ = error "length mismatch"

applySubst :: (ScopeReader m, SubstE v e, InjectableE e, InjectableV v, FromName v)
           => EnvFrag v o i o -> e i -> m o (e o)
applySubst substFrag x = do
  let fullSubst = idEnv <>> substFrag
  WithScope scope fullSubst' <- addScope fullSubst
  injectM $ fmapNames scope (fullSubst' !) x

applyAbs :: ( InjectableV v, InjectableE e
            , FromName v, ScopeReader m, BindsOneName b c, SubstE v e)
         => Abs b e n -> v c n -> m n (e n)
applyAbs (Abs b body) x = applySubst (b@>x) body

applyNaryAbs :: ( InjectableV v, FromName v, ScopeReader m, BindsNameList b c, SubstE v e
                , SubstB v b, InjectableE e)
             => Abs b e n -> [v c n] -> m n (e n)
applyNaryAbs (Abs bs body) xs = applySubst (bs @@> xs) body

lookupEnvFragProjected :: EnvFrag v i i' o -> Name c i' -> Either (Name c i) (v c o)
lookupEnvFragProjected m name =
  case projectName (envFragAsScope m) name of
    Left  name' -> Left name'
    Right name' -> Right $ lookupEnvFrag m name'

fromEnvPairs :: Nest (EnvPair v o) i i' -> EnvFrag v i i' o
fromEnvPairs Empty = emptyInFrag
fromEnvPairs (Nest (EnvPair b v) rest) =
  singletonEnv b v `catInFrags`fromEnvPairs rest

fmapNest :: (forall ii ii'. b ii ii' -> b' ii ii')
         -> Nest b  i i'
         -> Nest b' i i'
fmapNest _ Empty = Empty
fmapNest f (Nest b rest) = Nest (f b) $ fmapNest f rest

forEachNestItemM :: Monad m
                => Nest b i i'
                -> (forall ii ii'. b ii ii' -> m (b' ii ii'))
                -> m (Nest b' i i')
forEachNestItemM Empty _ = return Empty
forEachNestItemM (Nest b rest) f = Nest <$> f b <*> forEachNestItemM rest f

forEachNestItem :: Nest b i i'
                -> (forall ii ii'. b ii ii' -> b' ii ii')
                -> Nest b' i i'
forEachNestItem nest f = runIdentity $ forEachNestItemM nest (return . f)

-- TODO: make a more general E-kinded Traversable?
traverseEnvFrag :: forall v v' i i' o o' m .
                   Monad m
                => (forall c. NameColor c => v c o -> m (v' c o'))
                -> EnvFrag v i i' o  -> m (EnvFrag v' i i' o')
traverseEnvFrag f frag = liftM fromEnvPairs $
  forEachNestItemM (toEnvPairs frag) \(EnvPair b val) ->
    EnvPair b <$> f val

foldMapEnvFrag
  :: forall v i i' o accum . Monoid accum
  => (forall c. NameColor c => v c o -> accum)
  -> EnvFrag v i i' o -> accum
foldMapEnvFrag f frag =
  execWriter $ traverseEnvFrag (\x -> tell (f x) >> return x) frag

nestLength :: Nest b n l -> Int
nestLength Empty = 0
nestLength (Nest _ rest) = 1 + nestLength rest

nestToList :: BindsNames b
           => (forall n' l'. Ext l' l => b n' l' -> a)
           -> Nest b n l -> [a]
nestToList _ Empty = []
nestToList f (Nest b rest) = b' : nestToList f rest
  where b' = withExtEvidence (toExtEvidence rest) $ f b

splitNestAt :: Int -> Nest b n l -> PairB (Nest b) (Nest b) n l
splitNestAt 0 bs = PairB Empty bs
splitNestAt _  Empty = error "split index too high"
splitNestAt n (Nest b rest) =
  case splitNestAt (n-1) rest of
    PairB xs ys -> PairB (Nest b xs) ys

binderAnn :: BinderP c ann n l -> ann n
binderAnn (_:>ann) = ann

withManyFresh :: Distinct n
              => [NameHint] -> NameColorRep c -> Scope n
              -> (forall l. (Ext n l, Distinct l) => Nest (NameBinder c) n l -> a) -> a
withManyFresh [] _ _ cont = cont Empty
withManyFresh (h:hs) rep scope cont =
  withFresh h rep scope \b ->
    withManyFresh hs rep (scope `extendOutMap` toScopeFrag b) \bs ->
      cont $ Nest b bs

-- === versions of monad constraints with scope params ===

type MonadKind  =           * -> *
type MonadKind1 =      S -> * -> *
type MonadKind2 = S -> S -> * -> *

type Monad1 (m :: MonadKind1) = forall (n::S)        . Monad (m n  )
type Monad2 (m :: MonadKind2) = forall (n::S) (l::S) . Monad (m n l)

type Fallible1 (m :: MonadKind1) = forall (n::S)        . Fallible (m n  )
type Fallible2 (m :: MonadKind2) = forall (n::S) (l::S) . Fallible (m n l)

type MonadIO1 (m :: MonadKind1) = forall (n::S)        . MonadIO (m n  )
type MonadIO2 (m :: MonadKind2) = forall (n::S) (l::S) . MonadIO (m n l)

type Catchable1 (m :: MonadKind1) = forall (n::S)        . Catchable (m n  )
type Catchable2 (m :: MonadKind2) = forall (n::S) (l::S) . Catchable (m n l)

type Searcher1 (m :: MonadKind1) = forall (n::S)        . Searcher (m n  )
type Searcher2 (m :: MonadKind2) = forall (n::S) (l::S) . Searcher (m n l)

type CtxReader1 (m :: MonadKind1) = forall (n::S)        . CtxReader (m n  )
type CtxReader2 (m :: MonadKind2) = forall (n::S) (l::S) . CtxReader (m n l)

type MonadFail1 (m :: MonadKind1) = forall (n::S)        . MonadFail (m n  )
type MonadFail2 (m :: MonadKind2) = forall (n::S) (l::S) . MonadFail (m n l)

type ScopeReader2      (m::MonadKind2) = forall (n::S). ScopeReader      (m n)
type ScopeExtender2    (m::MonadKind2) = forall (n::S). ScopeExtender    (m n)

type AlwaysImmut2     (m::MonadKind2) = forall (n::S). AlwaysImmut     (m n)

type Alternative1 (m::MonadKind1) = forall (n::S)        . Alternative (m n)
type Alternative2 (m::MonadKind2) = forall (n::S) (l::S ). Alternative (m n l)

type Monoid1 (m :: E) = forall (n::S). Monoid (m n)

class MonadTrans1 (t :: MonadKind -> MonadKind1) where
  lift1 :: Monad m => m a -> t m n a

-- === subst monad ===

-- Only alllows non-trivial substitution with names that match the parameter
-- `cMatch`. For example, this lets us substitute ordinary variables in Core
-- with Atoms, while ensuring that things like data def names only get renamed.
data SubstVal (cMatch::C) (atom::E) (c::C) (n::S) where
  SubstVal :: atom n   -> SubstVal c      atom c n
  Rename   :: Name c n -> SubstVal cMatch atom c n

withFreshM :: (ScopeExtender m, AlwaysImmut m)
           => NameHint
           -> NameColorRep c
           -> (forall o'. (Distinct o', Ext o o')
                          => NameBinder c o o' -> m o' a)
           -> m o a
withFreshM hint rep cont = do
  Distinct <- getDistinct
  Immut <- getImmut
  m <- getScope
  withFresh hint rep m \b' -> do
    extendScope (toScopeFrag b') $
      cont b'

withFreshLike
  :: (AlwaysImmut m, ScopeExtender m, HasNameHint hint, HasNameColor hint c)
  => hint
  -> (forall o'. NameBinder c o o' -> m o' a)
  -> m o a
withFreshLike hint cont =
  withFreshM (getNameHint hint) (getNameColor hint) cont

class ColorsNotEqual a b where
  notEqProof :: ColorsEqual a b -> r

instance (ColorsNotEqual cMatch c)
         => (SubstE (SubstVal cMatch atom) (Name c)) where
  substE (_, env) name =
    case env ! name of
      Rename name' -> name'
      SubstVal _ -> notEqProof (ColorsEqual :: ColorsEqual c cMatch)

instance (SubstE (SubstVal cMatch atom) atom, NameColor c)
         => SubstE (SubstVal cMatch atom) (SubstVal cMatch atom c) where
  substE (_, env) (Rename name) = env ! name
  substE env (SubstVal val) = SubstVal $ substE env val

instance (SubstE (SubstVal cMatch atom) atom, InjectableE atom)
         => SubstV (SubstVal cMatch atom) (SubstVal cMatch atom) where

-- TODO: we can fill out the full (N^2) set of instances if we need to
instance ColorsNotEqual AtomNameC DataDefNameC where notEqProof = \case
instance ColorsNotEqual AtomNameC ClassNameC   where notEqProof = \case
instance ColorsNotEqual AtomNameC SuperclassNameC where notEqProof = \case

-- === alpha-renaming-invariant equality checking ===

type AlphaEq e = AlphaEqE e  :: Constraint

-- TODO: consider generalizing this to something that can also handle e.g.
-- unification and type checking with some light reduction
class ( forall i1 i2 o. Monad (m i1 i2 o)
      , forall i1 i2 o. Fallible (m i1 i2 o)
      , forall i1 i2 o. MonadFail (m i1 i2 o)
      , forall i1 i2.   ScopeExtender (m i1 i2)
      , forall i1 i2.   AlwaysImmut (m i1 i2))
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

addScope :: (ScopeReader m, InjectableE e) => e n -> m n (WithScope e n)
addScope e = liftImmut do
  scope <- getScope
  Distinct <- getDistinct
  return $ WithScope scope (inject e)

alphaEq :: (AlphaEqE e, ScopeReader m)
        => e n -> e n -> m n Bool
alphaEq e1 e2 = do
  WithScope scope (PairE e1' e2') <- addScope $ PairE e1 e2
  return $ case checkAlphaEqPure scope e1' e2' of
    Success _ -> True
    Failure _ -> False

checkAlphaEq :: (AlphaEqE e, Fallible1 m, ScopeReader m)
             => e n -> e n -> m n ()
checkAlphaEq e1 e2 = do
  WithScope scope (PairE e1' e2') <- addScope $ PairE e1 e2
  liftExcept $ checkAlphaEqPure scope e1' e2'

alphaEqPure :: (AlphaEqE e, Distinct n)
            => Scope n -> e n -> e n -> Bool
alphaEqPure scope e1 e2 = checkAlphaEqPure scope e1 e2 & \case
  Success _ -> True
  Failure _ -> False

-- TODO: Support sets of types and eliminate this!
nubAlphaEq :: (AlphaEqE e, ScopeReader m) => [e n] -> m n [e n]
nubAlphaEq l = fromListE <$> liftImmut do
  scope <- getScope
  Distinct <- getDistinct
  return $ ListE $ nubBy (alphaEqPure scope) $ fromListE $ inject $ ListE l

checkAlphaEqPure :: (AlphaEqE e, Distinct n)
                 => Scope n -> e n -> e n -> Except ()
checkAlphaEqPure scope e1 e2 =
  runScopeReaderT scope $
    flip runReaderT (emptyInMap, emptyInMap) $ runZipEnvReaderT $
      withEmptyZipEnv $ alphaEqE e1 e2

alphaElem :: AlphaEqE e => ScopeReader m => e n -> [e n] -> m n Bool
alphaElem _ [] = return False
alphaElem e1 (e2:rest) =
  alphaEq e1 e2 >>= \case
    True -> return True
    False -> alphaElem e1 rest

instance AlphaEqV Name
instance AlphaEqE (Name c) where
  alphaEqE v1 v2 = do
    v1' <- lookupZipEnvFst v1
    v2' <- lookupZipEnvSnd v2
    unless (v1' == v2') zipErr

instance AlphaEqB (NameBinder c) where
  withAlphaEqB b1 b2 cont = do
    Immut <- getImmut
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

instance AlphaEqE e => AlphaEqB (LiftB e) where
  withAlphaEqB (LiftB e1) (LiftB e2) cont = alphaEqE e1 e2 >> cont

instance AlphaEqE ann => AlphaEqB (BinderP c ann) where
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

type ScopeReaderM = ScopeReaderT Identity

runScopeReaderT :: Distinct n => Scope n -> ScopeReaderT m n a -> m a
runScopeReaderT scope m =
  flip runReaderT (Distinct, scope) $ runScopeReaderT' m

runScopeReaderM :: Distinct n => Scope n -> ScopeReaderM n a -> a
runScopeReaderM scope m = runIdentity $ runScopeReaderT scope m

instance Monad m => ScopeReader (ScopeReaderT m) where
  getDistinct = ScopeReaderT $ asks fst
  getScope = ScopeReaderT $ asks snd
  liftImmut cont = do
    Immut <- getImmut
    Distinct <- getDistinct
    cont

instance Monad m => ScopeExtender (ScopeReaderT m) where
  extendScope frag m = ScopeReaderT $ withReaderT
    (\(_, scope) -> (Distinct, extendOutMap scope frag)) $
        withExtEvidence (toExtEvidence frag) $
          runScopeReaderT' m

instance Monad m => AlwaysImmut (ScopeReaderT m) where
  getImmut = ScopeReaderT $ ReaderT \(_, scope) ->
    return $ withImmutEvidence (scopeToImmut scope) $ Immut

-- === EnvReaderT transformer ===

newtype EnvReaderT (v::V) (m::MonadKind1) (i::S) (o::S) (a:: *) =
  EnvReaderT { runEnvReaderT' :: ReaderT (Env v i o) (m o) a }
  deriving (Functor, Applicative, Monad, MonadFail, Catchable, Fallible, CtxReader,
            Alternative)

type ScopedEnvReader (v::V) = EnvReaderT v (ScopeReaderT Identity) :: MonadKind2

runScopedEnvReader :: Distinct o => Scope o -> Env v i o
                   -> ScopedEnvReader v i o a -> a
runScopedEnvReader scope env m =
  runIdentity $ runScopeReaderT scope $ runEnvReaderT env m

runEnvReaderT :: Env v i o -> EnvReaderT v m i o a -> m o a
runEnvReaderT env m = runReaderT (runEnvReaderT' m) env

instance (InjectableV v, Monad1 m) => EnvReader v (EnvReaderT v m) where
  getEnv = EnvReaderT ask
  withEnv env (EnvReaderT cont) = EnvReaderT $ withReaderT (const env) cont

instance (InjectableV v, ScopeReader m) => ScopeReader (EnvReaderT v m i) where
  getScope = EnvReaderT $ lift getScope
  getDistinct = EnvReaderT $ lift getDistinct
  liftImmut m = EnvReaderT $ ReaderT \env -> liftImmut do
    let EnvReaderT (ReaderT cont) = m
    env' <- injectM env
    cont env'

instance (InjectableV v, ScopeReader m, ScopeExtender m)
         => ScopeExtender (EnvReaderT v m i) where
  extendScope frag m = EnvReaderT $ ReaderT \env ->
    extendScope frag do
      let EnvReaderT (ReaderT cont) = m
      env' <- injectM env
      cont env'

instance (InjectableV v, MonadIO1 m) => MonadIO (EnvReaderT v m i o) where
  liftIO m = EnvReaderT $ lift $ liftIO m

instance AlwaysImmut m => AlwaysImmut (EnvReaderT v m i) where
  getImmut = EnvReaderT $ lift getImmut

instance (Monad1 m, MonadState (s o) (m o)) => MonadState (s o) (EnvReaderT v m i o) where
  state = EnvReaderT . lift . state

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
  getScope = OutReaderT $ lift getScope
  getDistinct = OutReaderT $ lift getDistinct
  liftImmut m = OutReaderT $ ReaderT \env -> liftImmut do
    let OutReaderT (ReaderT cont) = m
    env' <- injectM env
    cont env'

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

instance AlwaysImmut m => AlwaysImmut (OutReaderT e m) where
  getImmut = OutReaderT $ lift getImmut

instance OutReader e m => OutReader e (EnvReaderT v m i) where
  askOutReader = EnvReaderT $ ReaderT $ const askOutReader
  localOutReader e (EnvReaderT (ReaderT f)) = EnvReaderT $ ReaderT $ \env ->
    localOutReader e $ f env

instance (Monad1 m, Alternative (m n)) => Alternative (OutReaderT e m n) where
  empty = OutReaderT $ lift empty
  OutReaderT (ReaderT f1) <|> OutReaderT (ReaderT f2) =
    OutReaderT $ ReaderT \env ->
      f1 env <|> f2 env

instance Searcher1 m => Searcher (OutReaderT e m n) where
  OutReaderT (ReaderT f1) <!> OutReaderT (ReaderT f2) =
    OutReaderT $ ReaderT \env ->
      f1 env <!> f2 env

instance MonadWriter w (m n) => MonadWriter w (OutReaderT e m n) where
  tell w = OutReaderT $ lift $ tell w
  listen = undefined
  pass = undefined

-- === ZipEnvReaderT transformer ===

newtype ZipEnvReaderT (m::MonadKind1) (i1::S) (i2::S) (o::S) (a:: *) =
  ZipEnvReaderT { runZipEnvReaderT :: ReaderT (ZipEnv i1 i2 o) (m o) a }
  deriving (Functor, Applicative, Monad, Fallible, MonadFail)

type ZipEnv i1 i2 o = (Env Name i1 o, Env Name i2 o)

instance ScopeReader m => ScopeReader (ZipEnvReaderT m i1 i2) where
  getScope = ZipEnvReaderT $ lift getScope
  getDistinct = ZipEnvReaderT $ lift getDistinct
  liftImmut m = ZipEnvReaderT $ ReaderT \(env1, env2) -> liftImmut do
    let ZipEnvReaderT (ReaderT cont) = m
    env1' <- injectM env1
    env2' <- injectM env2
    cont (env1', env2')

instance (ScopeReader m, ScopeExtender m)
         => ScopeExtender (ZipEnvReaderT m i1 i2) where
  extendScope frag m =
    ZipEnvReaderT $ ReaderT \(env1, env2) -> do
      extendScope frag do
        let ZipEnvReaderT (ReaderT cont) = m
        env1' <- injectM env1
        env2' <- injectM env2
        cont (env1', env2')

instance (AlwaysImmut m, ScopeReader m, ScopeExtender m)
         => AlwaysImmut (ZipEnvReaderT m i1 i2) where
  getImmut = ZipEnvReaderT $ lift $ getImmut

instance (Monad1 m, ScopeReader m, ScopeExtender m, Fallible1 m, AlwaysImmut m)
         => ZipEnvReader (ZipEnvReaderT m) where

  lookupZipEnvFst v = ZipEnvReaderT $ (!v) <$> fst <$> ask
  lookupZipEnvSnd v = ZipEnvReaderT $ (!v) <$> snd <$> ask

  extendZipEnvFst frag (ZipEnvReaderT cont) = ZipEnvReaderT $ withReaderT (onFst (<>>frag)) cont
  extendZipEnvSnd frag (ZipEnvReaderT cont) = ZipEnvReaderT $ withReaderT (onSnd (<>>frag)) cont

  withEmptyZipEnv (ZipEnvReaderT cont) =
    ZipEnvReaderT $ withReaderT (const (newEnv id, newEnv id)) cont

-- === monadish thing for computations that produce names ===

class NameGen (m :: E -> S -> *) where
  returnG :: e n -> m e n
  bindG   :: m e n -> (forall l. (Distinct l, Ext n l) => e l -> m e' l) -> m e' n
  getDistinctEvidenceG :: m DistinctEvidence n

fmapG :: NameGen m => (forall l. e1 l -> e2 l) -> m e1 n -> m e2 n
fmapG f e = e `bindG` (returnG . f)

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
    return $ DistinctAbs id Distinct

-- === in-place scope updating monad -- immutable fragment ===

data InplaceT (bindings::E) (decls::B) (m::MonadKind) (n::S) (a :: *) = UnsafeMakeInplaceT
  { unsafeRunInplaceT :: Distinct n => bindings n -> m (a, decls UnsafeS UnsafeS) }

runInplaceT
  :: (ExtOutMap b d, Monad m)
  => (Distinct n, Immut n)
  => b n
  -> InplaceT b d m n a
  -> m (d n n, a)
runInplaceT bindings (UnsafeMakeInplaceT f) = do
  (result, d) <- f bindings
  return (unsafeCoerceB d, result)

-- Special case of extending without introducing new names
-- (doesn't require `Mut n`)
extendTrivialInplaceT
  :: (ExtOutMap b d, Monad m)
  => d n n
  -> InplaceT b d m n ()
extendTrivialInplaceT d =
  UnsafeMakeInplaceT \_ -> return ((), unsafeCoerceB d)

getOutMapInplaceT
  :: (ExtOutMap b d, Monad m)
  => Immut n
  => InplaceT b d m n (b n)
getOutMapInplaceT = UnsafeMakeInplaceT \bindings -> return (bindings, emptyOutFrag)

-- === in-place scope updating monad -- mutable stuff ===

-- This is intended to make it possible to implement `extendBindings` from
-- `BindingsReader`. We don't require an `Immut l` constraint so that it's
-- possible to extend with nameless fragments. But if `n` and `l` aren't equal
-- the `Immut l` must exist, as proved by the supplied function that produces a
-- `b l`.
extendInplaceTLocal
  :: (ExtOutMap b d, Monad m)
  => Distinct l
  => (b n -> b l)
  -> InplaceT b d m l a
  -> InplaceT b d m n a
extendInplaceTLocal f cont =
  UnsafeMakeInplaceT \bindings ->
    unsafeRunInplaceT cont (f bindings)

extendInplaceT
  :: forall m b d e n.
     (ExtOutMap b d, Monad m, InjectableE e)
  => Mut n
  => (forall l. (Distinct l, Immut l, Ext n l) => InplaceT b d m l (DistinctAbs d e l))
  -> InplaceT b d m n (e n)
extendInplaceT cont = do
  Immut <- return (fabricateImmutEvidence :: ImmutEvidence n)
  Distinct <- getDistinct
  DistinctAbs decls result <- cont
  UnsafeMakeInplaceT $ const $ return (unsafeCoerceE result, unsafeCoerceB decls)

locallyMutableInplaceT
  :: forall m b d n e.
     (ExtOutMap b d, Monad m, InjectableE e)
  => Immut n
  => (forall l. (Mut l, Distinct l, Ext n l) => InplaceT b d m l (e l))
  -> InplaceT b d m n (DistinctAbs d e n)
locallyMutableInplaceT cont = do
  UnsafeMakeInplaceT \bindings -> do
    (e, decls) <- withMutEvidence (fabricateMutEvidence :: MutEvidence n) do
                    unsafeRunInplaceT cont bindings
    return (DistinctAbs (unsafeCoerceB decls) e, emptyOutFrag)

locallyImmutableInplaceT
  :: forall m b d n e.
     (ExtOutMap b d, Monad m, InjectableE e)
  => (forall l. (Immut l, Ext n l) => InplaceT b d m l (e l))
  -> InplaceT b d m n (e n)
locallyImmutableInplaceT doWithImmut = do
  Immut <- return (fabricateImmutEvidence :: ImmutEvidence n)
  doWithImmut

liftBetweenInplaceTs
  :: Monad m
  => (forall a'. m' a' -> m a')
  -> (bs n -> bs' n)
  -> (forall l l' . Distinct l' => ds' l l' -> ds  l l')
  -> InplaceT bs' ds' m' n a
  -> InplaceT bs  ds  m  n a
liftBetweenInplaceTs liftInner lowerBindings liftDecls (UnsafeMakeInplaceT f) =
  UnsafeMakeInplaceT \bindingsOuter -> do
    (result, declsInner) <- liftInner $ f $ lowerBindings bindingsOuter
    withDistinctEvidence (fabricateDistinctEvidence :: DistinctEvidence UnsafeS) $
      return (result, liftDecls declsInner)

emitInplaceT
  :: (NameColor c, InjectableE e, ExtOutMap b d, Monad m)
  => Mut o
  => NameHint -> e o
  -> (forall n l. (Ext n l, Distinct l) => NameBinder c n l -> e n -> d n l)
  -> InplaceT b d m o (Name c o)
emitInplaceT hint e buildDecls =
  extendInplaceT do
    scope <- getScope
    return $ withFresh hint nameColorRep scope \b ->
      DistinctAbs (buildDecls b (inject e)) (binderName b)

-- === predicates for mutable and immutable scope parameters ===

class Mut (n::S)
data MutEvidence (n::S) where
  Mut :: Mut n => MutEvidence n
instance Mut UnsafeS

fabricateMutEvidence :: forall n. MutEvidence n
fabricateMutEvidence =
  withMutEvidence (error "pure fabrication" :: MutEvidence n) Mut

withMutEvidence :: forall n a. MutEvidence n -> (Mut n => a) -> a
withMutEvidence _ cont = fromWrapWithMut
 ( TrulyUnsafe.unsafeCoerce ( WrapWithMut cont :: WrapWithMut n       a
                                             ) :: WrapWithMut UnsafeS a)
newtype WrapWithMut n r =
  WrapWithMut { fromWrapWithMut :: Mut n => r }

-- proves that the names in n are distinct
class Immut (n::S)
data ImmutEvidence (n::S) where
  Immut :: Immut n => ImmutEvidence n
instance Immut UnsafeS

fabricateImmutEvidence :: forall n. ImmutEvidence n
fabricateImmutEvidence =
  withImmutEvidence (error "pure fabrication" :: ImmutEvidence n) Immut

withImmutEvidence :: forall n a. ImmutEvidence n -> (Immut n => a) -> a
withImmutEvidence _ cont = fromWrapWithImmut
 ( TrulyUnsafe.unsafeCoerce ( WrapWithImmut cont :: WrapWithImmut n       a
                                               ) :: WrapWithImmut UnsafeS a)

-- We should never have a `Scope n` if we're updating `n` in-place
scopeToImmut :: Scope n -> ImmutEvidence n
scopeToImmut _ = fabricateImmutEvidence

toImmutEvidence :: HasScope e => e n -> ImmutEvidence n
toImmutEvidence e = withImmutEvidence (scopeToImmut $ toScope e) Immut

newtype WrapWithImmut n r =
  WrapWithImmut { fromWrapWithImmut :: Immut n => r }

-- === InplaceT instances ===

instance (ExtOutMap bindings decls, BindsNames decls, InjectableB decls, Monad m)
         => Functor (InplaceT bindings decls m n) where
  fmap = liftM

instance (ExtOutMap bindings decls, BindsNames decls, InjectableB decls, Monad m)
         => Applicative (InplaceT bindings decls m n) where
  pure = return
  liftA2 = liftM2

instance (ExtOutMap bindings decls, BindsNames decls, InjectableB decls, Monad m)
         => Monad (InplaceT bindings decls m n) where
  return x = UnsafeMakeInplaceT \_ -> do
    Distinct <- return (fabricateDistinctEvidence :: DistinctEvidence UnsafeS)
    return (x, emptyOutFrag)
  m >>= f = UnsafeMakeInplaceT \outMap -> do
    (x, b1) <- unsafeRunInplaceT m outMap
    let outMap' = outMap `extendOutMap` unsafeCoerceB b1
    (y, b2) <- unsafeRunInplaceT (f x) outMap'
    Distinct <- return (fabricateDistinctEvidence :: DistinctEvidence UnsafeS)
    return (y, catOutFrags (unsafeCoerceE (toScope outMap')) b1 b2)

instance (ExtOutMap bindings decls, BindsNames decls, InjectableB decls, Monad m)
         => ScopeReader (InplaceT bindings decls m) where
  getDistinct = UnsafeMakeInplaceT \_ ->
    return (Distinct, emptyOutFrag)
  getScope = toScope <$> getOutMapInplaceT
  liftImmut cont = locallyImmutableInplaceT do
    Distinct <- getDistinct
    cont

instance (ExtOutMap bindings decls, BindsNames decls, InjectableB decls, Monad m, MonadFail m)
         => MonadFail (InplaceT bindings decls m n) where
  fail s = lift1 $ fail s

instance (ExtOutMap bindings decls, BindsNames decls, InjectableB decls, Monad m, Fallible m)
         => Fallible (InplaceT bindings decls m n) where
  throwErrs errs = UnsafeMakeInplaceT \_ -> throwErrs errs
  addErrCtx ctx cont = UnsafeMakeInplaceT \bindings ->
    addErrCtx ctx $ unsafeRunInplaceT cont bindings

instance (ExtOutMap bindings decls, BindsNames decls, InjectableB decls, Monad m, CtxReader m)
         => CtxReader (InplaceT bindings decls m n) where
  getErrCtx = lift1 getErrCtx

instance ( ExtOutMap bindings decls, BindsNames decls, InjectableB decls, Monad m
         , Alternative m)
         => Alternative (InplaceT bindings decls m n) where
  empty = lift1 empty
  UnsafeMakeInplaceT f1 <|> UnsafeMakeInplaceT f2 = UnsafeMakeInplaceT \bindings ->
    f1 bindings <|> f2 bindings

instance ( ExtOutMap bindings decls, BindsNames decls, InjectableB decls,
           Monad m, Alternative m, Searcher m)
         => Searcher (InplaceT bindings decls m n) where
  UnsafeMakeInplaceT f1 <!> UnsafeMakeInplaceT f2 = UnsafeMakeInplaceT \bindings ->
    f1 bindings <!> f2 bindings

instance ( ExtOutMap bindings decls, BindsNames decls, InjectableB decls,
           Catchable m)
         => Catchable (InplaceT bindings decls m n) where
  catchErr (UnsafeMakeInplaceT f1) handler = UnsafeMakeInplaceT \bindings ->
    f1 bindings `catchErr` \err -> case handler err of
      UnsafeMakeInplaceT f2 -> f2 bindings

instance ( ExtOutMap bindings decls, BindsNames decls, InjectableB decls
         , MonadWriter w m)
         => MonadWriter w (InplaceT bindings decls m n) where
  tell w = lift1 $ tell w
  listen = undefined
  pass = undefined

instance (ExtOutMap bindings decls, BindsNames decls, InjectableB decls)
         => MonadTrans1 (InplaceT bindings decls) where
  lift1 m = UnsafeMakeInplaceT \_ -> (,emptyOutFrag) <$> m

instance ( ExtOutMap bindings decls, BindsNames decls, InjectableB decls
         , MonadReader r m)
         => MonadReader r (InplaceT bindings decls m n) where
  ask = lift1 $ ask
  local = undefined

instance ( ExtOutMap bindings decls, BindsNames decls, InjectableB decls
         , MonadIO m)
         => MonadIO (InplaceT bindings decls m n) where
  liftIO = lift1 . liftIO

-- === name hints ===

class HasNameHint a where
  getNameHint :: a -> NameHint

instance HasNameHint (Name s n) where
  getNameHint name = getNameHint $ getRawName name

instance HasNameHint (NameBinder s n l) where
  getNameHint b = getNameHint $ getRawName $ binderName b

instance HasNameHint RawName where
  getNameHint (RawName s _) = Hint s

instance HasNameHint String where
  getNameHint = fromString

instance HasNameHint (BinderP c ann n l) where
  getNameHint (b:>_) = getNameHint b

-- === getting name colors ===

class HasNameColor a c | a -> c where
  getNameColor :: a -> NameColorRep c

instance HasNameColor (NameBinder c n l) c where
  getNameColor b = getNameColor $ nameBinderName b

-- === handling the dynamic/heterogeneous stuff for Env ===

data EnvVal (v::V) (n::S) where
  EnvVal :: NameColorRep c -> v c n -> EnvVal v n

deriving instance (forall c. Show (v c n)) => Show (EnvVal v n)

fromEnvVal ::  NameColorRep c -> EnvVal v o -> v c o
fromEnvVal rep (EnvVal rep' val) =
  case eqNameColorRep rep rep' of
    Just ColorsEqual -> val
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
deriving instance Ord  (NameColorRep c)

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

data ColorsEqual (c1::C) (c2::C) where
  ColorsEqual :: ColorsEqual c c

eqNameColorRep :: NameColorRep c1 -> NameColorRep c2 -> Maybe (ColorsEqual c1 c2)
eqNameColorRep rep1 rep2 = case (rep1, rep2) of
  (AtomNameRep      , AtomNameRep      ) -> Just ColorsEqual
  (DataDefNameRep   , DataDefNameRep   ) -> Just ColorsEqual
  (TyConNameRep     , TyConNameRep     ) -> Just ColorsEqual
  (DataConNameRep   , DataConNameRep   ) -> Just ColorsEqual
  (ClassNameRep     , ClassNameRep     ) -> Just ColorsEqual
  (SuperclassNameRep, SuperclassNameRep) -> Just ColorsEqual
  (MethodNameRep    , MethodNameRep    ) -> Just ColorsEqual
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
  Just ColorsEqual -> Just x
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

instance InjectableV v => InjectableE (Env v i) where
  injectionProofE fresh (Env f m) =
    Env (\name -> withNameColorRep (getNameColor name)  $
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

instance (HoistableB b, HoistableE e) => HoistableE (Abs b e) where
  freeVarsE (Abs b e) = freeVarsB b <> hoistNameSet b (freeVarsE e)

instance (SubstB v b, SubstE v e) => SubstE v (Abs b e) where
  substE env (Abs b body) = do
    substB env b \env' b' -> Abs b' $ substE env' body

instance (BindsNames b1, BindsNames b2) => ProvesExt  (PairB b1 b2) where
instance (BindsNames b1, BindsNames b2) => BindsNames (PairB b1 b2) where
  toScopeFrag (PairB b1 b2) = toScopeFrag b1 >>> toScopeFrag b2

instance (InjectableB b1, InjectableB b2) => InjectableB (PairB b1 b2) where
  injectionProofB fresh (PairB b1 b2) cont =
    injectionProofB fresh b1 \fresh' b1' ->
      injectionProofB fresh' b2 \fresh'' b2' ->
        cont fresh'' (PairB b1' b2')

instance ( BindsNames b1, SubstB v b1
         , BindsNames b2, SubstB v b2
         , InjectableV v, FromName v)
         => SubstB v (PairB b1 b2) where
  substB env (PairB b1 b2) cont =
    substB env b1 \env' b1' ->
      substB env' b2 \env'' b2' ->
        cont env'' $ PairB b1' b2'

  substBDistinct (scope, env) (PairB b1 b2) = do
    withSubscopeDistinct b2 do
      withExtEvidence b1 do
        let b1' = substBDistinct (scope, env) b1
        let scope' = scope `extendOutMap` toScopeFrag b1
        let env' = inject env <>> idEnvFrag (toScopeFrag b1)
        let b2' = substBDistinct (scope', env') b2
        PairB b1' b2'

instance InjectableE e => InjectableB (LiftB e) where
  injectionProofB fresh (LiftB e) cont = cont fresh $ LiftB $ injectionProofE fresh e

instance ProvesExt (LiftB e) where
instance BindsNames (LiftB e) where
  toScopeFrag (LiftB _) = id

instance HoistableE e => HoistableB (LiftB e) where
  freeVarsB (LiftB e) = freeVarsE e

instance (InjectableE e, SubstE v e) => SubstB v (LiftB e) where
  substB env (LiftB e) cont = cont env $ LiftB $ substE env e
  substBDistinct env (LiftB e) = LiftB $ substE env e

instance (BindsNames b1, BindsNames b2) => ProvesExt  (EitherB b1 b2) where
instance (BindsNames b1, BindsNames b2) => BindsNames (EitherB b1 b2) where
  toScopeFrag (LeftB  b) = toScopeFrag b
  toScopeFrag (RightB b) = toScopeFrag b

instance (HoistableB b1, HoistableB b2) => HoistableB (EitherB b1 b2) where
  freeVarsB (LeftB  b) = freeVarsB b
  freeVarsB (RightB b) = freeVarsB b

instance (InjectableB b1, InjectableB b2) => InjectableB (EitherB b1 b2) where
  injectionProofB fresh (LeftB b) cont =
    injectionProofB fresh b \fresh' b' ->
      cont fresh' (LeftB b')
  injectionProofB fresh (RightB b) cont =
    injectionProofB fresh b \fresh' b' ->
      cont fresh' (RightB b')

instance (SubstB v b1, SubstB v b2) => SubstB v (EitherB b1 b2) where
  substB env (LeftB b) cont =
    substB env b \env' b' ->
      cont env' $ LeftB b'
  substB env (RightB b) cont =
    substB env b \env' b' ->
      cont env' $ RightB b'

  substBDistinct env (LeftB  b) = LeftB  $ substBDistinct env b
  substBDistinct env (RightB b) = RightB $ substBDistinct env b

instance GenericB (BinderP c ann) where
  type RepB (BinderP c ann) = PairB (LiftB ann) (NameBinder c)
  fromB (b:>ann) = PairB (LiftB ann) b
  toB   (PairB (LiftB ann) b) = b:>ann

instance InjectableE ann => InjectableB (BinderP c ann)
instance (InjectableE ann, SubstE v ann, InjectableV v) => SubstB v (BinderP c ann)
instance ProvesExt  (BinderP c ann)
instance BindsNames (BinderP c ann)

instance BindsNames b => ProvesExt  (Nest b) where
instance BindsNames b => BindsNames (Nest b) where
  toScopeFrag Empty = id
  toScopeFrag (Nest b rest) = toScopeFrag b >>> toScopeFrag rest

instance (BindsNames b, SubstB v b, InjectableV v)
         => SubstB v (Nest b) where
  substB env (Nest b bs) cont =
    substB env b \env' b' ->
      substB env' bs \env'' bs' ->
        cont env'' $ Nest b' bs'
  substB env Empty cont = cont env Empty

  substBDistinct _ Empty = Empty
  substBDistinct env (Nest b bs) =
    case substBDistinct env $ PairB b bs of
      PairB b' bs' -> Nest b' bs'

instance InjectableE UnitE where
  injectionProofE _ UnitE = UnitE

instance HoistableE UnitE where
  freeVarsE UnitE = mempty

instance FromName v => SubstE v UnitE where
  substE _ UnitE = UnitE

instance (Functor f, InjectableE e) => InjectableE (ComposeE f e) where
  injectionProofE fresh (ComposeE xs) = ComposeE $ fmap (injectionProofE fresh) xs

instance (Traversable f, HoistableE e) => HoistableE (ComposeE f e) where
  freeVarsE (ComposeE xs) = foldMap freeVarsE xs

instance (Traversable f, SubstE v e) => SubstE v (ComposeE f e) where
  substE env (ComposeE xs) = ComposeE $ fmap (substE env) xs

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
  substBDistinct _ UnitB = UnitB

instance InjectableB VoidB where
  injectionProofB _ _ _ = error "impossible"

instance ProvesExt VoidB where
instance BindsNames VoidB where
  toScopeFrag _ = error "impossible"

instance HoistableB VoidB where
  freeVarsB _ = error "impossible"

instance AlphaEqB VoidB where
  withAlphaEqB _ _ _ = error "impossible"

instance FromName v => SubstB v VoidB where
  substB _ _ _ = error "impossible"
  substBDistinct _ _ = error "impossible"

instance InjectableE const => InjectableV (ConstE const)
instance InjectableE const => InjectableE (ConstE const ignored) where
  injectionProofE fresh (ConstE e) = ConstE $ injectionProofE fresh e

instance InjectableE VoidE where
  injectionProofE _ _ = error "impossible"

instance HoistableE VoidE where
  freeVarsE _ = error "impossible"

instance AlphaEqE VoidE where
  alphaEqE _ _ = error "impossible"

instance FromName v => SubstE v VoidE where
  substE _ _ = error "impossible"

instance (InjectableE e1, InjectableE e2) => InjectableE (PairE e1 e2) where
  injectionProofE fresh (PairE e1 e2) =
    PairE (injectionProofE fresh e1) (injectionProofE fresh e2)

instance (HoistableE e1, HoistableE e2) => HoistableE (PairE e1 e2) where
  freeVarsE (PairE e1 e2) = freeVarsE e1 <> freeVarsE e2

instance (SubstE v e1, SubstE v e2) => SubstE v (PairE e1 e2) where
  substE env (PairE x y) = PairE (substE env x) (substE env y)

instance (InjectableE e1, InjectableE e2) => InjectableE (EitherE e1 e2) where
  injectionProofE fresh (LeftE  e) = LeftE  (injectionProofE fresh e)
  injectionProofE fresh (RightE e) = RightE (injectionProofE fresh e)

instance (HoistableE e1, HoistableE e2) => HoistableE (EitherE e1 e2) where
  freeVarsE (LeftE  e) = freeVarsE e
  freeVarsE (RightE e) = freeVarsE e

instance (SubstE v e1, SubstE v e2) => SubstE v (EitherE e1 e2) where
  substE env (LeftE  x) = LeftE  $ substE env x
  substE env (RightE x) = RightE $ substE env x

instance InjectableE e => InjectableE (ListE e) where
  injectionProofE fresh (ListE xs) = ListE $ map (injectionProofE fresh) xs

instance AlphaEqE e => AlphaEqE (ListE e) where
  alphaEqE (ListE xs) (ListE ys)
    | length xs == length ys = mapM_ (uncurry alphaEqE) (zip xs ys)
    | otherwise              = zipErr

instance Monoid (ListE e n) where
  mempty = ListE []

instance Semigroup (ListE e n) where
  ListE xs <> ListE ys = ListE $ xs <> ys

instance InjectableE (LiftE a) where
  injectionProofE _ (LiftE x) = LiftE x

instance HoistableE (LiftE a) where
  freeVarsE (LiftE _) = mempty

instance FromName v => SubstE v (LiftE a) where
  substE _ (LiftE x) = LiftE x

instance Eq a => AlphaEqE (LiftE a) where
  alphaEqE (LiftE x) (LiftE y) = unless (x == y) zipErr

instance SubstE v e => SubstE v (ListE e) where
  substE env (ListE xs) = ListE $ map (substE env) xs

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
  toScopeFrag env = envFragAsScope $ fromRecEnvFrag env
instance HoistableV v => HoistableB (RecEnvFrag v) where
  freeVarsB (RecEnvFrag env) = freeVarsE (Abs (envFragAsScope env) env)

-- Traversing a recursive set of bindings is a bit tricky because we have to do
-- two passes: first we rename the binders, then we go and subst the payloads.
instance (InjectableV substVal, SubstV substVal v) => SubstB substVal (RecEnvFrag v) where
  substB env (RecEnvFrag recEnv) cont = do
    let pairs = toEnvPairs recEnv
    renameEnvPairBinders env pairs \env' pairs' -> do
      let pairs'' = forEachNestItem pairs' \(EnvPair b x) ->
                      EnvPair b $ substE env' x
      cont env' $ RecEnvFrag $ fromEnvPairs pairs''

  substBDistinct (scope, env) (RecEnvFrag recEnv) = do
    let scopeFrag = toScopeFrag (RecEnvFrag recEnv)
    withExtEvidence scopeFrag do
      let scope' = scope `extendOutMap` scopeFrag
      let env' = inject env <>> idEnvFrag scopeFrag
      let pairs' = forEachNestItem (toEnvPairs recEnv) \(EnvPair b x) ->
                     EnvPair b $ substE (scope', env') x
      RecEnvFrag $ fromEnvPairs pairs'

renameEnvPairBinders
  :: (Distinct o, InjectableV v, InjectableV substVal, FromName substVal)
  => (Scope o, Env substVal i o)
  -> Nest (EnvPair v ignored) i i'
  -> (forall o'.
         Distinct o'
      => (Scope o', Env substVal i' o')
      -> Nest (EnvPair v ignored) o o'
      -> a)
  -> a
renameEnvPairBinders env Empty cont = cont env Empty
renameEnvPairBinders env (Nest (EnvPair b v) rest) cont =
  substB env b \env' b' ->
    renameEnvPairBinders env' rest \env'' rest' ->
      cont env'' (Nest (EnvPair b' v) rest')

refreshRecEnvFrag :: (Distinct o,  InjectableV v, InjectableV substVal, SubstV substVal v)
                  => Scope o
                  -> Env substVal i o
                  -> RecEnvFrag v i i'
                  -> DistinctAbs (RecEnvFrag v) (Env substVal i') o
refreshRecEnvFrag scope env (RecEnvFrag frag) =
  renameEnvPairBindersPure scope env (toEnvPairs frag) \scope' env' pairs ->
    let frag' = fmapEnvFrag (\_ val -> fmapNames scope' (env'!) val) (fromEnvPairs pairs)
    in DistinctAbs (RecEnvFrag frag') env'

substAbsDistinct
  :: (Distinct o, SubstB v b, SubstE v e, FromName v)
  => Scope o -> Env v i o -> Abs b e i -> DistinctAbs b e o
substAbsDistinct scope env (Abs b e) =
  substB (scope, env) b \env' b' ->
    DistinctAbs b' $ substE env' e

refreshAbs :: forall n b e.
              (Distinct n, SubstB Name b, SubstE Name e)
           => Scope n -> Abs b e n -> DistinctAbs b e n
refreshAbs scope ab = substAbsDistinct scope (idEnv :: Env Name n n) ab

renameEnvPairBindersPure
  :: (Distinct o, InjectableV v, InjectableV substVal, FromName substVal)
  => Scope o
  -> Env substVal i o
  -> Nest (EnvPair v ignored) i i'
  -> (forall o'. Distinct o' => Scope o' -> Env substVal i' o' -> Nest (EnvPair v ignored) o o' -> a)
  -> a
renameEnvPairBindersPure scope env Empty cont = cont scope env Empty
renameEnvPairBindersPure scope env (Nest (EnvPair b v) rest) cont = do
  let rep = getNameColor $ nameBinderName b
  withFresh (getNameHint b) rep scope \b' -> do
    let env' = inject env <>> b @> (fromName $ binderName b')
    let scope' = extendOutMap scope $ toScopeFrag b'
    renameEnvPairBindersPure scope' env' rest \scope'' env'' rest' ->
      cont scope'' env'' $ Nest (EnvPair b' v) rest'

instance InjectableV v => InjectableB (RecEnvFrag v) where
  injectionProofB _ _ _ = todoInjectableProof

instance SubstV substVal v => SubstE substVal (EnvVal v) where
  substE env (EnvVal rep v) =
    withNameColorRep rep $ EnvVal rep $ substE env v

instance HoistableV v => HoistableE (EnvVal v) where
  freeVarsE (EnvVal rep v) =
    withNameColorRep rep $ freeVarsE v

instance Store RawName
instance Store (UnitE n)
instance Store (VoidE n)
instance (Store (e1 n), Store (e2 n)) => Store (PairE   e1 e2 n)
instance (Store (e1 n), Store (e2 n)) => Store (EitherE e1 e2 n)
instance Store (e n) => Store (ListE  e n)
instance Store a => Store (LiftE a n)
instance Store (const n) => Store (ConstE const ignored n)
instance (NameColor c, Store (ann n)) => Store (BinderP c ann n l)

instance ( forall c. NameColor c => Store (v c o')
         , forall c. NameColor c => Generic (v c o'))
         => Store (RecEnvFrag v o o')

instance ( forall c. NameColor c => Store (v c o)
         , forall c. NameColor c => Generic (v c o))
         => Store (RecEnv v o)

instance ( forall c. NameColor c => Store (v c o)
         , forall c. NameColor c => Generic (v c o))
         => Store (MaterializedEnv v i o)

deriving instance (forall c n. Pretty (v c n)) => Pretty (RecEnvFrag v o o')


type EE = EitherE

type EitherE1 e0                = EE e0 VoidE
type EitherE2 e0 e1             = EE e0 (EE e1 VoidE)
type EitherE3 e0 e1 e2          = EE e0 (EE e1 (EE e2 VoidE))
type EitherE4 e0 e1 e2 e3       = EE e0 (EE e1 (EE e2 (EE e3 VoidE)))
type EitherE5 e0 e1 e2 e3 e4    = EE e0 (EE e1 (EE e2 (EE e3 (EE e4 VoidE))))
type EitherE6 e0 e1 e2 e3 e4 e5 = EE e0 (EE e1 (EE e2 (EE e3 (EE e4 (EE e5 VoidE)))))

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

pattern Case5 :: e5 n ->  EE e0 (EE e1 (EE e2 (EE e3 (EE e4 (EE e5 rest))))) n
pattern Case5 e = RightE (RightE (RightE (RightE (RightE (LeftE e)))))

type EB = EitherB

type EitherB1 e0             = EB e0 VoidB
type EitherB2 e0 e1          = EB e0 (EB e1 VoidB)
type EitherB3 e0 e1 e2       = EB e0 (EB e1 (EB e2 VoidB))
type EitherB4 e0 e1 e2 e3    = EB e0 (EB e1 (EB e2 (EB e3 VoidB)))
type EitherB5 e0 e1 e2 e3 e4 = EB e0 (EB e1 (EB e2 (EB e3 (EB e4 VoidB))))

pattern CaseB0 :: e0 n l -> EB e0 rest n l
pattern CaseB0 e = LeftB e

pattern CaseB1 :: e1 n l -> EB e0 (EB e1 rest) n l
pattern CaseB1 e = RightB (LeftB e)

pattern CaseB2 :: e2 n l -> EB e0 (EB e1 (EB e2 rest)) n l
pattern CaseB2 e = RightB (RightB (LeftB e))

pattern CaseB3 :: e3 n l -> EB e0 (EB e1 (EB e2 (EB e3 rest))) n l
pattern CaseB3 e = RightB (RightB (RightB (LeftB e)))

pattern CaseB4 :: e4 n l ->  EB e0 (EB e1 (EB e2 (EB e3 (EB e4 rest)))) n l
pattern CaseB4 e = RightB (RightB (RightB (RightB (LeftB e))))

-- ============================================================================
-- ==============================  UNSAFE CORE  ===============================
-- ============================================================================

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

data SomeNameColor (n::S) where
  SomeNameColor :: NameColorRep c -> SomeNameColor n

type NameSet n = M.Map RawName (SomeNameColor n)

newtype ScopeFrag (n::S) (l::S) = UnsafeMakeScopeFrag (NameSet UnsafeS)
newtype Scope (n::S) = Scope { fromScope :: ScopeFrag VoidS n }

instance Category ScopeFrag where
  id = UnsafeMakeScopeFrag mempty
  UnsafeMakeScopeFrag s2 . UnsafeMakeScopeFrag s1 = UnsafeMakeScopeFrag $ s1 <> s2

instance BindsNames (NameBinder c) where
  toScopeFrag (UnsafeMakeBinder (UnsafeMakeName rep v)) =
    UnsafeMakeScopeFrag (M.singleton v $ SomeNameColor rep)

absurdNameFunction :: Name v VoidS -> a
absurdNameFunction _ = error "Void names shouldn't exist"

scopeFragToEnvFrag :: ScopeFrag n l -> EnvFrag (ConstE UnitE) n l VoidS
scopeFragToEnvFrag (UnsafeMakeScopeFrag m) =
  UnsafeMakeEnv $ M.map (\(SomeNameColor c) -> EnvVal c (ConstE UnitE)) m

type NameText = T.Text
data RawName = RawName !NameText !Int deriving (Show, Eq, Ord, Generic)

data Name (c::C)  -- Name color
          (n::S)  -- Scope parameter
  where UnsafeMakeName :: NameColorRep c -> RawName -> Name c n

data NameBinder (c::C)  -- name color
                (n::S)  -- scope above the binder
                (l::S)  -- scope under the binder (`l` for "local")
  = UnsafeMakeBinder { nameBinderName :: Name c l }

data NameHint = Hint NameText
              | NoHint

instance IsString NameHint where
  fromString s = Hint $ fromString s

withFresh :: forall n c a. Distinct n
          => NameHint -> NameColorRep c -> Scope n
          -> (forall l. (Ext n l, Immut l, Distinct l) => NameBinder c n l -> a) -> a
withFresh hint rep (Scope (UnsafeMakeScopeFrag scope)) cont =
  withDistinctEvidence (fabricateDistinctEvidence :: DistinctEvidence UnsafeS) $
    withExtEvidence' (FabricateExtEvidence :: ExtEvidence n UnsafeS) $
      cont $ UnsafeMakeBinder freshName
  where
    freshName :: Name c UnsafeS
    freshName = UnsafeMakeName rep $ freshRawName hint scope

freshRawName :: NameHint -> M.Map RawName a -> RawName
freshRawName hint usedNames = RawName tag nextNum
  where
    nextNum = case M.lookupLT (RawName tag bigInt) usedNames of
                Just (RawName tag' i, _)
                  | tag' /= tag -> 0
                  | i < bigInt  -> i + 1
                  | otherwise   -> error "Ran out of numbers!"
                _ -> 0
    bigInt = (10::Int) ^ (9::Int)  -- TODO: consider a real sentinel value
    tag = case hint of Hint v -> v
                       NoHint -> "v"

projectName :: ScopeFrag n l -> Name s l -> Either (Name s n) (Name s (n:=>:l))
projectName (UnsafeMakeScopeFrag scope) (UnsafeMakeName rep rawName)
  | M.member rawName scope = Right $ UnsafeMakeName rep rawName
  | otherwise              = Left  $ UnsafeMakeName rep rawName

-- proves that the names in n are distinct
class Distinct (n::S)

fabricateDistinctEvidence :: forall n .DistinctEvidence n
fabricateDistinctEvidence =
  withDistinctEvidence (error "pure fabrication" :: DistinctEvidence n) Distinct

data DistinctEvidence (n::S) where
  Distinct :: Distinct n => DistinctEvidence n

instance Distinct VoidS

withDistinctEvidence :: forall n a. DistinctEvidence n -> (Distinct n => a) -> a
withDistinctEvidence _ cont = fromWrapWithDistinct
 ( TrulyUnsafe.unsafeCoerce ( WrapWithDistinct cont :: WrapWithDistinct n     a
                                                  ) :: WrapWithDistinct VoidS a)

newtype WrapWithDistinct n r =
  WrapWithDistinct { fromWrapWithDistinct :: Distinct n => r }


withSubscopeDistinct :: forall n l b a.
                        (Distinct l, ProvesExt b)
                     => b n l -> ((Ext n l, Distinct n) => a) -> a
withSubscopeDistinct b cont =
  withExtEvidence' (toExtEvidence b) $
    withDistinctEvidence (fabricateDistinctEvidence :: DistinctEvidence n) $
      cont

-- useful for printing etc.
getRawName :: Name c n -> RawName
getRawName (UnsafeMakeName _ rawName) = rawName

instance HasNameColor (Name c n) c where
  getNameColor (UnsafeMakeName rep _) = rep

-- === injections ===

-- Note [Injections]

-- `Ext n l` is proof that `l` extends `n` (not necessarily freshly:
-- `Distinct l` is still needed to further prove that). Unlike `ScopeFrag`
-- (which is also proof) it doesn't actually carry any data, so we can unsafely
-- create one from nothing when we need to.
class    (ExtEnd n => ExtEnd l) => Ext n l
instance (ExtEnd n => ExtEnd l) => Ext n l

-- ExtEnd is just a dummy class we use to encode the transitivity and
-- reflexivity of `Ext` in a way that GHC understands.
class ExtEnd (n::S)

getExtEvidence :: Ext n l => ExtEvidence n l
getExtEvidence = FabricateExtEvidence

absurdExtEvidence :: ExtEvidence VoidS n
absurdExtEvidence = FabricateExtEvidence

-- We give this one a ' because the more general one defined in Name is the
-- version we usually want to use.
withExtEvidence' :: forall n l a. ExtEvidence n l -> (Ext n l => a) -> a
withExtEvidence' _ cont = fromWrapWithExt
 ( TrulyUnsafe.unsafeCoerce ( WrapWithExt cont :: WrapWithExt n     l     a
                                             ) :: WrapWithExt VoidS VoidS a)

newtype WrapWithExt n l r =
  WrapWithExt { fromWrapWithExt :: Ext n l => r }

data ExtEvidence (n::S) (l::S) = FabricateExtEvidence

instance Category ExtEvidence where
  id = FabricateExtEvidence
  -- Unfortunately, we can't write the class version of this transitivity axiom
  -- because the intermediate type would be ambiguous.
  FabricateExtEvidence . FabricateExtEvidence = FabricateExtEvidence

inject :: (InjectableE e, Distinct l, Ext n l) => e n -> e l
inject x = unsafeCoerceE x

injectR :: InjectableE e => e (n:=>:l) -> e l
injectR = unsafeCoerceE

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

class (forall c. NameColor c => HoistableE (v c))
      => HoistableV (v::V)

data InjectionCoercion (n::S) (l::S) where
  InjectionCoercion :: (forall s. Name s n -> Name s l) -> InjectionCoercion n l

instance InjectableV Name
instance HoistableV  Name

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
  injectionProofE _ _ = fabricateDistinctEvidence

instance InjectableE (ExtEvidence n) where
  injectionProofE _ _ = FabricateExtEvidence

-- === projections ===

unsafeCoerceNameSet :: NameSet n -> NameSet l
unsafeCoerceNameSet = TrulyUnsafe.unsafeCoerce

-- XXX: we need another constraint analogous to `InjectableE`, which says that
--      we can do the actual hoisting by coercion. But we can't use
--      `InjectableE` itself because `Distinct` can't implement it. For now,
--      we just have to be careful about only giving `HoistableE` instances to
--      the right types.
-- XXX: there are privileged functions that depend on `HoistableE` instances
--      being correct.
class HoistableE (e::E) where
  freeVarsE :: e n-> NameSet n
  default freeVarsE :: (GenericE e, HoistableE (RepE e)) => e n -> NameSet n
  freeVarsE e = freeVarsE $ fromE e

class BindsNames b => HoistableB (b::B) where
  freeVarsB :: b n l -> NameSet n
  default freeVarsB :: (GenericB b, HoistableB (RepB b)) => b n l -> NameSet n
  freeVarsB b = freeVarsB $ fromB b

data HoistExcept a = HoistSuccess a | HoistFailure [RawName]

liftHoistExcept :: Fallible m => HoistExcept a -> m a
liftHoistExcept (HoistSuccess x) = return x
liftHoistExcept (HoistFailure vs) = throw EscapedNameErr (pprint vs)

ignoreHoistFailure :: HoistExcept a -> a
ignoreHoistFailure (HoistSuccess x) = x
ignoreHoistFailure (HoistFailure _) = error "hoist failure"

hoist :: (BindsNames b, HoistableE e) => b n l -> e l -> HoistExcept (e n)
hoist b e =
  case nameSetRawNames $ M.intersection frag (freeVarsE e) of
    []          -> HoistSuccess $ unsafeCoerceE e
    leakedNames -> HoistFailure leakedNames
  where UnsafeMakeScopeFrag frag = toScopeFrag b

hoistToTop :: HoistableE e => e n -> HoistExcept (e VoidS)
hoistToTop e =
  case nameSetRawNames $ freeVarsE e of
    []          -> HoistSuccess $ unsafeCoerceE e
    leakedNames -> HoistFailure leakedNames

injectFromTop :: InjectableE e => e VoidS -> e n
injectFromTop = unsafeCoerceE

freeVarsList :: HoistableE e => NameColorRep c -> e n -> [Name c n]
freeVarsList c e = nameSetToList c $ freeVarsE e

nameSetToList :: NameColorRep c -> NameSet n -> [Name c n]
nameSetToList c nameSet =
  catMaybes $ flip map (M.toList nameSet) \(rawName, (SomeNameColor c')) ->
    case eqNameColorRep c c' of
      Just ColorsEqual -> Just $ UnsafeMakeName c rawName
      Nothing -> Nothing

toNameSet :: ScopeFrag n l -> NameSet l
toNameSet (UnsafeMakeScopeFrag s) = fmap unsafeCoerceE s

nameSetRawNames :: NameSet n -> [RawName]
nameSetRawNames m = M.keys m

isFreeIn :: HoistableE e => Name c n -> e n -> Bool
isFreeIn v e = getRawName v `M.member` freeVarsE e

exchangeBs :: (Distinct l, BindsNames b1, InjectableB b1, HoistableB b2)
              => PairB b1 b2 n l
              -> HoistExcept (PairB b2 b1 n l)
exchangeBs (PairB b1 b2) =
  case nameSetRawNames $ M.intersection frag (freeVarsB b2) of
    []          -> HoistSuccess $ PairB (unsafeCoerceB b2) (unsafeCoerceB b1)
    leakedNames -> HoistFailure leakedNames
  where UnsafeMakeScopeFrag frag = toScopeFrag b1

hoistNameSet :: BindsNames b => b n l -> NameSet l -> NameSet n
hoistNameSet b nameSet = unsafeCoerceNameSet $ nameSet `M.difference` frag
  where UnsafeMakeScopeFrag frag = toScopeFrag b

abstractFreeVars :: [(Name c n, ann n)]
                 -> e n -> Abs (Nest (BinderP c ann)) e n
abstractFreeVars vs e = Abs bs e
  where bs = unsafeCoerceB $ unsafeListToNest bsFlat
        bsFlat = vs <&> \(v, ann) ->
          UnsafeMakeBinder (unsafeCoerceE v) :> unsafeCoerceE ann

abstractFreeVarsNoAnn :: [Name c n] -> e n -> Abs (Nest (NameBinder c)) e n
abstractFreeVarsNoAnn vs e =
  case abstractFreeVars (zip vs (repeat UnitE)) e of
    Abs bs e' -> Abs bs' e'
      where bs' = fmapNest (\(b:>UnitE) -> b) bs

-- captureClosure decls result = do
--   let vs = capturedVars decls result
--   case abstractFreeVars (zip vs (repeat UnitE)) result of
--     Abs bs e -> do
--       let bs' = fmapNest (\(b:>UnitE) -> b) bs
--       case hoist decls $ Abs bs' e of
--         HoistSuccess abHoisted -> (vs, abHoisted)
--         HoistFailure _ ->
--           error "shouldn't happen"  -- but it will if we have types that reference
--                                     -- local vars. We really need a telescope.

instance HoistableB (NameBinder c) where
  freeVarsB _ = mempty

instance HoistableE (Name c) where
  freeVarsE name =
    M.singleton (getRawName name) (SomeNameColor $ getNameColor name)

instance (HoistableB b1, HoistableB b2) => HoistableB (PairB b1 b2) where
  freeVarsB (PairB b1 b2) =
    freeVarsB b1 <> hoistNameSet b1 (freeVarsB b2)

instance HoistableE ann => HoistableB (BinderP c ann) where
  freeVarsB (b:>ann) = freeVarsB b <> freeVarsE ann

instance HoistableB UnitB where
  freeVarsB = mempty

instance HoistableE e => HoistableE (ListE e) where
  freeVarsE (ListE xs) = foldMap freeVarsE xs

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
  = UnsafeMakeEnv (M.Map RawName (EnvVal v o))
  deriving (Generic)
deriving instance (forall c. Show (v c o)) => Show (EnvFrag v i i' o)

-- === environments and scopes ===

lookupEnvFrag :: EnvFrag v i i' o -> Name s (i:=>:i') -> v s o
lookupEnvFrag (UnsafeMakeEnv m) (UnsafeMakeName rep rawName) =
  case M.lookup rawName m of
    Nothing -> error "Env lookup failed (this should never happen)"
    Just d -> fromEnvVal rep d

-- Just for debugging
lookupEnvFragRaw :: EnvFrag v i i' o -> RawName -> Maybe (EnvVal v o)
lookupEnvFragRaw (UnsafeMakeEnv m) rawName = M.lookup rawName m

instance InFrag (EnvFrag v) where
  emptyInFrag = UnsafeMakeEnv mempty
  catInFrags (UnsafeMakeEnv m1) (UnsafeMakeEnv m2) =
    UnsafeMakeEnv (m2 <> m1) -- flipped because Data.Map uses a left-biased `<>`

singletonEnv :: NameBinder c i i' -> v c o -> EnvFrag v i i' o
singletonEnv (UnsafeMakeBinder (UnsafeMakeName rep name)) x =
  UnsafeMakeEnv (M.singleton name $ EnvVal rep x)

fmapEnvFrag :: InjectableV v
            => (forall c. NameColor c => Name c (i:=>:i') -> v c o -> v' c o')
            -> EnvFrag v i i' o -> EnvFrag v' i i' o'
fmapEnvFrag f (UnsafeMakeEnv m) = UnsafeMakeEnv m'
  where m' = flip M.mapWithKey m \k (EnvVal rep val) ->
               withNameColorRep rep $
                 EnvVal rep $ f (UnsafeMakeName rep k) val


envFragAsScope :: EnvFrag v i i' o -> ScopeFrag i i'
envFragAsScope (UnsafeMakeEnv m) = UnsafeMakeScopeFrag $
  fmap (\(EnvVal rep _) -> SomeNameColor rep) m

-- === iterating through env pairs ===

data EnvPair (v::V) (o::S) (i::S) (i'::S) where
  EnvPair :: NameColor c => NameBinder c i i' -> v c o -> EnvPair v o i i'

toEnvPairs :: forall v i i' o . EnvFrag v i i' o -> Nest (EnvPair v o) i i'
toEnvPairs (UnsafeMakeEnv m) =
  go $ M.elems $ M.mapWithKey mkPair m
  where
    mkPair :: RawName -> EnvVal v o -> EnvPair v o UnsafeS UnsafeS
    mkPair rawName (EnvVal rep v) =
      withNameColorRep rep $
        EnvPair (UnsafeMakeBinder $ UnsafeMakeName rep rawName) v

    go :: [EnvPair v o UnsafeS UnsafeS] -> Nest (EnvPair v o) i i'
    go [] = unsafeCoerceB Empty
    go (EnvPair b val : rest) = Nest (EnvPair (unsafeCoerceB b) val) $ go rest

data WithRenamer e i o where
  WithRenamer :: EnvFrag Name i i' o -> e i' -> WithRenamer e i o

collectFreeVars :: HoistableE e => e n -> WithRenamer e VoidS n
collectFreeVars e = WithRenamer idRenamerFrag e
  where idRenamerFrag = UnsafeMakeEnv $
          flip M.mapWithKey (freeVarsE e) \v (SomeNameColor c) ->
            EnvVal c $ UnsafeMakeName c v

-- Lets you process entries one by one, just as you'd traverse a list by pattern-matching
-- on `:` and `[]`.
unConsEnv :: EnvFrag v i i' o -> ConsEnv v i i' o
unConsEnv (UnsafeMakeEnv m) =
  case M.minViewWithKey m of
    Nothing -> unsafeCoerceB EmptyEnv
    Just ((v, EnvVal c x), rest)  ->
      withNameColorRep c $
        ConsEnv (UnsafeMakeBinder (UnsafeMakeName c v)) x (UnsafeMakeEnv rest)

data ConsEnv v i i' o where
  ConsEnv :: NameColor c
          => NameBinder c i1 i2 -> v c o -> EnvFrag v i2 i3 o
          -> ConsEnv v i1 i3 o
  EmptyEnv :: ConsEnv v i i o

instance Category (Nest b) where
  id = Empty
  nest' . nest = case nest of
    Empty -> nest'
    Nest b rest -> Nest b $ rest >>> nest'

instance ProvesExt (EnvPair v o) where
  toExtEvidence (EnvPair b _) = toExtEvidence b

instance BindsNames (EnvPair v o) where
  toScopeFrag (EnvPair b _) = toScopeFrag b

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

instance HoistableV v => HoistableE (EnvFrag v i i') where
  freeVarsE frag = foldMapEnvFrag freeVarsE frag

instance SubstV substVal v => SubstE substVal (EnvFrag v i i') where
   substE env frag = fmapEnvFrag (\_ val -> substE env val) frag

-- === unsafe coercions ===

-- Sometimes we need to break the glass. But at least these are slightly safer
-- than raw `unsafeCoerce` because at the checks the kind

unsafeCoerceE :: forall (e::E) i o . e i -> e o
unsafeCoerceE = TrulyUnsafe.unsafeCoerce

unsafeCoerceB :: forall (b::B) n l n' l' . b n l -> b n' l'
unsafeCoerceB = TrulyUnsafe.unsafeCoerce

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

instance HoistableB b => HoistableB (Nest b) where
  freeVarsB Empty = mempty
  freeVarsB (Nest b rest) = freeVarsB (PairB b rest)

instance (forall c n. Pretty (v c n)) => Pretty (EnvFrag v i i' o) where
  pretty (UnsafeMakeEnv m) =
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

  to = unsafeCoerceB . unsafeListToNest . to

unsafeListToNest :: [b UnsafeS UnsafeS] -> Nest b UnsafeS UnsafeS
unsafeListToNest l = case l of
  [] -> unsafeCoerceB Empty
  b:rest -> Nest (unsafeCoerceB b) $ unsafeListToNest rest

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
  injectionProofE = todoInjectableProof

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

instance Functor HoistExcept where
  fmap f x = f <$> x

instance Applicative HoistExcept where
  pure x = HoistSuccess x
  liftA2 = liftM2

instance Monad HoistExcept where
  return = pure
  HoistFailure vs >>= _ = HoistFailure vs
  HoistSuccess x >>= f = f x

-- TODO: this needs to be injective but it's currently not
-- (needs to figure out acceptable tag strings)
instance Pretty RawName where
  pretty (RawName tag n) = pretty tag <> suffix
            where suffix = case n of 0 -> ""
                                     _ -> pretty n

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
