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

module SaferNames.Name (
  Name (..), RawName, S (..), C (..), (<.>), EnvFrag (..), NameBinder (..),
  EnvReader (..), FromName (..), Distinct, DistinctWitness (..),
  Ext, ExtEvidence, ProvesExt (..), withExtEvidence, getExtEvidence, getScopeProxy,
  Env (..), idEnv, newEnv, envFromFrag,
  DistinctAbs (..), WithScope (..),
  extendRenamer, ScopeReader (..), ScopeExtender (..), ScopeGetter (..),
  Scope (..), ScopeFrag (..), SubstE (..), SubstB (..),
  SubstV, MonadicVal (..), lookupSustTraversalEnv,
  Inplace (..), InplaceT, emitInplace, doInplaceExcept,
  scopedInplaceExcept, runInplaceT, withInplaceOutEnv,
  E, B, V, HasNamesE, HasNamesB, BindsNames (..), HasScope (..), RecEnvFrag (..), RecEnv (..),
  MaterializedEnv (..), lookupTerminalEnvFrag, lookupMaterializedEnv,
  BindsOneName (..), BindsAtMostOneName (..), BindsNameList (..), NameColorRep (..),
  Abs (..), Nest (..), PairB (..), UnitB (..),
  IsVoidS (..), UnitE (..), VoidE, PairE (..), fromPairE, ListE (..), ComposeE (..),
  EitherE (..), LiftE (..), EqE, EqB, OrdE, OrdB, VoidB,
  EitherB (..), BinderP (..),
  LiftB, pattern LiftB,
  MaybeE, pattern JustE, pattern NothingE, MaybeB, pattern JustB, pattern NothingB,
  toConstAbs, PrettyE, PrettyB, ShowE, ShowB,
  runScopeReaderT, runEnvReaderT, ScopeReaderT (..), EnvReaderT (..),
  lookupEnvM, dropSubst, extendEnv, freeNames, emptyNameTraversalEnv, fmapNames,
  MonadKind, MonadKind1, MonadKind2,
  Monad1, Monad2, Fallible1, Fallible2, CtxReader1, CtxReader2, MonadFail1, MonadFail2,
  ScopeReader2, ScopeExtender2,
  applyAbs, applyNaryAbs, ZipEnvReader (..), alphaEqTraversable,
  checkAlphaEq, alphaEq, AlphaEq, AlphaEqE (..), AlphaEqB (..), AlphaEqV, ConstE (..),
  InjectableE (..), InjectableB (..), InjectableV, InjectionCoercion,
  withFreshM, withFreshLike, inject, injectM, injectMVia, (!), (<>>),
  envFragAsScope,
  EmptyAbs, pattern EmptyAbs, SubstVal (..),
  NameGen (..), fmapG, NameGenT (..), traverseEnvFrag, fmapNest, forEachNestItem,
  substM, ScopedEnvReader, runScopedEnvReader,
  HasNameHint (..), HasNameColor (..), NameHint (..), NameColor (..),
  GenericE (..), GenericB (..), ColorsEqual (..),
  EitherE1, EitherE2, EitherE3, EitherE4, EitherE5,
    pattern Case0, pattern Case1, pattern Case2, pattern Case3, pattern Case4,
  EitherB1, EitherB2, EitherB3, EitherB4, EitherB5,
    pattern CaseB0, pattern CaseB1, pattern CaseB2, pattern CaseB3, pattern CaseB4,
  splitNestAt, nestLength, nestToList, binderAnn,
  OutReaderT (..), OutReader (..), runOutReaderT, getDistinct,
  ExtWitness (..), idExt, injectExt,
  InFrag (..), InMap (..), OutFrag (..), OutMap (..), WithOutMap (..),
  toEnvPairs, fromEnvPairs, EnvPair (..), refreshRecEnvFrag, refreshAbs,
  hoist, fromConstAbs, exchangeBs, HoistableE (..), HoistableB (..),
  WrapE (..), EnvVal (..), DistinctEvidence (..), withSubscopeDistinct, tryAsColor, withFresh,
  withDistinctEvidence, getDistinctEvidence,
  unsafeCoerceE, unsafeCoerceB, getRawName, EqNameColor (..),
  eqNameColorRep, withNameColorRep, injectR, fmapEnvFrag, catRecEnvFrags,
  DeferredInjection (..), LocallyDistinctAbs, finishInjection, ignoreLocalDistinctness,
  ) where

import Prelude hiding (id, (.))
import Control.Category
import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Except hiding (Except)
import Control.Monad.Reader
import Control.Monad.Writer.Strict
import qualified Data.Set        as S
import qualified Data.Map.Strict as M
import Data.Foldable (fold)
import Data.Kind (Type)
import Data.String
import Data.Text.Prettyprint.Doc  hiding (nest)
import GHC.Exts (Constraint)
import GHC.Generics (Generic (..), Rep)
import Data.Store (Store)

import qualified Unsafe.Coerce as TrulyUnsafe

import qualified Env as D

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

class OutFrag (scopeFrag :: S -> S -> *) where
  emptyOutFrag :: scopeFrag n n
  -- The scope is here because solver subst concatenation needs it
  catOutFrags  :: Distinct n3 => Scope n3 -> scopeFrag n1 n2 -> scopeFrag n2 n3 -> scopeFrag n1 n3

class (OutFrag scopeFrag, HasScope scope)
      => OutMap (scope :: S -> *) (scopeFrag :: S -> S -> *) | scope -> scopeFrag where
  emptyOutMap :: scope VoidS
  extendOutMap :: Distinct l => scope n -> scopeFrag n l -> scope l

instance InMap (Env v) (EnvFrag v) where
  emptyInMap = newEnv absurdNameFunction
  extendInMap (Env f frag) frag' = Env f $ frag <.> frag'

instance OutFrag ScopeFrag where
  emptyOutFrag = id
  catOutFrags _ = (>>>)

instance HasScope Scope where
  toScope = id

instance OutMap Scope ScopeFrag where
  emptyOutMap = Scope id
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

instance InjectableV v => OutMap (RecEnv v) (RecEnvFrag v) where
  emptyOutMap = RecEnv emptyInFrag
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

instance OutFrag (Nest b) where
  emptyOutFrag = id
  catOutFrags _ = (>>>)

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

data BinderP (b::B) (ann::E) (n::S) (l::S) =
  (:>) (b n l) (ann n)
  deriving (Show, Generic)

type EmptyAbs b = Abs b UnitE :: E
pattern EmptyAbs :: b n l -> EmptyAbs b n
pattern EmptyAbs bs = Abs bs UnitE

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

class HasScope (bindings :: S -> *) where
  toScope :: bindings n -> Scope n

withExtEvidence :: ProvesExt b => b n l -> (Ext n l => a) -> a
withExtEvidence b cont = withExtEvidence' (toExtEvidence b) cont

-- like inject, but uses the ScopeReader monad for its `Distinct` proof
injectM :: (ScopeReader m, Ext n l, InjectableE e) => e n -> m l (e l)
injectM e = do
  Distinct <- getDistinct
  return $ inject e

-- since the injection is deferred, we can have an InjectableE instance even
-- when `e` itself is not injectable. It's useful when we need to pass around
-- things like `DistinctAbs`.
data DeferredInjection (e::E) (n::S) where
  DeferredInjection :: ExtWitness n' n -> e n' -> DeferredInjection e n

type LocallyDistinctAbs (b::B) (e::E) = DeferredInjection (DistinctAbs b e)

ignoreLocalDistinctness :: (Distinct n, InjectableB b, InjectableE e)
                        => LocallyDistinctAbs b e n -> Abs b e n
ignoreLocalDistinctness (DeferredInjection ExtW (DistinctAbs b e)) =
  finishInjection $ DeferredInjection ExtW (Abs b e)

finishInjection :: (Distinct n, InjectableE e) => DeferredInjection e n -> e n
finishInjection (DeferredInjection ExtW e) = inject e

instance InjectableE (DeferredInjection e) where
  injectionProofE fresh (DeferredInjection extW e) =
    DeferredInjection (injectionProofE fresh extW) e

data ExtWitness (n::S) (l::S) where
  ExtW :: Ext n l => ExtWitness n l

instance ProvesExt ExtWitness where
  toExtEvidence ExtW = getExtEvidence

instance InjectableE (ExtWitness n) where
  injectionProofE :: forall n' n l. InjectionCoercion n l -> ExtWitness n' n -> ExtWitness n' l
  injectionProofE fresh ExtW =
    withExtEvidence (injectionProofE fresh (getExtEvidence :: ExtEvidence n' n)) ExtW

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
traverseNames scope f e = substE (newEnv f', scope) e
  where f' :: forall c. Name c i -> MonadicVal m v c o
        f' x = MonadicVal $ f x

fmapNames :: forall v e i o.
             SubstE v e
          => Distinct o => Scope o -> (forall c. Name c i -> v c o) -> e i -> e o
fmapNames scope f e = runIdentity $ traverseNames scope (return . f) e

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
       (Env (MonadicVal m v) i o, Scope o)

lookupSustTraversalEnv :: SubstTraversalEnv m v i o -> Name c i -> m (v c o)
lookupSustTraversalEnv (env, _) v = fromMonadicVal $ env ! v

emptyNameTraversalEnv :: Monad m => Scope n -> SubstTraversalEnv m Name n n
emptyNameTraversalEnv scope = (newEnv (MonadicVal . return), scope)

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
    let rep = getNameColor $ nameBinderName b
    withFresh (getNameHint b) rep scope \b' -> do
      let env' = inject env <>> b @> (MonadicVal $ return $ fromName $ binderName b')
      let scope' = extendOutMap scope $ toScopeFrag b'
      cont (env', scope') b'

substM :: (EnvReader v m, ScopeReader2 m, SubstE v e, FromName v)
       => e i -> m i o (e o)
substM e = do
  env <- getEnv
  WithScope scope env' <- addScope env
  injectM $ fmapNames scope (env'!) e

-- === projections ===

fromConstAbs :: (BindsNames b, HoistableE e) => Abs b e n -> Maybe (e n)
fromConstAbs (Abs b e) = hoist b e

hoist :: (BindsNames b, HoistableE e) => b n l -> e l -> Maybe (e n)
hoist b e = hoistWithFreeVars (toScopeFrag b) (withFreeVarsE e)

exchangeBs :: (Distinct l, BindsNames b1, InjectableB b1, HoistableB b2)
              => PairB b1 b2 n l
              -> Maybe (PairB b2 b1 n l)
exchangeBs (PairB b1 b2) =
  exchangeWithFreeVars (toScopeFrag b1) b1 (withFreeVarsB b2)


-- XXX: we need another constraint analogous to `InjectableE`, which says that
--      we can do the actual hoisting by coercion. But we can't use
--      `InjectableE` itself because `Distinct` can't implement it. For now,
--      we just have to be careful about only giving `HoistableE` instances to
--      the right types.
class HoistableE (e::E) where
  withFreeVarsE :: e n-> WithFreeVarsE e n

  default withFreeVarsE :: (GenericE e, HoistableE (RepE e))
                       => e n -> WithFreeVarsE e n
  withFreeVarsE e = UnsafeMakeWithFreeVarsE (toE repE) fvs
    where UnsafeMakeWithFreeVarsE repE fvs = withFreeVarsE $ fromE e

class HoistableB (b::B) where
  withFreeVarsB :: b n l -> WithFreeVarsB b n l

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

fromPairE :: PairE e1 e2 n -> (e1 n, e2 n)
fromPairE (PairE x y) = (x, y)

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

instance BindsAtMostOneName b c => BindsAtMostOneName (BinderP b ann) c where
  (b:>_) @> x = b @> x

instance BindsOneName b c => BindsOneName (BinderP b ann) c where
  binderName (b:>_) = binderName b

infixr 7 @@>
class BindsNameList (b::B) (c::C) | b -> c where
  (@@>) :: b i i' -> [v c o] -> EnvFrag v i i' o

instance BindsAtMostOneName b c => BindsNameList (Nest b) c where
  (@@>) Empty [] = emptyInFrag
  (@@>) (Nest b rest) (x:xs) = b@>x <.> rest@@>xs
  (@@>) _ _ = error "length mismatch"

applySubst :: (ScopeReader m, SubstE v e, InjectableV v, FromName v)
           => EnvFrag v o i o -> e i -> m o (e o)
applySubst substFrag x = do
  let fullSubst = idEnv <>> substFrag
  WithScope scope fullSubst' <- addScope fullSubst
  injectM $ fmapNames scope (fullSubst' !) x

applyAbs :: (InjectableV v, FromName v, ScopeReader m, BindsOneName b c, SubstE v e)
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

freeNames :: HasNamesE e => NameColorRep c -> e n -> S.Set (Name c n)
freeNames = undefined

-- === versions of monad constraints with scope params ===

type MonadKind  =           * -> *
type MonadKind1 =      S -> * -> *
type MonadKind2 = S -> S -> * -> *

type Monad1 (m :: MonadKind1) = forall (n::S)        . Monad (m n  )
type Monad2 (m :: MonadKind2) = forall (n::S) (l::S) . Monad (m n l)

type Fallible1 (m :: MonadKind1) = forall (n::S)        . Fallible (m n  )
type Fallible2 (m :: MonadKind2) = forall (n::S) (l::S) . Fallible (m n l)

type CtxReader1 (m :: MonadKind1) = forall (n::S)        . CtxReader (m n  )
type CtxReader2 (m :: MonadKind2) = forall (n::S) (l::S) . CtxReader (m n l)

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
    extendScope (toScopeFrag b') $
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

checkAlphaEqPure :: (AlphaEqE e, Distinct n)
                 => Scope n -> e n -> e n -> Except ()
checkAlphaEqPure scope e1 e2 =
  runScopeReaderT scope $
    flip runReaderT (emptyInMap, emptyInMap) $ runZipEnvReaderT $
      withEmptyZipEnv $ alphaEqE e1 e2

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
    (\(_, scope) -> (getDistinctEvidence, extendOutMap scope frag)) $
        withExtEvidence (toExtEvidence frag) $
          runScopeReaderT' m

-- === EnvReaderT transformer ===

newtype EnvReaderT (v::V) (m::MonadKind1) (i::S) (o::S) (a:: *) =
  EnvReaderT { runEnvReaderT' :: ReaderT (Env v i o) (m o) a }
  deriving (Functor, Applicative, Monad, MonadFail, Fallible, CtxReader)

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

type ZipEnv i1 i2 o = (Env Name i1 o, Env Name i2 o)

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
    ZipEnvReaderT $ withReaderT (const (newEnv id, newEnv id)) cont

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

data WithOutMap (bindings::E) (e::E) (n::S) where
  WithOutMap :: (Distinct l, Ext l n) => Scope l -> bindings l -> e l -> WithOutMap bindings e n

data InplaceT (bindings::E) (decls::B) (m::MonadKind) (n::S) (a :: *) = UnsafeMakeInplaceT
  { unsafeRunInplaceT :: Distinct n => bindings n -> m (a, decls UnsafeS UnsafeS) }

class (ScopeReader m, OutMap bindings decls, BindsNames decls, InjectableB decls)
      => Inplace (m::MonadKind1) (bindings::E) (decls::B) | m -> bindings, m -> decls where
  doInplace
    :: (InjectableE e, InjectableE e')
    => e n
    -> (forall l. Distinct l => bindings l -> e l -> DistinctAbs decls e' l)
    -> m n (e' n)
  scopedInplace
    :: InjectableE e
    => (forall l. (Distinct l, Ext n l) => m l (e l))
    -> m n (LocallyDistinctAbs decls e n)

instance (Monad m, OutMap bindings decls, BindsNames decls, InjectableB decls)
         => Inplace (InplaceT bindings decls m) bindings decls where
  doInplace e cont = UnsafeMakeInplaceT \bindings -> do
    DistinctAbs decls e' <- return $ cont bindings e
    return (unsafeCoerceE e', unsafeCoerceB decls)

  scopedInplace cont = do
    UnitE :: UnitE n <- getScopeProxy
    UnsafeMakeInplaceT \bindings -> do
      (result, decls) <- unsafeRunInplaceT cont bindings
      withExtEvidence (FabricateExtEvidence :: ExtEvidence UnsafeS n) do
        withDistinctEvidence (FabricateDistinctEvidence :: DistinctEvidence UnsafeS) do
          let ab = DistinctAbs decls (unsafeCoerceE result)
          return (DeferredInjection ExtW ab, emptyOutFrag)

runInplaceT :: (Distinct n, OutMap bindings decls, Monad m)
            => bindings n
            -> (forall l. (Distinct l, Ext n l) => InplaceT bindings decls m l (e l))
            -> m (Abs decls e n)
runInplaceT bindings (UnsafeMakeInplaceT f) = do
  (result, decls) <- f bindings
  return $ Abs (unsafeCoerceB decls) (unsafeCoerceE result)


liftInplace :: (Monad m, OutFrag decls) => m a -> InplaceT bindings decls m n a
liftInplace m = UnsafeMakeInplaceT \_ -> (,emptyOutFrag) <$> m

emitInplace
  :: (Inplace m bindings decls, NameColor c, InjectableE e)
  => NameHint -> e o
  -> (forall n l. (Ext n l, Distinct l) => NameBinder c n l -> e n -> decls n l)
  -> m o (Name c o)
emitInplace hint e buildDecls = do
  doInplace e \bindings e' ->
    withFresh hint nameColorRep (toScope bindings) \b ->
      DistinctAbs (buildDecls b e') (binderName b)

doInplaceExcept
  :: (Inplace m bindings decls, Fallible1 m, InjectableE e, InjectableE e')
  => e n
  -> (forall l. Distinct l => bindings l -> e l -> Except (DistinctAbs decls e' l))
  -> m n (e' n)
doInplaceExcept eIn cont = do
  result <- doInplace eIn \bindings eIn' ->
    case cont bindings eIn' of
      Failure errs -> DistinctAbs emptyOutFrag $ LeftE $ LiftE errs
      Success (DistinctAbs decls result) -> DistinctAbs decls $ RightE result
  case result of
    LeftE (LiftE errs) -> throwErrs errs
    RightE ans -> return ans

scopedInplaceExcept
  :: (Inplace m bindings decls, Fallible1 m, InjectableE e, InjectableE e')
  => (forall l. Distinct l => bindings l -> DistinctAbs decls e l -> Except (e' l))
  -> (forall l. (Distinct l, Ext n l) => m l (e l))
  -> m n (e' n)
scopedInplaceExcept _ _ = undefined

withInplaceOutEnv
  :: (Inplace m bindings decls, InjectableE e, InjectableE e')
  => e n
  -> (forall l. Distinct l => bindings l -> e l -> e' l)
  -> m n (e' n)
withInplaceOutEnv eIn cont = doInplace eIn \bindings eIn' ->
  let eOut = cont bindings eIn'
  in DistinctAbs emptyOutFrag eOut

instance (OutMap bindings decls, BindsNames decls, InjectableB decls, Monad m)
         => Functor (InplaceT bindings decls m n) where
  fmap = liftM

instance (OutMap bindings decls, BindsNames decls, InjectableB decls, Monad m)
         => Applicative (InplaceT bindings decls m n) where
  pure = return
  liftA2 = liftM2

instance (OutMap bindings decls, BindsNames decls, InjectableB decls, Monad m)
         => Monad (InplaceT bindings decls m n) where
  return x = UnsafeMakeInplaceT \_ ->
    withDistinctEvidence (FabricateDistinctEvidence :: DistinctEvidence UnsafeS) $
      return (x, emptyOutFrag)
  m >>= f = UnsafeMakeInplaceT \outMap -> do
    (x, b1) <- unsafeRunInplaceT m outMap
    let outMap' = outMap `extendOutMap` unsafeCoerceB b1
    (y, b2) <- unsafeRunInplaceT (f x) outMap'
    withDistinctEvidence (FabricateDistinctEvidence :: DistinctEvidence UnsafeS) $
      return (y, catOutFrags (unsafeCoerceE (toScope outMap')) b1 b2)

instance (OutMap bindings decls, BindsNames decls, InjectableB decls, Monad m)
         => ScopeReader (InplaceT bindings decls m) where
  getDistinctEvidenceM = UnsafeMakeInplaceT \_ ->
    return (getDistinctEvidence, emptyOutFrag)
  addScope e = doInplace e \bindings e' ->
    DistinctAbs emptyOutFrag (WithScope (toScope bindings) e')

instance (OutMap bindings decls, BindsNames decls, InjectableB decls, Monad m, MonadFail m)
         => MonadFail (InplaceT bindings decls m n) where
  fail s = liftInplace $ fail s

instance (OutMap bindings decls, BindsNames decls, InjectableB decls, Monad m, Fallible m)
         => Fallible (InplaceT bindings decls m n) where
  throwErrs errs = UnsafeMakeInplaceT \_ -> throwErrs errs
  addErrCtx ctx cont = UnsafeMakeInplaceT \bindings ->
    addErrCtx ctx $ unsafeRunInplaceT cont bindings

instance (OutMap bindings decls, BindsNames decls, InjectableB decls, Monad m, CtxReader m)
         => CtxReader (InplaceT bindings decls m n) where
  getErrCtx = undefined

instance (Inplace m bindings decls, InjectableV v)
         => Inplace (EnvReaderT v m i) bindings decls where
  doInplace e cont = EnvReaderT $ lift $ doInplace e cont
  scopedInplace cont = EnvReaderT $ ReaderT \env ->
    scopedInplace do
      env' <- injectM env
      runReaderT (runEnvReaderT' cont) env'

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

instance HasNameColor (NameBinder c n l) c where
  getNameColor b = getNameColor $ nameBinderName b

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
  withFreeVarsE = undefined

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

instance (BindsNames b1, BindsNames b2) => ProvesExt  (EitherB b1 b2) where
instance (BindsNames b1, BindsNames b2) => BindsNames (EitherB b1 b2) where
  toScopeFrag (LeftB  b) = toScopeFrag b
  toScopeFrag (RightB b) = toScopeFrag b

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

instance HoistableE UnitE where
  withFreeVarsE = undefined

instance FromName v => SubstE v UnitE where
  substE _ UnitE = return UnitE

instance (Functor f, InjectableE e) => InjectableE (ComposeE f e) where
  injectionProofE fresh (ComposeE xs) = ComposeE $ fmap (injectionProofE fresh) xs

instance (Functor f, HoistableE e) => HoistableE (ComposeE f e) where
  withFreeVarsE = undefined

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

instance InjectableB VoidB where
  injectionProofB _ _ _ = error "impossible"

instance ProvesExt VoidB where
instance BindsNames VoidB where
  toScopeFrag _ = error "impossible"

instance HoistableB VoidB where
  withFreeVarsB = undefined

instance AlphaEqB VoidB where
  withAlphaEqB _ _ _ = error "impossible"

instance FromName v => SubstB v VoidB where
  substB _ _ _ = error "impossible"

instance InjectableE const => InjectableV (ConstE const)
instance InjectableE const => InjectableE (ConstE const ignored) where
  injectionProofE fresh (ConstE e) = ConstE $ injectionProofE fresh e

instance InjectableE VoidE where
  injectionProofE _ _ = error "impossible"

instance HoistableE VoidE where
  withFreeVarsE = undefined

instance AlphaEqE VoidE where
  alphaEqE _ _ = error "impossible"

instance FromName v => SubstE v VoidE where
  substE _ _ = error "impossible"

instance (InjectableE e1, InjectableE e2) => InjectableE (PairE e1 e2) where
  injectionProofE fresh (PairE e1 e2) =
    PairE (injectionProofE fresh e1) (injectionProofE fresh e2)

instance (HoistableE e1, HoistableE e2) => HoistableE (PairE e1 e2) where
  withFreeVarsE (PairE e1 e2) = undefined

instance (SubstE v e1, SubstE v e2) => SubstE v (PairE e1 e2) where
  substE env (PairE x y) =
    PairE <$> substE env x <*> substE env y

instance (InjectableE e1, InjectableE e2) => InjectableE (EitherE e1 e2) where
  injectionProofE fresh (LeftE  e) = LeftE  (injectionProofE fresh e)
  injectionProofE fresh (RightE e) = RightE (injectionProofE fresh e)

instance (HoistableE e1, HoistableE e2) => HoistableE (EitherE e1 e2) where
  withFreeVarsE (LeftE  e) = undefined
  withFreeVarsE (RightE e) = undefined

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

instance HoistableE (LiftE a) where
  withFreeVarsE = undefined

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
  toScopeFrag env = envFragAsScope $ fromRecEnvFrag env

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

refreshRecEnvFrag :: (Distinct o,  InjectableV v, InjectableV substVal, SubstV substVal v)
                  => Scope o
                  -> Env substVal i o
                  -> RecEnvFrag v i i'
                  -> DistinctAbs (RecEnvFrag v) (Env substVal i') o
refreshRecEnvFrag scope env (RecEnvFrag frag) =
  renameEnvPairBindersPure scope env (toEnvPairs frag) \scope' env' pairs ->
    let frag' = fmapEnvFrag (\_ val -> fmapNames scope' (env'!) val) (fromEnvPairs pairs)
    in DistinctAbs (RecEnvFrag frag') env'

refreshAbs :: (Distinct n, SubstB Name b, SubstE Name e)
           => Scope n -> Abs b e n -> DistinctAbs b e n
refreshAbs scope (Abs b e) =
  runIdentity $ substB env b \env' b' -> do
    e' <- substE env' e
    return $ DistinctAbs b' e'
  where env = emptyNameTraversalEnv scope

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

newtype ScopeFrag (n::S) (l::S) = UnsafeMakeScope (S.Set RawName)
newtype Scope (n::S) = Scope { fromScope :: ScopeFrag VoidS n }

instance Category ScopeFrag where
  id = UnsafeMakeScope mempty
  UnsafeMakeScope s2 . UnsafeMakeScope s1 = UnsafeMakeScope $ s1 <> s2

instance BindsNames (NameBinder c) where
  toScopeFrag (UnsafeMakeBinder (UnsafeMakeName _ v)) =
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
withFresh hint rep (Scope (UnsafeMakeScope scope)) cont =
  withDistinctEvidence (FabricateDistinctEvidence :: DistinctEvidence UnsafeS) $
    withExtEvidence' (FabricateExtEvidence :: ExtEvidence n UnsafeS) $
      cont $ UnsafeMakeBinder freshName
  where
    freshName :: Name c UnsafeS
    freshName = UnsafeMakeName rep $ freshRawName (D.nameTag $ hintToRawName hint) scope

hintToRawName :: NameHint -> RawName
hintToRawName hint = case hint of
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
 ( TrulyUnsafe.unsafeCoerce ( WrapWithDistinct cont :: WrapWithDistinct n     a
                                                  ) :: WrapWithDistinct VoidS a)

newtype WrapWithDistinct n r =
  WrapWithDistinct { fromWrapWithDistinct :: Distinct n => r }


withSubscopeDistinct :: forall n l b a.
                        (Distinct l, ProvesExt b)
                     => b n l -> ((Ext n l, Distinct n) => a) -> a
withSubscopeDistinct b cont =
  withExtEvidence' (toExtEvidence b) $
    withDistinctEvidence (FabricateDistinctEvidence :: DistinctEvidence n) $
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
class Ext (n::S) (l::S)

instance Ext (n::S) (n::S)

getExtEvidence :: Ext n l => ExtEvidence n l
getExtEvidence = FabricateExtEvidence

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

injectRB :: InjectableB b => b (h:=>:n) (h:=>:l) -> b n l
injectRB = unsafeCoerceB

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

-- === projections -- the unsafe bits ===

hoistWithFreeVars :: HoistableE e => ScopeFrag n l -> WithFreeVarsE e l -> Maybe (e n)
hoistWithFreeVars
    (UnsafeMakeScope frag)
    (UnsafeMakeWithFreeVarsE e freeVars) =
  if null $ S.intersection frag freeVars
    then Just $ unsafeCoerceE e
    else Nothing

-- What about preserving the free vars in the result?
exchangeWithFreeVars :: (Distinct n3, InjectableB b1, HoistableB b2)
                     => ScopeFrag n1 n2
                     -> b1 n1 n2
                     -> WithFreeVarsB b2 n2 n3
                     -> Maybe (PairB b2 b1 n1 n3)
exchangeWithFreeVars
    (UnsafeMakeScope frag)
    b1
    (UnsafeMakeWithFreeVarsB b2 freeVars _) =
  if null $ S.intersection frag freeVars
    then Just $ PairB (unsafeCoerceB b2) (unsafeCoerceB b1)
    else Nothing

data WithFreeVarsE (e::E) (n::S) where
  UnsafeMakeWithFreeVarsE :: e n -> S.Set RawName -> WithFreeVarsE e n

data WithFreeVarsB (b::B) (n::S) (l::S) where
  UnsafeMakeWithFreeVarsB :: b n l
                          -> S.Set RawName
                          -> ScopeFrag n l
                          -> WithFreeVarsB b n l

-- TODO: make a FunctorB class for this pattern?
fmapWithFresVarsB :: (forall n' l'. b n' l' -> b' n' l')
                  -> WithFreeVarsB b n l -> WithFreeVarsB b' n l
fmapWithFresVarsB f (UnsafeMakeWithFreeVarsB b fvs frag) =
  UnsafeMakeWithFreeVarsB (f b) fvs frag

instance HoistableB (NameBinder c) where
  withFreeVarsB = undefined

instance HoistableE (Name c) where
  withFreeVarsE = undefined

instance (HoistableB b1, HoistableB b2) => HoistableB (PairB b1 b2) where
  withFreeVarsB (PairB b1 b2) =
    UnsafeMakeWithFreeVarsB (PairB b1' b2') (S.union s1 s2) (f1 >>> f2)
    where
      UnsafeMakeWithFreeVarsB b1' s1 f1 = withFreeVarsB b1
      UnsafeMakeWithFreeVarsB b2' s2 f2 = withFreeVarsB b2

instance (HoistableB b, HoistableE ann) => HoistableB (BinderP b ann) where
  withFreeVarsB (b:>ann) = UnsafeMakeWithFreeVarsB (b':>ann') (S.union s1 s2) f
    where
      UnsafeMakeWithFreeVarsE ann' s1   = withFreeVarsE ann
      UnsafeMakeWithFreeVarsB b'   s2 f = withFreeVarsB b

instance HoistableB UnitB where
  withFreeVarsB UnitB = UnsafeMakeWithFreeVarsB UnitB mempty id

instance HoistableE e => HoistableE (ListE e) where
  withFreeVarsE (ListE xs) = UnsafeMakeWithFreeVarsE (ListE xs') $ fold fvss
    where (xs', fvss) = unzip [(x, fvs) | UnsafeMakeWithFreeVarsE x fvs <- map withFreeVarsE xs]

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

-- === environments and scopes ===

lookupEnvFrag :: EnvFrag v i i' o -> Name s (i:=>:i') -> v s o
lookupEnvFrag (UnsafeMakeEnv m _) (UnsafeMakeName rep rawName) =
  case M.lookup rawName m of
    Nothing -> error "Env lookup failed (this should never happen)"
    Just d -> fromEnvVal rep d

instance InFrag (EnvFrag v) where
  emptyInFrag = UnsafeMakeEnv mempty mempty
  catInFrags (UnsafeMakeEnv m1 s1) (UnsafeMakeEnv m2 s2) =
    UnsafeMakeEnv (m2 <> m1) (s2 <> s1)  -- flipped because Data.Map uses a left-biased `<>`

singletonEnv :: NameBinder c i i' -> v c o -> EnvFrag v i i' o
singletonEnv (UnsafeMakeBinder (UnsafeMakeName rep name)) x =
  UnsafeMakeEnv (M.singleton name $ EnvVal rep x) (S.singleton name)

fmapEnvFrag :: InjectableV v
            => (forall c. NameColor c => Name c (i:=>:i') -> v c o -> v' c o')
            -> EnvFrag v i i' o -> EnvFrag v' i i' o'
fmapEnvFrag f (UnsafeMakeEnv m s) = UnsafeMakeEnv m' s
  where m' = flip M.mapWithKey m \k (EnvVal rep val) ->
               withNameColorRep rep $
                 EnvVal rep $ f (UnsafeMakeName rep k) val


envFragAsScope :: EnvFrag v i i' o -> ScopeFrag i i'
envFragAsScope (UnsafeMakeEnv _ s) = UnsafeMakeScope s

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

instance Category (Nest b) where
  id = Empty
  nest' . nest = case nest of
    Empty -> nest'
    Nest b rest -> Nest b $ rest >>> nest'

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
  withFreeVarsB Empty = fmapWithFresVarsB (\UnitB -> Empty) $ withFreeVarsB UnitB
  withFreeVarsB (Nest b rest) =
    fmapWithFresVarsB (\(PairB b' rest') -> Nest b' rest') $
      withFreeVarsB (PairB b rest)

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
