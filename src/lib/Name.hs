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
  S (..), C (..), (<.>), SubstFrag (..), NameBinder (..),
  SubstReader (..), FromName (..), Distinct, DExt,
  Ext, ExtEvidence, ProvesExt (..), withExtEvidence, getExtEvidence,
  Subst (..), idSubst, idSubstFrag, newSubst, envFromFrag, traverseSubstFrag,
  WithScope (..), extendRenamer, ScopeReader (..), ScopeExtender (..),
  Scope (..), ScopeFrag (..), SubstE (..), SubstB (..),
  SubstV, InplaceT (..), extendInplaceT, extendInplaceTLocal,
  extendTrivialInplaceT, getOutMapInplaceT, runInplaceT,
  E, B, V, HasNamesE, HasNamesB, BindsNames (..), HasScope (..), RecSubstFrag (..), RecSubst (..),
  lookupTerminalSubstFrag,
  BindsOneName (..), BindsAtMostOneName (..), BindsNameList (..), (@@>),
  Abs (..), Nest (..), PairB (..), UnitB (..), NonEmptyNest (..), nonEmptyToNest,
  IsVoidS (..), UnitE (..), VoidE, PairE (..), toPairE, fromPairE,
  ListE (..), ComposeE (..), MapE (..), NonEmptyListE (..),
  EitherE (..), LiftE (..), EqE, EqB, OrdE, OrdB, VoidB,
  EitherB (..), BinderP (..),
  LiftB, pattern LiftB,
  HashMapE (..), HashableE,
  MaybeE, fromMaybeE, toMaybeE, pattern JustE, pattern NothingE, MaybeB,
  pattern JustB, pattern NothingB,
  toConstAbs, toConstAbsPure, PrettyE, PrettyB, ShowE, ShowB,
  runScopeReaderT, runScopeReaderM, runSubstReaderT, idNameSubst, liftSubstReaderT,
  liftScopeReaderT, liftScopeReaderM,
  ScopeReaderT (..), SubstReaderT (..),
  lookupSubstM, dropSubst, extendSubst, fmapNames, fmapNamesM, traverseNames,
  MonadKind, MonadKind1, MonadKind2,
  Monad1, Monad2, Fallible1, Fallible2, Catchable1, Catchable2, Monoid1,
  MonadIO1, MonadIO2,
  CtxReader1, CtxReader2, MonadFail1, MonadFail2, Alternative1, Alternative2,
  Searcher1, Searcher2, ScopeReader2, ScopeExtender2,
  applyAbs, applySubst, applyNaryAbs, ZipSubstReader (..), alphaEqTraversable,
  checkAlphaEq, alphaEq, alphaEqPure,
  AlphaEq, AlphaEqE (..), AlphaEqB (..), AlphaEqV, ConstE (..),
  AlphaHashableE (..), AlphaHashableB (..), EKey (..), EMap (..), ESet,
  lookupEMap, eMapSingleton, eSetSingleton, eMapToList, eSetToList,
  eMapFromList, eSetFromList,
  SinkableE (..), SinkableB (..), SinkableV, SinkingCoercion,
  withFreshM, sink, sinkList, sinkM, (!), (<>>), withManyFresh, refreshAbsPure,
  envFragAsScope, lookupSubstFrag, lookupSubstFragRaw,
  EmptyAbs, pattern EmptyAbs, NaryAbs, SubstVal (..),
  fmapNest, forEachNestItem, forEachNestItemM,
  substM, ScopedSubstReader, runScopedSubstReader,
  HasNameHint (..), NameHint (..), Color (..),
  GenericE (..), GenericB (..),
  EitherE1, EitherE2, EitherE3, EitherE4, EitherE5, EitherE6,
    pattern Case0, pattern Case1, pattern Case2, pattern Case3, pattern Case4, pattern Case5,
  EitherB1, EitherB2, EitherB3, EitherB4, EitherB5,
    pattern CaseB0, pattern CaseB1, pattern CaseB2, pattern CaseB3, pattern CaseB4,
  splitNestAt, joinNest, nestLength, nestToList, binderAnn,
  OutReaderT (..), OutReader (..), runOutReaderT,
  ExtWitness (..),
  InFrag (..), InMap (..), OutFrag (..), OutMap (..), ExtOutMap (..),
  toSubstPairs, fromSubstPairs, SubstPair (..),
  hoist, hoistToTop, sinkFromTop, fromConstAbs, exchangeBs, HoistableE (..),
  HoistExcept (..), liftHoistExcept, abstractFreeVars, abstractFreeVar,
  abstractFreeVarsNoAnn,
  WithRenamer (..), ignoreHoistFailure,
  HoistableB (..), HoistableV, withScopeFromFreeVars, canonicalizeForPrinting,
  ClosedWithScope (..),
  WrapE (..), WrapB (..), WithColor (..), fromWithColor,
  DistinctEvidence (..), withSubscopeDistinct, tryAsColor, withFresh,
  newName, newNameM, newNames, newNamesM,
  unsafeCoerceE, unsafeCoerceB, ColorsEqual (..), eqColorRep,
  sinkR, fmapSubstFrag, catRecSubstFrags, extendRecSubst,
  freeVarsList, isFreeIn, areFreeIn, todoSinkableProof,
  locallyMutableInplaceT, liftBetweenInplaceTs, toExtWitness,
  updateSubstFrag, nameSetToList, toNameSet, absurdExtEvidence,
  Mut, fabricateDistinctEvidence,
  MonadTrans1 (..), collectGarbage,
  ) where

import Prelude hiding (id, (.))
import Control.Category
import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Except hiding (Except)
import Control.Monad.Reader
import Control.Monad.Writer.Strict
import Control.Monad.State.Strict
import qualified Data.HashMap.Strict as HM
import qualified Data.Map.Strict as M
import qualified Data.Set        as S
import Data.Functor ((<&>))
import Data.Foldable (fold, toList)
import Data.Maybe (catMaybes)
import Data.Hashable
import Data.Kind (Type)
import Data.String
import Data.Function ((&))
import Data.List.NonEmpty (NonEmpty (..))
import Data.Text.Prettyprint.Doc  hiding (nest)
import qualified Data.Text as T
import GHC.Stack
import GHC.Exts (Constraint)
import GHC.Generics (Generic (..), Rep)
import Data.Store.Internal

import qualified Unsafe.Coerce as TrulyUnsafe

import Util (zipErr, onFst, onSnd, transitiveClosure)
import Err

-- === category-like classes for envs, scopes etc ===

data Subst v i o where
  Subst :: (forall c. Color c => Name c hidden -> v c o)
      -> SubstFrag v hidden i o
      -> Subst v i o

newSubst :: (forall c. Color c => Name c i -> v c o) -> Subst v i o
newSubst f = Subst f emptyInFrag

envFromFrag :: SubstFrag v VoidS i o -> Subst v i o
envFromFrag frag = Subst absurdNameFunction frag

idSubst :: FromName v => Subst v n n
idSubst = newSubst fromName

-- common instantiation (useful where `v` would be ambiguous)
idNameSubst :: Subst Name n n
idNameSubst = idSubst

idSubstFrag :: (BindsNames b, FromName v) => b n l -> SubstFrag v n l l
idSubstFrag b =
  fmapSubstFrag (\v _ -> fromName $ sinkR v) $ scopeFragToSubstFrag (toScopeFrag b)

infixl 9 !
(!) :: Color c => Subst v i o -> Name c i -> v c o
(!) (Subst f env) name =
  case lookupSubstFragProjected env name of
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

class (SinkableB scopeFrag, BindsNames scopeFrag) => OutFrag (scopeFrag :: S -> S -> *) where
  emptyOutFrag :: scopeFrag n n
  -- The scope is here because solver subst concatenation needs it
  catOutFrags  :: Distinct n3 => Scope n3 -> scopeFrag n1 n2 -> scopeFrag n2 n3 -> scopeFrag n1 n3

class HasScope scope => OutMap scope where
  emptyOutMap :: scope VoidS

class (OutFrag scopeFrag, OutMap scope)
      => ExtOutMap (scope :: S -> *) (scopeFrag :: S -> S -> *) where
  extendOutMap :: Distinct l => scope n -> scopeFrag n l -> scope l

todoSinkableProof :: a
todoSinkableProof =
  error "This will never be called. But we should really finish these proofs."

instance InMap (Subst v) (SubstFrag v) where
  emptyInMap = newSubst absurdNameFunction
  extendInMap (Subst f frag) frag' = Subst f $ frag <.> frag'

instance SinkableB ScopeFrag where
  sinkingProofB _ _ _ = todoSinkableProof

instance OutFrag ScopeFrag where
  emptyOutFrag = id
  catOutFrags _ = (>>>)

instance HasScope Scope where
  toScope = id

instance OutMap Scope where
  emptyOutMap = Scope id

instance ExtOutMap Scope ScopeFrag where
  extendOutMap (Scope scope) frag = Scope $ scope >>> frag

-- outvar version of SubstFrag/Subst, where the query name space and the result name
-- space are the same (thus recursive)
newtype RecSubst      (v::V) o    = RecSubst     { fromRecSubst     :: SubstFrag v VoidS o o } deriving Generic
newtype RecSubstFrag  (v::V) o o' = RecSubstFrag { fromRecSubstFrag :: SubstFrag v o o' o'   } deriving Generic

instance SinkableV v => OutFrag (RecSubstFrag v) where
  emptyOutFrag = RecSubstFrag $ emptyInFrag
  catOutFrags _ = catRecSubstFrags

catRecSubstFrags :: (Distinct n3, SinkableV v)
               => RecSubstFrag v n1 n2 -> RecSubstFrag v n2 n3 -> RecSubstFrag v n1 n3
catRecSubstFrags (RecSubstFrag frag1) (RecSubstFrag frag2) = RecSubstFrag $
  withExtEvidence (toExtEvidence (RecSubstFrag frag2)) $
    sink frag1 `catInFrags` frag2

extendRecSubst :: SinkableV v => Distinct l => RecSubst v n -> RecSubstFrag v n l
               -> RecSubst v l
extendRecSubst (RecSubst env) (RecSubstFrag frag) = RecSubst $
  withExtEvidence (toExtEvidence (RecSubstFrag frag)) $
    sink env <.> frag

deriving instance (forall c. Show (v c o')) => Show (RecSubstFrag v o o')

lookupTerminalSubstFrag :: Color c => SubstFrag v VoidS i o -> Name c i -> v c o
lookupTerminalSubstFrag frag name =
  case lookupSubstFragProjected frag name of
    Left name' -> absurdNameFunction name'
    Right val -> val

instance (SinkableB b, BindsNames b) => OutFrag (Nest b) where
  emptyOutFrag = id
  catOutFrags _ = (>>>)

updateSubstFrag :: Color c => Name c i -> v c o -> SubstFrag v VoidS i o
                -> SubstFrag v VoidS i o
updateSubstFrag (UnsafeMakeName v) rhs (UnsafeMakeSubst m) =
  UnsafeMakeSubst $ M.adjust (\(_:rest) -> (WithColor rhs) : rest ) v m

-- === monadic type classes for reading and extending envs and scopes ===

data WithScope (e::E) (n::S) where
  WithScope :: (Distinct l, Ext l n) => Scope l -> e l -> WithScope e n

instance SinkableE e => SinkableE (WithScope e) where
  sinkingProofE (fresh::SinkingCoercion n l) (WithScope (scope::Scope h) e) =
    withExtEvidence (sinkingProofE fresh ext) $
      WithScope scope e
    where ext = getExtEvidence :: ExtEvidence h n

class Monad1 m => ScopeReader (m::MonadKind1) where
  unsafeGetScope :: m n (Scope n)
  getDistinct :: m n (DistinctEvidence n)

class ScopeReader m => ScopeExtender (m::MonadKind1) where
  -- We normally use the EnvReader version, `refreshAbs`, but sometime we're
  -- working with raw binders that don't have env information associated with
  -- them, `BindsEnv b`, in which case this makes more sense.
  refreshAbsScope :: (SubstB Name b, SubstE Name e, BindsNames b)
                  => Abs b e n
                  -> (forall l. DExt n l => b n l -> e l -> m l a)
                  -> m n a

class (SinkableV v, Monad2 m) => SubstReader (v::V) (m::MonadKind2) | m -> v where
   getSubst :: m i o (Subst v i o)
   withSubst :: Subst v i' o -> m i' o a -> m i o a

lookupSubstM :: (Color c, SubstReader v m) => Name c i -> m i o (v c o)
lookupSubstM name = (!name) <$> getSubst

dropSubst :: (SubstReader v m, FromName v) => m o o r -> m i o r
dropSubst cont = withSubst idSubst cont

extendSubst :: SubstReader v m => SubstFrag v i i' o -> m i' o r -> m i o r
extendSubst frag cont = do
  env <- (<>>frag) <$> getSubst
  withSubst env cont

-- === extending envs with name-only substitutions ===

class FromName (v::V) where
  fromName :: Name c n -> v c n

instance FromName Name where
  fromName = id

instance FromName (SubstVal c v) where
  fromName = Rename

extendRenamer :: (SubstReader v m, FromName v) => SubstFrag Name i i' o -> m i' o r -> m i o r
extendRenamer frag = extendSubst (fmapSubstFrag (const fromName) frag)

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

data NonEmptyNest (b::B) (n::S) (l::S) where
  NonEmptyNest :: b n h -> Nest b h l -> NonEmptyNest b n l

nonEmptyToNest :: NonEmptyNest b n l -> Nest b n l
nonEmptyToNest (NonEmptyNest b bs) = Nest b bs

-- === Sinkings and projections ===

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

instance ProvesExt ExtEvidence where
  toExtEvidence = id

instance ProvesExt ScopeFrag
instance BindsNames ScopeFrag where
  toScopeFrag s = s

instance HoistableB ScopeFrag where
  freeVarsB _ = mempty

class HasScope (bindings :: S -> *) where
  -- XXX: this must be O(1)
  toScope :: bindings n -> Scope n

withExtEvidence :: ProvesExt b => b n l -> (Ext n l => a) -> a
withExtEvidence b cont = withExtEvidence' (toExtEvidence b) cont

-- like sink, but uses the ScopeReader monad for its `Distinct` proof
sinkM :: (ScopeReader m, Ext n l, SinkableE e) => e n -> m l (e l)
sinkM e = do
  Distinct <- getDistinct
  return $ sink e

data ExtWitness (n::S) (l::S) where
  ExtW :: Ext n l => ExtWitness n l

instance ProvesExt ExtWitness where
  toExtEvidence ExtW = getExtEvidence

instance SinkableE (ExtWitness n) where
  sinkingProofE :: forall l l'. SinkingCoercion l l' -> ExtWitness n l -> ExtWitness n l'
  sinkingProofE fresh ExtW =
    withExtEvidence (sinkingProofE fresh (getExtEvidence :: ExtEvidence n l)) ExtW

instance Category ExtWitness where
  id = ExtW
  ExtW . ExtW = ExtW

-- XXX: this only (monadically) visits each name once, even if a name has
-- multiple occurrences. So don't use it to count occurrences or anything like
-- that! It's not deliberate. It's just an accident of the implementation, where
-- we gather the (de-duplicated) free names and then traverse them. At some
-- point we may add a monadic traversal to `Subst{E,B}`, which would actually
-- visit each occurrence.
traverseNames
  :: forall v e m i o.
     (SubstE v e, HoistableE e, SinkableE e, FromName v, ScopeReader m)
  => (forall c. Color c => Name c i -> m o (v c o))
  -> e i -> m o (e o)
traverseNames f e = do
  let vs = freeVarsE e
  m <- M.fromList <$> forM (M.toList vs)
         \(rawName, WithColor (UnitV :: UnitV c UnsafeS)) -> do
            x <- f (UnsafeMakeName rawName :: Name c i)
            return (rawName, WithColor x)
  fmapNamesM (\((UnsafeMakeName v) :: Name c i) -> case M.lookup v m of
    Just (WithColor val) -> case tryAsColor val of
      Just val' -> val'
      Nothing -> error "shouldn't happen"
    Nothing -> fromName $ (UnsafeMakeName v :: Name c o)) e

fmapNames :: (SubstE v e, Distinct o)
          => Scope o -> (forall c. Color c => Name c i -> v c o) -> e i -> e o
fmapNames scope f e = substE (scope, newSubst f) e

fmapNamesM :: (SubstE v e, SinkableE e, ScopeReader m)
          => (forall c. Color c => Name c i -> v c o)
          -> e i -> m o (e o)
fmapNamesM f e = do
  scope <- unsafeGetScope
  Distinct <- getDistinct
  return $ substE (scope, newSubst f) e

toConstAbs :: (SinkableE e, ScopeReader m, Color c)
           => e n -> m n (Abs (NameBinder c) e n)
toConstAbs body = do
  WithScope scope body' <- addScope body
  withFresh "ignore" scope \b -> do
    sinkM $ Abs b $ sink body'

toConstAbsPure :: (HoistableE e, SinkableE e, Color c)
               => e n -> (Abs (NameBinder c) e n)
toConstAbsPure e = Abs (UnsafeMakeBinder n) (unsafeCoerceE e)
  where n = freshRawName NoHint $ freeVarsE e

-- === type classes for traversing names ===

class FromName v => SubstE (v::V) (e::E) where
  -- TODO: can't make an alias for these constraints because of impredicativity
  substE :: Distinct o => (Scope o, Subst v i o) -> e i -> e o

  default substE :: (GenericE e, SubstE v (RepE e), Distinct o)
                 => (Scope o, Subst v i o) -> e i -> e o
  substE env e = toE $ substE env (fromE e)

class (FromName v, SinkableB b) => SubstB (v::V) (b::B) where
  substB
    :: Distinct o
    => (Scope o, Subst v i o)
    -> b i i'
    -> (forall o'. Distinct o' => (Scope o', Subst v i' o') -> b o o' -> a)
    -> a

  default substB
    :: (GenericB b, SubstB v (RepB b))
    => Distinct o
    => (Scope o, Subst v i o)
    -> b i i'
    -> (forall o'. Distinct o' => (Scope o', Subst v i' o') -> b o o' -> a)
    -> a
  substB env b cont =
    substB env (fromB b) \env' b' ->
      cont env' $ toB b'

class ( FromName substVal, SinkableV v
      , forall c. Color c => SubstE substVal (v c))
      => SubstV (substVal::V) (v::V)

type HasNamesE e = (SubstE Name e, HoistableE e)
type HasNamesB = SubstB Name

instance SubstV Name Name where
instance Color c => SubstE Name (Name c) where
  substE (_, env) name = env ! name

instance (Color c, SinkableV v, FromName v) => SubstB v (NameBinder c) where
  substB (scope, env) b cont = do
    withFresh (getNameHint b) scope \b' -> do
      let scope' = scope `extendOutMap` toScopeFrag b'
      let env' = sink env <>> b @> (fromName $ binderName b')
      cont (scope', env') b'

substM :: (SubstReader v m, ScopeReader2 m, SinkableE e, SubstE v e, FromName v)
       => e i -> m i o (e o)
substM e = do
  env <- getSubst
  WithScope scope env' <- addScope env
  sinkM $ fmapNames scope (env'!) e

fromConstAbs :: (BindsNames b, HoistableE e) => Abs b e n -> HoistExcept (e n)
fromConstAbs (Abs b e) = hoist b e

-- === various E-kind and B-kind versions of standard containers and classes ===

type PrettyE e = (forall (n::S)       . Pretty (e n  )) :: Constraint
type PrettyB b = (forall (n::S) (l::S). Pretty (b n l)) :: Constraint

type ShowE e = (forall (n::S)       . Show (e n  )) :: Constraint
type ShowB b = (forall (n::S) (l::S). Show (b n l)) :: Constraint

type EqE e = (forall (n::S)       . Eq (e n  )) :: Constraint
type EqB b = (forall (n::S) (l::S). Eq (b n l)) :: Constraint

type OrdE e = (forall (n::S)       . Ord (e n  )) :: Constraint
type OrdB b = (forall (n::S) (l::S). Ord (b n l)) :: Constraint

type HashableE (e::E) = forall n. Hashable (e n)

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

newtype MapE (k::E) (v::E) (n::S) = MapE { fromMapE :: M.Map (k n) (v n) }
                                    deriving (Semigroup, Monoid)

newtype HashMapE (k::E) (v::E) (n::S) =
  HashMapE { fromHashMapE :: HM.HashMap (k n) (v n) }
  deriving (Semigroup, Monoid, Show)

newtype NonEmptyListE (e::E) (n::S) = NonEmptyListE { fromNonEmptyListE :: NonEmpty (e n)}
        deriving (Show, Eq, Generic)

newtype LiftE (a:: *) (n::S) = LiftE { fromLiftE :: a }
        deriving (Show, Eq, Generic, Monoid, Semigroup)

newtype ComposeE (f :: * -> *) (e::E) (n::S) =
  ComposeE { fromComposeE :: (f (e n)) }
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
type UnitV = ConstE UnitE
pattern UnitV :: UnitV c n
pattern UnitV = ConstE UnitE

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

pattern NothingB :: () => (n ~ l) => MaybeB b n l
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
  (@>) :: b i i' -> v c o -> SubstFrag v i i' o

class BindsAtMostOneName (b::B) (c::C)
  =>  BindsOneName (b::B) (c::C) | b -> c where
  binderName :: b i i' -> Name c i'

instance Color c => ProvesExt  (NameBinder c) where

instance Color c => BindsAtMostOneName (NameBinder c) c where
  b @> x = singletonSubst b x

instance Color c => BindsOneName (NameBinder c) c where
  binderName (UnsafeMakeBinder v) = UnsafeMakeName v

instance Color c => BindsAtMostOneName (BinderP c ann) c where
  (b:>_) @> x = b @> x

instance Color c => BindsOneName (BinderP c ann) c where
  binderName (b:>_) = binderName b

infixr 7 @@>
(@@>) :: (Foldable f, BindsNameList b c) => b i i' -> f (v c o) -> SubstFrag v i i' o
(@@>) bs xs = bindNameList bs (toList xs)

class BindsNameList (b::B) (c::C) | b -> c where
  bindNameList :: b i i' -> [v c o] -> SubstFrag v i i' o

instance BindsAtMostOneName b c => BindsNameList (Nest b) c where
  bindNameList Empty [] = emptyInFrag
  bindNameList (Nest b rest) (x:xs) = b@>x <.> bindNameList rest xs
  bindNameList _ _ = error "length mismatch"

instance GenericB (NonEmptyNest b) where
  type RepB (NonEmptyNest b) = PairB b (Nest b)
  fromB (NonEmptyNest b bs) = PairB b bs
  toB   (PairB b bs) = NonEmptyNest b bs

instance BindsAtMostOneName b c => BindsNameList (NonEmptyNest b) c where
  bindNameList (NonEmptyNest b bs) (x:xs) = b@>x <.> bindNameList bs xs
  bindNameList _ _ = error "length mismatch"

instance BindsNames b => ProvesExt  (NonEmptyNest b)
instance BindsNames b => BindsNames (NonEmptyNest b)
instance HoistableB b => HoistableB (NonEmptyNest b)
instance SinkableB  b => SinkableB  (NonEmptyNest b)
instance (BindsNames b, SinkableV v, SubstB v b) => SubstB v (NonEmptyNest b)

applySubst :: (ScopeReader m, SubstE v e, SinkableE e, SinkableV v, FromName v)
           => Ext h o
           => SubstFrag v h i o -> e i -> m o (e o)
applySubst substFrag x = do
  Distinct <- getDistinct
  let fullSubst = sink idSubst <>> substFrag
  WithScope scope fullSubst' <- addScope fullSubst
  sinkM $ fmapNames scope (fullSubst' !) x

applyAbs :: ( SinkableV v, SinkableE e
            , FromName v, ScopeReader m, BindsOneName b c, SubstE v e)
         => Abs b e n -> v c n -> m n (e n)
applyAbs (Abs b body) x = applySubst (b@>x) body

applyNaryAbs :: ( SinkableV v, FromName v, ScopeReader m, BindsNameList b c, SubstE v e
                , SubstB v b, SinkableE e)
             => Abs b e n -> [v c n] -> m n (e n)
applyNaryAbs (Abs bs body) xs = applySubst (bs @@> xs) body

lookupSubstFragProjected :: Color c => SubstFrag v i i' o -> Name c i'
                         -> Either (Name c i) (v c o)
lookupSubstFragProjected m name =
  case projectName (envFragAsScope m) name of
    Left  name' -> Left name'
    Right name' -> Right $ lookupSubstFrag m name'

fromSubstPairs :: Nest (SubstPair v o) i i' -> SubstFrag v i i' o
fromSubstPairs Empty = emptyInFrag
fromSubstPairs (Nest (SubstPair b v) rest) =
  singletonSubst b v `catInFrags`fromSubstPairs rest

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
traverseSubstFrag :: forall v v' i i' o o' m .
                   Monad m
                => (forall c. Color c => v c o -> m (v' c o'))
                -> SubstFrag v i i' o  -> m (SubstFrag v' i i' o')
traverseSubstFrag f frag = liftM fromSubstPairs $
  forEachNestItemM (toSubstPairs frag) \(SubstPair b val) ->
    SubstPair b <$> f val

foldMapSubstFrag
  :: forall v i i' o accum . Monoid accum
  => (forall c. Color c => v c o -> accum)
  -> SubstFrag v i i' o -> accum
foldMapSubstFrag f frag =
  execWriter $ traverseSubstFrag (\x -> tell (f x) >> return x) frag

nestLength :: Nest b n l -> Int
nestLength Empty = 0
nestLength (Nest _ rest) = 1 + nestLength rest

nestToList :: BindsNames b
           => (forall n' l'. (Ext n' l', Ext l' l) => b n' l' -> a)
           -> Nest b n l -> [a]
nestToList _ Empty = []
nestToList f (Nest b rest) = b' : nestToList f rest
  where b' = withExtEvidence (toExtEvidence rest) $
               withExtEvidence (toExtEvidence b) $
                 f b

splitNestAt :: Int -> Nest b n l -> PairB (Nest b) (Nest b) n l
splitNestAt 0 bs = PairB Empty bs
splitNestAt _  Empty = error "split index too high"
splitNestAt n (Nest b rest) =
  case splitNestAt (n-1) rest of
    PairB xs ys -> PairB (Nest b xs) ys

joinNest :: Nest b n m -> Nest b m l -> Nest b n l
joinNest l r = case l of
  Empty     -> r
  Nest b lt -> Nest b $ joinNest lt r

binderAnn :: BinderP c ann n l -> ann n
binderAnn (_:>ann) = ann

withManyFresh :: (Distinct n, Color c)
              => [NameHint] -> Scope n
              -> (forall l. DExt n l => Nest (NameBinder c) n l -> a) -> a
withManyFresh [] _ cont = cont Empty
withManyFresh (h:hs) scope cont =
  withFresh h scope \b ->
    withManyFresh hs (scope `extendOutMap` toScopeFrag b) \bs ->
      cont $ Nest b bs

refreshAbsPure
  :: forall n b e a .
     (Distinct n, BindsNames b, SubstB Name b, SubstE Name e)
  => Scope n -> Abs b e n
  -> (forall l. DExt n l => Scope l -> b n l -> e l -> a)
  -> a
refreshAbsPure scope (Abs b e) cont =
  case extendIfDistinct scope (toScopeFrag b) of
    Just (Distinct, scope') ->
      withExtEvidence b $ cont scope' b e
    Nothing ->
      substB (scope, idSubst :: Subst Name n n) b \(scope', subst') b' -> do
        let e' = substE (scope', subst') e
        withExtEvidence b' $ cont scope' b' e'

extendIfDistinct :: Scope n -> ScopeFrag n l
                 -> Maybe (DistinctEvidence l, Scope l)
extendIfDistinct scope frag = do
  if all isUnique extNames && M.disjoint scopeNames extNames
    then Just ( fabricateDistinctEvidence
              , Scope (UnsafeMakeScopeFrag (extNames  <> scopeNames)))
    else Nothing
  where
    Scope (UnsafeMakeScopeFrag scopeNames) = scope
    UnsafeMakeScopeFrag extNames = frag
    isUnique :: [a] -> Bool
    isUnique [_] = True
    isUnique _   = False

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

withFreshM :: (ScopeExtender m, Color c)
           => NameHint
           -> (forall o'. (DExt o o') => NameBinder c o o' -> m o' a)
           -> m o a
withFreshM hint cont = refreshAbsScope (newName hint) \b _ -> cont b

class ColorsNotEqual a b where
  notEqProof :: ColorsEqual a b -> r

instance (Color c, ColorsNotEqual cMatch c)
         => (SubstE (SubstVal cMatch atom) (Name c)) where
  substE (_, env) name =
    case env ! name of
      Rename name' -> name'
      SubstVal _ -> notEqProof (ColorsEqual :: ColorsEqual c cMatch)

instance (SubstE (SubstVal cMatch atom) atom, Color c)
         => SubstE (SubstVal cMatch atom) (SubstVal cMatch atom c) where
  substE (_, env) (Rename name) = env ! name
  substE env (SubstVal val) = SubstVal $ substE env val

instance (SubstE (SubstVal cMatch atom) atom, SinkableE atom)
         => SubstV (SubstVal cMatch atom) (SubstVal cMatch atom) where

instance (Color c, SinkableE atom, SubstE Name atom)
         => SubstE Name (SubstVal cMatch atom c) where
  substE (_, env) (Rename name) = Rename $ env ! name
  substE (scope, env) (SubstVal atom) = SubstVal $ substE (scope, env) atom

instance (SinkableE atom, SubstE Name atom) => SubstV Name (SubstVal cMatch atom)

-- TODO: we can fill out the full (N^2) set of instances if we need to
instance ColorsNotEqual AtomNameC DataDefNameC where notEqProof = \case
instance ColorsNotEqual AtomNameC ClassNameC   where notEqProof = \case
instance ColorsNotEqual AtomNameC SuperclassNameC where notEqProof = \case
instance ColorsNotEqual AtomNameC ImpFunNameC     where notEqProof = \case
instance ColorsNotEqual AtomNameC PtrNameC        where notEqProof = \case

-- === alpha-renaming-invariant equality checking ===

type AlphaEq e = AlphaEqE e  :: Constraint

-- TODO: consider generalizing this to something that can also handle e.g.
-- unification and type checking with some light reduction
class ( forall i1 i2 o. Monad (m i1 i2 o)
      , forall i1 i2 o. Fallible (m i1 i2 o)
      , forall i1 i2 o. MonadFail (m i1 i2 o)
      , forall i1 i2.   ScopeExtender (m i1 i2))
      => ZipSubstReader (m :: S -> S -> S -> * -> *) where
  lookupZipSubstFst :: Color c => Name c i1 -> m i1 i2 o (Name c o)
  lookupZipSubstSnd :: Color c => Name c i2 -> m i1 i2 o (Name c o)

  extendZipSubstFst :: SubstFrag Name i1 i1' o -> m i1' i2  o r -> m i1 i2 o r
  extendZipSubstSnd :: SubstFrag Name i2 i2' o -> m i1  i2' o r -> m i1 i2 o r

  withEmptyZipSubst :: m o o o a -> m i1 i2 o a

class SinkableE e => AlphaEqE (e::E) where
  alphaEqE :: ZipSubstReader m => e i1 -> e i2 -> m i1 i2 o ()

  default alphaEqE :: (GenericE e, AlphaEqE (RepE e), ZipSubstReader m)
                   => e i1 -> e i2 -> m i1 i2 o ()
  alphaEqE e1 e2 = fromE e1 `alphaEqE` fromE e2

class SinkableB b => AlphaEqB (b::B) where
  withAlphaEqB :: ZipSubstReader m => b i1 i1' -> b i2 i2'
               -> (forall o'. m i1' i2' o' a)
               ->             m i1  i2  o  a

  default withAlphaEqB :: (GenericB b, AlphaEqB (RepB b), ZipSubstReader m)
                       => b i1 i1' -> b i2 i2'
                       -> (forall o'. m i1' i2' o' a)
                       ->             m i1  i2  o  a
  withAlphaEqB b1 b2 cont = withAlphaEqB (fromB b1) (fromB b2) $ cont

class ( SinkableV v
      , forall c. Color c => AlphaEqE (v c))
      => AlphaEqV (v::V) where

addScope :: (ScopeReader m, SinkableE e) => e n -> m n (WithScope e n)
addScope e = do
  scope <- unsafeGetScope
  Distinct <- getDistinct
  return $ WithScope scope (sink e)

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

checkAlphaEqPure :: (AlphaEqE e, Distinct n)
                 => Scope n -> e n -> e n -> Except ()
checkAlphaEqPure scope e1 e2 =
  runScopeReaderT scope $
    flip runReaderT (emptyInMap, emptyInMap) $ runZipSubstReaderT $
      withEmptyZipSubst $ alphaEqE e1 e2

instance AlphaEqV Name
instance Color c => AlphaEqE (Name c) where
  alphaEqE v1 v2 = do
    v1' <- lookupZipSubstFst v1
    v2' <- lookupZipSubstSnd v2
    unless (v1' == v2') zipErr

instance Color c => AlphaEqB (NameBinder c) where
  withAlphaEqB b1 b2 cont = do
    withFreshM (getNameHint b1) \b -> do
      let v = binderName b
      extendZipSubstFst (b1@>v) $ extendZipSubstSnd (b2@>v) $ cont

alphaEqTraversable :: (AlphaEqE e, Traversable f, Eq (f ()), ZipSubstReader m)
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

instance Generic (e UnsafeS) => Generic (LiftB e n l) where
  -- We tack on unit because it makes the `Store e => Store (LiftB e)` instance
  -- work ... I guess it's the indirection somehow? There's probably some
  -- constructor you're supposed to use instead, but this works.
  type Rep (LiftB e n l) = Rep (e UnsafeS, ())
  from (LiftB e) = from ((unsafeCoerceE e :: e UnsafeS), ())
  to   rep = unsafeCoerceB (LiftB e :: LiftB e UnsafeS UnsafeS)
     where (e, ()) = to rep

instance AlphaEqE e => AlphaEqB (LiftB e) where
  withAlphaEqB (LiftB e1) (LiftB e2) cont = alphaEqE e1 e2 >> cont

instance (Color c, AlphaEqE ann) => AlphaEqB (BinderP c ann) where
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

-- === alpha-renaming-invariant hashing ===

type HashVal = Int
data NamePreHash (c::C) (n::S) =
   HashFreeName RawName
    -- XXX: convention is the opposite of de Bruijn order, `0` means the
    -- *outermost* binder
 | HashBoundName Int
 deriving (Eq, Generic)

instance Hashable RawName
instance Hashable (NamePreHash c n)

data HashEnv n =
  -- the Int is the number of local binders in scope
  HashEnv Int (Subst NamePreHash n VoidS)

emptyHashEnv :: HashEnv n
emptyHashEnv = HashEnv 0 (newSubst $ HashFreeName . getRawName)

lookupHashEnv :: Color c => HashEnv n -> Name c n -> NamePreHash c VoidS
lookupHashEnv (HashEnv _ env) name = env ! name

alphaHashWithSalt :: AlphaHashableE e => HashVal -> e n -> HashVal
alphaHashWithSalt salt e = hashWithSaltE emptyHashEnv salt e

extendHashEnv :: Color c => HashEnv n -> NameBinder c n l -> HashEnv l
extendHashEnv (HashEnv depth env) b =
  HashEnv (depth + 1) (env <>> b @> HashBoundName depth)

class AlphaHashableE (e::E) where
  hashWithSaltE :: HashEnv n -> HashVal -> e n -> HashVal

  default hashWithSaltE :: (GenericE e, AlphaHashableE (RepE e))
                        => HashEnv n -> HashVal -> e n -> HashVal
  hashWithSaltE env salt e = hashWithSaltE env salt (fromE e)

class AlphaHashableB (b::B) where
  hashWithSaltB :: HashEnv n -> HashVal -> b n l -> (HashVal, HashEnv l)
  default hashWithSaltB :: (GenericB b, AlphaHashableB (RepB b))
                        => HashEnv n -> HashVal -> b n l -> (HashVal, HashEnv l)
  hashWithSaltB env salt b = hashWithSaltB env salt (fromB b)

instance Color c => AlphaHashableE (Name c) where
  hashWithSaltE env salt v = hashWithSalt salt $ lookupHashEnv env v

instance Color c => AlphaHashableB (NameBinder c) where
  hashWithSaltB env salt b = (salt, extendHashEnv env b)

instance AlphaHashableE UnitE where
  hashWithSaltE _ salt UnitE = salt

instance (AlphaHashableE e1, AlphaHashableE e2) => AlphaHashableE (PairE e1 e2) where
  hashWithSaltE env salt (PairE e1 e2) = do
    let h = hashWithSaltE env salt e1
    hashWithSaltE env h e2

instance (AlphaHashableB b, AlphaHashableE e) => AlphaHashableE (Abs b e) where
  hashWithSaltE env salt (Abs b e) = do
    let (h, env') = hashWithSaltB env salt b
    hashWithSaltE env' h e

instance (AlphaHashableB b) => AlphaHashableB (Nest b) where
  hashWithSaltB env salt Empty = (hashWithSalt salt (0::Int), env)
  hashWithSaltB env salt (Nest b rest) = do
    let h1 = hashWithSalt salt (1::Int)
    let (h2, env') = hashWithSaltB env h1 b
    hashWithSaltB env' h2 rest

instance (AlphaHashableB b1, AlphaHashableB b2)
         => AlphaHashableB (PairB b1 b2) where
  hashWithSaltB env salt (PairB b1 b2) = do
    let (h, env') = hashWithSaltB env salt b1
    hashWithSaltB env' h b2

instance (Color c, AlphaHashableE ann) => AlphaHashableB (BinderP c ann) where
  hashWithSaltB env salt (b:>ann) = do
    let h = hashWithSaltE env salt ann
    hashWithSaltB env h b

instance Hashable a => AlphaHashableE (LiftE a) where
  hashWithSaltE _ salt (LiftE x) = hashWithSalt salt x

instance AlphaHashableE e => AlphaHashableB (LiftB e) where
  hashWithSaltB env salt (LiftB x) = (hashWithSaltE env salt x, env)

instance AlphaHashableE e => AlphaHashableE (ListE e) where
  hashWithSaltE _ salt (ListE []) = hashWithSalt salt (0::Int)
  hashWithSaltE env salt (ListE (x:xs)) = do
    let h1 = hashWithSalt salt (1::Int)
    let h2 = hashWithSaltE env h1 x
    hashWithSaltE env h2 $ ListE xs

instance (AlphaHashableE e1, AlphaHashableE e2) => AlphaHashableE (EitherE e1 e2) where
  hashWithSaltE env salt (LeftE e) = do
    let h = hashWithSalt salt (0::Int)
    hashWithSaltE env h e
  hashWithSaltE env salt (RightE e) = do
    let h = hashWithSalt salt (1::Int)
    hashWithSaltE env h e

instance AlphaHashableE VoidE where
  hashWithSaltE _ _ _ = error "impossible"

-- === wrapper for E-kinded things suitable for use as keys ===

newtype EKey (e::E) (n::S) = EKey { fromEKey :: e n }
        deriving (Show, Generic)

instance GenericE (EKey e) where
  type RepE (EKey e) = e
  fromE (EKey e) = e
  toE e = EKey e

-- We can do alpha-invariant equality checking without a scope at hand. It's
-- slower (because we have to query the free vars of both expressions) and its
-- implementation is unsafe, but it's needed for things like HashMap.
instance (HoistableE e, AlphaEqE e) => Eq (EKey e n) where
  EKey x == EKey y =
    case withScopeFromFreeVars $ PairE x y of
      ClosedWithScope scope (PairE x' y') ->
        runScopeReaderM scope $ alphaEq x' y'

instance (HoistableE e, AlphaEqE e, AlphaHashableE e) => Hashable (EKey e n) where
  hashWithSalt salt (EKey e) = alphaHashWithSalt salt e

instance SubstE v   e => SubstE v   (EKey e)
instance HoistableE e => HoistableE (EKey e)
instance SinkableE  e => SinkableE  (EKey e)
instance Store (e n) => Store (EKey e n)

data EMap (k::E) (v::E) (n::S) = EMap (HM.HashMap (EKey k n) (v n))
                                 deriving (Show, Generic)

eMapSingleton :: (HoistableE k, AlphaEqE k, AlphaHashableE k) => k n -> v n -> EMap k v n
eMapSingleton k v = EMap $ HM.singleton (EKey k) v

eMapToList :: EMap k v n -> [(k n, v n)]
eMapToList (EMap m) = [(k, v) | (EKey k, v) <- HM.toList m]

eMapFromList :: (AlphaEqE k, AlphaHashableE k, HoistableE k) => [(k n, v n)] -> EMap k v n
eMapFromList xs = EMap $ HM.fromList [(EKey k, v) | (k, v) <- xs]

eSetSingleton :: (AlphaEqE k, AlphaHashableE k, HoistableE k) => k n -> ESet k n
eSetSingleton k = eMapSingleton k UnitE

eSetToList :: ESet k n -> [k n]
eSetToList xs = map fst $ eMapToList xs

eSetFromList :: (AlphaEqE k, AlphaHashableE k, HoistableE k) => [k n] -> ESet k n
eSetFromList xs = eMapFromList $ zip xs (repeat UnitE)

lookupEMap :: (AlphaEqE k, HoistableE k, AlphaHashableE k)
           => EMap k v n -> k n -> Maybe (v n)
lookupEMap (EMap m) k = HM.lookup (EKey k) m

type ESet (k::E) = EMap k UnitE

instance (AlphaEqE k, AlphaHashableE k, HoistableE k)
         => Monoid (EMap k v n) where
  mempty = EMap mempty
  mappend = (<>)

instance (AlphaEqE k, AlphaHashableE k, HoistableE k)
         => Semigroup (EMap k v n) where
  -- right-biased instead of left-biased
  EMap x <> EMap y = EMap (y <> x)

instance (AlphaEqE k, AlphaHashableE k, HoistableE k)
         => GenericE (EMap k v) where
  type RepE (EMap k v) = ListE (PairE k v)
  fromE m = ListE $ map (uncurry PairE) $ eMapToList m
  toE (ListE pairs) = eMapFromList $ map fromPairE pairs

instance (AlphaEqE   k, AlphaHashableE k, HoistableE k, SubstE sv k, SubstE sv v) => SubstE sv (EMap k v)
instance (AlphaEqE   k, AlphaHashableE k, HoistableE k, SinkableE  k, SinkableE  v) => SinkableE  (EMap k v)
instance (AlphaEqE   k, AlphaHashableE k, HoistableE k, HoistableE v) => HoistableE (EMap k v)
instance (AlphaEqE   k, AlphaHashableE k, HoistableE k, AlphaEqE   v) => AlphaEqE   (EMap k v)
instance (HoistableE k, AlphaEqE k, AlphaHashableE k, Store (k n), Store (v n))
         => Store (EMap k v n)

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

liftScopeReaderT :: ScopeReader m' => ScopeReaderT m n a -> m' n (m a)
liftScopeReaderT m = do
  scope <- unsafeGetScope
  Distinct <- getDistinct
  return $ flip runReaderT (Distinct, scope) $ runScopeReaderT' m

liftScopeReaderM :: ScopeReader m' => ScopeReaderM n a -> m' n a
liftScopeReaderM m = liftM runIdentity $ liftScopeReaderT m

instance Monad m => ScopeReader (ScopeReaderT m) where
  getDistinct = ScopeReaderT $ asks fst
  unsafeGetScope = ScopeReaderT $ asks snd

instance Monad m => ScopeExtender (ScopeReaderT m) where
  refreshAbsScope ab cont = ScopeReaderT $ ReaderT
    \(Distinct, scope) -> refreshAbsPure scope ab
       \_ b e -> do
         let env' = extendOutMap scope $ toScopeFrag b
         runReaderT (runScopeReaderT' $ cont b e) (Distinct, env')

-- === SubstReaderT transformer ===

newtype SubstReaderT (v::V) (m::MonadKind1) (i::S) (o::S) (a:: *) =
  SubstReaderT { runSubstReaderT' :: ReaderT (Subst v i o) (m o) a }
  deriving (Functor, Applicative, Monad, MonadFail, Catchable, Fallible, CtxReader,
            Alternative)

type ScopedSubstReader (v::V) = SubstReaderT v (ScopeReaderT Identity) :: MonadKind2

liftSubstReaderT :: Monad1 m => m o a -> SubstReaderT v m i o a
liftSubstReaderT m = SubstReaderT $ lift m

runScopedSubstReader :: Distinct o => Scope o -> Subst v i o
                   -> ScopedSubstReader v i o a -> a
runScopedSubstReader scope env m =
  runIdentity $ runScopeReaderT scope $ runSubstReaderT env m

runSubstReaderT :: Subst v i o -> SubstReaderT v m i o a -> m o a
runSubstReaderT env m = runReaderT (runSubstReaderT' m) env

instance (SinkableV v, Monad1 m) => SubstReader v (SubstReaderT v m) where
  getSubst = SubstReaderT ask
  withSubst env (SubstReaderT cont) = SubstReaderT $ withReaderT (const env) cont

instance (SinkableV v, ScopeReader m) => ScopeReader (SubstReaderT v m i) where
  unsafeGetScope = SubstReaderT $ lift unsafeGetScope
  getDistinct = SubstReaderT $ lift getDistinct

instance (SinkableV v, ScopeReader m, ScopeExtender m)
         => ScopeExtender (SubstReaderT v m i) where
  refreshAbsScope ab cont = SubstReaderT $ ReaderT \env ->
    refreshAbsScope ab \b e -> do
      let SubstReaderT (ReaderT cont') = cont b e
      env' <- sinkM env
      cont' env'

instance (SinkableV v, MonadIO1 m) => MonadIO (SubstReaderT v m i o) where
  liftIO m = SubstReaderT $ lift $ liftIO m

instance (Monad1 m, MonadState (s o) (m o)) => MonadState (s o) (SubstReaderT v m i o) where
  state = SubstReaderT . lift . state

-- === OutReader monad: reads data in the output name space ===

class OutReader (e::E) (m::MonadKind1) | m -> e where
  askOutReader :: m n (e n)
  localOutReader :: e n -> m n a -> m n a

newtype OutReaderT (e::E) (m::MonadKind1) (n::S) (a :: *) =
  OutReaderT { runOutReaderT' :: ReaderT (e n) (m n) a }
  deriving (Functor, Applicative, Monad, MonadFail, Fallible)

runOutReaderT :: e n -> OutReaderT e m n a -> m n a
runOutReaderT env m = flip runReaderT env $ runOutReaderT' m

instance (SinkableE e, ScopeReader m)
         => ScopeReader (OutReaderT e m) where
  unsafeGetScope = OutReaderT $ lift unsafeGetScope
  getDistinct = OutReaderT $ lift getDistinct

instance (SinkableE e, ScopeExtender m)
         => ScopeExtender (OutReaderT e m) where
  refreshAbsScope ab cont = OutReaderT $ ReaderT \env ->
    refreshAbsScope ab \b e -> do
      let OutReaderT (ReaderT cont') = cont b e
      env' <- sinkM env
      cont' env'

instance Monad1 m => OutReader e (OutReaderT e m) where
  askOutReader = OutReaderT ask
  localOutReader r (OutReaderT m) = OutReaderT $ local (const r) m

instance OutReader e m => OutReader e (SubstReaderT v m i) where
  askOutReader = SubstReaderT $ ReaderT $ const askOutReader
  localOutReader e (SubstReaderT (ReaderT f)) = SubstReaderT $ ReaderT $ \env ->
    localOutReader e $ f env

instance MonadReader (r o) (m o) => MonadReader (r o) (SubstReaderT v m i o) where
  ask = SubstReaderT $ ReaderT $ const ask
  local r (SubstReaderT (ReaderT f)) = SubstReaderT $ ReaderT $ \env ->
    local r $ f env

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

-- === ZipSubstReaderT transformer ===

newtype ZipSubstReaderT (m::MonadKind1) (i1::S) (i2::S) (o::S) (a:: *) =
  ZipSubstReaderT { runZipSubstReaderT :: ReaderT (ZipSubst i1 i2 o) (m o) a }
  deriving (Functor, Applicative, Monad, Fallible, MonadFail)

type ZipSubst i1 i2 o = (Subst Name i1 o, Subst Name i2 o)

instance ScopeReader m => ScopeReader (ZipSubstReaderT m i1 i2) where
  unsafeGetScope = ZipSubstReaderT $ lift unsafeGetScope
  getDistinct = ZipSubstReaderT $ lift getDistinct

instance (ScopeReader m, ScopeExtender m)
         => ScopeExtender (ZipSubstReaderT m i1 i2) where
  refreshAbsScope ab cont =
    ZipSubstReaderT $ ReaderT \(env1, env2) -> do
      refreshAbsScope ab \b e -> do
        let ZipSubstReaderT (ReaderT cont') = cont b e
        env1' <- sinkM env1
        env2' <- sinkM env2
        cont' (env1', env2')

instance (Monad1 m, ScopeReader m, ScopeExtender m, Fallible1 m)
         => ZipSubstReader (ZipSubstReaderT m) where

  lookupZipSubstFst v = ZipSubstReaderT $ (!v) <$> fst <$> ask
  lookupZipSubstSnd v = ZipSubstReaderT $ (!v) <$> snd <$> ask

  extendZipSubstFst frag (ZipSubstReaderT cont) = ZipSubstReaderT $ withReaderT (onFst (<>>frag)) cont
  extendZipSubstSnd frag (ZipSubstReaderT cont) = ZipSubstReaderT $ withReaderT (onSnd (<>>frag)) cont

  withEmptyZipSubst (ZipSubstReaderT cont) =
    ZipSubstReaderT $ withReaderT (const (newSubst id, newSubst id)) cont

-- === in-place scope updating monad -- immutable fragment ===

data InplaceT (bindings::E) (decls::B) (m::MonadKind) (n::S) (a :: *) = UnsafeMakeInplaceT
  { unsafeRunInplaceT :: Distinct n => bindings n -> m (a, decls UnsafeS UnsafeS) }

runInplaceT
  :: (ExtOutMap b d, Monad m)
  => Distinct n
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
  => InplaceT b d m n (b n)
getOutMapInplaceT = UnsafeMakeInplaceT \bindings -> return (bindings, emptyOutFrag)

-- === in-place scope updating monad -- mutable stuff ===

-- This is intended to make it possible to implement `extendBindings` from
-- `BindingsReader`.
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
     (ExtOutMap b d, Monad m, SubstB Name d, SubstE Name e)
  => Mut n => Abs d e n -> InplaceT b d m n (e n)
extendInplaceT ab = do
  UnsafeMakeInplaceT \env ->
    refreshAbsPure (toScope env) ab \_ decls result ->
      return (unsafeCoerceE result, unsafeCoerceB decls)

locallyMutableInplaceT
  :: forall m b d n e.
     (ExtOutMap b d, Monad m, SinkableE e)
  => (forall l. (Mut l, DExt n l) => InplaceT b d m l (e l))
  -> InplaceT b d m n (Abs d e n)
locallyMutableInplaceT cont = do
  UnsafeMakeInplaceT \bindings -> do
    (e, decls) <- withMutEvidence (fabricateMutEvidence :: MutEvidence n) do
                    unsafeRunInplaceT cont bindings
    return (Abs (unsafeCoerceB decls) e, emptyOutFrag)

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

-- === InplaceT instances ===

instance (ExtOutMap bindings decls, BindsNames decls, SinkableB decls, Monad m)
         => Functor (InplaceT bindings decls m n) where
  fmap = liftM

instance (ExtOutMap bindings decls, BindsNames decls, SinkableB decls, Monad m)
         => Applicative (InplaceT bindings decls m n) where
  pure = return
  liftA2 = liftM2

instance (ExtOutMap bindings decls, BindsNames decls, SinkableB decls, Monad m)
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

instance (ExtOutMap bindings decls, BindsNames decls, SinkableB decls, Monad m)
         => ScopeReader (InplaceT bindings decls m) where
  getDistinct = UnsafeMakeInplaceT \_ ->
    return (Distinct, emptyOutFrag)
  unsafeGetScope = toScope <$> getOutMapInplaceT

instance (ExtOutMap bindings decls, BindsNames decls, SinkableB decls, Monad m, MonadFail m)
         => MonadFail (InplaceT bindings decls m n) where
  fail s = lift1 $ fail s

instance (ExtOutMap bindings decls, BindsNames decls, SinkableB decls, Monad m, Fallible m)
         => Fallible (InplaceT bindings decls m n) where
  throwErrs errs = UnsafeMakeInplaceT \_ -> throwErrs errs
  addErrCtx ctx cont = UnsafeMakeInplaceT \bindings ->
    addErrCtx ctx $ unsafeRunInplaceT cont bindings

instance (ExtOutMap bindings decls, BindsNames decls, SinkableB decls, Monad m, CtxReader m)
         => CtxReader (InplaceT bindings decls m n) where
  getErrCtx = lift1 getErrCtx

instance ( ExtOutMap bindings decls, BindsNames decls, SinkableB decls, Monad m
         , Alternative m)
         => Alternative (InplaceT bindings decls m n) where
  empty = lift1 empty
  UnsafeMakeInplaceT f1 <|> UnsafeMakeInplaceT f2 = UnsafeMakeInplaceT \bindings ->
    f1 bindings <|> f2 bindings

instance ( ExtOutMap bindings decls, BindsNames decls, SinkableB decls,
           Monad m, Alternative m, Searcher m)
         => Searcher (InplaceT bindings decls m n) where
  UnsafeMakeInplaceT f1 <!> UnsafeMakeInplaceT f2 = UnsafeMakeInplaceT \bindings ->
    f1 bindings <!> f2 bindings

instance ( ExtOutMap bindings decls, BindsNames decls, SinkableB decls,
           Catchable m)
         => Catchable (InplaceT bindings decls m n) where
  catchErr (UnsafeMakeInplaceT f1) handler = UnsafeMakeInplaceT \bindings ->
    f1 bindings `catchErr` \err -> case handler err of
      UnsafeMakeInplaceT f2 -> f2 bindings

instance ( ExtOutMap bindings decls, BindsNames decls, SinkableB decls
         , MonadWriter w m)
         => MonadWriter w (InplaceT bindings decls m n) where
  tell w = lift1 $ tell w
  listen = undefined
  pass = undefined

instance ( ExtOutMap bindings decls, BindsNames decls, SinkableB decls
         , MonadState s m)
         => MonadState s (InplaceT bindings decls m n) where
  state f = lift1 $ state f

instance (ExtOutMap bindings decls, BindsNames decls, SinkableB decls)
         => MonadTrans1 (InplaceT bindings decls) where
  lift1 m = UnsafeMakeInplaceT \_ -> (,emptyOutFrag) <$> m

instance ( ExtOutMap bindings decls, BindsNames decls, SinkableB decls
         , MonadReader r m)
         => MonadReader r (InplaceT bindings decls m n) where
  ask = lift1 $ ask
  local f (UnsafeMakeInplaceT cont) =
    UnsafeMakeInplaceT \bindings -> local f (cont bindings)

instance ( ExtOutMap bindings decls, BindsNames decls, SinkableB decls
         , MonadIO m)
         => MonadIO (InplaceT bindings decls m n) where
  liftIO = lift1 . liftIO

-- === name hints ===

class HasNameHint a where
  getNameHint :: a -> NameHint

instance HasNameHint RawName where
  getNameHint (RawName s _) = Hint s

instance HasNameHint String where
  getNameHint = fromString

instance HasNameHint a => HasNameHint (Maybe a) where
  getNameHint (Just x) = getNameHint x
  getNameHint (Nothing) = NoHint

instance Color c => HasNameHint (BinderP c ann n l) where
  getNameHint (b:>_) = getNameHint b

-- === handling the dynamic/heterogeneous stuff for Subst ===

data ColorProxy (c::C) = ColorProxy

data ColorsEqual (c1::C) (c2::C) where
  ColorsEqual :: ColorsEqual c c

eqColorRep :: forall c1 c2. (Color c1, Color c2) => Maybe (ColorsEqual c1 c2)
eqColorRep = if c1Rep == c2Rep
 then Just (TrulyUnsafe.unsafeCoerce (ColorsEqual :: ColorsEqual c1 c1) :: ColorsEqual c1 c2)
 else Nothing
 where c1Rep = getColorRep (ColorProxy :: ColorProxy c1)
       c2Rep = getColorRep (ColorProxy :: ColorProxy c2)

data WithColor (v::V) (n::S) where
  WithColor :: Color c => v c n -> WithColor v n

-- like Typeable, this gives a term-level representation of a name color
class Color (c::C) where
  getColorRep :: ColorProxy c -> C

instance Color AtomNameC       where getColorRep _ = AtomNameC
instance Color DataDefNameC    where getColorRep _ = DataDefNameC
instance Color TyConNameC      where getColorRep _ = TyConNameC
instance Color DataConNameC    where getColorRep _ = DataConNameC
instance Color ClassNameC      where getColorRep _ = ClassNameC
instance Color SuperclassNameC where getColorRep _ = SuperclassNameC
instance Color MethodNameC     where getColorRep _ = MethodNameC
instance Color ImpFunNameC     where getColorRep _ = ImpFunNameC
instance Color ObjectFileNameC where getColorRep _ = ObjectFileNameC
instance Color ModuleNameC     where getColorRep _ = ModuleNameC
instance Color PtrNameC        where getColorRep _ = ModuleNameC

interpretColor :: C -> WithColor UnitV VoidS
interpretColor c = case c of
  AtomNameC       -> WithColor (UnitV :: UnitV AtomNameC       VoidS)
  DataDefNameC    -> WithColor (UnitV :: UnitV DataDefNameC    VoidS)
  TyConNameC      -> WithColor (UnitV :: UnitV TyConNameC      VoidS)
  DataConNameC    -> WithColor (UnitV :: UnitV DataConNameC    VoidS)
  ClassNameC      -> WithColor (UnitV :: UnitV ClassNameC      VoidS)
  SuperclassNameC -> WithColor (UnitV :: UnitV SuperclassNameC VoidS)
  MethodNameC     -> WithColor (UnitV :: UnitV MethodNameC     VoidS)
  ImpFunNameC     -> WithColor (UnitV :: UnitV ImpFunNameC     VoidS)
  ObjectFileNameC -> WithColor (UnitV :: UnitV ObjectFileNameC VoidS)
  ModuleNameC     -> WithColor (UnitV :: UnitV ModuleNameC     VoidS)
  PtrNameC        -> WithColor (UnitV :: UnitV PtrNameC        VoidS)

deriving instance (forall c. Show (v c n)) => Show (WithColor v n)

fromWithColor ::  forall c v o. Color c => WithColor v o -> Maybe (v c o)
fromWithColor (WithColor (val :: v c' o)) =
  case eqColorRep of
    Just (ColorsEqual :: ColorsEqual c c') -> Just val
    _ -> Nothing

tryAsColor :: forall (v::V) (c1::C) (c2::C) (n::S).
              (Color c1, Color c2) => v c1 n -> Maybe (v c2 n)
tryAsColor x = case eqColorRep of
  Just (ColorsEqual :: ColorsEqual c1 c2) -> Just x
  Nothing -> Nothing

-- === instances ===

instance SinkableV v => SinkableE (Subst v i) where
  sinkingProofE fresh (Subst f m) =
    Subst (\name -> sinkingProofE fresh $ f name)
          (sinkingProofE fresh m)

instance SinkableE atom => SinkableV (SubstVal (cMatch::C) (atom::E))
instance SinkableE atom => SinkableE (SubstVal (cMatch::C) (atom::E) (c::C)) where
  sinkingProofE fresh substVal = case substVal of
    Rename name  -> Rename   $ sinkingProofE fresh name
    SubstVal val -> SubstVal $ sinkingProofE fresh val

instance (SinkableB b, SinkableE e) => SinkableE (Abs b e) where
  sinkingProofE fresh (Abs b body) =
    sinkingProofB fresh b \fresh' b' ->
      Abs b' (sinkingProofE fresh' body)

instance (HoistableB b, HoistableE e) => HoistableE (Abs b e) where
  freeVarsE (Abs b e) = freeVarsB b <> hoistNameSet b (freeVarsE e)

instance (SubstB v b, SubstE v e) => SubstE v (Abs b e) where
  substE env (Abs b body) = do
    substB env b \env' b' -> Abs b' $ substE env' body

instance (BindsNames b1, BindsNames b2) => ProvesExt  (PairB b1 b2) where
instance (BindsNames b1, BindsNames b2) => BindsNames (PairB b1 b2) where
  toScopeFrag (PairB b1 b2) = toScopeFrag b1 >>> toScopeFrag b2

instance (SinkableB b1, SinkableB b2) => SinkableB (PairB b1 b2) where
  sinkingProofB fresh (PairB b1 b2) cont =
    sinkingProofB fresh b1 \fresh' b1' ->
      sinkingProofB fresh' b2 \fresh'' b2' ->
        cont fresh'' (PairB b1' b2')

instance ( BindsNames b1, SubstB v b1
         , BindsNames b2, SubstB v b2
         , SinkableV v, FromName v)
         => SubstB v (PairB b1 b2) where
  substB env (PairB b1 b2) cont =
    substB env b1 \env' b1' ->
      substB env' b2 \env'' b2' ->
        cont env'' $ PairB b1' b2'

instance SinkableE e => SinkableB (LiftB e) where
  sinkingProofB fresh (LiftB e) cont = cont fresh $ LiftB $ sinkingProofE fresh e

instance ProvesExt (LiftB e) where
instance BindsNames (LiftB e) where
  toScopeFrag (LiftB _) = id

instance HoistableE e => HoistableB (LiftB e) where
  freeVarsB (LiftB e) = freeVarsE e

instance (SinkableE e, SubstE v e) => SubstB v (LiftB e) where
  substB env (LiftB e) cont = cont env $ LiftB $ substE env e

instance (BindsNames b1, BindsNames b2) => ProvesExt  (EitherB b1 b2) where
instance (BindsNames b1, BindsNames b2) => BindsNames (EitherB b1 b2) where
  toScopeFrag (LeftB  b) = toScopeFrag b
  toScopeFrag (RightB b) = toScopeFrag b

instance (HoistableB b1, HoistableB b2) => HoistableB (EitherB b1 b2) where
  freeVarsB (LeftB  b) = freeVarsB b
  freeVarsB (RightB b) = freeVarsB b

instance (SinkableB b1, SinkableB b2) => SinkableB (EitherB b1 b2) where
  sinkingProofB fresh (LeftB b) cont =
    sinkingProofB fresh b \fresh' b' ->
      cont fresh' (LeftB b')
  sinkingProofB fresh (RightB b) cont =
    sinkingProofB fresh b \fresh' b' ->
      cont fresh' (RightB b')

instance (SubstB v b1, SubstB v b2) => SubstB v (EitherB b1 b2) where
  substB env (LeftB b) cont =
    substB env b \env' b' ->
      cont env' $ LeftB b'
  substB env (RightB b) cont =
    substB env b \env' b' ->
      cont env' $ RightB b'

instance GenericB (BinderP c ann) where
  type RepB (BinderP c ann) = PairB (LiftB ann) (NameBinder c)
  fromB (b:>ann) = PairB (LiftB ann) b
  toB   (PairB (LiftB ann) b) = b:>ann

instance (Color c, SinkableE ann) => SinkableB (BinderP c ann)
instance (Color c, SinkableE ann, SubstE v ann, SinkableV v) => SubstB v (BinderP c ann)
instance Color c => ProvesExt  (BinderP c ann)
instance Color c => BindsNames (BinderP c ann)

instance BindsNames b => ProvesExt  (Nest b) where
instance BindsNames b => BindsNames (Nest b) where
  toScopeFrag Empty = id
  toScopeFrag (Nest b rest) = toScopeFrag b >>> toScopeFrag rest

instance (BindsNames b, SubstB v b, SinkableV v)
         => SubstB v (Nest b) where
  substB env (Nest b bs) cont =
    substB env b \env' b' ->
      substB env' bs \env'' bs' ->
        cont env'' $ Nest b' bs'
  substB env Empty cont = cont env Empty

instance SinkableE UnitE where
  sinkingProofE _ UnitE = UnitE

instance HoistableE UnitE where
  freeVarsE UnitE = mempty

instance FromName v => SubstE v UnitE where
  substE _ UnitE = UnitE

instance (Functor f, SinkableE e) => SinkableE (ComposeE f e) where
  sinkingProofE fresh (ComposeE xs) = ComposeE $ fmap (sinkingProofE fresh) xs

instance (Traversable f, HoistableE e) => HoistableE (ComposeE f e) where
  freeVarsE (ComposeE xs) = foldMap freeVarsE xs

instance (Traversable f, SubstE v e) => SubstE v (ComposeE f e) where
  substE env (ComposeE xs) = ComposeE $ fmap (substE env) xs

-- alternatively we could use Zippable, but we'd want to be able to derive it
-- (e.g. via generic) for the many-armed cases like PrimOp.
instance (Traversable f, Eq (f ()), AlphaEq e) => AlphaEqE (ComposeE f e) where
  alphaEqE (ComposeE xs) (ComposeE ys) = alphaEqTraversable xs ys

instance (Foldable f, Functor f, Hashable (f ()), AlphaHashableE e)
         => AlphaHashableE (ComposeE f e) where
  hashWithSaltE env salt (ComposeE xs) = do
    let h = hashWithSalt salt $ void xs
    foldl (hashWithSaltE env) h xs

instance SinkableB UnitB where
  sinkingProofB fresh UnitB cont = cont fresh UnitB

instance ProvesExt  UnitB where
instance BindsNames UnitB where
  toScopeFrag UnitB = id

instance FromName v => SubstB v UnitB where
  substB env UnitB cont = cont env UnitB

instance SinkableB VoidB where
  sinkingProofB _ _ _ = error "impossible"

instance ProvesExt VoidB where
instance BindsNames VoidB where
  toScopeFrag _ = error "impossible"

instance HoistableB VoidB where
  freeVarsB _ = error "impossible"

instance AlphaEqB VoidB where
  withAlphaEqB _ _ _ = error "impossible"

instance FromName v => SubstB v VoidB where
  substB _ _ _ = error "impossible"

instance SinkableE const => SinkableV (ConstE const)
instance SinkableE const => SinkableE (ConstE const ignored) where
  sinkingProofE fresh (ConstE e) = ConstE $ sinkingProofE fresh e

instance SinkableE VoidE where
  sinkingProofE _ _ = error "impossible"

instance HoistableE VoidE where
  freeVarsE _ = error "impossible"

instance AlphaEqE VoidE where
  alphaEqE _ _ = error "impossible"

instance FromName v => SubstE v VoidE where
  substE _ _ = error "impossible"

instance (SinkableE e1, SinkableE e2) => SinkableE (PairE e1 e2) where
  sinkingProofE fresh (PairE e1 e2) =
    PairE (sinkingProofE fresh e1) (sinkingProofE fresh e2)

instance (HoistableE e1, HoistableE e2) => HoistableE (PairE e1 e2) where
  freeVarsE (PairE e1 e2) = freeVarsE e1 <> freeVarsE e2

instance (SubstE v e1, SubstE v e2) => SubstE v (PairE e1 e2) where
  substE env (PairE x y) = PairE (substE env x) (substE env y)

instance (SinkableE e1, SinkableE e2) => SinkableE (EitherE e1 e2) where
  sinkingProofE fresh (LeftE  e) = LeftE  (sinkingProofE fresh e)
  sinkingProofE fresh (RightE e) = RightE (sinkingProofE fresh e)

instance (HoistableE e1, HoistableE e2) => HoistableE (EitherE e1 e2) where
  freeVarsE (LeftE  e) = freeVarsE e
  freeVarsE (RightE e) = freeVarsE e

instance (SubstE v e1, SubstE v e2) => SubstE v (EitherE e1 e2) where
  substE env (LeftE  x) = LeftE  $ substE env x
  substE env (RightE x) = RightE $ substE env x

instance (SinkableE k, SinkableE v, OrdE k) => SinkableE (MapE k v) where
  sinkingProofE fresh (MapE m) = MapE $ M.fromList newItems
    where
      itemsE = ListE $ toPairE <$> M.toList m
      newItems = fromPairE <$> (fromListE $ sinkingProofE fresh itemsE)

instance SinkableE e => SinkableE (ListE e) where
  sinkingProofE fresh (ListE xs) = ListE $ map (sinkingProofE fresh) xs

instance SinkableE e => SinkableE (NonEmptyListE e) where
  sinkingProofE fresh (NonEmptyListE xs) = NonEmptyListE $ fmap (sinkingProofE fresh) xs

instance AlphaEqE e => AlphaEqE (ListE e) where
  alphaEqE (ListE xs) (ListE ys)
    | length xs == length ys = mapM_ (uncurry alphaEqE) (zip xs ys)
    | otherwise              = zipErr

instance Monoid (ListE e n) where
  mempty = ListE []

instance Semigroup (ListE e n) where
  ListE xs <> ListE ys = ListE $ xs <> ys

instance (EqE k, HashableE k) => GenericE (HashMapE k v) where
  type RepE (HashMapE k v) = ListE (PairE k v)
  fromE (HashMapE m) = ListE $ map (uncurry PairE) $ HM.toList m
  toE   (ListE pairs) = HashMapE $ HM.fromList $ map fromPairE pairs
instance (EqE k, HashableE k, SinkableE k  , SinkableE   v) => SinkableE   (HashMapE k v)
instance (EqE k, HashableE k, HoistableE k , HoistableE  v) => HoistableE  (HashMapE k v)
instance (EqE k, HashableE k, SubstE Name k, SubstE Name v) => SubstE Name (HashMapE k v)

instance SinkableE (LiftE a) where
  sinkingProofE _ (LiftE x) = LiftE x

instance HoistableE (LiftE a) where
  freeVarsE (LiftE _) = mempty

instance FromName v => SubstE v (LiftE a) where
  substE _ (LiftE x) = LiftE x

instance Eq a => AlphaEqE (LiftE a) where
  alphaEqE (LiftE x) (LiftE y) = unless (x == y) zipErr

instance SubstE v e => SubstE v (ListE e) where
  substE env (ListE xs) = ListE $ map (substE env) xs

instance SubstE v e => SubstE v (NonEmptyListE e) where
  substE env (NonEmptyListE xs) = NonEmptyListE $ fmap (substE env) xs

instance (PrettyB b, PrettyE e) => Pretty (Abs b e n) where
  pretty (Abs b body) = "(Abs " <> pretty b <> " " <> pretty body <> ")"

instance Pretty a => Pretty (LiftE a n) where
  pretty (LiftE x) = pretty x

instance Pretty (UnitE n) where
  pretty UnitE = ""

instance (PrettyE e1, PrettyE e2) => Pretty (PairE e1 e2 n) where
  pretty (PairE e1 e2) = pretty (e1, e2)

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

instance ProvesExt  (RecSubstFrag v) where
instance BindsNames (RecSubstFrag v) where
  toScopeFrag env = envFragAsScope $ fromRecSubstFrag env
instance HoistableV v => HoistableB (RecSubstFrag v) where
  freeVarsB (RecSubstFrag env) = freeVarsE (Abs (envFragAsScope env) env)

-- Traversing a recursive set of bindings is a bit tricky because we have to do
-- two passes: first we rename the binders, then we go and subst the payloads.
instance (SinkableV substVal, SubstV substVal v) => SubstB substVal (RecSubstFrag v) where
  substB env (RecSubstFrag recSubst) cont = do
    let pairs = toSubstPairs recSubst
    renameSubstPairBinders env pairs \env' pairs' -> do
      let pairs'' = forEachNestItem pairs' \(SubstPair b x) ->
                      SubstPair b $ substE env' x
      cont env' $ RecSubstFrag $ fromSubstPairs pairs''

renameSubstPairBinders
  :: (Distinct o, SinkableV v, SinkableV substVal, FromName substVal)
  => (Scope o, Subst substVal i o)
  -> Nest (SubstPair v ignored) i i'
  -> (forall o'.
         Distinct o'
      => (Scope o', Subst substVal i' o')
      -> Nest (SubstPair v ignored) o o'
      -> a)
  -> a
renameSubstPairBinders env Empty cont = cont env Empty
renameSubstPairBinders env (Nest (SubstPair b v) rest) cont =
  substB env b \env' b' ->
    renameSubstPairBinders env' rest \env'' rest' ->
      cont env'' (Nest (SubstPair b' v) rest')

instance SinkableV v => SinkableB (RecSubstFrag v) where
  sinkingProofB _ _ _ = todoSinkableProof

instance SubstV substVal v => SubstE substVal (WithColor v) where
  substE env (WithColor v) = WithColor $ substE env v

instance HoistableV v => HoistableE (WithColor v) where
  freeVarsE (WithColor v) = freeVarsE v

instance Store C
instance Store RawName
instance Store (UnitE n)
instance Store (VoidE n)
instance (Store (e1 n), Store (e2 n)) => Store (PairE   e1 e2 n)
instance (Store (e1 n), Store (e2 n)) => Store (EitherE e1 e2 n)
instance Store (e n) => Store (ListE  e n)
instance Store a => Store (LiftE a n)
instance (Store (e UnsafeS), Generic (e UnsafeS)) => Store (LiftB e n l)
instance Store (const n) => Store (ConstE const ignored n)
instance (Color c, Store (ann n)) => Store (BinderP c ann n l)

instance ( forall c. Color c => Store (v c o')
         , forall c. Color c => Generic (v c o'))
         => Store (RecSubstFrag v o o')

instance ( forall c. Color c => Store (v c o)
         , forall c. Color c => Generic (v c o))
         => Store (RecSubst v o)
instance Store (ScopeFrag n l)
instance Store (Scope n)
deriving instance (forall c n. Pretty (v c n)) => Pretty (RecSubstFrag v o o')


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
  | ImpFunNameC
  | ObjectFileNameC
  | ModuleNameC
  | PtrNameC
    deriving (Eq, Ord, Generic)

type E = S -> *       -- expression-y things, covariant in the S param
type B = S -> S -> *  -- binder-y things, covariant in the first param and
                      -- contravariant in the second. These are things like
                      -- `Binder n l` or `Decl n l`, that bind the names in
                      -- `ScopeFrag n l`, extending `n` to `l`. Their free
                      -- name are in `Scope n`. We sometimes call `n` the
                      -- "outside scope" and "l" the "inside scope".
type V = C -> E       -- value-y things that we might look up in an environment
                      -- with a `Name c n`, parameterized by the name's color.

type ColorRep = WithColor UnitV UnsafeS
type NameSet (n::S) = M.Map RawName ColorRep

newtype ScopeFrag (n::S) (l::S) = UnsafeMakeScopeFrag (M.Map RawName [ColorRep]) deriving Generic
newtype Scope (n::S) = Scope { fromScope :: ScopeFrag VoidS n }  deriving Generic

instance Category ScopeFrag where
  id = UnsafeMakeScopeFrag mempty
  UnsafeMakeScopeFrag s2 . UnsafeMakeScopeFrag s1 =
    -- Flipped because the innermost names are at the left (head) of the list.
    -- But also flipped the other way because `(.)` is not like `(>>>)`.
    -- Hope we got that right!
    UnsafeMakeScopeFrag $ M.unionWith (++) s2 s1

instance Color c => BindsNames (NameBinder c) where
  toScopeFrag (UnsafeMakeBinder v) =
    UnsafeMakeScopeFrag $ M.singleton v [WithColor (UnitV :: UnitV c UnsafeS)]

absurdNameFunction :: Name v VoidS -> a
absurdNameFunction _ = error "Void names shouldn't exist"

scopeFragToSubstFrag :: ScopeFrag n l -> SubstFrag (ConstE UnitE) n l VoidS
scopeFragToSubstFrag (UnsafeMakeScopeFrag m) =
  unsafeCoerceE $ UnsafeMakeSubst m

type NameText = T.Text
data RawName = RawName !NameText !Int deriving (Show, Eq, Ord, Generic)

newtype Name (c::C)  -- Name color
             (n::S)  -- Scope parameter
  = UnsafeMakeName RawName
    deriving (Show, Eq, Ord, Pretty, HasNameHint, Generic, Store)

newtype NameBinder (c::C)  -- name color
                   (n::S)  -- scope above the binder
                   (l::S)  -- scope under the binder (`l` for "local")
  = UnsafeMakeBinder RawName
    deriving (Show, Pretty, HasNameHint, Generic, Store)

data NameHint = Hint NameText
              | NoHint

instance IsString NameHint where
  fromString s = Hint $ fromString s

newBinder :: Color c => NameHint -> (forall l. NameBinder c VoidS l -> a) -> a
newBinder hint cont =
  cont $ UnsafeMakeBinder $ RawName (interpretHint hint) 0

-- Closed binder-name pair. The name isn't fresh and it doesn't pretend to be.
-- It's intended for subsequent refreshing.
newName :: Color c => NameHint -> Abs (NameBinder c) (Name c) n
newName hint = sinkFromTop $ newBinder hint \b -> Abs b $ binderName b

-- uses the monad just to diambiguate the scope parameter
newNameM :: Monad1 m => Color c => NameHint -> m n (Abs (NameBinder c) (Name c) n)
newNameM hint = return $ newName hint

newNames :: Color c => [NameHint] -> Abs (Nest (NameBinder c)) (ListE (Name c)) n
newNames hints = do
  let rawNames =  [RawName (interpretHint hint) i | (i, hint) <- zip [0..] hints]
  let vs = map UnsafeMakeName rawNames
  let bs = unsafeListToNest $ map UnsafeMakeBinder rawNames
  unsafeCoerceE $ Abs bs $ ListE vs

newNamesM :: Monad1 m => Color c => [NameHint]
          -> m n (Abs (Nest (NameBinder c)) (ListE (Name c)) n)
newNamesM hints = return $ newNames hints

withFresh :: forall n c a. (Distinct n, Color c)
          => NameHint -> Scope n
          -> (forall l. DExt n l => NameBinder c n l -> a) -> a
withFresh hint (Scope (UnsafeMakeScopeFrag scope)) cont =
  withDistinctEvidence (fabricateDistinctEvidence :: DistinctEvidence UnsafeS) $
    withExtEvidence' (FabricateExtEvidence :: ExtEvidence n UnsafeS) $
      cont $ (UnsafeMakeBinder (freshRawName hint scope) :: NameBinder c n UnsafeS)

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
    tag = interpretHint hint

interpretHint :: NameHint -> NameText
interpretHint hint = case hint of
  Hint v -> v
  NoHint -> "v"

projectName :: ScopeFrag n l -> Name s l -> Either (Name s n) (Name s (n:=>:l))
projectName (UnsafeMakeScopeFrag scope) (UnsafeMakeName rawName)
  | M.member rawName scope = Right $ UnsafeMakeName rawName
  | otherwise              = Left  $ UnsafeMakeName rawName

-- proves that the names in n are distinct
class Distinct (n::S)
type DExt n l = (Distinct l, Ext n l)

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
getRawName (UnsafeMakeName rawName) = rawName

-- === sinkings ===

-- Note [Sinkings]

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

sink :: (SinkableE e, DExt n l) => e n -> e l
sink x = unsafeCoerceE x

sinkR :: SinkableE e => e (n:=>:l) -> e l
sinkR = unsafeCoerceE

sinkList :: (SinkableE e, DExt n l) => [e n] -> [e l]
sinkList = fromListE . sink . ListE

class SinkableE (e::E) where
  sinkingProofE :: SinkingCoercion n l -> e n -> e l

  default sinkingProofE :: (GenericE e, SinkableE (RepE e))
                          => SinkingCoercion n l -> e n -> e l
  sinkingProofE free x = toE $ sinkingProofE free $ fromE x

class SinkableB (b::B) where
  sinkingProofB :: SinkingCoercion n n' -> b n l
                  -> (forall l'. SinkingCoercion l l' -> b n' l' -> a)
                  -> a
  default sinkingProofB :: (GenericB b, SinkableB (RepB b))
                          => SinkingCoercion n n' -> b n l
                          -> (forall l'. SinkingCoercion l l' -> b n' l' -> a)
                          -> a
  sinkingProofB fresh b cont =
    sinkingProofB fresh (fromB b) \fresh' b' -> cont fresh' $ toB b'

-- previously we just had the alias
-- `type SinkableV v = forall c. Color c => SinkableE (v c)`
-- but GHC seemed to have trouble figuring out superclasses etc. so
-- we're making it an explicit class instead
class (forall c. Color c => SinkableE (v c))
      => SinkableV (v::V)

class (forall c. Color c => HoistableE (v c))
      => HoistableV (v::V)

data SinkingCoercion (n::S) (l::S) where
  SinkingCoercion :: (forall s. Name s n -> Name s l) -> SinkingCoercion n l

instance SinkableV Name
instance HoistableV  Name

instance SinkableE (Name c) where
  sinkingProofE (SinkingCoercion f) name = f name

-- This is the unsafely-implemented base case. Here's why it's valid. Let's say
-- the name of the binder is x. The scopes are related like this:
--   l  = n  ++ [x]
--   l' = n' ++ [x]
-- We're given an sinking from n to n' and we want to produce an sinking
-- from l to l'. Any name in l must be either:
--   (1) x itself, in which case it's also in l'
--   (2) in n, in which case it can be sinked to n'. The only issue would be
--       if it were shadowed by x, but it can't be because then we'd be in case (1).
instance SinkableB (NameBinder s) where
  sinkingProofB  _ (UnsafeMakeBinder b) cont =
    cont (SinkingCoercion unsafeCoerceE) (UnsafeMakeBinder b)

instance SinkableE DistinctEvidence where
  sinkingProofE _ _ = fabricateDistinctEvidence

instance SinkableE (ExtEvidence n) where
  sinkingProofE _ _ = FabricateExtEvidence

-- === projections ===

unsafeCoerceNameSet :: NameSet n -> NameSet l
unsafeCoerceNameSet = TrulyUnsafe.unsafeCoerce

-- XXX: we need another constraint analogous to `SinkableE`, which says that
--      we can do the actual hoisting by coercion. But we can't use
--      `SinkableE` itself because `Distinct` can't implement it. For now,
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

data ClosedWithScope (e::E) where
  ClosedWithScope :: Distinct n => Scope n -> e n -> ClosedWithScope e

withScopeFromFreeVars :: HoistableE e => e n -> ClosedWithScope e
withScopeFromFreeVars e =
  withDistinctEvidence (fabricateDistinctEvidence :: DistinctEvidence UnsafeS) $
    ClosedWithScope scope $ unsafeCoerceE e
  where scope = (Scope $ UnsafeMakeScopeFrag $ M.map (:[]) $ freeVarsE e) :: Scope UnsafeS

-- This renames internal binders in a way that doesn't depend on any extra
-- context. The resuling binder names are arbitrary (we make no promises!) but
-- at least they're deterministic.
canonicalizeForPrinting
  :: (HoistableE e, SubstE Name e) => e n -> (forall l. e l -> a) -> a
canonicalizeForPrinting e cont =
  case withScopeFromFreeVars e of
    ClosedWithScope scope e' ->
      cont $ fmapNames scope id e'

liftHoistExcept :: Fallible m => HoistExcept a -> m a
liftHoistExcept (HoistSuccess x) = return x
liftHoistExcept (HoistFailure vs) = throw EscapedNameErr (pprint vs)

ignoreHoistFailure :: HasCallStack => HoistExcept a -> a
ignoreHoistFailure (HoistSuccess x) = x
ignoreHoistFailure (HoistFailure _) = error "hoist failure"

hoist :: (BindsNames b, HoistableE e) => b n l -> e l -> HoistExcept (e n)
hoist b e =
  case nameSetRawNames $ M.intersection (freeVarsE e) frag of
    []          -> HoistSuccess $ unsafeCoerceE e
    leakedNames -> HoistFailure leakedNames
  where UnsafeMakeScopeFrag frag = toScopeFrag b

hoistToTop :: HoistableE e => e n -> HoistExcept (e VoidS)
hoistToTop e =
  case nameSetRawNames $ freeVarsE e of
    []          -> HoistSuccess $ unsafeCoerceE e
    leakedNames -> HoistFailure leakedNames

sinkFromTop :: SinkableE e => e VoidS -> e n
sinkFromTop = unsafeCoerceE

freeVarsList :: (HoistableE e, Color c) => e n -> [Name c n]
freeVarsList e = nameSetToList $ freeVarsE e

nameSetToList :: forall c n. Color c => NameSet n -> [Name c n]
nameSetToList nameSet =
  catMaybes $ flip map (M.toList nameSet) \(rawName, withColor) ->
    case fromWithColor withColor of
      Nothing -> Nothing
      Just (ConstE UnitE :: UnitV c UnsafeS)-> Just $ UnsafeMakeName rawName

toNameSet :: ScopeFrag n l -> NameSet l
toNameSet (UnsafeMakeScopeFrag s) = M.map head s

nameSetRawNames :: NameSet n -> [RawName]
nameSetRawNames m = M.keys m

isFreeIn :: HoistableE e => Name c n -> e n -> Bool
isFreeIn v e = getRawName v `M.member` freeVarsE e

areFreeIn :: HoistableE e => [Name c n] -> e n -> Bool
areFreeIn vs e =
  not $ null $ S.intersection (S.fromList $ map getRawName vs)
                              (M.keysSet $ freeVarsE e)

exchangeBs :: (Distinct l, BindsNames b1, SinkableB b1, HoistableB b2)
              => PairB b1 b2 n l
              -> HoistExcept (PairB b2 b1 n l)
exchangeBs (PairB b1 b2) =
  case nameSetRawNames $ M.intersection (freeVarsB b2) frag  of
    []          -> HoistSuccess $ PairB (unsafeCoerceB b2) (unsafeCoerceB b1)
    leakedNames -> HoistFailure leakedNames
  where UnsafeMakeScopeFrag frag = toScopeFrag b1

hoistNameSet :: BindsNames b => b n l -> NameSet l -> NameSet n
hoistNameSet b nameSet =
  unsafeCoerceNameSet $ nameSet `M.difference` frag
  where UnsafeMakeScopeFrag frag = toScopeFrag b

abstractFreeVar :: Name c n -> e n -> Abs (NameBinder c) e n
abstractFreeVar v e =
  case abstractFreeVarsNoAnn [v] e of
    Abs (Nest b Empty) e' -> Abs b e'
    _ -> error "impossible"

abstractFreeVars :: [(Name c n, ann n)]
                 -> e n -> Abs (Nest (BinderP c ann)) e n
abstractFreeVars vs e = Abs bs e
  where bs = unsafeCoerceB $ unsafeListToNest bsFlat
        bsFlat = vs <&> \(UnsafeMakeName v, ann) ->
          UnsafeMakeBinder v :> unsafeCoerceE ann

abstractFreeVarsNoAnn :: [Name c n] -> e n -> Abs (Nest (NameBinder c)) e n
abstractFreeVarsNoAnn vs e =
  case abstractFreeVars (zip vs (repeat UnitE)) e of
    Abs bs e' -> Abs bs' e'
      where bs' = fmapNest (\(b:>UnitE) -> b) bs

instance Color c => HoistableB (NameBinder c) where
  freeVarsB _ = mempty

instance Color c => HoistableE (Name c) where
  freeVarsE name =
    M.singleton (getRawName name) (WithColor (UnitV :: UnitV c UnsafeS))

instance (HoistableB b1, HoistableB b2) => HoistableB (PairB b1 b2) where
  freeVarsB (PairB b1 b2) =
    freeVarsB b1 <> hoistNameSet b1 (freeVarsB b2)

instance (Color c, HoistableE ann) => HoistableB (BinderP c ann) where
  freeVarsB (b:>ann) = freeVarsB b <> freeVarsE ann

instance HoistableB UnitB where
  freeVarsB = mempty

instance HoistableE e => HoistableE (ListE e) where
  freeVarsE (ListE xs) = foldMap freeVarsE xs

-- === environments ===

-- The `Subst` type is purely an optimization. We could do everything using
-- the safe API by defining:
--    type Subst v i o = (ScopeFrag i, forall s. Name s i -> v s o)
-- Instead, we use this unsafely-implemented data type for efficiency, to avoid
-- long chains of case analyses as we extend environments one name at a time.

data SubstFrag
  (v ::V)  -- env payload, as a function of the name's color
  (i ::S)  -- starting scope parameter for names we can look up in this env
  (i'::S)  -- ending   scope parameter for names we can look up in this env
  (o ::S)  -- scope parameter for the values stored in the env
  = UnsafeMakeSubst (M.Map RawName [WithColor v o])
  deriving (Generic)
deriving instance (forall c. Show (v c o)) => Show (SubstFrag v i i' o)

-- === environments and scopes ===

lookupSubstFrag :: Color c => SubstFrag v i i' o -> Name c (i:=>:i') -> v c o
lookupSubstFrag (UnsafeMakeSubst m) (UnsafeMakeName rawName) =
  case M.lookup rawName m of
    Just (d:_) -> case fromWithColor d of
      Nothing -> error "Wrong name color (should never happen)"
      Just x -> x
    _ -> error "Subst lookup failed (this should never happen)"

-- Just for debugging
lookupSubstFragRaw :: SubstFrag v i i' o -> RawName -> Maybe (WithColor v o)
lookupSubstFragRaw (UnsafeMakeSubst m) rawName = fmap head $ M.lookup rawName m

instance InFrag (SubstFrag v) where
  emptyInFrag = UnsafeMakeSubst mempty
  catInFrags (UnsafeMakeSubst m1) (UnsafeMakeSubst m2) =
    -- flipped because the innermost names are at the left (head) of the list
    UnsafeMakeSubst (M.unionWith (++) m2 m1)

singletonSubst :: Color c => NameBinder c i i' -> v c o -> SubstFrag v i i' o
singletonSubst (UnsafeMakeBinder name) x =
  UnsafeMakeSubst (M.singleton name [WithColor x])

fmapSubstFrag :: SinkableV v
            => (forall c. Color c => Name c (i:=>:i') -> v c o -> v' c o')
            -> SubstFrag v i i' o -> SubstFrag v' i i' o'
fmapSubstFrag f (UnsafeMakeSubst m) = UnsafeMakeSubst m'
  where m' = flip M.mapWithKey m $ \k xs ->
                flip map xs \(WithColor val) ->
                  WithColor $ f (UnsafeMakeName k) val

envFragAsScope :: forall v i i' o. SubstFrag v i i' o -> ScopeFrag i i'
envFragAsScope (UnsafeMakeSubst m) =
  UnsafeMakeScopeFrag $ flip fmap m \xs ->
    flip map xs \(WithColor (_ :: v c o)) -> WithColor (UnitV :: UnitV c UnsafeS)

-- === garbage collection ===

collectGarbage :: (HoistableV v, HoistableE e)
               => Distinct l => RecSubstFrag v n l -> e l
               -> (forall l'. Distinct l' => RecSubstFrag v n l' -> e l' -> a)
               -> a
collectGarbage (RecSubstFrag (UnsafeMakeSubst env)) e cont = do
  let seedNames = M.keys $ freeVarsE e
  let accessibleNames = S.fromList $ transitiveClosure getParents seedNames
  let env' = RecSubstFrag $ UnsafeMakeSubst $ M.restrictKeys env accessibleNames
  cont env' $ unsafeCoerceE e
  where
    getParents :: RawName -> [RawName]
    getParents name = case M.lookup name env of
      Nothing -> []
      Just [WithColor v] -> M.keys $ freeVarsE v
      _ -> error "shouldn't be possible, due to Distinct constraint"

-- === iterating through env pairs ===

data SubstPair (v::V) (o::S) (i::S) (i'::S) where
  SubstPair :: Color c => NameBinder c i i' -> v c o -> SubstPair v o i i'

toSubstPairs :: forall v i i' o . SubstFrag v i i' o -> Nest (SubstPair v o) i i'
toSubstPairs (UnsafeMakeSubst m) =
  go $ fold $ M.elems $ flip M.mapWithKey m \k xs -> map (mkPair k) xs
  where
    mkPair :: RawName -> WithColor v o -> SubstPair v o UnsafeS UnsafeS
    mkPair rawName (WithColor v) =
      SubstPair (UnsafeMakeBinder rawName) v

    go :: [SubstPair v o UnsafeS UnsafeS] -> Nest (SubstPair v o) i i'
    go [] = unsafeCoerceB Empty
    go (SubstPair b val : rest) = Nest (SubstPair (unsafeCoerceB b) val) $ go rest

data WithRenamer e i o where
  WithRenamer :: SubstFrag Name i i' o -> e i' -> WithRenamer e i o

instance Category (Nest b) where
  id = Empty
  nest' . nest = case nest of
    Empty -> nest'
    Nest b rest -> Nest b $ rest >>> nest'

instance ProvesExt (SubstPair v o) where
  toExtEvidence (SubstPair b _) = toExtEvidence b

instance BindsNames (SubstPair v o) where
  toScopeFrag (SubstPair b _) = toScopeFrag b

-- === instances ===

instance (forall c. Pretty (v c n)) => Pretty (WithColor v n) where
  pretty (WithColor val) = pretty val

instance SinkableV v => SinkableE (SubstFrag v i i') where
  sinkingProofE fresh m = fmapSubstFrag (\(UnsafeMakeName _) v -> sinkingProofE fresh v) m

instance HoistableV v => HoistableE (SubstFrag v i i') where
  freeVarsE frag = foldMapSubstFrag freeVarsE frag

instance SubstV substVal v => SubstE substVal (SubstFrag v i i') where
   substE env frag = fmapSubstFrag (\_ val -> substE env val) frag

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

instance SinkableB b => SinkableB (Nest b) where
  sinkingProofB fresh Empty cont = cont fresh Empty
  sinkingProofB fresh (Nest b rest) cont =
    sinkingProofB fresh b \fresh' b' ->
      sinkingProofB fresh' rest \fresh'' rest' ->
        cont fresh'' (Nest b' rest')

instance HoistableB b => HoistableB (Nest b) where
  freeVarsB Empty = mempty
  freeVarsB (Nest b rest) = freeVarsB (PairB b rest)

instance (forall c n. Pretty (v c n)) => Pretty (SubstFrag v i i' o) where
  pretty (UnsafeMakeSubst m) =
    fold [ pretty v <+> "@>" <+> pretty x <> hardline
         | (v, xs) <- M.toList m, WithColor x <- reverse xs]

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

instance (forall n' l'. Show (b n' l')) => Show (NonEmptyNest b n l) where
  show (NonEmptyNest b rest) = "(NonEmptyNest " <> show b <> " in " <> show rest <> ")"

instance (forall c. Color c => Store (v c n)) => Store (WithColor v n) where
  size = VarSize \(WithColor (v :: v c n)) ->
    getSize (getColorRep (ColorProxy :: ColorProxy c)) + getSize (v :: v c n)

  peek = do
    c <- peek
    WithColor (UnitV :: UnitV c VoidS) <- return $ interpretColor c
    v :: v c n <- peek
    return $ WithColor v

  poke (WithColor (v :: v c n)) = do
    let c = getColorRep (ColorProxy :: ColorProxy c)
    poke c
    poke v

instance SinkableV v => SinkableE (WithColor v) where
  sinkingProofE = todoSinkableProof

instance ( forall c. Color c => Store (v c o)
         , forall c. Color c => Generic (v c o))
         => Store (SubstFrag v i i' o) where

instance ( Store   (b UnsafeS UnsafeS)
         , Generic (b UnsafeS UnsafeS) ) => Store (Nest b n l)

instance Functor HoistExcept where
  fmap f x = f <$> x

instance Applicative HoistExcept where
  pure x = HoistSuccess x
  liftA2 = liftM2

instance Monad HoistExcept where
  return = pure
  HoistFailure vs >>= _ = HoistFailure vs
  HoistSuccess x >>= f = f x

-- TODO: this needs to be sinkive but it's currently not
-- (needs to figure out acceptable tag strings)
instance Pretty RawName where
  pretty (RawName tag n) = pretty tag <> suffix
            where suffix = case n of 0 -> ""
                                     _ -> pretty n

-- === notes ===

{-

Note [Sinkings]

When we inline an expression, we lift it into a larger (deeper) scope,
containing more in-scope variables. For example, when we turn this:

  let foo = \x. \y. x + y + z
  in \y. foo y

into this:

  \y. (\x. \y. x + y + z) y

The expression `\x. x + z + y`, initially in the scope `[z]`, gets sinked into
the scope `[z, y]`. For expression-like things, the sinking is valid if we
know that (1) that the new scope contains distinct names, and (2) it extends the
old scope. These are the `Distinct l` and `Ext n l` conditions in `sink`.
Note that the expression may end up with internal binders shadowing the new vars
in scope, shadows, like the inner `y` above, and that's fine.

But not everything with an expression-like kind `E` (`S -> *`) is sinkable.
For example, a type like `Name n -> Bool` can't be coerced to a `Name l -> Bool`
when `l` is an extension of `n`. It's the usual covariance/contravariance issue
with subtyping. So we have a further type class, `SinkableE`, which asserts
that a type is covariant in the name space parameter. To prove it, we implement the
`sinkingProofE` method (which is never actually called at runtime), which
must produce an sinking `e n -> e l` given an sinking
`forall s. Name s n -> Name s l`.

The typeclass should obey `sinkingProofE (SinkingCoercion id) = id`
Otherwise you could just give an `sinkableE` instance for `Name n -> Bool`
as `sinkingProofE _ _ = const True`.

-}
