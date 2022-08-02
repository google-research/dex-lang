-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MagicHash #-}

module Name (
  Name (..), RawName, freshRawName,
  S (..), C (..), (<.>), SubstFrag (..), NameBinder (..),
  SubstReader (..), FromName (..), Distinct, DExt,
  Ext, ExtEvidence, ProvesExt (..), withExtEvidence, getExtEvidence,
  Subst (..), idSubst, idSubstFrag, newSubst, envFromFrag, traverseSubstFrag,
  WithScope (..), extendRenamer, ScopeReader (..), ScopeExtender (..),
  Scope (..), ScopeFrag (..), SubstE (..), SubstB (..),
  SubstV, InplaceT (..), extendInplaceT, extendSubInplaceT, extendInplaceTLocal,
  DoubleInplaceT (..), liftDoubleInplaceT,
  emitDoubleInplaceTHoisted, unsafeEmitDoubleInplaceTHoisted,
  runDoubleInplaceT, DoubleInplaceTResult (..),
  freshExtendSubInplaceT, extendTrivialInplaceT, extendTrivialSubInplaceT, getOutMapInplaceT, runInplaceT,
  E, B, V, HasNamesE, HasNamesB, BindsNames (..), HasScope (..), RecSubstFrag (..), RecSubst (..),
  lookupTerminalSubstFrag, noShadows, checkNoBinders,
  BindsOneName (..), BindsAtMostOneName (..), BindsNameList (..), (@@>),
  Abs (..), Nest (..), RNest (..), unRNest, toRNest, NonEmptyNest (..),
  nonEmptyToNest, nestToNonEmpty,
  PairB (..), UnitB (..),
  IsVoidS (..), UnitE (..), VoidE, PairE (..), toPairE, fromPairE,
  ListE (..), ComposeE (..), MapE (..), NonEmptyListE (..),
  EitherE (..), LiftE (..), EqE, EqB, OrdE, OrdB, VoidB,
  EitherB (..), BinderP (..),
  LiftB, pattern LiftB,
  HashMapE (..), HashableE, nestToNames,
  MaybeE, fromMaybeE, toMaybeE, pattern JustE, pattern NothingE, MaybeB,
  pattern JustB, pattern NothingB,
  toConstAbs, toConstAbsPure, PrettyE, PrettyB, ShowE, ShowB,
  runScopeReaderT, runScopeReaderM, runSubstReaderT, liftSubstReaderT,
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
  lookupSubstFrag, lookupSubstFragProjected, lookupSubstFragRaw,
  EmptyAbs, pattern EmptyAbs, NaryAbs, SubstVal (..),
  fmapNest, forEachNestItem, forEachNestItemM,
  substM, ScopedSubstReader, runScopedSubstReader,
  HasNameHint (..), NameHint, noHint, Color (..),
  GenericE (..), GenericB (..),
  EitherE2, EitherE3, EitherE4, EitherE5, EitherE6, EitherE7, EitherE8 (..),
  splitNestAt, joinNest, joinRNest, nestLength, nestToList, binderAnn,
  OutReaderT (..), OutReader (..), runOutReaderT,
  toSubstPairs, fromSubstPairs, SubstPair (..),
  InFrag (..), InMap (..), OutFrag (..), OutMap (..), ExtOutMap (..), ExtOutFrag (..),
  hoist, hoistToTop, sinkFromTop, fromConstAbs, exchangeBs, HoistableE (..),
  HoistExcept (..), liftHoistExcept', liftHoistExcept, abstractFreeVars, abstractFreeVar,
  abstractFreeVarsNoAnn,
  WithRenamer (..), ignoreHoistFailure,
  HoistableB (..), HoistableV, withScopeFromFreeVars, canonicalizeForPrinting,
  ClosedWithScope (..),
  WrapE (..), WrapB (..),
  DistinctEvidence (..), withSubscopeDistinct, tryAsColor, withFresh,
  newName, newNameM, newNames,
  unsafeCoerceE, unsafeCoerceB, ColorsEqual (..), eqColorRep,
  sinkR, fmapSubstFrag, catRecSubstFrags, extendRecSubst,
  freeVarsList, isFreeIn, anyFreeIn, isInNameSet, todoSinkableProof,
  locallyMutableInplaceT, liftBetweenInplaceTs,
  updateSubstFrag, nameSetToList, toNameSet, hoistFilterNameSet, NameSet, absurdExtEvidence,
  Mut, fabricateDistinctEvidence, nameSetRawNames,
  MonadTrans1 (..), collectGarbage,
  NameMap, hoistFilterNameMap, insertNameMap, lookupNameMap, singletonNameMap, toListNameMap
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
import Data.Bits
import Data.Functor ((<&>))
import Data.Foldable (toList)
import Data.Maybe (catMaybes)
import Data.Hashable
import Data.Kind (Type)
import Data.Function ((&))
import Data.List.NonEmpty (NonEmpty (..))
import Data.Text.Prettyprint.Doc  hiding (nest)
import GHC.Stack
import GHC.Exts (Constraint, dataToTag#, tagToEnum#, Int(..))
import qualified GHC.Exts as GHC.Exts
import GHC.Generics (Generic (..), Rep)
import Data.Store.Internal

import qualified Unsafe.Coerce as TrulyUnsafe

import RawName ( RawNameMap, RawName, NameHint, HasNameHint (..)
               , freshRawName, rawNameFromHint, rawNames, noHint)
import qualified RawName as R
import Util (zipErr, onFst, onSnd, transitiveClosure)
import Err

-- === category-like classes for envs, scopes etc ===

data Subst v i o where
  Subst :: (forall c. Color c => Name c hidden -> v c o)
        -> SubstFrag v hidden i o
        -> Subst v i o
  -- This is a compact, but unsafe representation of a substitution
  -- that maps every input name `n` to `fromName n` (though realization
  -- of this often requires sticking `unsafeCoerceE` to cast from i to o).
  UnsafeMakeIdentitySubst :: FromName v => Subst v i o

tryApplyIdentitySubst :: Subst v i o -> e i -> Maybe (e o)
tryApplyIdentitySubst s e = case s of
  Subst _ _ -> Nothing
  UnsafeMakeIdentitySubst -> Just $ unsafeCoerceE e

newSubst :: (forall c. Color c => Name c i -> v c o) -> Subst v i o
newSubst f = Subst f emptyInFrag

envFromFrag :: SubstFrag v VoidS i o -> Subst v i o
envFromFrag frag = Subst absurdNameFunction frag

idSubst :: forall v n. FromName v => Subst v n n
idSubst = UnsafeMakeIdentitySubst

idSubstFrag :: (BindsNames b, FromName v) => b n l -> SubstFrag v n l l
idSubstFrag b =
  scopeFragToSubstFrag (\v -> fromName $ sinkR v) (toScopeFrag b)

infixl 9 !
(!) :: Color c => Subst v i o -> Name c i -> v c o
(!) (Subst f env) name =
  case lookupSubstFragProjected env name of
    Left name' -> f name'
    Right val -> val
(!) UnsafeMakeIdentitySubst name = fromName $ unsafeCoerceE name

infixl 1 <.>
(<.>) :: InFrag envFrag => envFrag i1 i2 o -> envFrag i2 i3 o -> envFrag i1 i3 o
(<.>) = catInFrags
{-# INLINE (<.>) #-}

infixl 1 <>>
(<>>) :: InMap env envFrag => env i o -> envFrag i i' o -> env i' o
(<>>) = extendInMap
{-# INLINE (<>>) #-}

class InFrag (envFrag :: S -> S -> S -> *) where
  emptyInFrag :: envFrag i i o
  catInFrags  :: envFrag i1 i2 o -> envFrag i2 i3 o -> envFrag i1 i3 o

class InMap (env :: S -> S -> *) (envFrag :: S -> S -> S -> *) | env -> envFrag where
  emptyInMap :: env VoidS o
  extendInMap :: env i o -> envFrag i i' o -> env i' o

class (SinkableB scopeFrag, BindsNames scopeFrag) => OutFrag (scopeFrag :: S -> S -> *) where
  emptyOutFrag :: scopeFrag n n
  -- The scope is here because solver subst concatenation needs it
  -- TODO: Removing the scope argument would let us implement a faster Applicative for InplaceT!
  catOutFrags  :: Distinct n3 => Scope n3 -> scopeFrag n1 n2 -> scopeFrag n2 n3 -> scopeFrag n1 n3

class HasScope scope => OutMap scope where
  emptyOutMap :: scope VoidS

class OutMap env => ExtOutMap (env :: S -> *) (frag :: S -> S -> *) where
  extendOutMap :: Distinct l => env n -> frag n l -> env l

class ExtOutFrag (frag :: B) (subfrag :: B) where
  extendOutFrag :: Distinct m => frag n l -> subfrag l m -> frag n m

todoSinkableProof :: a
todoSinkableProof =
  error "This will never be called. But we should really finish these proofs."

instance InMap (Subst v) (SubstFrag v) where
  emptyInMap = newSubst absurdNameFunction
  {-# INLINE emptyInMap #-}
  extendInMap UnsafeMakeIdentitySubst frag'@(UnsafeMakeSubst fragMap) =
    case R.null fragMap of
      True  -> UnsafeMakeIdentitySubst
      False -> Subst (fromName . unsafeCoerceE) frag'
  extendInMap (Subst f frag) frag' = Subst f $ frag <.> frag'
  {-# INLINE extendInMap #-}

instance SinkableB ScopeFrag where
  sinkingProofB _ _ _ = todoSinkableProof

instance OutFrag ScopeFrag where
  emptyOutFrag = id
  {-# INLINE emptyOutFrag #-}
  catOutFrags _ = (>>>)
  {-# INLINE catOutFrags #-}

instance HasScope Scope where
  toScope = id
  {-# INLINE toScope #-}

instance OutMap Scope where
  emptyOutMap = Scope id
  {-# INLINE emptyOutMap #-}

instance ExtOutMap Scope ScopeFrag where
  extendOutMap (Scope scope) frag = Scope $ scope >>> frag
  {-# INLINE extendOutMap #-}

-- outvar version of SubstFrag/Subst, where the query name space and the result name
-- space are the same (thus recursive)
newtype RecSubst      (v::V) o    = RecSubst     { fromRecSubst     :: SubstFrag v VoidS o o } deriving Generic
newtype RecSubstFrag  (v::V) o o' = RecSubstFrag { fromRecSubstFrag :: SubstFrag v o o' o'   } deriving Generic

instance SinkableV v => OutFrag (RecSubstFrag v) where
  emptyOutFrag = RecSubstFrag $ emptyInFrag
  {-# INLINE emptyOutFrag #-}
  catOutFrags _ = catRecSubstFrags
  {-# INLINE catOutFrags #-}

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
  {-# INLINE emptyOutFrag #-}
  catOutFrags _ = (>>>)
  {-# INLINE catOutFrags #-}

instance (SinkableB b, BindsNames b) => OutFrag (RNest b) where
  emptyOutFrag = id
  {-# INLINE emptyOutFrag #-}
  catOutFrags _ = (>>>)
  {-# INLINE catOutFrags #-}

updateSubstFrag :: Color c => Name c i -> v c o -> SubstFrag v VoidS i o
                -> SubstFrag v VoidS i o
updateSubstFrag (UnsafeMakeName v) rhs (UnsafeMakeSubst m) =
  UnsafeMakeSubst $ R.adjust (\(SubstItem f _) -> SubstItem f (unsafeCoerceVC rhs)) v m

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
{-# INLINE dropSubst #-}

extendSubst :: SubstReader v m => SubstFrag v i i' o -> m i' o r -> m i o r
extendSubst frag cont = do
  env <- (<>>frag) <$> getSubst
  withSubst env cont
{-# INLINE extendSubst #-}

-- === extending envs with name-only substitutions ===

class FromName (v::V) where
  fromName :: Name c n -> v c n

instance FromName Name where
  fromName = id
  {-# INLINE fromName #-}

instance FromName (SubstVal c v) where
  fromName = Rename
  {-# INLINE fromName #-}

extendRenamer :: (SubstReader v m, FromName v) => SubstFrag Name i i' o -> m i' o r -> m i o r
extendRenamer frag = extendSubst (fmapSubstFrag (const fromName) frag)

-- === common scoping patterns ===

data Abs (binder::B) (body::E) (n::S) where
  Abs :: binder n l -> body l -> Abs binder body n
deriving instance (ShowB b, ShowE e) => Show (Abs b e n)

data Nest (binder::B) (n::S) (l::S) where
  Nest  :: binder n h -> Nest binder h l -> Nest binder n l
  Empty ::                                  Nest binder n n

data RNest (binder::B) (n::S) (l::S) where
  RNest  :: RNest binder n h -> binder h l -> RNest binder n l
  REmpty ::                                   RNest binder n n

unRNest :: RNest b n l -> Nest b n l
unRNest rn = go Empty rn
  where
    go :: Nest b h l -> RNest b n h -> Nest b n l
    go acc = \case
      REmpty     -> acc
      RNest bs b -> go (Nest b acc) bs

toRNest :: Nest b n l -> RNest b n l
toRNest n = go REmpty n
  where
    go :: RNest b n h -> Nest b h l -> RNest b n l
    go acc = \case
      Empty     -> acc
      Nest b bs -> go (RNest acc b) bs

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

nestToNonEmpty :: Nest b n l -> Maybe (NonEmptyNest b n l)
nestToNonEmpty Empty = Nothing
nestToNonEmpty (Nest b bs) = Just $ NonEmptyNest b bs

-- === Sinkings and projections ===

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

instance ProvesExt ScopeFrag where
  toExtEvidence _ = fabricateExtEvidence

instance BindsNames ScopeFrag where
  toScopeFrag s = s

instance HoistableB ScopeFrag where
  freeVarsB _ = mempty

class HasScope (bindings :: S -> *) where
  -- XXX: this must be O(1)
  toScope :: bindings n -> Scope n

withExtEvidence :: ProvesExt b => b n l -> (Ext n l => a) -> a
withExtEvidence b cont = withExtEvidence' (toExtEvidence b) cont
{-# INLINE withExtEvidence #-}

-- like sink, but uses the ScopeReader monad for its `Distinct` proof
sinkM :: (ScopeReader m, Ext n l, SinkableE e) => e n -> m l (e l)
sinkM e = do
  Distinct <- getDistinct
  return $ sink e
{-# INLINE sinkM #-}

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
  m <- flip R.traverseWithKey vs \rawName (SubstItem fs _) ->
    interpretColor (substItemColor fs) \(ColorProxy :: ColorProxy c) -> do
      v' <- f (UnsafeMakeName rawName :: Name c i)
      return $ SubstItem fs (unsafeCoerceVC v')
  fmapNamesM (applyTraversed m) e
{-# INLINE traverseNames #-}

applyTraversed :: (FromName v, Color c)
               => RawNameMap (SubstItem v n) -> Name c i -> v c n
applyTraversed m = \((UnsafeMakeName v) :: Name c i) -> case R.lookup v m of
    Just item -> case fromSubstItem item of
      Just val' -> val'
      Nothing -> error "shouldn't happen"
    Nothing -> fromName $ (UnsafeMakeName v :: Name c o)

fmapNames :: (SubstE v e, Distinct o)
          => Scope o -> (forall c. Color c => Name c i -> v c o) -> e i -> e o
fmapNames scope f e = substE (scope, newSubst f) e
{-# INLINE fmapNames #-}

fmapNamesM :: (SubstE v e, SinkableE e, ScopeReader m)
          => (forall c. Color c => Name c i -> v c o)
          -> e i -> m o (e o)
fmapNamesM f e = do
  scope <- unsafeGetScope
  Distinct <- getDistinct
  return $ substE (scope, newSubst f) e
{-# INLINE fmapNamesM #-}

toConstAbs :: (SinkableE e, ScopeReader m, Color c)
           => e n -> m n (Abs (NameBinder c) e n)
toConstAbs body = do
  WithScope scope body' <- addScope body
  withFresh noHint scope \b -> do
    sinkM $ Abs b $ sink body'

toConstAbsPure :: (HoistableE e, SinkableE e, Color c)
               => e n -> (Abs (NameBinder c) e n)
toConstAbsPure e = Abs (UnsafeMakeBinder n) (unsafeCoerceE e)
  where n = freshRawName noHint $ freeVarsE e

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
      let UnsafeMakeName bn  = binderName b
      let UnsafeMakeName bn' = binderName b'
      let env' = case env of
                   UnsafeMakeIdentitySubst | bn == bn' -> UnsafeMakeIdentitySubst
                   _ -> sink env <>> b @> (fromName $ binderName b')
      cont (scope', env') b'

substM :: (SubstReader v m, ScopeReader2 m, SinkableE e, SubstE v e, FromName v)
       => e i -> m i o (e o)
substM e = do
  env <- getSubst
  case tryApplyIdentitySubst env e of
    Just e' -> return $ e'
    Nothing -> do
      WithScope scope env' <- addScope env
      sinkM $ fmapNames scope (env'!) e
{-# INLINE substM #-}

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
  {-# INLINE (@>) #-}

instance Color c => BindsOneName (NameBinder c) c where
  binderName (UnsafeMakeBinder v) = UnsafeMakeName v
  {-# INLINE binderName #-}

instance Color c => BindsAtMostOneName (BinderP c ann) c where
  (b:>_) @> x = b @> x
  {-# INLINE (@>) #-}

instance Color c => BindsOneName (BinderP c ann) c where
  binderName (b:>_) = binderName b
  {-# INLINE binderName #-}

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
  case tryApplyIdentitySubst fullSubst x of
    Just x' -> return x'
    Nothing -> do
      WithScope scope fullSubst' <- addScope fullSubst
      sinkM $ fmapNames scope (fullSubst' !) x
{-# INLINE applySubst #-}

applyAbs :: ( SinkableV v, SinkableE e
            , FromName v, ScopeReader m, BindsOneName b c, SubstE v e)
         => Abs b e n -> v c n -> m n (e n)
applyAbs (Abs b body) x = applySubst (b@>x) body
{-# INLINE applyAbs #-}

applyNaryAbs :: ( SinkableV v, FromName v, ScopeReader m, BindsNameList b c, SubstE v e
                , SubstB v b, SinkableE e)
             => Abs b e n -> [v c n] -> m n (e n)
applyNaryAbs (Abs bs body) xs = applySubst (bs @@> xs) body
{-# INLINE applyNaryAbs #-}

lookupSubstFragProjected :: Color c => SubstFrag v i i' o -> Name c i'
                         -> Either (Name c i) (v c o)
lookupSubstFragProjected (UnsafeMakeSubst s) (UnsafeMakeName rawName) =
  case R.lookup rawName s of
    Just d -> case fromSubstItem d of
      Nothing -> error "Wrong name color (should never happen)"
      Just x -> Right $ x
    _ -> Left $ UnsafeMakeName rawName

fromSubstPairs :: Nest (SubstPair v o) i i' -> SubstFrag v i i' o
fromSubstPairs Empty = emptyInFrag
fromSubstPairs (Nest (SubstPair (UnsafeRepeatedNameBinder d (UnsafeMakeBinder b)) v) rest) =
  (UnsafeMakeSubst $ R.singleton b $ toSubstItem d v) `catInFrags` fromSubstPairs rest

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

nestToNames :: (Distinct l, Ext n l, BindsOneName b c, BindsNames b)
            => Nest b n l -> [Name c l]
nestToNames bs = nestToList (sink . binderName) bs

splitNestAt :: Int -> Nest b n l -> PairB (Nest b) (Nest b) n l
splitNestAt 0 bs = PairB Empty bs
splitNestAt _  Empty = error "split index too high"
splitNestAt n (Nest b rest) =
  case splitNestAt (n-1) rest of
    PairB xs ys -> PairB (Nest b xs) ys

joinNest :: Nest b n m -> Nest b m l -> Nest b n l
joinNest l Empty = l
joinNest l r     = doJoinNest l r
{-# NOINLINE joinNest #-}
{-# RULES
      "joinNest Empty *"    forall n. joinNest Empty n = n;
      "joinNest * Empty"    forall n. joinNest n Empty = n;
  #-}

doJoinNest :: Nest b n m -> Nest b m l -> Nest b n l
doJoinNest l r = case l of
  Empty     -> r
  Nest b lt -> Nest b $ doJoinNest lt r

joinRNest :: RNest b n m -> RNest b m l -> RNest b n l
joinRNest l r = case r of
  REmpty     -> l
  RNest bs b -> RNest (joinRNest l bs) b
{-# NOINLINE joinRNest #-}
{-# RULES
      "joinRNest REmpty *"    forall n.   joinRNest REmpty n = n;
      "joinRNest * REmpty"    forall n.   joinRNest n REmpty = n;
  #-}

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
        let e' = case tryApplyIdentitySubst subst' e of
                   Just e'' -> e''
                   Nothing  -> substE (scope', subst') e
        withExtEvidence b' $ cont scope' b' e'

extendIfDistinct :: Scope n -> ScopeFrag n l
                 -> Maybe (DistinctEvidence l, Scope l)
extendIfDistinct scope frag = do
  if noShadows frag && R.disjoint scopeNames extNames
    then Just ( fabricateDistinctEvidence
              , Scope (UnsafeMakeScopeFrag (extNames  <> scopeNames)))
    else Nothing
  where
    Scope (UnsafeMakeScopeFrag scopeNames) = scope
    UnsafeMakeScopeFrag extNames = frag

noShadows :: ScopeFrag n l -> Bool
noShadows (UnsafeMakeScopeFrag frag) = all isUnique frag
  where
    isUnique item = case itemDistinctness item of
      DistinctName  -> True
      ShadowingName -> False

checkNoBinders :: BindsNames b => b n l -> Maybe (UnitB n l)
checkNoBinders b =
  case nameSetRawNames $ toNameSet $ toScopeFrag b of
    [] -> Just $ unsafeCoerceB UnitB
    _ -> Nothing

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
instance ColorsNotEqual AtomNameC InstanceNameC   where notEqProof = \case
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
{-# INLINE addScope #-}

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
    -- XXX: convention is the opposite of de Bruijn order, `0` means
    -- the *outermost* binder
 | HashBoundName Int
 deriving (Eq, Generic)

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
  {-# INLINE fromE #-}
  toE e = EKey e
  {-# INLINE toE #-}

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
  {-# INLINE fromE #-}
  toE (ListE pairs) = eMapFromList $ map fromPairE pairs
  {-# INLINE toE #-}

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
  {-# INLINE getDistinct #-}
  unsafeGetScope = ScopeReaderT $ asks snd
  {-# INLINE unsafeGetScope #-}

instance Monad m => ScopeExtender (ScopeReaderT m) where
  refreshAbsScope ab cont = ScopeReaderT $ ReaderT
    \(Distinct, scope) -> refreshAbsPure scope ab
       \_ b e -> do
         let env' = extendOutMap scope $ toScopeFrag b
         runReaderT (runScopeReaderT' $ cont b e) (Distinct, env')

-- === SubstReaderT transformer ===

newtype SubstReaderT (v::V) (m::MonadKind1) (i::S) (o::S) (a:: *) =
  SubstReaderT { runSubstReaderT' :: ReaderT (Subst v i o) (m o) a }

instance (forall n. Functor (m n)) => Functor (SubstReaderT v m i o) where
  fmap f (SubstReaderT m) = SubstReaderT $ fmap f m
  {-# INLINE fmap #-}

instance Monad1 m => Applicative (SubstReaderT v m i o) where
  pure   = SubstReaderT . pure
  {-# INLINE pure #-}
  liftA2 f (SubstReaderT x) (SubstReaderT y) = SubstReaderT $ liftA2 f x y
  {-# INLINE liftA2 #-}
  (SubstReaderT f) <*> (SubstReaderT x) = SubstReaderT $ f <*> x
  {-# INLINE (<*>) #-}

instance (forall n. Monad (m n)) => Monad (SubstReaderT v m i o) where
  return = SubstReaderT . return
  {-# INLINE return #-}
  (SubstReaderT m) >>= f = SubstReaderT (m >>= (runSubstReaderT' . f))
  {-# INLINE (>>=) #-}

deriving instance (Monad1 m, MonadFail1   m) => MonadFail   (SubstReaderT v m i o)
deriving instance (Monad1 m, Alternative1 m) => Alternative (SubstReaderT v m i o)
deriving instance (Fallible1 m) => Fallible (SubstReaderT v m i o)
deriving instance Catchable1 m => Catchable (SubstReaderT v m i o)
deriving instance CtxReader1 m => CtxReader (SubstReaderT v m i o)

type ScopedSubstReader (v::V) = SubstReaderT v (ScopeReaderT Identity) :: MonadKind2

liftSubstReaderT :: Monad1 m => m o a -> SubstReaderT v m i o a
liftSubstReaderT m = SubstReaderT $ lift m
{-# INLINE liftSubstReaderT #-}

runScopedSubstReader :: Distinct o => Scope o -> Subst v i o
                   -> ScopedSubstReader v i o a -> a
runScopedSubstReader scope env m =
  runIdentity $ runScopeReaderT scope $ runSubstReaderT env m
{-# INLINE runScopedSubstReader #-}

runSubstReaderT :: Subst v i o -> SubstReaderT v m i o a -> m o a
runSubstReaderT env m = runReaderT (runSubstReaderT' m) env
{-# INLINE runSubstReaderT #-}

instance (SinkableV v, Monad1 m) => SubstReader v (SubstReaderT v m) where
  getSubst = SubstReaderT ask
  {-# INLINE getSubst #-}
  withSubst env (SubstReaderT cont) = SubstReaderT $ withReaderT (const env) cont
  {-# INLINE withSubst #-}

instance (SinkableV v, ScopeReader m) => ScopeReader (SubstReaderT v m i) where
  unsafeGetScope = SubstReaderT $ lift unsafeGetScope
  {-# INLINE unsafeGetScope #-}
  getDistinct = SubstReaderT $ lift getDistinct
  {-# INLINE getDistinct #-}

instance (SinkableV v, ScopeReader m, ScopeExtender m)
         => ScopeExtender (SubstReaderT v m i) where
  refreshAbsScope ab cont = SubstReaderT $ ReaderT \env ->
    refreshAbsScope ab \b e -> do
      let SubstReaderT (ReaderT cont') = cont b e
      env' <- sinkM env
      cont' env'

instance (SinkableV v, MonadIO1 m) => MonadIO (SubstReaderT v m i o) where
  liftIO m = SubstReaderT $ lift $ liftIO m
  {-# INLINE liftIO #-}

instance (Monad1 m, MonadState (s o) (m o)) => MonadState (s o) (SubstReaderT v m i o) where
  state = SubstReaderT . lift . state
  {-# INLINE state #-}

-- === OutReader monad: reads data in the output name space ===

class OutReader (e::E) (m::MonadKind1) | m -> e where
  askOutReader :: m n (e n)
  localOutReader :: e n -> m n a -> m n a

newtype OutReaderT (e::E) (m::MonadKind1) (n::S) (a :: *) =
  OutReaderT { runOutReaderT' :: ReaderT (e n) (m n) a }
  deriving (Functor, Applicative, Monad, MonadFail, Fallible)

runOutReaderT :: e n -> OutReaderT e m n a -> m n a
runOutReaderT env m = flip runReaderT env $ runOutReaderT' m
{-# INLINE runOutReaderT #-}

instance (SinkableE e, ScopeReader m)
         => ScopeReader (OutReaderT e m) where
  unsafeGetScope = OutReaderT $ lift unsafeGetScope
  {-# INLINE unsafeGetScope #-}
  getDistinct = OutReaderT $ lift getDistinct
  {-# INLINE getDistinct #-}

instance (SinkableE e, ScopeExtender m)
         => ScopeExtender (OutReaderT e m) where
  refreshAbsScope ab cont = OutReaderT $ ReaderT \env ->
    refreshAbsScope ab \b e -> do
      let OutReaderT (ReaderT cont') = cont b e
      env' <- sinkM env
      cont' env'

instance Monad1 m => OutReader e (OutReaderT e m) where
  askOutReader = OutReaderT ask
  {-# INLINE askOutReader #-}
  localOutReader r (OutReaderT m) = OutReaderT $ local (const r) m
  {-# INLINE localOutReader #-}

instance OutReader e m => OutReader e (SubstReaderT v m i) where
  askOutReader = SubstReaderT $ ReaderT $ const askOutReader
  {-# INLINE askOutReader #-}
  localOutReader e (SubstReaderT (ReaderT f)) = SubstReaderT $ ReaderT $ \env ->
    localOutReader e $ f env
  {-# INLINE localOutReader #-}

instance (Monad1 m, MonadReader (r o) (m o)) => MonadReader (r o) (SubstReaderT v m i o) where
  ask = SubstReaderT $ ReaderT $ const ask
  {-# INLINE ask #-}
  local r (SubstReaderT (ReaderT f)) = SubstReaderT $ ReaderT $ \env ->
    local r $ f env
  {-# INLINE local #-}

instance (Monad1 m, Alternative (m n)) => Alternative (OutReaderT e m n) where
  empty = OutReaderT $ lift empty
  {-# INLINE empty #-}
  OutReaderT (ReaderT f1) <|> OutReaderT (ReaderT f2) =
    OutReaderT $ ReaderT \env ->
      f1 env <|> f2 env
  {-# INLINE (<|>) #-}

instance Searcher1 m => Searcher (OutReaderT e m n) where
  OutReaderT (ReaderT f1) <!> OutReaderT (ReaderT f2) =
    OutReaderT $ ReaderT \env ->
      f1 env <!> f2 env
  {-# INLINE (<!>) #-}

instance MonadWriter w (m n) => MonadWriter w (OutReaderT e m n) where
  tell w = OutReaderT $ lift $ tell w
  {-# INLINE tell #-}
  listen = undefined
  pass = undefined

-- === ZipSubstReaderT transformer ===

newtype ZipSubstReaderT (m::MonadKind1) (i1::S) (i2::S) (o::S) (a:: *) =
  ZipSubstReaderT { runZipSubstReaderT :: ReaderT (ZipSubst i1 i2 o) (m o) a }
  deriving (Functor, Applicative, Monad, Fallible, MonadFail)

type ZipSubst i1 i2 o = (Subst Name i1 o, Subst Name i2 o)

instance ScopeReader m => ScopeReader (ZipSubstReaderT m i1 i2) where
  unsafeGetScope = ZipSubstReaderT $ lift unsafeGetScope
  {-# INLINE unsafeGetScope #-}
  getDistinct = ZipSubstReaderT $ lift getDistinct
  {-# INLINE getDistinct #-}

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

-- The bindings returned by the action should be an extension of the input bindings by the emitted decls.
newtype InplaceT (bindings::E) (decls::B) (m::MonadKind) (n::S) (a :: *) = UnsafeMakeInplaceT
  { unsafeRunInplaceT :: Distinct n => bindings n -> decls UnsafeS UnsafeS -> m (a, decls UnsafeS UnsafeS, bindings UnsafeS) }

runInplaceT
  :: (ExtOutMap b d, OutFrag d, Monad m)
  => Distinct n
  => b n
  -> InplaceT b d m n a
  -> m (d n n, a)
runInplaceT bindings (UnsafeMakeInplaceT f) = do
  (result, d, _) <- f bindings emptyOutFrag
  return (unsafeCoerceB d, result)
{-# INLINE runInplaceT #-}

-- Special case of extending without introducing new names
-- (doesn't require `Mut n`)
extendTrivialInplaceT
  :: (ExtOutMap b d, OutFrag d, Monad m)
  => d n n
  -> InplaceT b d m n ()
extendTrivialInplaceT d =
  UnsafeMakeInplaceT \env decls -> do
    let env' = unsafeCoerceE $ extendOutMap env d
    withFabricatedDistinct @UnsafeS $
      return ((), catOutFrags (toScope env') decls $ unsafeCoerceB d, env')
{-# INLINE extendTrivialInplaceT #-}

extendTrivialSubInplaceT
  :: (ExtOutMap b d, ExtOutFrag ds d, Monad m)
  => d n n
  -> InplaceT b ds m n ()
extendTrivialSubInplaceT d =
  UnsafeMakeInplaceT \env decls -> do
    let env' = extendOutMap env d
    withFabricatedDistinct @UnsafeS $
      return ((), extendOutFrag decls $ unsafeCoerceB d, unsafeCoerceE env')
{-# INLINE extendTrivialSubInplaceT #-}

-- TODO: This should be declared unsafe!
getOutMapInplaceT
  :: (ExtOutMap b d, Monad m)
  => InplaceT b d m n (b n)
getOutMapInplaceT = UnsafeMakeInplaceT \env decls ->
  return (env, decls, unsafeCoerceE env)
{-# INLINE getOutMapInplaceT #-}

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
  UnsafeMakeInplaceT \env decls ->
    unsafeRunInplaceT cont (f env) decls
{-# INLINE extendInplaceTLocal #-}

extendInplaceT
  :: forall m b d e n.
     (ExtOutMap b d, OutFrag d, Monad m, SubstB Name d, SubstE Name e)
  => Mut n => Abs d e n -> InplaceT b d m n (e n)
extendInplaceT ab = do
  UnsafeMakeInplaceT \env decls ->
    refreshAbsPure (toScope env) ab \_ d result -> do
      let env' = unsafeCoerceE $ extendOutMap env d
      withFabricatedDistinct @UnsafeS $
        return (unsafeCoerceE result, catOutFrags (toScope env') decls $ unsafeCoerceB d, env')
{-# INLINE extendInplaceT #-}

extendSubInplaceT
  :: (ExtOutMap b d, ExtOutFrag ds d, BindsNames d, Monad m, SubstB Name d, SubstE Name e)
  => Mut n => Abs d e n -> InplaceT b ds m n (e n)
extendSubInplaceT ab = do
  UnsafeMakeInplaceT \env decls ->
    refreshAbsPure (toScope env) ab \_ d result -> do
      let env' = unsafeCoerceE $ extendOutMap env d
      withFabricatedDistinct @UnsafeS $
        return (unsafeCoerceE result, extendOutFrag decls $ unsafeCoerceB d, env')
{-# INLINE extendSubInplaceT #-}

freshExtendSubInplaceT
  :: (ExtOutMap b d, ExtOutFrag ds d, Monad m, Color c)
  => Mut n => NameHint -> (forall l. NameBinder c n l -> (d n l, e l)) -> InplaceT b ds m n (e n)
freshExtendSubInplaceT hint build =
   UnsafeMakeInplaceT \env decls ->
     withFresh hint (toScope env) \b -> do
       let (d, result) = build b
       let env' = unsafeCoerceE $ extendOutMap env d
       withFabricatedDistinct @UnsafeS $
         return (unsafeCoerceE result, extendOutFrag decls $ unsafeCoerceB d, env')
{-# INLINE freshExtendSubInplaceT #-}

locallyMutableInplaceT
  :: forall m b d n e.
     (ExtOutMap b d, OutFrag d, Monad m, SinkableE e)
  => (forall l. (Mut l, DExt n l) => InplaceT b d m l (e l))
  -> InplaceT b d m n (Abs d e n)
locallyMutableInplaceT cont = do
  UnsafeMakeInplaceT \env decls -> do
    (e, d, _) <- withFabricatedMut @n $
      unsafeRunInplaceT cont env emptyOutFrag
    return (Abs (unsafeCoerceB d) e, decls, unsafeCoerceE env)
{-# INLINE locallyMutableInplaceT #-}

liftBetweenInplaceTs
  :: (Monad m, ExtOutMap bs ds, OutFrag ds, OutFrag ds')
  => (forall a'. m' a' -> m a')
  -> (bs n -> bs' n)
  -> (forall l l' . Distinct l' => ds' l l' -> ds  l l')
  -> InplaceT bs' ds' m' n a
  -> InplaceT bs  ds  m  n a
liftBetweenInplaceTs liftInner lowerBindings liftDecls (UnsafeMakeInplaceT f) =
  UnsafeMakeInplaceT \envOuter declsOuter -> do
    (result, dInner, _) <- liftInner $ f (lowerBindings envOuter) emptyOutFrag
    withFabricatedDistinct @UnsafeS do
      let dOuter = liftDecls dInner
      let envOuter' = extendOutMap (unsafeCoerceE envOuter) dOuter
      return (result, catOutFrags (toScope envOuter') declsOuter dOuter, envOuter')
{-# INLINE liftBetweenInplaceTs #-}

-- === predicates for mutable and immutable scope parameters ===

class Mut (n::S)
instance Mut UnsafeS

withFabricatedMut :: forall n a. (Mut n => a) -> a
withFabricatedMut cont = fromWrapWithMut
 ( TrulyUnsafe.unsafeCoerce ( WrapWithMut cont :: WrapWithMut n       a
                                             ) :: WrapWithMut UnsafeS a)
{-# INLINE withFabricatedMut #-}

newtype WrapWithMut n r =
  WrapWithMut { fromWrapWithMut :: Mut n => r }

-- === InplaceT instances ===

instance (ExtOutMap bindings decls, BindsNames decls, SinkableB decls, Monad m)
         => Functor (InplaceT bindings decls m n) where
  fmap = liftM
  {-# INLINE fmap #-}

instance (ExtOutMap bindings decls, BindsNames decls, SinkableB decls, Monad m)
         => Applicative (InplaceT bindings decls m n) where
  pure = return
  {-# INLINE pure #-}
  liftA2 = liftM2
  {-# INLINE liftA2 #-}
  f <*> x = do { f' <- f; x' <- x; return (f' x') }
  {-# INLINE (<*>) #-}

instance (ExtOutMap bindings decls, BindsNames decls, SinkableB decls, Monad m)
         => Monad (InplaceT bindings decls m n) where
  return x = UnsafeMakeInplaceT \env decls -> do
    return (x, decls, unsafeCoerceE env)
  {-# INLINE return #-}
  m >>= f = UnsafeMakeInplaceT \outMap decls -> do
    (x, decls1, outMap1) <- unsafeRunInplaceT m outMap decls
    unsafeRunInplaceT (f x) (unsafeCoerceE outMap1) decls1
  {-# INLINE (>>=) #-}

instance (ExtOutMap bindings decls, BindsNames decls, SinkableB decls, Monad m)
         => ScopeReader (InplaceT bindings decls m) where
  getDistinct = UnsafeMakeInplaceT \env decls -> return (Distinct, decls, unsafeCoerceE env)
  {-# INLINE getDistinct #-}
  unsafeGetScope = toScope <$> getOutMapInplaceT
  {-# INLINE unsafeGetScope #-}

instance (ExtOutMap bindings decls, BindsNames decls, SinkableB decls, Monad m, MonadFail m)
         => MonadFail (InplaceT bindings decls m n) where
  fail s = lift1 $ fail s
  {-# INLINE fail #-}

instance (ExtOutMap bindings decls, BindsNames decls, SinkableB decls, Monad m, Fallible m)
         => Fallible (InplaceT bindings decls m n) where
  throwErrs errs = UnsafeMakeInplaceT \_ _ -> throwErrs errs
  addErrCtx ctx cont = UnsafeMakeInplaceT \env decls ->
    addErrCtx ctx $ unsafeRunInplaceT cont env decls
  {-# INLINE addErrCtx #-}

instance (ExtOutMap bindings decls, BindsNames decls, SinkableB decls, Monad m, CtxReader m)
         => CtxReader (InplaceT bindings decls m n) where
  getErrCtx = lift1 getErrCtx

instance ( ExtOutMap bindings decls, BindsNames decls, SinkableB decls, Monad m
         , Alternative m)
         => Alternative (InplaceT bindings decls m n) where
  empty = lift1 empty
  {-# INLINE empty #-}
  UnsafeMakeInplaceT f1 <|> UnsafeMakeInplaceT f2 = UnsafeMakeInplaceT \env decls ->
    f1 env decls <|> f2 env decls
  {-# INLINE (<|>) #-}

instance ( ExtOutMap bindings decls, BindsNames decls, SinkableB decls,
           Monad m, Alternative m, Searcher m)
         => Searcher (InplaceT bindings decls m n) where
  UnsafeMakeInplaceT f1 <!> UnsafeMakeInplaceT f2 = UnsafeMakeInplaceT \env decls ->
    f1 env decls <!> f2 env decls
  {-# INLINE (<!>) #-}

instance ( ExtOutMap bindings decls, BindsNames decls, SinkableB decls,
           Catchable m)
         => Catchable (InplaceT bindings decls m n) where
  catchErr (UnsafeMakeInplaceT f1) handler = UnsafeMakeInplaceT \env decls ->
    f1 env decls `catchErr` \err -> case handler err of
      UnsafeMakeInplaceT f2 -> f2 env decls

instance ( ExtOutMap bindings decls, BindsNames decls, SinkableB decls
         , MonadWriter w m)
         => MonadWriter w (InplaceT bindings decls m n) where
  tell w = lift1 $ tell w
  {-# INLINE tell #-}
  listen = undefined
  pass = undefined

instance ( ExtOutMap bindings decls, BindsNames decls, SinkableB decls
         , MonadState s m)
         => MonadState s (InplaceT bindings decls m n) where
  state f = lift1 $ state f
  {-# INLINE state #-}

instance (ExtOutMap bindings decls, BindsNames decls, SinkableB decls)
         => MonadTrans1 (InplaceT bindings decls) where
  lift1 m = UnsafeMakeInplaceT \env decls -> (, decls, unsafeCoerceE env) <$> m
  {-# INLINE lift1 #-}

instance ( ExtOutMap bindings decls, BindsNames decls, SinkableB decls
         , MonadReader r m)
         => MonadReader r (InplaceT bindings decls m n) where
  ask = lift1 $ ask
  {-# INLINE ask #-}
  local f (UnsafeMakeInplaceT cont) =
    UnsafeMakeInplaceT \env decls -> local f (cont env decls)
  {-# INLINE local #-}

instance ( ExtOutMap bindings decls, BindsNames decls, SinkableB decls
         , MonadIO m)
         => MonadIO (InplaceT bindings decls m n) where
  liftIO = lift1 . liftIO
  {-# INLINE liftIO #-}

-- === DoubleInplaceT ===

-- Allows emitting `d1` decls at the top level, if hoisting succeeds.

-- The ScopeFrag in the StateT tracks the initial names in scope, plus the names
-- introduced by the `d1` top decls. We use it for the hoisting check: if an
-- E-kinded thing mentions those names and no others, then we can safely hoist
-- it above the names introduced by `d2` and the names in `bindings` from use of
-- `EnvExtender`. Alternatively, we could maintain a
-- `ScopeFrag hidden_initial_scope n` to do the hoisting but then we couldn't
-- safely implement `liftDoubleInplaceT` because it wouldn't be extended
-- correctly.
newtype DoubleInplaceT (bindings::E) (d1::B) (d2::B) (m::MonadKind) (n::S) (a :: *) =
  UnsafeMakeDoubleInplaceT
  { unsafeRunDoubleInplaceT
    :: StateT (Scope UnsafeS, d1 UnsafeS UnsafeS) (InplaceT bindings d2 m n) a }
  deriving ( Functor, Applicative, Monad, MonadFail, Fallible
           , CtxReader, MonadWriter w, MonadReader r, MonadIO, Catchable)

liftDoubleInplaceT
  :: (Monad m, ExtOutMap bindings d2, OutFrag d2)
  => InplaceT bindings d2 m n a -> DoubleInplaceT bindings d1 d2 m n a
liftDoubleInplaceT m = UnsafeMakeDoubleInplaceT $ lift m

-- Emits top-level bindings, `d1`, failing if it can't be hoisted to the top,
-- and sinks an expression, `e`, that may mention those bindings, back to the
-- local scope (often `e` is just a name that the `d1` defines).
-- TODO: should we give this a distinctness constraint and avoid the refreshing?
emitDoubleInplaceTHoisted
  :: ( Monad m, ExtOutMap b d1, OutFrag d1
     , ExtOutMap b d2, OutFrag d2
     , HoistableE e, SubstE Name e, SubstB Name d1, HoistableB d1)
  => Abs d1 e n -> DoubleInplaceT b d1 d2 m n (Maybe (e n))
emitDoubleInplaceTHoisted emission = do
  Scope ~(UnsafeMakeScopeFrag topScopeFrag) <- UnsafeMakeDoubleInplaceT $ fst <$> get
  if R.containedIn (freeVarsE emission) topScopeFrag
    then do
      scope <- unsafeGetScope
      Distinct <- getDistinct
      refreshAbsPure scope emission \_ d e -> do
        unsafeEmitDoubleInplaceTHoisted $ unsafeCoerceB d
        return $ Just $ unsafeCoerceE e
    else
      return Nothing

unsafeEmitDoubleInplaceTHoisted
  :: ( Monad m, ExtOutMap b d1, OutFrag d1
     , ExtOutMap b d2, OutFrag d2
     , SubstB Name d1, HoistableB d1)
  => d1 UnsafeS UnsafeS -> DoubleInplaceT b d1 d2 m n ()
unsafeEmitDoubleInplaceTHoisted d1 = do
  UnsafeMakeDoubleInplaceT $ StateT \(topScope, d1Prev) ->
    UnsafeMakeInplaceT \env d2 -> do
      withFabricatedDistinct @UnsafeS do
        let topScopeNew = extendOutMap topScope (toScopeFrag $ unsafeCoerceB d1)
        let envNew = extendOutMap env (unsafeCoerceB d1)
        let d1New = catOutFrags (toScope envNew) d1Prev d1
        return (((), (topScopeNew, d1New)), d2, envNew)

data DoubleInplaceTResult (d::B) (e::E) (n::S) =
  DoubleInplaceTResult (d n n) (e n)

runDoubleInplaceT
  :: (ExtOutMap b d1, ExtOutMap b d2, OutFrag d1, OutFrag d2, Monad m)
  => Distinct n
  => b n
  -> (forall l. DExt n l => DoubleInplaceT b d1 d2 m l (e l))
  -> m (Abs d1 (DoubleInplaceTResult d2 e) n)
runDoubleInplaceT env cont = do
  let scope = unsafeCoerceE $ (toScope env) :: Scope UnsafeS
  (d2, (result, (_, d1))) <- runInplaceT env $
    runStateT (unsafeRunDoubleInplaceT cont) (scope, emptyOutFrag)
  return $ Abs (unsafeCoerceB d1) $ unsafeCoerceE $ DoubleInplaceTResult d2 result

instance ( ExtOutMap b d1, OutFrag d1
         , ExtOutMap b d2, OutFrag d2
         , Monad m)
          => ScopeReader (DoubleInplaceT b d1 d2 m) where
  getDistinct = liftDoubleInplaceT getDistinct
  {-# INLINE getDistinct #-}
  unsafeGetScope = liftDoubleInplaceT unsafeGetScope
  {-# INLINE unsafeGetScope #-}

-- === name hints ===

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
 where c1Rep = getColorRep @c1; c2Rep = getColorRep @c2
{-# INLINE eqColorRep #-}

tryAsColor :: forall (v::V) (c1::C) (c2::C) (n::S).
              (Color c1, Color c2) => v c1 n -> Maybe (v c2 n)
tryAsColor x = case eqColorRep of
  Just (ColorsEqual :: ColorsEqual c1 c2) -> Just x
  Nothing -> Nothing

-- like Typeable, this gives a term-level representation of a name color
class Color (c::C) where
  getColorRep :: C

instance Color AtomNameC       where getColorRep = AtomNameC
instance Color DataDefNameC    where getColorRep = DataDefNameC
instance Color TyConNameC      where getColorRep = TyConNameC
instance Color DataConNameC    where getColorRep = DataConNameC
instance Color ClassNameC      where getColorRep = ClassNameC
instance Color InstanceNameC   where getColorRep = InstanceNameC
instance Color MethodNameC     where getColorRep = MethodNameC
instance Color ImpFunNameC     where getColorRep = ImpFunNameC
instance Color ObjectFileNameC where getColorRep = ObjectFileNameC
instance Color ModuleNameC     where getColorRep = ModuleNameC
instance Color PtrNameC        where getColorRep = PtrNameC
instance Color EffectNameC     where getColorRep = EffectNameC
instance Color EffectOpNameC   where getColorRep = EffectOpNameC
instance Color HandlerNameC    where getColorRep = HandlerNameC
-- The instance for Color UnsafeC is purposefully missing! UnsafeC is
-- only used for storing heterogeneously-colored values and we should
-- restore their type before we every try to reflect upon their color!

interpretColor :: C -> (forall c. Color c => ColorProxy c -> a) -> a
interpretColor c cont = case c of
  AtomNameC       -> cont $ ColorProxy @AtomNameC
  DataDefNameC    -> cont $ ColorProxy @DataDefNameC
  TyConNameC      -> cont $ ColorProxy @TyConNameC
  DataConNameC    -> cont $ ColorProxy @DataConNameC
  ClassNameC      -> cont $ ColorProxy @ClassNameC
  InstanceNameC   -> cont $ ColorProxy @InstanceNameC
  MethodNameC     -> cont $ ColorProxy @MethodNameC
  ImpFunNameC     -> cont $ ColorProxy @ImpFunNameC
  ObjectFileNameC -> cont $ ColorProxy @ObjectFileNameC
  ModuleNameC     -> cont $ ColorProxy @ModuleNameC
  PtrNameC        -> cont $ ColorProxy @PtrNameC
  _               -> error "shouldn't reflect over Unsafe colors!"

-- === instances ===

instance SinkableV v => SinkableE (Subst v i) where
  sinkingProofE fresh (Subst f m) =
    Subst (\name -> sinkingProofE fresh $ f name)
          (sinkingProofE fresh m)
  sinkingProofE fresh UnsafeMakeIdentitySubst =
    sinkingProofE fresh $ Subst (fromName . unsafeCoerceE) emptyInFrag

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
  freeVarsE (Abs b e) = freeVarsB b <> hoistFilterNameSet b (freeVarsE e)

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
  {-# INLINE toScopeFrag #-}

instance HoistableE e => HoistableB (LiftB e) where
  freeVarsB (LiftB e) = freeVarsE e
  {-# INLINE freeVarsB #-}

instance (SinkableE e, SubstE v e) => SubstB v (LiftB e) where
  substB env@(_, subst) (LiftB e) cont = case tryApplyIdentitySubst subst e of
    Just e' -> cont env $ LiftB e'
    Nothing -> cont env $ LiftB $ substE env e
  {-# INLINE substB #-}

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
instance Color c => BindsNames (BinderP c ann) where
  toScopeFrag (b :> _) = toScopeFrag b

instance BindsNames b => ProvesExt  (RNest b) where
instance BindsNames b => BindsNames (RNest b) where
  toScopeFrag REmpty = id
  toScopeFrag (RNest rest b) = toScopeFrag rest >>> toScopeFrag b
instance (BindsNames b, SubstB v b, SinkableV v) => SubstB v (RNest b) where
  substB env (RNest bs b) cont =
    substB env bs \env' bs' ->
      substB env' b \env'' b' ->
        cont env'' $ RNest bs' b'
  substB env REmpty cont = cont env REmpty

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
  {-# INLINE fromE #-}
  toE   (ListE pairs) = HashMapE $ HM.fromList $ map fromPairE pairs
  {-# INLINE toE #-}
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

instance HasScope (RecSubst v) where
  toScope = Scope . toScopeFrag . RecSubstFrag . fromRecSubst
  {-# INLINE toScope #-}

instance ProvesExt  (RecSubstFrag v) where
instance BindsNames (RecSubstFrag v) where
  toScopeFrag env = substFragAsScope $ fromRecSubstFrag env
  {-# INLINE toScopeFrag #-}
instance HoistableV v => HoistableB (RecSubstFrag v) where
  freeVarsB (RecSubstFrag env) = freeVarsE (Abs (substFragAsScope env) env)

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

instance Store C
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
instance Store (Scope n)
deriving instance (forall c n. Pretty (v c n)) => Pretty (RecSubstFrag v o o')


-- We often have high-degree sum types that need GenericE instances, and
-- EitherE seems like a natural choice for those. However, if you have 20
-- constructors, injecting the last one into the generic representation
-- requires an unnecessary allocation of 19 RightE constructors! This is
-- why here we define an n-way sum type, so that the different cases can be
-- encoded compactly just by changing the constructor tag.
--
-- There's nothing special about the number 8 (other than that it is a small
-- power of two). We can always change the width as we see fit. But it did seem
-- to balance the amount of boilerplate well.
data EitherE8 (e0::E) (e1::E) (e2::E) (e3::E) (e4::E) (e5::E) (e6::E) (e7::E) (n::S)
  = Case0 (e0 n)
  | Case1 (e1 n)
  | Case2 (e2 n)
  | Case3 (e3 n)
  | Case4 (e4 n)
  | Case5 (e5 n)
  | Case6 (e6 n)
  | Case7 (e7 n)
  deriving (Generic)

type EitherE2 e0 e1                = EitherE8 e0 e1 VoidE VoidE VoidE VoidE VoidE VoidE
type EitherE3 e0 e1 e2             = EitherE8 e0 e1 e2    VoidE VoidE VoidE VoidE VoidE
type EitherE4 e0 e1 e2 e3          = EitherE8 e0 e1 e2    e3    VoidE VoidE VoidE VoidE
type EitherE5 e0 e1 e2 e3 e4       = EitherE8 e0 e1 e2    e3    e4    VoidE VoidE VoidE
type EitherE6 e0 e1 e2 e3 e4 e5    = EitherE8 e0 e1 e2    e3    e4    e5    VoidE VoidE
type EitherE7 e0 e1 e2 e3 e4 e5 e6 = EitherE8 e0 e1 e2    e3    e4    e5    e6    VoidE


instance (AlphaHashableE e0, AlphaHashableE e1, AlphaHashableE e2,
          AlphaHashableE e3, AlphaHashableE e4, AlphaHashableE e5,
          AlphaHashableE e6, AlphaHashableE e7)
            => AlphaHashableE (EitherE8 e0 e1 e2 e3 e4 e5 e6 e7) where
  hashWithSaltE env salt = \case
    Case0 e -> hashWithSaltE env (hashWithSalt salt (0::Int)) e
    Case1 e -> hashWithSaltE env (hashWithSalt salt (1::Int)) e
    Case2 e -> hashWithSaltE env (hashWithSalt salt (2::Int)) e
    Case3 e -> hashWithSaltE env (hashWithSalt salt (3::Int)) e
    Case4 e -> hashWithSaltE env (hashWithSalt salt (4::Int)) e
    Case5 e -> hashWithSaltE env (hashWithSalt salt (5::Int)) e
    Case6 e -> hashWithSaltE env (hashWithSalt salt (6::Int)) e
    Case7 e -> hashWithSaltE env (hashWithSalt salt (7::Int)) e
  {-# INLINE hashWithSaltE #-}

instance (SinkableE e0, SinkableE e1, SinkableE e2,
          SinkableE e3, SinkableE e4, SinkableE e5,
          SinkableE e6, SinkableE e7)
            => SinkableE (EitherE8 e0 e1 e2 e3 e4 e5 e6 e7) where
  sinkingProofE fresh = \case
    Case0 e -> Case0 $ sinkingProofE fresh e
    Case1 e -> Case1 $ sinkingProofE fresh e
    Case2 e -> Case2 $ sinkingProofE fresh e
    Case3 e -> Case3 $ sinkingProofE fresh e
    Case4 e -> Case4 $ sinkingProofE fresh e
    Case5 e -> Case5 $ sinkingProofE fresh e
    Case6 e -> Case6 $ sinkingProofE fresh e
    Case7 e -> Case7 $ sinkingProofE fresh e

instance (HoistableE e0, HoistableE e1, HoistableE e2,
          HoistableE e3, HoistableE e4, HoistableE e5,
          HoistableE e6, HoistableE e7)
            => HoistableE (EitherE8 e0 e1 e2 e3 e4 e5 e6 e7) where
  freeVarsE = \case
    Case0 e -> freeVarsE e
    Case1 e -> freeVarsE e
    Case2 e -> freeVarsE e
    Case3 e -> freeVarsE e
    Case4 e -> freeVarsE e
    Case5 e -> freeVarsE e
    Case6 e -> freeVarsE e
    Case7 e -> freeVarsE e
  {-# INLINE freeVarsE #-}

instance (SubstE v e0, SubstE v e1, SubstE v e2,
          SubstE v e3, SubstE v e4, SubstE v e5,
          SubstE v e6, SubstE v e7)
            => SubstE v (EitherE8 e0 e1 e2 e3 e4 e5 e6 e7) where
  substE env = \case
    Case0 e -> Case0 $ substE env e
    Case1 e -> Case1 $ substE env e
    Case2 e -> Case2 $ substE env e
    Case3 e -> Case3 $ substE env e
    Case4 e -> Case4 $ substE env e
    Case5 e -> Case5 $ substE env e
    Case6 e -> Case6 $ substE env e
    Case7 e -> Case7 $ substE env e
  {-# INLINE substE #-}

instance (AlphaEqE e0, AlphaEqE e1, AlphaEqE e2,
          AlphaEqE e3, AlphaEqE e4, AlphaEqE e5,
          AlphaEqE e6, AlphaEqE e7)
            => AlphaEqE (EitherE8 e0 e1 e2 e3 e4 e5 e6 e7) where
  alphaEqE (Case0 e1) (Case0 e2) = alphaEqE e1 e2
  alphaEqE (Case1 e1) (Case1 e2) = alphaEqE e1 e2
  alphaEqE (Case2 e1) (Case2 e2) = alphaEqE e1 e2
  alphaEqE (Case3 e1) (Case3 e2) = alphaEqE e1 e2
  alphaEqE (Case4 e1) (Case4 e2) = alphaEqE e1 e2
  alphaEqE (Case5 e1) (Case5 e2) = alphaEqE e1 e2
  alphaEqE (Case6 e1) (Case6 e2) = alphaEqE e1 e2
  alphaEqE (Case7 e1) (Case7 e2) = alphaEqE e1 e2
  alphaEqE _          _          = zipErr

instance (Store (e0 n), Store (e1 n), Store (e2 n),
          Store (e3 n), Store (e4 n), Store (e5 n),
          Store (e6 n), Store (e7 n))
            => Store (EitherE8 e0 e1 e2 e3 e4 e5 e6 e7 n)

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
  | InstanceNameC
  | MethodNameC
  | ImpFunNameC
  | ObjectFileNameC
  | ModuleNameC
  | PtrNameC
  | EffectNameC
  | EffectOpNameC
  | HandlerNameC
  | UnsafeC
    deriving (Eq, Ord, Generic, Show)

type E = S -> *       -- expression-y things, covariant in the S param
type B = S -> S -> *  -- binder-y things, covariant in the first param and
                      -- contravariant in the second. These are things like
                      -- `Binder n l` or `Decl n l`, that bind the names in
                      -- `ScopeFrag n l`, extending `n` to `l`. Their free
                      -- name are in `Scope n`. We sometimes call `n` the
                      -- "outside scope" and "l" the "inside scope".
type V = C -> E       -- value-y things that we might look up in an environment
                      -- with a `Name c n`, parameterized by the name's color.

-- We use SubstItem for ColorRep to be able ot unsafeCoerce scopes into name sets in O(1).
type ColorRep = SubstItem GHC.Exts.Any UnsafeS
type NameSet (n::S) = RawNameMap ColorRep

-- ScopeFrag is a SubstFrag that can contain _any_ V-kinded thing.
-- Semantically it is equivalent to M.Map RawName [C].
--
-- WARNING!
-- The "any" part is really important, beacuse we often use unsafeCoerce
-- to cheaply construct scopes out of substitutions. After composing a few of
-- those, there may be multiple different types of Vs embeded here. You should
-- never assume _anything_ about those and it is not safe to cast them back to
-- any other V. The only allowed operation is looking up colors embedded in SubstItem.
newtype ScopeFrag (n::S) (l::S) = UnsafeScopeFromSubst (SubstFrag GHC.Exts.Any n l UnsafeS)
                                  deriving Generic
newtype Scope (n::S) = Scope { fromScope :: ScopeFrag VoidS n }  deriving Generic

pattern UnsafeMakeScopeFrag :: RawNameMap ColorRep -> ScopeFrag n l
pattern UnsafeMakeScopeFrag m = UnsafeScopeFromSubst (UnsafeMakeSubst m)
{-# COMPLETE UnsafeMakeScopeFrag #-}

instance Category ScopeFrag where
  id = UnsafeMakeScopeFrag mempty
  {-# INLINE id #-}
  -- Note that `(.)` is flipped `(>>>)`, so s2 (lower scope) is the first arg.
  UnsafeMakeScopeFrag s2 . UnsafeMakeScopeFrag s1 =
    UnsafeMakeScopeFrag $ R.unionWith takeLeftNonDistinct s2 s1
  {-# INLINE (.) #-}

instance Color c => BindsNames (NameBinder c) where
  toScopeFrag (UnsafeMakeBinder v) = substFragAsScope $
    UnsafeMakeSubst $ R.singleton v $ toSubstItem DistinctName
      (TrulyUnsafe.unsafeCoerce UnitV :: GHC.Exts.Any c VoidS)

absurdNameFunction :: Name v VoidS -> a
absurdNameFunction v = error $ "Void names shouldn't exist: " ++ show v

scopeFragToSubstFrag :: forall v i i' o
                      . (forall c. Color c => Name c (i:=>:i') -> v c o)
                     -> ScopeFrag i i' -> SubstFrag v i i' o
scopeFragToSubstFrag f (UnsafeScopeFromSubst m) = fmapSubstFrag (\n _ -> f n) m

newtype Name (c::C)  -- Name color
             (n::S)  -- Scope parameter
  = UnsafeMakeName RawName
    deriving (Show, Eq, Ord, Pretty, HasNameHint, Generic, Store)

newtype NameBinder (c::C)  -- name color
                   (n::S)  -- scope above the binder
                   (l::S)  -- scope under the binder (`l` for "local")
  = UnsafeMakeBinder RawName
    deriving (Show, Pretty, HasNameHint, Generic, Store)

newBinder :: Color c => NameHint -> (forall l. NameBinder c VoidS l -> a) -> a
newBinder hint cont = cont $ UnsafeMakeBinder $ rawNameFromHint hint

-- Closed binder-name pair. The name isn't fresh and it doesn't pretend to be.
-- It's intended for subsequent refreshing.
newName :: Color c => NameHint -> Abs (NameBinder c) (Name c) n
newName hint = sinkFromTop $ newBinder hint \b -> Abs b $ binderName b

-- uses the monad just to diambiguate the scope parameter
newNameM :: Monad1 m => Color c => NameHint -> m n (Abs (NameBinder c) (Name c) n)
newNameM hint = return $ newName hint

newNames :: Color c => Int -> Abs (Nest (NameBinder c)) (ListE (Name c)) n
newNames n = do
  let ns = rawNames n
  let vs = map UnsafeMakeName ns
  let bs = unsafeListToNest $ map UnsafeMakeBinder ns
  unsafeCoerceE $ Abs bs $ ListE vs

withFresh :: forall n c a. (Distinct n, Color c)
          => NameHint -> Scope n
          -> (forall l. DExt n l => NameBinder c n l -> a) -> a
withFresh hint (Scope (UnsafeMakeScopeFrag scope)) cont =
  withFabricatedDistinct @UnsafeS $
    withFabricatedExt @n @UnsafeS $
      cont $ (UnsafeMakeBinder (freshRawName hint scope) :: NameBinder c n UnsafeS)
{-# INLINE withFresh #-}

-- proves that the names in n are distinct
class Distinct (n::S)
type DExt n l = (Distinct l, Ext n l)

fabricateDistinctEvidence :: forall n. DistinctEvidence n
fabricateDistinctEvidence =
  withFabricatedDistinct @n Distinct
{-# INLINE fabricateDistinctEvidence #-}

data DistinctEvidence (n::S) where
  Distinct :: Distinct n => DistinctEvidence n

instance Distinct VoidS

withFabricatedDistinct :: forall n a. (Distinct n => a) -> a
withFabricatedDistinct cont = fromWrapWithDistinct
 ( TrulyUnsafe.unsafeCoerce ( WrapWithDistinct cont :: WrapWithDistinct n     a
                                                  ) :: WrapWithDistinct VoidS a)
{-# INLINE withFabricatedDistinct #-}

newtype WrapWithDistinct n r =
  WrapWithDistinct { fromWrapWithDistinct :: Distinct n => r }


withSubscopeDistinct :: forall n l b a.
                        (Distinct l, ProvesExt b)
                     => b n l -> ((Ext n l, Distinct n) => a) -> a
withSubscopeDistinct b cont =
  withExtEvidence' (toExtEvidence b) $
    withFabricatedDistinct @n $
      cont
{-# INLINE withSubscopeDistinct #-}

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
getExtEvidence = ExtEvidence
{-# INLINE getExtEvidence #-}

absurdExtEvidence :: ExtEvidence VoidS n
absurdExtEvidence = fabricateExtEvidence
{-# INLINE absurdExtEvidence #-}

-- We give this one a ' because the more general one defined in Name is the
-- version we usually want to use.
withExtEvidence' :: forall n l a. ExtEvidence n l -> (Ext n l => a) -> a
withExtEvidence' ExtEvidence cont = cont
{-# INLINE withExtEvidence' #-}

withFabricatedExt :: forall n l a. (Ext n l => a) -> a
withFabricatedExt cont = fromWrapWithExt
 ( TrulyUnsafe.unsafeCoerce ( WrapWithExt cont :: WrapWithExt n     l     a
                                             ) :: WrapWithExt VoidS VoidS a)
{-# INLINE withFabricatedExt #-}

fabricateExtEvidence :: forall n l. ExtEvidence n l
fabricateExtEvidence = withFabricatedExt @n @l ExtEvidence
{-# INLINE fabricateExtEvidence #-}

newtype WrapWithExt n l r =
  WrapWithExt { fromWrapWithExt :: Ext n l => r }

data ExtEvidence (n::S) (l::S) where
  ExtEvidence :: (Ext n l) => ExtEvidence n l

instance Category ExtEvidence where
  id = ExtEvidence
  {-# INLINE id #-}
  ExtEvidence . ExtEvidence = ExtEvidence
  {-# INLINE (.) #-}

sink :: (SinkableE e, DExt n l) => e n -> e l
sink x = unsafeCoerceE x
{-# INLINE sink #-}

sinkR :: SinkableE e => e (n:=>:l) -> e l
sinkR = unsafeCoerceE
{-# INLINE sinkR #-}

sinkList :: (SinkableE e, DExt n l) => [e n] -> [e l]
sinkList = fromListE . sink . ListE
{-# INLINE sinkList #-}

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
  sinkingProofE _ _ = fabricateExtEvidence

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
  withFabricatedDistinct @UnsafeS $
    ClosedWithScope scope $ unsafeCoerceE e
  where scope = (Scope $ UnsafeMakeScopeFrag $ freeVarsE e) :: Scope UnsafeS

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

liftHoistExcept' :: Fallible m => String -> HoistExcept a -> m a
liftHoistExcept' _ (HoistSuccess x) = return x
liftHoistExcept' msg (HoistFailure vs) =
  throw EscapedNameErr $ (pprint vs) ++ "\n" ++ msg

ignoreHoistFailure :: HasCallStack => HoistExcept a -> a
ignoreHoistFailure (HoistSuccess x) = x
ignoreHoistFailure (HoistFailure _) = error "hoist failure"

hoist :: (BindsNames b, HoistableE e) => b n l -> e l -> HoistExcept (e n)
hoist b e =
  case R.disjoint fvs frag of
    True  -> HoistSuccess $ unsafeCoerceE e
    False -> HoistFailure $ nameSetRawNames $ R.intersection fvs frag
  where
    UnsafeMakeScopeFrag frag = toScopeFrag b
    fvs = freeVarsE e

hoistToTop :: HoistableE e => e n -> HoistExcept (e VoidS)
hoistToTop e =
  case nameSetRawNames $ freeVarsE e of
    []          -> HoistSuccess $ unsafeCoerceE e
    leakedNames -> HoistFailure leakedNames

sinkFromTop :: SinkableE e => e VoidS -> e n
sinkFromTop = unsafeCoerceE
{-# INLINE sinkFromTop #-}

freeVarsList :: (HoistableE e, Color c) => e n -> [Name c n]
freeVarsList e = nameSetToList $ freeVarsE e

nameSetToList :: forall c n. Color c => NameSet n -> [Name c n]
nameSetToList nameSet =
  catMaybes $ flip map (R.toList nameSet) \(rawName, item) ->
    case fromSubstItem item of
      Nothing -> Nothing
      Just (_ :: GHC.Exts.Any c UnsafeS) -> Just $ UnsafeMakeName rawName

toNameSet :: ScopeFrag n l -> NameSet l
toNameSet (UnsafeMakeScopeFrag s) = s

nameSetRawNames :: NameSet n -> [RawName]
nameSetRawNames m = R.keys m

isInNameSet :: Name c n -> NameSet n -> Bool
isInNameSet v ns = getRawName v `R.member` ns

isFreeIn :: HoistableE e => Name c n -> e n -> Bool
isFreeIn v e = getRawName v `R.member` freeVarsE e

anyFreeIn :: HoistableE e => [Name c n] -> e n -> Bool
anyFreeIn vs e =
  not $ R.disjoint (R.fromList $ map (\v -> (getRawName v, ())) vs)
                   (freeVarsE e)

exchangeBs :: (Distinct l, BindsNames b1, SinkableB b1, HoistableB b2)
              => PairB b1 b2 n l
              -> HoistExcept (PairB b2 b1 n l)
exchangeBs (PairB b1 b2) =
  case R.disjoint fvs2 frag of
    True  -> HoistSuccess $ PairB (unsafeCoerceB b2) (unsafeCoerceB b1)
    False -> HoistFailure $ nameSetRawNames $ R.intersection fvs2 frag
  where
    UnsafeMakeScopeFrag frag = toScopeFrag b1
    fvs2 = freeVarsB b2

hoistFilterNameSet :: BindsNames b => b n l -> NameSet l -> NameSet n
hoistFilterNameSet b nameSet =
  unsafeCoerceNameSet $ nameSet `R.difference` frag
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
  freeVarsE name = R.singleton (getRawName name) $
    toSubstItem DistinctName (TrulyUnsafe.unsafeCoerce UnitV :: GHC.Exts.Any c UnsafeS)

instance (HoistableB b1, HoistableB b2) => HoistableB (PairB b1 b2) where
  freeVarsB (PairB b1 b2) =
    freeVarsB b1 <> hoistFilterNameSet b1 (freeVarsB b2)

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

newtype SubstFrag
  (v ::V)  -- env payload, as a function of the name's color
  (i ::S)  -- starting scope parameter for names we can look up in this env
  (i'::S)  -- ending   scope parameter for names we can look up in this env
  (o ::S)  -- scope parameter for the values stored in the env
  = UnsafeMakeSubst (RawNameMap (SubstItem v o))
  deriving (Generic)
deriving instance (forall c. Show (v c o)) => Show (SubstFrag v i i' o)

data SubstItem (v::V) (n::S) = SubstItem {-# UNPACK #-} !SubstItemFlags (v UnsafeC n)
deriving instance (forall c. Show (v c n)) => Show (SubstItem v n)

fromSubstItem :: forall c v o. Color c => SubstItem v o -> Maybe (v c o)
fromSubstItem (SubstItem f (val :: v c' o)) =
  case (substItemColor f) == getColorRep @c of
    True  -> Just (TrulyUnsafe.unsafeCoerce val :: v c o)
    False -> Nothing
{-# INLINE fromSubstItem #-}

toSubstItem :: forall c v o. Color c => FragNameDistinctness -> v c o -> SubstItem v o
toSubstItem d v = SubstItem (packSubstItemFlags d $ getColorRep @c) (unsafeCoerceVC v)
{-# INLINE toSubstItem #-}

fromSubstItemPoly :: forall v o a. SubstItem v o -> (forall c. Color c => v c o -> a) -> a
fromSubstItemPoly (SubstItem f v) cont =
  interpretColor (substItemColor f) \(ColorProxy :: ColorProxy c) -> cont (unsafeCoerceVC @c v)
{-# INLINE fromSubstItemPoly #-}

-- === Packed representation of SubstItem properties ===
-- We use the MSB to encode shadowing: a name has been shadowed in the current
-- fragment if the bit is set. The rest of the bits are used to encode the tag
-- of the C constructor (representing name's color).

newtype SubstItemFlags = SubstItemFlags Int deriving (Show, Store)

shadowBit :: Int
shadowBit = finiteBitSize @Int undefined - 1
{-# INLINE shadowBit #-}

substItemColor :: SubstItemFlags -> C
substItemColor (SubstItemFlags f) = tagToEnum# tag
  where !(I# tag) = f `clearBit` shadowBit
{-# INLINE substItemColor #-}

packSubstItemFlags :: FragNameDistinctness -> C -> SubstItemFlags
packSubstItemFlags d c = SubstItemFlags $ case d of DistinctName -> f'; ShadowingName -> f' `setBit` shadowBit
  where f' = I# (dataToTag# c)
{-# INLINE packSubstItemFlags #-}

undistinctItem :: SubstItemFlags -> SubstItemFlags
undistinctItem (SubstItemFlags f) = SubstItemFlags $ f `setBit` shadowBit
{-# INLINE undistinctItem #-}

data FragNameDistinctness = DistinctName | ShadowingName deriving (Eq)

itemDistinctness :: SubstItem v n -> FragNameDistinctness
itemDistinctness (SubstItem (SubstItemFlags f) _) = case f `testBit` shadowBit of True -> ShadowingName; False -> DistinctName
{-# INLINE itemDistinctness #-}

takeLeftNonDistinct :: SubstItem v n -> SubstItem v n -> SubstItem v n
takeLeftNonDistinct (SubstItem f v) _ = SubstItem (undistinctItem f) v

-- === environments and scopes ===

lookupSubstFrag :: Color c => SubstFrag v i i' o -> Name c (i:=>:i') -> v c o
lookupSubstFrag (UnsafeMakeSubst m) (UnsafeMakeName rawName) =
  case R.lookup rawName m of
    Just d -> case fromSubstItem d of
      Nothing -> error "Wrong name color (should never happen)"
      Just x -> x
    _ -> error "Subst lookup failed (this should never happen)"

-- Just for debugging
lookupSubstFragRaw :: SubstFrag v i i' o -> RawName -> Maybe (v UnsafeC o)
lookupSubstFragRaw (UnsafeMakeSubst m) rawName =
  R.lookup rawName m <&> \(SubstItem _ v) -> v

instance InFrag (SubstFrag v) where
  emptyInFrag = UnsafeMakeSubst mempty
  {-# INLINE emptyInFrag #-}
  catInFrags (UnsafeMakeSubst m1) (UnsafeMakeSubst m2) =
    UnsafeMakeSubst (R.unionWith takeLeftNonDistinct m2 m1)
  {-# INLINE catInFrags #-}

singletonSubst :: Color c => NameBinder c i i' -> v c o -> SubstFrag v i i' o
singletonSubst (UnsafeMakeBinder name) x =
  UnsafeMakeSubst $ R.singleton name $ toSubstItem DistinctName x
{-# INLINE singletonSubst #-}

fmapSubstFrag :: (forall c. Color c => Name c (i:=>:i') -> v c o -> v' c o')
              -> SubstFrag v i i' o -> SubstFrag v' i i' o'
fmapSubstFrag f (UnsafeMakeSubst m) =
  UnsafeMakeSubst $ flip R.mapWithKey m $ \k item@(SubstItem fs _) ->
    SubstItem fs $ fromSubstItemPoly item \v ->
      unsafeCoerceVC @UnsafeC $ f (UnsafeMakeName k) v

substFragAsScope :: forall v i i' o. SubstFrag v i i' o -> ScopeFrag i i'
substFragAsScope m = UnsafeMakeScopeFrag $ TrulyUnsafe.unsafeCoerce m

-- === garbage collection ===

collectGarbage :: (HoistableV v, HoistableE e)
               => Distinct l => RecSubstFrag v n l -> (Name c l -> NameSet l) -> e l
               -> (forall l'. Distinct l' => RecSubstFrag v n l' -> e l' -> a)
               -> a
collectGarbage (RecSubstFrag (UnsafeMakeSubst env)) extraDeps e cont = do
  let seedNames = R.keys $ freeVarsE e
  let accessibleNames = transitiveClosure getParents seedNames
  let env' = RecSubstFrag $ UnsafeMakeSubst $ R.restrictKeys env accessibleNames
  cont env' $ unsafeCoerceE e
  where
    getParents :: RawName -> [RawName]
    getParents name = case R.lookup name env of
      Nothing   -> []
#ifdef DEX_DEBUG
      Just item | itemDistinctness item == ShadowingName ->
        error "shouldn't be possible, due to Distinct constraint"
#endif
      Just item -> (R.keys $ fromSubstItemPoly item freeVarsE) <> (R.keys $ extraDeps $ UnsafeMakeName name)

-- === iterating through env pairs ===

-- Taking this binder apart is unsafe, because converting a nest of RepeatedNameBinders
-- into a nest of their consecutive NameBinders is expressible in the safe fragment, but
-- it doesn't preserve the multiplicity of names in a scope fragment!
data RepeatedNameBinder (c::C) (n::S) (l::S) where
  UnsafeRepeatedNameBinder :: !FragNameDistinctness -> NameBinder c n l -> RepeatedNameBinder c n l
instance Color c => SinkableB (RepeatedNameBinder c) where
  sinkingProofB _ _ _ = todoSinkableProof
instance Color c => ProvesExt (RepeatedNameBinder c) where
  toExtEvidence (UnsafeRepeatedNameBinder _ b) = toExtEvidence b
  {-# INLINE toExtEvidence #-}
instance Color c => BindsNames (RepeatedNameBinder c) where
  toScopeFrag (UnsafeRepeatedNameBinder _ b) = toScopeFrag b
  {-# INLINE toScopeFrag #-}
instance (Color c, FromName v, SinkableV v) => SubstB v (RepeatedNameBinder c) where
  substB env (UnsafeRepeatedNameBinder d b) cont = substB env b \env' b' ->
    cont env' $ UnsafeRepeatedNameBinder d b'
  {-# INLINE substB #-}
instance Color c => BindsAtMostOneName (RepeatedNameBinder c) c where
  (UnsafeRepeatedNameBinder _ b) @> v = b @> v
  {-# INLINE (@>) #-}
instance Color c => BindsOneName (RepeatedNameBinder c) c where
  binderName (UnsafeRepeatedNameBinder _ b) = binderName b
  {-# INLINE binderName #-}
instance Color c => HasNameHint (RepeatedNameBinder c n l) where
  getNameHint (UnsafeRepeatedNameBinder _ b) = getNameHint b
  {-# INLINE getNameHint #-}


data SubstPair (v::V) (o::S) (i::S) (i'::S) where
  SubstPair :: Color c => {-# UNPACK #-} !(RepeatedNameBinder c i i') -> v c o -> SubstPair v o i i'

toSubstPairs :: forall v i i' o . SubstFrag v i i' o -> Nest (SubstPair v o) i i'
toSubstPairs (UnsafeMakeSubst m) =
  go $ R.toList m <&> \(rawName, item) ->
    fromSubstItemPoly item \v ->
      SubstPair (UnsafeRepeatedNameBinder (itemDistinctness item) (UnsafeMakeBinder rawName)) v
  where
    go :: [SubstPair v o UnsafeS UnsafeS] -> Nest (SubstPair v o) i i'
    go [] = unsafeCoerceB Empty
    go (SubstPair b val : rest) = Nest (SubstPair (unsafeCoerceB b) val) $ go rest

data WithRenamer e i o where
  WithRenamer :: SubstFrag Name i i' o -> e i' -> WithRenamer e i o

instance Category (Nest b) where
  id = Empty
  {-# INLINE id #-}
  (.) = flip joinNest
  {-# INLINE (.) #-}

instance Category (RNest b) where
  id = REmpty
  {-# INLINE id #-}
  (.) = flip joinRNest
  {-# INLINE (.) #-}

instance ProvesExt (SubstPair v o) where
  toExtEvidence (SubstPair b _) = toExtEvidence b

instance BindsNames (SubstPair v o) where
  toScopeFrag (SubstPair b _) = toScopeFrag b

-- === instances ===

instance (forall c. Pretty (v c n)) => Pretty (SubstItem v n) where
  pretty (SubstItem _ val) = pretty val

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
{-# NOINLINE [1] unsafeCoerceE #-}

unsafeCoerceB :: forall (b::B) n l n' l' . b n l -> b n' l'
unsafeCoerceB = TrulyUnsafe.unsafeCoerce
{-# NOINLINE [1] unsafeCoerceB #-}

unsafeCoerceVC :: forall c' (v::V) c o. v c o -> v c' o
unsafeCoerceVC = TrulyUnsafe.unsafeCoerce
{-# NOINLINE [1] unsafeCoerceVC #-}

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

instance SinkableB b => SinkableB (RNest b) where
  sinkingProofB fresh REmpty cont = cont fresh REmpty
  sinkingProofB fresh (RNest rest b) cont =
    sinkingProofB fresh rest \fresh' rest' ->
      sinkingProofB fresh' b \fresh'' b' ->
        cont fresh'' (RNest rest' b')

instance HoistableB b => HoistableB (RNest b) where
  freeVarsB REmpty = mempty
  freeVarsB (RNest rest b) = freeVarsB (PairB rest b)

instance (forall c n. Pretty (v c n)) => Pretty (SubstFrag v i i' o) where
  pretty (UnsafeMakeSubst m) =
    vcat [ pretty v <+> "@>" <+> pretty x | (v, SubstItem _ x) <- R.toList m ]

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

instance (forall c. Color c => Store (v c n)) => Store (SubstItem v n) where
  size = VarSize \item@(SubstItem f _) ->
    getSize f + fromSubstItemPoly item getSize

  peek = do
    f <- peek
    interpretColor (substItemColor f) \(ColorProxy :: ColorProxy c) -> do
      v :: v c n <- peek
      return $ SubstItem f (unsafeCoerceVC v)

  poke item@(SubstItem f _) = do
    poke f
    fromSubstItemPoly item poke

data StoreNothingV (c::C) (n::S) = StoreNothingV

instance Store (StoreNothingV c n) where
  size = ConstSize 0
  peek = return StoreNothingV
  poke = const $ return ()

pokeableScopeFrag :: SubstFrag GHC.Exts.Any n l o -> SubstFrag StoreNothingV n l o
pokeableScopeFrag = TrulyUnsafe.unsafeCoerce

fromPeekedScopeFrag :: SubstFrag StoreNothingV n l o -> SubstFrag GHC.Exts.Any n l o
fromPeekedScopeFrag = TrulyUnsafe.unsafeCoerce

instance Store (ScopeFrag n l) where
  size = VarSize \(UnsafeScopeFromSubst s) -> getSize $ pokeableScopeFrag s
  peek = UnsafeScopeFromSubst . fromPeekedScopeFrag <$> peek
  poke (UnsafeScopeFromSubst s) = poke $ pokeableScopeFrag s

instance SinkableV v => SinkableE (SubstItem v) where
  sinkingProofE = todoSinkableProof

instance (forall c. Color c => Store (v c o))
         => Store (SubstFrag v i i' o) where

instance ( Store   (b UnsafeS UnsafeS)
         , Generic (b UnsafeS UnsafeS) ) => Store (Nest b n l)

instance Functor HoistExcept where
  fmap = liftM
  {-# INLINE fmap #-}

instance Applicative HoistExcept where
  pure x = HoistSuccess x
  {-# INLINE pure #-}
  liftA2 = liftM2
  {-# INLINE liftA2 #-}

instance Monad HoistExcept where
  return = pure
  {-# INLINE return #-}
  HoistFailure vs >>= _ = HoistFailure vs
  HoistSuccess x >>= f = f x
  {-# INLINE (>>=) #-}

-- === extra data structures ===

newtype NameMap (c::C) (a:: *) (n::S) = UnsafeNameMap (RawNameMap a)
                                 deriving (Eq, Semigroup, Monoid)

hoistFilterNameMap :: BindsNames b => b n l -> NameMap c a l -> NameMap c a n
hoistFilterNameMap b (UnsafeNameMap raw) =
  UnsafeNameMap $ raw `R.difference` frag
  where UnsafeMakeScopeFrag frag = toScopeFrag b
{-# INLINE hoistFilterNameMap #-}

insertNameMap :: Name c n -> a -> NameMap c a n -> NameMap c a n
insertNameMap (UnsafeMakeName n) x (UnsafeNameMap raw) = UnsafeNameMap $ R.insert n x raw
{-# INLINE insertNameMap #-}

lookupNameMap :: Name c n -> NameMap c a n -> Maybe a
lookupNameMap (UnsafeMakeName n) (UnsafeNameMap raw) = R.lookup n raw
{-# INLINE lookupNameMap #-}

singletonNameMap :: Name c n -> a -> NameMap c a n
singletonNameMap (UnsafeMakeName n) x = UnsafeNameMap $ R.singleton n x
{-# INLINE singletonNameMap #-}

toListNameMap :: NameMap c a n -> [(Name c n, a)]
toListNameMap (UnsafeNameMap raw) = R.toList raw <&> \(r, x) -> (UnsafeMakeName r, x)
{-# INLINE toListNameMap #-}

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
