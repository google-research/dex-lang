-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DefaultSignatures #-}

module SaferNames.Syntax (
    Type, Kind, BaseType (..), ScalarBaseType (..), Except,
    EffectP (..), Effect, UEffect, RWS (..), EffectRowP (..), EffectRow, UEffectRow,
    Binder, Block (..), Decl (..), DeclBinding (..),
    Expr (..), Atom (..), Arrow (..), PrimTC (..), Abs (..),
    PrimExpr (..), PrimCon (..), LitVal (..), PrimEffect (..), PrimOp (..), PrimHof (..),
    LamBinding (..), LamBinder (..), LamExpr (..),
    PiBinding (..), PiBinder (..),
    PiType (..), LetAnn (..), SomeDecl (..),
    BinOp (..), UnOp (..), CmpOp (..), SourceMap (..), LitProg,
    ForAnn (..), Val, Op, Con, Hof, TC, Module (..), UModule (..),
    ClassDef (..), EvaluatedModule (..), SynthCandidates (..), Bindings (..), TopState,
    BindsBindings (..), BindsOneAtomName (..), WithBindings (..),
    DataConRefBinding (..), AltP, Alt, AtomBinding (..), SolverBinding (..),
    SubstE (..), SubstB (..), Ptr, PtrType,
    AddressSpace (..), Device (..), showPrimName, strToPrimName, primNameToStr,
    Direction (..), Limit (..), DataDef (..), DataConDef (..), Nest (..), IndexStructure,
    mkConsList, mkConsListTy, fromConsList, fromConsListTy, fromLeftLeaningConsListTy,
    mkBundle, mkBundleTy, BundleDesc,
    BaseMonoidP (..), BaseMonoid, getIntLit, getFloatLit, sizeOf, ptrSize, vectorWidth,
    IRVariant (..), SubstVal (..), AtomName, DataDefName, ClassName, AtomSubstVal,
    SourceName, SourceNameOr (..), UVar (..), UBinder (..),
    UExpr, UExpr' (..), UConDef, UDataDef (..), UDataDefTrail (..), UDecl (..),
    ULamExpr (..), UPiExpr (..), UDeclExpr (..), UForExpr (..), UAlt (..),
    UPat, UPat' (..), UPatAnn (..), UPatAnnArrow (..),
    UMethodDef (..), UAnnBinder (..),
    WithSrcE (..), WithSrcB (..), srcPos,
    SourceBlock (..), SourceBlock' (..), EnvQuery (..),
    SourceUModule (..), UMethodType(..), UType, ExtLabeledItemsE (..),
    CmdName (..), LogLevel (..), PassName, OutFormat (..), NamedDataDef,
    BindingsReader (..), BindingsExtender (..),  Binding (..),
    ToBinding (..), refreshBinders, refreshBindersI, withFreshBinder,
    withFreshLamBinder, withFreshPiBinder, piBinderToLamBinder,
    BindingsFrag (..), lookupBindings, lookupBindingsPure, lookupSourceMap,
    getSourceMapM, updateBindings, runBindingsReaderT,
    BindingsReaderM, runBindingsReaderM,
    BindingsReaderT (..), BindingsReader2, BindingsExtender2,
    getDB, DistinctBindings (..),
    naryNonDepPiType, nonDepPiType, fromNonDepPiType, fromNaryNonDepPiType,
    considerNonDepPiType,
    fromNonDepTabTy, binderType, atomBindingType, getProjection,
    applyIntBinOp, applyIntCmpOp, applyFloatBinOp, applyFloatUnOp,
    piArgType, piArrow, extendEffRow,
    bindingsFragToSynthCandidates,
    getSynthCandidatesM, getAllowedEffects, withAllowedEffects, todoInjectableProof,
    FallibleT1, runFallibleT1,
    pattern IdxRepTy, pattern IdxRepVal, pattern TagRepTy,
    pattern TagRepVal, pattern Word8Ty,
    pattern UnitTy, pattern PairTy,
    pattern FixedIntRange, pattern Fin, pattern RefTy, pattern RawRefTy,
    pattern BaseTy, pattern PtrTy, pattern UnitVal,
    pattern PairVal, pattern TyKind,
    pattern Pure, pattern LabeledRowKind, pattern EffKind, pattern UPatIgnore,
    pattern IntLitExpr, pattern FloatLitExpr, pattern ProdTy, pattern ProdVal,
    pattern TabTyAbs,
    pattern SumTy, pattern SumVal, pattern MaybeTy, pattern BinaryFunTy,
    pattern NothingAtom, pattern JustAtom,
    (-->), (?-->), (--@), (==>) ) where

import Data.Foldable (toList, fold)
import Control.Applicative
import Control.Monad.Except hiding (Except)
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.Writer.Strict (Writer, execWriter, tell)
import qualified Control.Monad.Trans.Except as MTE
import qualified Data.List.NonEmpty    as NE
import qualified Data.Map.Strict       as M
import qualified Data.Set              as S
import Data.Int
import Data.String (IsString, fromString)
import Data.Text.Prettyprint.Doc (Pretty (..), hardline, (<+>))
import Data.Word
import Foreign.Ptr
import Data.Maybe (fromJust)

import GHC.Generics (Generic (..))
import Data.Store (Store)

import Syntax
  ( LetAnn (..), IRVariant (..)
  , PrimExpr (..), PrimTC (..), PrimCon (..), PrimOp (..), PrimHof (..)
  , BaseMonoid, BaseMonoidP (..), PrimEffect (..), BinOp (..), UnOp (..)
  , CmpOp (..), Direction (..)
  , ForAnn (..), Limit (..), strToPrimName, primNameToStr, showPrimName
  , BlockId, ReachedEOF, ModuleName, CmdName (..), LogLevel (..)
  , RWS (..), LitVal (..), ScalarBaseType (..), BaseType (..)
  , AddressSpace (..), Device (..), PtrType, sizeOf, ptrSize, vectorWidth
  , PassName, OutFormat (..), Result (..))

import SaferNames.Name
import Err
import LabeledItems
import Util ((...))

-- === core IR ===

data Atom (n::S) =
   Var (AtomName n)
 | Lam (LamExpr n)
 | Pi  (PiType  n)
   -- SourceName is purely for printing
 | DataCon SourceName (NamedDataDef n) [Atom n] Int [Atom n]
 | TypeCon (NamedDataDef n) [Atom n]
 | LabeledRow (ExtLabeledItems (Type n) (AtomName n))
 | Record (LabeledItems (Atom n))
 | RecordTy  (ExtLabeledItems (Type n) (AtomName n))
 | Variant   (ExtLabeledItems (Type n) (AtomName n)) Label Int (Atom n)
 | VariantTy (ExtLabeledItems (Type n) (AtomName n))
 | Con (Con n)
 | TC  (TC  n)
 | Eff (EffectRow n)
 | ACase (Atom n) [AltP Atom n] (Type n)
   -- single-constructor only for now
 | DataConRef (NamedDataDef n) [Atom n] (EmptyAbs (Nest DataConRefBinding) n)
 | BoxedRef (Atom n) (Block n) (Abs Binder Atom n)  -- ptr, size, binder/body
 -- access a nested member of a binder
 -- XXX: Variable name must not be an alias for another name or for
 -- a statically-known atom. This is because the variable name used
 -- here may also appear in the type of the atom. (We maintain this
 -- invariant during substitution and in Builder.hs.)
 | ProjectElt (NE.NonEmpty Int) (AtomName n)
   deriving (Show, Generic)

data Expr n =
   App (Atom n) (Atom n)
 | Case (Atom n) [Alt n] (Type n)
 | Atom (Atom n)
 | Op  (Op  n)
 | Hof (Hof n)
   deriving (Show, Generic)

-- We inline the definition for compatibility with the unsafe IR.
-- TODO: remove once we don't need the bridge anymore
type NamedDataDef n = (DataDefName n, DataDef n)

data DeclBinding n = DeclBinding LetAnn (Type n) (Expr n)
     deriving (Show, Generic)
data Decl n l = Let (NameBinder AtomNameC n l) (DeclBinding n)
     deriving (Show, Generic)

type AtomName    = Name AtomNameC
type DataDefName = Name DataDefNameC
type ClassName   = Name ClassNameC

data DataConRefBinding (n::S) (l::S) = DataConRefBinding (Binder n l) (Atom n)

type AtomBinderP = BinderP AtomNameC
type Binder = AtomBinderP Type
type AltP (e::E) = Abs (Nest Binder) e :: E
type Alt = AltP Block                  :: E

data DataDef n where
  -- The `SourceName` is just for pretty-printing. The actual alpha-renamable
  -- binder name is in UExpr and Bindings
  DataDef :: SourceName -> Nest Binder n l -> [DataConDef l] -> DataDef n

-- As above, the `SourceName` is just for pretty-printing
data DataConDef n =
  DataConDef SourceName (EmptyAbs (Nest Binder) n)
  deriving (Show, Generic)

data ClassDef n =
  ClassDef SourceName [SourceName] (NamedDataDef n)
  deriving (Show, Generic)

-- The Type is the type of the result expression (and thus the type of the
-- block). It's given by querying the result expression's type, and checking
-- that it doesn't have any free names bound by the decls in the block. We store
-- it separately as an optimization, to avoid having to traverse the block.
data Block n where
  Block :: Type n -> Nest Decl n l -> Expr l -> Block n

data LamBinding (n::S) = LamBinding Arrow (Type n)
  deriving (Show, Generic)

data LamBinder (n::S) (l::S) =
  LamBinder (NameBinder AtomNameC n l) (Type n) Arrow (EffectRow l)
  deriving (Show, Generic)

data LamExpr (n::S) where
  LamExpr :: LamBinder n l -> Block l -> LamExpr n

data PiBinding (n::S) = PiBinding Arrow (Type n)
  deriving (Show, Generic)

data PiBinder (n::S) (l::S) =
  PiBinder (NameBinder AtomNameC n l) (Type n) Arrow
  deriving (Show, Generic)

data PiType  (n::S) where
  PiType :: PiBinder n l -> EffectRow l -> Type  l -> PiType n

data Arrow =
   PlainArrow
 | ImplicitArrow
 | ClassArrow
 | TabArrow
 | LinArrow
   deriving (Show, Eq, Generic)

type Val  = Atom
type Type = Atom
type Kind = Type

type TC  n = PrimTC  (Atom n)
type Con n = PrimCon (Atom n)
type Op  n = PrimOp  (Atom n)
type Hof n = PrimHof (Atom n)

type IndexStructure = Nest Binder

type AtomSubstVal = SubstVal AtomNameC Atom :: V

-- === bindings - static information we carry about a lexical scope ===

data Binding (c::C) (n::S) where
  AtomNameBinding   :: AtomBinding n                      -> Binding AtomNameC       n
  DataDefBinding    :: DataDef n                          -> Binding DataDefNameC    n
  TyConBinding      :: DataDefName n                      -> Binding TyConNameC      n
  DataConBinding    :: DataDefName n -> Int               -> Binding DataConNameC    n
  ClassBinding      :: ClassDef n                         -> Binding ClassNameC      n
  SuperclassBinding :: Name ClassNameC n -> Int -> Atom n -> Binding SuperclassNameC n
  MethodBinding     :: Name ClassNameC n -> Int -> Atom n -> Binding MethodNameC     n
deriving instance Show (Binding c n)

data AtomBinding (n::S) =
   LetBound    (DeclBinding   n)
 | LamBound    (LamBinding    n)
 | PiBound     (PiBinding     n)
 | MiscBound   (Type          n)
 | SolverBound (SolverBinding n)
   deriving (Show, Generic)

data SolverBinding (n::S) =
   InfVarBound (Type n) SrcPosCtx
 | SkolemBound (Type n)
   deriving (Show, Generic)

data BindingsFrag (n::S) (l::S) =
  BindingsFrag (RecEnvFrag Binding n l) (Maybe (EffectRow l))

data Bindings (n::S) = Bindings
  { getNameBindings        :: RecEnv Binding n
  , getSynthCandidates :: SynthCandidates n
  , getSourceMap       :: SourceMap n
  , getEffects         :: EffectRow n}
  deriving (Generic)

instance HasScope Bindings where
  toScope = toScope . getNameBindings

catBindingsFrags :: Distinct n3
                 => BindingsFrag n1 n2 -> BindingsFrag n2 n3 -> BindingsFrag n1 n3
catBindingsFrags (BindingsFrag (RecEnvFrag frag1) maybeEffs1)
                 (BindingsFrag (RecEnvFrag frag2) maybeEffs2) =
  withExtEvidence (toExtEvidence (RecEnvFrag frag2)) do
     let fragOut = inject frag1 `catInFrags` frag2
     let effsOut = case maybeEffs2 of
                     Nothing    -> fmap inject maybeEffs1
                     Just effs2 -> Just effs2
     BindingsFrag (RecEnvFrag fragOut) effsOut

instance OutFrag BindingsFrag where
  emptyOutFrag = BindingsFrag emptyOutFrag Nothing
  catOutFrags _ frag1 frag2 = catBindingsFrags frag1 frag2

instance OutMap Bindings where
  emptyOutMap = Bindings emptyOutMap mempty (SourceMap mempty) Pure

instance ExtOutMap Bindings BindingsFrag where
  extendOutMap (Bindings bindings scs sm oldEff) frag =
    withExtEvidence frag do
      let BindingsFrag newBindings maybeNewEff = frag
      let newEff = case maybeNewEff of
                     Nothing  -> inject oldEff
                     Just eff -> eff
      Bindings
        (bindings `extendOutMap` newBindings)
        (inject scs <> bindingsFragToSynthCandidates frag)
        (inject sm)
        newEff

bindingsFragToSynthCandidates :: Distinct l => BindingsFrag n l -> SynthCandidates l
bindingsFragToSynthCandidates (BindingsFrag (RecEnvFrag frag) _) =
  execWriter $ bindingsFragToSynthCandidates' $ toEnvPairs frag

bindingsFragToSynthCandidates' :: Distinct l => Nest (EnvPair Binding l) n l
                               -> Writer (SynthCandidates l) ()
bindingsFragToSynthCandidates' nest = case nest of
  Empty -> return ()
  Nest (EnvPair b binding) rest -> withExtEvidence rest do
    case binding of
       AtomNameBinding (LetBound (DeclBinding InstanceLet _ _)) -> do
         tell $ inject (SynthCandidates [] [] [Var $ binderName b])
       AtomNameBinding (LamBound (LamBinding ClassArrow _)) -> do
         tell $ inject (SynthCandidates [Var $ binderName b] [] [])
       AtomNameBinding (PiBound (PiBinding ClassArrow _)) -> do
         tell $ inject (SynthCandidates [Var $ binderName b] [] [])
       SuperclassBinding _ _ getter ->
         tell $ inject (SynthCandidates [] [getter] [])
       _ -> return ()
    bindingsFragToSynthCandidates' rest

data WithBindings (e::E) (n::S) where
  WithBindings :: (Distinct l, Ext l n) => Bindings l -> e l -> WithBindings e n

class ScopeReader m => BindingsReader (m::MonadKind1) where
  getBindings :: Immut n => m n (Bindings n)

getDB :: BindingsReader m => Immut n => m n (DistinctBindings n)
getDB = do
  Distinct <- getDistinct
  bindings <- getBindings
  return $ DB bindings

data DistinctBindings n where
  DB :: (Distinct n, Immut n) => Bindings n -> DistinctBindings n

class (BindingsReader m, Monad1 m)
      => BindingsExtender (m::MonadKind1) where
  -- Note that we don't require `Immut l` here. So it's still possible to extend
  -- with nameless fragments, of type `BindingsFrag n n`.
  extendBindings :: Distinct l => BindingsFrag n l -> (Ext n l => m l r) -> m n r

type BindingsReader2   (m::MonadKind2) = forall (n::S). BindingsReader   (m n)
type BindingsExtender2 (m::MonadKind2) = forall (n::S). BindingsExtender (m n)

instance (InjectableE e, BindingsReader m)
         => BindingsReader (OutReaderT e m) where
  getBindings = OutReaderT $ lift $ getBindings

instance (InjectableE e, ScopeReader m, BindingsExtender m)
         => BindingsExtender (OutReaderT e m) where
  extendBindings frag m = OutReaderT $ ReaderT \env ->
    extendBindings frag do
      let OutReaderT (ReaderT cont) = m
      env' <- injectM env
      cont env'

newtype BindingsReaderT (m::MonadKind) (n::S) (a:: *) =
  BindingsReaderT {runBindingsReaderT' :: ReaderT (DistinctEvidence n, Bindings n) m a }
  deriving (Functor, Applicative, Monad, MonadFail, Fallible, Alternative)

type BindingsReaderM = BindingsReaderT Identity
runBindingsReaderM :: Distinct n => Bindings n -> BindingsReaderM n a -> a
runBindingsReaderM bindings m = runIdentity $ runBindingsReaderT bindings m

runBindingsReaderT :: Distinct n => Bindings n -> (BindingsReaderT m n a) -> m a
runBindingsReaderT bindings cont =
  runReaderT (runBindingsReaderT' cont) (Distinct, bindings)

instance Monad m => BindingsReader (BindingsReaderT m) where
  getBindings = BindingsReaderT $ asks snd

instance Monad m => BindingsExtender (BindingsReaderT m) where
  extendBindings frag m = BindingsReaderT $ withReaderT
    (\(_, bindings) -> (Distinct, extendOutMap bindings frag)) $
        withExtEvidence (toExtEvidence frag) $
          runBindingsReaderT' m

instance Monad m => ScopeReader (BindingsReaderT m) where
  getDistinct = BindingsReaderT $ asks fst
  getScope = toScope <$> snd <$> BindingsReaderT ask
  liftImmut cont = do
    Immut <- getImmut
    cont

instance Monad m => AlwaysImmut (BindingsReaderT m) where
  getImmut = BindingsReaderT $ ReaderT \(_, bindings) ->
    return $ toImmutEvidence bindings

instance (InjectableV v, BindingsReader m) => BindingsReader (EnvReaderT v m i) where
  getBindings = EnvReaderT $ lift getBindings

instance (InjectableV v, ScopeReader m, BindingsExtender m)
         => BindingsExtender (EnvReaderT v m i) where
  extendBindings frag m = EnvReaderT $ ReaderT \env ->
    extendBindings frag do
      let EnvReaderT (ReaderT cont) = m
      env' <- injectM env
      cont env'

-- TODO: unify this with `HasNames` by parameterizing by the thing you bind,
-- like we do with `SubstE Name`, `SubstE AtomSubstVal`, etc?
class BindsNames b => BindsBindings (b::B) where
  toBindingsFrag :: Distinct l => b n l -> BindingsFrag n l

  default toBindingsFrag :: (GenericB b, BindsBindings (RepB b))
                        => Distinct l => b n l -> BindingsFrag n l
  toBindingsFrag b = toBindingsFrag $ fromB b

-- We're really just defining this so we can have a polymorphic `binderType`.
-- But maybe we don't need one. Or maybe we can make one using just
-- `BindsOneName b AtomNameC` and `BindsBindings b`.
class BindsOneName b AtomNameC => BindsOneAtomName (b::B) where
  boundAtomBinding :: b n l -> AtomBinding n

binderType :: BindsOneAtomName b => b n l -> Type n
binderType b =  atomBindingType $ toBinding $ boundAtomBinding b

instance (InjectableE ann, ToBinding ann c) => BindsBindings (BinderP c ann) where
  toBindingsFrag (b:>ann) = BindingsFrag (RecEnvFrag (b @> toBinding ann')) Nothing
    where ann' = withExtEvidence b $ inject ann

class (SubstE Name e, InjectableE e) => ToBinding (e::E) (c::C) | e -> c where
  toBinding :: e n -> Binding c n

instance NameColor c => ToBinding (Binding c) c where
  toBinding = id

instance ToBinding AtomBinding AtomNameC where
  toBinding = AtomNameBinding

instance ToBinding DeclBinding AtomNameC where
  toBinding = toBinding . LetBound

instance ToBinding LamBinding AtomNameC where
  toBinding = toBinding . LamBound

instance ToBinding PiBinding AtomNameC where
  toBinding = toBinding . PiBound

instance ToBinding Atom AtomNameC where
  toBinding = toBinding . MiscBound

instance ToBinding SolverBinding AtomNameC where
  toBinding = toBinding . SolverBound

instance (ToBinding e1 c, ToBinding e2 c) => ToBinding (EitherE e1 e2) c where
  toBinding (LeftE  e) = toBinding e
  toBinding (RightE e) = toBinding e

lookupBindings :: (NameColor c, BindingsReader m) => Name c o -> m o (Binding c o)
lookupBindings v = liftImmut do
  bindings <- getBindings
  v' <- injectM v
  return $ lookupBindingsPure bindings v'

lookupSourceMap :: BindingsReader m
                => NameColorRep c -> SourceName -> m n (Maybe (Name c n))
lookupSourceMap nameColor sourceName = do
  sourceMap <- getSourceMapM
  case M.lookup sourceName $ fromSourceMap sourceMap of
    Just envVal -> return $ Just $ fromEnvVal nameColor envVal
    Nothing -> return Nothing

getSourceMapM :: BindingsReader m => m n (SourceMap n)
getSourceMapM = liftImmut $ getSourceMap <$> getBindings

lookupBindingsPure :: Bindings n -> Name c n -> Binding c n
lookupBindingsPure (Bindings bindings _ _ _) v =
  lookupTerminalEnvFrag (fromRecEnv bindings) v

updateBindings :: Name c n -> Binding c n -> Bindings n -> Bindings n
updateBindings v rhs bindings =
  bindings { getNameBindings = RecEnv $ updateEnvFrag v rhs bs }
  where (RecEnv bs) = getNameBindings bindings

refreshBinders
  :: ( InjectableV v, SubstV v v, BindingsExtender2 m, FromName v
     , EnvReader v m, SubstB v b, BindsBindings b)
  => Immut o
  => b i i'
  -> (forall o'. Ext o o' => b o o' -> m i' o' a)
  -> m i o a
refreshBinders b cont = do
  scope <- getScope
  Distinct <- getDistinct
  env <- getEnv
  DistinctAbs b' envFrag <- return $ substAbsDistinct scope env $ Abs b (idEnvFrag b)
  extendBindings (toBindingsFrag b') do
    extendEnv envFrag do
      cont b'

-- Version of `refreshBinder` that gets its `Immut n` evidence from the monad.
-- TODO: make it easy to go the other way (from refreshI to refresh) by having a
-- `CarriesImmutT` transformer to add explicit Immut evidence when
-- needed. Then this can be the main version.
refreshBindersI
  :: ( InjectableV v, SubstV v v, BindingsExtender2 m, FromName v
     , EnvReader v m, SubstB v b, BindsBindings b)
  => AlwaysImmut2 m
  => b i i'
  -> (forall o'. Ext o o' => b o o' -> m i' o' a)
  -> m i o a
refreshBindersI b cont = do
  Immut <- getImmut
  refreshBinders b cont

withFreshBinder
  :: (NameColor c, BindingsExtender m, ToBinding binding c)
  => Immut n
  => NameHint -> binding n
  -> (forall l. (Immut l, Distinct l, Ext n l) => NameBinder c n l -> m l a)
  -> m n a
withFreshBinder hint binding cont = do
  scope    <- getScope
  Distinct <- getDistinct
  withFresh hint nameColorRep scope \b -> do
    extendBindings (toBindingsFrag (b:>binding)) $
      cont b

withFreshLamBinder
  :: (BindingsExtender m)
  => Immut n
  => NameHint -> LamBinding n
  -> Abs Binder EffectRow n
  -> (forall l. (Immut l, Distinct l, Ext n l) => LamBinder n l -> m l a)
  -> m n a
withFreshLamBinder hint binding@(LamBinding arr ty) effAbs cont = do
  withFreshBinder hint binding \b -> do
    effs <- applyAbs (inject effAbs) (binderName b)
    withAllowedEffects effs do
      cont $ LamBinder b ty arr effs

withFreshPiBinder
  :: BindingsExtender m
  => Immut n
  => NameHint -> PiBinding n
  -> (forall l. (Immut l, Distinct l, Ext n l) => PiBinder n l -> m l a)
  -> m n a
withFreshPiBinder hint binding@(PiBinding arr ty) cont = do
  withFreshBinder hint binding \b ->
    withAllowedEffects Pure $
      cont $ PiBinder b ty arr

piBinderToLamBinder :: PiBinder n l -> EffectRow l -> LamBinder n l
piBinderToLamBinder (PiBinder b ty arr) eff = LamBinder b ty arr eff

data SomeDecl (binding::V) (n::S) (l::S) where
  SomeDecl :: NameColor c => NameBinder c n l -> binding c n -> SomeDecl binding n l

instance ProvesExt (SomeDecl binding) where
  toExtEvidence (SomeDecl b _) = toExtEvidence b

instance (InjectableV v, SubstV v binding)
         => SubstB v (SomeDecl binding) where
  substB env (SomeDecl b binding) cont = do
    let binding' = substE env binding
    substB env b \env' b' -> cont env' $ SomeDecl b' binding'
  substBDistinct _ _ = undefined

instance HoistableV binding => HoistableB (SomeDecl binding) where
  freeVarsB (SomeDecl _ binding) = freeVarsE binding

instance InjectableV binding => InjectableB (SomeDecl binding) where
  injectionProofB _ _ _ = undefined

instance BindsNames (SomeDecl binding) where
  toScopeFrag (SomeDecl b _) = toScopeFrag b

instance (forall c. NameColor c => ToBinding (binding c) c)
         => BindsBindings (SomeDecl binding) where
  toBindingsFrag (SomeDecl b binding) =
    withExtEvidence b $
      BindingsFrag (RecEnvFrag $ b @> inject (toBinding binding)) Nothing

-- === FallibleT transformer ===

newtype FallibleT1 (m::MonadKind1) (n::S) a =
  FallibleT1 { fromFallibleT :: ReaderT ErrCtx (MTE.ExceptT Errs (m n)) a }
  deriving (Functor, Applicative, Monad)

runFallibleT1 :: Monad1 m => FallibleT1 m n a -> m n (Except a)
runFallibleT1 m =
  MTE.runExceptT (runReaderT (fromFallibleT m) mempty) >>= \case
    Right ans -> return $ Success ans
    Left errs -> return $ Failure errs

instance Monad1 m => MonadFail (FallibleT1 m n) where
  fail s = throw MonadFailErr s

instance Monad1 m => Fallible (FallibleT1 m n) where
  throwErrs (Errs errs) = FallibleT1 $ ReaderT \ambientCtx ->
    MTE.throwE $ Errs [Err errTy (ambientCtx <> ctx) s | Err errTy ctx s <- errs]
  addErrCtx ctx (FallibleT1 m) = FallibleT1 $ local (<> ctx) m

instance ScopeReader m => ScopeReader (FallibleT1 m) where
  getScope = FallibleT1 $ lift $ lift getScope
  getDistinct = FallibleT1 $ lift $ lift $ getDistinct
  liftImmut cont = FallibleT1 $ ReaderT \ctx -> do
    exceptResult <- lift $ liftImmut do
      MTE.runExceptT (runReaderT (fromFallibleT cont) ctx) >>= \case
        Right x  -> return $ RightE x
        Left err -> return $ LeftE (LiftE err)
    case exceptResult of
      RightE x -> return x
      LeftE (LiftE err) -> MTE.throwE err

instance BindingsReader m => BindingsReader (FallibleT1 m) where
  getBindings = FallibleT1 $ lift $ lift getBindings

-- === Querying static env ===

getSynthCandidatesM :: BindingsReader m => m n (SynthCandidates n)
getSynthCandidatesM = liftImmut $ getSynthCandidates <$> getBindings

getAllowedEffects :: BindingsReader m => m n (EffectRow n)
getAllowedEffects = liftImmut $ getEffects <$> getBindings

withAllowedEffects :: BindingsExtender m => EffectRow n -> m n a -> m n a
withAllowedEffects effs cont = do
  Distinct <- getDistinct
  extendBindings (BindingsFrag emptyOutFrag $ Just effs) cont

-- === front-end language AST ===

data SourceNameOr (a::E) (n::S) where
  -- Only appears before renaming pass
  SourceName :: SourceName -> SourceNameOr a VoidS
  -- Only appears after renaming pass
  InternalName :: a n -> SourceNameOr a n
deriving instance Eq (a n) => Eq (SourceNameOr (a::E) (n::S))
deriving instance Ord (a n) => Ord (SourceNameOr a n)
deriving instance Show (a n) => Show (SourceNameOr a n)

data UVar (n::S) =
   UAtomVar    (Name AtomNameC    n)
 | UTyConVar   (Name TyConNameC   n)
 | UDataConVar (Name DataConNameC n)
 | UClassVar   (Name ClassNameC   n)
 | UMethodVar  (Name MethodNameC  n)
   deriving (Eq, Ord, Show, Generic)

data UBinder (c::C) (n::S) (l::S) where
  -- Only appears before renaming pass
  UBindSource :: SourceName -> UBinder c n n
  -- May appear before or after renaming pass
  UIgnore :: UBinder c n n
  -- The following binders only appear after the renaming pass.
  UBind :: (NameBinder c n l) -> UBinder c n l

type UExpr = WithSrcE UExpr'
data UExpr' (n::S) =
   UVar (SourceNameOr UVar n)
 | ULam (ULamExpr n)
 | UPi  (UPiExpr n)
 | UApp Arrow (UExpr n) (UExpr n)
 | UDecl (UDeclExpr n)
 | UFor Direction (UForExpr n)
 | UCase (UExpr n) [UAlt n]
 | UHole
 | UTypeAnn (UExpr n) (UExpr n)
 | UTabCon [UExpr n]
 | UIndexRange (Limit (UExpr n)) (Limit (UExpr n))
 | UPrimExpr (PrimExpr (UExpr n))
 | URecord (ExtLabeledItems (UExpr n) (UExpr n))     -- {a=x, b=y, ...rest}
 | UVariant (LabeledItems ()) Label (UExpr n)        -- {|a|b| a=x |}
 | UVariantLift (LabeledItems ()) (UExpr n)          -- {|a|b| ...rest |}
 | URecordTy (ExtLabeledItems (UExpr n) (UExpr n))   -- {a:X & b:Y & ...rest}
 | UVariantTy (ExtLabeledItems (UExpr n) (UExpr n))  -- {a:X | b:Y | ...rest}
 | UIntLit  Int
 | UFloatLit Double
  deriving (Show, Generic)

data ULamExpr (n::S) where
  ULamExpr :: Arrow -> UPatAnn n l -> UExpr l -> ULamExpr n

data UPiExpr (n::S) where
  UPiExpr :: Arrow -> UPatAnn n l -> UEffectRow l -> UType l -> UPiExpr n

data UDeclExpr (n::S) where
  UDeclExpr :: UDecl n l -> UExpr l -> UDeclExpr n

type UConDef (n::S) (l::S) = (SourceName, Nest (UAnnBinder AtomNameC) n l)

-- TODO Why are the type and data constructor names SourceName, rather
-- than being scoped names of the proper color of their own?
data UDataDef (n::S) where
  UDataDef
    :: (SourceName, Nest (UAnnBinder AtomNameC) n l)    -- param binders
    -- Trailing l' is the last scope for the chain of potentially
    -- dependent constructor argument types.
    -> [(SourceName, UDataDefTrail l)] -- data constructor types
    -> UDataDef n

data UDataDefTrail (l::S) where
  UDataDefTrail :: Nest (UAnnBinder AtomNameC) l l' -> UDataDefTrail l

data UDecl (n::S) (l::S) where
  ULet :: LetAnn -> UPatAnn n l -> UExpr n -> UDecl n l
  UDataDefDecl
    :: UDataDef n                          -- actual definition
    -> UBinder TyConNameC n l'             -- type constructor name
    ->   Nest (UBinder DataConNameC) l' l  -- data constructor names
    -> UDecl n l
  UInterface
    :: Nest (UAnnBinder AtomNameC) n p     -- parameter binders
    ->  [UType p]                          -- superclasses
    ->  [UMethodType p]                    -- method types
    -> UBinder ClassNameC n l'             -- class name
    ->   Nest (UBinder MethodNameC) l' l   -- method names
    -> UDecl n l
  UInstance
    :: SourceNameOr (Name ClassNameC) n  -- class name
    -> Nest UPatAnnArrow n l'            -- dictionary args (i.e. conditions)
    ->   [UExpr l']                      -- class parameters
    ->   [UMethodDef l']                 -- method definitions
    -- Maybe we should make a separate color (namespace) for instance names?
    -> MaybeB (UBinder AtomNameC) n l  -- optional instance name
    -> UDecl n l

type UType = UExpr

data UMethodType (n::S) where
  UMethodType :: Either [SourceName] [Bool] -> UType s -> UMethodType s
  deriving (Show, Generic)

data UForExpr (n::S) where
  UForExpr :: UPatAnn n l -> UExpr l -> UForExpr n

data UMethodDef (n::S) = UMethodDef (SourceNameOr (Name MethodNameC) n) (UExpr n)
  deriving (Show, Generic)

data UPatAnn (n::S) (l::S) = UPatAnn (UPat n l) (Maybe (UType n))
  deriving (Show, Generic)

data UPatAnnArrow (n::S) (l::S) = UPatAnnArrow (UPatAnn n l) Arrow
  deriving (Show, Generic)

data UAnnBinder (c::C) (n::S) (l::S) = UAnnBinder (UBinder c n l) (UType n)
  deriving (Show, Generic)

data UAlt (n::S) where
  UAlt :: UPat n l -> UExpr l -> UAlt n

type UPat = WithSrcB UPat'
data UPat' (n::S) (l::S) =
   UPatBinder (UBinder AtomNameC n l)
 | UPatCon (SourceNameOr (Name DataConNameC) n) (Nest UPat n l)
 | UPatPair (PairB UPat UPat n l)
 | UPatUnit (UnitB n l)
 -- The ExtLabeledItems and the PairB are parallel, constrained by the parser.
 | UPatRecord (ExtLabeledItems () ()) (PairB (Nest UPat) (MaybeB UPat) n l) -- {a=x, b=y, ...rest}
 | UPatVariant (LabeledItems ()) Label (UPat n l)   -- {|a|b| a=x |}
 | UPatVariantLift (LabeledItems ()) (UPat n l)     -- {|a|b| ...rest |}
 | UPatTable (Nest UPat n l)
  deriving (Show)

data WithSrcE (a::E) (n::S) = WithSrcE SrcPosCtx (a n)
  deriving (Show)

data WithSrcB (binder::B) (n::S) (l::S) = WithSrcB SrcPosCtx (binder n l)
  deriving (Show)

class HasSrcPos a where
  srcPos :: a -> SrcPosCtx

instance HasSrcPos (WithSrcE (a::E) (n::S)) where
  srcPos (WithSrcE pos _) = pos

instance HasSrcPos (WithSrcB (b::B) (n::S) (n::S)) where
  srcPos (WithSrcB pos _) = pos

pattern UPatIgnore :: UPat' (n::S) n
pattern UPatIgnore = UPatBinder UIgnore

-- === top-level modules ===

type LitProg = [(SourceBlock, Result)]

type SourceName = String

-- body must only contain SourceName version of names and binders
data SourceUModule = SourceUModule (UDecl VoidS VoidS) deriving (Show)

-- body must only contain Name version of names and binders
data UModule (n::S) where
  UModule
    :: UDecl n l
    -> SourceMap l
    -> UModule n

data SourceBlock = SourceBlock
  { sbLine     :: Int
  , sbOffset   :: Int
  , sbLogLevel :: LogLevel
  , sbText     :: String
  , sbContents :: SourceBlock'
  , sbId       :: Maybe BlockId }  deriving (Show)

data SourceBlock' =
   RunModule SourceUModule
 | Command CmdName (SourceName, SourceUModule)
 | GetNameType SourceName
 -- TODO Add a color for module names?
 | ImportModule ModuleName
 | QueryEnv EnvQuery
 | ProseBlock String
 | CommentLine
 | EmptyLines
 | UnParseable ReachedEOF String
  deriving (Show, Generic)

data EnvQuery =
   DumpEnv
 | InternalNameInfo RawName
 | SourceNameInfo   SourceName
   deriving (Show, Generic)


type TopState = Bindings

data SourceMap (n::S) = SourceMap
  { fromSourceMap :: M.Map SourceName (EnvVal Name n)}
  deriving Show

data Module n where
  Module
    :: IRVariant
    -> Nest Decl n l      -- Unevaluated decls representing runtime work to be done
    -> EvaluatedModule l
    -> Module n

data EvaluatedModule (n::S) where
  EvaluatedModule
    :: BindingsFrag n l   -- Evaluated bindings
       -- TODO: we don't need this here because it's redundant with bindingsfrag
    -> SynthCandidates l  -- Values considered in scope for dictionary synthesis
    -> SourceMap l        -- Mapping of module's source names to internal names
    -> EvaluatedModule n

-- TODO: we could add a lot more structure for querying by dict type, caching, etc.
data SynthCandidates n = SynthCandidates
  { lambdaDicts       :: [Atom n]
  , superclassGetters :: [Atom n]
  , instanceDicts     :: [Atom n] }
  deriving (Show, Generic)

-- === effects ===

data EffectP (name::E) (n::S) =
  RWSEffect RWS (name n) | ExceptionEffect | IOEffect
  deriving (Show, Eq, Ord, Generic)

type Effect = EffectP AtomName
type UEffect = EffectP (SourceNameOr (Name AtomNameC))

data EffectRowP (name::E) (n::S) =
  EffectRow (S.Set (EffectP name n)) (Maybe (name n))
  deriving (Show, Eq, Ord, Generic)

type EffectRow = EffectRowP AtomName
type UEffectRow = EffectRowP (SourceNameOr (Name AtomNameC))

pattern Pure :: Ord (name n) => EffectRowP name n
pattern Pure <- ((\(EffectRow effs t) -> (S.null effs, t)) -> (True, Nothing))
 where  Pure = EffectRow mempty Nothing

extendEffRow :: S.Set (Effect n) -> (EffectRow n) -> (EffectRow n)
extendEffRow effs (EffectRow effs' t) = EffectRow (effs <> effs') t

-- === Helpers for function evaluation over fixed-width types ===

applyIntBinOp' :: (forall a. (Eq a, Ord a, Num a, Integral a)
               => (a -> Atom n) -> a -> a -> Atom n) -> Atom n -> Atom n -> Atom n
applyIntBinOp' f x y = case (x, y) of
  (Con (Lit (Int64Lit xv)), Con (Lit (Int64Lit yv))) -> f (Con . Lit . Int64Lit) xv yv
  (Con (Lit (Int32Lit xv)), Con (Lit (Int32Lit yv))) -> f (Con . Lit . Int32Lit) xv yv
  (Con (Lit (Word8Lit xv)), Con (Lit (Word8Lit yv))) -> f (Con . Lit . Word8Lit) xv yv
  (Con (Lit (Word32Lit xv)), Con (Lit (Word32Lit yv))) -> f (Con . Lit . Word32Lit) xv yv
  (Con (Lit (Word64Lit xv)), Con (Lit (Word64Lit yv))) -> f (Con . Lit . Word64Lit) xv yv
  _ -> error "Expected integer atoms"

applyIntBinOp :: (forall a. (Num a, Integral a) => a -> a -> a) -> Atom n -> Atom n -> Atom n
applyIntBinOp f x y = applyIntBinOp' (\w -> w ... f) x y

applyIntCmpOp :: (forall a. (Eq a, Ord a) => a -> a -> Bool) -> Atom n -> Atom n -> Atom n
applyIntCmpOp f x y = applyIntBinOp' (\_ -> (Con . Lit . Word8Lit . fromIntegral . fromEnum) ... f) x y

applyFloatBinOp :: (forall a. (Num a, Fractional a) => a -> a -> a) -> Atom n -> Atom n -> Atom n
applyFloatBinOp f x y = case (x, y) of
  (Con (Lit (Float64Lit xv)), Con (Lit (Float64Lit yv))) -> Con $ Lit $ Float64Lit $ f xv yv
  (Con (Lit (Float32Lit xv)), Con (Lit (Float32Lit yv))) -> Con $ Lit $ Float32Lit $ f xv yv
  _ -> error "Expected float atoms"

applyFloatUnOp :: (forall a. (Num a, Fractional a) => a -> a) -> Atom n -> Atom n
applyFloatUnOp f x = applyFloatBinOp (\_ -> f) undefined x

-- === Synonyms ===

atomBindingType :: Binding AtomNameC n -> Type n
atomBindingType (AtomNameBinding b) = case b of
  LetBound    (DeclBinding _ ty _) -> ty
  LamBound    (LamBinding  _ ty)   -> ty
  PiBound     (PiBinding   _ ty)   -> ty
  MiscBound   ty                   -> ty
  SolverBound (InfVarBound ty _)   -> ty
  SolverBound (SkolemBound ty)     -> ty

infixr 1 -->
infixr 1 --@
infixr 2 ==>

piArgType :: PiType n -> Type n
piArgType (PiType (PiBinder _ ty _) _ _) = ty

piArrow :: PiType n -> Arrow
piArrow (PiType (PiBinder _ _ arr) _ _) = arr

nonDepPiType :: ScopeReader m
             => Arrow -> Type n -> EffectRow n -> Type n -> m n (PiType n)
nonDepPiType arr argTy eff resultTy =
  toConstAbs AtomNameRep (PairE eff resultTy) >>= \case
    Abs b (PairE eff' resultTy') ->
      return $ PiType (PiBinder b argTy arr) eff' resultTy'

considerNonDepPiType :: PiType n -> Maybe (Arrow, Type n, EffectRow n, Type n)
considerNonDepPiType (PiType (PiBinder b argTy arr) eff resultTy) = do
  HoistSuccess (PairE eff' resultTy') <- return $ hoist b (PairE eff resultTy)
  return (arr, argTy, eff', resultTy')

fromNonDepPiType :: (ScopeReader m, MonadFail1 m)
                 => Arrow -> Type n -> m n (Type n, EffectRow n, Type n)
fromNonDepPiType arr ty = do
  Pi (PiType (PiBinder b argTy arr') eff resultTy) <- return ty
  unless (arr == arr') $ fail "arrow type mismatch"
  HoistSuccess (PairE eff' resultTy') <- return $ hoist b (PairE eff resultTy)
  return $ (argTy, eff', resultTy')

naryNonDepPiType :: ScopeReader m =>  Arrow -> EffectRow n -> [Type n] -> Type n -> m n (Type n)
naryNonDepPiType _ Pure [] resultTy = return resultTy
naryNonDepPiType _ _    [] _        = error "nullary function can't have effects"
naryNonDepPiType arr eff [ty] resultTy = Pi <$> nonDepPiType arr ty eff resultTy
naryNonDepPiType arr eff (ty:tys) resultTy = do
  innerFunctionTy <- naryNonDepPiType arr eff tys resultTy
  Pi <$> nonDepPiType arr ty Pure innerFunctionTy

fromNaryNonDepPiType :: (ScopeReader m, MonadFail1 m)
                     => [Arrow] -> Type n -> m n ([Type n], EffectRow n, Type n)
fromNaryNonDepPiType [] ty = return ([], Pure, ty)
fromNaryNonDepPiType [arr] ty = do
  (argTy, eff, resultTy) <- fromNonDepPiType arr ty
  return ([argTy], eff, resultTy)
fromNaryNonDepPiType (arr:arrs) ty = do
  (argTy, Pure, innerTy) <- fromNonDepPiType arr ty
  (argTys, eff, resultTy) <- fromNaryNonDepPiType arrs innerTy
  return (argTy:argTys, eff, resultTy)

fromNonDepTabTy :: (ScopeReader m, MonadFail1 m) => Type n -> m n (Type n, Type n)
fromNonDepTabTy ty = do
  (idxTy, Pure, resultTy) <- fromNonDepPiType TabArrow ty
  return (idxTy, resultTy)

(?-->) :: ScopeReader m => Type n -> Type n -> m n (Type n)
a ?--> b = Pi <$> nonDepPiType ImplicitArrow a Pure b

(-->) :: ScopeReader m => Type n -> Type n -> m n (Type n)
a --> b = Pi <$> nonDepPiType PlainArrow a Pure b

(--@) :: ScopeReader m => Type n -> Type n -> m n (Type n)
a --@ b = Pi <$> nonDepPiType LinArrow a Pure b

(==>) :: ScopeReader m => Type n -> Type n -> m n (Type n)
a ==> b = Pi <$> nonDepPiType TabArrow a Pure b

pattern IntLitExpr :: Int -> UExpr' n
pattern IntLitExpr x = UIntLit x

pattern FloatLitExpr :: Double -> UExpr' n
pattern FloatLitExpr x = UFloatLit x

getIntLit :: LitVal -> Int
getIntLit l = case l of
  Int64Lit i -> fromIntegral i
  Int32Lit i -> fromIntegral i
  Word8Lit  i -> fromIntegral i
  _ -> error $ "Expected an integer literal"

getFloatLit :: LitVal -> Double
getFloatLit l = case l of
  Float64Lit f -> f
  Float32Lit f -> realToFrac f
  _ -> error $ "Expected a floating-point literal"

-- Type used to represent indices at run-time
pattern IdxRepTy :: Type n
pattern IdxRepTy = TC (BaseType (Scalar Int32Type))

pattern IdxRepVal :: Int32 -> Atom n
pattern IdxRepVal x = Con (Lit (Int32Lit x))

-- Type used to represent sum type tags at run-time
pattern TagRepTy :: Type n
pattern TagRepTy = TC (BaseType (Scalar Word8Type))

pattern TagRepVal :: Word8 -> Atom n
pattern TagRepVal x = Con (Lit (Word8Lit x))

pattern Word8Ty :: Type n
pattern Word8Ty = TC (BaseType (Scalar Word8Type))

pattern ProdTy :: [Type n] -> Type n
pattern ProdTy tys = TC (ProdType tys)

pattern ProdVal :: [Atom n] -> Atom n
pattern ProdVal xs = Con (ProdCon xs)

pattern SumTy :: [Type n] -> Type n
pattern SumTy cs = TC (SumType cs)

pattern SumVal :: Type n -> Int -> Atom n -> Atom n
pattern SumVal ty tag payload = Con (SumCon ty tag payload)

pattern PairVal :: Atom n -> Atom n -> Atom n
pattern PairVal x y = Con (ProdCon [x, y])

pattern PairTy :: Type n -> Type n -> Type n
pattern PairTy x y = TC (ProdType [x, y])

pattern UnitVal :: Atom n
pattern UnitVal = Con (ProdCon [])

pattern UnitTy :: Type n
pattern UnitTy = TC (ProdType [])

pattern BaseTy :: BaseType -> Type n
pattern BaseTy b = TC (BaseType b)

pattern PtrTy :: PtrType -> Type n
pattern PtrTy ty = BaseTy (PtrType ty)

pattern RefTy :: Atom n -> Type n -> Type n
pattern RefTy r a = TC (RefType (Just r) a)

pattern RawRefTy :: Type n -> Type n
pattern RawRefTy a = TC (RefType Nothing a)

pattern TabTyAbs :: PiType n -> Type n
pattern TabTyAbs a <- Pi a@(PiType (PiBinder _ _ TabArrow) _ _)

pattern TyKind :: Kind n
pattern TyKind = TC TypeKind

pattern EffKind :: Kind n
pattern EffKind = TC EffectRowKind

pattern LabeledRowKind :: Kind n
pattern LabeledRowKind = TC LabeledRowKindTC

pattern FixedIntRange :: Int32 -> Int32 -> Type n
pattern FixedIntRange low high = TC (IntRange (IdxRepVal low) (IdxRepVal high))

pattern Fin :: Atom n -> Type n
pattern Fin n = TC (IntRange (IdxRepVal 0) n)

pattern BinaryFunTy :: PiBinder n l1 -> PiBinder l1 l2 -> EffectRow l2 -> Type l2 -> Type n
pattern BinaryFunTy b1 b2 eff ty <- Pi (PiType b1 Pure (Pi (PiType b2 eff ty)))

mkConsListTy :: [Type n] -> Type n
mkConsListTy = foldr PairTy UnitTy

mkConsList :: [Atom n] -> Atom n
mkConsList = foldr PairVal UnitVal

fromConsListTy :: Fallible m => Type n -> m [Type n]
fromConsListTy ty = case ty of
  UnitTy         -> return []
  PairTy t rest -> (t:) <$> fromConsListTy rest
  _              -> throw CompilerErr $ "Not a pair or unit: " ++ show ty

-- ((...((ans & x{n}) & x{n-1})... & x2) & x1) -> (ans, [x1, ..., x{n}])
fromLeftLeaningConsListTy :: Fallible m => Int -> Type n -> m (Type n, [Type n])
fromLeftLeaningConsListTy depth initTy = go depth initTy []
  where
    go 0        ty xs = return (ty, reverse xs)
    go remDepth ty xs = case ty of
      PairTy lt rt -> go (remDepth - 1) lt (rt : xs)
      _ -> throw CompilerErr $ "Not a pair: " ++ show xs

fromConsList :: Fallible m => Atom n -> m [Atom n]
fromConsList xs = case xs of
  UnitVal        -> return []
  PairVal x rest -> (x:) <$> fromConsList rest
  _              -> throw CompilerErr $ "Not a pair or unit: " ++ show xs

type BundleDesc = Int  -- length

getProjection :: [Int] -> Atom n -> Atom n
getProjection [] a = a
getProjection (i:is) a = case getProjection is a of
  Var name -> ProjectElt (NE.fromList [i]) name
  ProjectElt idxs' a' -> ProjectElt (NE.cons i idxs') a'
  DataCon _ _ _ _ xs -> xs !! i
  Record items -> toList items !! i
  Con (ProdCon xs) -> xs !! i
  a' -> error $ "Not a valid projection: " ++ show i ++ " of " ++ show a'

bundleFold :: a -> (a -> a -> a) -> [a] -> (a, BundleDesc)
bundleFold emptyVal pair els = case els of
  []  -> (emptyVal, 0)
  [e] -> (e, 1)
  h:t -> (pair h tb, td + 1)
    where (tb, td) = bundleFold emptyVal pair t

mkBundleTy :: [Type n] -> (Type n, BundleDesc)
mkBundleTy = bundleFold UnitTy PairTy

mkBundle :: [Atom n] -> (Atom n, BundleDesc)
mkBundle = bundleFold UnitVal PairVal

pattern MaybeTy :: Type n -> Type n
pattern MaybeTy a = SumTy [UnitTy, a]

pattern NothingAtom :: Type n -> Atom n
pattern NothingAtom a = SumVal (MaybeTy a) 0 UnitVal

pattern JustAtom :: Type n -> Atom n -> Atom n
pattern JustAtom a x = SumVal (MaybeTy a) 1 x

-- -- === instances ===

-- right-biased, unlike the underlying Map
instance Semigroup (SourceMap n) where
  m1 <> m2 = SourceMap $ fromSourceMap m2 <> fromSourceMap m1

instance Monoid (SourceMap n) where
  mempty = SourceMap mempty

instance GenericE DataDef where
  type RepE DataDef = PairE (LiftE SourceName) (Abs (Nest Binder) (ListE DataConDef))
  fromE (DataDef name bs cons) = PairE (LiftE name) (Abs bs (ListE cons))
  toE   (PairE (LiftE name) (Abs bs (ListE cons))) = DataDef name bs cons
deriving instance Show (DataDef n)
deriving via WrapE DataDef n instance Generic (DataDef n)
instance InjectableE DataDef
instance HoistableE  DataDef
instance SubstE Name DataDef
instance SubstE AtomSubstVal DataDef
instance AlphaEqE DataDef

instance GenericE DataConDef where
  type RepE DataConDef = PairE (LiftE SourceName) (Abs (Nest Binder) UnitE)
  fromE (DataConDef name ab) = PairE (LiftE name) ab
  toE   (PairE (LiftE name) ab) = DataConDef name ab
instance InjectableE DataConDef
instance HoistableE  DataConDef
instance SubstE Name DataConDef
instance SubstE AtomSubstVal DataConDef
instance AlphaEqE DataConDef

instance GenericE ClassDef where
  type RepE ClassDef = PairE (LiftE (SourceName, [SourceName]))
                             (PairE (Name DataDefNameC) DataDef)
  fromE (ClassDef className methodNames (dataDefName, dataDef)) =
          PairE (LiftE (className, methodNames)) (PairE dataDefName dataDef)
  toE (PairE (LiftE (className, methodNames)) (PairE dataDefName dataDef)) =
        ClassDef className methodNames (dataDefName, dataDef)
instance InjectableE         ClassDef
instance HoistableE        ClassDef
instance SubstE Name         ClassDef
instance SubstE AtomSubstVal ClassDef

instance GenericB DataConRefBinding where
  type RepB DataConRefBinding = PairB (LiftB Atom) Binder
  fromB (DataConRefBinding b val) = PairB (LiftB val) b
  toB   (PairB (LiftB val) b) = DataConRefBinding b val

instance InjectableB DataConRefBinding
instance HoistableB DataConRefBinding
instance ProvesExt  DataConRefBinding
instance BindsNames DataConRefBinding
instance SubstB Name DataConRefBinding
instance SubstB AtomSubstVal DataConRefBinding
instance AlphaEqB DataConRefBinding
deriving instance Show (DataConRefBinding n l)
deriving instance Generic (DataConRefBinding n l)

newtype ExtLabeledItemsE (e1::E) (e2::E) (n::S) =
  ExtLabeledItemsE (ExtLabeledItems (e1 n) (e2 n))

instance GenericE Atom where
  type RepE Atom =
      EitherE5
              (EitherE2
                   -- We isolate the Var and ProjectElt cases (and reorder them
                   -- compared to the data definition) because they need special
                   -- handling when you substitute with atoms. The rest just act
                   -- like containers
  {- Var -}        AtomName
  {- ProjectElt -} ( LiftE (NE.NonEmpty Int) `PairE` AtomName )
            ) (EitherE4
  {- Lam -}        LamExpr
  {- Pi -}         PiType
  {- DataCon -}    ( LiftE (SourceName, Int)   `PairE`
                     PairE DataDefName DataDef `PairE`
                     ListE Atom                `PairE`
                     ListE Atom )
  {- TypeCon -}    ( PairE DataDefName DataDef `PairE` ListE Atom )
            ) (EitherE5
  {- LabeledRow -} (ExtLabeledItemsE Type AtomName)
  {- Record -}     (ComposeE LabeledItems Atom)
  {- RecordTy -}   (ExtLabeledItemsE Type AtomName)
  {- Variant -}    ( ExtLabeledItemsE Type AtomName `PairE`
                     LiftE (Label, Int) `PairE` Atom )
  {- VariantTy -}  (ExtLabeledItemsE Type AtomName)
            ) (EitherE2
  {- Con -}        (ComposeE PrimCon Atom)
  {- TC -}         (ComposeE PrimTC  Atom)
            ) (EitherE4
  {- Eff -}        EffectRow
  {- ACase -}      ( Atom `PairE` ListE (AltP Atom) `PairE` Type )
  {- DataConRef -} ( PairE DataDefName DataDef      `PairE`
                     ListE Atom                     `PairE`
                     EmptyAbs (Nest DataConRefBinding) )
  {- BoxedRef -}   ( Atom `PairE` Block `PairE` Abs Binder Atom ))

  fromE atom = case atom of
    Var v -> Case0 (Case0 v)
    ProjectElt idxs x -> Case0 (Case1 (PairE (LiftE idxs) x))
    Lam lamExpr -> Case1 (Case0 lamExpr)
    Pi  piExpr  -> Case1 (Case1 piExpr)
    DataCon printName (defName, def) params con args -> Case1 $ Case2 $
      LiftE (printName, con) `PairE`
      PairE defName def      `PairE`
      ListE params           `PairE`
      ListE args
    TypeCon (defName, def) params ->
      Case1 $ Case3 $ PairE defName def `PairE` ListE params
    LabeledRow extItems -> Case2 $ Case0 $ ExtLabeledItemsE extItems
    Record items        -> Case2 $ Case1 $ ComposeE items
    RecordTy extItems   -> Case2 $ Case2 $ ExtLabeledItemsE extItems
    Variant extItems l con payload -> Case2 $ Case3 $
      ExtLabeledItemsE extItems `PairE` LiftE (l, con) `PairE` payload
    VariantTy extItems  -> Case2 $ Case4 $ ExtLabeledItemsE extItems
    Con con -> Case3 $ Case0 $ ComposeE con
    TC  con -> Case3 $ Case1 $ ComposeE con
    Eff effs -> Case4 $ Case0 $ effs
    ACase scrut alts ty -> Case4 $ Case1 $ scrut `PairE` ListE alts `PairE` ty
    DataConRef (defName, def) params bs ->
      Case4 $ Case2 $ PairE defName def `PairE` ListE params `PairE` bs
    BoxedRef ptr size ab ->
      Case4 $ Case3 $ ptr `PairE` size `PairE` ab

  toE atom = case atom of
    Case0 val -> case val of
      Case0 v -> Var v
      Case1 (PairE (LiftE idxs) x) -> ProjectElt idxs x
      _ -> error "impossible"
    Case1 val -> case val of
      Case0 lamExpr -> Lam lamExpr
      Case1 piExpr  -> Pi  piExpr
      Case2 ( LiftE (printName, con) `PairE`
              PairE defName def      `PairE`
              ListE params           `PairE`
              ListE args ) ->
        DataCon printName (defName, def) params con args
      Case3 (PairE defName def `PairE` ListE params) ->
        TypeCon (defName, def) params
      _ -> error "impossible"
    Case2 val -> case val of
      Case0 (ExtLabeledItemsE extItems) -> LabeledRow extItems
      Case1 (ComposeE items) -> Record items
      Case2 (ExtLabeledItemsE extItems) -> RecordTy extItems
      Case3 ( (ExtLabeledItemsE extItems) `PairE`
              LiftE (l, con)              `PairE`
              payload) -> Variant extItems l con payload
      Case4 (ExtLabeledItemsE extItems) -> VariantTy extItems
      _ -> error "impossible"
    Case3 val -> case val of
      Case0 (ComposeE con) -> Con con
      Case1 (ComposeE con) -> TC con
      _ -> error "impossible"
    Case4 val -> case val of
      Case0 effs -> Eff effs
      Case1 (scrut `PairE` ListE alts `PairE` ty) -> ACase scrut alts ty
      Case2 (PairE defName def `PairE` ListE params `PairE` bs) ->
        DataConRef (defName, def) params bs
      Case3 (ptr `PairE` size `PairE` ab) -> BoxedRef ptr size ab
      _ -> error "impossible"
    _ -> error "impossible"

instance InjectableE Atom
instance HoistableE  Atom
instance AlphaEqE Atom
instance SubstE Name Atom

instance SubstE AtomSubstVal Atom where
  substE (scope, env) atom = case fromE atom of
    LeftE specialCase -> case specialCase of
      -- Var
      Case0 v -> do
        case env ! v of
          Rename v' -> Var v'
          SubstVal x -> x
      -- ProjectElt
      Case1 (PairE (LiftE idxs) v) -> do
        let v' = case env ! v of
                   SubstVal x -> x
                   Rename v''  -> Var v''
        getProjection (NE.toList idxs) v'
      Case1 _ -> error "impossible"
      _ -> error "impossible"
    RightE rest -> (toE . RightE) $ substE (scope, env) rest

instance GenericE Expr where
  type RepE Expr =
     EitherE5
        (PairE Atom Atom)
        (PairE Atom (PairE (ListE Alt) Type))
        (Atom)
        (ComposeE PrimOp Atom)
        (ComposeE PrimHof Atom)
  fromE = \case
    App f e        -> Case0 (PairE f e)
    Case e alts ty -> Case1 (PairE e (PairE (ListE alts) ty))
    Atom x         -> Case2 (x)
    Op op          -> Case3 (ComposeE op)
    Hof hof        -> Case4 (ComposeE hof)

  toE = \case
    Case0 (PairE f e)                       -> App f e
    Case1 (PairE e (PairE (ListE alts) ty)) -> Case e alts ty
    Case2 (x)                               -> Atom x
    Case3 (ComposeE op)                     -> Op op
    Case4 (ComposeE hof)                    -> Hof hof
    _ -> error "impossible"

instance InjectableE Expr
instance HoistableE  Expr
instance AlphaEqE Expr
instance SubstE Name Expr
instance SubstE AtomSubstVal Expr

instance GenericE (ExtLabeledItemsE e1 e2) where
  type RepE (ExtLabeledItemsE e1 e2) = EitherE (ComposeE LabeledItems e1)
                                               (ComposeE LabeledItems e1 `PairE` e2)
  fromE (ExtLabeledItemsE (Ext items Nothing))  = LeftE  (ComposeE items)
  fromE (ExtLabeledItemsE (Ext items (Just t))) = RightE (ComposeE items `PairE` t)

  toE (LeftE  (ComposeE items          )) = ExtLabeledItemsE (Ext items Nothing)
  toE (RightE (ComposeE items `PairE` t)) = ExtLabeledItemsE (Ext items (Just t))

instance (InjectableE e1, InjectableE e2) => InjectableE (ExtLabeledItemsE e1 e2)
instance (HoistableE  e1, HoistableE  e2) => HoistableE  (ExtLabeledItemsE e1 e2)
instance (AlphaEqE    e1, AlphaEqE    e2) => AlphaEqE    (ExtLabeledItemsE e1 e2)
instance (SubstE Name e1, SubstE Name e2) => SubstE Name (ExtLabeledItemsE e1 e2)

instance SubstE AtomSubstVal (ExtLabeledItemsE Atom AtomName) where
  substE (scope, env) (ExtLabeledItemsE (Ext items maybeExt)) = do
    let items' = fmap (substE (scope, env)) items
    let ext = case maybeExt of
                Nothing -> NoExt NoLabeledItems
                Just v -> case env ! v of
                  Rename        v'  -> Ext NoLabeledItems $ Just v'
                  SubstVal (Var v') -> Ext NoLabeledItems $ Just v'
                  SubstVal (LabeledRow row) -> row
                  _ -> error "Not a valid labeled row substitution"
    ExtLabeledItemsE $ prefixExtLabeledItems items' ext

instance GenericE Block where
  type RepE Block = PairE Type (Abs (Nest Decl) Expr)
  fromE (Block ty decls result) = PairE ty (Abs decls result)
  toE   (PairE ty (Abs decls result)) = Block ty decls result
instance InjectableE Block
instance HoistableE  Block
instance AlphaEqE Block
instance SubstE Name Block
instance SubstE AtomSubstVal Block
deriving instance Show (Block n)
deriving via WrapE Block n instance Generic (Block n)

instance GenericB LamBinder where
  type RepB LamBinder =         LiftB (PairE Type (LiftE Arrow))
                        `PairB` NameBinder AtomNameC
                        `PairB` LiftB EffectRow
  fromB (LamBinder b ty arr effs) = LiftB (PairE ty (LiftE arr))
                            `PairB` b
                            `PairB` LiftB effs
  toB (       LiftB (PairE ty (LiftE arr))
      `PairB` b
      `PairB` LiftB effs) = LamBinder b ty arr effs

instance BindsBindings LamBinder where
  toBindingsFrag (LamBinder b ty arrow effects) =
    withExtEvidence b do
      let binding = toBinding $ inject $ LamBinding arrow ty
      BindingsFrag (RecEnvFrag $ b @> binding)
                   (Just $ inject effects)

instance BindsAtMostOneName LamBinder AtomNameC where
  LamBinder b _ _ _ @> x = b @> x

instance BindsOneName LamBinder AtomNameC where
  binderName (LamBinder b _ _ _) = binderName b

instance BindsOneAtomName LamBinder where
  boundAtomBinding (LamBinder _ ty arr _) =
    LamBound $ LamBinding arr ty

instance ProvesExt  LamBinder
instance BindsNames LamBinder
instance InjectableB LamBinder
instance HoistableB  LamBinder
instance SubstB Name LamBinder
instance SubstB AtomSubstVal LamBinder
instance AlphaEqB LamBinder

instance GenericE LamBinding where
  type RepE LamBinding = PairE (LiftE Arrow) Type
  fromE (LamBinding arr ty) = PairE (LiftE arr) ty
  toE   (PairE (LiftE arr) ty) = LamBinding arr ty

instance InjectableE LamBinding
instance HoistableE  LamBinding
instance SubstE Name LamBinding
instance SubstE AtomSubstVal LamBinding
instance AlphaEqE LamBinding

instance GenericE LamExpr where
  type RepE LamExpr = Abs LamBinder Block
  fromE (LamExpr b block) = Abs b block
  toE   (Abs b block) = LamExpr b block

instance InjectableE LamExpr
instance HoistableE  LamExpr
instance AlphaEqE LamExpr
instance SubstE Name LamExpr
instance SubstE AtomSubstVal LamExpr
deriving instance Show (LamExpr n)
deriving via WrapE LamExpr n instance Generic (LamExpr n)

instance GenericE PiBinding where
  type RepE PiBinding = PairE (LiftE Arrow) Type
  fromE (PiBinding arr ty) = PairE (LiftE arr) ty
  toE   (PairE (LiftE arr) ty) = PiBinding arr ty

instance InjectableE PiBinding
instance HoistableE  PiBinding
instance SubstE Name PiBinding
instance SubstE AtomSubstVal PiBinding
instance AlphaEqE PiBinding

instance GenericB PiBinder where
  type RepB PiBinder = BinderP AtomNameC (PairE Type (LiftE Arrow))
  fromB (PiBinder b ty arr) = b :> PairE ty (LiftE arr)
  toB   (b :> PairE ty (LiftE arr)) = PiBinder b ty arr

instance BindsAtMostOneName PiBinder AtomNameC where
  PiBinder b _ _ @> x = b @> x

instance BindsOneName PiBinder AtomNameC where
  binderName (PiBinder b _ _) = binderName b

instance BindsOneAtomName PiBinder where
  boundAtomBinding (PiBinder _ ty arr) =
    PiBound $ PiBinding arr ty

instance BindsBindings PiBinder where
  toBindingsFrag (PiBinder b ty arr) =
    withExtEvidence b do
      let binding = toBinding $ inject $ PiBinding arr ty
      BindingsFrag (RecEnvFrag $ b @> binding) (Just Pure)

instance ProvesExt  PiBinder
instance BindsNames PiBinder
instance InjectableB PiBinder
instance HoistableB  PiBinder
instance SubstB Name PiBinder
instance SubstB AtomSubstVal PiBinder
instance AlphaEqB PiBinder

instance GenericE PiType where
  type RepE PiType = Abs PiBinder (PairE EffectRow Type)
  fromE (PiType b eff resultTy) = Abs b (PairE eff resultTy)
  toE   (Abs b (PairE eff resultTy)) = PiType b eff resultTy

instance InjectableE PiType
instance HoistableE  PiType
instance AlphaEqE PiType
instance SubstE Name PiType
instance SubstE AtomSubstVal PiType
deriving instance Show (PiType n)
deriving via WrapE PiType n instance Generic (PiType n)

instance GenericE (EffectP name) where
  type RepE (EffectP name) =
    EitherE (PairE (LiftE RWS) name)
            (LiftE (Either () ()))
  fromE = \case
    RWSEffect rws name -> LeftE  (PairE (LiftE rws) name)
    ExceptionEffect -> RightE (LiftE (Left  ()))
    IOEffect        -> RightE (LiftE (Right ()))
  toE = \case
    LeftE  (PairE (LiftE rws) name) -> RWSEffect rws name
    RightE (LiftE (Left  ())) -> ExceptionEffect
    RightE (LiftE (Right ())) -> IOEffect

instance InjectableE   name => InjectableE   (EffectP name)
instance HoistableE    name => HoistableE    (EffectP name)
instance AlphaEqE      name => AlphaEqE      (EffectP name)
instance SubstE Name (EffectP AtomName)
instance SubstE AtomSubstVal (EffectP AtomName) where
  substE (_, env) eff = case eff of
    RWSEffect rws v -> do
      let v' = case env ! v of
                 Rename        v''  -> v''
                 SubstVal (Var v'') -> v''
                 SubstVal _ -> error "Heap parameter must be a name"
      RWSEffect rws v'
    ExceptionEffect -> ExceptionEffect
    IOEffect        -> IOEffect

instance OrdE name => GenericE (EffectRowP name) where
  type RepE (EffectRowP name) = PairE (ListE (EffectP name)) (MaybeE name)
  fromE (EffectRow effs ext) = ListE (S.toList effs) `PairE` ext'
    where ext' = case ext of Just v  -> JustE v
                             Nothing -> NothingE
  toE (ListE effs `PairE` ext) = EffectRow (S.fromList effs) ext'
    where ext' = case ext of JustE v  -> Just v
                             NothingE -> Nothing
                             _ -> error "impossible"

instance InjectableE (EffectRowP AtomName)
instance HoistableE  (EffectRowP AtomName)
instance SubstE Name (EffectRowP AtomName)
instance AlphaEqE    (EffectRowP AtomName)

instance SubstE AtomSubstVal (EffectRowP AtomName) where
  substE env (EffectRow effs tailVar) = do
    let effs' = S.fromList $ map (substE env) (S.toList effs)
    let tailEffRow = case tailVar of
          Nothing -> EffectRow mempty Nothing
          Just v -> case snd env ! v of
            Rename        v'  -> EffectRow mempty (Just v')
            SubstVal (Var v') -> EffectRow mempty (Just v')
            SubstVal (Eff r)  -> r
            _ -> error "Not a valid effect substitution"
    extendEffRow effs' tailEffRow

instance GenericE SynthCandidates where
  type RepE SynthCandidates = PairE (ListE Atom) (PairE (ListE Atom) (ListE Atom))
  fromE (SynthCandidates xs ys zs) = PairE (ListE xs) (PairE (ListE ys) (ListE zs))
  toE   (PairE (ListE xs) (PairE (ListE ys) (ListE zs))) = SynthCandidates xs ys zs

instance InjectableE SynthCandidates
instance HoistableE  SynthCandidates
instance SubstE Name SynthCandidates
instance SubstE AtomSubstVal SynthCandidates

instance GenericE AtomBinding where
  type RepE AtomBinding =
     EitherE5
        DeclBinding
        LamBinding
        PiBinding
        Type
        SolverBinding

  fromE = \case
    LetBound    x -> Case0 x
    LamBound    x -> Case1 x
    PiBound     x -> Case2 x
    MiscBound   x -> Case3 x
    SolverBound x -> Case4 x

  toE = \case
    Case0 x -> LetBound x
    Case1 x -> LamBound x
    Case2 x -> PiBound  x
    Case3 x -> MiscBound x
    Case4 x -> SolverBound x
    _ -> error "impossible"

instance InjectableE AtomBinding
instance HoistableE  AtomBinding
instance SubstE Name AtomBinding
instance SubstE AtomSubstVal AtomBinding
instance AlphaEqE AtomBinding

instance GenericE SolverBinding where
  type RepE SolverBinding = EitherE2
                              (PairE Type (LiftE SrcPosCtx))
                              Type
  fromE = \case
    InfVarBound  ty ctx -> Case0 (PairE ty (LiftE ctx))
    SkolemBound  ty     -> Case1 ty

  toE = \case
    Case0 (PairE ty (LiftE ct)) -> InfVarBound  ty ct
    Case1 ty                    -> SkolemBound  ty
    _ -> error "impossible"

instance InjectableE SolverBinding
instance HoistableE  SolverBinding
instance SubstE Name SolverBinding
instance SubstE AtomSubstVal SolverBinding
instance AlphaEqE SolverBinding

instance NameColor c => GenericE (Binding c) where
  type RepE (Binding c) =
    EitherE2
      (EitherE5
          AtomBinding
          DataDef
          DataDefName
          (DataDefName `PairE` LiftE Int)
          ClassDef)
      (EitherE2
          (Name ClassNameC `PairE` LiftE Int `PairE` Atom)
          (Name ClassNameC `PairE` LiftE Int `PairE` Atom))
  fromE binding = case binding of
    AtomNameBinding   tyinfo          -> Case0 $ Case0 $ tyinfo
    DataDefBinding    dataDef         -> Case0 $ Case1 $ dataDef
    TyConBinding      dataDefName     -> Case0 $ Case2 $ dataDefName
    DataConBinding    dataDefName idx -> Case0 $ Case3 $ dataDefName `PairE` LiftE idx
    ClassBinding      classDef        -> Case0 $ Case4 $ classDef
    SuperclassBinding className idx e -> Case1 $ Case0 $ className `PairE` LiftE idx `PairE` e
    MethodBinding     className idx e -> Case1 $ Case1 $ className `PairE` LiftE idx `PairE` e

  toE rep = case rep of
    Case0 (Case0 tyinfo)                                  -> fromJust $ tryAsColor $ AtomNameBinding   tyinfo
    Case0 (Case1 dataDef)                                 -> fromJust $ tryAsColor $ DataDefBinding    dataDef
    Case0 (Case2 dataDefName)                             -> fromJust $ tryAsColor $ TyConBinding      dataDefName
    Case0 (Case3 (dataDefName `PairE` LiftE idx))         -> fromJust $ tryAsColor $ DataConBinding    dataDefName idx
    Case0 (Case4 classDef)                                -> fromJust $ tryAsColor $ ClassBinding      classDef
    Case1 (Case0 (className `PairE` LiftE idx `PairE` e)) -> fromJust $ tryAsColor $ SuperclassBinding className idx e
    Case1 (Case1 (className `PairE` LiftE idx `PairE` e)) -> fromJust $ tryAsColor $ MethodBinding     className idx e
    _ -> error "impossible"

deriving via WrapE (Binding c) n instance NameColor c => Generic (Binding c n)
instance InjectableV         Binding
instance HoistableV          Binding
instance SubstV Name         Binding
instance SubstV AtomSubstVal Binding
instance NameColor c => InjectableE         (Binding c)
instance NameColor c => HoistableE          (Binding c)
instance NameColor c => SubstE Name         (Binding c)
instance NameColor c => SubstE AtomSubstVal (Binding c)

instance GenericE DeclBinding where
  type RepE DeclBinding = LiftE LetAnn `PairE` Type `PairE` Expr
  fromE (DeclBinding ann ty expr) = LiftE ann `PairE` ty `PairE` expr
  toE   (LiftE ann `PairE` ty `PairE` expr) = DeclBinding ann ty expr

instance InjectableE DeclBinding
instance HoistableE  DeclBinding
instance SubstE Name DeclBinding
instance SubstE AtomSubstVal DeclBinding
instance AlphaEqE DeclBinding

instance GenericB Decl where
  type RepB Decl = AtomBinderP DeclBinding
  fromB (Let b binding) = b :> binding
  toB   (b :> binding) = Let b binding

instance InjectableB Decl
instance HoistableB  Decl
instance SubstB AtomSubstVal Decl
instance SubstB Name Decl
instance AlphaEqB Decl
instance ProvesExt  Decl
instance BindsNames Decl
instance BindsBindings Decl

instance Pretty Arrow where
  pretty arr = case arr of
    PlainArrow     -> "->"
    TabArrow       -> "=>"
    LinArrow       -> "--o"
    ImplicitArrow  -> "?->"
    ClassArrow     -> "?=>"

instance Semigroup (SynthCandidates n) where
  SynthCandidates xs ys zs <> SynthCandidates xs' ys' zs' =
    SynthCandidates (xs<>xs') (ys<>ys') (zs<>zs')

instance Monoid (SynthCandidates n) where
  mempty = SynthCandidates mempty mempty mempty

instance GenericE SourceMap where
  type RepE SourceMap = ListE (PairE (LiftE SourceName) (EnvVal Name))
  fromE (SourceMap m) = ListE [PairE (LiftE v) def | (v, def) <- M.toList m]
  toE   (ListE pairs) = SourceMap $ M.fromList [(v, def) | (PairE (LiftE v) def) <- pairs]

deriving via WrapE SourceMap n instance Generic (SourceMap n)
-- instance Generic (SourceMap n) where
--   type Rep (SourceMap n) = Rep ()

instance InjectableE SourceMap
instance SubstE Name SourceMap
instance HoistableE  SourceMap

instance Pretty (SourceMap n) where
  pretty (SourceMap m) =
    fold [pretty v <+> "@>" <+> pretty x <> hardline | (v, x) <- M.toList m ]

instance GenericE Module where
  type RepE Module = LiftE IRVariant `PairE` Abs (Nest Decl) EvaluatedModule
  fromE = undefined
  toE = undefined

instance InjectableE Module
instance SubstE Name Module

instance GenericE EvaluatedModule where
  type RepE EvaluatedModule = Abs BindingsFrag (PairE SynthCandidates SourceMap)
  fromE (EvaluatedModule bs scs sm) = Abs bs (PairE scs sm)
  toE   (Abs bs (PairE scs sm)) = EvaluatedModule bs scs sm

instance InjectableE EvaluatedModule
instance HoistableE EvaluatedModule
instance SubstE Name EvaluatedModule

instance Store (Atom n)
instance Store (Expr n)
instance Store (SolverBinding n)
instance Store (AtomBinding n)
instance Store (LamBinding  n)
instance Store (DeclBinding n)
instance Store (Decl n l)
instance Store (DataDef n)
instance Store (DataConDef n)
instance Store (Block n)
instance Store (LamBinder n l)
instance Store (LamExpr n)
instance Store (PiBinding n)
instance Store (PiBinder n l)
instance Store (PiType  n)
instance Store Arrow
instance Store (ClassDef       n)
instance Store (SourceMap n)
instance Store (SynthCandidates n)
instance Store (EffectRow n)
instance Store (Effect n)
instance Store (DataConRefBinding n l)
instance Store (TopState n)
instance NameColor c => Store (Binding c n)

instance IsString (SourceNameOr a VoidS) where
  fromString = SourceName

instance IsString (UBinder s VoidS VoidS) where
  fromString = UBindSource

instance IsString (UPat' VoidS VoidS) where
  fromString = UPatBinder . fromString

instance IsString (UPatAnn VoidS VoidS) where
  fromString s = UPatAnn (fromString s) Nothing

instance IsString (UExpr' VoidS) where
  fromString = UVar . fromString

instance IsString (a n) => IsString (WithSrcE a n) where
  fromString = WithSrcE Nothing . fromString

instance IsString (b n l) => IsString (WithSrcB b n l) where
  fromString = WithSrcB Nothing . fromString

deriving instance Show (UBinder s n l)
deriving instance Show (UDataDefTrail n)
deriving instance Show (ULamExpr n)
deriving instance Show (UPiExpr n)
deriving instance Show (UDeclExpr n)
deriving instance Show (UDataDef n)
deriving instance Show (UDecl n l)
deriving instance Show (UForExpr n)
deriving instance Show (UAlt n)

instance (BindsBindings b1, BindsBindings b2)
         => (BindsBindings (PairB b1 b2)) where
  toBindingsFrag (PairB b1 b2) = do
    let bindings2 = toBindingsFrag b2
    let ext = toExtEvidence bindings2
    withSubscopeDistinct ext do
      toBindingsFrag b1 `catBindingsFrags` bindings2

instance BindsBindings b => (BindsBindings (Nest b)) where
  toBindingsFrag Empty = emptyOutFrag
  toBindingsFrag (Nest b rest) = toBindingsFrag $ PairB b rest

instance (BindsBindings b1, BindsBindings b2)
         => (BindsBindings (EitherB b1 b2)) where
  toBindingsFrag (LeftB  b) = toBindingsFrag b
  toBindingsFrag (RightB b) = toBindingsFrag b

instance GenericB BindingsFrag where
  type RepB BindingsFrag = PairB (RecEnvFrag Binding) (LiftB (MaybeE EffectRow))
  fromB (BindingsFrag frag (Just effs)) = PairB frag (LiftB (JustE effs))
  fromB (BindingsFrag frag Nothing    ) = PairB frag (LiftB NothingE)
  toB   (PairB frag (LiftB (JustE effs))) = BindingsFrag frag (Just effs)
  toB   (PairB frag (LiftB NothingE    )) = BindingsFrag frag Nothing
  toB   _ = error "impossible" -- GHC exhaustiveness bug?

instance InjectableB         BindingsFrag
instance HoistableB          BindingsFrag
instance ProvesExt           BindingsFrag
instance BindsNames          BindingsFrag
instance SubstB Name         BindingsFrag
instance SubstB AtomSubstVal BindingsFrag

instance BindsBindings BindingsFrag where
  toBindingsFrag frag = frag

instance BindsBindings UnitB where
  toBindingsFrag UnitB = emptyOutFrag

-- TODO: name subst instances for the rest of UExpr
instance SubstE Name UVar where
  substE env = \case
    UAtomVar    v -> UAtomVar    $ substE env v
    UTyConVar   v -> UTyConVar   $ substE env v
    UDataConVar v -> UDataConVar $ substE env v
    UClassVar   v -> UClassVar   $ substE env v
    UMethodVar  v -> UMethodVar  $ substE env v

instance InjectableE e => InjectableE (WithBindings e) where
  injectionProofE (fresh::InjectionCoercion n l) (WithBindings (bindings :: Bindings h) e) =
    withExtEvidence (injectionProofE fresh ext) $
      WithBindings bindings e
    where ext = getExtEvidence :: ExtEvidence h n

instance InjectableE UVar where
  injectionProofE = todoInjectableProof

instance HasNameHint (b n l) => HasNameHint (WithSrcB b n l) where
  getNameHint (WithSrcB _ b) = getNameHint b

instance HasNameHint (UPat' n l) where
  getNameHint (UPatBinder b) = getNameHint b
  getNameHint _ = "pat"

instance HasNameHint (UBinder c n l) where
  getNameHint b = case b of
    UBindSource v -> getNameHint v
    UIgnore       -> fromString "_ign"
    UBind v       -> getNameHint v

instance BindsNames (UBinder c) where
  toScopeFrag (UBindSource _) = emptyOutFrag
  toScopeFrag (UIgnore)       = emptyOutFrag
  toScopeFrag (UBind b)       = toScopeFrag b

instance ProvesExt (UBinder c) where
instance BindsAtMostOneName (UBinder c) c where
  b @> x = case b of
    UBindSource _ -> emptyInFrag
    UIgnore       -> emptyInFrag
    UBind b'      -> b' @> x

instance ProvesExt (UAnnBinder c) where
instance BindsNames (UAnnBinder c) where
  toScopeFrag (UAnnBinder b _) = toScopeFrag b

instance BindsAtMostOneName (UAnnBinder c) c where
  UAnnBinder b _ @> x = b @> x

instance InjectableE UModule where
  injectionProofE = todoInjectableProof

instance Eq SourceBlock where
  x == y = sbText x == sbText y

instance Ord SourceBlock where
  compare x y = compare (sbText x) (sbText y)
