-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DefaultSignatures #-}

module Syntax (
    Type, Kind, BaseType (..), ScalarBaseType (..), Except,
    EffectP (..), Effect, UEffect, RWS (..), EffectRowP (..), EffectRow, UEffectRow,
    Binder, Block (..), BlockAnn (..), Decl (..), DeclBinding (..),
    FieldRowElem (..), FieldRowElems, fromFieldRowElems,
    fieldRowElemsFromList, prependFieldRowElem, extRowAsFieldRowElems, fieldRowElemsAsExtRow,
    pattern StaticRecordTy, pattern RecordTyWithElems,
    Expr (..), Atom (..), Arrow (..), PrimTC (..), Abs (..),
    PrimExpr (..), PrimCon (..), LitVal (..), PtrLitVal (..), PtrSnapshot (..),
    PrimEffect (..), PrimOp (..), PrimHof (..),
    LamBinding (..), LamBinder (..), LamExpr (..),
    PiBinding (..), PiBinder (..),
    PiType (..), DepPairType (..), LetAnn (..), SomeDecl (..),
    BinOp (..), UnOp (..), CmpOp (..), SourceMap (..), SourceNameDef (..), LitProg,
    ForAnn (..), Val, Op, Con, Hof, TC,
    ClassDef (..), SynthCandidates (..), Env (..), TopEnv (..), ModuleEnv (..),
    ImportStatus (..), emptyModuleEnv,
    ModuleSourceName (..), LoadedModules (..), Cache (..), ObjectFiles (..),
    BindsEnv (..), BindsOneAtomName (..), WithEnv (..), AtomNameBinder,
    DataConRefBinding (..), AltP, Alt, AtomBinding (..), SolverBinding (..),
    SubstE (..), SubstB (..), Ptr, PtrType,
    AddressSpace (..), Device (..), showPrimName, strToPrimName, primNameToStr,
    Direction (..), Limit (..), DataDef (..), DataConDef (..), Nest (..),
    mkConsList, mkConsListTy, fromConsList, fromConsListTy, fromLeftLeaningConsListTy,
    mkBundle, mkBundleTy, BundleDesc,
    BaseMonoidP (..), BaseMonoid, getIntLit, getFloatLit, sizeOf, ptrSize, vectorWidth,
    IRVariant (..), SubstVal (..), AtomName, DataDefName, ClassName, AtomSubstVal,
    SourceName, SourceNameOr (..), UVar (..), UBinder (..), uBinderSourceName,
    UExpr, UExpr' (..), UConDef, UDataDef (..), UDataDefTrail (..), UDecl (..),
    UFieldRowElems, UFieldRowElem (..),
    ULamExpr (..), UPiExpr (..), UDeclExpr (..), UForExpr (..), UAlt (..),
    UPat, UPat' (..), UPatAnn (..), UPatAnnArrow (..), UFieldRowPat (..),
    UMethodDef (..), UAnnBinder (..),
    WithSrcE (..), WithSrcB (..), srcPos,
    SourceBlock (..), SourceBlock' (..), EnvQuery (..),
    ModuleName, Module (..), UModule (..), UModulePartialParse (..),
    UMethodType(..), UType, ExtLabeledItemsE (..),
    CmdName (..), LogLevel (..), OutFormat (..),
    EnvReader (..), EnvReaderI (..), EnvReaderIT (..), runEnvReaderIT,
    extendI, liftEnvReaderI, refreshAbsI, refreshLamI,
    EnvExtender (..),  Binding (..),
    TopEnvFrag (..), ToBinding (..), PartialTopEnvFrag (..), withFreshBinders,
    refreshBinders, substBinders, withFreshBinder,
    withFreshLamBinder, withFreshPureLamBinder, captureClosure,
    withFreshPiBinder, piBinderToLamBinder, catEnvFrags,
    EnvFrag (..), lookupEnv, lookupDataDef, lookupAtomName, lookupImpFun, lookupModule,
    lookupEnvPure, lookupSourceMap, lookupSourceMapPure,
    withEnv, updateEnv, runEnvReaderT, liftEnvReaderM,
    liftEnvReaderT, liftSubstEnvReaderM,
    SubstEnvReaderM,
    EnvReaderM, runEnvReaderM,
    EnvReaderT (..), EnvReader2, EnvExtender2, DistinctEnv (..),
    naryNonDepPiType, nonDepPiType, fromNonDepPiType, fromNaryNonDepPiType,
    considerNonDepPiType, trySelectBranch,
    fromNonDepTabTy, nonDepDataConTys, binderType, bindersTypes,
    atomBindingType, getProjection,
    applyIntBinOp, applyIntCmpOp, applyFloatBinOp, applyFloatUnOp,
    piArgType, lamArgType, piArrow, extendEffRow,
    bindingsFragToSynthCandidates,
    getLambdaDicts, getSuperclassProjs, getInstanceDicts,
    getAllowedEffects, withAllowedEffects, todoSinkableProof,
    FallibleT1, runFallibleT1, abstractPtrLiterals, freeAtomVarsList,
    IExpr (..), IBinder (..), IPrimOp, IVal, IType, Size, IFunType (..),
    ImpFunction (..), ImpBlock (..), ImpDecl (..),
    ImpInstr (..), iBinderType,
    ImpFunName, IFunVar, CallingConvention (..), CUDAKernel (..), Backend (..),
    Output (..), PassName (..), Result (..), BenchStats,
    IsCUDARequired (..),
    NaryLamExpr (..), NaryPiType (..), fromNaryLam, fromNaryPiType,
    NonEmpty (..), nonEmpty,
    naryLamExprAsAtom, naryPiTypeAsType,
    ObjectFile (..), ObjectFileName, CFunName, CFun (..),
    pattern IdxRepTy, pattern IdxRepVal,
    pattern IIdxRepTy, pattern IIdxRepVal,
    pattern TagRepTy,
    pattern TagRepVal, pattern Word8Ty,
    pattern UnitTy, pattern PairTy,
    pattern FixedIntRange, pattern Fin, pattern RefTy, pattern RawRefTy,
    pattern BaseTy, pattern PtrTy, pattern UnitVal,
    pattern PairVal, pattern TyKind,
    pattern Pure, pattern LabeledRowKind, pattern EffKind, pattern UPatIgnore,
    pattern IntLitExpr, pattern FloatLitExpr, pattern ProdTy, pattern ProdVal,
    pattern TabTyAbs, pattern TabTy, pattern TabVal,
    pattern SumTy, pattern SumVal, pattern MaybeTy, pattern BinaryFunTy,
    pattern BinaryLamExpr,
    pattern NothingAtom, pattern JustAtom, pattern AtomicBlock,
    pattern BoolTy, pattern FalseAtom, pattern TrueAtom,
    (-->), (?-->), (--@), (==>) ) where

import Data.Functor
import Data.Foldable (toList, fold)
import Data.Tuple (swap)
import Data.Hashable
import Control.Applicative
import Control.Monad.Except hiding (Except)
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer.Strict (Writer, execWriter, tell)
import qualified Control.Monad.Trans.Except as MTE
import qualified Data.ByteString       as BS
import qualified Data.ByteString.Char8 as B
import qualified Data.List.NonEmpty    as NE
import Data.List.NonEmpty (NonEmpty (..), nonEmpty)
import qualified Data.Map.Strict       as M
import qualified Data.Set              as S
import Data.Int
import Data.String (IsString, fromString)
import Data.Text.Prettyprint.Doc (Pretty (..), hardline, (<+>))
import Data.Word
import Data.Maybe (catMaybes)
import Foreign.Ptr
import Data.Maybe (fromJust)

import GHC.Stack
import GHC.Generics (Generic (..))
import Data.Store (Store (..))
import qualified Data.Store.Internal as SI

import Name
import Err
import LabeledItems
import Util ((...), enumerate, IsBool (..), File (..), FileHash, foldMapM)

-- === core IR ===

data Atom (n::S) =
   Var (AtomName n)
 | Lam (LamExpr n)
 | Pi  (PiType  n)
 | DepPairTy (DepPairType n)
 | DepPair   (Atom n) (Atom n) (DepPairType n)
   -- SourceName is purely for printing
 | DataCon SourceName (DataDefName n) [Atom n] Int [Atom n]
 | TypeCon SourceName (DataDefName n) [Atom n]
 | LabeledRow (FieldRowElems n)
 | Record (LabeledItems (Atom n))
 | RecordTy  (FieldRowElems n)
 | Variant   (ExtLabeledItems (Type n) (AtomName n)) Label Int (Atom n)
 | VariantTy (ExtLabeledItems (Type n) (AtomName n))
 | Con (Con n)
 | TC  (TC  n)
 | Eff (EffectRow n)
   -- only used within Simplify
 | ACase (Atom n) [AltP Atom n] (Type n)
   -- single-constructor only for now
 | DataConRef (DataDefName n) [Atom n] (EmptyAbs (Nest DataConRefBinding) n)
 -- lhs ref, rhs ref abstracted over the eventual value of lhs ref, type
 | DepPairRef (Atom n) (Abs Binder Atom n) (DepPairType n)
 | BoxedRef [(Atom n, Block n)]        -- ptrptrs/sizes
            (NaryAbs AtomNameC Atom n) -- abstracted dest
 -- access a nested member of a binder
 -- XXX: Variable name must not be an alias for another name or for
 -- a statically-known atom. This is because the variable name used
 -- here may also appear in the type of the atom. (We maintain this
 -- invariant during substitution and in Builder.hs.)
 | ProjectElt (NE.NonEmpty Int) (AtomName n)
   deriving (Show, Generic)

data Expr n =
   App (Atom n) (NonEmpty (Atom n))
 | Case (Atom n) [Alt n] (Type n) (EffectRow n)
 | Atom (Atom n)
 | Op  (Op  n)
 | Hof (Hof n)
   deriving (Show, Generic)

data DeclBinding n = DeclBinding LetAnn (Type n) (Expr n)
     deriving (Show, Generic)
data Decl n l = Let (NameBinder AtomNameC n l) (DeclBinding n)
     deriving (Show, Generic)

type AtomName    = Name AtomNameC
type DataDefName = Name DataDefNameC
type ClassName   = Name ClassNameC
type ModuleName  = Name ModuleNameC
type PtrName     = Name PtrNameC

type AtomNameBinder = NameBinder AtomNameC

data DataConRefBinding (n::S) (l::S) = DataConRefBinding (Binder n l) (Atom n)

type AtomBinderP = BinderP AtomNameC
type Binder = AtomBinderP Type
type AltP (e::E) = Abs (Nest Binder) e :: E
type Alt = AltP Block                  :: E

-- The additional invariant enforced by this newtype is that the list should
-- never contain empty StaticFields members, nor StaticFields in two consecutive
-- positions.
newtype FieldRowElems (n::S) = UnsafeFieldRowElems { fromFieldRowElems :: [FieldRowElem n] }
                               deriving (Show, Generic)

data FieldRowElem (n::S)
  = StaticFields (LabeledItems (Type n))
  | DynField     (AtomName n) (Type n)
  | DynFields    (AtomName n)
  deriving (Show, Generic)

data DataDef n where
  -- The `SourceName` is just for pretty-printing. The actual alpha-renamable
  -- binder name is in UExpr and Env
  DataDef :: SourceName -> Nest Binder n l -> [DataConDef l] -> DataDef n

-- As above, the `SourceName` is just for pretty-printing
data DataConDef n =
  DataConDef SourceName (EmptyAbs (Nest Binder) n)
  deriving (Show, Generic)

data ClassDef n =
  ClassDef SourceName [SourceName] (DataDefName n)
  deriving (Show, Generic)

-- The Type is the type of the result expression (and thus the type of the
-- block). It's given by querying the result expression's type, and checking
-- that it doesn't have any free names bound by the decls in the block. We store
-- it separately as an optimization, to avoid having to traverse the block.
-- If the decls are empty we can skip the type annotation, because then we can
-- cheaply query the result, and, more importantly, there's no risk of having a
-- type that mentions local variables.
data Block n where
  Block :: BlockAnn n l -> Nest Decl n l -> Expr l -> Block n

data BlockAnn n l where
  BlockAnn :: Type n -> BlockAnn n l
  NoBlockAnn :: BlockAnn n n

data LamBinding (n::S) = LamBinding Arrow (Type n)
  deriving (Show, Generic)

data LamBinder (n::S) (l::S) =
  LamBinder (NameBinder AtomNameC n l) (Type n) Arrow (EffectRow l)
  deriving (Show, Generic)

data LamExpr (n::S) where
  LamExpr :: LamBinder n l -> Block l -> LamExpr n

-- TODO: sometimes I wish we'd written these this way instead:
--   data NaryLamExpr (n::S) where
--     UnaryLamExpr :: LamExpr n -> NaryLamExpr n
--     NaryLamExpr :: Binder n l -> NaryLamExpr l -> NaryLamExpr n
-- maybe we should at least make a pattern so we can use it either way.
data NaryLamExpr (n::S) where
  NaryLamExpr :: NonEmptyNest Binder n l -> EffectRow l -> Block l
              -> NaryLamExpr n

data NaryPiType (n::S) where
  NaryPiType :: NonEmptyNest PiBinder n l -> EffectRow l -> Type l
             -> NaryPiType n

data PiBinding (n::S) = PiBinding Arrow (Type n)
  deriving (Show, Generic)

data PiBinder (n::S) (l::S) =
  PiBinder (NameBinder AtomNameC n l) (Type n) Arrow
  deriving (Show, Generic)

data PiType  (n::S) where
  PiType :: PiBinder n l -> EffectRow l -> Type l -> PiType n

data DepPairType (n::S) where
  DepPairType :: Binder n l -> Type  l -> DepPairType n

data Arrow =
   PlainArrow
 | ImplicitArrow
 | ClassArrow
 | TabArrow
 | LinArrow
   deriving (Show, Eq, Generic)

data LetAnn = PlainLet
            | InstanceLet
            | NoInlineLet
              deriving (Show, Eq, Generic)

type Val  = Atom
type Type = Atom
type Kind = Type

type TC  n = PrimTC  (Atom n)
type Con n = PrimCon (Atom n)
type Op  n = PrimOp  (Atom n)
type Hof n = PrimHof (Atom n)

type AtomSubstVal = SubstVal AtomNameC Atom :: V

-- === envs and modules ===

-- `ModuleEnv` contains data that only makes sense in the context of evaluating
-- a particular module. `TopEnv` contains everything that makes sense "between"
-- evaluating modules.
data Env n = Env
  { topEnv    :: TopEnv n
  , moduleEnv :: ModuleEnv n }
  deriving (Generic)

data TopEnv (n::S) = TopEnv
  { envScope :: Scope n
  , envDefs  :: RecSubst Binding n
  , envCache :: Cache n
  , envLoadedModules :: LoadedModules n }
  deriving (Generic)

-- TODO: consider splitting this further into `ModuleEnv` (the env that's
-- relevant between top-level decls) and `LocalEnv` (the additional parts of the
-- env that's relevant under a lambda binder). Unlike the Top/Module
-- distinction, there's some overlap. For example, instances can be defined at
-- both the module-level and local level. Similarly, if we start allowing
-- top-level effects in `Main` then we'll have module-level effects and local
-- effects.
data ModuleEnv (n::S) = ModuleEnv
  { envImportStatus    :: ImportStatus n
  , envSourceMap       :: SourceMap n
  , envSynthCandidates :: SynthCandidates n
  , envObjectFiles     :: ObjectFiles n
  -- TODO: should these live elsewhere?
  , allowedEffects       :: EffectRow n }
  deriving (Generic)

data Module (n::S) = Module
  { moduleSourceName :: ModuleSourceName
  , moduleDirectDeps :: S.Set (ModuleName n)
  , moduleTransDeps  :: S.Set (ModuleName n)  -- XXX: doesn't include the module itself
  , moduleExports    :: SourceMap n
    -- these are just the synth candidates and object files required by this
    -- module by itself. We'll usually also need those required by the module's
    -- (transitive) dependencies, which must be looked up separately.
  , moduleSynthCandidates :: SynthCandidates n
  , moduleObjectFiles     :: ObjectFiles n }
  deriving (Show, Generic)

data ModuleSourceName = Prelude | Main | OrdinaryModule SourceName
     deriving (Show, Eq, Ord, Generic)

data LoadedModules (n::S) = LoadedModules
  { fromLoadedModules   :: M.Map ModuleSourceName (ModuleName n)}
  deriving (Show, Generic)

emptyModuleEnv :: ModuleEnv n
emptyModuleEnv = ModuleEnv emptyImportStatus (SourceMap mempty) mempty mempty Pure

emptyLoadedModules :: LoadedModules n
emptyLoadedModules = LoadedModules mempty

data ImportStatus (n::S) = ImportStatus
  { directImports :: S.Set (ModuleName n)
    -- XXX: This are cached for efficiency. It's derivable from `directImports`.
  , transImports           :: S.Set (ModuleName n) }
  deriving (Show, Generic)

emptyImportStatus :: ImportStatus n
emptyImportStatus = ImportStatus mempty mempty

-- Parsed just enough to know the dependencies.
data UModulePartialParse = UModulePartialParse
  { umppName          :: ModuleSourceName
  , umppDirectImports :: [ModuleSourceName]
  , umppSource        :: File }
  deriving (Show, Generic)

data UModule = UModule
  { uModuleName          :: ModuleSourceName
  , uModuleDirectImports :: [ModuleSourceName]
  , uModuleSourceBlocks  :: [SourceBlock] }
  deriving (Show, Generic)

-- TODO: figure out the additional top-level context we need -- backend, other
-- compiler flags etc. We can have a map from those to this.
data Cache (n::S) = Cache
  { simpCache :: EMap AtomName AtomName n
  , impCache  :: EMap AtomName ImpFunName n
  , objCache  :: EMap ImpFunName CFun n
    -- This is memoizing `parseAndGetDeps :: Text -> [ModuleSourceName]`. But we
    -- only want to store one entry per module name as a simple cache eviction
    -- policy, so we store it keyed on the module name, with the text hash for
    -- the validity check.
  , parsedDeps :: M.Map ModuleSourceName (FileHash, [ModuleSourceName])
  , moduleEvaluations :: M.Map ModuleSourceName ((FileHash, [ModuleName n]), ModuleName n)
  } deriving (Show, Generic)

-- === bindings - static information we carry about a lexical scope ===

-- TODO: consider making this an open union via a typeable-like class
data Binding (c::C) (n::S) where
  AtomNameBinding   :: AtomBinding n                      -> Binding AtomNameC       n
  DataDefBinding    :: DataDef n                          -> Binding DataDefNameC    n
  TyConBinding      :: DataDefName n        -> Atom n -> Binding TyConNameC      n
  DataConBinding    :: DataDefName n -> Int -> Atom n -> Binding DataConNameC    n
  ClassBinding      :: ClassDef n -> Atom n               -> Binding ClassNameC      n
  SuperclassBinding :: Name ClassNameC n -> Int -> Atom n -> Binding SuperclassNameC n
  MethodBinding     :: Name ClassNameC n -> Int -> Atom n -> Binding MethodNameC     n
  ImpFunBinding     :: ImpFunction n                      -> Binding ImpFunNameC     n
  ObjectFileBinding :: ObjectFile n                       -> Binding ObjectFileNameC n
  ModuleBinding     :: Module n                           -> Binding ModuleNameC     n
  PtrBinding        :: PtrLitVal                          -> Binding PtrNameC        n
deriving instance Show (Binding c n)

data AtomBinding (n::S) =
   LetBound    (DeclBinding   n)
 | LamBound    (LamBinding    n)
 | PiBound     (PiBinding     n)
 | MiscBound   (Type          n)
 | SolverBound (SolverBinding n)
 | PtrLitBound PtrType (PtrName n)
 | SimpLamBound (NaryPiType n) (NaryLamExpr n)  -- first-order functions only
 | FFIFunBound  (NaryPiType n) (ImpFunName n)
   deriving (Show, Generic)

data SolverBinding (n::S) =
   InfVarBound (Type n) SrcPosCtx
 | SkolemBound (Type n)
   deriving (Show, Generic)

data EnvFrag (n::S) (l::S) =
  EnvFrag (RecSubstFrag Binding n l) (Maybe (EffectRow l))

instance HasScope Env where
  toScope = envScope . topEnv

catEnvFrags :: Distinct n3
                 => EnvFrag n1 n2 -> EnvFrag n2 n3 -> EnvFrag n1 n3
catEnvFrags (EnvFrag frag1 maybeEffs1)
                 (EnvFrag frag2 maybeEffs2) =
  withExtEvidence (toExtEvidence frag2) do
    let fragOut = catRecSubstFrags frag1 frag2
    let effsOut = case maybeEffs2 of
                     Nothing    -> fmap sink maybeEffs1
                     Just effs2 -> Just effs2
    EnvFrag fragOut effsOut

instance OutFrag EnvFrag where
  emptyOutFrag = EnvFrag emptyOutFrag Nothing
  catOutFrags _ frag1 frag2 = catEnvFrags frag1 frag2

instance OutMap Env where
  emptyOutMap =
    Env (TopEnv emptyOutMap (RecSubst emptyInFrag) mempty emptyLoadedModules)
        emptyModuleEnv

instance ExtOutMap Env (RecSubstFrag Binding)  where
  extendOutMap (Env (TopEnv scope defs cache loaded)
                    (ModuleEnv imports sm scs objs effs)) frag =
    withExtEvidence frag $ Env
      (TopEnv
        (scope `extendOutMap` toScopeFrag frag)
        (defs  `extendRecSubst` frag)
        (sink cache)
        (sink loaded))
      (ModuleEnv
        (sink imports)
        (sink sm)
        (sink scs <> bindingsFragToSynthCandidates (EnvFrag frag Nothing))
        (sink objs)
        (sink effs))

instance ExtOutMap Env EnvFrag where
  extendOutMap env frag = do
    let EnvFrag newEnv maybeNewEff = frag
    case extendOutMap env newEnv of
      Env envTop (ModuleEnv imports sm scs obs oldEff) -> do
        let newEff = case maybeNewEff of
                       Nothing  -> sink oldEff
                       Just eff -> eff
        Env envTop (ModuleEnv imports sm scs obs newEff)

bindingsFragToSynthCandidates :: Distinct l => EnvFrag n l -> SynthCandidates l
bindingsFragToSynthCandidates (EnvFrag (RecSubstFrag frag) _) =
  execWriter $ bindingsFragToSynthCandidates' $ toSubstPairs frag

bindingsFragToSynthCandidates' :: Distinct l => Nest (SubstPair Binding l) n l
                               -> Writer (SynthCandidates l) ()
bindingsFragToSynthCandidates' nest = case nest of
  Empty -> return ()
  Nest (SubstPair b binding) rest -> withExtEvidence rest do
    case binding of
       AtomNameBinding (LetBound (DeclBinding InstanceLet ty _)) -> do
         let dataDefName = getInstanceLetDataDefName ty
         let m = M.singleton dataDefName [sink $ Var $ binderName b]
         tell $ (SynthCandidates [] [] m)
       AtomNameBinding (LamBound (LamBinding ClassArrow _)) -> do
         tell $ sink (SynthCandidates [Var $ binderName b] [] mempty)
       AtomNameBinding (PiBound (PiBinding ClassArrow _)) -> do
         tell $ sink (SynthCandidates [Var $ binderName b] [] mempty)
       SuperclassBinding _ _ getter ->
         tell $ sink (SynthCandidates [] [getter] mempty)
       _ -> return ()
    bindingsFragToSynthCandidates' rest

getInstanceLetDataDefName :: Type n -> DataDefName n
getInstanceLetDataDefName (Pi (PiType b _ resultTy)) =
  ignoreHoistFailure $ hoist b $ getInstanceLetDataDefName resultTy
getInstanceLetDataDefName (TypeCon _ defName _) = defName
getInstanceLetDataDefName _ = error "not a valid instance type"

data WithEnv (e::E) (n::S) where
  WithEnv :: (Distinct l, Ext l n) => Env l -> e l -> WithEnv e n

class ScopeReader m => EnvReader (m::MonadKind1) where
  -- Unsafe because an in-place update to `n` would invalidate the env.
  unsafeGetEnv :: m n (Env n)

withEnv :: (SinkableE e, EnvReader m) => (Env n -> e n) -> m n (e n)
withEnv f = f <$> unsafeGetEnv

data DistinctEnv n where
  DB :: Distinct n => Env n -> DistinctEnv n

class (EnvReader m, Monad1 m) => EnvExtender (m::MonadKind1) where
  refreshAbs
    :: (BindsEnv b, SubstB Name b, SubstE Name e)
    => Abs b e n
    -> (forall l. DExt n l => b n l -> e l -> m l a)
    -> m n a

type EnvReader2   (m::MonadKind2) = forall (n::S). EnvReader   (m n)
type EnvExtender2 (m::MonadKind2) = forall (n::S). EnvExtender (m n)

instance (SinkableE e, EnvReader m)
         => EnvReader (OutReaderT e m) where
  unsafeGetEnv = OutReaderT $ lift $ unsafeGetEnv

instance (SinkableE e, ScopeReader m, EnvExtender m)
         => EnvExtender (OutReaderT e m) where
  refreshAbs ab cont = OutReaderT $ ReaderT \env ->
    refreshAbs ab \b e -> do
      let OutReaderT (ReaderT cont') = cont b e
      env' <- sinkM env
      cont' env'

newtype EnvReaderT (m::MonadKind) (n::S) (a:: *) =
  EnvReaderT {runEnvReaderT' :: ReaderT (DistinctEvidence n, Env n) m a }
  deriving (Functor, Applicative, Monad, MonadFail, Fallible, Alternative)

type EnvReaderM = EnvReaderT Identity
runEnvReaderM :: Distinct n => Env n -> EnvReaderM n a -> a
runEnvReaderM bindings m = runIdentity $ runEnvReaderT bindings m

runEnvReaderT :: Distinct n => Env n -> EnvReaderT m n a -> m a
runEnvReaderT bindings cont =
  runReaderT (runEnvReaderT' cont) (Distinct, bindings)

liftEnvReaderM :: EnvReader m => EnvReaderM n a -> m n a
liftEnvReaderM cont = liftM runIdentity $ liftEnvReaderT cont

liftEnvReaderT :: EnvReader m' => EnvReaderT m n a -> m' n (m a)
liftEnvReaderT cont = do
  env <- unsafeGetEnv
  Distinct <- getDistinct
  return $ runReaderT (runEnvReaderT' cont) (Distinct, env)

type SubstEnvReaderM v = SubstReaderT v EnvReaderM :: MonadKind2

liftSubstEnvReaderM
  :: (EnvReader m, FromName v)
  => SubstEnvReaderM v n n a
  -> m n a
liftSubstEnvReaderM cont = liftEnvReaderM $ runSubstReaderT idSubst $ cont

instance Monad m => EnvReader (EnvReaderT m) where
  unsafeGetEnv = EnvReaderT $ asks snd

instance Monad m => EnvExtender (EnvReaderT m) where
  refreshAbs ab cont = EnvReaderT $ ReaderT
    \(Distinct, env) -> refreshAbsPure (toScope env) ab
       \_ b e -> do
         let env' = extendOutMap env $ toEnvFrag b
         runReaderT (runEnvReaderT' $ cont b e) (Distinct, env')

instance Monad m => ScopeReader (EnvReaderT m) where
  getDistinct = EnvReaderT $ asks fst
  unsafeGetScope = toScope <$> snd <$> EnvReaderT ask

instance MonadIO m => MonadIO (EnvReaderT m n) where
  liftIO m = EnvReaderT $ lift $ liftIO m

instance (SinkableV v, EnvReader m) => EnvReader (SubstReaderT v m i) where
  unsafeGetEnv = SubstReaderT $ lift unsafeGetEnv

instance (SinkableV v, ScopeReader m, EnvExtender m)
         => EnvExtender (SubstReaderT v m i) where
  refreshAbs ab cont = SubstReaderT $ ReaderT \subst ->
    refreshAbs ab \b e -> do
      subst' <- sinkM subst
      let SubstReaderT (ReaderT cont') = cont b e
      cont' subst'

instance (Monad m, ExtOutMap Env decls)
         => EnvReader   (InplaceT Env decls m) where
  unsafeGetEnv = getOutMapInplaceT

instance (Monad m, ExtOutMap Env decls)
         => EnvExtender (InplaceT Env decls m) where
  refreshAbs ab cont = UnsafeMakeInplaceT \env ->
    refreshAbsPure (toScope env) ab \_ b e -> do
      let env' = extendOutMap env $ toEnvFrag b
      unsafeRunInplaceT (cont b e) env'

-- TODO: unify this with `HasNames` by parameterizing by the thing you bind,
-- like we do with `SubstE Name`, `SubstE AtomSubstVal`, etc?
class BindsNames b => BindsEnv (b::B) where
  toEnvFrag :: Distinct l => b n l -> EnvFrag n l

  default toEnvFrag :: (GenericB b, BindsEnv (RepB b))
                        => Distinct l => b n l -> EnvFrag n l
  toEnvFrag b = toEnvFrag $ fromB b

-- We're really just defining this so we can have a polymorphic `binderType`.
-- But maybe we don't need one. Or maybe we can make one using just
-- `BindsOneName b AtomNameC` and `BindsEnv b`.
class BindsOneName b AtomNameC => BindsOneAtomName (b::B) where
  boundAtomBinding :: b n l -> AtomBinding n

binderType :: BindsOneAtomName b => b n l -> Type n
binderType b =  atomBindingType $ toBinding $ boundAtomBinding b

bindersTypes :: (Distinct l, ProvesExt b, BindsNames b, BindsOneAtomName b)
             => Nest b n l -> [Type l]
bindersTypes Empty = []
bindersTypes (Nest b bs) = ty : bindersTypes bs
  where ty = withExtEvidence b $ withSubscopeDistinct bs $ sink (binderType b)

instance (Color c, SinkableE ann, ToBinding ann c) => BindsEnv (BinderP c ann) where
  toEnvFrag (b:>ann) = EnvFrag (RecSubstFrag (b @> toBinding ann')) Nothing
    where ann' = withExtEvidence b $ sink ann

class (SubstE Name e, SinkableE e) => ToBinding (e::E) (c::C) | e -> c where
  toBinding :: e n -> Binding c n

instance Color c => ToBinding (Binding c) c where
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

lookupEnv :: (Color c, EnvReader m) => Name c o -> m o (Binding c o)
lookupEnv v = withEnv $ flip lookupEnvPure v

lookupAtomName :: EnvReader m => AtomName n -> m n (AtomBinding n)
lookupAtomName name = lookupEnv name >>= \case AtomNameBinding x -> return x

lookupImpFun :: EnvReader m => ImpFunName n -> m n (ImpFunction n)
lookupImpFun name = lookupEnv name >>= \case ImpFunBinding f -> return f

lookupModule :: EnvReader m => ModuleName n -> m n (Module n)
lookupModule name = do
  ~(ModuleBinding m) <- lookupEnv name
  return m

lookupDataDef :: EnvReader m => DataDefName n -> m n (DataDef n)
lookupDataDef name = lookupEnv name >>= \case DataDefBinding x -> return x

lookupSourceMapPure :: SourceMap n -> SourceName -> [SourceNameDef n]
lookupSourceMapPure (SourceMap m) v = M.findWithDefault [] v m

lookupSourceMap :: EnvReader m => SourceName -> m n (Maybe (UVar n))
lookupSourceMap sourceName = do
  sm <- withEnv $ envSourceMap . moduleEnv
  case lookupSourceMapPure sm sourceName of
    LocalVar x:_  -> return $ Just x
    [ModuleVar _ (Just x)] -> return $ Just x
    _   -> return Nothing

lookupEnvPure :: Color c => Env n -> Name c n -> Binding c n
lookupEnvPure env v = lookupTerminalSubstFrag (fromRecSubst $ envDefs $ topEnv env) v

updateEnv :: Color c => Name c n -> Binding c n -> Env n -> Env n
updateEnv v rhs env =
  env { topEnv = (topEnv env) { envDefs = RecSubst $ updateSubstFrag v rhs bs } }
  where (RecSubst bs) = envDefs $ topEnv env

refreshBinders
  :: (EnvExtender m, BindsEnv b, SubstB Name b)
  => b n l
  -> (forall l'. DExt n l' => b n l' -> SubstFrag Name n l l' -> m l' a)
  -> m n a
refreshBinders b cont = refreshAbs (Abs b $ idSubstFrag b) cont

substBinders
  :: ( SinkableV v, SubstV v v, EnvExtender2 m, FromName v
     , SubstReader v m, SubstB v b, SubstV Name v, SubstB Name b, BindsEnv b)
  => b i i'
  -> (forall o'. DExt o o' => b o o' -> m i' o' a)
  -> m i o a
substBinders b cont = do
  ab <- substM $ Abs b $ idSubstFrag b
  refreshAbs ab \b' subst ->
    extendSubst subst $ cont b'

withFreshBinder
  :: (Color c, EnvExtender m, ToBinding binding c)
  => NameHint -> binding n
  -> (forall l. DExt n l => NameBinder c n l -> m l a)
  -> m n a
withFreshBinder hint binding cont = do
  Abs b v <- newNameM hint
  refreshAbs (Abs (b:>binding) v) \(b':>_) _ -> cont b'

withFreshBinders
  :: (Color c, EnvExtender m, ToBinding binding c)
  => [binding n]
  -> (forall l. DExt n l => Nest (BinderP c binding) n l -> [Name c l] -> m l a)
  -> m n a
withFreshBinders [] cont = do
  Distinct <- getDistinct
  cont Empty []
withFreshBinders (binding:rest) cont = do
  withFreshBinder NoHint binding \b -> do
    ListE rest' <- sinkM $ ListE rest
    withFreshBinders rest' \bs vs ->
      cont (Nest (b :> binding) bs)
           (sink (binderName b) : vs)

withFreshLamBinder
  :: (EnvExtender m)
  => NameHint -> LamBinding n
  -> Abs Binder EffectRow n
  -> (forall l. DExt n l => LamBinder n l -> m l a)
  -> m n a
withFreshLamBinder hint binding@(LamBinding arr ty) effAbs cont = do
  withFreshBinder hint binding \b -> do
    effs <- applyAbs (sink effAbs) (binderName b)
    withAllowedEffects effs do
      cont $ LamBinder b ty arr effs

withFreshPureLamBinder
  :: (EnvExtender m)
  => NameHint -> LamBinding n
  -> (forall l. DExt n l => LamBinder n l -> m l a)
  -> m n a
withFreshPureLamBinder hint binding@(LamBinding arr ty) cont = do
  withFreshBinder hint binding \b -> do
    withAllowedEffects Pure do
      cont $ LamBinder b ty arr Pure

withFreshPiBinder
  :: EnvExtender m
  => NameHint -> PiBinding n
  -> (forall l. DExt n l => PiBinder n l -> m l a)
  -> m n a
withFreshPiBinder hint binding@(PiBinding arr ty) cont = do
  withFreshBinder hint binding \b ->
    withAllowedEffects Pure $
      cont $ PiBinder b ty arr

piBinderToLamBinder :: PiBinder n l -> EffectRow l -> LamBinder n l
piBinderToLamBinder (PiBinder b ty arr) eff = LamBinder b ty arr eff

data SomeDecl (binding::V) (n::S) (l::S) where
  SomeDecl :: Color c => NameBinder c n l -> binding c n -> SomeDecl binding n l

instance ProvesExt (SomeDecl binding) where
  toExtEvidence (SomeDecl b _) = toExtEvidence b

instance (SinkableV v, SubstV v binding)
         => SubstB v (SomeDecl binding) where
  substB env (SomeDecl b binding) cont = do
    let binding' = substE env binding
    substB env b \env' b' -> cont env' $ SomeDecl b' binding'

instance HoistableV binding => HoistableB (SomeDecl binding) where
  freeVarsB (SomeDecl _ binding) = freeVarsE binding

instance SinkableV binding => SinkableB (SomeDecl binding) where
  sinkingProofB _ _ _ = undefined

instance BindsNames (SomeDecl binding) where
  toScopeFrag (SomeDecl b _) = toScopeFrag b

instance (forall c. Color c => ToBinding (binding c) c)
         => BindsEnv (SomeDecl binding) where
  toEnvFrag (SomeDecl b binding) =
    withExtEvidence b $
      EnvFrag (RecSubstFrag $ b @> sink (toBinding binding)) Nothing

-- === Env reader on the input side ===

class Monad2 m => EnvReaderI (m::MonadKind2) where
   getEnvI :: m i o (Env i)
   getDistinctI :: m i o (DistinctEvidence i)
   withEnvI :: Distinct i' => Env i' -> m i' o a -> m i o a

newtype EnvReaderIT (m::MonadKind1) (i::S) (o::S) (a:: *) =
  EnvReaderIT { runEnvReaderIT' :: ReaderT (DistinctEvidence i, Env i) (m o) a }
  deriving (Functor, Applicative, Monad, MonadFail, Catchable, Fallible, CtxReader,
            Alternative)

runEnvReaderIT :: Distinct i => Env i -> EnvReaderIT m i o a -> m o a
runEnvReaderIT env m = runReaderT (runEnvReaderIT' m) (Distinct, env)

instance Monad1 m => EnvReaderI (EnvReaderIT m) where
  getEnvI = EnvReaderIT $ asks snd
  getDistinctI = EnvReaderIT $ asks fst
  withEnvI env cont = EnvReaderIT $ withReaderT (const (Distinct, env)) $
    runEnvReaderIT' cont

-- run a monadic EnvReaderM function over the in-space env
liftEnvReaderI :: EnvReaderI m => EnvReaderM i a -> m i o a
liftEnvReaderI cont = do
  env <- getEnvI
  Distinct <- getDistinctI
  return $ runEnvReaderM env cont

extendI :: (BindsEnv b, EnvReaderI m, Distinct i')
        => b i i' -> m i' o a -> m i o a
extendI b cont = do
  env <- getEnvI
  Distinct <- getDistinctI
  withEnvI (extendOutMap env $ toEnvFrag b) cont

refreshAbsI :: (EnvReaderI m, BindsEnv b, SubstB Name b, SubstE Name e)
            => Abs b e i
            -> (forall i'. DExt i i' => b i i' -> e i' -> m i' o a)
            -> m i o a
refreshAbsI ab cont = do
  env <- getEnvI
  Distinct <- getDistinctI
  refreshAbsPure (toScope env) ab \_ b e ->
    extendI b $ cont b e

refreshLamI :: EnvReaderI m
            => LamExpr i
            -> (forall i'. DExt i i' => LamBinder i i' -> Block i' -> m i' o a)
            -> m i o a
refreshLamI _ _ = undefined

instance EnvReader m => EnvReader (EnvReaderIT m i) where
  unsafeGetEnv = EnvReaderIT $ lift unsafeGetEnv

instance (ScopeReader m, EnvExtender m)
         => EnvExtender (EnvReaderIT m i) where
  refreshAbs ab cont = EnvReaderIT $ ReaderT \env ->
    refreshAbs ab \b e -> do
      let EnvReaderIT (ReaderT cont') = cont b e
      cont' env

instance ScopeReader m => ScopeReader (EnvReaderIT m i) where
  unsafeGetScope = EnvReaderIT $ lift unsafeGetScope
  getDistinct = EnvReaderIT $ lift getDistinct

instance (ScopeReader m, ScopeExtender m)
         => ScopeExtender (EnvReaderIT m i) where
  refreshAbsScope ab cont = EnvReaderIT $ ReaderT \env ->
    refreshAbsScope ab \b e -> do
      let EnvReaderIT (ReaderT cont') = cont b e
      cont' env

deriving instance MonadIO1 m => MonadIO (EnvReaderIT m i o)
deriving instance (Monad1 m, MonadState (s o) (m o))
                  => MonadState (s o) (EnvReaderIT m i o)

-- === reconstruction abstractions ===

captureClosure
  :: (HoistableB b, HoistableE e, Color c)
  => b n l -> e l -> ([Name c l], NaryAbs c e n)
captureClosure decls result = do
  let vs = capturedVars decls result
  let ab = abstractFreeVarsNoAnn vs result
  case hoist decls ab of
    HoistSuccess abHoisted -> (vs, abHoisted)
    HoistFailure _ ->
      error "shouldn't happen"  -- but it will if we have types that reference
                                -- local vars. We really need a telescope.

capturedVars :: (Color c, BindsNames b, HoistableE e)
             => b n l -> e l -> [Name c l]
capturedVars b e = nameSetToList nameSet
  where nameSet = M.intersection (toNameSet (toScopeFrag b)) (freeVarsE e)

abstractPtrLiterals
  :: (EnvReader m, HoistableE e)
  => e n -> m n (Abs (Nest IBinder) e n, [LitVal])
abstractPtrLiterals block = do
  let fvs = freeAtomVarsList block
  (ptrNames, ptrVals) <- unzip <$> catMaybes <$> forM fvs \v ->
    lookupAtomName v >>= \case
      PtrLitBound _ name -> lookupEnv name >>= \case
        PtrBinding (PtrLitVal ty ptr) ->
          return $ Just ((v, LiftE (PtrType ty)), PtrLit $ PtrLitVal ty ptr)
        PtrBinding (PtrSnapshot _ _) -> error "this case is only for serialization"
      _ -> return Nothing
  Abs nameBinders block' <- return $ abstractFreeVars ptrNames block
  let ptrBinders = fmapNest (\(b:>LiftE ty) -> IBinder b ty) nameBinders
  return (Abs ptrBinders block', ptrVals)

freeAtomVarsList :: HoistableE e => e n -> [AtomName n]
freeAtomVarsList = freeVarsList

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
  unsafeGetScope = FallibleT1 $ lift $ lift unsafeGetScope
  getDistinct = FallibleT1 $ lift $ lift $ getDistinct

instance EnvReader m => EnvReader (FallibleT1 m) where
  unsafeGetEnv = FallibleT1 $ lift $ lift unsafeGetEnv

-- === Querying static env ===

getLambdaDicts :: EnvReader m => m n [Atom n]
getLambdaDicts = do
  env <- withEnv moduleEnv
  return $ lambdaDicts $ envSynthCandidates env

getSuperclassProjs :: EnvReader m => m n [Atom n]
getSuperclassProjs = do
  env <- withEnv moduleEnv
  return $ superclassGetters $ envSynthCandidates env

getInstanceDicts :: EnvReader m => DataDefName n -> m n [Atom n]
getInstanceDicts name = do
  env <- withEnv moduleEnv
  return $ M.findWithDefault [] name $ instanceDicts $ envSynthCandidates env

getAllowedEffects :: EnvReader m => m n (EffectRow n)
getAllowedEffects = withEnv $ allowedEffects . moduleEnv

-- === Extending effects ===

data EffectBinder n l where
  EffectBinder :: EffectRow n -> EffectBinder n n

withAllowedEffects :: EnvExtender m => EffectRow n -> m n a -> m n a
withAllowedEffects effs cont =
  refreshAbs (Abs (EffectBinder effs) UnitE) \(EffectBinder _) UnitE ->
    cont

instance GenericB EffectBinder where
  type RepB EffectBinder = LiftB EffectRow
  fromB (EffectBinder effs) = LiftB effs
  toB   (LiftB effs) = EffectBinder effs

instance BindsEnv EffectBinder where
  toEnvFrag (EffectBinder effs) = EnvFrag emptyOutFrag $ Just effs

instance SinkableB EffectBinder
instance HoistableB EffectBinder
instance ProvesExt  EffectBinder
instance BindsNames EffectBinder
instance SubstB Name EffectBinder

-- === front-end language AST ===

data SourceNameOr (a::E) (n::S) where
  -- Only appears before renaming pass
  SourceName :: SourceName -> SourceNameOr a VoidS
  -- Only appears after renaming pass
  -- We maintain the source name for user-facing error messages.
  InternalName :: SourceName -> a n -> SourceNameOr a n
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
  -- We maintain the source name for user-facing error messages.
  UBind :: SourceName -> NameBinder c n l -> UBinder c n l

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
 | ULabel String
 | URecord (UFieldRowElems n)                        -- {@v=x, a=y, b=z, ...rest}
 | UVariant (LabeledItems ()) Label (UExpr n)        -- {|a|b| a=x |}
 | UVariantLift (LabeledItems ()) (UExpr n)          -- {|a|b| ...rest |}
 | ULabeledRow (UFieldRowElems n)                    -- {@v:X ? a:Y ? b:Z ? ...rest}
 | URecordTy (UFieldRowElems n)                      -- {@v:X & a:Y & b:Z & ...rest}
 | UVariantTy (ExtLabeledItems (UExpr n) (UExpr n))  -- {a:X | b:Y | ...rest}
 | UIntLit  Int
 | UFloatLit Double
  deriving (Show, Generic)

type UFieldRowElems (n::S) = [UFieldRowElem n]
data UFieldRowElem (n::S)
  = UStaticField String                (UExpr n)
  | UDynField    (SourceNameOr UVar n) (UExpr n)
  | UDynFields   (UExpr n)
  deriving (Show)

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
    :: (SourceName, Nest (UAnnBinder AtomNameC) n l')    -- param binders
    -> Nest (UAnnBinder AtomNameC) l' l  -- typeclass binders
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

data UFieldRowPat (n::S) (l::S) where
  UEmptyRowPat    :: UFieldRowPat n n
  URemFieldsPat   :: UBinder AtomNameC n l -> UFieldRowPat n l
  UStaticFieldPat :: Label               -> UPat n l' -> UFieldRowPat l' l -> UFieldRowPat n l
  UDynFieldsPat   :: SourceNameOr UVar n -> UPat n l' -> UFieldRowPat l' l -> UFieldRowPat n l
  UDynFieldPat    :: SourceNameOr UVar n -> UPat n l' -> UFieldRowPat l' l -> UFieldRowPat n l

instance Show (UFieldRowPat n l) where
  show _ = "UFieldRowPat <TODO>"

type UPat = WithSrcB UPat'
data UPat' (n::S) (l::S) =
   UPatBinder (UBinder AtomNameC n l)
 | UPatCon (SourceNameOr (Name DataConNameC) n) (Nest UPat n l)
 | UPatPair (PairB UPat UPat n l)
 | UPatUnit (UnitB n l)
 -- The name+ExtLabeledItems and the PairBs are parallel, constrained by the parser.
 | UPatRecord (UFieldRowPat n l)
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

-- === top-level blocks ===

type SourceName = String

data SourceBlock = SourceBlock
  { sbLine     :: Int
  , sbOffset   :: Int
  , sbLogLevel :: LogLevel
  , sbText     :: String
  , sbContents :: SourceBlock' }
  deriving (Show, Generic)

type ReachedEOF = Bool

data SourceBlock' =
   EvalUDecl (UDecl VoidS VoidS)
 | Command CmdName (UExpr VoidS)
 | DeclareForeign SourceName (UAnnBinder AtomNameC VoidS VoidS)
 | GetNameType SourceName
 | ImportModule ModuleSourceName
 | QueryEnv EnvQuery
 | ProseBlock String
 | CommentLine
 | EmptyLines
 | UnParseable ReachedEOF String
  deriving (Show, Generic)

data CmdName = GetType | EvalExpr OutFormat | ExportFun String
               deriving  (Show, Generic)

data LogLevel = LogNothing | PrintEvalTime | PrintBench String
              | LogPasses [PassName] | LogAll
                deriving  (Show, Generic)

data EnvQuery =
   DumpSubst
 | InternalNameInfo RawName
 | SourceNameInfo   SourceName
   deriving (Show, Generic)

data SourceNameDef n =
    LocalVar  (UVar n)                          -- bound within a decl or expression
    -- the Nothing case is for vars whose definitions have errors
  | ModuleVar ModuleSourceName (Maybe (UVar n)) -- bound at the module level
    deriving (Show, Generic)

data SourceMap (n::S) = SourceMap
  {fromSourceMap :: M.Map SourceName [SourceNameDef n]}
  deriving Show

data IRVariant = Surface | Typed | Core | Simp | Evaluated
                 deriving (Show, Eq, Ord, Generic)

data TopEnvFrag n l = TopEnvFrag (EnvFrag n l) (PartialTopEnvFrag l)

-- This is really the type of updates to `Env`. We should probably change the
-- names to reflect that.
data PartialTopEnvFrag n = PartialTopEnvFrag
  { fragCache           :: Cache n
  , fragLoadedModules   :: LoadedModules n
  , fragLocalModuleEnv  :: ModuleEnv n }

-- TODO: we could add a lot more structure for querying by dict type, caching, etc.
-- TODO: make these `Name n` instead of `Atom n` so they're usable as cache keys.
data SynthCandidates n = SynthCandidates
  { lambdaDicts       :: [Atom n]
  , superclassGetters :: [Atom n]
  , instanceDicts     :: M.Map (DataDefName n) [Atom n] }
  deriving (Show, Generic)

-- === primitive constructors and operators ===

data PrimExpr e =
        TCExpr  (PrimTC  e)
      | ConExpr (PrimCon e)
      | OpExpr  (PrimOp  e)
      | HofExpr (PrimHof e)
        deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

data PrimTC e =
        BaseType BaseType
      | ProdType [e]
      | SumType [e]
      | IntRange e e
      | IndexRange e (Limit e) (Limit e)
      | IndexSlice e e      -- Sliced index set, slice length. Note that this is no longer an index set!
      | RefType (Maybe e) e
      | TypeKind
      | EffectRowKind
      | LabeledRowKindTC
      | ParIndexRange e e e  -- Full index set, global thread id, thread count
      | LabelType
        deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

data PrimCon e =
        Lit LitVal
      | ProdCon [e]
      | SumCon e Int e  -- type, tag, payload
      | ClassDictHole SrcPosCtx e  -- Only used during type inference
      | SumAsProd e e [[e]] -- type, tag, payload (only used during Imp lowering)
      -- These are just newtype wrappers. TODO: use ADTs instead
      | IntRangeVal   e e e
      | IndexRangeVal e (Limit e) (Limit e) e
      | IndexSliceVal e e e    -- Sliced index set, slice length, ordinal index
      | BaseTypeRef e
      | TabRef e
      | ConRef (PrimCon e)
      | RecordRef (LabeledItems e)
      | ParIndexCon e e        -- Type, value
      | LabelCon String
        deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

data PrimOp e =
        TabCon e [e]                 -- table type elements
      | ScalarBinOp BinOp e e
      | ScalarUnOp UnOp e
      | Select e e e                 -- predicate, val-if-true, val-if-false
      | PrimEffect e (PrimEffect e)
      | IndexRef e e
      | ProjRef Int e
      | Inject e
      | SliceOffset e e              -- Index slice first, inner index second
      | SliceCurry  e e              -- Index slice first, curried index second
      -- Low-level memory operations
      | IOAlloc BaseType e
      | IOFree e
      | PtrOffset e e
      | PtrLoad e
      | PtrStore e e
      -- SIMD operations
      | VectorBinOp BinOp e e
      | VectorPack [e]               -- List should have exactly vectorWidth elements
      | VectorIndex e e              -- Vector first, index second
      -- Idx (survives simplification, because we allow it to be backend-dependent)
      | UnsafeFromOrdinal e e   -- index set, ordinal index. XXX: doesn't check bounds
      | ToOrdinal e
      | IdxSetSize e
      | ThrowError e                 -- Hard error (parameterized by result type)
      | ThrowException e             -- Catchable exceptions (unlike `ThrowError`)
      | CastOp e e                   -- Type, then value. See Type.hs for valid coercions.
      -- Extensible record and variant operations:
      -- Concatenate two records.
      | RecordCons   e e
      -- Split off a labeled row from the front of the record.
      | RecordSplit  e e
      -- Add a dynamically named field to a record (on the left).
      -- Args are as follows: label, value, record.
      | RecordConsDynamic e e e
      -- Splits a label from the record.
      | RecordSplitDynamic e e
      -- Extend a variant with empty alternatives (on the left).
      -- Left arg contains the types of the empty alternatives to add.
      | VariantLift  (LabeledItems e) e
      -- Split {a:A | b:B | ...rest} into (effectively) {a:A | b:B} | {|...rest}.
      -- Left arg contains the types of the fields to extract (e.g. a:A, b:B).
      -- (see https://github.com/google-research/dex-lang/pull/201#discussion_r471591972)
      | VariantSplit (LabeledItems e) e
      -- Ask which constructor was used, as its Word8 index
      | DataConTag e
      -- Create an enum (payload-free ADT) from a Word8
      | ToEnum e e
      -- Converts sum types returned by primitives to variant-types that
      -- can be scrutinized in the surface language.
      | SumToVariant e
      -- Pointer to the stdout-like output stream
      | OutputStreamPtr
      | SynthesizeDict SrcPosCtx e  -- Only used during type inference
        deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

data PrimHof e =
        For ForAnn e
      | Tile Int e e          -- dimension number, tiled body, scalar body
      | While e
      | RunReader e e
      | RunWriter (BaseMonoidP e) e
      | RunState  e e
      | RunIO e
      | CatchException e
      | Linearize e
      | Transpose e
      | PTileReduce [BaseMonoidP e] e e  -- accumulator monoids, index set, thread body
        deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

data BaseMonoidP e = BaseMonoid { baseEmpty :: e, baseCombine :: e }
                     deriving (Show, Eq, Generic, Functor, Foldable, Traversable)
type BaseMonoid n = BaseMonoidP (Atom n)

data PrimEffect e = MAsk | MExtend (BaseMonoidP e) e | MGet | MPut e
    deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

data BinOp = IAdd | ISub | IMul | IDiv | ICmp CmpOp
           | FAdd | FSub | FMul | FDiv | FCmp CmpOp | FPow
           | BAnd | BOr | BShL | BShR | IRem | BXor
             deriving (Show, Eq, Generic)

data UnOp = Exp | Exp2
          | Log | Log2 | Log10 | Log1p
          | Sin | Cos | Tan | Sqrt
          | Floor | Ceil | Round
          | LGamma
          | FNeg | BNot
            deriving (Show, Eq, Generic)

data CmpOp = Less | Greater | Equal | LessEqual | GreaterEqual
             deriving (Show, Eq, Generic)

data Direction = Fwd | Rev  deriving (Show, Eq, Generic)
data ForAnn = RegularFor Direction | ParallelFor
                deriving (Show, Eq, Generic)

data Limit a = InclusiveLim a
             | ExclusiveLim a
             | Unlimited
               deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

type PrimName = PrimExpr ()

strToPrimName :: String -> Maybe PrimName
strToPrimName s = M.lookup s builtinNames

primNameToStr :: PrimName -> String
primNameToStr prim = case lookup prim $ map swap $ M.toList builtinNames of
  Just s  -> s
  Nothing -> show prim

showPrimName :: PrimExpr e -> String
showPrimName prim = primNameToStr $ fmap (const ()) prim

-- === effects ===

data RWS = Reader | Writer | State  deriving (Show, Eq, Ord, Generic)

data EffectP (name::E) (n::S) =
  RWSEffect RWS (Maybe (name n)) | ExceptionEffect | IOEffect
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

instance OrdE name => Semigroup (EffectRowP name n) where
  EffectRow effs t <> EffectRow effs' t' =
    EffectRow (S.union effs effs') newTail
    where
      newTail = case (t, t') of
        (Nothing, effTail) -> effTail
        (effTail, Nothing) -> effTail
        _ | t == t' -> t
          | otherwise -> error "Can't combine effect rows with mismatched tails"

instance OrdE name => Monoid (EffectRowP name n) where
  mempty = EffectRow mempty Nothing

-- === imperative IR ===

type ImpFunName = Name ImpFunNameC
data IExpr n = ILit LitVal
             -- We use AtomName because we convert between atoms and imp
             -- expressions without chaning names. Maybe we shouldn't do that.
             | IVar (AtomName n) BaseType
               deriving (Show, Generic)

data IBinder n l = IBinder (NameBinder AtomNameC n l) IType
                   deriving (Show, Generic)

type IPrimOp n = PrimOp (IExpr n)
type IVal = IExpr  -- only ILit and IRef constructors
type IType = BaseType
type Size = IExpr

type IFunVar = (SourceName, IFunType)
data IFunType = IFunType CallingConvention [IType] [IType] -- args, results
                deriving (Show, Eq, Generic)

data IsCUDARequired = CUDARequired | CUDANotRequired  deriving (Eq, Show, Generic)

instance IsBool IsCUDARequired where
  toBool CUDARequired = True
  toBool CUDANotRequired = False

data CallingConvention =
   CEntryFun
 | CInternalFun
 | EntryFun IsCUDARequired
 | FFIFun
 | FFIMultiResultFun
 | CUDAKernelLaunch
 | MCThreadLaunch
   deriving (Show, Eq, Generic)

data ImpFunction n =
   ImpFunction IFunType (Abs (Nest IBinder) ImpBlock n)
 | FFIFunction IFunType SourceName
   deriving (Show, Generic)

data ImpBlock n where
  ImpBlock :: Nest ImpDecl n l -> [IExpr l] -> ImpBlock n
deriving instance Show (ImpBlock n)

data ImpDecl n l = ImpLet (Nest IBinder n l) (ImpInstr n)
     deriving (Show, Generic)

data ImpInstr n =
   IFor Direction (Size n) (Abs IBinder ImpBlock n)
 | IWhile (ImpBlock n)
 | ICond (IExpr n) (ImpBlock n) (ImpBlock n)
 | IQueryParallelism IFunVar (IExpr n) -- returns the number of available concurrent threads
 | ISyncWorkgroup
 | ILaunch IFunVar (Size n) [IExpr n]
 | ICall (ImpFunName n) [IExpr n]
 | Store (IExpr n) (IExpr n)           -- dest, val
 | Alloc AddressSpace IType (Size n)
 | MemCopy (IExpr n) (IExpr n) (IExpr n)   -- dest, source, numel
 | Free (IExpr n)
 | IThrowError  -- TODO: parameterize by a run-time string
 | ICastOp IType (IExpr n)
 | IPrimOp (IPrimOp n)
   deriving (Show, Generic)

iBinderType :: IBinder n l -> IType
iBinderType (IBinder _ ty) = ty

data Backend = LLVM | LLVMCUDA | LLVMMC | MLIR | Interpreter  deriving (Show, Eq)
newtype CUDAKernel = CUDAKernel B.ByteString deriving (Show)

-- === object file representations ===

-- TODO: think about the naming discipline for compiled function names. We can't
-- use our standard naming systems because these need to interact with the
-- outside world, LLVM etc.

type CFunName = String
data CFun n = CFun CFunName (ObjectFileName n)
              deriving (Show, Generic)

type ObjectFileName = Name ObjectFileNameC

data ObjectFile n = ObjectFile
  { objectFileContents :: BS.ByteString
  , objectFileFunsDefined :: [CFunName]
  -- XXX: direct dependencies only
  , objectFileDeps :: [ObjectFileName n] }
  deriving (Show, Generic)

newtype ObjectFiles n = ObjectFiles (S.Set (ObjectFileName n))
        deriving (Show, Generic, Semigroup, Monoid)

-- === base types ===

-- TODO: we could consider using some mmap-able instead of ByteString
data PtrSnapshot = ByteArray BS.ByteString
                 | PtrArray [PtrSnapshot]
                 | NullPtr
                   deriving (Show, Eq, Ord, Generic)

data PtrLitVal = PtrLitVal   PtrType (Ptr ())
               | PtrSnapshot PtrType PtrSnapshot
                 deriving (Show, Eq, Ord, Generic)

instance Store PtrSnapshot where
instance Store PtrLitVal where
  size = SI.VarSize \case
    PtrSnapshot t p -> SI.getSize (t, p)
    PtrLitVal _ _ -> error "can't serialize pointer literals"
  peek = do
    (t, p) <- peek
    return $ PtrSnapshot t p
  poke (PtrSnapshot t p) = poke (t, p)
  poke (PtrLitVal _ _) = error "can't serialize pointer literals"

data LitVal = Int64Lit   Int64
            | Int32Lit   Int32
            | Word8Lit   Word8
            | Word32Lit  Word32
            | Word64Lit  Word64
            | Float64Lit Double
            | Float32Lit Float
              -- XXX: we have to be careful with this, because it can't be
              -- serialized we only use it in a few places, like the interpreter
              -- and for passing values to LLVM's JIT. Otherwise, pointers
              -- should be referred to by name.
            | PtrLit PtrLitVal
            | VecLit [LitVal]  -- Only one level of nesting allowed!
              deriving (Show, Eq, Ord, Generic)

data ScalarBaseType = Int64Type | Int32Type
                    | Word8Type | Word32Type | Word64Type
                    | Float64Type | Float32Type
                      deriving (Show, Eq, Ord, Generic)
data BaseType = Scalar  ScalarBaseType
              | Vector  ScalarBaseType
              | PtrType PtrType
                deriving (Show, Eq, Ord, Generic)

data Device = CPU | GPU  deriving (Show, Eq, Ord, Generic)
data AddressSpace = Stack | Heap Device     deriving (Show, Eq, Ord, Generic)
type PtrType = (AddressSpace, BaseType)

sizeOf :: BaseType -> Int
sizeOf t = case t of
  Scalar Int64Type   -> 8
  Scalar Int32Type   -> 4
  Scalar Word8Type   -> 1
  Scalar Word32Type  -> 4
  Scalar Word64Type  -> 8
  Scalar Float64Type -> 8
  Scalar Float32Type -> 4
  PtrType _          -> ptrSize
  Vector st          -> vectorWidth * sizeOf (Scalar st)

ptrSize :: Int
ptrSize = 8

vectorWidth :: Int
vectorWidth = 4

-- === passes ===

data PassName = Parse | RenamePass | TypePass | SynthPass | SimpPass | ImpPass | JitPass
              | LLVMOpt | AsmPass | JAXPass | JAXSimpPass | LLVMEval
              | ResultPass | JaxprAndHLO | OptimPass
                deriving (Ord, Eq, Bounded, Enum, Generic)

instance Show PassName where
  show p = case p of
    Parse    -> "parse" ; RenamePass -> "rename";
    TypePass -> "typed"   ; SynthPass -> "synth"
    SimpPass -> "simp"  ; ImpPass  -> "imp"     ; JitPass   -> "llvm"
    LLVMOpt  -> "llvmopt" ; AsmPass   -> "asm"
    JAXPass  -> "jax"   ; JAXSimpPass -> "jsimp"; ResultPass -> "result"
    LLVMEval -> "llvmeval" ; JaxprAndHLO -> "jaxprhlo"; OptimPass -> "optimized"

-- === outputs ===

type LitProg = [(SourceBlock, Result)]

data Result = Result
                { resultOutputs :: [Output]
                , resultErrs    :: Except () }
              deriving (Show, Eq)

type BenchStats = (Int, Double) -- number of runs, total benchmarking time
data Output = TextOut String
            | HtmlOut String
            | PassInfo PassName String
            | EvalTime  Double (Maybe BenchStats)
            | TotalTime Double
            | BenchResult String Double Double (Maybe BenchStats) -- name, compile time, eval time
            | MiscLog String
            -- | ExportedFun String Atom
              deriving (Show, Eq, Generic)

data OutFormat = Printed | RenderHtml  deriving (Show, Eq, Generic)

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
  PtrLitBound ty _ -> BaseTy (PtrType ty)
  SimpLamBound ty _ -> naryPiTypeAsType ty
  FFIFunBound  ty _ -> naryPiTypeAsType ty

infixr 1 -->
infixr 1 --@
infixr 2 ==>

piArgType :: PiType n -> Type n
piArgType (PiType (PiBinder _ ty _) _ _) = ty

lamArgType :: LamExpr n -> Type n
lamArgType (LamExpr (LamBinder _ ty _ _) _) = ty

piArrow :: PiType n -> Arrow
piArrow (PiType (PiBinder _ _ arr) _ _) = arr

nonDepPiType :: ScopeReader m
             => Arrow -> Type n -> EffectRow n -> Type n -> m n (PiType n)
nonDepPiType arr argTy eff resultTy =
  toConstAbs (PairE eff resultTy) >>= \case
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

nonDepDataConTys :: DataConDef n -> Maybe [Type n]
nonDepDataConTys (DataConDef _ (Abs binders UnitE)) = go binders
  where
    go :: Nest Binder n l -> Maybe [Type n]
    go Empty = return []
    go (Nest (b:>ty) bs) = do
      tys <- go bs
      case hoist b (ListE tys) of
        HoistFailure _ -> Nothing
        HoistSuccess (ListE tys') -> return $ ty:tys'

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

pattern IIdxRepVal :: Int32 -> IExpr n
pattern IIdxRepVal x = ILit (Int32Lit x)

pattern IIdxRepTy :: IType
pattern IIdxRepTy = Scalar Int32Type

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

pattern TabTy :: PiBinder n l -> Type l -> Type n
pattern TabTy b body <- Pi (PiType (b@(PiBinder _ _ TabArrow)) Pure body)
  where TabTy b body = Pi (PiType b Pure body)

pattern TabVal :: LamBinder n l -> Block l -> Atom n
pattern TabVal b body <- Lam (LamExpr b@(LamBinder _ _ TabArrow _) body)

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

pattern AtomicBlock :: Atom n -> Block n
pattern AtomicBlock atom <- Block _ Empty (Atom atom)
  where AtomicBlock atom = Block NoBlockAnn Empty (Atom atom)

pattern BinaryLamExpr :: LamBinder n l1 -> LamBinder l1 l2 -> Block l2 -> LamExpr n
pattern BinaryLamExpr b1 b2 body = LamExpr b1 (AtomicBlock (Lam (LamExpr b2 body)))

-- first argument is the number of args expected
fromNaryLam :: Int -> Atom n -> Maybe (NaryLamExpr n)
fromNaryLam n _ | n <= 0 = error "expected positive number of args"
fromNaryLam 1 lam = case lam of
  Lam (LamExpr (LamBinder b ty _ effs) body) ->
    Just $ NaryLamExpr (NonEmptyNest (b:>ty) Empty) effs body
  _ -> Nothing
fromNaryLam n (Lam (LamExpr (LamBinder b1 ty _ Pure) (AtomicBlock lam))) = do
  NaryLamExpr (NonEmptyNest b2 bs) effs body <- fromNaryLam (n-1) lam
  return $ NaryLamExpr (NonEmptyNest (b1:>ty) (Nest b2 bs)) effs body
fromNaryLam _ _ = Nothing

-- first argument is the number of args expected
fromNaryPiType :: Int -> Type n -> Maybe (NaryPiType n)
fromNaryPiType n _ | n <= 0 = error "expected positive number of args"
fromNaryPiType 1 ty = case ty of
  Pi (PiType b effs resultTy) -> Just $ NaryPiType (NonEmptyNest b Empty) effs resultTy
  _ -> Nothing
fromNaryPiType n (Pi (PiType b1 Pure piTy)) = do
  NaryPiType (NonEmptyNest b2 bs) effs resultTy <- fromNaryPiType (n-1) piTy
  Just $ NaryPiType (NonEmptyNest b1 (Nest b2 bs)) effs resultTy
fromNaryPiType _ _ = Nothing

naryPiTypeAsType :: NaryPiType n -> Type n
naryPiTypeAsType (NaryPiType (NonEmptyNest b bs) effs resultTy) = case bs of
  Empty -> Pi $ PiType b effs resultTy
  Nest b' rest -> Pi $ PiType b Pure restTy
    where restTy = naryPiTypeAsType $ NaryPiType (NonEmptyNest b' rest) effs resultTy

naryLamExprAsAtom :: NaryLamExpr n -> Atom n
naryLamExprAsAtom (NaryLamExpr (NonEmptyNest (b:>ty) bs) effs body) = case bs of
  Empty -> Lam $ LamExpr (LamBinder b ty PlainArrow effs) body
  Nest b' rest -> Lam $ LamExpr (LamBinder b ty PlainArrow Pure) (AtomicBlock restBody)
    where restBody = naryLamExprAsAtom $ NaryLamExpr (NonEmptyNest b' rest) effs body

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

getProjection :: HasCallStack => [Int] -> Atom n -> Atom n
getProjection [] a = a
getProjection (i:is) a = case getProjection is a of
  Var name -> ProjectElt (NE.fromList [i]) name
  ProjectElt idxs' a' -> ProjectElt (NE.cons i idxs') a'
  DataCon _ _ _ _ xs -> xs !! i
  Record items -> toList items !! i
  Con (ProdCon xs) -> xs !! i
  DepPair l _ _ | i == 0 -> l
  DepPair _ r _ | i == 1 -> r
  ACase scrut alts resultTy -> ACase scrut alts' resultTy'
    where
      alts' = alts <&> \(Abs bs body) -> Abs bs $ getProjection [i] body
      resultTy' = case resultTy of
        ProdTy tys -> tys !! i
        -- We can't handle all cases here because we'll end up needing access to
        -- the env. This `ProjectElt` is a steady source of issues. Maybe we can
        -- do away with it.
        _ -> error "oops"
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

pattern BoolTy :: Type n
pattern BoolTy = Word8Ty

pattern FalseAtom :: Atom n
pattern FalseAtom = Con (Lit (Word8Lit 0))

pattern TrueAtom :: Atom n
pattern TrueAtom = Con (Lit (Word8Lit 1))

fieldRowElemsFromList :: [FieldRowElem n] -> FieldRowElems n
fieldRowElemsFromList = foldr prependFieldRowElem (UnsafeFieldRowElems [])

prependFieldRowElem :: FieldRowElem n -> FieldRowElems n -> FieldRowElems n
prependFieldRowElem e (UnsafeFieldRowElems els) = case e of
  DynField  _ _ -> UnsafeFieldRowElems $ e : els
  DynFields _   -> UnsafeFieldRowElems $ e : els
  StaticFields items | null items -> UnsafeFieldRowElems els
  StaticFields items -> case els of
    (StaticFields items':rest) -> UnsafeFieldRowElems $ StaticFields (items <> items') : rest
    _                          -> UnsafeFieldRowElems $ e : els

extRowAsFieldRowElems :: ExtLabeledItems (Type n) (AtomName n) -> FieldRowElems n
extRowAsFieldRowElems (Ext items ext) = UnsafeFieldRowElems $ itemsEl ++ extEl
  where
    itemsEl = if null items then [] else [StaticFields items]
    extEl = case ext of Nothing -> []; Just r -> [DynFields r]

fieldRowElemsAsExtRow :: Alternative f => FieldRowElems n -> f (ExtLabeledItems (Type n) (AtomName n))
fieldRowElemsAsExtRow (UnsafeFieldRowElems els) = case els of
  []                                -> pure $ Ext mempty Nothing
  [DynFields r]                     -> pure $ Ext mempty (Just r)
  [StaticFields items]              -> pure $ Ext items  Nothing
  [StaticFields items, DynFields r] -> pure $ Ext items  (Just r)
  _ -> empty

_getAtMostSingleStatic :: Atom n -> Maybe (LabeledItems (Type n))
_getAtMostSingleStatic = \case
  RecordTy (UnsafeFieldRowElems els) -> case els of
    [] -> Just mempty
    [StaticFields items] -> Just items
    _ -> Nothing
  _ -> Nothing

pattern StaticRecordTy :: LabeledItems (Type n) -> Atom n
pattern StaticRecordTy items <- (_getAtMostSingleStatic -> Just items)
  where StaticRecordTy items = RecordTy (fieldRowElemsFromList [StaticFields items])

pattern RecordTyWithElems :: [FieldRowElem n] -> Atom n
pattern RecordTyWithElems elems <- RecordTy (UnsafeFieldRowElems elems)
  where RecordTyWithElems elems = RecordTy $ fieldRowElemsFromList elems

-- -- === instances ===

instance Semigroup (SourceMap n) where
  m1 <> m2 = SourceMap $ M.unionWith (++) (fromSourceMap m2) (fromSourceMap m1)

instance Monoid (SourceMap n) where
  mempty = SourceMap mempty

instance GenericE DataDef where
  type RepE DataDef = PairE (LiftE SourceName) (Abs (Nest Binder) (ListE DataConDef))
  fromE (DataDef name bs cons) = PairE (LiftE name) (Abs bs (ListE cons))
  toE   (PairE (LiftE name) (Abs bs (ListE cons))) = DataDef name bs cons
deriving instance Show (DataDef n)
deriving via WrapE DataDef n instance Generic (DataDef n)
instance SinkableE DataDef
instance HoistableE  DataDef
instance SubstE Name DataDef
instance SubstE AtomSubstVal DataDef
instance AlphaEqE DataDef
instance AlphaHashableE DataDef

instance GenericE DataConDef where
  type RepE DataConDef = PairE (LiftE SourceName) (Abs (Nest Binder) UnitE)
  fromE (DataConDef name ab) = PairE (LiftE name) ab
  toE   (PairE (LiftE name) ab) = DataConDef name ab
instance SinkableE DataConDef
instance HoistableE  DataConDef
instance SubstE Name DataConDef
instance SubstE AtomSubstVal DataConDef
instance AlphaEqE DataConDef
instance AlphaHashableE DataConDef

instance GenericE FieldRowElem where
  type RepE FieldRowElem = EitherE3 (ExtLabeledItemsE Type UnitE) (AtomName `PairE` Type) AtomName
  fromE = \case
    StaticFields items         -> Case0 $ ExtLabeledItemsE $ NoExt items
    DynField  labVarName labTy -> Case1 $ labVarName `PairE` labTy
    DynFields fieldVarName     -> Case2 $ fieldVarName
  toE = \case
    Case0 (ExtLabeledItemsE (Ext items _)) -> StaticFields items
    Case1 (n `PairE` t) -> DynField n t
    Case2 n             -> DynFields n
    _ -> error "unreachable"
instance SinkableE      FieldRowElem
instance HoistableE     FieldRowElem
instance SubstE Name    FieldRowElem
instance AlphaEqE       FieldRowElem
instance AlphaHashableE FieldRowElem

instance GenericE FieldRowElems where
  type RepE FieldRowElems = ListE FieldRowElem
  fromE = ListE . fromFieldRowElems
  toE = fieldRowElemsFromList . fromListE
instance SinkableE FieldRowElems
instance HoistableE FieldRowElems
instance SubstE Name FieldRowElems
instance AlphaEqE FieldRowElems
instance AlphaHashableE FieldRowElems
instance SubstE AtomSubstVal FieldRowElems where
  substE :: forall i o. Distinct o => (Scope o, Subst AtomSubstVal i o) -> FieldRowElems i -> FieldRowElems o
  substE env (UnsafeFieldRowElems els) = fieldRowElemsFromList $ foldMap substItem els
    where
      substItem = \case
        DynField v ty -> case snd env ! v of
          SubstVal (Con (LabelCon l)) -> [StaticFields $ labeledSingleton l ty']
          SubstVal (Var v') -> [DynField v' ty']
          Rename v'         -> [DynField v' ty']
          _ -> error "ill-typed substitution"
          where ty' = substE env ty
        DynFields v -> case snd env ! v of
          SubstVal (LabeledRow items) -> fromFieldRowElems items
          SubstVal (Var v') -> [DynFields v']
          Rename v'         -> [DynFields v']
          _ -> error "ill-typed substitution"
        StaticFields items -> [StaticFields items']
          where ExtLabeledItemsE (NoExt items') = substE env
                  (ExtLabeledItemsE (NoExt items) :: ExtLabeledItemsE Atom AtomName i)

instance GenericE ClassDef where
  type RepE ClassDef = PairE (LiftE (SourceName, [SourceName]))
                             (Name DataDefNameC)
  fromE (ClassDef className methodNames dataDefName) =
          PairE (LiftE (className, methodNames)) dataDefName
  toE (PairE (LiftE (className, methodNames)) dataDefName) =
        ClassDef className methodNames dataDefName
instance SinkableE         ClassDef
instance HoistableE        ClassDef
instance SubstE Name         ClassDef
instance SubstE AtomSubstVal ClassDef

instance GenericB DataConRefBinding where
  type RepB DataConRefBinding = PairB (LiftB Atom) Binder
  fromB (DataConRefBinding b val) = PairB (LiftB val) b
  toB   (PairB (LiftB val) b) = DataConRefBinding b val

instance SinkableB DataConRefBinding
instance HoistableB DataConRefBinding
instance ProvesExt  DataConRefBinding
instance BindsNames DataConRefBinding
instance SubstB Name DataConRefBinding
instance SubstB AtomSubstVal DataConRefBinding
instance AlphaEqB DataConRefBinding
instance AlphaHashableB DataConRefBinding
deriving instance Show (DataConRefBinding n l)
deriving instance Generic (DataConRefBinding n l)

newtype ExtLabeledItemsE (e1::E) (e2::E) (n::S) =
  ExtLabeledItemsE
   { fromExtLabeledItemsE :: ExtLabeledItems (e1 n) (e2 n) }

instance GenericE Atom where
  type RepE Atom =
      EitherE5
              (EitherE2
                   -- We isolate those few cases (and reorder them
                   -- compared to the data definition) because they need special
                   -- handling when you substitute with atoms. The rest just act
                   -- like containers
  {- Var -}        AtomName
  {- ProjectElt -} ( LiftE (NE.NonEmpty Int) `PairE` AtomName )
            ) (EitherE6
  {- Lam -}        LamExpr
  {- Pi -}         PiType
  {- DepPairTy -}  DepPairType
  {- DepPair -}    ( Atom `PairE` Atom `PairE` DepPairType)
  {- DataCon -}    ( LiftE (SourceName, Int)   `PairE`
                     DataDefName               `PairE`
                     ListE Atom                `PairE`
                     ListE Atom )
  {- TypeCon -}    ( LiftE SourceName `PairE` DataDefName `PairE` ListE Atom )
            ) (EitherE5
  {- LabeledRow -} ( FieldRowElems )
  {- Record -}     ( ComposeE LabeledItems Atom )
  {- RecordTy -}   ( FieldRowElems )
  {- Variant -}    ( ExtLabeledItemsE Type AtomName `PairE`
                     LiftE (Label, Int) `PairE` Atom )
  {- VariantTy -}  ( ExtLabeledItemsE Type AtomName )
            ) (EitherE2
  {- Con -}        (ComposeE PrimCon Atom)
  {- TC -}         (ComposeE PrimTC  Atom)
            ) (EitherE5
  {- Eff -}        EffectRow
  {- ACase -}      ( Atom `PairE` ListE (AltP Atom) `PairE` Type )
  {- DataConRef -} ( DataDefName                    `PairE`
                     ListE Atom                     `PairE`
                     EmptyAbs (Nest DataConRefBinding) )
  {- BoxedRef -}   ( ListE (Atom `PairE` Block) `PairE` NaryAbs AtomNameC Atom )
  {- DepPairRef -} ( Atom `PairE` Abs Binder Atom `PairE` DepPairType))

  fromE atom = case atom of
    Var v -> Case0 (Case0 v)
    ProjectElt idxs x -> Case0 (Case1 (PairE (LiftE idxs) x))
    Lam lamExpr -> Case1 (Case0 lamExpr)
    Pi  piExpr  -> Case1 (Case1 piExpr)
    DepPairTy ty -> Case1 (Case2 ty)
    DepPair l r ty -> Case1 (Case3 $ l `PairE` r `PairE` ty)
    DataCon printName defName params con args -> Case1 $ Case4 $
      LiftE (printName, con) `PairE`
            defName          `PairE`
      ListE params           `PairE`
      ListE args
    TypeCon sourceName defName params -> Case1 $ Case5 $
      LiftE sourceName `PairE` defName `PairE` ListE params
    LabeledRow elems    -> Case2 $ Case0 $ elems
    Record items        -> Case2 $ Case1 $ ComposeE items
    RecordTy elems -> Case2 $ Case2 elems
    Variant extItems l con payload -> Case2 $ Case3 $
      ExtLabeledItemsE extItems `PairE` LiftE (l, con) `PairE` payload
    VariantTy extItems  -> Case2 $ Case4 $ ExtLabeledItemsE extItems
    Con con -> Case3 $ Case0 $ ComposeE con
    TC  con -> Case3 $ Case1 $ ComposeE con
    Eff effs -> Case4 $ Case0 $ effs
    ACase scrut alts ty -> Case4 $ Case1 $ scrut `PairE` ListE alts `PairE` ty
    DataConRef defName params bs ->
      Case4 $ Case2 $ defName `PairE` ListE params `PairE` bs
    BoxedRef ptrsAndSizes ab ->
      Case4 $ Case3 $ ListE (map (uncurry PairE) ptrsAndSizes) `PairE` ab
    DepPairRef lhs rhs ty ->
      Case4 $ Case4 $ lhs `PairE` rhs `PairE` ty

  toE atom = case atom of
    Case0 val -> case val of
      Case0 v -> Var v
      Case1 (PairE (LiftE idxs) x) -> ProjectElt idxs x
      _ -> error "impossible"
    Case1 val -> case val of
      Case0 lamExpr -> Lam lamExpr
      Case1 piExpr  -> Pi  piExpr
      Case2 ty      -> DepPairTy ty
      Case3 (l `PairE` r `PairE` ty) -> DepPair l r ty
      Case4 ( LiftE (printName, con) `PairE`
                    defName          `PairE`
              ListE params           `PairE`
              ListE args ) ->
        DataCon printName defName params con args
      Case5 (LiftE sourceName `PairE` defName `PairE` ListE params) ->
        TypeCon sourceName defName params
      _ -> error "impossible"
    Case2 val -> case val of
      Case0 elems -> LabeledRow elems
      Case1 (ComposeE items) -> Record items
      Case2 elems -> RecordTy elems
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
      Case2 (defName `PairE` ListE params `PairE` bs) ->
        DataConRef defName params bs
      Case3 (ListE ptrsAndSizes `PairE` ab) -> BoxedRef (map fromPairE ptrsAndSizes) ab
      Case4 (lhs `PairE` rhs `PairE` ty) -> DepPairRef lhs rhs ty
      _ -> error "impossible"
    _ -> error "impossible"

instance SinkableE   Atom
instance HoistableE  Atom
instance AlphaEqE    Atom
instance AlphaHashableE Atom
instance SubstE Name Atom

-- TODO: special handling of ACase too
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
      _ -> error "impossible"
    RightE rest -> (toE . RightE) $ substE (scope, env) rest

trySelectBranch :: Atom n -> Maybe (Int, [Atom n])
trySelectBranch e = case e of
  DataCon _ _ _ con args -> return (con, args)
  Variant (NoExt types) label i value -> do
    let LabeledItems ixtypes = enumerate types
    let index = fst $ (ixtypes M.! label) NE.!! i
    return (index, [value])
  SumVal _ i value -> Just (i, [value])
  Con (SumAsProd _ (TagRepVal tag) vals) -> do
    let i = fromIntegral tag
    return (i , vals !! i)
  _ -> Nothing

instance GenericE Expr where
  type RepE Expr =
     EitherE5
        (Atom `PairE` Atom `PairE` ListE Atom)
        (Atom `PairE` ListE Alt `PairE` Type `PairE` EffectRow)
        (Atom)
        (ComposeE PrimOp Atom)
        (ComposeE PrimHof Atom)
  fromE = \case
    App f (x:|xs)  -> Case0 (f `PairE` x `PairE` ListE xs)
    Case e alts ty eff -> Case1 (e `PairE` ListE alts `PairE` ty `PairE` eff)
    Atom x         -> Case2 (x)
    Op op          -> Case3 (ComposeE op)
    Hof hof        -> Case4 (ComposeE hof)

  toE = \case
    Case0 (f `PairE` x `PairE` ListE xs)    -> App f (x:|xs)
    Case1 (e `PairE` ListE alts `PairE` ty `PairE` eff) -> Case e alts ty eff
    Case2 (x)                               -> Atom x
    Case3 (ComposeE op)                     -> Op op
    Case4 (ComposeE hof)                    -> Hof hof
    _ -> error "impossible"

instance SinkableE Expr
instance HoistableE  Expr
instance AlphaEqE Expr
instance AlphaHashableE Expr
instance SubstE Name Expr
instance SubstE AtomSubstVal Expr

instance GenericE (ExtLabeledItemsE e1 e2) where
  type RepE (ExtLabeledItemsE e1 e2) = EitherE (ComposeE LabeledItems e1)
                                               (ComposeE LabeledItems e1 `PairE` e2)
  fromE (ExtLabeledItemsE (Ext items Nothing))  = LeftE  (ComposeE items)
  fromE (ExtLabeledItemsE (Ext items (Just t))) = RightE (ComposeE items `PairE` t)

  toE (LeftE  (ComposeE items          )) = ExtLabeledItemsE (Ext items Nothing)
  toE (RightE (ComposeE items `PairE` t)) = ExtLabeledItemsE (Ext items (Just t))

instance (SinkableE e1, SinkableE e2) => SinkableE (ExtLabeledItemsE e1 e2)
instance (HoistableE  e1, HoistableE  e2) => HoistableE  (ExtLabeledItemsE e1 e2)
instance (AlphaEqE    e1, AlphaEqE    e2) => AlphaEqE    (ExtLabeledItemsE e1 e2)
instance (AlphaHashableE    e1, AlphaHashableE    e2) => AlphaHashableE    (ExtLabeledItemsE e1 e2)
instance (SubstE Name e1, SubstE Name e2) => SubstE Name (ExtLabeledItemsE e1 e2)

instance SubstE AtomSubstVal (ExtLabeledItemsE Atom AtomName) where
  substE (scope, env) (ExtLabeledItemsE (Ext items maybeExt)) = do
    let items' = fmap (substE (scope, env)) items
    let ext = case maybeExt of
                Nothing -> NoExt NoLabeledItems
                Just v -> case env ! v of
                  Rename        v'  -> Ext NoLabeledItems $ Just v'
                  SubstVal (Var v') -> Ext NoLabeledItems $ Just v'
                  SubstVal (LabeledRow row) -> case fieldRowElemsAsExtRow row of
                    Just row' -> row'
                    Nothing -> error "Not implemented: unrepresentable subst of ExtLabeledItems"
                  _ -> error "Not a valid labeled row substitution"
    ExtLabeledItemsE $ prefixExtLabeledItems items' ext

instance GenericE Block where
  type RepE Block = PairE (MaybeE Type) (Abs (Nest Decl) Expr)
  fromE (Block (BlockAnn ty) decls result) = PairE (JustE ty) (Abs decls result)
  fromE (Block NoBlockAnn Empty result) = PairE NothingE (Abs Empty result)
  fromE _ = error "impossible"
  toE   (PairE (JustE ty) (Abs decls result)) = Block (BlockAnn ty) decls result
  toE   (PairE NothingE (Abs Empty result)) = Block NoBlockAnn Empty result
  toE   _ = error "impossible"

deriving instance Show (BlockAnn n l)

instance SinkableE Block
instance HoistableE  Block
instance AlphaEqE Block
instance AlphaHashableE Block
instance SubstE Name Block
instance SubstE AtomSubstVal Block
deriving instance Show (Block n)
deriving via WrapE Block n instance Generic (Block n)

instance GenericE Cache where
  type RepE Cache =
            EMap AtomName AtomName
    `PairE` EMap AtomName ImpFunName
    `PairE` EMap ImpFunName CFun
    `PairE` LiftE (M.Map ModuleSourceName (FileHash, [ModuleSourceName]))
    `PairE` ListE (        LiftE ModuleSourceName
                   `PairE` LiftE FileHash
                   `PairE` ListE ModuleName
                   `PairE` ModuleName)
  fromE (Cache x y z parseCache evalCache) =
    x `PairE` y `PairE` z `PairE` LiftE parseCache `PairE`
      ListE [LiftE sourceName `PairE` LiftE hashVal `PairE` ListE deps `PairE` result
             | (sourceName, ((hashVal, deps), result)) <- M.toList evalCache ]
  toE   (x `PairE` y `PairE` z `PairE` LiftE parseCache `PairE` ListE evalCache) =
    Cache x y z parseCache
      (M.fromList
       [(sourceName, ((hashVal, deps), result))
       | LiftE sourceName `PairE` LiftE hashVal `PairE` ListE deps `PairE` result
          <- evalCache])

instance SinkableE  Cache
instance HoistableE Cache
instance AlphaEqE   Cache
instance SubstE Name Cache
instance Store (Cache n)

instance Monoid (Cache n) where
  mempty = Cache mempty mempty mempty mempty mempty
  mappend = (<>)

instance Semigroup (Cache n) where
  -- right-biased instead of left-biased
  Cache x1 x2 x3 x4 x5 <> Cache y1 y2 y3 y4 y5 =
    Cache (y1<>x1) (y2<>x2) (y3<>x3) (y4<>x4) (y5<>x5)

instance BindsOneAtomName (BinderP AtomNameC Type) where
  boundAtomBinding (_ :> ty) = MiscBound ty

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

instance BindsEnv LamBinder where
  toEnvFrag (LamBinder b ty arrow effects) =
    withExtEvidence b do
      let binding = toBinding $ sink $ LamBinding arrow ty
      EnvFrag (RecSubstFrag $ b @> binding)
                   (Just $ sink effects)

instance BindsAtMostOneName LamBinder AtomNameC where
  LamBinder b _ _ _ @> x = b @> x

instance BindsOneName LamBinder AtomNameC where
  binderName (LamBinder b _ _ _) = binderName b

instance BindsOneAtomName LamBinder where
  boundAtomBinding (LamBinder _ ty arr _) =
    LamBound $ LamBinding arr ty

instance HasNameHint (LamBinder n l) where
  getNameHint (LamBinder b _ _ _) = getNameHint b

instance ProvesExt  LamBinder
instance BindsNames LamBinder
instance SinkableB LamBinder
instance HoistableB  LamBinder
instance SubstB Name LamBinder
instance SubstB AtomSubstVal LamBinder
instance AlphaEqB LamBinder
instance AlphaHashableB LamBinder

instance GenericE LamBinding where
  type RepE LamBinding = PairE (LiftE Arrow) Type
  fromE (LamBinding arr ty) = PairE (LiftE arr) ty
  toE   (PairE (LiftE arr) ty) = LamBinding arr ty

instance SinkableE LamBinding
instance HoistableE  LamBinding
instance SubstE Name LamBinding
instance SubstE AtomSubstVal LamBinding
instance AlphaEqE LamBinding
instance AlphaHashableE LamBinding

instance GenericE LamExpr where
  type RepE LamExpr = Abs LamBinder Block
  fromE (LamExpr b block) = Abs b block
  toE   (Abs b block) = LamExpr b block

instance SinkableE LamExpr
instance HoistableE  LamExpr
instance AlphaEqE LamExpr
instance AlphaHashableE LamExpr
instance SubstE Name LamExpr
instance SubstE AtomSubstVal LamExpr
deriving instance Show (LamExpr n)
deriving via WrapE LamExpr n instance Generic (LamExpr n)

instance GenericE PiBinding where
  type RepE PiBinding = PairE (LiftE Arrow) Type
  fromE (PiBinding arr ty) = PairE (LiftE arr) ty
  toE   (PairE (LiftE arr) ty) = PiBinding arr ty

instance SinkableE PiBinding
instance HoistableE  PiBinding
instance SubstE Name PiBinding
instance SubstE AtomSubstVal PiBinding
instance AlphaEqE PiBinding
instance AlphaHashableE PiBinding

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

instance BindsEnv PiBinder where
  toEnvFrag (PiBinder b ty arr) =
    withExtEvidence b do
      let binding = toBinding $ sink $ PiBinding arr ty
      EnvFrag (RecSubstFrag $ b @> binding) (Just Pure)

instance HasNameHint (PiBinder n l) where
  getNameHint (PiBinder b _ _) = getNameHint b

instance ProvesExt  PiBinder
instance BindsNames PiBinder
instance SinkableB PiBinder
instance HoistableB  PiBinder
instance SubstB Name PiBinder
instance SubstB AtomSubstVal PiBinder
instance AlphaEqB PiBinder
instance AlphaHashableB PiBinder

instance GenericE PiType where
  type RepE PiType = Abs PiBinder (PairE EffectRow Type)
  fromE (PiType b eff resultTy) = Abs b (PairE eff resultTy)
  toE   (Abs b (PairE eff resultTy)) = PiType b eff resultTy

instance SinkableE PiType
instance HoistableE  PiType
instance AlphaEqE PiType
instance AlphaHashableE PiType
instance SubstE Name PiType
instance SubstE AtomSubstVal PiType
deriving instance Show (PiType n)
deriving via WrapE PiType n instance Generic (PiType n)

instance GenericE NaryPiType where
  type RepE NaryPiType = Abs (PairB PiBinder (Nest PiBinder)) (PairE EffectRow Type)
  fromE (NaryPiType (NonEmptyNest b bs) eff resultTy) = Abs (PairB b bs) (PairE eff resultTy)
  toE   (Abs (PairB b bs) (PairE eff resultTy)) = NaryPiType (NonEmptyNest b bs) eff resultTy

instance SinkableE NaryPiType
instance HoistableE  NaryPiType
instance AlphaEqE NaryPiType
instance AlphaHashableE NaryPiType
instance SubstE Name NaryPiType
instance SubstE AtomSubstVal NaryPiType
deriving instance Show (NaryPiType n)
deriving via WrapE NaryPiType n instance Generic (NaryPiType n)
instance Store (NaryPiType n)

instance GenericE NaryLamExpr where
  type RepE NaryLamExpr = Abs (PairB Binder (Nest Binder)) (PairE EffectRow Block)
  fromE (NaryLamExpr (NonEmptyNest b bs) eff body) = Abs (PairB b bs) (PairE eff body)
  toE   (Abs (PairB b bs) (PairE eff body)) = NaryLamExpr (NonEmptyNest b bs) eff body

instance SinkableE NaryLamExpr
instance HoistableE  NaryLamExpr
instance AlphaEqE NaryLamExpr
instance AlphaHashableE NaryLamExpr
instance SubstE Name NaryLamExpr
instance SubstE AtomSubstVal NaryLamExpr
deriving instance Show (NaryLamExpr n)
deriving via WrapE NaryLamExpr n instance Generic (NaryLamExpr n)
instance Store (NaryLamExpr n)

instance GenericE DepPairType where
  type RepE DepPairType = Abs Binder Type
  fromE (DepPairType b resultTy) = Abs b resultTy
  toE   (Abs b resultTy) = DepPairType b resultTy

instance SinkableE   DepPairType
instance HoistableE  DepPairType
instance AlphaEqE    DepPairType
instance AlphaHashableE DepPairType
instance SubstE Name DepPairType
instance SubstE AtomSubstVal DepPairType
deriving instance Show (DepPairType n)
deriving via WrapE DepPairType n instance Generic (DepPairType n)

instance GenericE (EffectP name) where
  type RepE (EffectP name) =
    EitherE (PairE (LiftE RWS) (MaybeE name))
            (LiftE (Either () ()))
  fromE = \case
    RWSEffect rws name -> LeftE  (PairE (LiftE rws) $ toMaybeE name)
    ExceptionEffect -> RightE (LiftE (Left  ()))
    IOEffect        -> RightE (LiftE (Right ()))
  toE = \case
    LeftE  (PairE (LiftE rws) name) -> RWSEffect rws $ fromMaybeE name
    RightE (LiftE (Left  ())) -> ExceptionEffect
    RightE (LiftE (Right ())) -> IOEffect

instance SinkableE   name => SinkableE   (EffectP name)
instance HoistableE     name => HoistableE     (EffectP name)
instance AlphaEqE       name => AlphaEqE       (EffectP name)
instance AlphaHashableE name => AlphaHashableE (EffectP name)
instance SubstE Name (EffectP AtomName)
instance SubstE AtomSubstVal (EffectP AtomName) where
  substE (_, env) eff = case eff of
    RWSEffect rws Nothing -> RWSEffect rws Nothing
    RWSEffect rws (Just v) -> do
      let v' = case env ! v of
                 Rename        v''  -> Just v''
                 SubstVal UnitTy    -> Nothing  -- used at runtime/imp-translation-time
                 SubstVal (Var v'') -> Just v''
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

instance SinkableE (EffectRowP AtomName)
instance HoistableE  (EffectRowP AtomName)
instance SubstE Name (EffectRowP AtomName)
instance AlphaEqE    (EffectRowP AtomName)
instance AlphaHashableE    (EffectRowP AtomName)

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
  type RepE SynthCandidates =
    ListE Atom `PairE` ListE Atom `PairE` ListE (PairE DataDefName (ListE Atom))
  fromE (SynthCandidates xs ys zs) = ListE xs `PairE` ListE ys `PairE` ListE zs'
    where zs' = map (\(k,vs) -> PairE k (ListE vs)) (M.toList zs)
  toE (ListE xs `PairE` ListE ys `PairE` ListE zs) = SynthCandidates xs ys zs'
    where zs' = M.fromList $ map (\(PairE k (ListE vs)) -> (k,vs)) zs

instance SinkableE      SynthCandidates
instance HoistableE     SynthCandidates
instance AlphaEqE       SynthCandidates
instance AlphaHashableE SynthCandidates
instance SubstE Name    SynthCandidates

instance GenericE AtomBinding where
  type RepE AtomBinding =
     EitherE2
       (EitherE5
          DeclBinding     -- LetBound
          LamBinding      -- LamBound
          PiBinding       -- PiBound
          Type            -- MiscBound
          SolverBinding)  -- SolverBound
       (EitherE3
          (PairE (LiftE PtrType) PtrName) -- PtrLitBound
          (PairE NaryPiType NaryLamExpr)  -- SimpLamBound
          (PairE NaryPiType ImpFunName))  -- FFIFunBound

  fromE = \case
    LetBound    x -> Case0 $ Case0 x
    LamBound    x -> Case0 $ Case1 x
    PiBound     x -> Case0 $ Case2 x
    MiscBound   x -> Case0 $ Case3 x
    SolverBound x -> Case0 $ Case4 x
    PtrLitBound x y -> Case1 (Case0 (LiftE x `PairE` y))
    SimpLamBound x y  -> Case1 (Case1 (PairE x y))
    FFIFunBound x y   -> Case1 (Case2 (PairE x y))

  toE = \case
    Case0 x' -> case x' of
      Case0 x -> LetBound x
      Case1 x -> LamBound x
      Case2 x -> PiBound  x
      Case3 x -> MiscBound x
      Case4 x -> SolverBound x
      _ -> error "impossible"
    Case1 x' -> case x' of
      Case0 (LiftE x `PairE` y) -> PtrLitBound x y
      Case1 (PairE x y) -> SimpLamBound x y
      Case2 (PairE x y) -> FFIFunBound x y
      _ -> error "impossible"
    _ -> error "impossible"

instance SinkableE AtomBinding
instance HoistableE  AtomBinding
instance SubstE Name AtomBinding
instance SubstE AtomSubstVal AtomBinding
instance AlphaEqE AtomBinding
instance AlphaHashableE AtomBinding

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

instance SinkableE SolverBinding
instance HoistableE  SolverBinding
instance SubstE Name SolverBinding
instance SubstE AtomSubstVal SolverBinding
instance AlphaEqE SolverBinding
instance AlphaHashableE SolverBinding

instance Color c => GenericE (Binding c) where
  type RepE (Binding c) =
    EitherE2
      (EitherE5
          AtomBinding
          DataDef
          (DataDefName `PairE` Atom)
          (DataDefName `PairE` LiftE Int `PairE` Atom)
          (ClassDef `PairE` Atom))
      (EitherE6
          (Name ClassNameC `PairE` LiftE Int `PairE` Atom)
          (Name ClassNameC `PairE` LiftE Int `PairE` Atom)
          (ImpFunction)
          (ObjectFile)
          (Module)
          (LiftE PtrLitVal))
  fromE binding = case binding of
    AtomNameBinding   tyinfo            -> Case0 $ Case0 $ tyinfo
    DataDefBinding    dataDef           -> Case0 $ Case1 $ dataDef
    TyConBinding      dataDefName     e -> Case0 $ Case2 $ dataDefName `PairE` e
    DataConBinding    dataDefName idx e -> Case0 $ Case3 $ dataDefName `PairE` LiftE idx `PairE` e
    ClassBinding      classDef        e -> Case0 $ Case4 $ classDef `PairE` e
    SuperclassBinding className idx e   -> Case1 $ Case0 $ className `PairE` LiftE idx `PairE` e
    MethodBinding     className idx e   -> Case1 $ Case1 $ className `PairE` LiftE idx `PairE` e
    ImpFunBinding     fun               -> Case1 $ Case2 $ fun
    ObjectFileBinding objfile           -> Case1 $ Case3 $ objfile
    ModuleBinding m                     -> Case1 $ Case4 $ m
    PtrBinding p                        -> Case1 $ Case5 $ LiftE p

  toE rep = case rep of
    Case0 (Case0 tyinfo)                                    -> fromJust $ tryAsColor $ AtomNameBinding   tyinfo
    Case0 (Case1 dataDef)                                   -> fromJust $ tryAsColor $ DataDefBinding    dataDef
    Case0 (Case2 (dataDefName `PairE` e))                   -> fromJust $ tryAsColor $ TyConBinding      dataDefName e
    Case0 (Case3 (dataDefName `PairE` LiftE idx `PairE` e)) -> fromJust $ tryAsColor $ DataConBinding    dataDefName idx e
    Case0 (Case4 (classDef `PairE` e))                      -> fromJust $ tryAsColor $ ClassBinding      classDef e
    Case1 (Case0 (className `PairE` LiftE idx `PairE` e))   -> fromJust $ tryAsColor $ SuperclassBinding className idx e
    Case1 (Case1 (className `PairE` LiftE idx `PairE` e))   -> fromJust $ tryAsColor $ MethodBinding     className idx e
    Case1 (Case2 fun)                                       -> fromJust $ tryAsColor $ ImpFunBinding     fun
    Case1 (Case3 objfile)                                   -> fromJust $ tryAsColor $ ObjectFileBinding objfile
    Case1 (Case4 m)                                         -> fromJust $ tryAsColor $ ModuleBinding     m
    Case1 (Case5 (LiftE ptr))                               -> fromJust $ tryAsColor $ PtrBinding        ptr
    _ -> error "impossible"

deriving via WrapE (Binding c) n instance Color c => Generic (Binding c n)
instance SinkableV         Binding
instance HoistableV        Binding
instance SubstV Name       Binding
instance Color c => SinkableE   (Binding c)
instance Color c => HoistableE  (Binding c)
instance Color c => SubstE Name (Binding c)

instance GenericE DeclBinding where
  type RepE DeclBinding = LiftE LetAnn `PairE` Type `PairE` Expr
  fromE (DeclBinding ann ty expr) = LiftE ann `PairE` ty `PairE` expr
  toE   (LiftE ann `PairE` ty `PairE` expr) = DeclBinding ann ty expr

instance SinkableE DeclBinding
instance HoistableE  DeclBinding
instance SubstE Name DeclBinding
instance SubstE AtomSubstVal DeclBinding
instance AlphaEqE DeclBinding
instance AlphaHashableE DeclBinding

instance GenericB Decl where
  type RepB Decl = AtomBinderP DeclBinding
  fromB (Let b binding) = b :> binding
  toB   (b :> binding) = Let b binding

instance SinkableB Decl
instance HoistableB  Decl
instance SubstB AtomSubstVal Decl
instance SubstB Name Decl
instance AlphaEqB Decl
instance AlphaHashableB Decl
instance ProvesExt  Decl
instance BindsNames Decl
instance BindsEnv Decl

instance Pretty Arrow where
  pretty arr = case arr of
    PlainArrow     -> "->"
    TabArrow       -> "=>"
    LinArrow       -> "--o"
    ImplicitArrow  -> "?->"
    ClassArrow     -> "?=>"

instance Semigroup (SynthCandidates n) where
  SynthCandidates xs ys zs <> SynthCandidates xs' ys' zs' =
    SynthCandidates (xs<>xs') (ys<>ys') (M.unionWith (<>) zs zs')

instance Monoid (SynthCandidates n) where
  mempty = SynthCandidates mempty mempty mempty

instance GenericE SourceNameDef where
  type RepE SourceNameDef = EitherE UVar (LiftE ModuleSourceName `PairE` MaybeE UVar)
  fromE (LocalVar v) = LeftE v
  fromE (ModuleVar name maybeUVar) = RightE (PairE (LiftE name) (toMaybeE maybeUVar))
  toE (LeftE v) = LocalVar v
  toE (RightE (PairE (LiftE name) maybeUVar)) = ModuleVar name (fromMaybeE maybeUVar)

instance SinkableE      SourceNameDef
instance HoistableE     SourceNameDef
instance AlphaEqE       SourceNameDef
instance AlphaHashableE SourceNameDef
instance SubstE Name    SourceNameDef

instance GenericE SourceMap where
  type RepE SourceMap = ListE (PairE (LiftE SourceName) (ListE SourceNameDef))
  fromE (SourceMap m) = ListE [PairE (LiftE v) (ListE defs) | (v, defs) <- M.toList m]
  toE   (ListE pairs) = SourceMap $ M.fromList [(v, defs) | (PairE (LiftE v) (ListE defs)) <- pairs]

deriving via WrapE SourceMap n instance Generic (SourceMap n)

instance SinkableE      SourceMap
instance HoistableE     SourceMap
instance AlphaEqE       SourceMap
instance AlphaHashableE SourceMap
instance SubstE Name    SourceMap

instance Pretty (SourceNameDef n) where
  pretty def = case def of
    LocalVar v -> pretty v
    ModuleVar _ Nothing -> "<error in definition>"
    ModuleVar mname (Just v) -> pretty v <> " defined in " <> pretty mname

instance Pretty ModuleSourceName where
  pretty Main = "main"
  pretty Prelude = "prelude"
  pretty (OrdinaryModule s) = pretty s

instance Pretty (SourceMap n) where
  pretty (SourceMap m) =
    fold [pretty v <+> "@>" <+> pretty x <> hardline | (v, x) <- M.toList m ]

instance GenericE ObjectFile where
  type RepE ObjectFile = LiftE (BS.ByteString, [CFunName]) `PairE` ListE ObjectFileName
  fromE (ObjectFile contents fs deps) = LiftE (contents, fs) `PairE` ListE deps
  toE   (LiftE (contents, fs) `PairE` ListE deps) = ObjectFile contents fs deps

instance Store (ObjectFile n)
instance SubstE Name ObjectFile
instance SinkableE  ObjectFile
instance HoistableE ObjectFile

instance GenericE CFun where
  type RepE CFun = LiftE CFunName `PairE` ObjectFileName
  fromE (CFun name obj) = LiftE name `PairE` obj
  toE   (LiftE name `PairE` obj) = CFun name obj

instance Store (CFun n)
instance SubstE Name CFun
instance AlphaEqE CFun
instance SinkableE  CFun
instance HoistableE CFun

instance Store ForAnn
instance Store AddressSpace
instance Store LetAnn
instance Store RWS
instance Store Direction
instance Store UnOp
instance Store BinOp
instance Store CmpOp
instance Store BaseType
instance Store LitVal
instance Store ScalarBaseType
instance Store Device
instance Store LogLevel
instance Store PassName
instance Store ModuleSourceName

instance Store a => Store (PrimOp  a)
instance Store a => Store (PrimCon a)
instance Store a => Store (PrimTC  a)
instance Store a => Store (PrimHof a)
instance Store a => Store (Limit a)
instance Store a => Store (PrimEffect a)
instance Store a => Store (BaseMonoidP a)

instance Store (Atom n)
instance Store (Expr n)
instance Store (SolverBinding n)
instance Store (AtomBinding n)
instance Store (LamBinding  n)
instance Store (DeclBinding n)
instance Store (FieldRowElem  n)
instance Store (FieldRowElems n)
instance Store (Decl n l)
instance Store (DataDef n)
instance Store (DataConDef n)
instance Store (Block n)
instance Store (LamBinder n l)
instance Store (LamExpr n)
instance Store (PiBinding n)
instance Store (PiBinder n l)
instance Store (PiType  n)
instance Store (DepPairType  n)
instance Store Arrow
instance Store (ClassDef       n)
instance Store (UVar n)
instance Store (SourceNameDef n)
instance Store (SourceMap n)
instance Store (SynthCandidates n)
instance Store (EffectRow n)
instance Store (Effect n)
instance Store (DataConRefBinding n l)
instance Store (ObjectFiles n)
instance Store (Module n)
instance Store (ImportStatus n)
instance Store (LoadedModules n)
instance Color c => Store (Binding c n)
instance Store (ModuleEnv n)
instance Store (TopEnv n)
instance Store (Env n)

instance Store IsCUDARequired
instance Store CallingConvention

instance Store (IBinder n l)
instance Store (ImpDecl n l)
instance Store (IFunType)
instance Store (ImpInstr n)
instance Store (IExpr n)
instance Store (ImpBlock n)
instance Store (ImpFunction n)

instance Hashable ForAnn
instance Hashable AddressSpace
instance Hashable LetAnn
instance Hashable RWS
instance Hashable Direction
instance Hashable UnOp
instance Hashable BinOp
instance Hashable CmpOp
instance Hashable BaseType
instance Hashable PtrLitVal
instance Hashable PtrSnapshot
instance Hashable LitVal
instance Hashable ScalarBaseType
instance Hashable Device
instance Hashable Arrow
instance Hashable ModuleSourceName

instance Hashable IsCUDARequired
instance Hashable CallingConvention
instance Hashable IFunType

instance Hashable a => Hashable (PrimOp  a)
instance Hashable a => Hashable (PrimCon a)
instance Hashable a => Hashable (PrimTC  a)
instance Hashable a => Hashable (PrimHof a)
instance Hashable a => Hashable (Limit a)
instance Hashable a => Hashable (PrimEffect a)
instance Hashable a => Hashable (BaseMonoidP a)

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

instance (BindsEnv b1, BindsEnv b2)
         => (BindsEnv (PairB b1 b2)) where
  toEnvFrag (PairB b1 b2) = do
    let bindings2 = toEnvFrag b2
    let ext = toExtEvidence bindings2
    withSubscopeDistinct ext do
      toEnvFrag b1 `catEnvFrags` bindings2

instance BindsEnv b => (BindsEnv (Nest b)) where
  toEnvFrag Empty = emptyOutFrag
  toEnvFrag (Nest b rest) = toEnvFrag $ PairB b rest

instance BindsEnv b => (BindsEnv (NonEmptyNest b)) where
  toEnvFrag (NonEmptyNest b rest) = toEnvFrag $ Nest b rest

instance (BindsEnv b1, BindsEnv b2)
         => (BindsEnv (EitherB b1 b2)) where
  toEnvFrag (LeftB  b) = toEnvFrag b
  toEnvFrag (RightB b) = toEnvFrag b

instance GenericB EnvFrag where
  type RepB EnvFrag = PairB (RecSubstFrag Binding) (LiftB (MaybeE EffectRow))
  fromB (EnvFrag frag (Just effs)) = PairB frag (LiftB (JustE effs))
  fromB (EnvFrag frag Nothing    ) = PairB frag (LiftB NothingE)
  toB   (PairB frag (LiftB (JustE effs))) = EnvFrag frag (Just effs)
  toB   (PairB frag (LiftB NothingE    )) = EnvFrag frag Nothing
  toB   _ = error "impossible" -- GHC exhaustiveness bug?

instance SinkableB   EnvFrag
instance HoistableB  EnvFrag
instance ProvesExt   EnvFrag
instance BindsNames  EnvFrag
instance SubstB Name EnvFrag

instance BindsEnv EnvFrag where
  toEnvFrag frag = frag

instance BindsEnv (RecSubstFrag Binding) where
  toEnvFrag frag = EnvFrag frag mempty

instance BindsEnv UnitB where
  toEnvFrag UnitB = emptyOutFrag

instance GenericE UVar where
  type RepE UVar = EitherE5 (Name AtomNameC)    (Name TyConNameC)
                            (Name DataConNameC) (Name ClassNameC)
                            (Name MethodNameC)
  fromE name = case name of
    UAtomVar    v -> Case0 v
    UTyConVar   v -> Case1 v
    UDataConVar v -> Case2 v
    UClassVar   v -> Case3 v
    UMethodVar  v -> Case4 v

  toE name = case name of
    Case0 v -> UAtomVar    v
    Case1 v -> UTyConVar   v
    Case2 v -> UDataConVar v
    Case3 v -> UClassVar   v
    Case4 v -> UMethodVar  v
    _ -> error "impossible"

instance Pretty (UVar n) where
  pretty name = case name of
    UAtomVar    v -> "Atom name: " <> pretty v
    UTyConVar   v -> "Type constructor name: " <> pretty v
    UDataConVar v -> "Data constructor name: " <> pretty v
    UClassVar   v -> "Class name: " <> pretty v
    UMethodVar  v -> "Method name: " <> pretty v

-- TODO: name subst instances for the rest of UExpr
instance SinkableE      UVar
instance HoistableE     UVar
instance AlphaEqE       UVar
instance AlphaHashableE UVar
instance SubstE Name    UVar

instance SinkableE e => SinkableE (WithEnv e) where
  sinkingProofE (fresh::SinkingCoercion n l) (WithEnv (bindings :: Env h) e) =
    withExtEvidence (sinkingProofE fresh ext) $
      WithEnv bindings e
    where ext = getExtEvidence :: ExtEvidence h n

instance HasNameHint (b n l) => HasNameHint (WithSrcB b n l) where
  getNameHint (WithSrcB _ b) = getNameHint b

instance HasNameHint (UPat' n l) where
  getNameHint (UPatBinder b) = getNameHint b
  getNameHint _ = "pat"

instance Color c => HasNameHint (UBinder c n l) where
  getNameHint b = case b of
    UBindSource v -> getNameHint v
    UIgnore       -> fromString "_ign"
    UBind v _     -> getNameHint v

instance Color c => BindsNames (UBinder c) where
  toScopeFrag (UBindSource _) = emptyOutFrag
  toScopeFrag (UIgnore)       = emptyOutFrag
  toScopeFrag (UBind _ b)     = toScopeFrag b

instance Color c => ProvesExt (UBinder c) where
instance Color c => BindsAtMostOneName (UBinder c) c where
  b @> x = case b of
    UBindSource _ -> emptyInFrag
    UIgnore       -> emptyInFrag
    UBind _ b'    -> b' @> x

uBinderSourceName :: UBinder c n l -> SourceName
uBinderSourceName b = case b of
  UBindSource v -> v
  UIgnore       -> "_"
  UBind v _     -> v

instance Color c => ProvesExt (UAnnBinder c) where
instance Color c => BindsNames (UAnnBinder c) where
  toScopeFrag (UAnnBinder b _) = toScopeFrag b

instance Color c => BindsAtMostOneName (UAnnBinder c) c where
  UAnnBinder b _ @> x = b @> x

instance Eq SourceBlock where
  x == y = sbText x == sbText y

instance Ord SourceBlock where
  compare x y = compare (sbText x) (sbText y)

instance GenericE ImpInstr where
  type RepE ImpInstr = EitherE4
      (EitherE4
  {- IFor -}    (LiftE Direction `PairE` Size `PairE` Abs IBinder ImpBlock)
  {- IWhile -}  (ImpBlock)
  {- ICond -}   (IExpr `PairE` ImpBlock `PairE` ImpBlock)
  {- IQuery -}  (LiftE IFunVar `PairE` IExpr)
    ) (EitherE4
  {- ISyncW -}  (UnitE)
  {- ILaunch -} (LiftE IFunVar `PairE` Size `PairE` ListE IExpr)
  {- ICall -}   (ImpFunName `PairE` ListE IExpr)
  {- Store -}   (IExpr `PairE` IExpr)
    ) (EitherE4
  {- Alloc -}   (LiftE (AddressSpace, IType) `PairE` Size)
  {- MemCopy -} (IExpr `PairE` IExpr `PairE` IExpr)
  {- Free -}    (IExpr)
  {- IThrowE -} (UnitE)
    ) (EitherE2
  {- ICastOp -} (LiftE IType `PairE` IExpr)
  {- IPrimOp -} (ComposeE PrimOp IExpr)
      )

  fromE instr = case instr of
    IFor d n ab           -> Case0 $ Case0 $ LiftE d `PairE` n `PairE` ab
    IWhile body           -> Case0 $ Case1 body
    ICond p cons alt      -> Case0 $ Case2 $ p `PairE` cons `PairE` alt
    IQueryParallelism f s -> Case0 $ Case3 $ LiftE f `PairE` s

    ISyncWorkgroup      -> Case1 $ Case0 UnitE
    ILaunch f n args    -> Case1 $ Case1 $ LiftE f `PairE` n `PairE` ListE args
    ICall f args        -> Case1 $ Case2 $ f `PairE` ListE args
    Store dest val      -> Case1 $ Case3 $ dest `PairE` val

    Alloc a t s            -> Case2 $ Case0 $ LiftE (a, t) `PairE` s
    MemCopy dest src numel -> Case2 $ Case1 $ dest `PairE` src `PairE` numel
    Free ptr               -> Case2 $ Case2 ptr
    IThrowError            -> Case2 $ Case3 UnitE

    ICastOp idt ix -> Case3 $ Case0 $ LiftE idt `PairE` ix
    IPrimOp op     -> Case3 $ Case1 $ ComposeE op

  toE instr = case instr of
    Case0 instr' -> case instr' of
      Case0 (LiftE d `PairE` n `PairE` ab) -> IFor d n ab
      Case1 body                           -> IWhile body
      Case2 (p `PairE` cons `PairE` alt)   -> ICond p cons alt
      Case3 (LiftE f `PairE` s)            -> IQueryParallelism f s
      _ -> error "impossible"

    Case1 instr' -> case instr' of
      Case0 UnitE                                     -> ISyncWorkgroup
      Case1 (LiftE f `PairE` n `PairE` ListE args)    -> ILaunch f n args
      Case2 (f `PairE` ListE args)                    -> ICall f args
      Case3 (dest `PairE` val )                       -> Store dest val
      _ -> error "impossible"

    Case2 instr' -> case instr' of
      Case0 (LiftE (a, t) `PairE` s )         -> Alloc a t s
      Case1 (dest `PairE` src `PairE` numel)  -> MemCopy dest src numel
      Case2 ptr                               -> Free ptr
      Case3 UnitE                             -> IThrowError
      _ -> error "impossible"

    Case3 instr' -> case instr' of
      Case0 (LiftE idt `PairE` ix ) -> ICastOp idt ix
      Case1 (ComposeE op )          -> IPrimOp op
      _ -> error "impossible"

    _ -> error "impossible"

instance SinkableE ImpInstr
instance HoistableE  ImpInstr
instance AlphaEqE ImpInstr
instance AlphaHashableE ImpInstr
instance SubstE Name ImpInstr

instance GenericE ImpBlock where
  type RepE ImpBlock = Abs (Nest ImpDecl) (ListE IExpr)
  fromE (ImpBlock decls results) = Abs decls (ListE results)
  toE   (Abs decls (ListE results)) = ImpBlock decls results

instance SinkableE ImpBlock
instance HoistableE  ImpBlock
instance AlphaEqE ImpBlock
instance AlphaHashableE ImpBlock
instance SubstE Name ImpBlock
deriving via WrapE ImpBlock n instance Generic (ImpBlock n)

instance GenericE IExpr where
  type RepE IExpr = EitherE2 (LiftE LitVal)
                             (PairE AtomName (LiftE BaseType))
  fromE iexpr = case iexpr of
    ILit x -> Case0 (LiftE x)
    IVar v ty -> Case1 (v `PairE` LiftE ty)

  toE rep = case rep of
    Case0 (LiftE x) -> ILit x
    Case1 (v `PairE` LiftE ty) -> IVar v ty
    _ -> error "impossible"

instance SinkableE IExpr
instance HoistableE  IExpr
instance AlphaEqE IExpr
instance AlphaHashableE IExpr
instance SubstE Name IExpr

instance GenericB IBinder where
  type RepB IBinder = PairB (LiftB (LiftE IType)) (NameBinder AtomNameC)
  fromB (IBinder b ty) = PairB (LiftB (LiftE ty)) b
  toB   (PairB (LiftB (LiftE ty)) b) = IBinder b ty

instance HasNameHint (IBinder n l) where
  getNameHint (IBinder b _) = getNameHint b

instance BindsEnv IBinder where
  toEnvFrag (IBinder b ty) = toEnvFrag $ b :> BaseTy ty

instance BindsAtMostOneName IBinder AtomNameC where
  IBinder b _ @> x = b @> x

instance BindsOneName IBinder AtomNameC where
  binderName (IBinder b _) = binderName b

instance BindsNames IBinder where
  toScopeFrag (IBinder b _) = toScopeFrag b

instance ProvesExt  IBinder
instance SinkableB IBinder
instance HoistableB  IBinder
instance SubstB Name IBinder
instance SubstB AtomSubstVal IBinder
instance AlphaEqB IBinder
instance AlphaHashableB IBinder

instance GenericB ImpDecl where
  type RepB ImpDecl = PairB (LiftB ImpInstr) (Nest IBinder)
  fromB (ImpLet bs instr) = PairB (LiftB instr) bs
  toB   (PairB (LiftB instr) bs) = ImpLet bs instr

instance SinkableB ImpDecl
instance HoistableB  ImpDecl
instance SubstB Name ImpDecl
instance AlphaEqB ImpDecl
instance AlphaHashableB ImpDecl
instance ProvesExt  ImpDecl
instance BindsNames ImpDecl

instance BindsEnv ImpDecl where
  toEnvFrag (ImpLet bs _) =
    toEnvFrag bs

instance GenericE ImpFunction where
  type RepE ImpFunction = EitherE2 (LiftE IFunType `PairE` Abs (Nest IBinder) ImpBlock)
                                   (LiftE (IFunType, SourceName))
  fromE f = case f of
    ImpFunction ty ab   -> Case0 $ LiftE ty `PairE` ab
    FFIFunction ty name -> Case1 $ LiftE (ty, name)

  toE f = case f of
    Case0 (LiftE ty `PairE` ab) -> ImpFunction ty ab
    Case1 (LiftE (ty, name))    -> FFIFunction ty name
    _ -> error "impossible"

instance SinkableE ImpFunction
instance HoistableE  ImpFunction
instance AlphaEqE    ImpFunction
instance AlphaHashableE    ImpFunction
instance SubstE Name ImpFunction

instance GenericE PartialTopEnvFrag where
  type RepE PartialTopEnvFrag = Cache
                              `PairE` LoadedModules
                              `PairE` ModuleEnv
  fromE (PartialTopEnvFrag cache loaded env) = cache `PairE` loaded `PairE` env
  toE (cache `PairE` loaded `PairE` env) = PartialTopEnvFrag cache loaded env

instance SinkableE      PartialTopEnvFrag
instance HoistableE     PartialTopEnvFrag
instance AlphaEqE       PartialTopEnvFrag
instance SubstE Name    PartialTopEnvFrag

instance Semigroup (PartialTopEnvFrag n) where
  PartialTopEnvFrag x1 x2 x3 <> PartialTopEnvFrag y1 y2 y3 =
    PartialTopEnvFrag (x1<>y1) (x2<>y2) (x3<>y3)

instance Monoid (PartialTopEnvFrag n) where
  mempty = PartialTopEnvFrag mempty mempty mempty
  mappend = (<>)

instance GenericB TopEnvFrag where
  type RepB TopEnvFrag = PairB EnvFrag (LiftB PartialTopEnvFrag)
  fromB (TopEnvFrag frag1 frag2) = PairB frag1 (LiftB frag2)
  toB   (PairB frag1 (LiftB frag2)) = TopEnvFrag frag1 frag2

instance BindsEnv TopEnvFrag where
  toEnvFrag = undefined

instance SubstB Name TopEnvFrag
instance HoistableB  TopEnvFrag
instance SinkableB TopEnvFrag
instance ProvesExt   TopEnvFrag
instance BindsNames  TopEnvFrag

instance OutFrag TopEnvFrag where
  emptyOutFrag = TopEnvFrag emptyOutFrag mempty
  catOutFrags scope (TopEnvFrag frag1 partial1)
                    (TopEnvFrag frag2 partial2) =
    withExtEvidence frag2 $
      TopEnvFrag
        (catOutFrags scope frag1 frag2)
        (sink partial1 <> partial2)

-- XXX: unlike `ExtOutMap Env EnvFrag` instance, this once doesn't
-- extend the synthesis candidates based on the annotated let-bound names. It
-- only extends synth candidates when they're supplied explicitly.
instance ExtOutMap Env TopEnvFrag where
  extendOutMap (Env (TopEnv scope defs cache loaded) mEnv)
               (TopEnvFrag (EnvFrag frag _)
                  (PartialTopEnvFrag cache' loaded' mEnv')) =
    Env newTopEnv newModuleEnv
    where
      newTopEnv = withExtEvidence frag $ TopEnv
        (scope `extendOutMap` toScopeFrag frag)
        (defs `extendRecSubst` frag)
        (sink cache <> cache')
        (sink loaded <> loaded')

      newModuleEnv = withExtEvidence frag $ runEnvReaderM (Env newTopEnv mempty) do
        let ModuleEnv imports sm scs objs effs = sink mEnv
        let ModuleEnv imports' sm' scs' objs' effs' = mEnv'
        let newDirectImports = S.difference (directImports imports') (directImports imports)
        let newTransImports  = S.difference (transImports  imports') (transImports  imports)
        newImportedSM  <- flip foldMapM newDirectImports $ liftM moduleExports         . lookupModule
        newImportedSC  <- flip foldMapM newTransImports  $ liftM moduleSynthCandidates . lookupModule
        newImportedObj <- flip foldMapM newTransImports  $ liftM moduleObjectFiles     . lookupModule
        return $ ModuleEnv
          (imports <> imports')
          (sm   <> sm'   <> newImportedSM)
          (scs  <> scs'  <> newImportedSC)
          (objs <> objs' <> newImportedObj)
          (effs <> effs')

instance GenericE (WithSrcE e) where
  type RepE (WithSrcE e) = PairE (LiftE SrcPosCtx) e
  fromE (WithSrcE ctx x) = PairE (LiftE ctx) x
  toE   (PairE (LiftE ctx) x) = WithSrcE ctx x

instance SinkableE e => SinkableE (WithSrcE e)

instance SinkableE UExpr' where
  sinkingProofE _ = todoSinkableProof

instance SinkableB UDecl where
  sinkingProofB _ _ _ = todoSinkableProof

instance GenericE Module where
  type RepE Module =       LiftE ModuleSourceName
                   `PairE` ListE ModuleName
                   `PairE` ListE ModuleName
                   `PairE` SourceMap
                   `PairE` SynthCandidates
                   `PairE` ObjectFiles

  fromE (Module name deps transDeps sm sc objs) =
    LiftE name `PairE` ListE (S.toList deps) `PairE` ListE (S.toList transDeps)
      `PairE` sm `PairE` sc `PairE` objs

  toE (LiftE name `PairE` ListE deps `PairE` ListE transDeps
         `PairE` sm `PairE` sc `PairE` objs) =
    Module name (S.fromList deps) (S.fromList transDeps) sm sc objs

instance SinkableE      Module
instance HoistableE     Module
instance AlphaEqE       Module
instance AlphaHashableE Module
instance SubstE Name    Module

instance GenericE ImportStatus where
  type RepE ImportStatus = ListE ModuleName `PairE` ListE ModuleName
  fromE (ImportStatus direct trans) = ListE (S.toList direct)
                              `PairE` ListE (S.toList trans)
  toE (ListE direct `PairE` ListE trans) =
    ImportStatus (S.fromList direct) (S.fromList trans)

instance SinkableE      ImportStatus
instance HoistableE     ImportStatus
instance AlphaEqE       ImportStatus
instance AlphaHashableE ImportStatus
instance SubstE Name    ImportStatus

instance Semigroup (ImportStatus n) where
  ImportStatus direct trans <> ImportStatus direct' trans' =
    ImportStatus (direct <> direct') (trans <> trans')

instance Monoid (ImportStatus n) where
  mappend = (<>)
  mempty = ImportStatus mempty mempty

instance GenericE LoadedModules where
  type RepE LoadedModules = ListE (PairE (LiftE ModuleSourceName) ModuleName)
  fromE (LoadedModules m) =
    ListE $ M.toList m <&> \(v,md) -> PairE (LiftE v) md
  toE (ListE pairs) =
    LoadedModules $ M.fromList $ pairs <&> \(PairE (LiftE v) md) -> (v, md)

instance SinkableE      LoadedModules
instance HoistableE     LoadedModules
instance AlphaEqE       LoadedModules
instance AlphaHashableE LoadedModules
instance SubstE Name    LoadedModules

instance GenericE ObjectFiles where
  type RepE ObjectFiles = ListE ObjectFileName
  fromE (ObjectFiles xs) = ListE $ S.toList xs
  toE   (ListE xs) = ObjectFiles $ S.fromList xs

instance SinkableE      ObjectFiles
instance HoistableE     ObjectFiles
instance AlphaEqE       ObjectFiles
instance AlphaHashableE ObjectFiles
instance SubstE Name    ObjectFiles

instance GenericE ModuleEnv where
  type RepE ModuleEnv = ImportStatus
                `PairE` SourceMap
                `PairE` SynthCandidates
                `PairE` ObjectFiles
                `PairE` EffectRow
  fromE (ModuleEnv imports sm sc obj eff) =
    imports `PairE` sm `PairE` sc `PairE` obj `PairE` eff
  toE (imports `PairE` sm `PairE` sc `PairE` obj `PairE` eff) =
    ModuleEnv imports sm sc obj eff

instance SinkableE      ModuleEnv
instance HoistableE     ModuleEnv
instance AlphaEqE       ModuleEnv
instance AlphaHashableE ModuleEnv
instance SubstE Name    ModuleEnv

instance Semigroup (ModuleEnv n) where
  ModuleEnv x1 x2 x3 x4 x5 <> ModuleEnv y1 y2 y3 y4 y5 =
    ModuleEnv (x1<>y1) (x2<>y2) (x3<>y3) (x4<>y4) (x5<>y5)

instance Monoid (ModuleEnv n) where
  mempty = ModuleEnv mempty mempty mempty mempty mempty

instance Semigroup (LoadedModules n) where
  LoadedModules m1 <> LoadedModules m2 = LoadedModules (m2 <> m1)

instance Monoid (LoadedModules n) where
  mempty = LoadedModules mempty

instance HasNameHint ModuleSourceName where
  getNameHint (OrdinaryModule name) = getNameHint name
  getNameHint Prelude = "prelude"
  getNameHint Main = "main"

-- TODO: Can we derive these generically? Or use Show/Read?
--       (These prelude-only names don't have to be pretty.)
builtinNames :: M.Map String PrimName
builtinNames = M.fromList
  [ ("iadd", binOp IAdd), ("isub", binOp ISub)
  , ("imul", binOp IMul), ("fdiv", binOp FDiv)
  , ("fadd", binOp FAdd), ("fsub", binOp FSub)
  , ("fmul", binOp FMul), ("idiv", binOp IDiv)
  , ("irem", binOp IRem)
  , ("fpow", binOp FPow)
  , ("and" , binOp BAnd), ("or"  , binOp BOr ), ("not" , unOp BNot), ("xor", binOp BXor)
  , ("shl" , binOp BShL), ("shr" , binOp BShR)
  , ("ieq" , binOp (ICmp Equal  )), ("feq", binOp (FCmp Equal  ))
  , ("igt" , binOp (ICmp Greater)), ("fgt", binOp (FCmp Greater))
  , ("ilt" , binOp (ICmp Less)),    ("flt", binOp (FCmp Less))
  , ("fneg", unOp  FNeg)
  , ("exp" , unOp  Exp), ("exp2"  , unOp  Exp2)
  , ("log" , unOp Log), ("log2" , unOp Log2 ), ("log10" , unOp Log10)
  , ("sin" , unOp  Sin), ("cos" , unOp Cos)
  , ("tan" , unOp  Tan), ("sqrt", unOp Sqrt)
  , ("floor", unOp Floor), ("ceil", unOp Ceil), ("round", unOp Round)
  , ("log1p", unOp Log1p), ("lgamma", unOp LGamma)
  , ("vfadd", vbinOp FAdd), ("vfsub", vbinOp FSub), ("vfmul", vbinOp FMul)
  , ("idxSetSize"  , OpExpr $ IdxSetSize ())
  , ("unsafeFromOrdinal", OpExpr $ UnsafeFromOrdinal () ())
  , ("toOrdinal"        , OpExpr $ ToOrdinal ())
  , ("sumToVariant"   , OpExpr $ SumToVariant ())
  , ("throwError"     , OpExpr $ ThrowError ())
  , ("throwException" , OpExpr $ ThrowException ())
  , ("ask"        , OpExpr $ PrimEffect () $ MAsk)
  , ("mextend"    , OpExpr $ PrimEffect () $ MExtend (BaseMonoid () ()) ())
  , ("get"        , OpExpr $ PrimEffect () $ MGet)
  , ("put"        , OpExpr $ PrimEffect () $ MPut  ())
  , ("indexRef"   , OpExpr $ IndexRef () ())
  , ("inject"     , OpExpr $ Inject ())
  , ("select"     , OpExpr $ Select () () ())
  , ("while"           , HofExpr $ While ())
  , ("linearize"       , HofExpr $ Linearize ())
  , ("linearTranspose" , HofExpr $ Transpose ())
  , ("runReader"       , HofExpr $ RunReader () ())
  , ("runWriter"       , HofExpr $ RunWriter (BaseMonoid () ()) ())
  , ("runState"        , HofExpr $ RunState  () ())
  , ("runIO"           , HofExpr $ RunIO ())
  , ("catchException"  , HofExpr $ CatchException ())
  , ("tiled"           , HofExpr $ Tile 0 () ())
  , ("tiledd"          , HofExpr $ Tile 1 () ())
  , ("TyKind"    , TCExpr $ TypeKind)
  , ("Float64"   , TCExpr $ BaseType $ Scalar Float64Type)
  , ("Float32"   , TCExpr $ BaseType $ Scalar Float32Type)
  , ("Int64"     , TCExpr $ BaseType $ Scalar Int64Type)
  , ("Int32"     , TCExpr $ BaseType $ Scalar Int32Type)
  , ("Word8"     , TCExpr $ BaseType $ Scalar Word8Type)
  , ("Word32"    , TCExpr $ BaseType $ Scalar Word32Type)
  , ("Word64"    , TCExpr $ BaseType $ Scalar Word64Type)
  , ("Int32Ptr"  , TCExpr $ BaseType $ ptrTy $ Scalar Int32Type)
  , ("Word8Ptr"  , TCExpr $ BaseType $ ptrTy $ Scalar Word8Type)
  , ("Float32Ptr", TCExpr $ BaseType $ ptrTy $ Scalar Float32Type)
  , ("PtrPtr"    , TCExpr $ BaseType $ ptrTy $ ptrTy $ Scalar Word8Type)
  , ("IntRange"  , TCExpr $ IntRange () ())
  , ("Label"     , TCExpr $ LabelType)
  , ("Ref"       , TCExpr $ RefType (Just ()) ())
  , ("PairType"  , TCExpr $ ProdType [(), ()])
  , ("UnitType"  , TCExpr $ ProdType [])
  , ("EffKind"   , TCExpr $ EffectRowKind)
  , ("LabeledRowKind", TCExpr $ LabeledRowKindTC)
  , ("IndexSlice", TCExpr $ IndexSlice () ())
  , ("pair", ConExpr $ ProdCon [(), ()])
  , ("fstRef", OpExpr $ ProjRef 0 ())
  , ("sndRef", OpExpr $ ProjRef 1 ())
  -- TODO: Lift vectors to constructors
  --, ("VectorFloatType",  TCExpr $ BaseType $ Vector FloatType)
  , ("vectorPack", OpExpr $ VectorPack $ replicate vectorWidth ())
  , ("vectorIndex", OpExpr $ VectorIndex () ())
  , ("cast", OpExpr  $ CastOp () ())
  , ("sliceOffset", OpExpr $ SliceOffset () ())
  , ("sliceCurry", OpExpr $ SliceCurry () ())
  , ("alloc", OpExpr $ IOAlloc (Scalar Word8Type) ())
  , ("free" , OpExpr $ IOFree ())
  , ("ptrOffset", OpExpr $ PtrOffset () ())
  , ("ptrLoad"  , OpExpr $ PtrLoad ())
  , ("ptrStore" , OpExpr $ PtrStore () ())
  , ("dataConTag", OpExpr $ DataConTag ())
  , ("toEnum"    , OpExpr $ ToEnum () ())
  , ("outputStreamPtr", OpExpr $ OutputStreamPtr)
  ]
  where
    vbinOp op = OpExpr $ VectorBinOp op () ()
    binOp  op = OpExpr $ ScalarBinOp op () ()
    unOp   op = OpExpr $ ScalarUnOp  op ()
    ptrTy  ty = PtrType (Heap CPU, ty)
