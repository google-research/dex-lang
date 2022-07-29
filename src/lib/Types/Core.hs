-- Copyright 2022 Google LLC
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

module Types.Core (module Types.Core, SymbolicZeros (..)) where

import Control.Applicative
import Control.Monad.Writer.Strict (Writer, execWriter, tell)
import Data.Word
import Data.Maybe
import Data.Functor
import Data.Foldable
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty    as NE
import qualified Data.ByteString       as BS
import qualified Data.Map.Strict       as M
import qualified Data.Set              as S

import GHC.Stack
import GHC.Generics (Generic (..))
import Data.Store (Store (..))

import Name
import Err
import LabeledItems
import Util (FileHash)

import Types.Primitives
import Types.Source
import Types.Imp

-- === core IR ===

data Atom (n::S) =
   Var (AtomName n)
 | Lam (LamExpr n)
 | Pi  (PiType  n)
 | TabLam (TabLamExpr n)
 | TabPi  (TabPiType n)
 | DepPairTy (DepPairType n)
 | DepPair   (Atom n) (Atom n) (DepPairType n)
   -- SourceName is purely for printing
 | DataCon SourceName (DataDefName n) (DataDefParams n) Int [Atom n]
 | TypeCon SourceName (DataDefName n) (DataDefParams n)
 | DictCon (DictExpr n)
 | DictTy  (DictType n)
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
 | DataConRef (DataDefName n) (DataDefParams n) (EmptyAbs (Nest DataConRefBinding) n)
 -- lhs ref, rhs ref abstracted over the eventual value of lhs ref, type
 | DepPairRef (Atom n) (Abs Binder Atom n) (DepPairType n)
 | BoxedRef (Abs (NonDepNest BoxPtr) Atom n)
 -- access a nested member of a binder
 -- XXX: Variable name must not be an alias for another name or for
 -- a statically-known atom. This is because the variable name used
 -- here may also appear in the type of the atom. (We maintain this
 -- invariant during substitution and in Builder.hs.)
 | ProjectElt (NE.NonEmpty Int) (AtomName n)
   deriving (Show, Generic)

data Expr n =
   App (Atom n) (NonEmpty (Atom n))
 | TabApp (Atom n) (NonEmpty (Atom n)) -- TODO: put this in PrimOp?
 | Case (Atom n) [Alt n] (Type n) (EffectRow n)
 | Atom (Atom n)
 | Op  (Op  n)
 | Hof (Hof n)
   deriving (Show, Generic)

data DeclBinding n = DeclBinding LetAnn (Type n) (Expr n)
     deriving (Show, Generic)
data Decl n l = Let (NameBinder AtomNameC n l) (DeclBinding n)
     deriving (Show, Generic)
type Decls = Nest Decl

type AtomName     = Name AtomNameC
type DataDefName  = Name DataDefNameC
type ClassName    = Name ClassNameC
type MethodName   = Name MethodNameC
type InstanceName = Name InstanceNameC
type ModuleName   = Name ModuleNameC
type PtrName      = Name PtrNameC

type AtomNameBinder = NameBinder AtomNameC

type Effect    = EffectP    AtomName
type EffectRow = EffectRowP AtomName
type BaseMonoid n = BaseMonoidP (Atom n)

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
  DataDef :: SourceName -> DataDefBinders n l -> [DataConDef l] -> DataDef n

-- As above, the `SourceName` is just for pretty-printing
data DataConDef n =
  DataConDef SourceName (EmptyAbs (Nest Binder) n)
  deriving (Show, Generic)

data DataDefBinders n l where
  DataDefBinders
    :: Nest Binder n h  -- ordinary params
    -> Nest Binder h l  -- dict params
    -> DataDefBinders n l

data DataDefParams n = DataDefParams [Atom n] [Atom n]  -- ordinary params, dict params
                       deriving (Show, Generic)

-- The Type is the type of the result expression (and thus the type of the
-- block). It's given by querying the result expression's type, and checking
-- that it doesn't have any free names bound by the decls in the block. We store
-- it separately as an optimization, to avoid having to traverse the block.
-- If the decls are empty we can skip the type annotation, because then we can
-- cheaply query the result, and, more importantly, there's no risk of having a
-- type that mentions local variables.
data Block n where
  Block :: BlockAnn n l -> Nest Decl n l -> Atom l -> Block n

data BlockAnn n l where
  BlockAnn :: Type n -> EffectRow n -> BlockAnn n l
  NoBlockAnn :: BlockAnn n n

data LamBinding (n::S) = LamBinding Arrow (Type n)
  deriving (Show, Generic)

data LamBinder (n::S) (l::S) =
  LamBinder (NameBinder AtomNameC n l) (Type n) Arrow (EffectRow l)
  deriving (Show, Generic)

data LamExpr (n::S) where
  LamExpr :: LamBinder n l -> Block l -> LamExpr n

type IxDict = Atom

data IxType (n::S) =
  IxType { ixTypeType :: Type n
         , ixTypeDict :: IxDict n }
  deriving (Show, Generic)

type IxBinder = BinderP AtomNameC IxType

data TabLamExpr (n::S) where
  TabLamExpr :: IxBinder n l -> Block l -> TabLamExpr n

data TabPiType (n::S) where
  TabPiType :: IxBinder n l -> Type l -> TabPiType n

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

type Val  = Atom
type Type = Atom
type Kind = Type

type TC  n = PrimTC  (Atom n)
type Con n = PrimCon (Atom n)
type Op  n = PrimOp  (Atom n)
type Hof n = PrimHof (Atom n)

type AtomSubstVal = SubstVal AtomNameC Atom :: V

data EffectBinder n l where
  EffectBinder :: EffectRow n -> EffectBinder n n

instance GenericB EffectBinder where
  type RepB EffectBinder = LiftB EffectRow
  fromB (EffectBinder effs) = LiftB effs
  toB   (LiftB effs) = EffectBinder effs

data BoxPtr n = BoxPtr (Atom n) (Block n)  -- ptrptr, size
                deriving (Show, Generic)

-- A nest where the annotation of a binder cannot depend on the binders
-- introduced before it. You can think of it as introducing a bunch of
-- names into the scope in parallel, but since safer names only reasons
-- about sequential scope extensions, we encode it differently.
data NonDepNest ann n l = NonDepNest (Nest AtomNameBinder n l) [ann n]
                          deriving (Generic)

-- === type classes ===

data SuperclassBinders n l =
  SuperclassBinders
    { superclassBinders :: Nest AtomNameBinder n l
    , superclassTypes   :: [Type n] }
  deriving (Show, Generic)

data ClassDef (n::S) where
  ClassDef
    :: SourceName
    -> [SourceName]              -- method source names
    -> Nest Binder n1 n2         -- parameters
    ->   SuperclassBinders n2 n3 -- superclasses
    ->   [MethodType n3]         -- method types
    -> ClassDef n1

data InstanceDef (n::S) where
  InstanceDef
    :: ClassName n1
    -> Nest PiBinder n1 n2 -- parameters (types and dictionaries)
    ->   [Type n2]         -- class parameters
    ->   InstanceBody n2
    -> InstanceDef n1

data InstanceBody (n::S) =
  InstanceBody
    [Atom n]   -- superclasses dicts
    [Block n]  -- method definitions
  deriving (Show, Generic)

data MethodType (n::S) =
  MethodType
    [Bool]    -- indicates explicit args
    (Type n)  -- actual method type
 deriving (Show, Generic)

data DictType (n::S) = DictType SourceName (ClassName n) [Type n]
     deriving (Show, Generic)

data DictExpr (n::S) =
   InstanceDict (InstanceName n) [Atom n]
   -- We use NonEmpty because givens without args can be represented using `Var`.
 | InstantiatedGiven (Atom n) (NonEmpty (Atom n))
 | SuperclassProj (Atom n) Int  -- (could instantiate here too, but we don't need it for now)
   -- Special case for `Ix (Fin n)`  (TODO: a more general mechanism for built-in classes and instances)
 | IxFin (Atom n)
   deriving (Show, Generic)

-- TODO: Use an IntMap
newtype CustomRules (n::S) = CustomRules { customRulesMap :: M.Map (AtomName n) (AtomRules n) }
                             deriving (Semigroup, Monoid, Store)
data AtomRules (n::S) = CustomLinearize Int SymbolicZeros (Atom n)  -- number of implicit args, linearization function
                        deriving (Generic)

-- === envs and modules ===

-- `ModuleEnv` contains data that only makes sense in the context of evaluating
-- a particular module. `TopEnv` contains everything that makes sense "between"
-- evaluating modules.
data Env n = Env
  { topEnv    :: {-# UNPACK #-} TopEnv n
  , moduleEnv :: {-# UNPACK #-} ModuleEnv n }
  deriving (Generic)

data TopEnv (n::S) = TopEnv
  { envDefs  :: RecSubst Binding n
  , envCustomRules :: CustomRules n
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

data TopEnvFrag n l = TopEnvFrag (EnvFrag n l) (PartialTopEnvFrag l)

-- This is really the type of updates to `Env`. We should probably change the
-- names to reflect that.
data PartialTopEnvFrag n = PartialTopEnvFrag
  { fragCache           :: Cache n
  , fragCustomRules     :: CustomRules n
  , fragLoadedModules   :: LoadedModules n
  , fragLocalModuleEnv  :: ModuleEnv n }

-- TODO: we could add a lot more structure for querying by dict type, caching, etc.
-- TODO: make these `Name n` instead of `Atom n` so they're usable as cache keys.
data SynthCandidates n = SynthCandidates
  { lambdaDicts       :: [AtomName n]
  , instanceDicts     :: M.Map (ClassName n) [InstanceName n] }
  deriving (Show, Generic)

emptyImportStatus :: ImportStatus n
emptyImportStatus = ImportStatus mempty mempty

-- TODO: figure out the additional top-level context we need -- backend, other
-- compiler flags etc. We can have a map from those to this.
data Cache (n::S) = Cache
  { specializationCache :: EMap SpecializationSpec AtomName n
  , impCache  :: EMap AtomName ImpFunName n
  , objCache  :: EMap ImpFunName CFun n
    -- This is memoizing `parseAndGetDeps :: Text -> [ModuleSourceName]`. But we
    -- only want to store one entry per module name as a simple cache eviction
    -- policy, so we store it keyed on the module name, with the text hash for
    -- the validity check.
  , parsedDeps :: M.Map ModuleSourceName (FileHash, [ModuleSourceName])
  , moduleEvaluations :: M.Map ModuleSourceName ((FileHash, [ModuleName n]), ModuleName n)
  } deriving (Show, Generic)

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

-- === bindings - static information we carry about a lexical scope ===

-- TODO: consider making this an open union via a typeable-like class
data Binding (c::C) (n::S) where
  AtomNameBinding   :: AtomBinding n                  -> Binding AtomNameC       n
  DataDefBinding    :: DataDef n                      -> Binding DataDefNameC    n
  TyConBinding      :: DataDefName n        -> Atom n -> Binding TyConNameC      n
  DataConBinding    :: DataDefName n -> Int -> Atom n -> Binding DataConNameC    n
  ClassBinding      :: ClassDef n                     -> Binding ClassNameC      n
  InstanceBinding   :: InstanceDef n                  -> Binding InstanceNameC   n
  MethodBinding     :: Name ClassNameC n -> Int -> Atom n -> Binding MethodNameC     n
  ImpFunBinding     :: ImpFunction n                  -> Binding ImpFunNameC     n
  ObjectFileBinding :: ObjectFile n                   -> Binding ObjectFileNameC n
  ModuleBinding     :: Module n                       -> Binding ModuleNameC     n
  PtrBinding        :: PtrLitVal                      -> Binding PtrNameC        n
deriving instance Show (Binding c n)

data AtomBinding (n::S) =
   LetBound    (DeclBinding   n)
 | LamBound    (LamBinding    n)
 | PiBound     (PiBinding     n)
 | IxBound     (IxType        n)
 | MiscBound   (Type          n)
 | SolverBound (SolverBinding n)
 | PtrLitBound PtrType (PtrName n)
 | TopFunBound (NaryPiType n) (TopFunBinding n)
   deriving (Show, Generic)

data TopFunBinding (n::S) =
   UnspecializedTopFun Int (Atom n)    -- num specialization args, definition
 | SpecializedTopFun (SpecializationSpec n) -- Original (unspecialized) function, specialization args
 | SimpTopFun          (NaryLamExpr n)
 | FFITopFun           (ImpFunName n)
   deriving (Show, Generic)

-- TODO: extend with AD-oriented specializations, backend-specific specializations etc.
data SpecializationSpec (n::S) =
  -- The additional binders are for "data" components of the specialization types, like
  -- `n` in `Fin n`.
  AppSpecialization (AtomName n) (Abs (Nest Binder) (ListE Type) n)
  deriving (Show, Generic)

atomBindingType :: Binding AtomNameC n -> Type n
atomBindingType (AtomNameBinding b) = case b of
  LetBound    (DeclBinding _ ty _) -> ty
  LamBound    (LamBinding  _ ty)   -> ty
  PiBound     (PiBinding   _ ty)   -> ty
  IxBound     (IxType ty _)        -> ty
  MiscBound   ty                   -> ty
  SolverBound (InfVarBound ty _)   -> ty
  SolverBound (SkolemBound ty)     -> ty
  PtrLitBound ty _ -> BaseTy (PtrType ty)
  TopFunBound ty _ -> naryPiTypeAsType ty

-- TODO: Move this to Inference!
data SolverBinding (n::S) =
   InfVarBound (Type n) SrcPosCtx
 | SkolemBound (Type n)
   deriving (Show, Generic)

data EnvFrag (n::S) (l::S) =
  EnvFrag (RecSubstFrag Binding n l) (Maybe (EffectRow l))

instance HasScope Env where
  toScope = toScope . envDefs . topEnv

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
  {-# INLINE emptyOutFrag #-}
  catOutFrags _ frag1 frag2 = catEnvFrags frag1 frag2
  {-# INLINE catOutFrags #-}

instance OutMap Env where
  emptyOutMap =
    Env (TopEnv (RecSubst emptyInFrag) mempty mempty emptyLoadedModules)
        emptyModuleEnv
  {-# INLINE emptyOutMap #-}

instance ExtOutMap Env (RecSubstFrag Binding)  where
  -- TODO: We might want to reorganize this struct to make this
  -- do less explicit sinking etc. It's a hot operation!
  extendOutMap (Env (TopEnv defs rules cache loaded)
                    (ModuleEnv imports sm scs objs effs)) frag =
    withExtEvidence frag $ Env
      (TopEnv
        (defs  `extendRecSubst` frag)
        (sink rules)
        (sink cache)
        (sink loaded))
      (ModuleEnv
        (sink imports)
        (sink sm)
        (sink scs <> bindingsFragToSynthCandidates (EnvFrag frag Nothing))
        (sink objs)
        (sink effs))
  {-# INLINE extendOutMap #-}

instance ExtOutMap Env EnvFrag where
  extendOutMap = extendEnv
  {-# INLINE extendOutMap #-}

extendEnv :: Distinct l => Env n -> EnvFrag n l -> Env l
extendEnv env (EnvFrag newEnv maybeNewEff) = do
  case extendOutMap env newEnv of
    Env envTop (ModuleEnv imports sm scs obs oldEff) -> do
      let newEff = case maybeNewEff of
                     Nothing  -> sink oldEff
                     Just eff -> eff
      Env envTop (ModuleEnv imports sm scs obs newEff)
{-# NOINLINE [1] extendEnv #-}

bindingsFragToSynthCandidates :: Distinct l => EnvFrag n l -> SynthCandidates l
bindingsFragToSynthCandidates (EnvFrag (RecSubstFrag frag) _) =
  execWriter $ go $ toSubstPairs frag
  where
    go :: Distinct l
       => Nest (SubstPair Binding l) n l -> Writer (SynthCandidates l) ()
    go nest = case nest of
      Empty -> return ()
      Nest (SubstPair b binding) rest -> withExtEvidence rest do
        case binding of
           AtomNameBinding (LamBound (LamBinding ClassArrow _)) -> do
             tell $ sink (SynthCandidates [binderName b] mempty)
           AtomNameBinding (PiBound (PiBinding ClassArrow _)) -> do
             tell $ sink (SynthCandidates [binderName b] mempty)
           _ -> return ()
        go rest

-- WARNING: This is not exactly faithful, because NaryPiType erases intermediate arrows!
naryPiTypeAsType :: NaryPiType n -> Type n
naryPiTypeAsType (NaryPiType (NonEmptyNest b bs) effs resultTy) = case bs of
  Empty -> Pi $ PiType b effs resultTy
  Nest b' rest -> Pi $ PiType b Pure restTy
    where restTy = naryPiTypeAsType $ NaryPiType (NonEmptyNest b' rest) effs resultTy

-- WARNING: This is not exactly faithful, because NaryLamExpr erases intermediate arrows!
naryLamExprAsAtom :: NaryLamExpr n -> Atom n
naryLamExprAsAtom (NaryLamExpr (NonEmptyNest (b:>ty) bs) effs body) = case bs of
  Empty -> Lam $ LamExpr (LamBinder b ty PlainArrow effs) body
  Nest b' rest -> Lam $ LamExpr (LamBinder b ty PlainArrow Pure) (AtomicBlock restBody)
    where restBody = naryLamExprAsAtom $ NaryLamExpr (NonEmptyNest b' rest) effs body

-- === BindsOneAtomName ===

-- We're really just defining this so we can have a polymorphic `binderType`.
-- But maybe we don't need one. Or maybe we can make one using just
-- `BindsOneName b AtomNameC` and `BindsEnv b`.
class BindsOneName b AtomNameC => BindsOneAtomName (b::B) where
  binderType :: b n l -> Type n

bindersTypes :: (Distinct l, ProvesExt b, BindsNames b, BindsOneAtomName b)
             => Nest b n l -> [Type l]
bindersTypes Empty = []
bindersTypes n@(Nest b bs) = ty : bindersTypes bs
  where ty = withExtEvidence n $ sink (binderType b)

instance BindsOneAtomName (BinderP AtomNameC Type) where
  binderType (_ :> ty) = ty

instance BindsOneAtomName LamBinder where
  binderType (LamBinder _ ty _ _) = ty

instance BindsOneAtomName PiBinder where
  binderType (PiBinder _ ty _) = ty

instance BindsOneAtomName IxBinder where
  binderType (_ :> IxType ty _) = ty

-- === ToBinding ===

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

instance ToBinding IxType AtomNameC where
  toBinding = toBinding . IxBound

-- We don't need this for now and it seems a little annoying to implement.
-- If you ever hit this, add a Type n to BoxPtr and return it here.
instance ToBinding BoxPtr AtomNameC where
  toBinding = error "not implemented!"

instance (ToBinding e1 c, ToBinding e2 c) => ToBinding (EitherE e1 e2) c where
  toBinding (LeftE  e) = toBinding e
  toBinding (RightE e) = toBinding e

-- === HasArgType ===

class HasArgType (e::E) where
  argType :: e n -> Type n

instance HasArgType PiType where
  argType (PiType (PiBinder _ ty _) _ _) = ty

instance HasArgType TabPiType where
  argType (TabPiType (_:>IxType ty _) _) = ty

instance HasArgType LamExpr where
  argType (LamExpr (LamBinder _ ty _ _) _) = ty

instance HasArgType TabLamExpr where
  argType (TabLamExpr (_:>IxType ty _) _) = ty

-- === Pattern synonyms ===

-- Type used to represent indices and sizes at run-time
pattern IdxRepTy :: Type n
pattern IdxRepTy = TC (BaseType (Scalar Word32Type))

pattern IdxRepVal :: Word32 -> Atom n
pattern IdxRepVal x = Con (Lit (Word32Lit x))

pattern IIdxRepVal :: Word32 -> IExpr n
pattern IIdxRepVal x = ILit (Word32Lit x)

pattern IIdxRepTy :: IType
pattern IIdxRepTy = Scalar Word32Type

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

pattern TabTy :: IxBinder n l -> Type l -> Type n
pattern TabTy b body = TabPi (TabPiType b body)

pattern TabVal :: IxBinder n l -> Block l -> Atom n
pattern TabVal b body = TabLam (TabLamExpr b body)

pattern TyKind :: Kind n
pattern TyKind = TC TypeKind

pattern EffKind :: Kind n
pattern EffKind = TC EffectRowKind

pattern LabeledRowKind :: Kind n
pattern LabeledRowKind = TC LabeledRowKindTC

pattern FinConst :: Word32 -> Type n
pattern FinConst n = TC (Fin (IdxRepVal n))

pattern BinaryFunTy :: PiBinder n l1 -> PiBinder l1 l2 -> EffectRow l2 -> Type l2 -> Type n
pattern BinaryFunTy b1 b2 eff ty <- Pi (PiType b1 Pure (Pi (PiType b2 eff ty)))

pattern AtomicBlock :: Atom n -> Block n
pattern AtomicBlock atom <- Block _ Empty atom
  where AtomicBlock atom = Block NoBlockAnn Empty atom

pattern BinaryLamExpr :: LamBinder n l1 -> LamBinder l1 l2 -> Block l2 -> LamExpr n
pattern BinaryLamExpr b1 b2 body = LamExpr b1 (AtomicBlock (Lam (LamExpr b2 body)))

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

-- === Typeclass instances for Name and other Haskell libraries ===

instance GenericE AtomRules where
  type RepE AtomRules = (LiftE (Int, SymbolicZeros)) `PairE` Atom
  fromE (CustomLinearize ni sz a) = LiftE (ni, sz) `PairE` a
  toE (LiftE (ni, sz) `PairE` a) = CustomLinearize ni sz a
instance SinkableE AtomRules
instance HoistableE AtomRules
instance AlphaEqE AtomRules
instance SubstE Name AtomRules

instance GenericE CustomRules where
  type RepE CustomRules = ListE (PairE AtomName AtomRules)
  fromE (CustomRules m) = ListE $ toPairE <$> M.toList m
  toE (ListE l) = CustomRules $ M.fromList $ fromPairE <$> l
instance SinkableE CustomRules
instance HoistableE CustomRules
instance AlphaEqE CustomRules
instance SubstE Name CustomRules

instance SinkableB EffectBinder
instance HoistableB EffectBinder
instance ProvesExt  EffectBinder
instance BindsNames EffectBinder
instance SubstB Name EffectBinder

instance GenericB DataDefBinders where
  type RepB DataDefBinders = PairB (Nest Binder) (Nest Binder)
  fromB (DataDefBinders bs1 bs2) = PairB bs1 bs2
  {-# INLINE fromB #-}
  toB   (PairB bs1 bs2) = DataDefBinders bs1 bs2
  {-# INLINE toB #-}

instance SinkableB   DataDefBinders
instance HoistableB  DataDefBinders
instance ProvesExt   DataDefBinders
instance BindsNames  DataDefBinders
instance SubstB Name DataDefBinders
instance SubstB AtomSubstVal DataDefBinders
instance AlphaHashableB DataDefBinders
instance AlphaEqB       DataDefBinders
deriving instance Show (DataDefBinders n l)
deriving via WrapB DataDefBinders n l instance Generic (DataDefBinders n l)

instance GenericE DataDefParams where
  type RepE DataDefParams = PairE (ListE Atom) (ListE Atom)
  fromE (DataDefParams xs ys) = PairE (ListE xs) (ListE ys)
  {-# INLINE fromE #-}
  toE   (PairE (ListE xs) (ListE ys)) = DataDefParams xs ys
  {-# INLINE toE #-}

-- We ignore the dictionary parameters because we assume coherence
instance AlphaEqE DataDefParams where
  alphaEqE (DataDefParams params _) (DataDefParams params' _) =
    alphaEqE (ListE params) (ListE params')

instance AlphaHashableE DataDefParams where
  hashWithSaltE env salt (DataDefParams params _) =
    hashWithSaltE env salt (ListE params)

instance SinkableE           DataDefParams
instance HoistableE          DataDefParams
instance SubstE Name         DataDefParams
instance SubstE AtomSubstVal DataDefParams

instance GenericE DataDef where
  type RepE DataDef = PairE (LiftE SourceName) (Abs DataDefBinders (ListE DataConDef))
  fromE (DataDef sourceName bs cons) = PairE (LiftE sourceName) (Abs bs (ListE cons))
  {-# INLINE fromE #-}
  toE   (PairE (LiftE sourceName) (Abs bs (ListE cons))) = DataDef sourceName bs cons
  {-# INLINE toE #-}

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
  {-# INLINE fromE #-}
  toE   (PairE (LiftE name) ab) = DataConDef name ab
  {-# INLINE toE #-}
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
  {-# INLINE fromE #-}
  toE = \case
    Case0 (ExtLabeledItemsE (Ext items _)) -> StaticFields items
    Case1 (n `PairE` t) -> DynField n t
    Case2 n             -> DynFields n
    _ -> error "unreachable"
  {-# INLINE toE #-}
instance SinkableE      FieldRowElem
instance HoistableE     FieldRowElem
instance SubstE Name    FieldRowElem
instance AlphaEqE       FieldRowElem
instance AlphaHashableE FieldRowElem

instance GenericE FieldRowElems where
  type RepE FieldRowElems = ListE FieldRowElem
  fromE = ListE . fromFieldRowElems
  {-# INLINE fromE #-}
  toE = fieldRowElemsFromList . fromListE
  {-# INLINE toE #-}
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
   deriving Show

instance GenericE Atom where
  -- As tempting as it might be to reorder cases here, the current permutation
  -- was chosen as to make GHC inliner confident enough to simplify through
  -- toE/fromE entirely. If you wish to modify the order, please consuly the
  -- GHC Core dump to make sure you haven't regressed this optimization.
  type RepE Atom =
      EitherE6
              (EitherE2
                   -- We isolate those few cases (and reorder them
                   -- compared to the data definition) because they need special
                   -- handling when you substitute with atoms. The rest just act
                   -- like containers
  {- Var -}        AtomName
  {- ProjectElt -} ( LiftE (NE.NonEmpty Int) `PairE` AtomName )
            ) (EitherE4
  {- Lam -}        LamExpr
  {- Pi -}         PiType
  {- TabLam -}     TabLamExpr
  {- TabPi -}      TabPiType
            ) (EitherE6
  {- DepPairTy -}  DepPairType
  {- DepPair -}    ( Atom `PairE` Atom `PairE` DepPairType)
  {- DataCon -}    ( LiftE (SourceName, Int)   `PairE`
                     DataDefName               `PairE`
                     DataDefParams               `PairE`
                     ListE Atom )
  {- TypeCon -}    ( LiftE SourceName `PairE` DataDefName `PairE` DataDefParams)
  {- DictCon  -}   DictExpr
  {- DictTy  -}    DictType
            ) (EitherE5
  {- LabeledRow -} ( FieldRowElems )
  {- Record -}     ( ComposeE LabeledItems Atom )
  {- RecordTy -}   ( FieldRowElems )
  {- Variant -}    ( ExtLabeledItemsE Type AtomName `PairE`
                     LiftE (Label, Int) `PairE` Atom )
  {- VariantTy -}  ( ExtLabeledItemsE Type AtomName )
            ) (EitherE4
  {- Con -}        (ComposeE PrimCon Atom)
  {- TC -}         (ComposeE PrimTC  Atom)
  {- Eff -}        EffectRow
  {- ACase -}      ( Atom `PairE` ListE (AltP Atom) `PairE` Type )
            ) (EitherE3
  {- BoxedRef -}   ( Abs (NonDepNest BoxPtr) Atom )
  {- DataConRef -} ( DataDefName                    `PairE`
                     DataDefParams                  `PairE`
                     EmptyAbs (Nest DataConRefBinding) )
  {- DepPairRef -} ( Atom `PairE` Abs Binder Atom `PairE` DepPairType))

  fromE atom = case atom of
    Var v -> Case0 (Case0 v)
    ProjectElt idxs x -> Case0 (Case1 (PairE (LiftE idxs) x))
    Lam lamExpr -> Case1 (Case0 lamExpr)
    Pi  piExpr  -> Case1 (Case1 piExpr)
    TabLam lamExpr -> Case1 (Case2 lamExpr)
    TabPi  piExpr  -> Case1 (Case3 piExpr)
    DepPairTy ty -> Case2 (Case0 ty)
    DepPair l r ty -> Case2 (Case1 $ l `PairE` r `PairE` ty)
    DataCon printName defName params con args -> Case2 $ Case2 $
      LiftE (printName, con) `PairE`
            defName          `PairE`
            params           `PairE`
      ListE args
    TypeCon sourceName defName params -> Case2 $ Case3 $
      LiftE sourceName `PairE` defName `PairE` params
    DictCon d -> Case2 $ Case4 d
    DictTy  d -> Case2 $ Case5 d
    LabeledRow elems    -> Case3 $ Case0 $ elems
    Record items        -> Case3 $ Case1 $ ComposeE items
    RecordTy elems -> Case3 $ Case2 elems
    Variant extItems l con payload -> Case3 $ Case3 $
      ExtLabeledItemsE extItems `PairE` LiftE (l, con) `PairE` payload
    VariantTy extItems  -> Case3 $ Case4 $ ExtLabeledItemsE extItems
    Con con -> Case4 $ Case0 $ ComposeE con
    TC  con -> Case4 $ Case1 $ ComposeE con
    Eff effs -> Case4 $ Case2 $ effs
    ACase scrut alts ty -> Case4 $ Case3 $ scrut `PairE` ListE alts `PairE` ty
    BoxedRef ab -> Case5 $ Case0 ab
    DataConRef defName params bs -> Case5 $ Case1 $ defName `PairE` params `PairE` bs
    DepPairRef lhs rhs ty ->
      Case5 $ Case2 $ lhs `PairE` rhs `PairE` ty
  {-# INLINE fromE #-}

  toE atom = case atom of
    Case0 val -> case val of
      Case0 v -> Var v
      Case1 (PairE (LiftE idxs) x) -> ProjectElt idxs x
      _ -> error "impossible"
    Case1 val -> case val of
      Case0 lamExpr -> Lam lamExpr
      Case1 piExpr  -> Pi  piExpr
      Case2 lamExpr -> TabLam lamExpr
      Case3 piExpr  -> TabPi  piExpr
      _ -> error "impossible"
    Case2 val -> case val of
      Case0 ty      -> DepPairTy ty
      Case1 (l `PairE` r `PairE` ty) -> DepPair l r ty
      Case2 ( LiftE (printName, con) `PairE`
                    defName          `PairE`
                    params           `PairE`
              ListE args ) ->
        DataCon printName defName params con args
      Case3 (LiftE sourceName `PairE` defName `PairE` params) ->
        TypeCon sourceName defName params
      Case4 d -> DictCon d
      Case5 d -> DictTy  d
      _ -> error "impossible"
    Case3 val -> case val of
      Case0 elems -> LabeledRow elems
      Case1 (ComposeE items) -> Record items
      Case2 elems -> RecordTy elems
      Case3 ( (ExtLabeledItemsE extItems) `PairE`
              LiftE (l, con)              `PairE`
              payload) -> Variant extItems l con payload
      Case4 (ExtLabeledItemsE extItems) -> VariantTy extItems
      _ -> error "impossible"
    Case4 val -> case val of
      Case0 (ComposeE con) -> Con con
      Case1 (ComposeE con) -> TC con
      Case2 effs -> Eff effs
      Case3 (scrut `PairE` ListE alts `PairE` ty) -> ACase scrut alts ty
      _ -> error "impossible"
    Case5 val -> case val of
      Case0 ab -> BoxedRef ab
      Case1 (defName `PairE` params `PairE` bs) -> DataConRef defName params bs
      Case2 (lhs `PairE` rhs `PairE` ty) -> DepPairRef lhs rhs ty
      _ -> error "impossible"
    _ -> error "impossible"
  {-# INLINE toE #-}

instance SinkableE   Atom
instance HoistableE  Atom
instance AlphaEqE    Atom
instance AlphaHashableE Atom
instance SubstE Name Atom

-- TODO: special handling of ACase too
instance SubstE AtomSubstVal Atom where
  substE (scope, env) atom = case fromE atom of
    Case0 specialCase -> case specialCase of
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
    Case1 rest -> (toE . Case1) $ substE (scope, env) rest
    Case2 rest -> (toE . Case2) $ substE (scope, env) rest
    Case3 rest -> (toE . Case3) $ substE (scope, env) rest
    Case4 rest -> (toE . Case4) $ substE (scope, env) rest
    Case5 rest -> (toE . Case5) $ substE (scope, env) rest
    Case6 rest -> (toE . Case6) $ substE (scope, env) rest
    Case7 rest -> (toE . Case7) $ substE (scope, env) rest

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

instance GenericE Expr where
  type RepE Expr =
     EitherE6
        (Atom `PairE` Atom `PairE` ListE Atom)
        (Atom `PairE` Atom `PairE` ListE Atom)
        (Atom `PairE` ListE Alt `PairE` Type `PairE` EffectRow)
        (Atom)
        (ComposeE PrimOp Atom)
        (ComposeE PrimHof Atom)
  fromE = \case
    App    f (x:|xs)  -> Case0 (f `PairE` x `PairE` ListE xs)
    TabApp f (x:|xs)  -> Case1 (f `PairE` x `PairE` ListE xs)
    Case e alts ty eff -> Case2 (e `PairE` ListE alts `PairE` ty `PairE` eff)
    Atom x         -> Case3 (x)
    Op op          -> Case4 (ComposeE op)
    Hof hof        -> Case5 (ComposeE hof)
  {-# INLINE fromE #-}
  toE = \case
    Case0 (f `PairE` x `PairE` ListE xs)    -> App    f (x:|xs)
    Case1 (f `PairE` x `PairE` ListE xs)    -> TabApp f (x:|xs)
    Case2 (e `PairE` ListE alts `PairE` ty `PairE` eff) -> Case e alts ty eff
    Case3 (x)                               -> Atom x
    Case4 (ComposeE op)                     -> Op op
    Case5 (ComposeE hof)                    -> Hof hof
    _ -> error "impossible"
  {-# INLINE toE #-}

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
  {-# INLINE fromE #-}
  toE (LeftE  (ComposeE items          )) = ExtLabeledItemsE (Ext items Nothing)
  toE (RightE (ComposeE items `PairE` t)) = ExtLabeledItemsE (Ext items (Just t))
  {-# INLINE toE #-}

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
  type RepE Block = PairE (MaybeE (PairE Type EffectRow)) (Abs (Nest Decl) Atom)
  fromE (Block (BlockAnn ty effs) decls result) = PairE (JustE (PairE ty effs)) (Abs decls result)
  fromE (Block NoBlockAnn Empty result) = PairE NothingE (Abs Empty result)
  fromE _ = error "impossible"
  {-# INLINE fromE #-}
  toE   (PairE (JustE (PairE ty effs)) (Abs decls result)) = Block (BlockAnn ty effs) decls result
  toE   (PairE NothingE (Abs Empty result)) = Block NoBlockAnn Empty result
  toE   _ = error "impossible"
  {-# INLINE toE #-}

deriving instance Show (BlockAnn n l)

instance SinkableE Block
instance HoistableE  Block
instance AlphaEqE Block
instance AlphaHashableE Block
instance SubstE Name Block
instance SubstE AtomSubstVal Block
deriving instance Show (Block n)
deriving via WrapE Block n instance Generic (Block n)

instance GenericE BoxPtr where
  type RepE BoxPtr = Atom `PairE` Block
  fromE (BoxPtr p s) = p `PairE` s
  {-# INLINE fromE #-}
  toE (p `PairE` s) = BoxPtr p s
  {-# INLINE toE #-}
instance SinkableE BoxPtr
instance HoistableE BoxPtr
instance AlphaEqE BoxPtr
instance AlphaHashableE BoxPtr
instance SubstE Name BoxPtr
instance SubstE AtomSubstVal BoxPtr

instance GenericB (NonDepNest ann) where
  type RepB (NonDepNest ann) = (LiftB (ListE ann)) `PairB` Nest AtomNameBinder
  fromB (NonDepNest bs anns) = LiftB (ListE anns) `PairB` bs
  {-# INLINE fromB #-}
  toB (LiftB (ListE anns) `PairB` bs) = NonDepNest bs anns
  {-# INLINE toB #-}
instance ProvesExt (NonDepNest ann)
instance BindsNames (NonDepNest ann)
instance SinkableE ann => SinkableB (NonDepNest ann)
instance HoistableE ann => HoistableB (NonDepNest ann)
instance (SubstE Name ann, SinkableE ann) => SubstB Name (NonDepNest ann)
instance (SubstE AtomSubstVal ann, SinkableE ann) => SubstB AtomSubstVal (NonDepNest ann)
instance AlphaEqE ann => AlphaEqB (NonDepNest ann)
instance AlphaHashableE ann => AlphaHashableB (NonDepNest ann)
deriving instance (Show (ann n)) => Show (NonDepNest ann n l)

instance GenericB SuperclassBinders where
  type RepB SuperclassBinders = PairB (LiftB (ListE Type)) (Nest AtomNameBinder)
  fromB (SuperclassBinders bs tys) = PairB (LiftB (ListE tys)) bs
  toB   (PairB (LiftB (ListE tys)) bs) = SuperclassBinders bs tys

instance BindsNameList SuperclassBinders AtomNameC where
  bindNameList (SuperclassBinders bs _) xs = bindNameList bs xs

instance ProvesExt  SuperclassBinders
instance BindsNames SuperclassBinders
instance SinkableB SuperclassBinders
instance HoistableB  SuperclassBinders
instance SubstB Name SuperclassBinders
instance SubstB AtomSubstVal SuperclassBinders
instance AlphaEqB SuperclassBinders
instance AlphaHashableB SuperclassBinders

instance GenericE ClassDef where
  type RepE ClassDef =
    LiftE (SourceName, [SourceName])
     `PairE` Abs (Nest Binder) (Abs SuperclassBinders (ListE MethodType))
  fromE (ClassDef name names b scs tys) =
    LiftE (name, names) `PairE` Abs b (Abs scs (ListE tys))
  {-# INLINE fromE #-}
  toE (LiftE (name, names) `PairE` Abs b (Abs scs (ListE tys))) =
    ClassDef name names b scs tys
  {-# INLINE toE #-}

instance SinkableE ClassDef
instance HoistableE  ClassDef
instance AlphaEqE ClassDef
instance AlphaHashableE ClassDef
instance SubstE Name ClassDef
instance SubstE AtomSubstVal ClassDef
deriving instance Show (ClassDef n)
deriving via WrapE ClassDef n instance Generic (ClassDef n)

instance GenericE InstanceDef where
  type RepE InstanceDef =
    ClassName `PairE` Abs (Nest PiBinder) (ListE Type `PairE` InstanceBody)
  fromE (InstanceDef name bs params body) =
    name `PairE` Abs bs (ListE params `PairE` body)
  toE (name `PairE` Abs bs (ListE params `PairE` body)) =
    InstanceDef name bs params body

instance SinkableE InstanceDef
instance HoistableE  InstanceDef
instance AlphaEqE InstanceDef
instance AlphaHashableE InstanceDef
instance SubstE Name InstanceDef
instance SubstE AtomSubstVal InstanceDef
deriving instance Show (InstanceDef n)
deriving via WrapE InstanceDef n instance Generic (InstanceDef n)

instance GenericE InstanceBody where
  type RepE InstanceBody = ListE Atom `PairE` ListE Block
  fromE (InstanceBody scs methods) = ListE scs `PairE` ListE methods
  toE   (ListE scs `PairE` ListE methods) = InstanceBody scs methods

instance SinkableE InstanceBody
instance HoistableE  InstanceBody
instance AlphaEqE InstanceBody
instance AlphaHashableE InstanceBody
instance SubstE Name InstanceBody
instance SubstE AtomSubstVal InstanceBody

instance GenericE MethodType where
  type RepE MethodType = PairE (LiftE [Bool]) Type
  fromE (MethodType explicit ty) = PairE (LiftE explicit) ty
  toE   (PairE (LiftE explicit) ty) = MethodType explicit ty

instance SinkableE MethodType
instance HoistableE  MethodType
instance AlphaEqE MethodType
instance AlphaHashableE MethodType
instance SubstE Name MethodType
instance SubstE AtomSubstVal MethodType

instance GenericE DictType where
  type RepE DictType = LiftE SourceName `PairE` ClassName `PairE` ListE Type
  fromE (DictType sourceName className params) =
    LiftE sourceName `PairE` className `PairE` ListE params
  toE (LiftE sourceName `PairE` className `PairE` ListE params) =
    DictType sourceName className params

instance SinkableE           DictType
instance HoistableE          DictType
instance AlphaEqE            DictType
instance AlphaHashableE      DictType
instance SubstE Name         DictType
instance SubstE AtomSubstVal DictType

instance GenericE DictExpr where
  type RepE DictExpr =
    EitherE4
 {- InstanceDict -}      (PairE InstanceName (ListE Atom))
 {- InstantiatedGiven -} (PairE Atom (ListE Atom))
 {- SuperclassProj -}    (PairE Atom (LiftE Int))
 {- IxFin -}             (Atom)
  fromE d = case d of
    InstanceDict v args -> Case0 $ PairE v (ListE args)
    InstantiatedGiven given (arg:|args) -> Case1 $ PairE given (ListE (arg:args))
    SuperclassProj x i -> Case2 (PairE x (LiftE i))
    IxFin x            -> Case3 x
  toE d = case d of
    Case0 (PairE v (ListE args)) -> InstanceDict v args
    Case1 (PairE given (ListE ~(arg:args))) -> InstantiatedGiven given (arg:|args)
    Case2 (PairE x (LiftE i)) -> SuperclassProj x i
    Case3 x -> IxFin x
    _ -> error "impossible"

instance SinkableE           DictExpr
instance HoistableE          DictExpr
instance AlphaEqE            DictExpr
instance AlphaHashableE      DictExpr
instance SubstE Name         DictExpr
instance SubstE AtomSubstVal DictExpr

instance GenericE Cache where
  type RepE Cache =
            EMap SpecializationSpec AtomName
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
  {-# INLINE fromE #-}
  toE   (x `PairE` y `PairE` z `PairE` LiftE parseCache `PairE` ListE evalCache) =
    Cache x y z parseCache
      (M.fromList
       [(sourceName, ((hashVal, deps), result))
       | LiftE sourceName `PairE` LiftE hashVal `PairE` ListE deps `PairE` result
          <- evalCache])
  {-# INLINE toE #-}

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

instance BindsAtMostOneName LamBinder AtomNameC where
  LamBinder b _ _ _ @> x = b @> x

instance BindsOneName LamBinder AtomNameC where
  binderName (LamBinder b _ _ _) = binderName b

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
  {-# INLINE fromE #-}
  toE   (PairE (LiftE arr) ty) = LamBinding arr ty
  {-# INLINE toE #-}

instance SinkableE LamBinding
instance HoistableE  LamBinding
instance SubstE Name LamBinding
instance SubstE AtomSubstVal LamBinding
instance AlphaEqE LamBinding
instance AlphaHashableE LamBinding

instance GenericE LamExpr where
  type RepE LamExpr = Abs LamBinder Block
  fromE (LamExpr b block) = Abs b block
  {-# INLINE fromE #-}
  toE   (Abs b block) = LamExpr b block
  {-# INLINE toE #-}

instance SinkableE LamExpr
instance HoistableE  LamExpr
instance AlphaEqE LamExpr
instance AlphaHashableE LamExpr
instance SubstE Name LamExpr
instance SubstE AtomSubstVal LamExpr
deriving instance Show (LamExpr n)
deriving via WrapE LamExpr n instance Generic (LamExpr n)

instance GenericE TabLamExpr where
  type RepE TabLamExpr = Abs IxBinder Block
  fromE (TabLamExpr b block) = Abs b block
  {-# INLINE fromE #-}
  toE   (Abs b block) = TabLamExpr b block
  {-# INLINE toE #-}

instance SinkableE TabLamExpr
instance HoistableE  TabLamExpr
instance AlphaEqE TabLamExpr
instance AlphaHashableE TabLamExpr
instance SubstE Name TabLamExpr
instance SubstE AtomSubstVal TabLamExpr
deriving instance Show (TabLamExpr n)
deriving via WrapE TabLamExpr n instance Generic (TabLamExpr n)


instance GenericE PiBinding where
  type RepE PiBinding = PairE (LiftE Arrow) Type
  fromE (PiBinding arr ty) = PairE (LiftE arr) ty
  {-# INLINE fromE #-}
  toE   (PairE (LiftE arr) ty) = PiBinding arr ty
  {-# INLINE toE #-}

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
  {-# INLINE fromE #-}
  toE   (Abs b (PairE eff resultTy)) = PiType b eff resultTy
  {-# INLINE toE #-}

instance SinkableE PiType
instance HoistableE  PiType
instance AlphaEqE PiType
instance AlphaHashableE PiType
instance SubstE Name PiType
instance SubstE AtomSubstVal PiType
deriving instance Show (PiType n)
deriving via WrapE PiType n instance Generic (PiType n)

instance GenericE IxType where
  type RepE IxType = PairE Type IxDict
  fromE (IxType ty d) = PairE ty d
  {-# INLINE fromE #-}
  toE   (PairE ty d) = IxType ty d
  {-# INLINE toE #-}

instance SinkableE IxType
instance HoistableE  IxType
instance SubstE Name IxType
instance SubstE AtomSubstVal IxType

instance AlphaEqE IxType where
  alphaEqE (IxType t1 _) (IxType t2 _) = alphaEqE t1 t2

instance AlphaHashableE IxType where
  hashWithSaltE env salt (IxType t _) = hashWithSaltE env salt t

instance GenericE TabPiType where
  type RepE TabPiType = Abs IxBinder Type
  fromE (TabPiType b resultTy) = Abs b resultTy
  {-# INLINE fromE #-}
  toE   (Abs b resultTy) = TabPiType b resultTy
  {-# INLINE toE #-}

instance SinkableE TabPiType
instance HoistableE  TabPiType
instance AlphaEqE TabPiType
instance AlphaHashableE TabPiType
instance SubstE Name TabPiType
instance SubstE AtomSubstVal TabPiType
deriving instance Show (TabPiType n)
deriving via WrapE TabPiType n instance Generic (TabPiType n)

instance GenericE NaryPiType where
  type RepE NaryPiType = Abs (PairB PiBinder (Nest PiBinder)) (PairE EffectRow Type)
  fromE (NaryPiType (NonEmptyNest b bs) eff resultTy) = Abs (PairB b bs) (PairE eff resultTy)
  {-# INLINE fromE #-}
  toE   (Abs (PairB b bs) (PairE eff resultTy)) = NaryPiType (NonEmptyNest b bs) eff resultTy
  {-# INLINE toE #-}

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
  {-# INLINE fromE #-}
  toE   (Abs (PairB b bs) (PairE eff body)) = NaryLamExpr (NonEmptyNest b bs) eff body
  {-# INLINE toE #-}

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
  {-# INLINE fromE #-}
  toE   (Abs b resultTy) = DepPairType b resultTy
  {-# INLINE toE #-}

instance SinkableE   DepPairType
instance HoistableE  DepPairType
instance AlphaEqE    DepPairType
instance AlphaHashableE DepPairType
instance SubstE Name DepPairType
instance SubstE AtomSubstVal DepPairType
deriving instance Show (DepPairType n)
deriving via WrapE DepPairType n instance Generic (DepPairType n)

instance GenericE SynthCandidates where
  type RepE SynthCandidates =
    ListE AtomName `PairE` ListE (PairE ClassName (ListE InstanceName))
  fromE (SynthCandidates xs ys) = ListE xs `PairE` ListE ys'
    where ys' = map (\(k,vs) -> PairE k (ListE vs)) (M.toList ys)
  {-# INLINE fromE #-}
  toE (ListE xs `PairE` ListE ys) = SynthCandidates xs ys'
    where ys' = M.fromList $ map (\(PairE k (ListE vs)) -> (k,vs)) ys
  {-# INLINE toE #-}

instance SinkableE      SynthCandidates
instance HoistableE     SynthCandidates
instance AlphaEqE       SynthCandidates
instance AlphaHashableE SynthCandidates
instance SubstE Name    SynthCandidates

instance GenericE AtomBinding where
  type RepE AtomBinding =
     EitherE2
       (EitherE6
          DeclBinding     -- LetBound
          LamBinding      -- LamBound
          PiBinding       -- PiBound
          IxType          -- IxBound
          Type            -- MiscBound
          SolverBinding)  -- SolverBound
       (EitherE2
          (PairE (LiftE PtrType) PtrName)   -- PtrLitBound
          (PairE NaryPiType TopFunBinding)) -- TopFunBound

  fromE = \case
    LetBound    x -> Case0 $ Case0 x
    LamBound    x -> Case0 $ Case1 x
    PiBound     x -> Case0 $ Case2 x
    IxBound     x -> Case0 $ Case3 x
    MiscBound   x -> Case0 $ Case4 x
    SolverBound x -> Case0 $ Case5 x
    PtrLitBound x y -> Case1 (Case0 (LiftE x `PairE` y))
    TopFunBound ty f ->  Case1 (Case1 (ty `PairE` f))
  {-# INLINE fromE #-}

  toE = \case
    Case0 x' -> case x' of
      Case0 x -> LetBound x
      Case1 x -> LamBound x
      Case2 x -> PiBound  x
      Case3 x -> IxBound  x
      Case4 x -> MiscBound x
      Case5 x -> SolverBound x
      _ -> error "impossible"
    Case1 x' -> case x' of
      Case0 (LiftE x `PairE` y) -> PtrLitBound x y
      Case1 (ty `PairE` f) -> TopFunBound ty f
      _ -> error "impossible"
    _ -> error "impossible"
  {-# INLINE toE #-}

instance SinkableE AtomBinding
instance HoistableE  AtomBinding
instance SubstE Name AtomBinding
instance SubstE AtomSubstVal AtomBinding
instance AlphaEqE AtomBinding
instance AlphaHashableE AtomBinding

instance GenericE TopFunBinding where
  type RepE TopFunBinding = EitherE4
    (LiftE Int `PairE` Atom)  -- UnspecializedTopFun
    SpecializationSpec        -- SpecializedTopFun
    NaryLamExpr               -- SimpTopFun
    ImpFunName                -- FFITopFun
  fromE = \case
    UnspecializedTopFun n x  -> Case0 $ PairE (LiftE n) x
    SpecializedTopFun x -> Case1 x
    SimpTopFun        x -> Case2 x
    FFITopFun         x -> Case3 x
  {-# INLINE fromE #-}

  toE = \case
    Case0 (PairE (LiftE n) x) -> UnspecializedTopFun n x
    Case1 x                   -> SpecializedTopFun x
    Case2 x                   -> SimpTopFun        x
    Case3 x                   -> FFITopFun         x
    _ -> error "impossible"
  {-# INLINE toE #-}


instance SinkableE TopFunBinding
instance HoistableE  TopFunBinding
instance SubstE Name TopFunBinding
instance SubstE AtomSubstVal TopFunBinding
instance AlphaEqE TopFunBinding
instance AlphaHashableE TopFunBinding

instance GenericE SpecializationSpec where
  type RepE SpecializationSpec = PairE AtomName (Abs (Nest Binder) (ListE Type))
  fromE (AppSpecialization fname (Abs bs args)) = PairE fname (Abs bs args)
  {-# INLINE fromE #-}
  toE   (PairE fname (Abs bs args)) = AppSpecialization fname (Abs bs args)
  {-# INLINE toE #-}

instance HasNameHint (SpecializationSpec n) where
  getNameHint (AppSpecialization f _) = getNameHint f

instance SubstE AtomSubstVal SpecializationSpec where
  substE env (AppSpecialization f ab) = do
    let f' = case snd env ! f of
               Rename v -> v
               SubstVal (Var v) -> v
               _ -> error "bad substitution"
    AppSpecialization f' (substE env ab)

instance SinkableE SpecializationSpec
instance HoistableE  SpecializationSpec
instance SubstE Name SpecializationSpec
instance AlphaEqE SpecializationSpec
instance AlphaHashableE SpecializationSpec

instance GenericE SolverBinding where
  type RepE SolverBinding = EitherE2
                              (PairE Type (LiftE SrcPosCtx))
                              Type
  fromE = \case
    InfVarBound  ty ctx -> Case0 (PairE ty (LiftE ctx))
    SkolemBound  ty     -> Case1 ty
  {-# INLINE fromE #-}

  toE = \case
    Case0 (PairE ty (LiftE ct)) -> InfVarBound  ty ct
    Case1 ty                    -> SkolemBound  ty
    _ -> error "impossible"
  {-# INLINE toE #-}

instance SinkableE SolverBinding
instance HoistableE  SolverBinding
instance SubstE Name SolverBinding
instance SubstE AtomSubstVal SolverBinding
instance AlphaEqE SolverBinding
instance AlphaHashableE SolverBinding

instance Color c => GenericE (Binding c) where
  type RepE (Binding c) =
    EitherE2
      (EitherE6
          AtomBinding
          DataDef
          (DataDefName `PairE` Atom)
          (DataDefName `PairE` LiftE Int `PairE` Atom)
          (ClassDef)
          (InstanceDef))
      (EitherE5
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
    ClassBinding      classDef          -> Case0 $ Case4 $ classDef
    InstanceBinding   instanceDef       -> Case0 $ Case5 $ instanceDef
    MethodBinding     className idx f   -> Case1 $ Case0 $ className `PairE` LiftE idx `PairE` f
    ImpFunBinding     fun               -> Case1 $ Case1 $ fun
    ObjectFileBinding objfile           -> Case1 $ Case2 $ objfile
    ModuleBinding m                     -> Case1 $ Case3 $ m
    PtrBinding p                        -> Case1 $ Case4 $ LiftE p
  {-# INLINE fromE #-}

  toE rep = case rep of
    Case0 (Case0 tyinfo)                                    -> fromJust $ tryAsColor $ AtomNameBinding   tyinfo
    Case0 (Case1 dataDef)                                   -> fromJust $ tryAsColor $ DataDefBinding    dataDef
    Case0 (Case2 (dataDefName `PairE` e))                   -> fromJust $ tryAsColor $ TyConBinding      dataDefName e
    Case0 (Case3 (dataDefName `PairE` LiftE idx `PairE` e)) -> fromJust $ tryAsColor $ DataConBinding    dataDefName idx e
    Case0 (Case4 (classDef))                                -> fromJust $ tryAsColor $ ClassBinding      classDef
    Case0 (Case5 (instanceDef))                             -> fromJust $ tryAsColor $ InstanceBinding   instanceDef
    Case1 (Case0 (className `PairE` LiftE idx `PairE` f))   -> fromJust $ tryAsColor $ MethodBinding     className idx f
    Case1 (Case1 fun)                                       -> fromJust $ tryAsColor $ ImpFunBinding     fun
    Case1 (Case2 objfile)                                   -> fromJust $ tryAsColor $ ObjectFileBinding objfile
    Case1 (Case3 m)                                         -> fromJust $ tryAsColor $ ModuleBinding     m
    Case1 (Case4 (LiftE ptr))                               -> fromJust $ tryAsColor $ PtrBinding        ptr
    _ -> error "impossible"
  {-# INLINE toE #-}

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
  {-# INLINE fromE #-}
  toE   (LiftE ann `PairE` ty `PairE` expr) = DeclBinding ann ty expr
  {-# INLINE toE #-}

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

instance Semigroup (SynthCandidates n) where
  SynthCandidates xs ys <> SynthCandidates xs' ys' =
    SynthCandidates (xs<>xs') (M.unionWith (<>) ys ys')

instance Monoid (SynthCandidates n) where
  mempty = SynthCandidates mempty mempty


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

instance GenericE PartialTopEnvFrag where
  type RepE PartialTopEnvFrag = Cache
                              `PairE` CustomRules
                              `PairE` LoadedModules
                              `PairE` ModuleEnv
  fromE (PartialTopEnvFrag cache rules loaded env) = cache `PairE` rules `PairE` loaded `PairE` env
  {-# INLINE fromE #-}
  toE (cache `PairE` rules `PairE` loaded `PairE` env) = PartialTopEnvFrag cache rules loaded env
  {-# INLINE toE #-}

instance SinkableE      PartialTopEnvFrag
instance HoistableE     PartialTopEnvFrag
instance AlphaEqE       PartialTopEnvFrag
instance SubstE Name    PartialTopEnvFrag

instance Semigroup (PartialTopEnvFrag n) where
  PartialTopEnvFrag x1 x2 x3 x4 <> PartialTopEnvFrag y1 y2 y3 y4=
    PartialTopEnvFrag (x1<>y1) (x2<>y2) (x3<>y3) (x4<>y4)

instance Monoid (PartialTopEnvFrag n) where
  mempty = PartialTopEnvFrag mempty mempty mempty mempty
  mappend = (<>)

instance GenericB TopEnvFrag where
  type RepB TopEnvFrag = PairB EnvFrag (LiftB PartialTopEnvFrag)
  fromB (TopEnvFrag frag1 frag2) = PairB frag1 (LiftB frag2)
  toB   (PairB frag1 (LiftB frag2)) = TopEnvFrag frag1 frag2

instance SubstB Name TopEnvFrag
instance HoistableB  TopEnvFrag
instance SinkableB TopEnvFrag
instance ProvesExt   TopEnvFrag
instance BindsNames  TopEnvFrag

instance OutFrag TopEnvFrag where
  emptyOutFrag = TopEnvFrag emptyOutFrag mempty
  {-# INLINE emptyOutFrag #-}
  catOutFrags scope (TopEnvFrag frag1 partial1)
                    (TopEnvFrag frag2 partial2) =
    withExtEvidence frag2 $
      TopEnvFrag
        (catOutFrags scope frag1 frag2)
        (sink partial1 <> partial2)
  {-# INLINE catOutFrags #-}

-- XXX: unlike `ExtOutMap Env EnvFrag` instance, this once doesn't
-- extend the synthesis candidates based on the annotated let-bound names. It
-- only extends synth candidates when they're supplied explicitly.
instance ExtOutMap Env TopEnvFrag where
  extendOutMap env (TopEnvFrag (EnvFrag frag _) (PartialTopEnvFrag cache' rules' loaded' mEnv')) = result
    where
      Env (TopEnv defs rules cache loaded) mEnv = env
      result = Env newTopEnv newModuleEnv

      newTopEnv = withExtEvidence frag $ TopEnv
        (defs `extendRecSubst` frag)
        (sink rules <> rules')
        (sink cache <> cache')
        (sink loaded <> loaded')

      newModuleEnv =
        ModuleEnv
          (imports <> imports')
          (sm   <> sm'   <> newImportedSM)
          (scs  <> scs'  <> newImportedSC)
          (objs <> objs' <> newImportedObj)
          (effs <> effs')
        where
          ModuleEnv imports sm scs objs effs = withExtEvidence frag $ sink mEnv
          ModuleEnv imports' sm' scs' objs' effs' = mEnv'
          newDirectImports = S.difference (directImports imports') (directImports imports)
          newTransImports  = S.difference (transImports  imports') (transImports  imports)
          newImportedSM  = flip foldMap newDirectImports $ moduleExports         . lookupModulePure
          newImportedSC  = flip foldMap newTransImports  $ moduleSynthCandidates . lookupModulePure
          newImportedObj = flip foldMap newTransImports  $ moduleObjectFiles     . lookupModulePure

      lookupModulePure v = case lookupEnvPure (Env newTopEnv mempty) v of ModuleBinding m -> m

lookupEnvPure :: Color c => Env n -> Name c n -> Binding c n
lookupEnvPure env v = lookupTerminalSubstFrag (fromRecSubst $ envDefs $ topEnv env) v

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
  {-# INLINE fromE #-}

  toE (LiftE name `PairE` ListE deps `PairE` ListE transDeps
         `PairE` sm `PairE` sc `PairE` objs) =
    Module name (S.fromList deps) (S.fromList transDeps) sm sc objs
  {-# INLINE toE #-}

instance SinkableE      Module
instance HoistableE     Module
instance AlphaEqE       Module
instance AlphaHashableE Module
instance SubstE Name    Module

instance GenericE ImportStatus where
  type RepE ImportStatus = ListE ModuleName `PairE` ListE ModuleName
  fromE (ImportStatus direct trans) = ListE (S.toList direct)
                              `PairE` ListE (S.toList trans)
  {-# INLINE fromE #-}
  toE (ListE direct `PairE` ListE trans) =
    ImportStatus (S.fromList direct) (S.fromList trans)
  {-# INLINE toE #-}

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
  {-# INLINE fromE #-}
  toE (ListE pairs) =
    LoadedModules $ M.fromList $ pairs <&> \(PairE (LiftE v) md) -> (v, md)
  {-# INLINE toE #-}

instance SinkableE      LoadedModules
instance HoistableE     LoadedModules
instance AlphaEqE       LoadedModules
instance AlphaHashableE LoadedModules
instance SubstE Name    LoadedModules

instance GenericE ObjectFile where
  type RepE ObjectFile = LiftE (BS.ByteString, [CFunName]) `PairE` ListE ObjectFileName
  fromE (ObjectFile contents fs deps) = LiftE (contents, fs) `PairE` ListE deps
  {-# INLINE fromE #-}
  toE   (LiftE (contents, fs) `PairE` ListE deps) = ObjectFile contents fs deps
  {-# INLINE toE #-}

instance Store (ObjectFile n)
instance SubstE Name ObjectFile
instance SinkableE  ObjectFile
instance HoistableE ObjectFile

instance GenericE CFun where
  type RepE CFun = LiftE CFunName `PairE` ObjectFileName
  fromE (CFun name obj) = LiftE name `PairE` obj
  {-# INLINE fromE #-}
  toE   (LiftE name `PairE` obj) = CFun name obj
  {-# INLINE toE #-}

instance Store (CFun n)
instance SubstE Name CFun
instance AlphaEqE CFun
instance SinkableE  CFun
instance HoistableE CFun

instance GenericE ObjectFiles where
  type RepE ObjectFiles = ListE ObjectFileName
  fromE (ObjectFiles xs) = ListE $ S.toList xs
  {-# INLINE fromE #-}
  toE   (ListE xs) = ObjectFiles $ S.fromList xs
  {-# INLINE toE #-}

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
  {-# INLINE fromE #-}
  toE (imports `PairE` sm `PairE` sc `PairE` obj `PairE` eff) =
    ModuleEnv imports sm sc obj eff
  {-# INLINE toE #-}

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

instance Store (Atom n)
instance Store (Expr n)
instance Store (SolverBinding n)
instance Store (AtomBinding n)
instance Store (SpecializationSpec n)
instance Store (TopFunBinding n)
instance Store (LamBinding  n)
instance Store (DeclBinding n)
instance Store (FieldRowElem  n)
instance Store (FieldRowElems n)
instance Store (Decl n l)
instance Store (DataDefBinders n l)
instance Store (DataDefParams n)
instance Store (DataDef n)
instance Store (DataConDef n)
instance Store (Block n)
instance Store (LamBinder n l)
instance Store (LamExpr n)
instance Store (IxType n)
instance Store (TabLamExpr n)
instance Store (PiBinding n)
instance Store (PiBinder n l)
instance Store (PiType n)
instance Store (TabPiType n)
instance Store (DepPairType  n)
instance Store (SuperclassBinders n l)
instance Store (AtomRules n)
instance Store (ClassDef     n)
instance Store (InstanceDef  n)
instance Store (InstanceBody n)
instance Store (MethodType   n)
instance Store (DictType n)
instance Store (DictExpr n)
instance Store (SynthCandidates n)
instance Store (DataConRefBinding n l)
instance Store (ObjectFiles n)
instance Store (Module n)
instance Store (ImportStatus n)
instance Store (LoadedModules n)
instance Color c => Store (Binding c n)
instance Store (ModuleEnv n)
instance Store (TopEnv n)
instance Store (Env n)
instance Store (BoxPtr n)
instance (Store (ann n)) => Store (NonDepNest ann n l)

-- === Orphan instances ===
-- TODO: Resolve this!

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
