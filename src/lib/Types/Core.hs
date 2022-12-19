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
{-# LANGUAGE ConstraintKinds #-}

module Types.Core (module Types.Core, SymbolicZeros (..)) where

import Control.Applicative
import Control.Monad.Writer.Strict (Writer, execWriter, tell)
import Data.Word
import Data.Maybe
import Data.Functor
import Data.Foldable (toList)
import Data.Hashable
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty    as NE
import qualified Data.Map.Strict       as M
import qualified Data.Set              as S

import GHC.Stack
import GHC.Generics (Generic (..))
import Data.Store (Store (..))
import Foreign.Ptr

import Name
import Err
import LabeledItems
import Util (FileHash, onFst, SnocList (..), toSnocList, Tree (..))
import IRVariants

import Types.Primitives
import Types.Source
import Types.Imp

-- === core IR ===

data Atom (r::IR) (n::S) where
 Var        :: AtomName r n    -> Atom r n
 TabPi      :: TabPiType r n   -> Atom r n
 Con        :: Con r n         -> Atom r n
 TC         :: TC  r n         -> Atom r n
 PtrVar     :: PtrName n       -> Atom r n
 DepPair    :: Atom r n -> Atom r n -> DepPairType r n  -> Atom r n
 DepPairTy  :: DepPairType r n                          -> Atom r n
 -- === CoreIR only ===
 -- The binder in the `EffAbs n` is meant to be parallel to the binder in
 -- the `LamExpr`, of which there must be only one (for now).
 Lam        :: HasCore r => LamExpr r n -> Arrow -> EffAbs n -> Atom r n
 Pi         :: HasCore r => PiType  r n               -> Atom r n
 Eff        :: HasCore r => EffectRow n -> Atom r n
 DictCon    :: HasCore r => DictExpr r n                  -> Atom r n
 DictTy     :: HasCore r => DictType r n                  -> Atom r n
 -- XXX: Variable name must not be an alias for another name or for
 -- a statically-known atom. This is because the variable name used
 -- here may also appear in the type of the atom. (We maintain this
 -- invariant during substitution and in Builder.hs.)
 ProjectElt   :: NE.NonEmpty Projection -> AtomName r n -> Atom r n
 NewtypeCon   :: HasCore r => NewtypeCon r n   -> Atom r n -> Atom r n
 NewtypeTyCon :: HasCore r => NewtypeTyCon r n             -> Atom r n
 ACase        :: HasCore r => Atom r n -> [AltP r (Atom r) n] -> Type r n -> Atom r n
 -- TODO: consider restricting TabLam further and only allowing it in CoreToSimpIR
 TabLam       :: HasCore r => TabLamExpr r n  -> Atom r n
 -- === Temporary transitional constructors ===
 -- XXX: Because of the "rhs is a var" constraint on `ProjectElt, we need
 -- `SimpInCore` to reimplement projections ... twice! We need projections both
 -- before and after the type coercion. TODO: remove the projections once we fix
 -- the ProjectElt mess.
 SimpInCore :: [Projection] -> Maybe (Type r n) -> [Projection] -> AtomName SimpIR n -> Atom r n
 RepValAtom :: r `Sat` Is SimpToImpIR  => RepVal r n -> Atom r n

deriving instance Show (Atom r n)
deriving via WrapE (Atom r) n instance Generic (Atom r n)

data Expr r n where
 App    :: Atom r n -> NonEmpty (Atom r n)   -> Expr r n
 TabApp :: Atom r n -> NonEmpty (Atom r n)   -> Expr r n
 Case   :: Atom r n -> [Alt r n] -> Type r n -> EffectRow n -> Expr r n
 Atom   :: Atom r n                          -> Expr r n
 Hof    :: Hof r n                           -> Expr r n
 TabCon :: Type r n -> [Atom r n]            -> Expr r n
 RefOp  :: Atom r n -> RefOp r n             -> Expr r n
 PrimOp :: PrimOp (Atom r n)                 -> Expr r n
 UserEffectOp    :: HasCore r    => UserEffectOp r n           -> Expr r n
 ProjMethod      :: HasCore r    => Atom r n -> Int            -> Expr r n
 RecordVariantOp :: HasCore r    => RecordVariantOp (Atom r n) -> Expr r n
 DAMOp           :: IsLowered r => DAMOp r n                  -> Expr r n

deriving instance Show (Expr r n)
deriving via WrapE (Expr r) n instance Generic (Expr r n)

data BaseMonoid r n =
  BaseMonoid { baseEmpty   :: Atom r n
             , baseCombine :: LamExpr r n }
  deriving (Show, Generic)

type EffAbs = Abs AtomNameBinder EffectRow

data DeclBinding r n = DeclBinding LetAnn (Type r n) (Expr r n)
     deriving (Show, Generic)
data Decl (r::IR) (n::S) (l::S) = Let (AtomNameBinder n l) (DeclBinding r n)
     deriving (Show, Generic)
type Decls r = Nest (Decl r)

-- TODO: make this a newtype with an unsafe constructor The idea is that the `r`
-- parameter will play a role a bit like the `c` parameter in names: if you have
-- an `AtomName r n` and you look up its definition in the `Env`, you're sure to
-- get an `AtomBinding r n`.
type AtomName (r::IR) = Name AtomNameC
type AtomNameBinder   = NameBinder AtomNameC

type ClassName    = Name ClassNameC
type DataDefName  = Name DataDefNameC
type EffectName   = Name EffectNameC
type EffectOpName = Name EffectOpNameC
type HandlerName  = Name HandlerNameC
type InstanceName = Name InstanceNameC
type MethodName   = Name MethodNameC
type ModuleName   = Name ModuleNameC
type PtrName      = Name PtrNameC
type SpecDictName = Name SpecializedDictNameC
type FunObjCodeName = Name FunObjCodeNameC

type Effect    = EffectP    Name
type EffectRow = EffectRowP Name

type AtomBinderP = BinderP AtomNameC
type Binder r = AtomBinderP (Type r) :: B
type AltP (r::IR) (e::E) = Abs (Binder r) e :: E
type Alt r = AltP r (Block r) :: E

-- The additional invariant enforced by this newtype is that the list should
-- never contain empty StaticFields members, nor StaticFields in two consecutive
-- positions.
newtype FieldRowElems (r::IR) (n::S) = UnsafeFieldRowElems { fromFieldRowElems :: [FieldRowElem r n] }
                                       deriving (Show, Generic)

data FieldRowElem (r::IR) (n::S)
  = StaticFields (LabeledItems (Type r n))
  | DynField     (AtomName r n) (Type r n)
  | DynFields    (AtomName r n)
  deriving (Show, Generic)

data DataDef n where
  -- The `SourceName` is just for pretty-printing. The actual alpha-renamable
  -- binder name is in UExpr and Env
  DataDef :: SourceName -> Nest (RolePiBinder CoreIR) n l -> [DataConDef l] -> DataDef n

data DataConDef n =
  -- Name for pretty printing, constructor elements, representation type,
  -- list of projection indices that recovers elements from the representation.
  DataConDef SourceName (CType n) [[Projection]]
  deriving (Show, Generic)

data ParamRole = TypeParam | DictParam | DataParam deriving (Show, Generic, Eq)

newtype DataDefParams r n = DataDefParams [(Arrow, Atom r n)]
  deriving (Show, Generic)

-- The Type is the type of the result expression (and thus the type of the
-- block). It's given by querying the result expression's type, and checking
-- that it doesn't have any free names bound by the decls in the block. We store
-- it separately as an optimization, to avoid having to traverse the block.
-- If the decls are empty we can skip the type annotation, because then we can
-- cheaply query the result, and, more importantly, there's no risk of having a
-- type that mentions local variables.
data Block (r::IR) (n::S) where
  Block :: BlockAnn r n l -> Nest (Decl r) n l -> Atom r l -> Block r n

data BlockAnn r n l where
  BlockAnn :: Type r n -> EffectRow n -> BlockAnn r n l
  NoBlockAnn :: BlockAnn r n n

data LamBinding (r::IR) (n::S) = LamBinding Arrow (Type r n)
  deriving (Show, Generic)

data LamExpr (r::IR) (n::S) where
  LamExpr :: Nest (Binder r) n l -> Block r l -> LamExpr r n

data IxDict r n where
  IxDictAtom        :: HasCore r => Atom r n         -> IxDict r n
  -- TODO: make these two only available in SimpIR (currently we can't do that
  -- because we need CoreIR to be a superset of SimpIR)
  IxDictFin         :: Atom r n                     -> IxDict r n
  IxDictSpecialized :: Type r n -> SpecDictName n -> [Atom r n] -> IxDict r n

deriving instance Show (IxDict r n)
deriving via WrapE (IxDict r) n instance Generic (IxDict r n)

data IxMethod = Size | Ordinal | UnsafeFromOrdinal
     deriving (Show, Generic, Enum, Bounded, Eq)

data IxType (r::IR) (n::S) =
  IxType { ixTypeType :: Type r n
         , ixTypeDict :: IxDict r n }
  deriving (Show, Generic)

type IxBinder r = BinderP AtomNameC (IxType r)

data TabLamExpr (r::IR) (n::S) where
  TabLamExpr :: IxBinder r n l -> Block r l -> TabLamExpr r n

data TabPiType (r::IR) (n::S) where
  TabPiType :: IxBinder r n l -> Type r l -> TabPiType r n

data NaryPiType (r::IR) (n::S) where
  NaryPiType :: Nest (PiBinder r) n l -> EffectRow l -> Type r l -> NaryPiType r n

data PiBinding (r::IR) (n::S) = PiBinding Arrow (Type r n)
  deriving (Show, Generic)

data PiBinder (r::IR) (n::S) (l::S) =
  PiBinder (AtomNameBinder n l) (Type r n) Arrow
  deriving (Show, Generic)

data PiType (r::IR) (n::S) where
  PiType :: PiBinder r n l -> EffectRow l -> Type r l -> PiType r n

data DepPairType (r::IR) (n::S) where
  DepPairType :: Binder r n l -> Type r l -> DepPairType r n

data Projection =
   UnwrapNewtype -- TODO: add `HasCore r` constraint
 | ProjectProduct Int
     deriving (Show, Eq, Generic)

type Val  = Atom
type Type = Atom
type Kind = Type
type Dict = Atom

type TC  r n = PrimTC  r (Atom r n)
type Con r n = PrimCon r (Atom r n)

type AtomSubstVal r = SubstVal AtomNameC (Atom r) :: V

data EffectBinder n l where
  EffectBinder :: EffectRow n -> EffectBinder n n

instance GenericB EffectBinder where
  type RepB EffectBinder = LiftB EffectRow
  fromB (EffectBinder effs) = LiftB effs
  toB   (LiftB effs) = EffectBinder effs

data BoxPtr (r::IR) (n::S) = BoxPtr (Atom r n) (Block r n)  -- ptrptr, size
                             deriving (Show, Generic)

-- A nest where the annotation of a binder cannot depend on the binders
-- introduced before it. You can think of it as introducing a bunch of
-- names into the scope in parallel, but since safer names only reasons
-- about sequential scope extensions, we encode it differently.
data NonDepNest r ann n l = NonDepNest (Nest AtomNameBinder n l) [ann n]
                            deriving (Generic)

-- === Various ops ===

data Hof r n where
 For       :: ForAnn -> IxDict r n -> LamExpr r n -> Hof r n
 While     :: Block r n -> Hof r n
 RunReader :: Atom r n -> LamExpr r n -> Hof r n
 RunWriter :: Maybe (Atom r n) -> BaseMonoid r n -> LamExpr r n -> Hof r n
 RunState  :: Maybe (Atom r n) -> Atom r n -> LamExpr r n -> Hof r n  -- dest, initial value, body lambda
 RunIO     :: Block r n -> Hof r n
 RunInit   :: Block r n -> Hof r n
 CatchException :: HasCore r => Block r n -> Hof r n
 Linearize      :: HasCore r => LamExpr r n -> Hof r n
 Transpose      :: HasCore r => LamExpr r n -> Hof r n

deriving instance Show (Hof r n)
deriving via WrapE (Hof r) n instance Generic (Hof r n)


-- Ops for "Dex Abstract Machine"
data DAMOp r n =
   Seq Direction (IxDict r n) (Atom r n) (LamExpr r n)   -- ix dict, carry dests, body lambda
 | RememberDest (Atom r n) (LamExpr r n)
 | AllocDest (Atom r n)        -- type
 | Place (Atom r n) (Atom r n) -- reference, value
 | Freeze (Atom r n)           -- reference
   deriving (Show, Generic)

data RefOp r n =
   MAsk
 | MExtend (BaseMonoid r n) (Atom r n)
 | MGet
 | MPut (Atom r n)
 | IndexRef (Atom r n)
 | ProjRef Int
  deriving (Show, Generic)

data UserEffectOp r n =
   Handle (HandlerName n) [Atom r n] (Block r n)
 | Resume (Atom r n) (Atom r n)     -- Resume from effect handler (type, arg)
 | Perform (Atom r n) Int  -- Call an effect operation (effect name) (op #)
   deriving (Show, Generic)

-- === IR variants ===

instance CovariantInIR Atom
instance CovariantInIR Block
instance CovariantInIR Expr
instance CovariantInIR IxType
instance CovariantInIR LamExpr
instance CovariantInIR BaseMonoid
instance CovariantInIR IxDict

type CAtom  = Atom CoreIR
type CType  = Type CoreIR
type CExpr  = Expr CoreIR
type CBlock = Block CoreIR
type CDecl  = Decl  CoreIR
type CDecls = Decls CoreIR
type CAtomSubstVal = AtomSubstVal CoreIR
type CAtomName  = AtomName CoreIR

type SAtom  = Atom SimpIR
type SType  = Type SimpIR
type SExpr  = Expr SimpIR
type SBlock = Block SimpIR
type SDecl  = Decl  SimpIR
type SDecls = Decls SimpIR
type SAtomSubstVal = AtomSubstVal SimpIR
type SAtomName  = AtomName SimpIR
type SBinder = Binder SimpIR

-- === newtypes ===

-- Describes how to lift the "shallow" representation type to the newtype.
data NewtypeCon (r::IR) (n::S) =
   RecordCon  (LabeledItems ())
 | VariantCon (LabeledItems ())
 | UserADTData (DataDefName n) (DataDefParams r n)
 | NatCon
 | FinCon (Atom r n)
   deriving (Show, Generic)

data NewtypeTyCon (r::IR) (n::S) =
   Nat
 | Fin (Atom r n)
 | EffectRowKind
 | LabeledRowKindTC
 | LabelType
 | RecordTyCon  (FieldRowElems r n)
 | VariantTyCon (ExtLabeledItems (Type r n) (AtomName r n))
 | LabelCon String
 | LabeledRowCon (FieldRowElems r n)
 | UserADTType SourceName (DataDefName n) (DataDefParams r n)
   deriving (Show, Generic)

pattern TypeCon :: HasCore r => SourceName -> DataDefName n -> DataDefParams r n -> Atom r n
pattern TypeCon s d xs = NewtypeTyCon (UserADTType s d xs)

pattern LabeledRow :: HasCore r => FieldRowElems r n -> Atom r n
pattern LabeledRow xs = NewtypeTyCon (LabeledRowCon xs)

pattern RecordTy :: HasCore r => FieldRowElems r n -> Atom r n
pattern RecordTy xs = NewtypeTyCon (RecordTyCon xs)

pattern VariantTy :: HasCore r => ExtLabeledItems (Type r n) (AtomName r n) -> Atom r n
pattern VariantTy xs = NewtypeTyCon (VariantTyCon xs)

isSumCon :: NewtypeCon r n -> Bool
isSumCon = \case
 VariantCon _ -> True
 UserADTData _ _ -> True
 _ -> False

-- === type classes ===

data SuperclassBinders n l =
  SuperclassBinders
    { superclassBinders :: Nest AtomNameBinder n l
    , superclassTypes   :: [CType n] }
  deriving (Show, Generic)

data ClassDef (n::S) where
  ClassDef
    :: SourceName
    -> [SourceName]                       -- method source names
    -> Nest (RolePiBinder CoreIR) n1 n2   -- parameters
    ->   SuperclassBinders n2 n3          -- superclasses
    ->   [MethodType n3]                  -- method types
    -> ClassDef n1

data RolePiBinder r n l = RolePiBinder (AtomNameBinder n l) (Type r n) Arrow ParamRole
     deriving (Show, Generic)

data InstanceDef (n::S) where
  InstanceDef
    :: ClassName n1
    -> Nest (RolePiBinder CoreIR) n1 n2 -- parameters (types and dictionaries)
    ->   [CType n2]                     -- class parameters
    ->   InstanceBody n2
    -> InstanceDef n1

data InstanceBody (n::S) =
  InstanceBody
    [Atom  CoreIR n]   -- superclasses dicts
    [Block CoreIR n]  -- method definitions
  deriving (Show, Generic)

data MethodType (n::S) =
  MethodType
    [Bool]     -- indicates explicit args
    (CType n)  -- actual method type
 deriving (Show, Generic)

data DictType (r::IR) (n::S) = DictType SourceName (ClassName n) [Type r n]
     deriving (Show, Generic)

data DictExpr (r::IR) (n::S) =
   InstantiatedGiven (Atom r n) (NonEmpty (Atom r n))
 | SuperclassProj (Atom r n) Int  -- (could instantiate here too, but we don't need it for now)
   -- We use NonEmpty because givens without args can be represented using `Var`.
 | InstanceDict (InstanceName n) [Atom r n]
   -- Special case for `Ix (Fin n)`  (TODO: a more general mechanism for built-in classes and instances)
 | IxFin (Atom r n)
   deriving (Show, Generic)

-- TODO: Use an IntMap
newtype CustomRules (n::S) =
  CustomRules { customRulesMap :: M.Map (AtomName CoreIR n) (AtomRules n) }
  deriving (Semigroup, Monoid, Store)
data AtomRules (n::S) = CustomLinearize Int SymbolicZeros (CAtom n)  -- number of implicit args, linearization function
                        deriving (Generic)

-- === Runtime representations ===

data RepVal (r::IR) (n::S) = RepVal (Type r n) (Tree (IExpr n))
     deriving (Show, Generic)

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
  , envLoadedModules :: LoadedModules n
  , envLoadedObjects :: LoadedObjects n }
  deriving (Generic)

data SerializedEnv n = SerializedEnv
  { serializedEnvDefs        :: RecSubst Binding n
  , serializedEnvCustomRules :: CustomRules n
  , serializedEnvCache       :: Cache n }
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
  -- TODO: should these live elsewhere?
  , allowedEffects       :: EffectRow n }
  deriving (Generic)

data Module (n::S) = Module
  { moduleSourceName :: ModuleSourceName
  , moduleDirectDeps :: S.Set (ModuleName n)
  , moduleTransDeps  :: S.Set (ModuleName n)  -- XXX: doesn't include the module itself
  , moduleExports    :: SourceMap n
    -- these are just the synth candidates required by this
    -- module by itself. We'll usually also need those required by the module's
    -- (transitive) dependencies, which must be looked up separately.
  , moduleSynthCandidates :: SynthCandidates n }
  deriving (Show, Generic)

data LoadedModules (n::S) = LoadedModules
  { fromLoadedModules   :: M.Map ModuleSourceName (ModuleName n)}
  deriving (Show, Generic)

emptyModuleEnv :: ModuleEnv n
emptyModuleEnv = ModuleEnv emptyImportStatus (SourceMap mempty) mempty Pure

emptyLoadedModules :: LoadedModules n
emptyLoadedModules = LoadedModules mempty

data LoadedObjects (n::S) = LoadedObjects
  -- the pointer points to the actual runtime function
  { fromLoadedObjects :: M.Map (FunObjCodeName n) NativeFunction}
  deriving (Show, Generic)

emptyLoadedObjects :: LoadedObjects n
emptyLoadedObjects = LoadedObjects mempty

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
  , fragLoadedObjects   :: LoadedObjects n
  , fragLocalModuleEnv  :: ModuleEnv n
  , fragFinishSpecializedDict :: SnocList (SpecDictName n, [LamExpr SimpIR n]) }

-- TODO: we could add a lot more structure for querying by dict type, caching, etc.
-- TODO: make these `Name n` instead of `Atom n` so they're usable as cache keys.
data SynthCandidates n = SynthCandidates
  { lambdaDicts       :: [AtomName CoreIR n]
  , instanceDicts     :: M.Map (ClassName n) [InstanceName n] }
  deriving (Show, Generic)

emptyImportStatus :: ImportStatus n
emptyImportStatus = ImportStatus mempty mempty

-- TODO: figure out the additional top-level context we need -- backend, other
-- compiler flags etc. We can have a map from those to this.

data Cache (n::S) = Cache
  { specializationCache :: EMap SpecializationSpec (AtomName CoreIR) n
  , ixDictCache :: EMap AbsDict SpecDictName n
  , impCache  :: EMap (AtomName CoreIR) ImpFunName n
  , objCache  :: EMap ImpFunName FunObjCodeName n
    -- This is memoizing `parseAndGetDeps :: Text -> [ModuleSourceName]`. But we
    -- only want to store one entry per module name as a simple cache eviction
    -- policy, so we store it keyed on the module name, with the text hash for
    -- the validity check.
  , parsedDeps :: M.Map ModuleSourceName (FileHash, [ModuleSourceName])
  , moduleEvaluations :: M.Map ModuleSourceName ((FileHash, [ModuleName n]), ModuleName n)
  } deriving (Show, Generic)

updateEnv :: Color c => Name c n -> Binding c n -> Env n -> Env n
updateEnv v rhs env =
  env { topEnv = (topEnv env) { envDefs = RecSubst $ updateSubstFrag v rhs bs } }
  where (RecSubst bs) = envDefs $ topEnv env

-- === runtime function and variable representations ===

type RuntimeEnv = DynamicVarKeyPtrs

type DexDestructor = FunPtr (IO ())

data NativeFunction = NativeFunction
  { nativeFunPtr      :: FunPtr ()
  , nativeFunTeardown :: IO () }

instance Show NativeFunction where
  show _ = "<native function>"

-- Holds pointers to thread-local storage used to simulate dynamically scoped
-- variables, such as the output stream file descriptor.
type DynamicVarKeyPtrs = [(DynamicVar, Ptr ())]

data DynamicVar = OutStreamDyvar -- TODO: add others as needed
                  deriving (Enum, Bounded)

dynamicVarCName :: DynamicVar -> String
dynamicVarCName OutStreamDyvar = "dex_out_stream_dyvar"

dynamicVarLinkMap :: DynamicVarKeyPtrs -> [(String, Ptr ())]
dynamicVarLinkMap dyvars = dyvars <&> \(v, ptr) -> (dynamicVarCName v, ptr)

-- === bindings - static information we carry about a lexical scope ===

-- TODO: consider making this an open union via a typeable-like class
data Binding (c::C) (n::S) where
  AtomNameBinding   :: AtomBinding CoreIR n            -> Binding AtomNameC       n
  DataDefBinding    :: DataDef n                       -> Binding DataDefNameC    n
  TyConBinding      :: DataDefName n        -> CAtom n -> Binding TyConNameC      n
  DataConBinding    :: DataDefName n -> Int -> CAtom n -> Binding DataConNameC    n
  ClassBinding      :: ClassDef n                      -> Binding ClassNameC      n
  InstanceBinding   :: InstanceDef n                   -> Binding InstanceNameC   n
  MethodBinding     :: ClassName n   -> Int -> CAtom n -> Binding MethodNameC     n
  EffectBinding     :: EffectDef n                    -> Binding EffectNameC     n
  HandlerBinding    :: HandlerDef n                   -> Binding HandlerNameC    n
  EffectOpBinding   :: EffectOpDef n                  -> Binding EffectOpNameC   n
  ImpFunBinding     :: ImpFunction n                  -> Binding ImpFunNameC     n
  FunObjCodeBinding :: FunObjCode -> LinktimeNames n  -> Binding FunObjCodeNameC n
  ModuleBinding     :: Module n                       -> Binding ModuleNameC     n
  -- TODO: add a case for abstracted pointers, as used in `ClosedImpFunction`
  PtrBinding        :: PtrType -> PtrLitVal           -> Binding PtrNameC        n
  SpecializedDictBinding :: SpecializedDictDef n      -> Binding SpecializedDictNameC n
  ImpNameBinding    :: BaseType                       -> Binding ImpNameC n
deriving instance Show (Binding c n)

data EffectOpDef (n::S) where
  EffectOpDef :: EffectName n  -- name of associated effect
              -> EffectOpIdx   -- index in effect definition
              -> EffectOpDef n
  deriving (Show, Generic)

instance GenericE EffectOpDef where
  type RepE EffectOpDef =
    EffectName `PairE` LiftE EffectOpIdx
  fromE (EffectOpDef name idx) = name `PairE` LiftE idx
  toE (name `PairE` LiftE idx) = EffectOpDef name idx

instance SinkableE   EffectOpDef
instance HoistableE  EffectOpDef
instance SubstE Name EffectOpDef

data EffectOpIdx = ReturnOp | OpIdx Int
  deriving (Show, Eq, Generic)

data EffectDef (n::S) where
  EffectDef :: SourceName
            -> [(SourceName, EffectOpType n)]
            -> EffectDef n

instance GenericE EffectDef where
  type RepE EffectDef =
    LiftE SourceName `PairE` ListE (LiftE SourceName `PairE` EffectOpType)
  fromE (EffectDef name ops) =
    LiftE name `PairE` ListE (map (\(x, y) -> LiftE x `PairE` y) ops)
  toE (LiftE name `PairE` ListE ops) =
    EffectDef name (map (\(LiftE x `PairE` y)->(x,y)) ops)

instance SinkableE EffectDef
instance HoistableE  EffectDef
instance AlphaEqE EffectDef
instance AlphaHashableE EffectDef
instance SubstE Name EffectDef
instance SubstE (AtomSubstVal CoreIR) EffectDef
deriving instance Show (EffectDef n)
deriving via WrapE EffectDef n instance Generic (EffectDef n)

data HandlerDef (n::S) where
  HandlerDef :: EffectName n
             -> PiBinder CoreIR n r -- body type arg
             -> Nest (PiBinder CoreIR) r l
               -> EffectRow l
               -> CType l          -- return type
               -> [Block CoreIR l] -- effect operations
               -> Block CoreIR l   -- return body
             -> HandlerDef n

instance GenericE HandlerDef where
  type RepE HandlerDef =
    EffectName `PairE` Abs (PiBinder CoreIR `PairB` Nest (PiBinder CoreIR))
      (EffectRow `PairE` CType `PairE` ListE (Block CoreIR) `PairE` Block CoreIR)
  fromE (HandlerDef name bodyTyArg bs effs ty ops ret) =
    name `PairE` Abs (bodyTyArg `PairB` bs) (effs `PairE` ty `PairE` ListE ops `PairE` ret)
  toE (name `PairE` Abs (bodyTyArg `PairB` bs) (effs `PairE` ty `PairE` ListE ops `PairE` ret)) =
    HandlerDef name bodyTyArg bs effs ty ops ret

instance SinkableE HandlerDef
instance HoistableE  HandlerDef
instance AlphaEqE HandlerDef
instance AlphaHashableE HandlerDef
instance SubstE Name HandlerDef
-- instance SubstE (AtomSubstVal r) HandlerDef
deriving instance Show (HandlerDef n)
deriving via WrapE HandlerDef n instance Generic (HandlerDef n)

data EffectOpType (n::S) where
  EffectOpType :: UResumePolicy -> CType n -> EffectOpType n

instance GenericE EffectOpType where
  type RepE EffectOpType =
    LiftE UResumePolicy `PairE` CType
  fromE (EffectOpType pol ty) = LiftE pol `PairE` ty
  toE (LiftE pol `PairE` ty) = EffectOpType pol ty

instance SinkableE EffectOpType
instance HoistableE  EffectOpType
instance AlphaEqE EffectOpType
instance AlphaHashableE EffectOpType
instance SubstE Name EffectOpType
instance SubstE (AtomSubstVal CoreIR) EffectOpType
deriving instance Show (EffectOpType n)
deriving via WrapE EffectOpType n instance Generic (EffectOpType n)

instance GenericE SpecializedDictDef where
  type RepE SpecializedDictDef = AbsDict `PairE` MaybeE (ListE (LamExpr SimpIR))
  fromE (SpecializedDict ab methods) = ab `PairE` methods'
    where methods' = case methods of Just xs -> LeftE (ListE xs)
                                     Nothing -> RightE UnitE
  {-# INLINE fromE #-}
  toE   (ab `PairE` methods) = SpecializedDict ab methods'
    where methods' = case methods of LeftE (ListE xs) -> Just xs
                                     RightE UnitE     -> Nothing
  {-# INLINE toE #-}

instance SinkableE      SpecializedDictDef
instance HoistableE     SpecializedDictDef
instance AlphaEqE       SpecializedDictDef
instance AlphaHashableE SpecializedDictDef
instance SubstE Name    SpecializedDictDef

data AtomBinding (r::IR) (n::S) =
   LetBound    (DeclBinding r  n)
 | LamBound    (LamBinding  r  n)
 | PiBound     (PiBinding   r  n)
 | IxBound     (IxType      r  n)
 | MiscBound   (Type        r  n)
 | SolverBound (SolverBinding r n)
 | TopFunBound (NaryPiType r n) (TopFunBinding n)
 | TopDataBound (RepVal SimpToImpIR n)
   deriving (Show, Generic)

data TopFunBinding (n::S) =
   -- This is for functions marked `@noinline`, before we've seen their use
   -- sites and discovered what arguments we need to specialize on.
   AwaitingSpecializationArgsTopFun Int (CAtom n)
   -- Specification of a specialized function. We still need to simplify, lower,
   -- and translate-to-Imp this function. When we do that we'll store the result
   -- in the `impCache`. Or, if we're dealing with ix method specializations, we
   -- won't go all the way to Imp and we'll store the result in
   -- `ixLoweredCache`.
 | SpecializedTopFun (SpecializationSpec n)
 | LoweredTopFun     (LamExpr SimpIR n)
 | FFITopFun         (ImpFunName n)
   deriving (Show, Generic)

-- It would be nice to let bindings be parametric in the IR, but
-- there will be CoreIR top-level bindings.  We shouldn't refer
-- to those from SimpIR, but we're not checking that invariant
-- statically.
atomBindingType :: AtomBinding CoreIR n -> Type CoreIR n
atomBindingType b = case b of
  LetBound    (DeclBinding _ ty _) -> ty
  LamBound    (LamBinding  _ ty)   -> ty
  PiBound     (PiBinding   _ ty)   -> ty
  IxBound     (IxType ty _)        -> ty
  MiscBound   ty                   -> ty
  SolverBound (InfVarBound ty _)   -> ty
  SolverBound (SkolemBound ty)     -> ty
  TopFunBound ty _ -> naryPiTypeAsType ty
  TopDataBound (RepVal ty _) -> unsafeCoerceIRE ty

-- TODO: Move this to Inference!
data SolverBinding (r::IR) (n::S) =
   InfVarBound (Type r n) SrcPosCtx
 | SkolemBound (Type r n)
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
    Env (TopEnv (RecSubst emptyInFrag) mempty mempty emptyLoadedModules emptyLoadedObjects)
        emptyModuleEnv
  {-# INLINE emptyOutMap #-}

instance ExtOutMap Env (RecSubstFrag Binding)  where
  -- TODO: We might want to reorganize this struct to make this
  -- do less explicit sinking etc. It's a hot operation!
  extendOutMap (Env (TopEnv defs rules cache loadedM loadedO)
                    (ModuleEnv imports sm scs effs)) frag =
    withExtEvidence frag $ Env
      (TopEnv
        (defs  `extendRecSubst` frag)
        (sink rules)
        (sink cache)
        (sink loadedM)
        (sink loadedO))
      (ModuleEnv
        (sink imports)
        (sink sm)
        (sink scs <> bindingsFragToSynthCandidates (EnvFrag frag Nothing))
        (sink effs))
  {-# INLINE extendOutMap #-}

instance ExtOutMap Env EnvFrag where
  extendOutMap = extendEnv
  {-# INLINE extendOutMap #-}

extendEnv :: Distinct l => Env n -> EnvFrag n l -> Env l
extendEnv env (EnvFrag newEnv maybeNewEff) = do
  case extendOutMap env newEnv of
    Env envTop (ModuleEnv imports sm scs oldEff) -> do
      let newEff = case maybeNewEff of
                     Nothing  -> sink oldEff
                     Just eff -> eff
      Env envTop (ModuleEnv imports sm scs newEff)
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

naryPiTypeAsType :: HasCore r => NaryPiType r n -> Type r n
naryPiTypeAsType (NaryPiType Empty Pure resultTy) = resultTy
naryPiTypeAsType (NaryPiType (Nest b bs) effs resultTy) = case bs of
  Empty -> Pi $ PiType b effs resultTy
  Nest _ _ -> Pi $ PiType b Pure $ naryPiTypeAsType $ NaryPiType bs effs resultTy
naryPiTypeAsType _ = error "Effectful naryPiType should have at least one argument"

-- === Specialization and generalization ===

type Generalized (r::IR) (e::E) (n::S) = (Abstracted r e n, [Atom r n])
type Abstracted (r::IR) (e::E) = Abs (Nest (Binder r)) e
type AbsDict = Abstracted CoreIR (Dict CoreIR)

data SpecializedDictDef n =
   SpecializedDict
     (AbsDict n)
     -- Methods (thunked if nullary), if they're available.
     -- We create specialized dict names during simplification, but we don't
     -- actually simplify/lower them until we return to TopLevel
     (Maybe [LamExpr SimpIR n])
   deriving (Show, Generic)

-- TODO: extend with AD-oriented specializations, backend-specific specializations etc.
data SpecializationSpec (n::S) =
   AppSpecialization (AtomName CoreIR n) (Abstracted CoreIR (ListE CType) n)
   deriving (Show, Generic)


-- === BindsOneAtomName ===

-- We're really just defining this so we can have a polymorphic `binderType`.
-- But maybe we don't need one. Or maybe we can make one using just
-- `BindsOneName b AtomNameC` and `BindsEnv b`.
class BindsOneName b AtomNameC => BindsOneAtomName (r::IR) (b::B) | b -> r where
  binderType :: b n l -> Type r n
  -- binderAtomName :: b n l -> AtomName r l

bindersTypes :: (Distinct l, ProvesExt b, BindsNames b, BindsOneAtomName r b)
             => Nest b n l -> [Type r l]
bindersTypes Empty = []
bindersTypes n@(Nest b bs) = ty : bindersTypes bs
  where ty = withExtEvidence n $ sink (binderType b)

instance BindsOneAtomName r (BinderP AtomNameC (Type r)) where
  binderType (_ :> ty) = ty

instance BindsOneAtomName r (PiBinder r) where
  binderType (PiBinder _ ty _) = ty

instance BindsOneAtomName r (IxBinder r) where
  binderType (_ :> IxType ty _) = ty

instance BindsOneAtomName r (RolePiBinder r) where
  binderType (RolePiBinder _ ty _ _) = ty

toBinderNest :: BindsOneAtomName r b => Nest b n l -> Nest (Binder r) n l
toBinderNest Empty = Empty
toBinderNest (Nest b bs) = Nest (asNameBinder b :> binderType b) (toBinderNest bs)

-- === ToBinding ===

atomBindingToBinding :: AtomBinding r n -> Binding AtomNameC n
atomBindingToBinding b = AtomNameBinding $ unsafeCoerceIRE b

bindingToAtomBinding :: Binding AtomNameC n -> AtomBinding r n
bindingToAtomBinding (AtomNameBinding b) = unsafeCoerceIRE b

class (SubstE Name e, SinkableE e) => ToBinding (e::E) (c::C) | e -> c where
  toBinding :: e n -> Binding c n

instance Color c => ToBinding (Binding c) c where
  toBinding = id

instance ToBinding (AtomBinding r) AtomNameC where
  toBinding = atomBindingToBinding

instance ToBinding (DeclBinding r) AtomNameC where
  toBinding = toBinding . LetBound

instance ToBinding (LamBinding r) AtomNameC where
  toBinding = toBinding . LamBound

instance ToBinding (PiBinding r) AtomNameC where
  toBinding = toBinding . PiBound

instance ToBinding (Atom r) AtomNameC where
  toBinding = toBinding . MiscBound

instance ToBinding (SolverBinding r) AtomNameC where
  toBinding = toBinding . SolverBound @ r

instance ToBinding (IxType r) AtomNameC where
  toBinding = toBinding . IxBound

-- We don't need this for now and it seems a little annoying to implement.
-- If you ever hit this, add a Type n to BoxPtr and return it here.
instance ToBinding (BoxPtr r) AtomNameC where
  toBinding = error "not implemented!"

instance (ToBinding e1 c, ToBinding e2 c) => ToBinding (EitherE e1 e2) c where
  toBinding (LeftE  e) = toBinding e
  toBinding (RightE e) = toBinding e

-- === HasArgType ===

class HasArgType (e::E) (r::IR) | e -> r where
  argType :: e n -> Type r n

instance HasArgType (PiType r) r where
  argType (PiType (PiBinder _ ty _) _ _) = ty

instance HasArgType (TabPiType r) r where
  argType (TabPiType (_:>IxType ty _) _) = ty

instance HasArgType (TabLamExpr r) r where
  argType (TabLamExpr (_:>IxType ty _) _) = ty

-- === Pattern synonyms ===

pattern IdxRepScalarBaseTy :: ScalarBaseType
pattern IdxRepScalarBaseTy = Word32Type

-- Type used to represent indices and sizes at run-time
pattern IdxRepTy :: Type r n
pattern IdxRepTy = TC (BaseType (Scalar Word32Type))

pattern IdxRepVal :: Word32 -> Atom r n
pattern IdxRepVal x = Con (Lit (Word32Lit x))

pattern IIdxRepVal :: Word32 -> IExpr n
pattern IIdxRepVal x = ILit (Word32Lit x)

pattern IIdxRepTy :: IType
pattern IIdxRepTy = Scalar Word32Type

-- Type used to represent sum type tags at run-time
pattern TagRepTy :: Type r n
pattern TagRepTy = TC (BaseType (Scalar Word8Type))

pattern TagRepVal :: Word8 -> Atom r n
pattern TagRepVal x = Con (Lit (Word8Lit x))

pattern Word8Ty :: Type r n
pattern Word8Ty = TC (BaseType (Scalar Word8Type))

pattern ProdTy :: [Type r n] -> Type r n
pattern ProdTy tys = TC (ProdType tys)

pattern ProdVal :: [Atom r n] -> Atom r n
pattern ProdVal xs = Con (ProdCon xs)

pattern Record :: HasCore r => LabeledItems () -> [Atom r n] -> Atom r n
pattern Record ty xs = NewtypeCon (RecordCon ty) (ProdVal xs)

pattern SumTy :: [Type r n] -> Type r n
pattern SumTy cs = TC (SumType cs)

pattern SumVal :: [Type r n] -> Int -> Atom r n -> Atom r n
pattern SumVal tys tag payload = Con (SumCon tys tag payload)

pattern PairVal :: Atom r n -> Atom r n -> Atom r n
pattern PairVal x y = Con (ProdCon [x, y])

pattern PairTy :: Type r n -> Type r n -> Type r n
pattern PairTy x y = TC (ProdType [x, y])

pattern UnitVal :: Atom r n
pattern UnitVal = Con (ProdCon [])

pattern UnitTy :: Type r n
pattern UnitTy = TC (ProdType [])

pattern BaseTy :: BaseType -> Type r n
pattern BaseTy b = TC (BaseType b)

pattern PtrTy :: PtrType -> Type r n
pattern PtrTy ty = BaseTy (PtrType ty)

pattern RefTy :: Maybe (Atom r n) -> Type r n -> Type r n
pattern RefTy r a = TC (RefType r a)

pattern RawRefTy :: Type r n -> Type r n
pattern RawRefTy a = TC (RefType Nothing a)

pattern TabTy :: IxBinder r n l -> Type r l -> Type r n
pattern TabTy b body = TabPi (TabPiType b body)

pattern FinTy :: HasCore r => Atom r n -> Type r n
pattern FinTy n = NewtypeTyCon (Fin n)

pattern NatTy :: HasCore r => Type r n
pattern NatTy = NewtypeTyCon Nat

pattern NatVal :: HasCore r => Word32 -> Atom r n
pattern NatVal n = NewtypeCon NatCon (IdxRepVal n)

pattern TabVal :: HasCore r => IxBinder r n l -> Block r l -> Atom r n
pattern TabVal b body = TabLam (TabLamExpr b body)

pattern TyKind :: Kind r n
pattern TyKind = TC TypeKind

pattern EffKind :: HasCore r => Kind r n
pattern EffKind = NewtypeTyCon EffectRowKind

pattern LabeledRowKind :: HasCore r => Kind r n
pattern LabeledRowKind = NewtypeTyCon LabeledRowKindTC

pattern FinConst :: HasCore r => Word32 -> Type r n
pattern FinConst n = NewtypeTyCon (Fin (NatVal n))

pattern UnaryLamExpr :: Binder r n l -> Block r l -> LamExpr r n
pattern UnaryLamExpr b body = LamExpr (UnaryNest b) body

pattern BinaryLamExpr :: Binder r n l1 -> Binder r l1 l2 -> Block r l2 -> LamExpr r n
pattern BinaryLamExpr b1 b2 body = LamExpr (BinaryNest b1 b2) body

pattern BinaryFunTy :: PiBinder r n l1 -> PiBinder r l1 l2 -> EffectRow l2 -> Type r l2 -> Type r n
pattern BinaryFunTy b1 b2 eff ty <- Pi (PiType b1 Pure (Pi (PiType b2 eff ty)))

pattern AtomicBlock :: Atom r n -> Block r n
pattern AtomicBlock atom <- Block _ Empty atom
  where AtomicBlock atom = Block NoBlockAnn Empty atom

exprBlock :: Block r n -> Maybe (Expr r n)
exprBlock (Block _ (Nest (Let b (DeclBinding _ _ expr)) Empty) (Var n))
  | n == binderName b = Just expr
exprBlock _ = Nothing
{-# INLINE exprBlock #-}

pattern MaybeTy :: Type r n -> Type r n
pattern MaybeTy a = SumTy [UnitTy, a]

pattern NothingAtom :: Type r n -> Atom r n
pattern NothingAtom a = SumVal [UnitTy, a] 0 UnitVal

pattern JustAtom :: Type r n -> Atom r n -> Atom r n
pattern JustAtom a x = SumVal [UnitTy, a] 1 x

pattern BoolTy :: Type r n
pattern BoolTy = Word8Ty

pattern FalseAtom :: Atom r n
pattern FalseAtom = Con (Lit (Word8Lit 0))

pattern TrueAtom :: Atom r n
pattern TrueAtom = Con (Lit (Word8Lit 1))

fieldRowElemsFromList :: [FieldRowElem r n] -> FieldRowElems r n
fieldRowElemsFromList = foldr prependFieldRowElem (UnsafeFieldRowElems [])

prependFieldRowElem :: FieldRowElem r n -> FieldRowElems r n -> FieldRowElems r n
prependFieldRowElem e (UnsafeFieldRowElems els) = case e of
  DynField  _ _ -> UnsafeFieldRowElems $ e : els
  DynFields _   -> UnsafeFieldRowElems $ e : els
  StaticFields items | null items -> UnsafeFieldRowElems els
  StaticFields items -> case els of
    (StaticFields items':rest) -> UnsafeFieldRowElems $ StaticFields (items <> items') : rest
    _                          -> UnsafeFieldRowElems $ e : els

extRowAsFieldRowElems :: ExtLabeledItems (Type r n) (AtomName r n) -> FieldRowElems r n
extRowAsFieldRowElems (Ext items ext) = UnsafeFieldRowElems $ itemsEl ++ extEl
  where
    itemsEl = if null items then [] else [StaticFields items]
    extEl = case ext of Nothing -> []; Just r -> [DynFields r]

fieldRowElemsAsExtRow
  :: Alternative f => FieldRowElems r n -> f (ExtLabeledItems (Type r n) (AtomName r n))
fieldRowElemsAsExtRow (UnsafeFieldRowElems els) = case els of
  []                                -> pure $ Ext mempty Nothing
  [DynFields r]                     -> pure $ Ext mempty (Just r)
  [StaticFields items]              -> pure $ Ext items  Nothing
  [StaticFields items, DynFields r] -> pure $ Ext items  (Just r)
  _ -> empty

getAtMostSingleStatic :: NewtypeTyCon r n -> Maybe (LabeledItems (Type r n))
getAtMostSingleStatic = \case
  RecordTyCon (UnsafeFieldRowElems els) -> case els of
    [] -> Just mempty
    [StaticFields items] -> Just items
    _ -> Nothing
  _ -> Nothing

pattern StaticRecordTy :: HasCore r => LabeledItems (Type r n) -> Type r n
pattern StaticRecordTy items = NewtypeTyCon (StaticRecordTyCon items)

pattern StaticRecordTyCon :: LabeledItems (Type r n) -> NewtypeTyCon r n
pattern StaticRecordTyCon items <- (getAtMostSingleStatic -> Just items)
  where StaticRecordTyCon items = RecordTyCon (fieldRowElemsFromList [StaticFields items])

pattern RecordTyWithElems :: HasCore r => [FieldRowElem r n] -> Atom r n
pattern RecordTyWithElems elems <- RecordTy (UnsafeFieldRowElems elems)
  where RecordTyWithElems elems = RecordTy $ fieldRowElemsFromList elems

-- === Typeclass instances for Name and other Haskell libraries ===

instance GenericE AtomRules where
  type RepE AtomRules = (LiftE (Int, SymbolicZeros)) `PairE` CAtom
  fromE (CustomLinearize ni sz a) = LiftE (ni, sz) `PairE` a
  toE (LiftE (ni, sz) `PairE` a) = CustomLinearize ni sz a
instance SinkableE AtomRules
instance HoistableE AtomRules
instance AlphaEqE AtomRules
instance SubstE Name AtomRules

instance GenericE (RepVal r) where
  type RepE (RepVal r) = PairE (Type r) (ComposeE Tree IExpr)
  fromE (RepVal ty tree) = ty `PairE` ComposeE tree
  toE   (ty `PairE` ComposeE tree) = RepVal ty tree

instance SubstE (AtomSubstVal r) IExpr

instance SinkableE   (RepVal r)
instance SubstE Name (RepVal r)
instance SubstE (AtomSubstVal r) (RepVal r)
instance HoistableE  (RepVal r)
instance AlphaHashableE (RepVal r)
instance AlphaEqE (RepVal r)

instance GenericE CustomRules where
  type RepE CustomRules = ListE (PairE (AtomName CoreIR) AtomRules)
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

instance GenericE (DataDefParams r) where
  type RepE (DataDefParams r) = ListE (PairE (LiftE Arrow) (Atom r))
  fromE (DataDefParams xs) = ListE $ map toPairE $ map (onFst LiftE) xs
  {-# INLINE fromE #-}
  toE (ListE xs) = DataDefParams $ map (onFst fromLiftE) $ map fromPairE xs
  {-# INLINE toE #-}

-- We ignore the dictionary parameters because we assume coherence
instance AlphaEqE (DataDefParams r) where
  alphaEqE (DataDefParams params) (DataDefParams params') =
    alphaEqE (ListE $ plainArrows params) (ListE $ plainArrows params')

instance AlphaHashableE (DataDefParams r) where
  hashWithSaltE env salt (DataDefParams params) =
    hashWithSaltE env salt (ListE $ plainArrows params)

instance SinkableE           (DataDefParams r)
instance HoistableE          (DataDefParams r)
instance SubstE Name         (DataDefParams r)
instance SubstE (AtomSubstVal r) (DataDefParams r)

instance GenericE DataDef where
  type RepE DataDef = PairE (LiftE SourceName) (Abs (Nest (RolePiBinder CoreIR)) (ListE DataConDef))
  fromE (DataDef sourceName bs cons) = PairE (LiftE sourceName) (Abs bs (ListE cons))
  {-# INLINE fromE #-}
  toE   (PairE (LiftE sourceName) (Abs bs (ListE cons))) = DataDef sourceName bs cons
  {-# INLINE toE #-}

deriving instance Show (DataDef n)
deriving via WrapE DataDef n instance Generic (DataDef n)
instance SinkableE DataDef
instance HoistableE  DataDef
instance SubstE Name DataDef
instance SubstE (AtomSubstVal CoreIR) DataDef
instance AlphaEqE DataDef
instance AlphaHashableE DataDef

instance GenericE DataConDef where
  type RepE DataConDef = (LiftE (SourceName, [[Projection]])) `PairE` CType
  fromE (DataConDef name repTy idxs) = (LiftE (name, idxs)) `PairE` repTy
  {-# INLINE fromE #-}
  toE   ((LiftE (name, idxs)) `PairE` repTy) = DataConDef name repTy idxs
  {-# INLINE toE #-}
instance SinkableE DataConDef
instance HoistableE  DataConDef
instance SubstE Name DataConDef
instance SubstE (AtomSubstVal CoreIR) DataConDef
instance AlphaEqE DataConDef
instance AlphaHashableE DataConDef

instance GenericE (NewtypeCon r) where
  type RepE (NewtypeCon r) = EitherE5
   {- RecordCon -}    (LiftE (LabeledItems ()))
   {- VariantCon -}   (LiftE (LabeledItems ()))
   {- UserADTData -}  (DataDefName `PairE` DataDefParams r)
   {- NatCon -}       UnitE
   {- FinCon -}       (Atom r)
  fromE = \case
    RecordCon  l    -> Case0 $ LiftE l
    VariantCon l    -> Case1 $ LiftE l
    UserADTData d p -> Case2 $ d `PairE` p
    NatCon          -> Case3 UnitE
    FinCon n        -> Case4 n
  {-# INLINE fromE #-}
  toE = \case
    Case0 (LiftE l)     -> RecordCon  l
    Case1 (LiftE l)     -> VariantCon l
    Case2 (d `PairE` p) -> UserADTData d p
    Case3 UnitE         -> NatCon
    Case4 n             -> FinCon n
    _ -> error "impossible"
  {-# INLINE toE #-}

instance SinkableE      (NewtypeCon r)
instance HoistableE     (NewtypeCon r)
instance AlphaEqE       (NewtypeCon r)
instance AlphaHashableE (NewtypeCon r)
instance SubstE Name    (NewtypeCon r)
instance SubstE (AtomSubstVal r) (NewtypeCon r)

instance GenericE (NewtypeTyCon r) where
  type RepE (NewtypeTyCon r) = EitherE2
           ( EitherE5
    {- Nat -}              UnitE
    {- Fin -}              (Atom r)
    {- EffectRowKind -}    UnitE
    {- LabeledRowKindTC -} UnitE
    {- LabelType -}        UnitE
         ) ( EitherE5
    {- RecordTyCon -}      (FieldRowElems r)
    {- VariantTyCon  -}    (ExtLabeledItemsE (Type r) (AtomName r))
    {- LabelCon -}         (LiftE String)
    {- LabeledRowCon -}    (FieldRowElems r)
    {- UserADTType -}      (LiftE SourceName `PairE` DataDefName `PairE` DataDefParams r)
         )
  fromE = \case
    Nat               -> Case0 $ Case0 UnitE
    Fin n             -> Case0 $ Case1 n
    EffectRowKind     -> Case0 $ Case2 UnitE
    LabeledRowKindTC  -> Case0 $ Case3 UnitE
    LabelType         -> Case0 $ Case4 UnitE
    RecordTyCon   xs  -> Case1 $ Case0 xs
    VariantTyCon  xs  -> Case1 $ Case1 $ ExtLabeledItemsE xs
    LabelCon      s   -> Case1 $ Case2 (LiftE s)
    LabeledRowCon x   -> Case1 $ Case3 x
    UserADTType s d p -> Case1 $ Case4 (LiftE s `PairE` d `PairE` p)
  {-# INLINE fromE #-}

  toE = \case
    Case0 case0 -> case case0 of
      Case0 UnitE -> Nat
      Case1 n     -> Fin n
      Case2 UnitE -> EffectRowKind
      Case3 UnitE -> LabeledRowKindTC
      Case4 UnitE -> LabelType
      _ -> error "impossible"
    Case1 case1 -> case case1 of
      Case0 xs                            -> RecordTyCon   xs
      Case1 (ExtLabeledItemsE xs)         -> VariantTyCon  xs
      Case2 (LiftE s)                     -> LabelCon      s
      Case3 x                             -> LabeledRowCon x
      Case4 (LiftE s `PairE` d `PairE` p) -> UserADTType s d p
      _ -> error "impossible"
    _ -> error "impossible"
  {-# INLINE toE #-}

instance SinkableE      (NewtypeTyCon r)
instance HoistableE     (NewtypeTyCon r)
instance AlphaEqE       (NewtypeTyCon r)
instance AlphaHashableE (NewtypeTyCon r)
instance SubstE Name    (NewtypeTyCon r)
instance SubstE (AtomSubstVal r) (NewtypeTyCon r)

instance GenericE (BaseMonoid r) where
  type RepE (BaseMonoid r) = PairE (Atom r) (LamExpr r)
  fromE (BaseMonoid x f) = PairE x f
  {-# INLINE fromE #-}
  toE   (PairE x f) = BaseMonoid x f
  {-# INLINE toE #-}

instance SinkableE (BaseMonoid r)
instance HoistableE  (BaseMonoid r)
instance SubstE Name (BaseMonoid r)
instance SubstE (AtomSubstVal r) (BaseMonoid r)
instance AlphaEqE (BaseMonoid r)
instance AlphaHashableE (BaseMonoid r)

instance GenericE (UserEffectOp r) where
  type RepE (UserEffectOp r) = EitherE3
 {- Handle -}  (HandlerName `PairE` ListE (Atom r) `PairE` Block r)
 {- Resume -}  (Atom r `PairE` Atom r)
 {- Perform -} (Atom r `PairE` LiftE Int)
  fromE = \case
    Handle name args body -> Case0 $ name `PairE` ListE args `PairE` body
    Resume x y            -> Case1 $ x `PairE` y
    Perform x i           -> Case2 $ x `PairE` LiftE i
  {-# INLINE fromE #-}
  toE = \case
    Case0 (name `PairE` ListE args `PairE` body) -> Handle name args body
    Case1 (x `PairE` y)                          -> Resume x y
    Case2 (x `PairE` LiftE i)                    -> Perform x i
    _ -> error "impossible"
  {-# INLINE toE #-}


instance SinkableE (UserEffectOp r)
instance HoistableE  (UserEffectOp r)
instance SubstE Name (UserEffectOp r)
instance SubstE (AtomSubstVal r) (UserEffectOp r)
instance AlphaEqE (UserEffectOp r)
instance AlphaHashableE (UserEffectOp r)

instance GenericE (DAMOp r) where
  type RepE (DAMOp r) = EitherE5
  {- Seq -}            (LiftE Direction `PairE` IxDict r `PairE` Atom r `PairE` LamExpr r)
  {- RememberDest -}   (Atom r `PairE` LamExpr r)
  {- AllocDest -}      (Atom r)
  {- Place -}          (Atom r `PairE` Atom r)
  {- Freeze -}         (Atom r)
  fromE = \case
    Seq d x y z      -> Case0 $ LiftE d `PairE` x `PairE` y `PairE` z
    RememberDest x y -> Case1 (x `PairE` y)
    AllocDest x      -> Case2 x
    Place x y        -> Case3 (x `PairE` y)
    Freeze x         -> Case4 x
  {-# INLINE fromE #-}
  toE = \case
    Case0 (LiftE d `PairE` x `PairE` y `PairE` z) -> Seq d x y z
    Case1 (x `PairE` y)                           -> RememberDest x y
    Case2 x                                       -> AllocDest x
    Case3 (x `PairE` y)                           -> Place x y
    Case4 x                                       -> Freeze x
    _ -> error "impossible"
  {-# INLINE toE #-}

instance SinkableE (DAMOp r)
instance HoistableE  (DAMOp r)
instance SubstE Name (DAMOp r)
instance SubstE (AtomSubstVal r) (DAMOp r)
instance AlphaEqE (DAMOp r)
instance AlphaHashableE (DAMOp r)

instance GenericE (Hof r) where
  type RepE (Hof r) = EitherE2
    (EitherE6
  {- For -}       (LiftE ForAnn `PairE` IxDict r `PairE` LamExpr r)
  {- While -}     (Block r)
  {- RunReader -} (Atom r `PairE` LamExpr r)
  {- RunWriter -} (MaybeE (Atom r) `PairE` BaseMonoid r `PairE` LamExpr r)
  {- RunState -}  (MaybeE (Atom r) `PairE` Atom r `PairE` LamExpr r)
  {- RunIO -}     (Block r)
    ) (EitherE4
  {- RunInit -}        (Block r)
  {- CatchException -} (WhenE (HasCore' r) (Block r))
  {- Linearize -}      (WhenE (HasCore' r ) (LamExpr r))
  {- Transpose -}      (WhenE (HasCore' r ) (LamExpr r)))

  fromE = \case
    For ann d body      -> Case0 (Case0 (LiftE ann `PairE` d `PairE` body))
    While body          -> Case0 (Case1 body)
    RunReader x body    -> Case0 (Case2 (x `PairE` body))
    RunWriter d bm body -> Case0 (Case3 (toMaybeE d `PairE` bm `PairE` body))
    RunState  d x body  -> Case0 (Case4 (toMaybeE d `PairE` x `PairE` body))
    RunIO body          -> Case0 (Case5 body)
    RunInit body        -> Case1 (Case0 body)
    CatchException body -> Case1 (Case1 (WhenE body))
    Linearize body      -> Case1 (Case2 (WhenE body))
    Transpose body      -> Case1 (Case3 (WhenE body))
  {-# INLINE fromE #-}
  toE = \case
    Case0 hof -> case hof of
      Case0 (LiftE ann `PairE` d `PairE` body) -> For ann d body
      Case1 body                        -> While body
      Case2 (x `PairE` body)            -> RunReader x body
      Case3 (d `PairE` bm `PairE` body) -> RunWriter (fromMaybeE d) bm body
      Case4 (d `PairE` x `PairE` body)  -> RunState  (fromMaybeE d) x body
      Case5 body                        -> RunIO     body
      _ -> error "impossible"
    Case1 hof -> case hof of
      Case0 body -> RunInit body
      Case1 (WhenE body) -> CatchException body
      Case2 (WhenE body) -> Linearize body
      Case3 (WhenE body) -> Transpose body
      _ -> error "impossible"
    _ -> error "impossible"
  {-# INLINE toE #-}

instance SinkableE (Hof r)
instance HoistableE  (Hof r)
instance SubstE Name (Hof r)
instance SubstE (AtomSubstVal r) (Hof r)
instance AlphaEqE (Hof r)
instance AlphaHashableE (Hof r)

instance GenericE (RefOp r) where
  type RepE (RefOp r) =
    EitherE6
      UnitE                         -- MAsk
      (BaseMonoid r `PairE` Atom r) -- MExtend
      UnitE                         -- MGet
      (Atom r)                      -- MPut
      (Atom r)                      -- IndexRef
      (LiftE Int)                   -- ProjRef
  fromE = \case
    MAsk         -> Case0 UnitE
    MExtend bm x -> Case1 (bm `PairE` x)
    MGet         -> Case2 UnitE
    MPut x       -> Case3 x
    IndexRef x   -> Case4 x
    ProjRef i    -> Case5 (LiftE i)
  {-# INLINE fromE #-}
  toE = \case
    Case0 UnitE          -> MAsk
    Case1 (bm `PairE` x) -> MExtend bm x
    Case2 UnitE          -> MGet
    Case3 x              -> MPut x
    Case4 x              -> IndexRef x
    Case5 (LiftE i)      -> ProjRef i
    _ -> error "impossible"
  {-# INLINE toE #-}

instance SinkableE (RefOp r)
instance HoistableE  (RefOp r)
instance SubstE Name (RefOp r)
instance SubstE (AtomSubstVal r) (RefOp r)
instance AlphaEqE (RefOp r)
instance AlphaHashableE (RefOp r)

instance GenericE (FieldRowElem r) where
  type RepE (FieldRowElem r) = EitherE3 (ExtLabeledItemsE (Type r) UnitE) (AtomName r `PairE` (Type r)) (AtomName r)
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
instance SinkableE      (FieldRowElem r)
instance HoistableE     (FieldRowElem r)
instance SubstE Name    (FieldRowElem r)
instance AlphaEqE       (FieldRowElem r)
instance AlphaHashableE (FieldRowElem r)

instance GenericE (FieldRowElems r) where
  type RepE (FieldRowElems r) = ListE (FieldRowElem r)
  fromE = ListE . fromFieldRowElems
  {-# INLINE fromE #-}
  toE = fieldRowElemsFromList . fromListE
  {-# INLINE toE #-}
instance SinkableE   (FieldRowElems r)
instance HoistableE  (FieldRowElems r)
instance SubstE Name (FieldRowElems r)
instance AlphaEqE    (FieldRowElems r)
instance AlphaHashableE (FieldRowElems r)
instance SubstE (AtomSubstVal r) (FieldRowElems r) where
  substE :: forall i o. Distinct o => (Scope o, Subst (AtomSubstVal r) i o) -> FieldRowElems r i -> FieldRowElems r o
  substE env (UnsafeFieldRowElems els) = fieldRowElemsFromList $ foldMap substItem els
    where
      substItem = \case
        DynField v ty -> case snd env ! v of
          SubstVal (NewtypeTyCon (LabelCon l)) -> [StaticFields $ labeledSingleton l ty']
          SubstVal (Var v') -> [DynField v' ty']
          Rename v'         -> [DynField v' ty']
          _ -> error "ill-typed substitution"
          where ty' = substE env ty
        DynFields v -> case snd env ! v of
          SubstVal (NewtypeTyCon (LabeledRowCon items)) -> fromFieldRowElems items
          SubstVal (Var v') -> [DynFields v']
          Rename v'         -> [DynFields v']
          _ -> error "ill-typed substitution"
        StaticFields items -> [StaticFields items']
          where ExtLabeledItemsE (NoExt items') = substE env
                  (ExtLabeledItemsE (NoExt items) :: ExtLabeledItemsE (Atom r) (AtomName r) i)

newtype ExtLabeledItemsE (e1::E) (e2::E) (n::S) =
  ExtLabeledItemsE
   { fromExtLabeledItemsE :: ExtLabeledItems (e1 n) (e2 n) }
   deriving (Show, Generic)
instance (Store (e1 n), Store (e2 n)) => Store (ExtLabeledItemsE e1 e2 n)

instance GenericE (Atom r) where
  -- As tempting as it might be to reorder cases here, the current permutation
  -- was chosen as to make GHC inliner confident enough to simplify through
  -- toE/fromE entirely. If you wish to modify the order, please consult the
  -- GHC Core dump to make sure you haven't regressed this optimization.
  type RepE (Atom r) = EitherE6
              (EitherE2
                   -- We isolate those few cases (and reorder them
                   -- compared to the data definition) because they need special
                   -- handling when you substitute with atoms. The rest just act
                   -- like containers
  {- Var -}        (AtomName r)
  {- ProjectElt -} ( LiftE (NE.NonEmpty Projection) `PairE` AtomName r)
            ) (EitherE4
  {- Lam -}        (WhenE (HasCore' r) (LamExpr r `PairE` LiftE Arrow `PairE` EffAbs))
  {- Pi -}         (WhenE (HasCore' r) (PiType r))
  {- TabLam -}     (WhenE (HasCore' r) (TabLamExpr r))
  {- TabPi -}      (TabPiType r)
            ) (EitherE4
  {- DepPairTy -}  (DepPairType r)
  {- DepPair -}    ( Atom r `PairE` Atom r `PairE` DepPairType r)
  {- DictCon  -}   (WhenE (HasCore' r) (DictExpr r))
  {- DictTy  -}    (WhenE (HasCore' r) (DictType r))
            ) (EitherE2
  {- NewtypeCon -}     (WhenE (HasCore' r) (NewtypeCon r `PairE` Atom r))
  {- NewtypeTyCon -}   (WhenE (HasCore' r) (NewtypeTyCon r))
            ) (EitherE6
  {- Con -}        (ComposeE (PrimCon r) (Atom r))
  {- TC -}         (ComposeE (PrimTC  r) (Atom r))
  {- Eff -}        ( WhenE (HasCore' r) EffectRow)
  {- PtrVar -}     PtrName
  {- ACase -}      ( WhenE (HasCore' r) (Atom r `PairE` ListE (AltP r (Atom r)) `PairE` Type r))
  {- RepValAtom -} ( WhenE (Sat' r (Is SimpToImpIR)) (RepVal r))
            ) (
  {- SimpInCore -} (LiftE [Projection] `PairE` MaybeE (Type r) `PairE` LiftE [Projection] `PairE` AtomName SimpIR)
              )
  fromE atom = case atom of
    Var v -> Case0 (Case0 v)
    ProjectElt idxs x -> Case0 (Case1 (PairE (LiftE idxs) x))
    Lam lamExpr arr eff -> Case1 (Case0 (WhenE (lamExpr `PairE` LiftE arr `PairE` eff)))
    Pi  piExpr  -> Case1 (Case1 (WhenE piExpr))
    TabLam lamExpr -> Case1 (Case2 (WhenE lamExpr))
    TabPi  piExpr  -> Case1 (Case3 piExpr)
    DepPairTy ty -> Case2 (Case0 ty)
    DepPair l r ty -> Case2 (Case1 $ l `PairE` r `PairE` ty)
    DictCon d      -> Case2 $ Case2 $ WhenE d
    DictTy  d      -> Case2 $ Case3 $ WhenE d
    NewtypeCon c x -> Case3 $ Case0 $ WhenE (c `PairE` x)
    NewtypeTyCon t -> Case3 $ Case1 $ WhenE t
    Con con -> Case4 $ Case0 $ ComposeE con
    TC  con -> Case4 $ Case1 $ ComposeE con
    Eff effs -> Case4 $ Case2 $ WhenE effs
    PtrVar v -> Case4 $ Case3 $ v
    ACase scrut alts ty -> Case4 $ Case4 $ WhenE $ scrut `PairE` ListE alts `PairE` ty
    RepValAtom rv  -> Case4 $ Case5 $ WhenE $ rv
    SimpInCore p1 t p2 x -> Case5 $ LiftE p1 `PairE` toMaybeE t `PairE` LiftE p2`PairE` x
  {-# INLINE fromE #-}

  toE atom = case atom of
    Case0 val -> case val of
      Case0 v -> Var v
      Case1 (PairE (LiftE idxs) x) -> ProjectElt idxs x
      _ -> error "impossible"
    Case1 val -> case val of
      Case0 (WhenE (lamExpr `PairE` LiftE arr `PairE` effs)) -> Lam lamExpr arr effs
      Case1 (WhenE piExpr)  -> Pi  piExpr
      Case2 (WhenE lamExpr) -> TabLam lamExpr
      Case3 piExpr  -> TabPi  piExpr
      _ -> error "impossible"
    Case2 val -> case val of
      Case0 ty      -> DepPairTy ty
      Case1 (l `PairE` r `PairE` ty) -> DepPair l r ty
      Case2 (WhenE d) -> DictCon d
      Case3 (WhenE d) -> DictTy  d
      _ -> error "impossible"
    Case3 val -> case val of
      Case0 (WhenE (c `PairE` x)) -> NewtypeCon c x
      Case1 (WhenE t)             -> NewtypeTyCon t
      _ -> error "impossible"
    Case4 val -> case val of
      Case0 (ComposeE con) -> Con con
      Case1 (ComposeE con) -> TC con
      Case2 (WhenE effs) -> Eff effs
      Case3 v -> PtrVar v
      Case4 (WhenE (scrut `PairE` ListE alts `PairE` ty)) -> ACase scrut alts ty
      Case5 (WhenE rv) -> RepValAtom rv
      _ -> error "impossible"
    Case5 (LiftE p1 `PairE` t `PairE` LiftE p2 `PairE` x) -> SimpInCore p1 (fromMaybeE t) p2 x
    _ -> error "impossible"
  {-# INLINE toE #-}

instance SinkableE   (Atom r)
instance HoistableE  (Atom r)
instance AlphaEqE    (Atom r)
instance AlphaHashableE (Atom r)
instance SubstE Name (Atom r)

-- TODO: special handling of ACase too
instance SubstE (AtomSubstVal r) (Atom r) where
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
    -- SimpInCore
    Case5 (t `PairE` x) ->
      toE $ Case5 $ substE (scope, env) t `PairE` x'
      -- TODO: this shouldn't be necessary once we put IR tags on local names
      where (Var x') = unsafeCoerceIRE @SimpIR $ substE (scope, env) (unsafeCoerceIRE @r (Var x))
    Case6 rest -> (toE . Case6) $ substE (scope, env) rest
    Case7 rest -> (toE . Case7) $ substE (scope, env) rest

getProjection :: HasCallStack => [Projection] -> Atom r n -> Atom r n
getProjection [] a = a
getProjection (i:is) a = case getProjection is a of
  Var name -> ProjectElt (i NE.:| []) name
  ProjectElt idxs' a' -> ProjectElt (NE.cons i idxs') a'
  Con (ProdCon xs) -> xs !! iProd
  DepPair l _ _ | iProd == 0 -> l
  DepPair _ r _ | iProd == 1 -> r
  ACase scrut alts resultTy -> ACase scrut alts' resultTy'
    where
      alts' = alts <&> \(Abs bs body) -> Abs bs $ getProjection [i] body
      resultTy' = case resultTy of
        ProdTy tys -> tys !! iProd
        -- We can't handle all cases here because we'll end up needing access to
        -- the env. This `ProjectElt` is a steady source of issues. Maybe we can
        -- do away with it.
        _ -> error "oops"
  NewtypeCon _ x | i == UnwrapNewtype -> x
  SimpInCore is' ty p v -> SimpInCore (i:is') ty p v
  RepValAtom (RepVal (ProdTy tys) (Branch xs)) -> RepValAtom $ RepVal (tys!!iProd) (xs!!iProd)
  a' -> error $ "Not a valid projection: " ++ show i ++ " of " ++ show a'
  where
    iProd = case i of
      ProjectProduct i' -> i'
      _ -> error $ "Not a product projection"

instance GenericE (Expr r) where
  type RepE (Expr r) = EitherE2
    ( EitherE5
 {- App -}    (Atom r `PairE` Atom r `PairE` ListE (Atom r))
 {- TabApp -} (Atom r `PairE` Atom r `PairE` ListE (Atom r))
 {- Case -}   (Atom r `PairE` ListE (Alt r) `PairE` Type r `PairE` EffectRow)
 {- Atom -}   (Atom r)
 {- Hof -}    (Hof r)
    )
    ( EitherE7
 {- TabCon -}          (Type r `PairE` ListE (Atom r))
 {- RefOp -}           (Atom r `PairE` RefOp r)
 {- PrimOp -}          (ComposeE PrimOp (Atom r))
 {- UserEffectOp -}    (WhenE (HasCore' r) (UserEffectOp r))
 {- ProjMethod -}      (WhenE (HasCore' r) (Atom r `PairE` LiftE Int))
 {- RecordVariantOp -} (WhenE (HasCore' r) (ComposeE RecordVariantOp (Atom r)))
 {- DAMOp -}           (WhenE (IsLowered' r) (DAMOp r)))


  fromE = \case
    App    f (x:|xs)   -> Case0 $ Case0 (f `PairE` x `PairE` ListE xs)
    TabApp f (x:|xs)   -> Case0 $ Case1 (f `PairE` x `PairE` ListE xs)
    Case e alts ty eff -> Case0 $ Case2 (e `PairE` ListE alts `PairE` ty `PairE` eff)
    Atom x             -> Case0 $ Case3 (x)
    Hof hof            -> Case0 $ Case4 hof
    TabCon ty xs       -> Case1 $ Case0 (ty `PairE` ListE xs)
    RefOp ref op       -> Case1 $ Case1 (ref `PairE` op)
    PrimOp op          -> Case1 $ Case2 (ComposeE op)
    UserEffectOp op    -> Case1 $ Case3 (WhenE op)
    ProjMethod d i     -> Case1 $ Case4 (WhenE (d `PairE` LiftE i))
    RecordVariantOp op -> Case1 $ Case5 (WhenE (ComposeE op))
    DAMOp op           -> Case1 $ Case6 (WhenE op)
  {-# INLINE fromE #-}
  toE = \case
    Case0 case0 -> case case0 of
      Case0 (f `PairE` x `PairE` ListE xs)                -> App    f (x:|xs)
      Case1 (f `PairE` x `PairE` ListE xs)                -> TabApp f (x:|xs)
      Case2 (e `PairE` ListE alts `PairE` ty `PairE` eff) -> Case e alts ty eff
      Case3 (x)                                           -> Atom x
      Case4 hof                                           -> Hof hof
      _ -> error "impossible"
    Case1 case1 -> case case1 of
      Case0 (ty `PairE` ListE xs) -> TabCon ty xs
      Case1 (ref `PairE` op)      -> RefOp ref op
      Case2 (ComposeE op)         -> PrimOp op
      Case3 (WhenE op)            -> UserEffectOp op
      Case4 (WhenE (d `PairE` LiftE i)) -> ProjMethod d i
      Case5 (WhenE (ComposeE op)) -> RecordVariantOp op
      Case6 (WhenE op)            -> DAMOp op
      _ -> error "impossible"
    _ -> error "impossible"
  {-# INLINE toE #-}

instance SinkableE      (Expr r)
instance HoistableE     (Expr r)
instance AlphaEqE       (Expr r)
instance AlphaHashableE (Expr r)
instance SubstE Name    (Expr r)
instance SubstE (AtomSubstVal r) (Expr r)

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

instance SubstE (AtomSubstVal r) (ExtLabeledItemsE (Atom r) (AtomName r)) where
  substE (scope, env) (ExtLabeledItemsE (Ext items maybeExt)) = do
    let items' = fmap (substE (scope, env)) items
    let ext = case maybeExt of
                Nothing -> NoExt NoLabeledItems
                Just v -> case env ! v of
                  Rename        v'  -> Ext NoLabeledItems $ Just v'
                  SubstVal (Var v') -> Ext NoLabeledItems $ Just v'
                  SubstVal (NewtypeTyCon (LabeledRowCon row)) -> case fieldRowElemsAsExtRow row of
                    Just row' -> row'
                    Nothing -> error "Not implemented: unrepresentable subst of ExtLabeledItems"
                  _ -> error "Not a valid labeled row substitution"
    ExtLabeledItemsE $ prefixExtLabeledItems items' ext

instance GenericE (Block r) where
  type RepE (Block r) = PairE (MaybeE (PairE (Type r) EffectRow)) (Abs (Nest (Decl r)) (Atom r))
  fromE (Block (BlockAnn ty effs) decls result) = PairE (JustE (PairE ty effs)) (Abs decls result)
  fromE (Block NoBlockAnn Empty result) = PairE NothingE (Abs Empty result)
  fromE _ = error "impossible"
  {-# INLINE fromE #-}
  toE   (PairE (JustE (PairE ty effs)) (Abs decls result)) = Block (BlockAnn ty effs) decls result
  toE   (PairE NothingE (Abs Empty result)) = Block NoBlockAnn Empty result
  toE   _ = error "impossible"
  {-# INLINE toE #-}

deriving instance Show (BlockAnn r n l)

instance SinkableE      (Block r)
instance HoistableE     (Block r)
instance AlphaEqE       (Block r)
instance AlphaHashableE (Block r)
instance SubstE Name    (Block r)
instance SubstE (AtomSubstVal r) (Block r)
deriving instance Show (Block r n)
deriving via WrapE (Block r) n instance Generic (Block r n)

instance GenericE (BoxPtr r) where
  type RepE (BoxPtr r) = Atom r `PairE` Block r
  fromE (BoxPtr p s) = p `PairE` s
  {-# INLINE fromE #-}
  toE (p `PairE` s) = BoxPtr p s
  {-# INLINE toE #-}
instance SinkableE  (BoxPtr r)
instance HoistableE (BoxPtr r)
instance AlphaEqE   (BoxPtr r)
instance AlphaHashableE (BoxPtr r)
instance SubstE Name (BoxPtr r)
instance SubstE (AtomSubstVal r) (BoxPtr r)

instance GenericB (NonDepNest r ann) where
  type RepB (NonDepNest r ann) = (LiftB (ListE ann)) `PairB` Nest AtomNameBinder
  fromB (NonDepNest bs anns) = LiftB (ListE anns) `PairB` bs
  {-# INLINE fromB #-}
  toB (LiftB (ListE anns) `PairB` bs) = NonDepNest bs anns
  {-# INLINE toB #-}
instance ProvesExt (NonDepNest r ann)
instance BindsNames (NonDepNest r ann)
instance SinkableE ann => SinkableB (NonDepNest r ann)
instance HoistableE ann => HoistableB (NonDepNest r ann)
instance (SubstE Name ann, SinkableE ann) => SubstB Name (NonDepNest r ann)
instance (SubstE (AtomSubstVal r) ann, SinkableE ann) => SubstB (AtomSubstVal r) (NonDepNest r ann)
instance AlphaEqE ann => AlphaEqB (NonDepNest r ann)
instance AlphaHashableE ann => AlphaHashableB (NonDepNest r ann)
deriving instance (Show (ann n)) => Show (NonDepNest r ann n l)

instance GenericB SuperclassBinders where
  type RepB SuperclassBinders = PairB (LiftB (ListE CType)) (Nest AtomNameBinder)
  fromB (SuperclassBinders bs tys) = PairB (LiftB (ListE tys)) bs
  toB   (PairB (LiftB (ListE tys)) bs) = SuperclassBinders bs tys

instance BindsNameList SuperclassBinders AtomNameC where
  bindNameList (SuperclassBinders bs _) xs = bindNameList bs xs

instance ProvesExt   SuperclassBinders
instance BindsNames  SuperclassBinders
instance SinkableB   SuperclassBinders
instance HoistableB  SuperclassBinders
instance SubstB Name SuperclassBinders
instance SubstB (AtomSubstVal CoreIR) SuperclassBinders
instance AlphaEqB SuperclassBinders
instance AlphaHashableB SuperclassBinders

instance GenericE ClassDef where
  type RepE ClassDef =
    LiftE (SourceName, [SourceName])
     `PairE` Abs (Nest (RolePiBinder CoreIR)) (Abs SuperclassBinders (ListE MethodType))
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
instance SubstE (AtomSubstVal CoreIR) ClassDef
deriving instance Show (ClassDef n)
deriving via WrapE ClassDef n instance Generic (ClassDef n)

instance GenericE InstanceDef where
  type RepE InstanceDef =
    ClassName `PairE` Abs (Nest (RolePiBinder CoreIR)) (ListE CType `PairE` InstanceBody)
  fromE (InstanceDef name bs params body) =
    name `PairE` Abs bs (ListE params `PairE` body)
  toE (name `PairE` Abs bs (ListE params `PairE` body)) =
    InstanceDef name bs params body

instance SinkableE InstanceDef
instance HoistableE  InstanceDef
instance AlphaEqE InstanceDef
instance AlphaHashableE InstanceDef
instance SubstE Name InstanceDef
instance SubstE (AtomSubstVal CoreIR) InstanceDef
deriving instance Show (InstanceDef n)
deriving via WrapE InstanceDef n instance Generic (InstanceDef n)

instance GenericE InstanceBody where
  type RepE InstanceBody = ListE CAtom `PairE` ListE (Block CoreIR)
  fromE (InstanceBody scs methods) = ListE scs `PairE` ListE methods
  toE   (ListE scs `PairE` ListE methods) = InstanceBody scs methods

instance SinkableE InstanceBody
instance HoistableE  InstanceBody
instance AlphaEqE InstanceBody
instance AlphaHashableE InstanceBody
instance SubstE Name InstanceBody
instance SubstE (AtomSubstVal CoreIR) InstanceBody

instance GenericE MethodType where
  type RepE MethodType = PairE (LiftE [Bool]) CType
  fromE (MethodType explicit ty) = PairE (LiftE explicit) ty
  toE   (PairE (LiftE explicit) ty) = MethodType explicit ty

instance SinkableE      MethodType
instance HoistableE     MethodType
instance AlphaEqE       MethodType
instance AlphaHashableE MethodType
instance SubstE Name MethodType
instance SubstE (AtomSubstVal CoreIR) MethodType

instance GenericE (DictType r) where
  type RepE (DictType r) = LiftE SourceName `PairE` ClassName `PairE` ListE (Type r)
  fromE (DictType sourceName className params) =
    LiftE sourceName `PairE` className `PairE` ListE params
  toE (LiftE sourceName `PairE` className `PairE` ListE params) =
    DictType sourceName className params

instance SinkableE           (DictType r)
instance HoistableE          (DictType r)
instance AlphaEqE            (DictType r)
instance AlphaHashableE      (DictType r)
instance SubstE Name         (DictType r)
instance SubstE (AtomSubstVal r) (DictType r)

instance GenericE (DictExpr r) where
  type RepE (DictExpr r) =
    EitherE4
 {- InstanceDict -}      (PairE InstanceName (ListE (Atom r)))
 {- InstantiatedGiven -} (PairE (Atom r) (ListE (Atom r)))
 {- SuperclassProj -}    (PairE (Atom r) (LiftE Int))
 {- IxFin -}             (Atom r)
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

instance SinkableE           (DictExpr r)
instance HoistableE          (DictExpr r)
instance AlphaEqE            (DictExpr r)
instance AlphaHashableE      (DictExpr r)
instance SubstE Name         (DictExpr r)
instance SubstE (AtomSubstVal r) (DictExpr r)

instance GenericE Cache where
  type RepE Cache =
            EMap SpecializationSpec (AtomName CoreIR)
    `PairE` EMap AbsDict SpecDictName
    `PairE` EMap (AtomName CoreIR) ImpFunName
    `PairE` EMap ImpFunName FunObjCodeName
    `PairE` LiftE (M.Map ModuleSourceName (FileHash, [ModuleSourceName]))
    `PairE` ListE (        LiftE ModuleSourceName
                   `PairE` LiftE FileHash
                   `PairE` ListE ModuleName
                   `PairE` ModuleName)
  fromE (Cache x y z w parseCache evalCache) =
    x `PairE` y `PairE` z `PairE` w `PairE` LiftE parseCache `PairE`
      ListE [LiftE sourceName `PairE` LiftE hashVal `PairE` ListE deps `PairE` result
             | (sourceName, ((hashVal, deps), result)) <- M.toList evalCache ]
  {-# INLINE fromE #-}
  toE   (x `PairE` y `PairE` z `PairE` w `PairE` LiftE parseCache `PairE` ListE evalCache) =
    Cache x y z w parseCache
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
  mempty = Cache mempty mempty mempty mempty mempty mempty
  mappend = (<>)

instance Semigroup (Cache n) where
  -- right-biased instead of left-biased
  Cache x1 x2 x3 x4 x5 x6 <> Cache y1 y2 y3 y4 y5 y6 =
    Cache (y1<>x1) (y2<>x2) (y3<>x3) (y4<>x4) (y5<>x5) (y6<>x6)

instance GenericE (LamBinding r) where
  type RepE (LamBinding r) = PairE (LiftE Arrow) (Type r)
  fromE (LamBinding arr ty) = PairE (LiftE arr) ty
  {-# INLINE fromE #-}
  toE   (PairE (LiftE arr) ty) = LamBinding arr ty
  {-# INLINE toE #-}

instance SinkableE     (LamBinding r)
instance HoistableE    (LamBinding r)
instance SubstE Name   (LamBinding r)
instance SubstE (AtomSubstVal r) (LamBinding r)
instance AlphaEqE       (LamBinding r)
instance AlphaHashableE (LamBinding r)

instance GenericE (LamExpr r) where
  type RepE (LamExpr r) = Abs (Nest (Binder r)) (Block r)
  fromE (LamExpr b block) = Abs b block
  {-# INLINE fromE #-}
  toE   (Abs b block) = LamExpr b block
  {-# INLINE toE #-}

instance SinkableE      (LamExpr r)
instance HoistableE     (LamExpr r)
instance AlphaEqE       (LamExpr r)
instance AlphaHashableE (LamExpr r)
instance SubstE Name    (LamExpr r)
instance SubstE (AtomSubstVal r) (LamExpr r)
deriving instance Show (LamExpr r n)
deriving via WrapE (LamExpr r) n instance Generic (LamExpr r n)

instance GenericE (TabLamExpr r) where
  type RepE (TabLamExpr r) = Abs (IxBinder r) (Block r)
  fromE (TabLamExpr b block) = Abs b block
  {-# INLINE fromE #-}
  toE   (Abs b block) = TabLamExpr b block
  {-# INLINE toE #-}

instance SinkableE      (TabLamExpr r)
instance HoistableE     (TabLamExpr r)
instance AlphaEqE       (TabLamExpr r)
instance AlphaHashableE (TabLamExpr r)
instance SubstE Name    (TabLamExpr r)
instance SubstE (AtomSubstVal r) (TabLamExpr r)
deriving instance Show (TabLamExpr r n)
deriving via WrapE (TabLamExpr r) n instance Generic (TabLamExpr r n)

instance GenericE (PiBinding r) where
  type RepE (PiBinding r) = PairE (LiftE Arrow) (Type r)
  fromE (PiBinding arr ty) = PairE (LiftE arr) ty
  {-# INLINE fromE #-}
  toE   (PairE (LiftE arr) ty) = PiBinding arr ty
  {-# INLINE toE #-}

instance SinkableE   (PiBinding r)
instance HoistableE  (PiBinding r)
instance SubstE Name (PiBinding r)
instance SubstE (AtomSubstVal r) (PiBinding r)
instance AlphaEqE (PiBinding r)
instance AlphaHashableE (PiBinding r)

instance GenericB (PiBinder r) where
  type RepB (PiBinder r) = BinderP AtomNameC (PairE (Type r) (LiftE Arrow))
  fromB (PiBinder b ty arr) = b :> PairE ty (LiftE arr)
  toB   (b :> PairE ty (LiftE arr)) = PiBinder b ty arr

instance BindsAtMostOneName (PiBinder r) AtomNameC where
  PiBinder b _ _ @> x = b @> x
  {-# INLINE (@>) #-}

instance BindsOneName (PiBinder r) AtomNameC where
  binderName (PiBinder b _ _) = binderName b
  {-# INLINE binderName #-}

instance HasNameHint (PiBinder r n l) where
  getNameHint (PiBinder b _ _) = getNameHint b
  {-# INLINE getNameHint #-}

instance ProvesExt   (PiBinder r)
instance BindsNames  (PiBinder r)
instance SinkableB   (PiBinder r)
instance HoistableB  (PiBinder r)
instance SubstB Name (PiBinder r)
instance SubstB (AtomSubstVal r) (PiBinder r)
instance AlphaEqB (PiBinder r)
instance AlphaHashableB (PiBinder r)

instance GenericE (PiType r) where
  type RepE (PiType r) = Abs (PiBinder r) (PairE EffectRow (Type r))
  fromE (PiType b eff resultTy) = Abs b (PairE eff resultTy)
  {-# INLINE fromE #-}
  toE   (Abs b (PairE eff resultTy)) = PiType b eff resultTy
  {-# INLINE toE #-}

instance SinkableE      (PiType r)
instance HoistableE     (PiType r)
instance AlphaEqE       (PiType r)
instance AlphaHashableE (PiType r)
instance SubstE Name    (PiType r)
instance SubstE (AtomSubstVal r) (PiType r)
deriving instance Show (PiType r n)
deriving via WrapE (PiType r) n instance Generic (PiType r n)

instance GenericB (RolePiBinder r) where
  type RepB (RolePiBinder r) = BinderP AtomNameC (PairE (Type r) (LiftE (Arrow, ParamRole)))
  fromB (RolePiBinder b ty arr role) = b :> PairE ty (LiftE (arr, role))
  {-# INLINE fromB #-}
  toB   (b :> PairE ty (LiftE (arr, role))) = RolePiBinder b ty arr role
  {-# INLINE toB #-}

instance HasNameHint (RolePiBinder r n l) where
  getNameHint (RolePiBinder b _ _ _) = getNameHint b
  {-# INLINE getNameHint #-}

instance BindsAtMostOneName (RolePiBinder r) AtomNameC where
  RolePiBinder b _ _ _ @> x = b @> x

instance BindsOneName (RolePiBinder r) AtomNameC where
  binderName (RolePiBinder b _ _ _) = binderName b

instance ProvesExt   (RolePiBinder r)
instance BindsNames  (RolePiBinder r)
instance SinkableB   (RolePiBinder r)
instance HoistableB  (RolePiBinder r)
instance SubstB Name (RolePiBinder r)
instance SubstB (AtomSubstVal r) (RolePiBinder r)
instance AlphaEqB (RolePiBinder r)
instance AlphaHashableB (RolePiBinder r)

instance GenericE (IxDict r) where
  type RepE (IxDict r) =
    EitherE3
      (WhenE (HasCore' r) (Atom r))
      (Atom r)
      (Type r `PairE` SpecDictName `PairE` ListE (Atom r))
  fromE = \case
    IxDictAtom x -> Case0 $ WhenE x
    IxDictFin n  -> Case1 $ n
    IxDictSpecialized t d xs -> Case2 $ t `PairE` d `PairE` ListE xs
  {-# INLINE fromE #-}
  toE = \case
    Case0 (WhenE x)            -> IxDictAtom x
    Case1 (n)                  -> IxDictFin n
    Case2 (t `PairE` d `PairE` ListE xs) -> IxDictSpecialized t d xs
    _ -> error "impossible"
  {-# INLINE toE #-}

instance SinkableE   (IxDict r)
instance HoistableE  (IxDict r)
instance SubstE Name (IxDict r)
instance SubstE (AtomSubstVal r) (IxDict r)
instance AlphaEqE       (IxDict r)
instance AlphaHashableE (IxDict r)

instance GenericE (IxType r) where
  type RepE (IxType r) = PairE (Type r) (IxDict r)
  fromE (IxType ty d) = PairE ty d
  {-# INLINE fromE #-}
  toE   (PairE ty d) = IxType ty d
  {-# INLINE toE #-}

instance SinkableE   (IxType r)
instance HoistableE  (IxType r)
instance SubstE Name (IxType r)
instance SubstE (AtomSubstVal r) (IxType r)

instance AlphaEqE (IxType r) where
  alphaEqE (IxType t1 _) (IxType t2 _) = alphaEqE t1 t2

instance AlphaHashableE (IxType r) where
  hashWithSaltE env salt (IxType t _) = hashWithSaltE env salt t

instance GenericE (TabPiType r) where
  type RepE (TabPiType r) = Abs (IxBinder r) (Type r)
  fromE (TabPiType b resultTy) = Abs b resultTy
  {-# INLINE fromE #-}
  toE   (Abs b resultTy) = TabPiType b resultTy
  {-# INLINE toE #-}

instance SinkableE      (TabPiType r)
instance HoistableE     (TabPiType r)
instance AlphaEqE       (TabPiType r)
instance AlphaHashableE (TabPiType r)
instance SubstE Name    (TabPiType r)
instance SubstE (AtomSubstVal r) (TabPiType r)
deriving instance Show (TabPiType r n)
deriving via WrapE (TabPiType r) n instance Generic (TabPiType r n)

instance GenericE (NaryPiType r) where
  type RepE (NaryPiType r) = Abs (Nest (PiBinder r)) (PairE EffectRow (Type r))
  fromE (NaryPiType bs eff resultTy) = Abs bs (PairE eff resultTy)
  {-# INLINE fromE #-}
  toE   (Abs bs (PairE eff resultTy)) = NaryPiType bs eff resultTy
  {-# INLINE toE #-}

instance SinkableE      (NaryPiType r)
instance HoistableE     (NaryPiType r)
instance AlphaEqE       (NaryPiType r)
instance AlphaHashableE (NaryPiType r)
instance SubstE Name (NaryPiType r)
instance SubstE (AtomSubstVal r) (NaryPiType r)
deriving instance Show (NaryPiType r n)
deriving via WrapE (NaryPiType r) n instance Generic (NaryPiType r n)
instance Store (NaryPiType r n)

instance GenericE (DepPairType r) where
  type RepE (DepPairType r) = Abs (Binder r) (Type r)
  fromE (DepPairType b resultTy) = Abs b resultTy
  {-# INLINE fromE #-}
  toE   (Abs b resultTy) = DepPairType b resultTy
  {-# INLINE toE #-}

instance SinkableE   (DepPairType r)
instance HoistableE  (DepPairType r)
instance AlphaEqE    (DepPairType r)
instance AlphaHashableE (DepPairType r)
instance SubstE Name (DepPairType r)
instance SubstE (AtomSubstVal r) (DepPairType r)
deriving instance Show (DepPairType r n)
deriving via WrapE (DepPairType r) n instance Generic (DepPairType r n)

instance GenericE SynthCandidates where
  type RepE SynthCandidates =
    ListE (AtomName CoreIR) `PairE` ListE (PairE ClassName (ListE InstanceName))
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

instance GenericE (AtomBinding r) where
  type RepE (AtomBinding r) =
     EitherE2
       (EitherE6
          (DeclBinding   r)   -- LetBound
          (LamBinding    r)   -- LamBound
          (PiBinding     r)   -- PiBound
          (IxType        r)   -- IxBound
          (Type          r)   -- MiscBound
          (SolverBinding r))  -- SolverBound
       (EitherE2
          (PairE (NaryPiType r) TopFunBinding) -- TopFunBound
          (RepVal SimpToImpIR))                -- TopDataBound

  fromE = \case
    LetBound    x -> Case0 $ Case0 x
    LamBound    x -> Case0 $ Case1 x
    PiBound     x -> Case0 $ Case2 x
    IxBound     x -> Case0 $ Case3 x
    MiscBound   x -> Case0 $ Case4 x
    SolverBound x -> Case0 $ Case5 x
    TopFunBound ty f ->  Case1 (Case0 (ty `PairE` f))
    TopDataBound repVal ->  Case1 (Case1 repVal)
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
      Case0 (ty `PairE` f) -> TopFunBound ty f
      Case1 repVal -> TopDataBound repVal
      _ -> error "impossible"
    _ -> error "impossible"
  {-# INLINE toE #-}


instance SinkableE   (AtomBinding r)
instance HoistableE  (AtomBinding r)
instance SubstE Name (AtomBinding r)
instance AlphaEqE (AtomBinding r)
instance AlphaHashableE (AtomBinding r)

instance GenericE TopFunBinding where
  type RepE TopFunBinding = EitherE4
    (LiftE Int `PairE` CAtom)  -- AwaitingSpecializationArgsTopFun
    SpecializationSpec         -- SpecializedTopFun
    (LamExpr SimpIR)           -- LoweredTopFun
    ImpFunName                 -- FFITopFun
  fromE = \case
    AwaitingSpecializationArgsTopFun n x  -> Case0 $ PairE (LiftE n) x
    SpecializedTopFun x -> Case1 x
    LoweredTopFun     x -> Case2 x
    FFITopFun         x -> Case3 x
  {-# INLINE fromE #-}

  toE = \case
    Case0 (PairE (LiftE n) x) -> AwaitingSpecializationArgsTopFun n x
    Case1 x                   -> SpecializedTopFun x
    Case2 x                   -> LoweredTopFun     x
    Case3 x                   -> FFITopFun         x
    _ -> error "impossible"
  {-# INLINE toE #-}


instance SinkableE TopFunBinding
instance HoistableE  TopFunBinding
instance SubstE Name TopFunBinding
instance AlphaEqE TopFunBinding
instance AlphaHashableE TopFunBinding

instance GenericE SpecializationSpec where
  type RepE SpecializationSpec =
         PairE (AtomName CoreIR) (Abs (Nest (Binder CoreIR)) (ListE CType))
  fromE (AppSpecialization fname (Abs bs args)) = PairE fname (Abs bs args)
  {-# INLINE fromE #-}
  toE   (PairE fname (Abs bs args)) = AppSpecialization fname (Abs bs args)
  {-# INLINE toE #-}

instance HasNameHint (SpecializationSpec n) where
  getNameHint (AppSpecialization f _) = getNameHint f

instance SinkableE SpecializationSpec
instance HoistableE  SpecializationSpec
instance SubstE Name SpecializationSpec
instance AlphaEqE SpecializationSpec
instance AlphaHashableE SpecializationSpec

instance GenericE (SolverBinding r) where
  type RepE (SolverBinding r) = EitherE2
                                  (PairE (Type r) (LiftE SrcPosCtx))
                                  (Type r)
  fromE = \case
    InfVarBound  ty ctx -> Case0 (PairE ty (LiftE ctx))
    SkolemBound  ty     -> Case1 ty
  {-# INLINE fromE #-}

  toE = \case
    Case0 (PairE ty (LiftE ct)) -> InfVarBound  ty ct
    Case1 ty                    -> SkolemBound  ty
    _ -> error "impossible"
  {-# INLINE toE #-}

instance SinkableE   (SolverBinding r)
instance HoistableE  (SolverBinding r)
instance SubstE Name (SolverBinding r)
instance SubstE (AtomSubstVal r) (SolverBinding r)
instance AlphaEqE       (SolverBinding r)
instance AlphaHashableE (SolverBinding r)

instance Color c => GenericE (Binding c) where
  type RepE (Binding c) =
    EitherE3
      (EitherE7
          (AtomBinding CoreIR)
          DataDef
          (DataDefName `PairE` CAtom)
          (DataDefName `PairE` LiftE Int `PairE` CAtom)
          (ClassDef)
          (InstanceDef)
          (ClassName `PairE` LiftE Int `PairE` CAtom))
      (EitherE7
          (ImpFunction)
          (LiftE FunObjCode `PairE` LinktimeNames)
          (Module)
          (LiftE (PtrType, PtrLitVal))
          (EffectDef)
          (HandlerDef)
          (EffectOpDef))
      (EitherE2
          (SpecializedDictDef)
          (LiftE BaseType))

  fromE binding = case binding of
    AtomNameBinding   tyinfo            -> Case0 $ Case0 $ tyinfo
    DataDefBinding    dataDef           -> Case0 $ Case1 $ dataDef
    TyConBinding      dataDefName     e -> Case0 $ Case2 $ dataDefName `PairE` e
    DataConBinding    dataDefName idx e -> Case0 $ Case3 $ dataDefName `PairE` LiftE idx `PairE` e
    ClassBinding      classDef          -> Case0 $ Case4 $ classDef
    InstanceBinding   instanceDef       -> Case0 $ Case5 $ instanceDef
    MethodBinding     className idx f   -> Case0 $ Case6 $ className `PairE` LiftE idx `PairE` f
    ImpFunBinding     fun               -> Case1 $ Case0 $ fun
    FunObjCodeBinding x y               -> Case1 $ Case1 $ LiftE x `PairE` y
    ModuleBinding m                     -> Case1 $ Case2 $ m
    PtrBinding ty p                     -> Case1 $ Case3 $ LiftE (ty,p)
    EffectBinding   effDef              -> Case1 $ Case4 $ effDef
    HandlerBinding  hDef                -> Case1 $ Case5 $ hDef
    EffectOpBinding opDef               -> Case1 $ Case6 $ opDef
    SpecializedDictBinding def          -> Case2 $ Case0 $ def
    ImpNameBinding ty                   -> Case2 $ Case1 $ LiftE ty
  {-# INLINE fromE #-}

  toE rep = case rep of
    Case0 (Case0 tyinfo)                                    -> fromJust $ tryAsColor $ AtomNameBinding   tyinfo
    Case0 (Case1 dataDef)                                   -> fromJust $ tryAsColor $ DataDefBinding    dataDef
    Case0 (Case2 (dataDefName `PairE` e))                   -> fromJust $ tryAsColor $ TyConBinding      dataDefName e
    Case0 (Case3 (dataDefName `PairE` LiftE idx `PairE` e)) -> fromJust $ tryAsColor $ DataConBinding    dataDefName idx e
    Case0 (Case4 (classDef))                                -> fromJust $ tryAsColor $ ClassBinding      classDef
    Case0 (Case5 (instanceDef))                             -> fromJust $ tryAsColor $ InstanceBinding   instanceDef
    Case0 (Case6 (className `PairE` LiftE idx `PairE` f))   -> fromJust $ tryAsColor $ MethodBinding     className idx f
    Case1 (Case0 fun)                                       -> fromJust $ tryAsColor $ ImpFunBinding     fun
    Case1 (Case1 (LiftE x `PairE` y))                       -> fromJust $ tryAsColor $ FunObjCodeBinding x y
    Case1 (Case2 m)                                         -> fromJust $ tryAsColor $ ModuleBinding     m
    Case1 (Case3 (LiftE (ty,p)))                            -> fromJust $ tryAsColor $ PtrBinding        ty p
    Case1 (Case4 effDef)                                    -> fromJust $ tryAsColor $ EffectBinding     effDef
    Case1 (Case5 hDef)                                      -> fromJust $ tryAsColor $ HandlerBinding    hDef
    Case1 (Case6 opDef)                                     -> fromJust $ tryAsColor $ EffectOpBinding   opDef
    Case2 (Case0 def)                                       -> fromJust $ tryAsColor $ SpecializedDictBinding def
    Case2 (Case1 (LiftE ty))                                -> fromJust $ tryAsColor $ ImpNameBinding    ty
    _ -> error "impossible"
  {-# INLINE toE #-}

deriving via WrapE (Binding c) n instance Color c => Generic (Binding c n)
instance SinkableV         Binding
instance HoistableV        Binding
instance SubstV Name       Binding
instance Color c => SinkableE   (Binding c)
instance Color c => HoistableE  (Binding c)
instance Color c => SubstE Name (Binding c)

instance GenericE (DeclBinding r) where
  type RepE (DeclBinding r) = LiftE LetAnn `PairE` Type r `PairE` Expr r
  fromE (DeclBinding ann ty expr) = LiftE ann `PairE` ty `PairE` expr
  {-# INLINE fromE #-}
  toE   (LiftE ann `PairE` ty `PairE` expr) = DeclBinding ann ty expr
  {-# INLINE toE #-}

instance SinkableE (DeclBinding r)
instance HoistableE  (DeclBinding r)
instance SubstE Name (DeclBinding r)
instance SubstE (AtomSubstVal r) (DeclBinding r)
instance AlphaEqE (DeclBinding r)
instance AlphaHashableE (DeclBinding r)

instance GenericB (Decl r) where
  type RepB (Decl r) = AtomBinderP (DeclBinding r)
  fromB (Let b binding) = b :> binding
  {-# INLINE fromB #-}
  toB   (b :> binding) = Let b binding
  {-# INLINE toB #-}

instance SinkableB (Decl r)
instance HoistableB  (Decl r)
instance SubstB (AtomSubstVal r) (Decl r)
instance SubstB Name (Decl r)
instance AlphaEqB (Decl r)
instance AlphaHashableB (Decl r)
instance ProvesExt  (Decl r)
instance BindsNames (Decl r)

instance BindsAtMostOneName (Decl r) AtomNameC where
  Let b _ @> x = b @> x
  {-# INLINE (@>) #-}

instance BindsOneName (Decl r) AtomNameC where
  binderName (Let b _) = binderName b
  {-# INLINE binderName #-}

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
                              `PairE` LoadedObjects
                              `PairE` ModuleEnv
                              `PairE` ListE (PairE SpecDictName (ListE (LamExpr SimpIR)))
  fromE (PartialTopEnvFrag cache rules loadedM loadedO env d) =
    cache `PairE` rules `PairE` loadedM `PairE` loadedO `PairE` env `PairE` d'
    where d' = ListE $ [name `PairE` ListE methods | (name, methods) <- toList d]
  {-# INLINE fromE #-}
  toE (cache `PairE` rules `PairE` loadedM `PairE` loadedO `PairE` env `PairE` d) =
    PartialTopEnvFrag cache rules loadedM loadedO env d'
    where d' = toSnocList [(name, methods) | name `PairE` ListE methods <- fromListE d]
  {-# INLINE toE #-}

instance SinkableE      PartialTopEnvFrag
instance HoistableE     PartialTopEnvFrag
instance SubstE Name    PartialTopEnvFrag

instance Semigroup (PartialTopEnvFrag n) where
  PartialTopEnvFrag x1 x2 x3 x4 x5 x6 <> PartialTopEnvFrag y1 y2 y3 y4 y5 y6 =
    PartialTopEnvFrag (x1<>y1) (x2<>y2) (x3<>y3) (x4<>y4) (x5<>y5) (x6<>y6)

instance Monoid (PartialTopEnvFrag n) where
  mempty = PartialTopEnvFrag mempty mempty mempty mempty mempty mempty
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
  extendOutMap env
    (TopEnvFrag (EnvFrag frag _)
    (PartialTopEnvFrag cache' rules' loadedM' loadedO' mEnv' d')) = resultWithDictMethods
    where
      Env (TopEnv defs rules cache loadedM loadedO) mEnv = env
      result = Env newTopEnv newModuleEnv
      resultWithDictMethods = foldr addMethods result (toList d')

      newTopEnv = withExtEvidence frag $ TopEnv
        (defs `extendRecSubst` frag)
        (sink rules <> rules')
        (sink cache <> cache')
        (sink loadedM <> loadedM')
        (sink loadedO <> loadedO')

      newModuleEnv =
        ModuleEnv
          (imports <> imports')
          (sm   <> sm'   <> newImportedSM)
          (scs  <> scs'  <> newImportedSC)
          (effs <> effs')
        where
          ModuleEnv imports sm scs effs = withExtEvidence frag $ sink mEnv
          ModuleEnv imports' sm' scs' effs' = mEnv'
          newDirectImports = S.difference (directImports imports') (directImports imports)
          newTransImports  = S.difference (transImports  imports') (transImports  imports)
          newImportedSM  = flip foldMap newDirectImports $ moduleExports         . lookupModulePure
          newImportedSC  = flip foldMap newTransImports  $ moduleSynthCandidates . lookupModulePure

      lookupModulePure v = case lookupEnvPure (Env newTopEnv mempty) v of ModuleBinding m -> m

addMethods :: (SpecDictName n, [LamExpr SimpIR n]) -> Env n -> Env n
addMethods (dName, methods) e = do
  let SpecializedDictBinding (SpecializedDict dAbs oldMethods) = lookupEnvPure e dName
  case oldMethods of
    Nothing -> do
      let newBinding = SpecializedDictBinding $ SpecializedDict dAbs (Just methods)
      updateEnv dName newBinding e
    Just _ -> error "shouldn't be adding methods if we already have them"

lookupEnvPure :: Color c => Env n -> Name c n -> Binding c n
lookupEnvPure env v = lookupTerminalSubstFrag (fromRecSubst $ envDefs $ topEnv env) v

instance GenericE Module where
  type RepE Module =       LiftE ModuleSourceName
                   `PairE` ListE ModuleName
                   `PairE` ListE ModuleName
                   `PairE` SourceMap
                   `PairE` SynthCandidates

  fromE (Module name deps transDeps sm sc) =
    LiftE name `PairE` ListE (S.toList deps) `PairE` ListE (S.toList transDeps)
      `PairE` sm `PairE` sc
  {-# INLINE fromE #-}

  toE (LiftE name `PairE` ListE deps `PairE` ListE transDeps
         `PairE` sm `PairE` sc) =
    Module name (S.fromList deps) (S.fromList transDeps) sm sc
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

instance GenericE LoadedObjects where
  type RepE LoadedObjects = ListE (PairE FunObjCodeName (LiftE NativeFunction))
  fromE (LoadedObjects m) =
    ListE $ M.toList m <&> \(v,p) -> PairE v (LiftE p)
  {-# INLINE fromE #-}
  toE (ListE pairs) =
    LoadedObjects $ M.fromList $ pairs <&> \(PairE v (LiftE p)) -> (v, p)
  {-# INLINE toE #-}

instance SinkableE      LoadedObjects
instance HoistableE     LoadedObjects
instance SubstE Name    LoadedObjects

instance GenericE ModuleEnv where
  type RepE ModuleEnv = ImportStatus
                `PairE` SourceMap
                `PairE` SynthCandidates
                `PairE` EffectRow
  fromE (ModuleEnv imports sm sc eff) =
    imports `PairE` sm `PairE` sc `PairE` eff
  {-# INLINE fromE #-}
  toE (imports `PairE` sm `PairE` sc `PairE` eff) =
    ModuleEnv imports sm sc eff
  {-# INLINE toE #-}

instance SinkableE      ModuleEnv
instance HoistableE     ModuleEnv
instance AlphaEqE       ModuleEnv
instance AlphaHashableE ModuleEnv
instance SubstE Name    ModuleEnv

instance Semigroup (ModuleEnv n) where
  ModuleEnv x1 x2 x3 x4 <> ModuleEnv y1 y2 y3 y4 =
    ModuleEnv (x1<>y1) (x2<>y2) (x3<>y3) (x4<>y4)

instance Monoid (ModuleEnv n) where
  mempty = ModuleEnv mempty mempty mempty mempty

instance Semigroup (LoadedModules n) where
  LoadedModules m1 <> LoadedModules m2 = LoadedModules (m2 <> m1)

instance Monoid (LoadedModules n) where
  mempty = LoadedModules mempty

instance Semigroup (LoadedObjects n) where
  LoadedObjects m1 <> LoadedObjects m2 = LoadedObjects (m2 <> m1)

instance Monoid (LoadedObjects n) where
  mempty = LoadedObjects mempty

instance Hashable Projection
instance Hashable IxMethod
instance Hashable ParamRole

instance Store (RepVal r n)
instance Store (Atom r n)
instance Store (Expr r n)
instance Store (SolverBinding r n)
instance Store (AtomBinding r n)
instance Store (SpecializationSpec n)
instance Store (TopFunBinding n)
instance Store (LamBinding  r n)
instance Store (DeclBinding r n)
instance Store (FieldRowElem  r n)
instance Store (FieldRowElems r n)
instance Store (Decl r n l)
instance Store (RolePiBinder r n l)
instance Store (DataDefParams r n)
instance Store (DataDef n)
instance Store (DataConDef n)
instance Store (Block r n)
instance Store (LamExpr r n)
instance Store (IxType r n)
instance Store (TabLamExpr r n)
instance Store (PiBinding r n)
instance Store (PiBinder r n l)
instance Store (PiType r n)
instance Store (TabPiType r n)
instance Store (DepPairType  r n)
instance Store (SuperclassBinders n l)
instance Store (AtomRules n)
instance Store (ClassDef     n)
instance Store (InstanceDef  n)
instance Store (InstanceBody n)
instance Store (MethodType   n)
instance Store (DictType r n)
instance Store (DictExpr r n)
instance Store (EffectDef n)
instance Store (EffectOpDef n)
instance Store (HandlerDef n)
instance Store (EffectOpType n)
instance Store (EffectOpIdx)
instance Store (SynthCandidates n)
instance Store (Module n)
instance Store (ImportStatus n)
instance Color c => Store (Binding c n)
instance Store (ModuleEnv n)
instance Store (SerializedEnv n)
instance Store (BoxPtr r n)
instance (Store (ann n)) => Store (NonDepNest r ann n l)
instance Store Projection
instance Store IxMethod
instance Store ParamRole
instance Store (SpecializedDictDef n)
instance Store (Hof r n)
instance Store (RefOp r n)
instance Store (BaseMonoid r n)
instance Store (DAMOp r n)
instance Store (UserEffectOp r n)
instance Store (IxDict r n)
instance Store (NewtypeCon r n)
instance Store (NewtypeTyCon r n)

-- === Orphan instances ===
-- TODO: Resolve this!

instance SubstE (AtomSubstVal r) (EffectRowP Name) where
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

instance SubstE (AtomSubstVal r) (EffectP Name) where
  substE (_, env) eff = case eff of
    RWSEffect rws Nothing -> RWSEffect rws Nothing
    RWSEffect rws (Just v) -> do
      let v' = case env ! v of
                 Rename        v''  -> Just v''
                 SubstVal (Con HeapVal) -> Nothing
                 SubstVal (Var v'') -> Just v''
                 SubstVal (SimpInCore [] _ [] v'') -> Just v''
                 SubstVal _ -> error "Heap parameter must be a name"
      RWSEffect rws v'
    ExceptionEffect -> ExceptionEffect
    IOEffect        -> IOEffect
    UserEffect v    ->
      case env ! v of
        Rename v' -> UserEffect v'
        -- other cases are proven unreachable by type system
        -- v' is an EffectNameC but other cases apply only to
        -- AtomNameC
    InitEffect -> InitEffect
