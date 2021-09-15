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
{-# LANGUAGE Rank2Types #-}

module Syntax (
    Type, Kind, BaseType (..), ScalarBaseType (..),
    EffectP (..), Effect, RWS (..), EffectRowP (..), EffectRow,
    ClassName (..), TyQual (..), Var, Binder, Block (..), Decl (..),
    Expr (..), Atom (..), ArrowP (..), Arrow, PrimTC (..), Abs (..),
    PrimExpr (..), PrimCon (..), LitVal (..), PrimEffect (..), PrimOp (..),
    PrimHof (..), LamExpr, PiType, WithSrc (..), srcPos, LetAnn (..),
    BinOp (..), UnOp (..), CmpOp (..), SourceBlock (..),
    ReachedEOF, SourceBlock' (..), SubstEnv, ScopedSubstEnv, SubstVal (..),
    Scope, CmdName (..), HasIVars (..), ForAnn (..),
    Val, Op, Con, Hof, TC, Module (..), TopState (..), emptyTopState,
    EvaluatedModule (..), SynthCandidates (..),
    emptyEvaluatedModule, DataConRefBinding (..),
    ImpModule (..), ImpBlock (..), ImpFunction (..), ImpDecl (..),
    IExpr (..), IVal, ImpInstr (..), Backend (..), Device (..),
    IPrimOp, IVar, IBinder, IType, SetVal (..), MonMap (..), LitProg,
    IFunType (..), IFunVar, CallingConvention (..), IsCUDARequired (..),
    UAlt (..), AltP, Alt, ModuleName,
    IScope, BinderInfo (..), AnyBinderInfo (..), AsRecEnv (..),
    Bindings, CUDAKernel (..), BenchStats,
    Result (..), Output (..), OutFormat (..),
    Err (..), ErrType (..), Except, throw, throwIf, addContext,
    addSrcContext, catchIOExcept, liftExcept, (-->), (--@), (==>),
    boundUVars, PassName (..), boundVars, renamingSubst, bindingsAsVars,
    freeVars, freeUVars, Subst, HasVars, BindsVars, Ptr, PtrType,
    AddressSpace (..), showPrimName, strToPrimName, primNameToStr,
    monMapSingle, monMapLookup, Direction (..), Limit (..),
    SourceName, SourceMap (..), UExpr, UExpr' (..), UType, UPatAnn (..),
    UAnnBinder (..), UVar (..), UBinder (..), UMethodDef (..),
    UMethodType (..), UPatAnnArrow (..), UVars,
    UPat, UPat' (..), SourceUModule (..), SourceNameDef (..), sourceNameDefName,
    UModule (..), UDecl (..), UDataDef (..), UArrow, arrowEff,
    UEffect, UEffectRow, UEffArrow,
    DataDef (..), NamedDataDef, DataConDef (..), ClassDef (..), UConDef, Nest (..), toNest,
    DataDefName, ClassDefName,
    subst, scopelessSubst, absArgType, applyAbs, makeAbs,
    applyNaryAbs, applyDataDefParams, freshSkolemVar, IndexStructure,
    fromLeftLeaningConsListTy,
    mkBundle, mkBundleTy, BundleDesc,
    extendEffRow, getProjection, simplifyCase,
    varType, binderType, isTabTy, BlockId, LogLevel (..), IRVariant (..),
    BaseMonoidP (..), BaseMonoid, getBaseMonoidType,
    applyIntBinOp, applyIntCmpOp, applyFloatBinOp, applyFloatUnOp,
    getIntLit, getFloatLit, sizeOf, ptrSize, vectorWidth,
    ProtoludeScope (..),
    pattern MaybeTy, pattern JustAtom, pattern NothingAtom,
    pattern BoolTy, pattern FalseAtom, pattern TrueAtom,
    pattern IdxRepTy, pattern IdxRepVal, pattern IIdxRepVal, pattern IIdxRepTy,
    pattern TagRepTy, pattern TagRepVal, pattern Word8Ty,
    pattern IntLitExpr, pattern FloatLitExpr,
    pattern Int32Ty, pattern Int64Ty,
    pattern UnitTy, pattern PairTy,
    pattern ProdTy, pattern ProdVal,
    pattern SumTy, pattern SumVal,
    pattern FunTy, pattern PiTy,
    pattern FixedIntRange, pattern Fin, pattern RefTy, pattern RawRefTy,
    pattern BaseTy, pattern PtrTy, pattern UnitVal,
    pattern PairVal, pattern PureArrow,
    pattern TyKind, pattern LamVal,
    pattern TabTy, pattern TabTyAbs, pattern TabVal, pattern TabValA,
    pattern Pure, pattern BinaryFunTy, pattern BinaryFunVal,
    pattern EffKind, pattern NestOne, pattern BinderAnn,
    pattern LabeledRowKind, pattern UPatIgnore, pattern ClassDictCon)
  where

import qualified Data.Map.Strict as M
import Control.Monad.Except hiding (Except)
import qualified Data.ByteString.Char8 as B
import qualified Data.List.NonEmpty as NE
import qualified Data.Set as S
import Data.Store (Store)
import Data.Tuple (swap)
import Data.Foldable (toList)
import Data.Int
import Data.Word
import Data.String (IsString, fromString)
import Foreign.Ptr
import GHC.Generics

import Cat
import Err
import LabeledItems
import Env
import Util (IsBool (..), (...), Zippable (..), zipErr, enumerate)

-- === core IR ===

data Atom = Var Var
          | Lam LamExpr
          | Pi  PiType
          | DepPairTy           (Abs Binder Type)
          | DepPair   Atom Atom (Abs Binder Type) -- lhs, rhs, rhs type abstracted over lhs
          | DataCon NamedDataDef [Atom] Int [Atom]
          | TypeCon NamedDataDef [Atom]
          | LabeledRow (ExtLabeledItems Type Name)
          | Record (LabeledItems Atom)
          | RecordTy (ExtLabeledItems Type Name)
          | Variant (ExtLabeledItems Type Name) Label Int Atom
          | VariantTy (ExtLabeledItems Type Name)
          | Con Con
          | TC  TC
          | Eff EffectRow
          | ACase Atom [AltP Atom] Type
            -- single-constructor only for now
          | DataConRef NamedDataDef [Atom] (Nest DataConRefBinding)
          -- lhs ref, rhs ref abstracted over the eventual value of lhs ref, type
          | DepPairRef Atom (Abs Binder Atom) (Abs Binder Type)
          | BoxedRef Binder Atom Block Atom  -- binder, ptr, size, body
          -- access a nested member of a binder
          -- XXX: Variable name must not be an alias for another name or for
          -- a statically-known atom. This is because the variable name used
          -- here may also appear in the type of the atom. (We maintain this
          -- invariant during substitution and in Builder.hs.)
          | ProjectElt (NE.NonEmpty Int) Var
            deriving (Show, Generic)

data Expr = App Atom Atom
          | Case Atom [Alt] Type
          | Atom Atom
          | Op  Op
          | Hof Hof
            deriving (Show, Generic)

data Decl = Let LetAnn Binder Expr deriving (Show, Generic)

data DataConRefBinding = DataConRefBinding Binder Atom  deriving (Show, Generic)

data Block = Block (Nest Decl) Expr    deriving (Show, Generic)
type AltP a = Abs (Nest Binder) a
type Alt = AltP Block

type Var    = VarP Type
type Binder = BinderP Type

-- The SourceNames in DataDef, DataConDef and ClassDef are purely for printing
data DataDef = DataDef SourceName (Nest Binder) [DataConDef]  deriving (Show, Generic)
data DataConDef = DataConDef SourceName (Nest Binder)    deriving (Show, Generic)
-- The SourceNames are the method names, for reporting errors
data ClassDef = ClassDef NamedDataDef [SourceName]  deriving (Show, Generic)

type NamedDataDef = (Name, DataDef)

data Abs b body = Abs b body               deriving (Show, Generic)
data Nest a = Nest a (Nest a) | Empty
              deriving (Show, Generic, Functor, Foldable, Traversable)

data NestPair b1 b2 = NestPair b1 b2
                      deriving (Show, Generic)

type LamExpr = Abs Binder (Arrow, Block)
type PiType  = Abs Binder (Arrow, Type)

type Arrow = ArrowP EffectRow
data ArrowP eff = PlainArrow eff
                | ImplicitArrow
                | ClassArrow
                | TabArrow
                | LinArrow
                  deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

data LetAnn = PlainLet
            | InstanceLet
            | NoInlineLet
              deriving (Show, Eq, Generic)

type Val  = Atom
type Type = Atom
type Kind = Type

type TC  = PrimTC  Atom
type Con = PrimCon Atom
type Op  = PrimOp  Atom
type Hof = PrimHof Atom

data SourceNameDef =
   SrcAtomName    Name
 | SrcTyConName   Name
 | SrcDataConName Name
 | SrcClassName   Name
 | SrcMethodName  Name
   deriving (Show, Generic)

sourceNameDefName :: SourceNameDef -> Name
sourceNameDefName def = case def of
  SrcAtomName    v -> v
  SrcTyConName   v -> v
  SrcDataConName v -> v
  SrcClassName   v -> v
  SrcMethodName  v -> v

data SourceMap = SourceMap { fromSourceMap :: M.Map SourceName SourceNameDef }  deriving (Show, Generic)

data Module = Module IRVariant (Nest Decl) EvaluatedModule deriving (Show, Generic)

data EvaluatedModule =
  EvaluatedModule Bindings SynthCandidates SourceMap deriving (Show, Generic)

data TopState = TopState
  { topBindings        :: Bindings
  , topSynthCandidates :: SynthCandidates
  , topSourceMap       :: SourceMap
  , topProtolude       :: ProtoludeScope }
  deriving (Show, Generic)

emptyTopState :: ProtoludeScope -> TopState
emptyTopState = TopState mempty mempty mempty

emptyEvaluatedModule :: EvaluatedModule
emptyEvaluatedModule = EvaluatedModule mempty mempty mempty

data IRVariant = Surface | Typed | Core | Simp | Evaluated
                 deriving (Show, Eq, Ord, Generic)


-- === front-end language AST ===

type SourceName = String

data UVar =
   -- Only appears before renaming pass
   USourceVar SourceName
   -- Only appears after renaming pass
 | UInternalVar Name
   deriving (Eq, Ord, Show, Generic)

data UBinder =
   -- Only appears before renaming pass
   UBindSource SourceName
   -- May appear before or after renaming pass
 | UIgnore
   -- The following binders only appear after the renaming pass.
 | UBind Name
   deriving (Show, Generic)


type UExpr = WithSrc UExpr'
data UExpr' = UVar UVar
            | ULam UPatAnn UArrow UExpr
            | UPi  UPatAnn UEffArrow UType
            | UApp UArrow UExpr UExpr
            | UDecl UDecl UExpr
            | UFor Direction UPatAnn UExpr
            | UCase UExpr [UAlt]
            | UHole
            | UTypeAnn UExpr UExpr
            | UTabCon [UExpr]
            | UIndexRange (Limit UExpr) (Limit UExpr)
            | UPrimExpr (PrimExpr UExpr)
            | URecord (ExtLabeledItems UExpr UExpr)     -- {a=x, b=y, ...rest}
            | UVariant (LabeledItems ()) Label UExpr    -- {|a|b| a=x |}
            | UVariantLift (LabeledItems ()) UExpr      -- {|a|b| ...rest |}
            | URecordTy (ExtLabeledItems UExpr UExpr)   -- {a:X & b:Y & ...rest}
            | UVariantTy (ExtLabeledItems UExpr UExpr)  -- {a:X | b:Y | ...rest}
            | UIntLit  Int
            | UFloatLit Double
              deriving (Show, Generic)

type UConDef = (SourceName,  Nest UAnnBinder)

data UDataDef = UDataDef
        (SourceName, Nest UAnnBinder)  -- param binders
       [(SourceName, Nest UAnnBinder)] -- data constructor types
                deriving (Show, Generic)

data UDecl =
   ULet LetAnn UPatAnn UExpr
 | UDataDefDecl
     UDataDef       -- actual definition
     UBinder        -- type constructor name
     (Nest UBinder) -- data constructor names
 | UInterface
     (Nest UAnnBinder)  -- parameter binders
        [UType]         -- superclasses
        [UMethodType]   -- method types
     UBinder            -- class name
       (Nest UBinder)   -- method names
 | UInstance
     (Nest UPatAnnArrow)      -- dictionary args (i.e. conditions)
       UVar [UExpr]           -- class var and params
       [UMethodDef]           -- method definitions
     (Maybe UBinder)          -- optional instance name
   deriving (Show, Generic)

type UType  = UExpr
type UArrow = ArrowP ()
type UEffect    = EffectP    UVar
type UEffectRow = EffectRowP UVar
type UEffArrow = ArrowP UEffectRow

data UMethodType = UMethodType { uMethodExplicitBs :: [UVar], uMethodType :: UType }
                   deriving (Show, Generic)
data UMethodDef = UMethodDef UVar UExpr deriving (Show, Generic)

data UPatAnn      = UPatAnn      UPat    (Maybe UType)  deriving (Show, Generic)
data UPatAnnArrow = UPatAnnArrow UPatAnn UArrow         deriving (Show, Generic)

data UAnnBinder = UAnnBinder UBinder UType  deriving (Show, Generic)
data UAlt = UAlt UPat UExpr deriving (Show, Generic)

-- body must only contain SourceName version of names and binders
data SourceUModule = SourceUModule UDecl deriving (Show)

-- body must only contain Name version of names and binders
data UModule = UModule UDecl SourceMap deriving (Show)

type UPat  = WithSrc UPat'
data UPat' = UPatBinder UBinder
           | UPatCon UVar (Nest UPat)
           | UPatPair UPat UPat
           | UPatUnit
           | UPatRecord (ExtLabeledItems UPat UPat)     -- {a=x, b=y, ...rest}
           | UPatVariant (LabeledItems ()) Label UPat   -- {|a|b| a=x |}
           | UPatVariantLift (LabeledItems ()) UPat     -- {|a|b| ...rest |}
           | UPatTable [UPat]
             deriving (Show)

data WithSrc a = WithSrc SrcPosCtx a
                 deriving (Show, Functor, Foldable, Traversable)

pattern UPatIgnore :: UPat'
pattern UPatIgnore = UPatBinder UIgnore

srcPos :: WithSrc a -> SrcPosCtx
srcPos (WithSrc pos _) = pos

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
        deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

data PrimOp e =
        TabCon e [e]                 -- table type elements
      | ScalarBinOp BinOp e e
      | ScalarUnOp UnOp e
      | Select e e e                 -- predicate, val-if-true, val-if-false
      | PrimEffect e (PrimEffect e)
      | IndexRef e e
      | ProjRef Int e
      | FFICall String e [e]
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
      -- Add fields to a record (on the left). Left arg contains values to add.
      | RecordCons   (LabeledItems e) e
      -- Split {a:A & b:B & ...rest} into (effectively) {a:A & b:B} & {&...rest}.
      -- Left arg contains the types of the fields to extract (e.g. a:A, b:B).
      | RecordSplit  (LabeledItems e) e
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
type BaseMonoid = BaseMonoidP Atom

data PrimEffect e = MAsk | MExtend e | MGet | MPut e
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

data ClassName = DataClass | VSpace | IdxSet | Eq | Ord deriving (Show, Eq, Generic)

data TyQual = TyQual Var ClassName  deriving (Show, Eq, Generic)

type PrimName = PrimExpr ()

type IndexStructure = Nest Binder

strToPrimName :: String -> Maybe PrimName
strToPrimName s = M.lookup s builtinNames

primNameToStr :: PrimName -> String
primNameToStr prim = case lookup prim $ map swap $ M.toList builtinNames of
  Just s  -> s
  Nothing -> show prim

showPrimName :: PrimExpr e -> String
showPrimName prim = primNameToStr $ fmap (const ()) prim

getBaseMonoidType :: Type -> Type
getBaseMonoidType ty = case ty of
  TabTy _ b -> getBaseMonoidType b
  _         -> ty

-- === effects ===

data EffectRowP name = EffectRow (S.Set (EffectP name)) (Maybe name)
                      deriving (Show, Eq, Generic)

data RWS = Reader | Writer | State               deriving (Show, Eq, Ord, Generic)
data EffectP name = RWSEffect RWS name | ExceptionEffect | IOEffect
                    deriving (Show, Eq, Ord, Generic, Functor, Foldable, Traversable)

type EffectRow = EffectRowP Name
type Effect    = EffectP    Name

pattern Pure :: Ord name => EffectRowP name
pattern Pure <- ((\(EffectRow effs t) -> (S.null effs, t)) -> (True, Nothing))
 where  Pure = mempty

instance Ord name => Semigroup (EffectRowP name) where
  EffectRow effs t <> EffectRow effs' t' =
    EffectRow (S.union effs effs') newTail
    where
      newTail = case (t, t') of
        (Nothing, effTail) -> effTail
        (effTail, Nothing) -> effTail
        _ | t == t' -> t
          | otherwise -> error "Can't combine effect rows with mismatched tails"

instance Ord name => Monoid (EffectRowP name) where
  mempty = EffectRow mempty Nothing

-- === top-level constructs ===

data SourceBlock = SourceBlock
  { sbLine     :: Int
  , sbOffset   :: Int
  , sbLogLevel :: LogLevel
  , sbText     :: String
  , sbContents :: SourceBlock'
  , sbId       :: Maybe BlockId }  deriving (Show)

type BlockId = Int
type ReachedEOF = Bool
type ModuleName = String
data SourceBlock' = RunModule SourceUModule
                  | Command CmdName (SourceName, SourceUModule)
                  | GetNameType SourceName
                  | ImportModule ModuleName
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

-- === imperative IR ===

data IExpr = ILit LitVal
           | IVar IVar
             deriving (Show)

type IPrimOp = PrimOp IExpr
type IVal = IExpr  -- only ILit and IRef constructors
type IBinder = BinderP IType
type IVar = VarP IType
type IType = BaseType
type Size = IExpr

type IFunVar = VarP IFunType
data IFunType = IFunType CallingConvention [IType] [IType] -- args, results
                deriving (Show)

data IsCUDARequired = CUDARequired | CUDANotRequired  deriving (Eq, Show)

instance IsBool IsCUDARequired where
  toBool CUDARequired = True
  toBool CUDANotRequired = False

data CallingConvention = CEntryFun
                       | EntryFun IsCUDARequired
                       | FFIFun
                       | FFIMultiResultFun
                       | CUDAKernelLaunch
                       | MCThreadLaunch
                         deriving (Show)

data ImpModule   = ImpModule [ImpFunction] deriving (Show)
data ImpFunction = ImpFunction IFunVar [IBinder] ImpBlock
                 | FFIFunction IFunVar
                   deriving (Show)
data ImpBlock    = ImpBlock (Nest ImpDecl) [IExpr]    deriving (Show)
data ImpDecl     = ImpLet [IBinder] ImpInstr deriving (Show)
data ImpInstr = IFor Direction IBinder Size ImpBlock
              | IWhile ImpBlock
              | ICond IExpr ImpBlock ImpBlock
              | IQueryParallelism IFunVar IExpr -- returns the number of available concurrent threads
              | ISyncWorkgroup
              | ILaunch IFunVar Size [IExpr]
              | ICall IFunVar [IExpr]
              | Store IExpr IExpr           -- dest, val
              | Alloc AddressSpace IType Size
              | MemCopy IExpr IExpr IExpr   -- dest, source, numel
              | Free IExpr
              | IThrowError  -- TODO: parameterize by a run-time string
              | ICastOp IType IExpr
              | IPrimOp IPrimOp
                deriving (Show)

data Backend = LLVM | LLVMCUDA | LLVMMC | MLIR | Interpreter  deriving (Show, Eq)
newtype CUDAKernel = CUDAKernel B.ByteString deriving (Show)

-- === base types ===

data LitVal = Int64Lit   Int64
            | Int32Lit   Int32
            | Word8Lit   Word8
            | Word32Lit  Word32
            | Word64Lit  Word64
            | Float64Lit Double
            | Float32Lit Float
            | PtrLit PtrType (Ptr ())
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

-- === protolude ===

data ProtoludeScope = ProtoludeScope
  { protoludeFromIntegerIface  :: Name
  , protoludeFromIntegerMethod :: Name
  }
  deriving (Show, Eq, Generic)


-- === some handy monoids ===

data SetVal a = Set a | NotSet
newtype MonMap k v = MonMap (M.Map k v)  deriving (Show, Eq)

instance Semigroup (SetVal a) where
  x <> NotSet = x
  _ <> Set x  = Set x

instance Monoid (SetVal a) where
  mempty = NotSet

instance (Ord k, Semigroup v) => Semigroup (MonMap k v) where
  MonMap m <> MonMap m' = MonMap $ M.unionWith (<>) m m'

instance (Ord k, Semigroup v) => Monoid (MonMap k v) where
  mempty = MonMap mempty

monMapSingle :: k -> v -> MonMap k v
monMapSingle k v = MonMap (M.singleton k v)

monMapLookup :: (Monoid v, Ord k) => MonMap k v -> k -> v
monMapLookup (MonMap m) k = case M.lookup k m of Nothing -> mempty
                                                 Just v  -> v

-- === passes ===

data PassName = Parse | RenamePass | TypePass | SynthPass | SimpPass | ImpPass | JitPass
              | LLVMOpt | AsmPass | JAXPass | JAXSimpPass | LLVMEval
              | ResultPass | JaxprAndHLO | OptimPass
                deriving (Ord, Eq, Bounded, Enum)

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
            | ExportedFun String Atom
              deriving (Show, Eq, Generic)

data OutFormat = Printed | RenderHtml  deriving (Show, Eq, Generic)

-- === UExpr free variables ===

type UVars = Env ()

uvarSingleton :: UVar -> UVars
uvarSingleton v = case v of
  USourceVar   _  -> error "Should only query `freeUVars` on post-renaming IR"
  UInternalVar v' -> v' @> ()

class HasUVars a where
  freeUVars :: a -> UVars

class BindsUVars a where
  boundUVars :: a -> UVars

instance HasUVars a => HasUVars [a] where
  freeUVars xs = foldMap freeUVars xs

instance HasUVars a => HasUVars (NE.NonEmpty a) where
  freeUVars xs = foldMap freeUVars xs

instance (BindsUVars a, HasUVars a) => HasUVars (Nest a) where
  freeUVars Empty = mempty
  freeUVars (Nest x xs) = freeUVars x <> (freeUVars xs `envDiff` boundUVars x)

instance BindsUVars a => BindsUVars (Nest a) where
  boundUVars xs = foldMap boundUVars xs

instance (HasUVars b, BindsUVars b, HasUVars body)
         => HasUVars (Abs b body) where
  freeUVars (Abs b body) = freeUVars b <> (freeUVars body `envDiff` boundUVars b)

instance HasUVars a => HasUVars (WithSrc a) where
  freeUVars (WithSrc _ e) = freeUVars e

instance HasUVars UExpr' where
  freeUVars expr = case expr of
    UVar v -> uvarSingleton v
    ULam pat _ body -> freeUVars (Abs pat body)
    UPi pat arr ty -> freeUVars $ Abs pat (arr, ty)
    -- TODO: maybe distinguish table arrow application
    -- (otherwise `x.i` and `x i` are the same)
    UApp _ f x -> freeUVars f <> freeUVars x
    UDecl decl body -> freeUVars $ Abs decl body
    UFor _ pat body -> freeUVars (Abs pat body)
    UHole -> mempty
    UTypeAnn v ty -> freeUVars v <> freeUVars ty
    UTabCon xs -> foldMap freeUVars xs
    UIndexRange low high -> foldMap freeUVars low <> foldMap freeUVars high
    UPrimExpr prim -> foldMap freeUVars prim
    UCase e alts -> freeUVars e <> foldMap freeUVars alts
    URecord ulr -> freeUVars ulr
    UVariant types _ val -> freeUVars types <> freeUVars val
    URecordTy ulr -> freeUVars ulr
    UVariantTy ulr -> freeUVars ulr
    UVariantLift skip val -> freeUVars skip <> freeUVars val
    UIntLit  _ -> mempty
    UFloatLit _ -> mempty

instance HasUVars UAlt where
  freeUVars (UAlt p body) = freeUVars $ Abs p body

instance HasUVars () where
  freeUVars = mempty

instance HasUVars UPat' where
  freeUVars pat = case pat of
    UPatBinder _   -> mempty
    UPatCon con ps -> uvarSingleton con <> foldMap freeUVars ps
    UPatPair p1 p2 -> freeUVars p1 <> freeUVars p2
    UPatUnit       -> mempty
    UPatRecord items -> freeUVars items
    UPatVariant _ _ p -> freeUVars p
    UPatVariantLift _ p -> freeUVars p
    UPatTable ps -> foldMap freeUVars ps

instance BindsUVars UPat' where
  boundUVars pat = case pat of
    UPatBinder b   -> boundUVars b
    UPatCon _ ps   -> foldMap boundUVars ps
    UPatPair p1 p2 -> boundUVars p1 <> boundUVars p2
    UPatUnit       -> mempty
    UPatRecord items -> boundUVars items
    UPatVariant _ _ p -> boundUVars p
    UPatVariantLift _ p -> boundUVars p
    UPatTable ps -> foldMap boundUVars ps

instance HasUVars UBinder where
  freeUVars = mempty

instance BindsUVars UBinder where
  boundUVars (UBind v) = v @> ()
  boundUVars (UBindSource _) = mempty
  boundUVars UIgnore = mempty

instance HasName UBinder where
  getName UIgnore         = Nothing
  getName (UBindSource _) = Nothing
  getName (UBind v)       = Just v

instance HasUVars UDecl where
  freeUVars (ULet _ p expr) = freeUVars p <> freeUVars expr
  freeUVars (UDataDefDecl dataDef bTyCon bDataCons) =
    freeUVars dataDef <> freeUVars (Abs bTyCon bDataCons)
  freeUVars (UInterface paramBs superclasses methods _ _) =
    freeUVars $ Abs paramBs (superclasses, uMethodType <$> methods)
  freeUVars (UInstance bs className params methods _) =
    freeUVars $ Abs bs ((className, params), methods)

instance (BindsUVars b1, HasUVars b1, HasUVars b2) => HasUVars (NestPair b1 b2) where
  freeUVars (NestPair b1 b2) =
    freeUVars b1 <> (freeUVars b2 `envDiff` boundUVars b1)

instance HasUVars UDataDef where
  freeUVars (UDataDef (_, paramBs) dataCons) =
    freeUVars $ NestPair paramBs $ map snd dataCons

instance HasUVars UMethodDef where
  freeUVars (UMethodDef name def) = freeUVars name <> freeUVars def

instance HasUVars UPatAnn where
  freeUVars (UPatAnn p ann) = freeUVars ann <> freeUVars p

instance BindsUVars UPatAnn where
  boundUVars (UPatAnn p _) = boundUVars p

instance HasUVars UPatAnnArrow where
  freeUVars (UPatAnnArrow b ann) = freeUVars b <> freeUVars ann

instance BindsUVars UPatAnnArrow where
  boundUVars (UPatAnnArrow p _) = boundUVars p

instance BindsUVars UDecl where
  boundUVars decl = case decl of
    ULet _ p _           -> boundUVars p
    UDataDefDecl _ bTyCon bDataCons ->
      boundUVars $ NestPair bTyCon bDataCons
    UInterface _ _ _ className methodNames ->
      boundUVars $ NestPair className methodNames
    UInstance _ _ _ _ instanceName  -> foldMap boundUVars instanceName

instance (BindsUVars b1, BindsUVars b2) => BindsUVars (NestPair b1 b2) where
  boundUVars (NestPair b1 b2) = boundUVars b1 <> boundUVars b2

instance HasUVars UModule where
  freeUVars (UModule decl sourceMap) =
    freeUVars (Abs decl sourceMap)

instance HasUVars SourceMap where
  freeUVars (SourceMap m) = foldMap (@>()) m

instance HasUVars UEffectRow where
  freeUVars (EffectRow effs tailVar) =
    foldMap freeUVars effs <> foldMap uvarSingleton tailVar

instance HasUVars UEffect where
  freeUVars (RWSEffect _ h) = uvarSingleton h
  freeUVars ExceptionEffect = mempty
  freeUVars IOEffect        = mempty

instance HasUVars UVar where
  freeUVars v = uvarSingleton v

instance HasUVars UAnnBinder where
  freeUVars (UAnnBinder _ ann) = freeUVars ann

instance BindsUVars UAnnBinder where
  boundUVars (UAnnBinder b _) = boundUVars b

instance HasUVars a => HasUVars (LabeledItems a) where
  freeUVars (LabeledItems items) = foldMap freeUVars items

instance HasUVars a => HasUVars (ExtLabeledItems a a) where
  freeUVars (Ext items rest) = freeUVars items <> freeUVars rest

instance HasUVars eff => HasUVars (ArrowP eff) where
  freeUVars (PlainArrow eff) = freeUVars eff
  freeUVars _ = mempty

instance (HasUVars a, HasUVars b) => HasUVars (a, b) where
  freeUVars (x, y) = freeUVars x <> freeUVars y

instance HasUVars a => HasUVars (Maybe a) where
  freeUVars Nothing = mempty
  freeUVars (Just x) = freeUVars x

instance BindsUVars a => BindsUVars (WithSrc a) where
  boundUVars (WithSrc _ x) = boundUVars x

instance BindsUVars a => BindsUVars (LabeledItems a) where
  boundUVars items = foldMap boundUVars items

instance BindsUVars a => BindsUVars (ExtLabeledItems a a) where
  boundUVars (Ext items rest) = boundUVars items <> boundUVars rest

instance BindsUVars a => BindsUVars (Maybe a) where
  boundUVars Nothing = mempty
  boundUVars (Just x) = boundUVars x

-- === Expr free variables and substitutions ===

-- In the safer-names system we use Typeable to make this an open sum type, but
-- here all the cases are explicit.
data AnyBinderInfo =
   AtomBinderInfo Type BinderInfo
 | DataDefName  DataDef
 | TyConName    DataDefName
 | DataConName  DataDefName Int
 | ClassDefName ClassDef
 -- The atoms in SuperclassName and MethodNames are the dict projections, cached
 -- for fast lookup.
 | SuperclassName ClassDefName Int Atom
 | MethodName     ClassDefName Int Atom
 | LocalUExprBound
 | ImpBound
 | TrulyUnknownBinder
   deriving (Show, Generic)

-- Just documentation for now, but they'll be distinct types with safer-names
type DataDefName  = Name
type ClassDefName = Name

data BinderInfo =
        LamBound (ArrowP ())
        -- TODO: make the expression optional, for when it's effectful?
        -- (or we could put the effect tag on the let annotation)
      | PatBound
      | LetBound LetAnn Expr
      | PiBound
      | UnknownBinder
        deriving (Show, Generic)

data SubstVal e = SubstVal e
                | Rename Name

type SubstEnv = Env (SubstVal Atom)
type Bindings = Env AnyBinderInfo
type Scope = Bindings  -- when we only care about the names, not the payloads
type ScopedSubstEnv = (SubstEnv, Bindings)

-- TODO: we could add a lot more structure for querying by dict type, caching, etc.
data SynthCandidates = SynthCandidates
  { lambdaDicts       :: [Atom]
  , superclassGetters :: [Atom]
  , instanceDicts     :: [Atom] }
  deriving (Show, Generic)

scopelessSubst :: (HasVars a, Subst a) => SubstEnv -> a -> a
scopelessSubst env x = subst (env, scope) x
  where scope = foldMap freeVars env <> (freeVars x `envDiff` env)

-- XXX: only gives the atom bindings
bindingsAsVars :: Bindings -> [Var]
bindingsAsVars env =
  flip map (envPairs env) \(v, info) ->
    case info of
      AtomBinderInfo ty _ -> v:>ty
      -- XXX: this type is nonsense. We shouldn't rely on the types obtained
      -- from querying free vars (and we're getting rid of them completely in
      -- safer-names).
      _ -> v:>UnitTy

class HasVars a where
  freeVars :: a -> Scope

class Subst a where
  subst :: ScopedSubstEnv -> a -> a

class BindsVars a where
  boundVars :: a -> Scope
  renamingSubst :: ScopedSubstEnv -> a -> (a, ScopedSubstEnv)

instance HasVars e => HasVars (SubstVal e) where
  freeVars (SubstVal x) = freeVars x
  freeVars (Rename v) = v @> TrulyUnknownBinder

instance Subst (SubstVal Atom) where
  subst env (SubstVal x) = SubstVal (subst env x)
  subst (env, _) (Rename v) =
    case envLookup env v of
      Nothing -> Rename v
      Just x -> x

instance (HasVars b, BindsVars b, HasVars body) => HasVars (Abs b body) where
  freeVars (Abs b body) = freeVars b <> (freeVars body `envDiff` boundVars b)

instance (BindsVars b, Subst body) => Subst (Abs b body) where
  subst env (Abs b body) = Abs b' body'
    where (b', env') = renamingSubst env b
          body' = subst (env <> env') body

instance (HasVars a, BindsVars a) => HasVars (Nest a) where
  freeVars xs = case xs of
    Empty -> mempty
    Nest b rest -> freeVars b <> (freeVars rest `envDiff` boundVars b)

instance (Subst a, BindsVars a) => Subst (Nest a) where
  subst env xs = case xs of
    Empty -> Empty
    Nest x rest -> Nest x' rest'
      where x' = subst env x
            env' = (mempty, boundVars x')
            rest' = subst (env <> env') rest

instance BindsVars a => BindsVars (Nest a) where
  boundVars xs = foldMap boundVars xs
  renamingSubst env xs = case xs of
    Empty -> (Empty, mempty)
    Nest x rest -> (Nest x' rest', xEnv <> restEnv)
      where
        (x', xEnv) = renamingSubst env x
        (rest', restEnv) = renamingSubst (env <> xEnv) rest

instance HasVars Binder where
  freeVars b = freeVars $ binderType b

instance Subst Binder where
  -- BUG: the following case should be unreachable but it shows up in tests
  -- subst env@(_, scope) b | b `isin` scope = error $ "shadowed binder: " ++ show b
  -- XXX: this doesn't rename the bound vars, so they must not be in scope
  subst env b = fmap (subst env) b

instance BindsVars Binder where
  boundVars b = b @> AtomBinderInfo (binderType b) UnknownBinder
  renamingSubst env (Ignore ty) = (Ignore (subst env ty), mempty)
  renamingSubst env@(_, scope) b@(Bind (v:>ty)) = (b', env')
    where v' = genFresh v scope
          b' = Bind (v':>ty')
          ty' = subst env ty
          env' = (b@>SubstVal (Var (v':>ty')), b' @> AtomBinderInfo ty' UnknownBinder)

instance HasVars DataConRefBinding where
  freeVars (DataConRefBinding b ref) = freeVars b <> freeVars ref

instance Subst DataConRefBinding where
  subst env (DataConRefBinding b ref) =
    DataConRefBinding (subst env b) (subst env ref)

instance BindsVars DataConRefBinding where
  boundVars (DataConRefBinding b _) = b @> AtomBinderInfo (binderType b) UnknownBinder
  renamingSubst env (DataConRefBinding b ref) = (DataConRefBinding b' ref', env')
    where
      ref' = subst env ref
      (b', env') = renamingSubst env b

instance Eq Atom where
  Var v == Var v' = v == v'
  Pi ab == Pi ab' = ab == ab'
  DataCon def params con args == DataCon def' params' con' args' =
    def == def' && params == params' && con == con' && args == args'
  TypeCon def params == TypeCon def' params' = def == def' && params == params'
  Variant lr l i v == Variant lr' l' i' v' =
    (lr, l, i, v) == (lr', l', i', v')
  Record lr    == Record lr'      = lr == lr'
  RecordTy lr  == RecordTy lr'    = lr == lr'
  VariantTy lr == VariantTy lr'   = lr == lr'
  Con con == Con con' = con == con'
  TC  con == TC  con' = con == con'
  Eff eff == Eff eff' = eff == eff'
  ProjectElt idxs v == ProjectElt idxs' v' = (idxs, v) == (idxs', v')
  _ == _ = False

instance Eq DataDef where
  DataDef name _ _ == DataDef name' _ _ = name == name'

instance (Show a, HasVars a, Subst a, Eq a) => Eq (Abs Binder a) where
  Abs (Ignore a) b == Abs (Ignore a') b' = a == a' && b == b'
  ab == ab' = absArgType ab == absArgType ab' && applyAbs ab v == applyAbs ab' v
    where v = Var $ freshSkolemVar (ab, ab') (absArgType ab)

instance Eq (Nest Binder) where
  Empty == Empty = True
  (Nest b bs) == (Nest b' bs') = Abs b bs == Abs b' bs'
  _ == _ = False

freshSkolemVar :: HasVars a => a -> Type -> Var
freshSkolemVar x ty = v :> ty
  where v = genFresh (rawName Skolem "skol") (freeVars x)

applyAbs :: (HasVars a, Subst a) => Abs Binder a -> Atom -> a
applyAbs (Abs b body) x = scopelessSubst (b@>SubstVal x) body

applyNaryAbs :: (HasVars a, Subst a) => Abs (Nest Binder) a -> [Atom] -> a
applyNaryAbs (Abs Empty body) [] = body
applyNaryAbs (Abs (Nest b bs) body) (x:xs) = applyNaryAbs ab xs
  where ab = applyAbs (Abs b (Abs bs body)) x
applyNaryAbs _ _ = error "wrong number of arguments"

applyDataDefParams :: DataDef -> [Type] -> [DataConDef]
applyDataDefParams (DataDef _ bs cons) params
  | length params == length (toList bs) = applyNaryAbs (Abs bs cons) params
  | otherwise = error $ "Wrong number of parameters: " ++ show (length params)

makeAbs :: HasVars a => Binder -> a -> Abs Binder a
makeAbs b body | b `isin` freeVars body = Abs b body
               | otherwise = Abs (Ignore (binderType b)) body

absArgType :: Abs Binder a -> Type
absArgType (Abs b _) = binderType b

toNest :: [a] -> Nest a
toNest = foldr Nest Empty

instance HasVars Arrow where
  freeVars arrow = case arrow of
    PlainArrow eff -> freeVars eff
    _ -> mempty
instance Subst Arrow where
  subst env arrow = case arrow of
    PlainArrow eff -> PlainArrow $ subst env eff
    _ -> arrow

arrowEff :: Arrow -> EffectRow
arrowEff (PlainArrow eff) = eff
arrowEff _ = Pure

substVar :: (SubstEnv, Scope) -> Var -> Atom
substVar env@(sub, _) v = case envLookup sub v of
  Nothing -> Var $ fmap (subst env) v
  Just (SubstVal x') -> x'
  Just (Rename v') -> Var $ v' :> subst env (varAnn v)


-- wrapper for substitution instances for recursively-scoped bindings
newtype AsRecEnv a = AsRecEnv (Env a)

instance HasVars a => HasVars (AsRecEnv a) where
  freeVars (AsRecEnv env) = foldMap freeVars env `envDiff` env

instance BindsVars (AsRecEnv AnyBinderInfo) where
  boundVars (AsRecEnv recEnv) = recEnv
  renamingSubst (substEnv, scope) (AsRecEnv recEnv) = let
    (names, vals) = unzip $ envPairs recEnv
    names' = freshNames scope (envNames recEnv)
    substEnv' = newEnv names (map Rename names')
    tmpScope = newEnv names' (repeat TrulyUnknownBinder)
    recEnv' = newEnv names' $ subst (substEnv <> substEnv', scope <> tmpScope) vals
    in (AsRecEnv recEnv', (substEnv', scope <> recEnv'))

freshNames :: NameHint hint => Scope -> [hint] -> [Name]
freshNames initScope hints = fst $ flip runCat initScope $
  forM hints \hint -> do
    scope <- look
    let nameHint = case asNameHint hint of
                     Just name -> rawName GenName name
                     Nothing   -> rawName GenName "tmp"
    let v = genFresh nameHint scope
    extend (v@>TrulyUnknownBinder)
    return v

instance HasVars Expr where
  freeVars expr = case expr of
    App f x -> freeVars f <> freeVars x
    Atom x  -> freeVars x
    Op  e   -> foldMap freeVars e
    Hof e   -> foldMap freeVars e
    Case e alts resultTy ->
      freeVars e <> freeVars alts <> freeVars resultTy

instance Subst Expr where
  subst env expr = case expr of
    App f x -> App (subst env f) (subst env x)
    Atom x  -> Atom $ subst env x
    Op  e   -> Op  $ fmap (subst env) e
    Hof e   -> Hof $ fmap (subst env) e
    Case e alts resultTy ->
      Case (subst env e) (subst env alts) (subst env resultTy)

instance HasVars Decl where
  freeVars decl = case decl of
    Let _  b expr  -> freeVars expr <> freeVars b

instance Subst Decl where
  subst env decl = case decl of
    Let ann b expr -> Let ann (fmap (subst env) b) $ subst env expr

instance BindsVars Decl where
  boundVars decl = case decl of
    Let ann b expr -> b @> AtomBinderInfo (binderType b) (LetBound ann expr)

  renamingSubst env decl = case decl of
    Let ann b expr -> (Let ann b' expr', env')
      where expr' = subst env expr
            (b', env') = renamingSubst env b

instance HasVars Block where
  freeVars (Block decls result) = freeVars $ Abs decls result
instance Subst Block where
  subst env (Block decls result) = Block decls' result'
    where Abs decls' result' = subst env $ Abs decls result

instance HasVars Atom where
  freeVars atom = case atom of
    Var v@(_:>t) -> (v @> AtomBinderInfo t UnknownBinder) <> freeVars t
    Lam lam -> freeVars lam
    Pi  ty  -> freeVars ty
    Con con -> foldMap freeVars con
    TC  tc  -> foldMap freeVars tc
    Eff eff -> freeVars eff
    DepPairTy     ta -> freeVars ta
    DepPair   x y ta -> freeVars x <> freeVars y <> freeVars ta
    -- TODO: think about these cases. We don't want to needlessly traverse the
    --       data definition but we might need to know the free Vars.
    DataCon _ params _ args -> freeVars params <> freeVars args
    TypeCon _ params        -> freeVars params
    LabeledRow la -> freeVars la
    Record la -> freeVars la
    Variant la _ _ val -> freeVars la <> freeVars val
    RecordTy row -> freeVars row
    VariantTy row -> freeVars row
    ACase e alts rty -> freeVars e <> freeVars alts <> freeVars rty
    DataConRef _ params args -> freeVars params <> freeVars args
    DepPairRef l r a -> freeVars l <> freeVars r <> freeVars a
    BoxedRef b ptr size body ->
      freeVars ptr <> freeVars size <> freeVars (Abs b body)
    ProjectElt _ v -> freeVars (Var v)

instance Subst Atom where
  subst env@(subEnv, bs) atom = case atom of
    Var v   -> substVar env v
    Lam lam -> Lam $ subst env lam
    Pi  ty  -> Pi  $ subst env ty
    TC  tc  -> TC  $ fmap (subst env) tc
    Con con -> Con $ fmap (subst env) con
    Eff eff -> Eff $ subst env eff
    DepPairTy     ta -> DepPairTy $ subst env ta
    DepPair   x y ta -> DepPair (subst env x) (subst env y) (subst env ta)
    DataCon def params con args -> DataCon def (subst env params) con (subst env args)
    TypeCon def params          -> TypeCon def (subst env params)
    LabeledRow row -> LabeledRow $ subst env row
    Record la -> Record $ subst env la
    Variant row label i val -> Variant (subst env row) label i (subst env val)
    RecordTy row -> RecordTy $ subst env row
    VariantTy row -> VariantTy $ subst env row
    ACase s alts rty -> case simplifyCase s' alts of
      Just (cenv, result) -> subst (subEnv <> cenv, bs) result
      Nothing             -> ACase s' (subst env alts) (subst env rty)
      where s' = subst env s
    DataConRef def params args -> DataConRef def (subst env params) args'
      where Abs args' () = subst env $ Abs args ()
    DepPairRef l r a -> DepPairRef (subst env l) (subst env r) (subst env a)
    BoxedRef b ptr size body -> BoxedRef b' (subst env ptr) (subst env size) body'
        where Abs b' body' = subst env $ Abs b body
    ProjectElt idxs v -> getProjection (toList idxs) $ substVar env v

simplifyCase :: Atom -> [AltP a] -> Maybe (SubstEnv, a)
simplifyCase e alts = case e of
  DataCon _ _ con args -> do
    let Abs bs result = alts !! con
    Just (newEnv bs (map SubstVal args), result)
  Variant (NoExt types) label i value -> do
    let LabeledItems ixtypes = enumerate types
    let index = fst $ (ixtypes M.! label) NE.!! i
    let Abs bs result = alts !! index
    Just (newEnv bs [SubstVal value], result)
  SumVal _ i value -> do
    let Abs bs result = alts !! i
    Just (newEnv bs [SubstVal value], result)
  Con (SumAsProd _ (TagRepVal tag) vals) -> do
    let Abs bs result = alts !! (fromIntegral tag)
    Just (newEnv bs (map SubstVal (vals !! fromIntegral tag)), result)
  _ -> Nothing

instance HasVars EffectRow where
  freeVars (EffectRow row t) = foldMap freeVars row
                            <> foldMap (\v -> v @> AtomBinderInfo EffKind UnknownBinder) t
instance Subst EffectRow where
  subst env (EffectRow row t) = extendEffRow row' t'
   where
     row' = S.map (subst env) row
     t' = substEffTail (fst env) t

instance HasVars Effect where
  freeVars eff = case eff of
    RWSEffect _ v -> v @> AtomBinderInfo TyKind UnknownBinder
    ExceptionEffect -> mempty
    IOEffect        -> mempty
instance Subst Effect where
  subst (env,_) eff = case eff of
    RWSEffect rws v -> RWSEffect rws (substName env v)
    ExceptionEffect -> ExceptionEffect
    IOEffect        -> IOEffect

instance HasVars BinderInfo where
  freeVars binfo = case binfo of
   LetBound _ expr -> freeVars expr
   _ -> mempty

instance Subst BinderInfo where
  subst env binfo = case binfo of
   LetBound a expr -> LetBound a $ subst env expr
   _ -> binfo

instance HasVars AnyBinderInfo where
  freeVars info = case info of
    AtomBinderInfo ty binfo -> freeVars ty <> freeVars binfo
    DataDefName dataDef     -> freeVars dataDef
    ClassDefName classDef   -> freeVars classDef
    TyConName      dataDefName   -> freeVarsName dataDefName
    DataConName    dataDefName _ -> freeVarsName dataDefName
    SuperclassName dataDefName _ getter -> freeVarsName dataDefName <> freeVars getter
    MethodName     dataDefName _ getter -> freeVarsName dataDefName <> freeVars getter
    LocalUExprBound    -> mempty
    ImpBound           -> mempty
    TrulyUnknownBinder -> mempty

instance Subst AnyBinderInfo where
  subst env@(substEnv, _) info = case info of
    AtomBinderInfo ty binfo    -> AtomBinderInfo (subst env ty) (subst env binfo)
    DataDefName dataDef        -> DataDefName    (subst env dataDef)
    ClassDefName classDef      -> ClassDefName   (subst env classDef)
    TyConName      dataDefName        -> TyConName   (substName substEnv dataDefName)
    DataConName    dataDefName idx -> DataConName    (substName substEnv dataDefName) idx
    SuperclassName dataDefName idx getter ->
      SuperclassName (substName substEnv dataDefName) idx (subst env getter)
    MethodName     dataDefName idx getter ->
      MethodName     (substName substEnv dataDefName) idx (subst env getter)
    LocalUExprBound    -> LocalUExprBound
    ImpBound           -> ImpBound
    TrulyUnknownBinder -> TrulyUnknownBinder

instance HasVars SynthCandidates where
  freeVars (SynthCandidates xs ys zs) =
    foldMap freeVars xs <> foldMap freeVars ys <> foldMap freeVars zs

instance Subst SynthCandidates where
  subst env (SynthCandidates xs ys zs) =
    SynthCandidates (map (subst env) xs) (map (subst env) ys) (map (subst env) zs)

instance HasVars DataDef where
  freeVars (DataDef _ paramBs dataCons) = freeVars $ Abs paramBs dataCons

instance Subst DataDef where
  subst env (DataDef tcName paramBs dataCons) =
    DataDef tcName paramBs' dataCons'
    where Abs paramBs' dataCons' = subst env $ Abs paramBs dataCons

instance HasVars ClassDef where
  freeVars (ClassDef (_, dataDef) _) = freeVars dataDef

instance Subst ClassDef where
  subst env (ClassDef (name, dataDef) methodNames) =
    ClassDef (substName (fst env) name, subst env dataDef) methodNames

instance HasVars DataConDef where
  freeVars (DataConDef _ bs) = freeVars $ Abs bs ()
instance Subst DataConDef where
  subst env (DataConDef name bs) = DataConDef name bs'
    where Abs bs' () = subst env $ Abs bs ()

instance HasVars a => HasVars (LabeledItems a) where
  freeVars (LabeledItems items) = foldMap freeVars items

instance Subst a => Subst (LabeledItems a) where
  subst env (LabeledItems items) = LabeledItems $ fmap (subst env) items

instance HasVars a => HasVars (ExtLabeledItems a Name) where
  freeVars (Ext items Nothing) = freeVars items
  freeVars (Ext items (Just v)) =
    freeVars items <> (v @> AtomBinderInfo LabeledRowKind UnknownBinder)

instance Subst (ExtLabeledItems Type Name) where
  subst env@(env', _) (Ext items rest) =
    prefixExtLabeledItems (subst env items) (substExtLabeledItemsTail env' rest)

substEffTail :: SubstEnv -> Maybe Name -> EffectRow
substEffTail _ Nothing = EffectRow mempty Nothing
substEffTail env (Just v) = case envLookup env (v:>()) of
  Nothing -> EffectRow mempty (Just v)
  Just (Rename v')              -> EffectRow mempty (Just v')
  Just (SubstVal (Var (v':>_))) -> EffectRow mempty (Just v')
  Just (SubstVal (Eff r))       -> r
  _ -> error "Not a valid effect substitution"

substName :: SubstEnv -> Name -> Name
substName env v = case envLookup env (v:>()) of
  Nothing -> v
  Just (Rename         v'     ) -> v'
  Just (SubstVal (Var (v':>_))) -> v'
  _ -> error "Should only substitute with a name"

-- XXX: this is a hack. (Should be fixed with safer-names)
freeVarsName :: Name -> Scope
freeVarsName name = name @> LocalUExprBound

extendEffRow :: S.Set Effect -> EffectRow -> EffectRow
extendEffRow effs (EffectRow effs' t) = EffectRow (effs <> effs') t

substExtLabeledItemsTail :: SubstEnv -> Maybe Name -> ExtLabeledItems Type Name
substExtLabeledItemsTail _ Nothing = NoExt NoLabeledItems
substExtLabeledItemsTail env (Just v) = case envLookup env (v:>()) of
  Nothing -> Ext NoLabeledItems $ Just v
  Just (Rename v')                 -> Ext NoLabeledItems $ Just v'
  Just (SubstVal (Var (v':>_)))    -> Ext NoLabeledItems $ Just v'
  Just (SubstVal (LabeledRow row)) -> row
  _ -> error "Not a valid labeled row substitution"

getProjection :: [Int] -> Atom -> Atom
getProjection [] a = a
getProjection (i:is) a = case getProjection is a of
  Var v               -> ProjectElt (NE.fromList [i]) v
  ProjectElt idxs' a' -> ProjectElt (NE.cons i idxs') a'
  DataCon _ _ _ xs    -> xs !! i
  Record items        -> toList items !! i
  ProdVal xs          -> xs !! i
  DepPair l _ _ | i == 0 -> l
  DepPair _ r _ | i == 1 -> r
  _ -> error $ "Not a valid projection: " ++ show i ++ " of " ++ show a

instance HasVars () where freeVars () = mempty
instance Subst () where subst _ () = ()

instance (HasVars a, HasVars b) => HasVars (a, b) where
  freeVars (x, y) = freeVars x <> freeVars y
instance (Subst a, Subst b) => Subst (a, b) where
  subst env (x, y) = (subst env x, subst env y)

instance HasVars a => HasVars (Maybe a) where freeVars x = foldMap freeVars x
instance Subst a => Subst (Maybe a) where subst env x = fmap (subst env) x

instance HasVars a => HasVars (Env a) where freeVars x = foldMap freeVars x
instance Subst a => Subst (Env a) where subst env x = fmap (subst env) x

instance HasVars a => HasVars [a] where freeVars x = foldMap freeVars x
instance Subst a => Subst [a] where subst env x = fmap (subst env) x

instance HasVars a => HasVars (NE.NonEmpty a) where freeVars x = foldMap freeVars x
instance Subst a => Subst (NE.NonEmpty a) where subst env x = fmap (subst env) x

instance Eq SourceBlock where
  x == y = sbText x == sbText y

instance Ord SourceBlock where
  compare x y = compare (sbText x) (sbText y)

type IScope = Env IType

class HasIVars a where
  freeIVars :: a -> IScope

instance HasIVars IExpr where
  freeIVars e = case e of
    ILit _        -> mempty
    IVar v@(_:>t) -> v @> t <> freeIVars t

instance HasIVars IType where
  freeIVars _ = mempty

instance HasIVars ImpBlock where
  freeIVars (ImpBlock Empty results) = foldMap freeIVars results
  freeIVars (ImpBlock (Nest (ImpLet bs instr) rest) results) =
    freeIVars instr <>
      (freeIVars (ImpBlock rest results) `envDiff` newEnv bs (repeat ()))

instance HasIVars ImpInstr where
  freeIVars i = case i of
    IFor _ b n p      -> freeIVars n <> (freeIVars p `envDiff` (b @> ()))
    IWhile p          -> freeIVars p
    ICond  c t f      -> freeIVars c <> freeIVars t <> freeIVars f
    IQueryParallelism _ s -> freeIVars s
    ISyncWorkgroup      -> mempty
    ILaunch _ size args -> freeIVars size <> foldMap freeIVars args
    ICall   _      args -> foldMap freeIVars args
    Store d e     -> freeIVars d <> freeIVars e
    Alloc _ t s   -> freeIVars t <> freeIVars s
    MemCopy x y z -> freeIVars x <> freeIVars y <> freeIVars z
    Free x        -> freeIVars x
    ICastOp t x   -> freeIVars t <> freeIVars x
    IPrimOp op    -> foldMap freeIVars op
    IThrowError   -> mempty

instance Semigroup (Nest a) where
  (<>) = mappend

-- TODO: think about performance. This is used with the Cat/Writer monad a lot.
instance Monoid (Nest a) where
  mempty = Empty
  mappend xs ys = toNest $ toList xs ++ toList ys

-- === Helpers for function evaluation over fixed-width types ===

applyIntBinOp' :: (forall a. (Eq a, Ord a, Num a, Integral a) => (a -> Atom) -> a -> a -> Atom) -> Atom -> Atom -> Atom
applyIntBinOp' f x y = case (x, y) of
  (Con (Lit (Int64Lit xv)), Con (Lit (Int64Lit yv))) -> f (Con . Lit . Int64Lit) xv yv
  (Con (Lit (Int32Lit xv)), Con (Lit (Int32Lit yv))) -> f (Con . Lit . Int32Lit) xv yv
  (Con (Lit (Word8Lit xv)), Con (Lit (Word8Lit yv))) -> f (Con . Lit . Word8Lit) xv yv
  (Con (Lit (Word32Lit xv)), Con (Lit (Word32Lit yv))) -> f (Con . Lit . Word32Lit) xv yv
  (Con (Lit (Word64Lit xv)), Con (Lit (Word64Lit yv))) -> f (Con . Lit . Word64Lit) xv yv
  _ -> error $ "Expected integer atoms, got: " ++ show x ++ " and " ++ show y

applyIntBinOp :: (forall a. (Num a, Integral a) => a -> a -> a) -> Atom -> Atom -> Atom
applyIntBinOp f x y = applyIntBinOp' (\w -> w ... f) x y

applyIntCmpOp :: (forall a. (Eq a, Ord a) => a -> a -> Bool) -> Atom -> Atom -> Atom
applyIntCmpOp f x y = applyIntBinOp' (\_ -> (Con . Lit . Word8Lit . fromIntegral . fromEnum) ... f) x y

applyFloatBinOp :: (forall a. (Num a, Fractional a) => a -> a -> a) -> Atom -> Atom -> Atom
applyFloatBinOp f x y = case (x, y) of
  (Con (Lit (Float64Lit xv)), Con (Lit (Float64Lit yv))) -> Con $ Lit $ Float64Lit $ f xv yv
  (Con (Lit (Float32Lit xv)), Con (Lit (Float32Lit yv))) -> Con $ Lit $ Float32Lit $ f xv yv
  _ -> error "Expected float atoms"

applyFloatUnOp :: (forall a. (Num a, Fractional a) => a -> a) -> Atom -> Atom
applyFloatUnOp f x = applyFloatBinOp (\_ -> f) undefined x

-- === Synonyms ===

varType :: Var -> Type
varType = varAnn

binderType :: Binder -> Type
binderType = binderAnn

infixr 1 -->
infixr 1 --@
infixr 2 ==>

(-->) :: Type -> Type -> Type
a --> b = Pi (Abs (Ignore a) (PureArrow, b))

(--@) :: Type -> Type -> Type
a --@ b = Pi (Abs (Ignore a) (LinArrow, b))

(==>) :: Type -> Type -> Type
a ==> b = Pi (Abs (Ignore a) (TabArrow, b))

pattern IntLitExpr :: Int -> UExpr'
pattern IntLitExpr x = UIntLit x

pattern FloatLitExpr :: Double -> UExpr'
pattern FloatLitExpr x = UFloatLit x

getIntLit :: LitVal -> Int
getIntLit l = case l of
  Int64Lit i -> fromIntegral i
  Int32Lit i -> fromIntegral i
  Word8Lit  i -> fromIntegral i
  Word32Lit  i -> fromIntegral i
  Word64Lit  i -> fromIntegral i
  _ -> error $ "Expected an integer literal"

getFloatLit :: LitVal -> Double
getFloatLit l = case l of
  Float64Lit f -> f
  Float32Lit f -> realToFrac f
  _ -> error $ "Expected a floating-point literal"

-- Type used to represent indices at run-time
pattern IdxRepTy :: Type
pattern IdxRepTy = TC (BaseType IIdxRepTy)

pattern IdxRepVal :: Int32 -> Atom
pattern IdxRepVal x = Con (Lit (Int32Lit x))

pattern IIdxRepVal :: Int32 -> IExpr
pattern IIdxRepVal x = ILit (Int32Lit x)

pattern IIdxRepTy :: IType
pattern IIdxRepTy = Scalar Int32Type

-- Type used to represent sum type tags at run-time
pattern TagRepTy :: Type
pattern TagRepTy = TC (BaseType (Scalar Word8Type))

pattern TagRepVal :: Word8 -> Atom
pattern TagRepVal x = Con (Lit (Word8Lit x))

pattern Word8Ty :: Type
pattern Word8Ty = TC (BaseType (Scalar Word8Type))

pattern PairVal :: Atom -> Atom -> Atom
pattern PairVal x y = Con (ProdCon [x, y])

pattern PairTy :: Type -> Type -> Type
pattern PairTy x y = TC (ProdType [x, y])

pattern ProdTy :: [Type] -> Type
pattern ProdTy tys = TC (ProdType tys)

pattern ProdVal :: [Atom] -> Atom
pattern ProdVal xs = Con (ProdCon xs)

pattern SumTy :: [Type] -> Type
pattern SumTy cs = TC (SumType cs)

pattern SumVal :: Type -> Int -> Atom -> Atom
pattern SumVal ty tag payload = Con (SumCon ty tag payload)

pattern UnitVal :: Atom
pattern UnitVal = Con (ProdCon [])

pattern UnitTy :: Type
pattern UnitTy = TC (ProdType [])

pattern BaseTy :: BaseType -> Type
pattern BaseTy b = TC (BaseType b)

pattern PtrTy :: PtrType -> Type
pattern PtrTy ty = BaseTy (PtrType ty)

pattern RefTy :: Atom -> Type -> Type
pattern RefTy r a = TC (RefType (Just r) a)

pattern RawRefTy :: Type -> Type
pattern RawRefTy a = TC (RefType Nothing a)

pattern TyKind :: Kind
pattern TyKind = TC TypeKind

pattern EffKind :: Kind
pattern EffKind = TC EffectRowKind

pattern LabeledRowKind :: Kind
pattern LabeledRowKind = TC LabeledRowKindTC

pattern FixedIntRange :: Int32 -> Int32 -> Type
pattern FixedIntRange low high = TC (IntRange (IdxRepVal low) (IdxRepVal high))

pattern Fin :: Atom -> Type
pattern Fin n = TC (IntRange (IdxRepVal 0) n)

pattern PureArrow :: Arrow
pattern PureArrow = PlainArrow Pure

pattern TabTy :: Binder -> Type -> Type
pattern TabTy v i = Pi (Abs v (TabArrow, i))

pattern TabTyAbs :: PiType -> Type
pattern TabTyAbs a <- Pi a@(Abs _ (TabArrow, _))

pattern LamVal :: Binder -> Block -> Atom
pattern LamVal v b <- Lam (Abs v (_, b))

pattern TabVal :: Binder -> Block -> Atom
pattern TabVal v b = Lam (Abs v (TabArrow, b))

pattern TabValA :: Binder -> Atom -> Atom
pattern TabValA v a = Lam (Abs v (TabArrow, (Block Empty (Atom a))))

pattern Int32Ty :: Type
pattern Int32Ty = BaseTy (Scalar Int32Type)

pattern Int64Ty :: Type
pattern Int64Ty = BaseTy (Scalar Int64Type)

isTabTy :: Type -> Bool
isTabTy (TabTy _ _) = True
isTabTy _ = False

-- ((...((ans & x{n}) & x{n-1})... & x2) & x1) -> (ans, [x1, ..., x{n}])
fromLeftLeaningConsListTy :: Fallible m => Int -> Type -> m (Type, [Type])
fromLeftLeaningConsListTy depth initTy = go depth initTy []
  where
    go 0        ty xs = return (ty, reverse xs)
    go remDepth ty xs = case ty of
      PairTy lt rt -> go (remDepth - 1) lt (rt : xs)
      _ -> throw CompilerErr $ "Not a pair: " ++ show xs

type BundleDesc = Int  -- length

bundleFold :: a -> (a -> a -> a) -> [a] -> (a, BundleDesc)
bundleFold empty pair els = case els of
  []  -> (empty, 0)
  [e] -> (e, 1)
  h:t -> (pair h tb, td + 1)
    where (tb, td) = bundleFold empty pair t

mkBundleTy :: [Type] -> (Type, BundleDesc)
mkBundleTy = bundleFold UnitTy PairTy

mkBundle :: [Atom] -> (Atom, BundleDesc)
mkBundle = bundleFold UnitVal PairVal

pattern FunTy :: Binder -> EffectRow -> Type -> Type
pattern FunTy b eff bodyTy = Pi (Abs b (PlainArrow eff, bodyTy))

pattern PiTy :: Binder -> Arrow -> Type -> Type
pattern PiTy b arr bodyTy = Pi (Abs b (arr, bodyTy))

pattern BinaryFunTy :: Binder -> Binder -> EffectRow -> Type -> Type
pattern BinaryFunTy b1 b2 eff bodyTy = FunTy b1 Pure (FunTy b2 eff bodyTy)

pattern BinaryFunVal :: Binder -> Binder -> EffectRow -> Block -> Type
pattern BinaryFunVal b1 b2 eff body =
          Lam (Abs b1 (PureArrow, Block Empty (Atom (
          Lam (Abs b2 (PlainArrow eff, body))))))

pattern NestOne :: a -> Nest a
pattern NestOne x = Nest x Empty

pattern BinderAnn :: a -> BinderP a
pattern BinderAnn x <- ((\case Ignore   ann  -> ann
                               Bind (_:>ann) -> ann) -> x)
  where BinderAnn x = Ignore x

pattern ClassDictCon :: [Type] -> [Type] -> DataConDef
pattern ClassDictCon superclassTys methodTys <-
 DataConDef _ (Nest (BinderAnn (PairTy (ProdTy superclassTys) (ProdTy methodTys))) Empty)

pattern MaybeTy :: Type -> Type
pattern MaybeTy a = SumTy [UnitTy, a]

pattern NothingAtom :: Type -> Atom
pattern NothingAtom a = SumVal (MaybeTy a) 0 UnitVal

pattern JustAtom :: Type -> Atom -> Atom
pattern JustAtom a x = SumVal (MaybeTy a) 1 x

pattern BoolTy :: Type
pattern BoolTy = Word8Ty

pattern FalseAtom :: Atom
pattern FalseAtom = Con (Lit (Word8Lit 0))

pattern TrueAtom :: Atom
pattern TrueAtom = Con (Lit (Word8Lit 1))

-- TODO: Enable once https://gitlab.haskell.org//ghc/ghc/issues/13363 is fixed...
-- {-# COMPLETE TypeVar, ArrowType, TabTy, Forall, TypeAlias, Effect, NoAnn, TC #-}

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
  , ("mextend"    , OpExpr $ PrimEffect () $ MExtend ())
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

instance Store a => Store (PrimOp  a)
instance Store a => Store (PrimCon a)
instance Store a => Store (PrimTC  a)
instance Store a => Store (PrimHof a)
instance (Store a, Store b) => Store (Abs a b)
instance Store a => Store (Nest a)
instance Store a => Store (ArrowP a)
instance Store a => Store (Limit a)
instance Store a => Store (PrimEffect a)
instance Store a => Store (BaseMonoidP a)
instance Store ForAnn
instance Store Atom
instance Store Expr
instance Store Block
instance Store Decl
instance Store RWS
instance Store Effect
instance Store EffectRow
instance Store Direction
instance Store UnOp
instance Store BinOp
instance Store CmpOp
instance Store LetAnn
instance Store BinderInfo
instance Store AnyBinderInfo
instance Store DataDef
instance Store ClassDef
instance Store DataConDef
instance Store LitVal
instance Store ScalarBaseType
instance Store BaseType
instance Store AddressSpace
instance Store Device
instance Store DataConRefBinding
instance Store SourceMap
instance Store SynthCandidates
instance Store SourceNameDef
instance Store ProtoludeScope
instance Store TopState

instance IsString UVar where
  fromString = USourceVar . fromString

instance IsString UBinder where
  fromString = UBindSource . fromString

instance NameHint UBinder where
  asNameHint b = case b of
    UBindSource name -> Just $ fromString name
    UIgnore -> Nothing
    UBind name -> asNameHint name

instance IsString UPat' where
  fromString = UPatBinder . fromString

instance IsString UPatAnn where
  fromString s = UPatAnn (fromString s) Nothing

instance IsString UExpr' where
  fromString = UVar . fromString

instance IsString a => IsString (WithSrc a) where
  fromString = WithSrc Nothing . fromString

instance Zippable ArrowP where
  zipWithZ f arr1 arr2 = case (arr1, arr2) of
    (PlainArrow e1, PlainArrow e2) -> PlainArrow <$> f e1 e2
    (ImplicitArrow, ImplicitArrow) -> return ImplicitArrow
    (ClassArrow   , ClassArrow   ) -> return ClassArrow
    (TabArrow     , TabArrow     ) -> return TabArrow
    (LinArrow     , LinArrow     ) -> return LinArrow
    _ -> zipErr

instance Semigroup SourceMap where
  SourceMap m1 <> SourceMap m2 = SourceMap $ m2 <> m1

instance Monoid SourceMap where
  mempty = SourceMap mempty

instance Semigroup SynthCandidates where
  SynthCandidates xs ys zs <> SynthCandidates xs' ys' zs' =
    SynthCandidates (xs<>xs') (ys<>ys') (zs<>zs')

instance Monoid SynthCandidates where
  mempty = SynthCandidates mempty mempty mempty

instance HasName SourceNameDef where
  getName srcName = Just $ sourceNameDefName srcName
