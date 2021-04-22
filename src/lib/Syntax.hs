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
{-# LANGUAGE KindSignatures #-}

module Syntax (
    Type, Kind, BaseType (..), ScalarBaseType (..),
    Effect (..), RWS (..), EffectRow (..),
    SrcPos, Var, Binder, AnnBinderP, Block (..), Decl (..),
    Expr (..), Atom (..), ArrowP (..), Arrow, PrimTC (..), Abs (..),
    PrimExpr (..), PrimCon (..), LitVal (..), PrimEffect (..), PrimOp (..),
    PrimHof (..), LamExpr, PiType, srcPos, srcPosH, LetAnn (..),
    BinOp (..), UnOp (..), CmpOp (..), SourceBlock (..), SourceNameMap (..),
    ReachedEOF, SourceBlock' (..), SubstEnv, SubstEnvFrag, applySubst,
    CmdName (..), HasIVars (..), ForAnn (..), substEnvLookup,
    Val, Op, Con, Hof, TC, Module (..), EvaluatedModule, WithBindings,
    emptyEvaluatedModule, DataConRefBinding (..),
    ImpModule (..), ImpBlock (..), ImpFunction (..), ImpDecl (..),
    IExpr (..), IVal, ImpInstr (..), Backend (..), Device (..),
    IPrimOp, IVar, IBinder, IBinderList, IType, SetVal (..), MonMap (..), LitProg,
    IFunType (..), IFunVar, CallingConvention (..), IsCUDARequired (..),
    UAlt (..), AltP, Alt, Label, LabeledItems (..), labeledSingleton,
    lookupLabelHead, reflectLabels, withLabels, ExtLabeledItems (..),
    prefixExtLabeledItems, getLabels, ModuleName, SourceModule,
    BinderInfo (..), TypedBinderInfo (..), Bindings, BindingsFrag, emptyBindings,
    CUDAKernel (..), BenchStats, SrcCtx, Result (..), Output (..), OutFormat (..),
    Err (..), ErrType (..), Except, throw, throwIf, modifyErr, addContext,
    addSrcContext, catchIOExcept, liftEitherIO, (-->), (--@), (==>),
    PassName (..),
    freeUVars, Subst (..), BindsNamesCore (..), Ptr, PtrType,
    AddressSpace (..), showPrimName, strToPrimName, primNameToStr,
    monMapSingle, monMapLookup, Direction (..), Limit (..),
    UExpr, UExpr' (..), UType, UPatAnn, UAnnBinder, UVar,
    UMethodDef (..), UPatAnnArrow, UAnnBinderList,
    UPat, UPat' (..), UModule (..), UDecl (..), UArrow, arrowEff,
    DataDef (..), UDataDef (..),
    NamedDataDef (..), DataConDef (..), Nest (..), toNest,
    WithSrc (..), WithSrcH (..), WithSrcH2 (..), AnnVarP (..),
    absArgType, applyAbs, scopelessApplyAbs, scopelessApplyNaryAbs,
    -- makeAbs,
    applyNaryAbs, applyDataDefParams, -- freshSkolemVar,
    IndexStructure,
    mkConsList, mkConsListTy, fromConsList, fromConsListTy, fromLeftLeaningConsListTy,
    mkBundle, mkBundleTy, BundleDesc,
    -- extendEffRow,
    getProjection, outputStreamPtrName,
    binderType, isTabTy, LogLevel (..), IRVariant (..),
    BaseMonoidP (..), BaseMonoid, getBaseMonoidType,
    applyIntBinOp, applyIntCmpOp, applyFloatBinOp, applyFloatUnOp,
    getIntLit, getFloatLit, sizeOf, ptrSize, vectorWidth,
    WithArrow (..), withoutArrow, justArrow,
    -- pattern MaybeTy, pattern JustAtom, pattern NothingAtom,
    pattern IdxRepTy, pattern IdxRepVal, pattern IIdxRepVal, pattern IIdxRepTy,
    pattern TagRepTy, pattern TagRepVal, pattern Word8Ty,
    pattern IntLitExpr, pattern FloatLitExpr,
    pattern UnitTy, pattern PairTy, pattern FunTy, pattern PiTy,
    pattern FixedIntRange, pattern Fin, pattern RefTy, pattern RawRefTy,
    pattern BaseTy, pattern PtrTy, pattern UnitVal,
    pattern PairVal, pattern PureArrow,
    pattern TyKind, pattern LamVal,
    pattern TabTy, pattern TabTyAbs, pattern TabVal, pattern TabValA,
    pattern Pure, pattern BinaryFunTy, pattern BinaryFunVal,
    pattern Unlabeled, pattern NoExt, pattern LabeledRowKind,
    pattern NoLabeledItems, pattern InternalSingletonLabel, pattern EffKind,
    pattern NestOne,
    -- pattern BinderAnn,
    -- ClassDictDef (..), pattern ClassDictCon,
    pattern UnderscoreUPat)
  where

import Prelude hiding ((.), id)
import Control.Category
import Control.Exception hiding (throw)
import Control.Monad.Identity
import Control.Monad.Writer hiding (Alt)
import Control.Monad.Except hiding (Except)
import qualified Data.ByteString.Char8 as B
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import qualified Data.Set        as S
import Data.Tuple (swap)
import Data.Foldable (toList)
import Data.Int
import Data.Word
import Data.String (IsString, fromString)
import Foreign.Ptr
import GHC.Generics

import Name
import Util (IsBool (..), enumerate, (...))
import HigherKinded

-- === core IR ===

data Atom n =
   Var (Var n)
 | Lam (LamExpr n)
 | Pi  (PiType  n)
 | DataCon (NamedDataDef n) [Atom n] Int [Atom n]
 | TypeCon (NamedDataDef n) [Atom n]
 | LabeledRow (ExtLabeledItems (Type n) (Name n))
 | Record (LabeledItems (Atom n))
 | RecordTy  (ExtLabeledItems (Type n) (Name n))
 | Variant   (ExtLabeledItems (Type n) (Name n)) Label Int (Atom n)
 | VariantTy (ExtLabeledItems (Type n) (Name n))
 | Con (Con n)
 | TC  (TC  n)
 | Eff (EffectRow n)
 | ACase (Atom n) [AltP Atom n] (Type n)
   -- single-constructor only for now
 | DataConRef (DataDef n) [Atom n] (EmptyNest DataConRefBinding n)
 | BoxedRef (Atom n) (Atom n) (Abs Binder Block n)  -- ptr, size, binder/body
 -- access a nested member of a binder
 -- XXX: Variable name must not be an alias for another name or for
 -- a statically-known atom. This is because the variable name used
 -- here may also appear in the type of the atom. (We maintain this
 -- invariant during substitution and in Builder.hs.)
 | ProjectElt (NE.NonEmpty Int) (Var n)
   deriving (Show, Generic)

data Expr n =
   App (Atom n) (Atom n)
 | Case (Atom n) [Alt n] (Type n)
 | Atom (Atom n)
 | Op  (Op  n)
 | Hof (Hof n)
   deriving (Show, Generic)

data Decl n l = Let LetAnn (Binder n l) (Expr n) deriving (Show, Generic)

data DataConRefBinding n l = DataConRefBinding (Binder n l) (Atom n)  deriving (Show, Generic)

type AltP (e :: * -> *) = Abs (Nest Binder) e :: * -> *
type Alt = AltP Block                         :: * -> *

-- TODO: get rid of annotations on variable occurrences
data AnnVarP (ann :: * -> *) n = AnnVar (Name n) (ann n)  deriving (Show, Eq)

type Var = AnnVarP Type :: * -> *
type Binder     = AnnBinderP PlainBinder            Type  :: * -> * -> *
type BinderList = AnnBinderP PlainBinderList (ListH Type) :: * -> * -> *

data DataDef n where
  DataDef :: RawName -> BinderList n l -> ListH DataConDef l -> DataDef n

data DataConDef n = DataConDef RawName (EmptyNest Binder n)   deriving (Show, Generic)

data NamedDataDef n = NamedDataDef (Name n) (DataDef n)  deriving (Show)

data Block n where Block :: Nest Decl n l -> Expr l -> Block n

type LamExpr = Abs Binder (WithArrow Block)  :: * -> *
type PiType  = Abs Binder (WithArrow Type)   :: * -> *

data WithArrow e n = WithArrow (Arrow n) (e n)

withoutArrow :: WithArrow e n -> e n
withoutArrow (WithArrow _ x) = x

justArrow :: WithArrow e n -> Arrow n
justArrow (WithArrow arr _) = arr

type Arrow n = ArrowP (EffectRow n)
data ArrowP eff =
   PlainArrow eff
 | ImplicitArrow
 | ClassArrow
 | TabArrow
 | LinArrow
   deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

data LetAnn = PlainLet
            | InstanceLet
            | SuperclassLet
            | NoInlineLet
              deriving (Show, Eq, Generic)

type Val  = Atom
type Type = Atom
type Kind = Type

type TC  n = PrimTC  (Atom n)
type Con n = PrimCon (Atom n)
type Op  n = PrimOp  (Atom n)
type Hof n = PrimHof (Atom n)

data SourceNameMap n = SourceNameMap
  { fromSourceNameMap :: M.Map SourceName (Name n)}

data Module n where
  Module :: IRVariant
         -> Nest Decl n l
         -> BindingsFrag l l'
         -> SourceNameMap l'
         -> Module n

type WithBindings = Abs BindingsFrag
type EvaluatedModule = WithBindings SourceNameMap  :: * -> *

emptyEvaluatedModule :: EvaluatedModule n
emptyEvaluatedModule = Abs (RecEnvFrag id) mempty

data IRVariant = Surface | Typed | Core | Simp | Evaluated
                 deriving (Show, Eq, Ord, Generic)

-- The label for a field in a record or variant.
type Label = String

-- Collection of labeled values of type `a`. Each value has a field label, and
-- multiple values can share the same label. This is the canonical form for
-- the item types in record and variant types as well as for the values in
-- record objects; the order in the concrete syntax of items with different
-- fields is discarded (so both `{b:Z & a:X & a:Y}` and `{a:X & b:Z & a:Y}` map
-- to `M.fromList [("a", NE.fromList [X, Y]), ("b", NE.fromList [Z])]` )
newtype LabeledItems a = LabeledItems (M.Map Label (NE.NonEmpty a))
  deriving (Eq, Show, Generic, Functor, Foldable, Traversable)

labeledSingleton :: Label -> a -> LabeledItems a
labeledSingleton label value = LabeledItems $ M.singleton label (value NE.:|[])

reflectLabels :: LabeledItems a -> LabeledItems (Label, Int)
reflectLabels (LabeledItems items) = LabeledItems $
  flip M.mapWithKey items \k xs -> fmap (\(i,_) -> (k,i)) (enumerate xs)

getLabels :: LabeledItems a -> [Label]
getLabels labeledItems = map fst $ toList $ reflectLabels labeledItems

withLabels :: LabeledItems a -> LabeledItems (Label, Int, a)
withLabels (LabeledItems items) = LabeledItems $
  flip M.mapWithKey items \k xs -> fmap (\(i,a) -> (k,i,a)) (enumerate xs)

lookupLabelHead :: LabeledItems a -> Label -> Maybe a
lookupLabelHead (LabeledItems items) l = case M.lookup l items of
  Nothing -> Nothing
  Just (x NE.:| _) -> Just x

-- Extensible version of LabeledItems, which allows an optional object in tail
-- position. The items of the tail object will always be interpreted as a
-- "suffix" in the sense that for any field label, the object represented by
-- an ExtLabeledItems contains first the values in the (LabeledItems a) for that
-- field, followed by the values in the (Maybe b) for that field if they exist.
data ExtLabeledItems a b = Ext (LabeledItems a) (Maybe b)
  deriving (Eq, Show, Generic)

-- Adds more items to the front of an ExtLabeledItems.
prefixExtLabeledItems :: LabeledItems a -> ExtLabeledItems a b -> ExtLabeledItems a b
prefixExtLabeledItems items (Ext items' rest) = Ext (items <> items') rest

-- === front-end language AST ===

type UExpr = WithSrcH UExpr'
data UExpr' n where
  UVar  :: UVar n                            -> UExpr' n
  ULam  :: UPatAnn n l -> UArrow -> UExpr l  -> UExpr' n
  UPi   :: UPatAnn n l -> Arrow l -> UType l -> UExpr' n
  UApp  :: UArrow -> UExpr n -> UExpr n      -> UExpr' n
  UDecl :: UDecl n l -> UExpr l              -> UExpr' n
  UFor  :: Direction -> UPatAnn n l -> UExpr l -> UExpr' n
  UCase :: UExpr n -> [UAlt n] -> UExpr' n
  UHole :: UExpr' n
  UTypeAnn :: UExpr n -> UExpr n -> UExpr' n
  UTabCon     :: [UExpr n] -> UExpr' n
  UIndexRange :: Limit (UExpr n) ->  Limit (UExpr n) -> UExpr' n
  UPrimExpr   :: PrimExpr (UExpr n) -> UExpr' n
  URecord :: ExtLabeledItems (UExpr n) (UExpr n)      -> UExpr' n  -- {a=x, b=y, ...rest}
  UVariant :: LabeledItems () -> Label -> UExpr n     -> UExpr' n  -- {|a|b| a=x |}
  UVariantLift :: LabeledItems () -> UExpr n          -> UExpr' n  -- {|a|b| ...rest |}
  URecordTy    :: ExtLabeledItems (UExpr n) (UExpr n) -> UExpr' n  -- {a:X & b:Y & ...rest}
  UVariantTy   :: ExtLabeledItems (UExpr n) (UExpr n) -> UExpr' n  -- {a:X | b:Y | ...rest}
  UIntLit   :: Int    -> UExpr' n
  UFloatLit :: Double -> UExpr' n

data UDataDef n where
  UDataDef :: UAnnBinderList n l -> ListH (EmptyNest UAnnBinder) l -> UDataDef n

data UDecl n l where
  ULet :: LetAnn ->  UPatAnn n l -> UExpr n -> UDecl n l
  UDataDefDecl
    :: UDataDef n
    -> PlainBinder n l         -- type constructor name
    ->   PlainBinderList l l'  -- data constructor names
    ->     UDecl n l'
  UInterface
    :: Nest UAnnBinder n p  -- class parameters
    ->   [UType p]          -- superclasses
    ->   [UType p]          -- method types
    -> PlainBinder n l          -- class name
    ->   PlainBinderList l l'   -- method names
    ->     UDecl n l'
  UInstance
    :: Nest UPatAnnArrow n l  -- dictionary args (i.e. conditions)
    ->   UType l              -- dictionary type
    ->   [UMethodDef l]       -- method definitions
    -> PlainBinder n l'           -- optional instance name
    ->   UDecl n l'

type UArrow = ArrowP ()
type UType  = UExpr          :: * -> *
type UVar    = Name          :: * -> *
data UMethodDef n = UMethodDef (UVar n) (UExpr n) deriving (Show, Generic)

type UPatAnn = AnnBinderP UPat (MaybeH UType)
type UPatAnnArrow = AnnBinderP UPatAnn (LiftH UArrow)

type UAnnBinder     = AnnBinderP     PlainBinder UType :: * -> * -> *
type UAnnBinderList = AnnBinderListP PlainBinder UType :: * -> * -> *

data UAlt n where
  UAlt :: UPat n l -> UExpr l -> UAlt n

data UModule n where
  UModule :: UDecl n l -> SourceNameMap l -> UModule n

type UPat = WithSrcH2 UPat'
data UPat' n l where
  UPatUnit   :: UPat' n n
  UPatBinder :: PlainBinder n l         -> UPat' n l
  UPatPair   :: UPat n n' -> UPat n' l  -> UPat' n l
  UPatCon    :: Name n -> Nest UPat n l -> UPat' n l
  UPatRecord :: ExtLabeledItems () () ->  Nest UPat n l   -> UPat' n l-- {a=x, b=y, ...rest}
  UPatVariant     :: LabeledItems () -> Label -> UPat n l -> UPat' n l  -- {|a|b| a=x |}
  UPatVariantLift :: LabeledItems () -> UPat n l          -> UPat' n l  -- {|a|b| ...rest |}
  UPatTable :: Nest UPat n l -> UPat' n l

pattern UnderscoreUPat :: UPat n n
pattern UnderscoreUPat = WithSrcH2 Nothing (UPatBinder Ignore)

-- === tracking source code positions ===

type SrcPos = (Int, Int)
type SrcCtx = Maybe SrcPos

data WithSrc   (a ::           *)     = WithSrc   SrcCtx a       deriving Show
data WithSrcH  (e ::      * -> *) n   = WithSrcH  SrcCtx (e n)   deriving Show
data WithSrcH2 (b :: * -> * -> *) n l = WithSrcH2 SrcCtx (b n l) deriving Show

srcPos :: WithSrc a -> SrcCtx
srcPos (WithSrc pos _) = pos

srcPosH :: WithSrcH e n -> SrcCtx
srcPosH (WithSrcH pos _) = pos

-- === primitive constructors and operators ===

data PrimExpr e =
        TCExpr  (PrimTC  e)
      | ConExpr (PrimCon e)
      | OpExpr  (PrimOp  e)
      | HofExpr (PrimHof e)
        deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

data PrimTC e =
        BaseType BaseType
      | IntRange e e
      | IndexRange e (Limit e) (Limit e)
      | IndexSlice e e      -- Sliced index set, slice length. Note that this is no longer an index set!
      | PairType e e
      | UnitType
      | RefType (Maybe e) e
      | TypeKind
      | EffectRowKind
      | LabeledRowKindTC
      | ParIndexRange e e e  -- Full index set, global thread id, thread count
        deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

data PrimCon e =
        Lit LitVal
      | PairCon e e
      | UnitCon
      | ClassDictHole SrcCtx e   -- Only used during type inference
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
      | FstRef e
      | SndRef e
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
      | ThrowError e
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

data PrimEffect e = MAsk | MExtend e | MGet | MPut e
    deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

data BinOp = IAdd | ISub | IMul | IDiv | ICmp CmpOp
           | FAdd | FSub | FMul | FDiv | FCmp CmpOp | FPow
           | BAnd | BOr | BShL | BShR | IRem
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

type IndexStructure = Nest Binder

strToPrimName :: String -> Maybe PrimName
strToPrimName s = M.lookup s builtinNames

primNameToStr :: PrimName -> String
primNameToStr prim = case lookup prim $ map swap $ M.toList builtinNames of
  Just s  -> s
  Nothing -> show prim

showPrimName :: PrimExpr e -> String
showPrimName prim = primNameToStr $ fmap (const ()) prim

getBaseMonoidType :: Scope n -> Type n -> Type n
getBaseMonoidType scope ty = case ty of
  TabTy i b -> case lowerNames scope (i@>()) b of
    Just b' -> b'
    Nothing -> error "Can't use a dependent table as a monoid"
  _         -> ty

-- === effects ===

data EffectRow n = EffectRow (S.Set (Effect n)) (Maybe (Name n))
                   deriving (Show, Eq, Generic)

data RWS = Reader | Writer | State               deriving (Show, Eq, Ord, Generic)
data Effect n = RWSEffect RWS (Name n) | ExceptionEffect | IOEffect
                deriving (Show, Eq, Ord, Generic)

pattern Pure :: EffectRow n
pattern Pure <- ((\(EffectRow effs t) -> (S.null effs, t)) -> (True, Nothing))
 where  Pure = mempty

outputStreamPtrName :: Name SourceNS
outputStreamPtrName = SourceName "OUT_STREAM_PTR"

-- hostPtrTy :: BaseType -> BaseType
-- hostPtrTy ty = PtrType (Heap CPU, ty)

-- === top-level constructs ===

type SourceModule = UDecl SourceNS SourceNS

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
data SourceBlock' = RunModule SourceModule
                  | Command CmdName (Name SourceNS, SourceModule)
                  | GetNameType (Name SourceNS)
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

data IExpr n = ILit LitVal
             | IVar (IVar n)
               deriving (Show)

type IPrimOp n = PrimOp (IExpr n)
type IVal = IExpr  -- only ILit and IRef constructors
type IBinder     = AnnBinderP PlainBinder            ITypeH
type IBinderList = AnnBinderP PlainBinderList (ListH ITypeH)
type IVar = AnnVarP ITypeH
type IType = BaseType
type Size = IExpr

type IFunVar = AnnVarP (LiftH IFunType)
data IFunType = IFunType CallingConvention [IType] [IType] -- args, results
                deriving (Show)

type ITypeH    = LiftH IType

data IsCUDARequired = CUDARequired | CUDANotRequired  deriving (Eq, Show)

data CallingConvention = CEntryFun
                       | EntryFun IsCUDARequired
                       | FFIFun
                       | FFIMultiResultFun
                       | CUDAKernelLaunch
                       | MCThreadLaunch
                         deriving (Show)

data ImpModule n where
  ImpModule :: PlainBinderList n l    -- local function names
            -> [IFunType]             -- local function types
            -> [ImpFunction l]        -- local function definitions
            -> Maybe (ImpFunction l)  -- optional main function definition
            -> ImpModule n

data ImpFunction n where
  ImpFunction :: IBinderList n l -> ImpBlock l -> ImpFunction n
  FFIFunction :: String -> ImpFunction n

data ImpBlock n where
  ImpBlock :: Nest ImpDecl n l ->  [IExpr l] -> ImpBlock n

data ImpDecl n l = ImpLet (Nest IBinder n l) (ImpInstr n) deriving (Show)
data ImpInstr n =
   IFor Direction (Size n) (Abs IBinder ImpBlock n)
 | IWhile (ImpBlock n)
 | ICond (IExpr n) (ImpBlock n) (ImpBlock n)
 | IQueryParallelism (IFunVar n) (IExpr n) -- returns the number of available concurrent threads
 | ISyncWorkgroup
 | ILaunch (IFunVar n) (Size n) [IExpr n]
 | ICall (IFunVar n) [IExpr n]
 | Store (IExpr n) (IExpr n)           -- dest, val
 | Alloc AddressSpace IType (Size n)
 | MemCopy (IExpr n) (IExpr n) (IExpr n)   -- dest, source, numel
 | Free (IExpr n)
 | IThrowError  -- TODO: parameterize by a run-time string
 | ICastOp IType (IExpr n)
 | IPrimOp (IPrimOp n)
   deriving (Show)

data Backend = LLVM | LLVMCUDA | LLVMMC | Interpreter  deriving (Show, Eq)
newtype CUDAKernel = CUDAKernel B.ByteString deriving (Show)

-- === base types ===

data LitVal = Int64Lit   Int64
            | Int32Lit   Int32
            | Word8Lit   Word8
            | Float64Lit Double
            | Float32Lit Float
            | PtrLit PtrType (Ptr ())
            | VecLit [LitVal]  -- Only one level of nesting allowed!
              deriving (Show, Eq, Ord, Generic)

data ScalarBaseType = Int64Type | Int32Type | Word8Type
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
  Scalar Float64Type -> 8
  Scalar Float32Type -> 4
  PtrType _          -> ptrSize
  Vector st          -> vectorWidth * sizeOf (Scalar st)

ptrSize :: Int
ptrSize = 8

vectorWidth :: Int
vectorWidth = 4

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

data PassName = Parse | TypePass | SynthPass | SimpPass | ImpPass | JitPass
              | LLVMOpt | AsmPass | JAXPass | JAXSimpPass | LLVMEval
              | ResultPass | JaxprAndHLO | OptimPass
                deriving (Ord, Eq, Bounded, Enum)

instance Show PassName where
  show p = case p of
    Parse    -> "parse" ; TypePass -> "typed"   ; SynthPass -> "synth"
    SimpPass -> "simp"  ; ImpPass  -> "imp"     ; JitPass   -> "llvm"
    LLVMOpt  -> "llvmopt" ; AsmPass   -> "asm"
    JAXPass  -> "jax"   ; JAXSimpPass -> "jsimp"; ResultPass -> "result"
    LLVMEval -> "llvmeval" ; JaxprAndHLO -> "jaxprhlo"; OptimPass -> "optimized"

-- === outputs ===

type LitProg = [(SourceBlock, Result)]
data Result = Result [Output] (Except ())  deriving (Show, Eq)

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

data Err = Err ErrType SrcCtx String  deriving (Show, Eq)
data ErrType = NoErr
             | ParseErr
             | TypeErr
             | KindErr
             | LinErr
             | UnboundVarErr
             | LeakedVarErr
             | RepeatedVarErr
             | CompilerErr
             | IRVariantErr
             | NotImplementedErr
             | DataIOErr
             | MiscErr
             | RuntimeErr
               deriving (Show, Eq)

type Except = Either Err

throw :: MonadError Err m => ErrType -> String -> m a
throw e s = throwError $ Err e Nothing s

throwIf :: MonadError Err m => Bool -> ErrType -> String -> m ()
throwIf True  e s = throw e s
throwIf False _ _ = return ()

modifyErr :: MonadError e m => m a -> (e -> e) -> m a
modifyErr m f = catchError m \e -> throwError (f e)

addContext :: MonadError Err m => String -> m a -> m a
addContext s m = modifyErr m \(Err e p s') -> Err e p (s' ++ "\n" ++ s)

addSrcContext :: MonadError Err m => SrcCtx -> m a -> m a
addSrcContext ctx m = modifyErr m updateErr
  where
    updateErr :: Err -> Err
    updateErr (Err e ctx' s) = case ctx' of Nothing -> Err e ctx  s
                                            Just _  -> Err e ctx' s

catchIOExcept :: (MonadIO m , MonadError Err m) => IO a -> m a
catchIOExcept m = (liftIO >=> liftEither) $ (liftM Right m) `catches`
  [ Handler \(e::Err)           -> return $ Left e
  , Handler \(e::IOError)       -> return $ Left $ Err DataIOErr   Nothing $ show e
  , Handler \(e::SomeException) -> return $ Left $ Err CompilerErr Nothing $ show e
  ]

liftEitherIO :: (Exception e, MonadIO m) => Either e a -> m a
liftEitherIO (Left err) = liftIO $ throwIO err
liftEitherIO (Right x ) = return x

instance MonadFail (Either Err) where
  fail s = Left $ Err CompilerErr Nothing s

-- === UExpr free variables ===

class HasUVars (e :: * -> *) where
  freeUVars :: e n -> NameSet n

-- -- class BindsUVars (b :: * -> * -> *) where
-- --   boundUVars :: b n l -> BinderListP UnitH n l

-- instance HasUVars a => HasUVars [a] where
--   freeUVars xs = foldMap freeUVars xs

-- instance HasUVars a => HasUVars (NE.NonEmpty a) where
--   freeUVars xs = foldMap freeUVars xs

-- instance (BindsUVars a, HasUVars a) => HasUVars (Nest a) where
--   freeUVars Empty = mempty
--   freeUVars (Nest x xs) = freeUVars x <> (freeUVars xs `envDiff` boundUVars x)

-- instance BindsUVars a => BindsUVars (Nest a) where
--   boundUVars xs = foldMap boundUVars xs

-- instance (HasUVars b, BindsUVars b, HasUVars body)
--          => HasUVars (Abs b body) where
--   freeUVars (Abs b body) = freeUVars b <> (freeUVars body `envDiff` boundUVars b)

-- instance HasUVars a => HasUVars (WithSrc a) where
--   freeUVars (WithSrc _ e) = freeUVars e

-- instance HasUVars UExpr' where
--   freeUVars expr = case expr of
--     UVar v -> v @>()
--     -- ULam (pat,ty) _ body -> freeUVars ty <> freeUVars (Abs pat body)
--     -- UPi (pat,kind) arr ty -> freeUVars kind <> freeUVars (Abs pat (arr, ty))
--     -- -- TODO: maybe distinguish table arrow application
--     -- -- (otherwise `x.i` and `x i` are the same)
--     -- UApp _ f x -> freeUVars f <> freeUVars x
--     -- UDecl decl body -> freeUVars $ Abs decl body
--     -- UFor _ (pat,ty) body -> freeUVars ty <> freeUVars (Abs pat body)
--     -- UHole -> mempty
--     -- UTypeAnn v ty -> freeUVars v <> freeUVars ty
--     -- UTabCon xs -> foldMap freeUVars xs
--     -- UIndexRange low high -> foldMap freeUVars low <> foldMap freeUVars high
--     -- UPrimExpr prim -> foldMap freeUVars prim
--     -- UCase e alts -> freeUVars e <> foldMap freeUVars alts
--     -- URecord ulr -> freeUVars ulr
--     -- UVariant types _ val -> freeUVars types <> freeUVars val
--     -- URecordTy ulr -> freeUVars ulr
--     -- UVariantTy ulr -> freeUVars ulr
--     -- UVariantLift skip val -> freeUVars skip <> freeUVars val
--     -- UIntLit  _ -> mempty
--     -- UFloatLit _ -> mempty

-- instance HasUVars UAlt where
--   freeUVars (UAlt p body) = freeUVars $ Abs p body

-- instance HasUVars () where
--   freeUVars = mempty

-- instance HasUVars UPat' where
--   freeUVars pat = case pat of
--     -- UPatBinder _   -> mempty
--     -- UPatCon con ps -> con @> () <> foldMap freeUVars ps
--     -- UPatPair p1 p2 -> freeUVars p1 <> freeUVars p2
--     UPatUnit       -> mempty
--     -- UPatRecord items -> freeUVars items
--     -- UPatVariant _ _ p -> freeUVars p
--     -- UPatVariantLift _ p -> freeUVars p
--     -- UPatTable ps -> foldMap freeUVars ps

-- instance BindsUVars UPat' where
--   boundUVars pat = case pat of
--     -- UPatBinder v   -> v @> ()
--     -- UPatCon _ ps   -> foldMap boundUVars ps
--     -- UPatPair p1 p2 -> boundUVars p1 <> boundUVars p2
--     UPatUnit       -> mempty
--     -- UPatRecord items -> boundUVars items
--     -- UPatVariant _ _ p -> boundUVars p
--     -- UPatVariantLift _ p -> boundUVars p
--     -- UPatTable ps -> foldMap boundUVars ps

-- instance HasUVars UDecl where
--   freeUVars (ULet _ p expr) = freeUVars p <> freeUVars expr
--   -- freeUVars (UData (UConDef _ bs) dataCons) = freeUVars $ Abs bs dataCons
--   -- freeUVars (UInterface superclasses tc methods) =
--   --   freeUVars $ Abs tc (superclasses, methods)
--   -- freeUVars (UInstance _ bsArrows ty methods) = freeUVars $ Abs bs (ty, methods)
--   --   where bs = fmap fst bsArrows

-- -- instance HasUVars UMethodDef where
-- --   freeUVars (UMethodDef _ def) = freeUVars def

-- -- instance BindsUVars UPatAnn where
-- --   boundUVars (p, _) = boundUVars p

-- instance BindsUVars UDecl where
--   boundUVars decl = case decl of
--     ULet _ (p,_) _           -> boundUVars p
--     -- UData tyCon dataCons     -> boundUVars tyCon <> foldMap boundUVars dataCons
--     -- UInterface _ _ _         -> mempty
--     -- UInstance Nothing  _ _ _ -> mempty
--     -- UInstance (Just v) _ _ _ -> v @> ()

-- instance HasUVars UModule where
--   freeUVars (UModule decls) = freeUVars decls

-- instance BindsUVars UModule where
--   boundUVars (UModule decls) = boundUVars decls

-- instance HasUVars SourceBlock where
--   freeUVars block = uVarsAsGlobal $
--     case sbContents block of
--       RunModule (   m) -> freeUVars m
--       Command _ (_, m) -> freeUVars m
--       GetNameType v -> v @> ()
--       _ -> mempty

-- instance BindsUVars SourceBlock where
--   boundUVars block = uVarsAsGlobal $
--     case sbContents block of
--       RunModule (   m) -> boundUVars m
--       _ -> mempty

-- instance HasUVars EffectRow where
--   freeUVars (EffectRow effs tailVar) =
--     foldMap freeUVars effs <> foldMap nameAsEnv tailVar

-- instance HasUVars Effect where
--   freeUVars (RWSEffect _ h) = nameAsEnv h
--   freeUVars ExceptionEffect = mempty
--   freeUVars IOEffect        = mempty

-- instance HasUVars a => HasUVars (LabeledItems a) where
--   freeUVars (LabeledItems items) = foldMap freeUVars items

-- instance HasUVars a => HasUVars (ExtLabeledItems a a) where
--   freeUVars (Ext items rest) = freeUVars items <> freeUVars rest

-- instance HasUVars eff => HasUVars (ArrowP eff) where
--   freeUVars (PlainArrow eff) = freeUVars eff
--   freeUVars _ = mempty

-- instance (HasUVars a, HasUVars b) => HasUVars (a, b) where
--   freeUVars (x, y) = freeUVars x <> freeUVars y

-- instance HasUVars a => HasUVars (Maybe a) where
--   freeUVars Nothing = mempty
--   freeUVars (Just x) = freeUVars x

-- instance HasUVars a => HasUVars (BinderP a) where
--   freeUVars b = freeUVars $ binderAnn b

-- instance HasUVars a => BindsUVars (BinderP a) where
--   boundUVars b = b @> ()

-- -- instance HasUVars UConDef where
-- --   freeUVars (UConDef _ bs) = freeUVars bs

-- -- instance BindsUVars UConDef where
-- --   boundUVars (UConDef con _) = con @>()

-- instance BindsUVars a => BindsUVars (WithSrc a) where
--   boundUVars (WithSrc _ x) = boundUVars x

-- instance BindsUVars a => BindsUVars (LabeledItems a) where
--   boundUVars items = foldMap boundUVars items

-- instance BindsUVars a => BindsUVars (ExtLabeledItems a a) where
--   boundUVars (Ext items rest) = boundUVars items <> boundUVars rest

-- instance BindsUVars a => BindsUVars (Maybe a) where
--   boundUVars Nothing = mempty
--   boundUVars (Just x) = boundUVars x

-- nameAsEnv :: Name -> UVars
-- nameAsEnv v = v@>()

-- === Recursive bindings ===

data BinderInfo n =
   LamBound (ArrowP ())
 -- TODO: make the expression optional, for when it's effectful?
 -- (or we could put the effect tag on the let annotation)
 | PatBound
 | LetBound LetAnn (Expr n)
 | PiBound
 | UnknownBinder
 | DataDefName (DataDef n)
 | ClassName -- TODO
 | MethodName  (NamedDataDef n) Int  -- TODO: just have a class name and a label
 | DataConName (NamedDataDef n) Int
 | TypeConName (NamedDataDef n)
 -- TODO: avoid this case by having the inference monad use an alternative
 -- version of BinderInfo
 | InferenceName
   deriving (Show, Generic)

data TypedBinderInfo n = TypedBinderInfo (Maybe (Type n)) (BinderInfo n)

type BindingsFrag = RecEnvFrag TypedBinderInfo :: * -> * -> *
type Bindings = BindingsFrag VoidNS

emptyBindings :: Bindings VoidNS
emptyBindings = RecEnvFrag voidEnv

-- === Substitution with Atoms ===

-- TODO: make this just `Env (Atom o) i` if we remove type annotations from
-- variable occurrences
type AtomSubstVal = SubstVal Atom
type SubstEnvFrag i i' o = EnvFrag (AtomSubstVal o) i i'
type SubstEnv i o = SubstEnvFrag o i o

data CoreNameTraversal m i o where
  CoreNameTraversal :: (Name i -> m (AtomSubstVal o))
                    -> RenameEnvFrag i i' o
                    -> CoreNameTraversal m i' o

class HasNames e => Subst e where
  traverseNamesCore
    :: Monad m
    => Scope o
    -> CoreNameTraversal m i o
    -> e i
    -> m (e o)

class BindsNames b => BindsNamesCore (b :: * -> * -> *) where
  traverseNamesCoreBinders
    :: Monad m
    => Scope o
    -> CoreNameTraversal m i o
    -> b i i'
    -> m (Fresh b i i' o)

  asBindingsFrag :: b n l -> BindingsFrag n l

traverseFreeNamesFromSubst :: (Subst e, Monad m)
                           => Scope o -> NameTraversal m i o -> e i -> m (e o)
traverseFreeNamesFromSubst scope (NameTraversal f renamer) e =
  traverseNamesCore scope (CoreNameTraversal f' renamer) e
  where f' name = Rename <$> f name

traverseFreeNamesBindersFromBindsNamesCore
  :: (BindsNamesCore b, Monad m)
  => Scope o -> NameTraversal m i o -> b i i' -> m (Fresh b i i' o)
traverseFreeNamesBindersFromBindsNamesCore _ _ _ = undefined

fmapAtomNames :: Subst e => Scope o -> (Name i -> AtomSubstVal o) -> e i -> e o
fmapAtomNames scope f e = runIdentity $ traverseNamesCore scope t e
  where t = CoreNameTraversal (pure . f) id

applySubst :: Subst e => Scope o -> SubstEnv i o -> e i -> e o
applySubst scope env e = fmapAtomNames scope (substEnvLookup env) e

substEnvLookup :: SubstEnv i o -> Name i -> AtomSubstVal o
substEnvLookup subst name = case envFragLookup subst name of
  Left name' -> Rename name'
  Right val -> val

-- instance (BindsNamesCore b, HasNames body) => HasNames (Abs b body) where
--   freeVars (Abs b body) = freeVars b <> (freeVars body `envDiff` boundVars b)

-- instance (BindsNamesCore b, Subst body) => Subst (Abs b body) where
--   subst env (Abs b body) = Abs b' body'
--     where (b', env') = renamingSubst env b
--           body' = subst (env <> env') body

-- instance BindsNamesCore a => HasNames (Nest a) where
--   freeVars xs = case xs of
--     Empty -> mempty
--     Nest b rest -> freeVars b <> (freeVars rest `envDiff` boundVars b)

-- instance (Subst a, BindsNamesCore a) => Subst (Nest a) where
--   subst env xs = case xs of
--     Empty -> Empty
--     Nest x rest -> Nest x' rest'
--       where x' = subst env x
--             env' = (mempty, boundVars x')
--             rest' = subst (env <> env') rest

-- instance BindsNamesCore a => BindsNamesCore (Nest a) where
--   boundVars xs = foldMap boundVars xs
--   renamingSubst env xs = case xs of
--     Empty -> (Empty, mempty)
--     Nest x rest -> (Nest x' rest', xEnv <> restEnv)
--       where
--         (x', xEnv) = renamingSubst env x
--         (rest', restEnv) = renamingSubst (env <> xEnv) rest

-- instance HasNames Binder where
--   freeVars b = freeVars $ binderType b

-- instance Subst Binder where
--   -- BUG: the following case should be unreachable but it shows up in tests
--   -- subst env@(_, scope) b | b `isin` scope = error $ "shadowed binder: " ++ show b
--   -- XXX: this doesn't rename the bound vars, so they must not be in scope
--   subst env b = fmap (subst env) b

-- instance BindsNamesCore Binder where
--   boundVars b = b @> (binderType b, UnknownBinder)
--   renamingSubst env (Ignore ty) = (Ignore (subst env ty), mempty)
--   renamingSubst env@(_, scope) b@(Bind (v:>ty)) = (b', env')
--     where v' = genFresh v scope
--           b' = Bind (v':>ty')
--           ty' = subst env ty
--           env' = (b@>Var (v':>ty'), b'@>(ty', UnknownBinder))

-- instance HasNames DataConRefBinding where
--   freeVars (DataConRefBinding b ref) = freeVars b <> freeVars ref

-- instance Subst DataConRefBinding where
--   subst env (DataConRefBinding b ref) =
--     DataConRefBinding (subst env b) (subst env ref)

-- instance BindsNamesCore DataConRefBinding where
--   boundVars (DataConRefBinding b _) = b @> (binderType b, UnknownBinder)
--   renamingSubst env (DataConRefBinding b ref) = (DataConRefBinding b' ref', env')
--     where
--       ref' = subst env ref
--       (b', env') = renamingSubst env b

-- instance Eq Atom where
--   Var v == Var v' = v == v'
--   Pi ab == Pi ab' = ab == ab'
--   DataCon def params con args == DataCon def' params' con' args' =
--     def == def' && params == params' && con == con' && args == args'
--   TypeCon def params == TypeCon def' params' = def == def' && params == params'
--   Variant lr l i v == Variant lr' l' i' v' =
--     (lr, l, i, v) == (lr', l', i', v')
--   Record lr    == Record lr'      = lr == lr'
--   RecordTy lr  == RecordTy lr'    = lr == lr'
--   VariantTy lr == VariantTy lr'   = lr == lr'
--   Con con == Con con' = con == con'
--   TC  con == TC  con' = con == con'
--   Eff eff == Eff eff' = eff == eff'
--   ProjectElt idxs v == ProjectElt idxs' v' = (idxs, v) == (idxs', v')
--   _ == _ = False

-- instance Eq DataDef where
--   DataDef name _ _ == DataDef name' _ _ = name == name'

-- instance (Show a, Subst a, Eq a) => Eq (Abs Binder a) where
--   Abs (Ignore a) b == Abs (Ignore a') b' = a == a' && b == b'
--   ab == ab' = absArgType ab == absArgType ab' && applyAbs ab v == applyAbs ab' v
--     where v = Var $ freshSkolemVar (ab, ab') (absArgType ab)

-- instance Eq (Nest Binder) where
--   Empty == Empty = True
--   (Nest b bs) == (Nest b' bs') = Abs b bs == Abs b' bs'
--   _ == _ = False

-- freshSkolemVar :: HasNames a => a -> Type -> Var
-- freshSkolemVar x ty = v :> ty
--   where v = genFresh (rawName Skolem "skol") (freeVars x)

applyAbs :: Subst e => Scope n -> Abs Binder e n -> Atom n -> e n
applyAbs scope (Abs b body) x = applySubst scope (b@>SubstVal x) body

applyNaryAbs :: Subst e => Scope n -> Abs (Nest Binder) e n -> [Atom n] -> e n
applyNaryAbs _ (Abs Empty body) [] = body
applyNaryAbs scope (Abs (Nest b bs) body) (x:xs) =
  applyNaryAbs scope ab xs
  where ab = applyAbs scope (Abs b (Abs bs body)) x
applyNaryAbs _ _ _ = error "wrong number of arguments"

-- TODO: see if we can avoid needing this version
scopelessApplyAbs :: Subst e => Abs Binder e n -> Atom n -> e n
scopelessApplyAbs ab x = withTempScope (PairH ab x) \ext scope (PairH ab' x') ->
  liftNames ext $ applyAbs scope ab' x'

scopelessApplyNaryAbs :: Subst e => Abs (Nest Binder) e n -> [Atom n] -> e n
scopelessApplyNaryAbs ab xs = withTempScope (PairH ab (H xs)) \ext scope (PairH ab' (H xs')) ->
  liftNames ext $ applyNaryAbs scope ab' xs'

applyDataDefParams :: DataDef n -> [Type n] -> [DataConDef n]
applyDataDefParams = undefined
-- applyDataDefParams (DataDef _ bs cons) params
--   | length params == length (toList bs) = applyNaryAbs (Abs bs cons) params
--   | otherwise = error $ "Wrong number of parameters: " ++ show (length params)

-- makeAbs :: HasNames a => Binder -> a -> Abs Binder e n
-- makeAbs b body | b `isin` freeVars body = Abs b body
--                | otherwise = Abs (Ignore (binderType b)) body

absArgType :: Abs Binder e n -> Type n
absArgType (Abs b _) = binderType b

-- toNest :: [a] -> Nest a
-- toNest = foldr Nest Empty

-- instance HasNames Arrow where
--   freeVars arrow = case arrow of
--     PlainArrow eff -> freeVars eff
--     _ -> mempty
-- instance Subst Arrow where
--   subst env arrow = case arrow of
--     PlainArrow eff -> PlainArrow $ subst env eff
--     _ -> arrow

arrowEff :: Arrow n -> EffectRow n
arrowEff (PlainArrow eff) = eff
arrowEff _ = Pure

-- substVar :: (SubstEnv, Scope) -> Var -> Atom
-- substVar env@(sub, scope) v = case envLookup sub v of
--   Nothing -> Var $ fmap (subst env) v
--   Just x' -> deShadow x' scope

-- deShadow :: Subst a => a -> Scope -> a
-- deShadow x scope = subst (mempty, scope) x

-- instance HasNames Expr where
--   freeVars expr = case expr of
--     App f x -> freeVars f <> freeVars x
--     Atom x  -> freeVars x
--     Op  e   -> foldMap freeVars e
--     Hof e   -> foldMap freeVars e
--     Case e alts resultTy ->
--       freeVars e <> freeVars alts <> freeVars resultTy

-- instance Subst Expr where
--   subst env expr = case expr of
--     App f x -> App (subst env f) (subst env x)
--     Atom x  -> Atom $ subst env x
--     Op  e   -> Op  $ fmap (subst env) e
--     Hof e   -> Hof $ fmap (subst env) e
--     Case e alts resultTy ->
--       Case (subst env e) (subst env alts) (subst env resultTy)

-- instance HasNames Decl where
--   freeVars decl = case decl of
--     Let _  b expr  -> freeVars expr <> freeVars b

-- instance Subst Decl where
--   subst env decl = case decl of
--     Let ann b expr -> Let ann (fmap (subst env) b) $ subst env expr


  --   boundVars decl = case decl of
--     Let ann b expr -> b @> (binderType b, LetBound ann expr)

--   renamingSubst env decl = case decl of
--     Let ann b expr -> (Let ann b' expr', env')
--       where expr' = subst env expr
--             (b', env') = renamingSubst env b

-- instance HasNames Block where
--   freeVars (Block decls result) = freeVars $ Abs decls result
-- instance Subst Block where
--   subst env (Block decls result) = Block decls' result'
--     where Abs decls' result' = subst env $ Abs decls result

-- instance HasNames Atom where
--   freeVars atom = case atom of
--     Var v@(_:>t) -> (v @> (t, UnknownBinder)) <> freeVars t
--     Lam lam -> freeVars lam
--     Pi  ty  -> freeVars ty
--     Con con -> foldMap freeVars con
--     TC  tc  -> foldMap freeVars tc
--     Eff eff -> freeVars eff
--     -- TODO: think about these cases. We don't want to needlessly traverse the
--     --       data definition but we might need to know the free Vars.
--     DataCon _ params _ args -> freeVars params <> freeVars args
--     TypeCon _ params        -> freeVars params
--     LabeledRow la -> freeVars la
--     Record la -> freeVars la
--     Variant la _ _ val -> freeVars la <> freeVars val
--     RecordTy row -> freeVars row
--     VariantTy row -> freeVars row
--     ACase e alts rty -> freeVars e <> freeVars alts <> freeVars rty
--     DataConRef _ params args -> freeVars params <> freeVars args
--     BoxedRef b ptr size body ->
--       freeVars ptr <> freeVars size <> freeVars (Abs b body)
--     ProjectElt _ v -> freeVars (Var v)

-- instance Subst Atom where
--   subst env atom = case atom of
--     Var v   -> substVar env v
--     Lam lam -> Lam $ subst env lam
--     Pi  ty  -> Pi  $ subst env ty
--     TC  tc  -> TC  $ fmap (subst env) tc
--     Con con -> Con $ fmap (subst env) con
--     Eff eff -> Eff $ subst env eff
--     DataCon def params con args -> DataCon def (subst env params) con (subst env args)
--     TypeCon def params          -> TypeCon def (subst env params)
--     LabeledRow row -> LabeledRow $ subst env row
--     Record la -> Record $ subst env la
--     Variant row label i val -> Variant (subst env row) label i (subst env val)
--     RecordTy row -> RecordTy $ subst env row
--     VariantTy row -> VariantTy $ subst env row
--     ACase v alts rty -> ACase (subst env v) (subst env alts) (subst env rty)
--     DataConRef def params args -> DataConRef def (subst env params) args'
--       where Abs args' () = subst env $ Abs args ()
--     BoxedRef b ptr size body -> BoxedRef b' (subst env ptr) (subst env size) body'
--         where Abs b' body' = subst env $ Abs b body
--     ProjectElt idxs v -> getProjection (toList idxs) $ substVar env v

-- instance HasNames Module where
--   freeVars (Module _ decls bindings) = freeVars $ Abs decls bindings
-- instance Subst Module where
--   subst env (Module variant decls bindings) = Module variant decls' bindings'
--     where Abs decls' bindings' = subst env $ Abs decls bindings

-- instance HasNames EffectRow where
--   freeVars (EffectRow row t) = foldMap freeVars row
--                             <> foldMap (\v -> v@>(EffKind, UnknownBinder)) t
-- instance Subst EffectRow where
--   subst env (EffectRow row t) = extendEffRow row' t'
--    where
--      row' = S.map (subst env) row
--      t' = substEffTail (fst env) t

-- instance HasNames Effect where
--   freeVars eff = case eff of
--     RWSEffect _ v -> v@>(TyKind , UnknownBinder)
--     ExceptionEffect -> mempty
--     IOEffect        -> mempty
-- instance Subst Effect where
--   subst (env,_) eff = case eff of
--     RWSEffect rws v -> RWSEffect rws (substName env v)
--     ExceptionEffect -> ExceptionEffect
--     IOEffect        -> IOEffect

-- instance HasNames BinderInfo where
--   freeVars binfo = case binfo of
--    LetBound _ expr -> freeVars expr
--    _ -> mempty

-- instance Subst BinderInfo where
--   subst env binfo = case binfo of
--    LetBound a expr -> LetBound a $ subst env expr
--    _ -> binfo

-- instance HasNames DataConDef where
--   freeVars (DataConDef _ bs) = freeVars $ Abs bs ()
-- instance Subst DataConDef where
--   subst env (DataConDef name bs) = DataConDef name bs'
--     where Abs bs' () = subst env $ Abs bs ()

-- instance HasNames a => HasNames (LabeledItems a) where
--   freeVars (LabeledItems items) = foldMap freeVars items

-- instance Subst a => Subst (LabeledItems a) where
--   subst env (LabeledItems items) = LabeledItems $ fmap (subst env) items

-- instance HasNames a => HasNames (ExtLabeledItems a Name) where
--   freeVars (Ext items Nothing) = freeVars items
--   freeVars (Ext items (Just v)) =
--     freeVars items <> (v @> (LabeledRowKind, UnknownBinder))

-- instance Subst (ExtLabeledItems Type Name) where
--   subst env@(env', _) (Ext items rest) =
--     prefixExtLabeledItems (subst env items) (substExtLabeledItemsTail env' rest)

-- substEffTail :: SubstEnv i o -> Maybe (Name i) -> EffectRow o
-- substEffTail _ Nothing = EffectRow mempty Nothing
-- substEffTail env (Just v) = case envLookup env v of
--   Left v' -> EffectRow mempty (Just v')
--   Right (Var (v':>_)) -> EffectRow mempty (Just v')
--   Right (Eff r) -> r
--   _ -> error "Not a valid effect substitution"

-- substName :: SubstEnv i o -> Name i -> Name o
-- substName env v = case envLookup env v of
--   Left v' -> v'
--   Right (Var (v':>_)) -> v'
--   _ -> error "Should only substitute with a name"

-- extendEffRow :: S.Set Effect -> EffectRow -> EffectRow
-- extendEffRow effs (EffectRow effs' t) = EffectRow (effs <> effs') t

-- substExtLabeledItemsTail :: SubstEnv -> Maybe Name -> ExtLabeledItems Type Name
-- substExtLabeledItemsTail _ Nothing = NoExt NoLabeledItems
-- substExtLabeledItemsTail env (Just v) = case envLookup env (v:>()) of
--   Nothing -> Ext NoLabeledItems $ Just v
--   Just (Var (v':>_)) -> Ext NoLabeledItems $ Just v'
--   Just (LabeledRow row) -> row
--   _ -> error "Not a valid labeled row substitution"

getProjection :: [Int] -> Atom n -> Atom n
getProjection [] a = a
getProjection (i:is) a = case getProjection is a of
  Var v -> ProjectElt (NE.fromList [i]) v
  ProjectElt idxs' a' -> ProjectElt (NE.cons i idxs') a'
  DataCon _ _ _ xs -> xs !! i
  Record items -> toList items !! i
  PairVal x _ | i == 0 -> x
  PairVal _ y | i == 1 -> y
  _ -> error $ "Not a valid projection: " ++ show i ++ " of " ++ show a

-- instance HasNames () where freeVars () = mempty
-- instance Subst () where subst _ () = ()

-- instance (HasNames a, HasNames b) => HasNames (a, b) where
--   freeVars (x, y) = freeVars x <> freeVars y
-- instance (Subst a, Subst b) => Subst (a, b) where
--   subst env (x, y) = (subst env x, subst env y)

-- instance HasNames a => HasNames (Maybe a) where freeVars x = foldMap freeVars x
-- instance Subst a => Subst (Maybe a) where subst env x = fmap (subst env) x

-- instance HasNames a => HasNames (Env a) where freeVars x = foldMap freeVars x
-- instance Subst a => Subst (Env a) where subst env x = fmap (subst env) x

-- instance HasNames a => HasNames [a] where freeVars x = foldMap freeVars x
-- instance Subst a => Subst [a] where subst env x = fmap (subst env) x

-- instance HasNames a => HasNames (NE.NonEmpty a) where freeVars x = foldMap freeVars x
-- instance Subst a => Subst (NE.NonEmpty a) where subst env x = fmap (subst env) x

-- instance Eq SourceBlock where
--   x == y = sbText x == sbText y

-- instance Ord SourceBlock where
--   compare x y = compare (sbText x) (sbText y)

class HasIVars (e :: * -> *) where
  freeIVars :: e n -> NameSet n

-- instance HasIVars IExpr where
--   freeIVars e = case e of
--     ILit _        -> mempty
--     IVar v@(_:>t) -> v @> t <> freeIVars t

-- instance HasIVars IType where
--   freeIVars _ = mempty

-- instance HasIVars ImpBlock where
--   freeIVars (ImpBlock Empty results) = foldMap freeIVars results
--   freeIVars (ImpBlock (Nest (ImpLet bs instr) rest) results) =
--     freeIVars instr <>
--       (freeIVars (ImpBlock rest results) `envDiff` newEnv bs (repeat ()))

-- instance HasIVars ImpInstr where
--   freeIVars i = case i of
--     IFor _ b n p      -> freeIVars n <> (freeIVars p `envDiff` (b @> ()))
--     IWhile p          -> freeIVars p
--     ICond  c t f      -> freeIVars c <> freeIVars t <> freeIVars f
--     IQueryParallelism _ s -> freeIVars s
--     ISyncWorkgroup      -> mempty
--     ILaunch _ size args -> freeIVars size <> foldMap freeIVars args
--     ICall   _      args -> foldMap freeIVars args
--     Store d e     -> freeIVars d <> freeIVars e
--     Alloc _ t s   -> freeIVars t <> freeIVars s
--     MemCopy x y z -> freeIVars x <> freeIVars y <> freeIVars z
--     Free x        -> freeIVars x
--     ICastOp t x   -> freeIVars t <> freeIVars x
--     IPrimOp op    -> foldMap freeIVars op
--     IThrowError   -> mempty

-- instance Semigroup (Nest a) where
--   (<>) = mappend

-- -- TODO: think about performance. This is used with the Cat/Writer monad a lot.
-- instance Monoid (Nest a) where
--   mempty = Empty
--   mappend xs ys = toNest $ toList xs ++ toList ys

-- === Helpers for function evaluation over fixed-width types ===

applyIntBinOp' :: (forall a. (Eq a, Ord a, Num a, Integral a) => (a -> Atom n) -> a -> a -> Atom n) -> Atom n -> Atom n -> Atom n
applyIntBinOp' f x y = case (x, y) of
  (Con (Lit (Int64Lit xv)), Con (Lit (Int64Lit yv))) -> f (Con . Lit . Int64Lit) xv yv
  (Con (Lit (Int32Lit xv)), Con (Lit (Int32Lit yv))) -> f (Con . Lit . Int32Lit) xv yv
  (Con (Lit (Word8Lit xv)), Con (Lit (Word8Lit yv))) -> f (Con . Lit . Word8Lit) xv yv
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

binderType :: Binder n l -> Type n
binderType (_:>ann) = ann

infixr 1 -->
infixr 1 --@
infixr 2 ==>

(-->) :: Type n -> Type n -> Type n
a --> b = Pi (Abs (Ignore:>a) (WithArrow PureArrow b))

(--@) :: Type n -> Type n -> Type n
a --@ b = Pi (Abs (Ignore:>a) (WithArrow LinArrow b))

(==>) :: Type n -> Type n -> Type n
a ==> b = Pi (Abs (Ignore:>a) (WithArrow TabArrow b))

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
pattern IdxRepTy = TC (BaseType IIdxRepTy)

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

pattern PairVal :: Atom n -> Atom n -> Atom n
pattern PairVal x y = Con (PairCon x y)

pattern PairTy :: Type n -> Type n -> Type n
pattern PairTy x y = TC (PairType x y)

pattern UnitVal :: Atom n
pattern UnitVal = Con UnitCon

pattern UnitTy :: Type n
pattern UnitTy = TC UnitType

pattern BaseTy :: BaseType -> Type n
pattern BaseTy b = TC (BaseType b)

pattern PtrTy :: PtrType -> Type n
pattern PtrTy ty = BaseTy (PtrType ty)

pattern RefTy :: Atom n -> Type n -> Type n
pattern RefTy r a = TC (RefType (Just r) a)

pattern RawRefTy :: Type n -> Type n
pattern RawRefTy a = TC (RefType Nothing a)

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

pattern PureArrow :: Arrow n
pattern PureArrow = PlainArrow Pure

pattern TabTy :: Binder n l -> Type l -> Type n
pattern TabTy v i = Pi (Abs v (WithArrow TabArrow i))

pattern TabTyAbs :: PiType n -> Type n
pattern TabTyAbs a <- Pi a@(Abs _ (WithArrow TabArrow _))

pattern LamVal :: Binder n l -> Block l -> Atom n
pattern LamVal v b <- Lam (Abs v (WithArrow _ b))

pattern TabVal :: Binder n l -> Block l -> Atom n
pattern TabVal v b = Lam (Abs v (WithArrow TabArrow b))

pattern TabValA :: Binder n l -> Atom l -> Atom n
pattern TabValA v a = Lam (Abs v (WithArrow TabArrow (Block Empty (Atom a))))

isTabTy :: Type n -> Bool
isTabTy (TabTy _ _) = True
isTabTy _ = False

mkConsListTy :: [Type n] -> Type n
mkConsListTy = foldr PairTy UnitTy

mkConsList :: [Atom n] -> Atom n
mkConsList = foldr PairVal UnitVal

fromConsListTy :: MonadError Err m => Type n -> m [Type n]
fromConsListTy ty = case ty of
  UnitTy         -> return []
  PairTy t rest -> (t:) <$> fromConsListTy rest
  _              -> throw CompilerErr $ "Not a pair or unit: " ++ show ty

-- ((...((ans & x{n}) & x{n-1})... & x2) & x1) -> (ans, [x1, ..., x{n}])
fromLeftLeaningConsListTy :: MonadError Err m => Int -> Type n -> m (Type n, [Type n])
fromLeftLeaningConsListTy depth initTy = go depth initTy []
  where
    go 0        ty xs = return (ty, reverse xs)
    go remDepth ty xs = case ty of
      PairTy lt rt -> go (remDepth - 1) lt (rt : xs)
      _ -> throw CompilerErr $ "Not a pair: " ++ show xs

fromConsList :: MonadError Err m => Atom n -> m [Atom n]
fromConsList xs = case xs of
  UnitVal        -> return []
  PairVal x rest -> (x:) <$> fromConsList rest
  _              -> throw CompilerErr $ "Not a pair or unit: " ++ show xs

type BundleDesc = Int  -- length

bundleFold :: a -> (a -> a -> a) -> [a] -> (a, BundleDesc)
bundleFold empty pair els = case els of
  []  -> (empty, 0)
  [e] -> (e, 1)
  h:t -> (pair h tb, td + 1)
    where (tb, td) = bundleFold empty pair t

mkBundleTy :: [Type n] -> (Type n, BundleDesc)
mkBundleTy = bundleFold UnitTy PairTy

mkBundle :: [Atom n] -> (Atom n, BundleDesc)
mkBundle = bundleFold UnitVal PairVal

pattern FunTy :: Binder n l -> EffectRow l -> Type l -> Type n
pattern FunTy b eff bodyTy = Pi (Abs b (WithArrow (PlainArrow eff) bodyTy))

pattern PiTy :: Binder n l -> Arrow l -> Type l -> Type n
pattern PiTy b arr bodyTy = Pi (Abs b (WithArrow arr bodyTy))

pattern BinaryFunTy :: Binder n l' -> Binder l' l -> EffectRow l -> Type l -> Type n
pattern BinaryFunTy b1 b2 eff bodyTy = FunTy b1 Pure (FunTy b2 eff bodyTy)

pattern BinaryFunVal :: Binder n l' -> Binder l' l -> EffectRow l -> Block l -> Type n
pattern BinaryFunVal b1 b2 eff body =
          Lam (Abs b1 (WithArrow PureArrow (Block Empty (Atom (
          Lam (Abs b2 (WithArrow (PlainArrow eff) body)))))))

pattern NoLabeledItems :: LabeledItems a
pattern NoLabeledItems <- ((\(LabeledItems items) -> M.null items) -> True)
  where NoLabeledItems = LabeledItems M.empty

pattern NoExt :: LabeledItems a -> ExtLabeledItems a b
pattern NoExt a = Ext a Nothing

-- An internal label that we can use to treat records and variants as unlabeled
-- internal sum and product types. Note that this is not a valid label in the
-- concrete syntax and will be rejected by the parser (although there wouldn't
-- be any serious problems with overloading a user-written label).
pattern InternalSingletonLabel :: Label
pattern InternalSingletonLabel = "%UNLABELED%"

_getUnlabeled :: LabeledItems a -> Maybe [a]
_getUnlabeled (LabeledItems items) = case length items of
  0 -> Just []
  1 -> NE.toList <$> M.lookup InternalSingletonLabel items
  _ -> Nothing

pattern Unlabeled :: [a] -> LabeledItems a
pattern Unlabeled as <- (_getUnlabeled -> Just as)
  where Unlabeled as = case NE.nonEmpty as of
          Just ne -> LabeledItems (M.singleton InternalSingletonLabel ne)
          Nothing -> NoLabeledItems


-- TODO: figure out how to handle these built-in globals

-- maybeDataDef :: DataDef
-- maybeDataDef = DataDef (GlobalName "Maybe") (Nest (Bind ("a":>TyKind)) Empty)
--   [ DataConDef (GlobalName "Nothing") Empty
--   , DataConDef (GlobalName "Just"   ) (Nest (Ignore (Var ("a":>TyKind))) Empty)]

-- pattern MaybeTy :: Type -> Type
-- pattern MaybeTy a = TypeCon MaybeDataDef [a]

-- pattern MaybeDataDef :: DataDef
-- pattern MaybeDataDef <- ((\def -> def == maybeDataDef) -> True)
--   where MaybeDataDef = maybeDataDef

-- pattern NothingAtom :: Type -> Atom
-- pattern NothingAtom ty = DataCon MaybeDataDef [ty] 0 []

-- pattern JustAtom :: Type -> Atom -> Atom
-- pattern JustAtom ty x = DataCon MaybeDataDef [ty] 1 [x]

pattern NestOne :: b n l -> Nest b n l
pattern NestOne x = Nest x Empty

-- pattern ClassDictDef :: RawName -> LabeledItems (Type n) -> LabeledItems (Type n) -> DataDef n
-- pattern ClassDictDef name superclasses methods =
--   DataDef name
--   [DataConDef conName
--      (Nest (BinderAnn (RecordTy (NoExt superclasses)))
--      (Nest (BinderAnn (RecordTy (NoExt methods))) Empty))]

-- pattern ClassDictCon :: DataDef n
--                      -> [Type n] -> LabeledItems (Atom n) -> LabeledItems (Atom n)
--                      -> Atom n
-- pattern ClassDictCon def params superclasses methods =
--   -- DataCon def params 0 [Record superclasses, Record methods]


-- pattern ClassDictCon :: DataDef n -> [Type n]
--                      -> LabeledItems (Atom n) -> LabeledItems (Atom n) -> (Atom n)
-- pattern ClassDictCon def params superclasses methods =
--   DataCon def params 0 [Record superclasses, Record methods]

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
  , ("and" , binOp BAnd), ("or"  , binOp BOr ), ("not" , unOp BNot)
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
  , ("TyKind"  , TCExpr $ TypeKind)
  , ("Float64" , TCExpr $ BaseType $ Scalar Float64Type)
  , ("Float32" , TCExpr $ BaseType $ Scalar Float32Type)
  , ("Int64"   , TCExpr $ BaseType $ Scalar Int64Type)
  , ("Int32"   , TCExpr $ BaseType $ Scalar Int32Type)
  , ("Word8"   , TCExpr $ BaseType $ Scalar Word8Type)
  , ("Int32Ptr", TCExpr $ BaseType $ ptrTy $ Scalar Int32Type)
  , ("Word8Ptr", TCExpr $ BaseType $ ptrTy $ Scalar Word8Type)
  , ("PtrPtr"  , TCExpr $ BaseType $ ptrTy $ ptrTy $ Scalar Word8Type)
  , ("IntRange", TCExpr $ IntRange () ())
  , ("Ref"     , TCExpr $ RefType (Just ()) ())
  , ("PairType", TCExpr $ PairType () ())
  , ("UnitType", TCExpr $ UnitType)
  , ("EffKind" , TCExpr $ EffectRowKind)
  , ("LabeledRowKind", TCExpr $ LabeledRowKindTC)
  , ("IndexSlice", TCExpr $ IndexSlice () ())
  , ("pair", ConExpr $ PairCon () ())
  , ("fstRef", OpExpr $ FstRef ())
  , ("sndRef", OpExpr $ SndRef ())
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
  ]
  where
    vbinOp op = OpExpr $ VectorBinOp op () ()
    binOp  op = OpExpr $ ScalarBinOp op () ()
    unOp   op = OpExpr $ ScalarUnOp  op ()
    ptrTy  ty = PtrType (Heap CPU, ty)

-- instance Store a => Store (PrimOp  a)
-- instance Store a => Store (PrimCon a)
-- instance Store a => Store (PrimTC  a)
-- instance Store a => Store (PrimHof a)
-- instance (Store a, Store b) => Store (Abs a b)
-- instance Store a => Store (Nest a)
-- instance Store a => Store (ArrowP a)
-- instance Store a => Store (Limit a)
-- instance Store a => Store (PrimEffect a)
-- instance Store a => Store (BaseMonoidP a)
-- instance Store a => Store (LabeledItems a)
-- instance (Store a, Store b) => Store (ExtLabeledItems a b)
-- instance Store ForAnn
-- instance Store Atom
-- instance Store Expr
-- instance Store Block
-- instance Store Decl
-- instance Store RWS
-- instance Store Effect
-- instance Store EffectRow
-- instance Store Direction
-- instance Store UnOp
-- instance Store BinOp
-- instance Store CmpOp
-- instance Store LetAnn
-- instance Store BinderInfo
-- instance Store DataDef
-- instance Store DataConDef
-- instance Store LitVal
-- instance Store ScalarBaseType
-- instance Store BaseType
-- instance Store AddressSpace
-- instance Store Device
-- instance Store DataConRefBinding

instance HasNames EffectRow where traverseFreeNames = traverseFreeNamesFromSubst
instance Subst EffectRow where
  traverseNamesCore = undefined

instance HasNames Atom where traverseFreeNames = traverseFreeNamesFromSubst
instance Subst    Atom where
  traverseNamesCore = undefined

instance AlphaEq  Atom where
  alphaEq = undefined

instance HasNames Expr where traverseFreeNames = traverseFreeNamesFromSubst
instance AlphaEq  Expr where
  alphaEq = undefined
instance Subst    Expr where
  traverseNamesCore = undefined

instance HasNames Block where traverseFreeNames = traverseFreeNamesFromSubst
instance AlphaEq  Block where
  alphaEq = undefined
instance Subst    Block where
  traverseNamesCore = undefined

instance (Subst e) => HasNames (WithArrow e) where
  traverseFreeNames = traverseFreeNamesFromSubst
instance (Subst e)  => AlphaEq (WithArrow e) where
  alphaEq = undefined
instance (Subst e)    => Subst (WithArrow e) where
  traverseNamesCore = undefined

instance BindsNamesCore Binder where
  traverseNamesCoreBinders _ _ _= undefined
  asBindingsFrag = undefined

instance (BindsNamesCore b) => BindsNamesCore (Nest b) where
  traverseNamesCoreBinders _ _ _= undefined
  asBindingsFrag = undefined

instance (BindsNamesCore b, Subst e) => Subst (Abs b e) where
  traverseNamesCore = undefined

instance Show (e n) => Show (WithArrow e n) where
  show = undefined

instance Show (Block n) where
  show = undefined

instance Show (DataDef n) where
  show = undefined

instance HasNames Module where
  traverseFreeNames = traverseFreeNamesFromSubst

instance Subst Module where
  traverseNamesCore = undefined

instance HasNames BinderInfo where
  traverseFreeNames = traverseFreeNamesFromSubst

instance Subst BinderInfo where
  traverseNamesCore = undefined

instance HasNames TypedBinderInfo where
  traverseFreeNames = traverseFreeNamesFromSubst

instance Subst TypedBinderInfo where
  traverseNamesCore = undefined

instance HasNames SourceNameMap where
  traverseFreeNames = traverseFreeNamesFromSubst

instance Subst SourceNameMap where
  traverseNamesCore = undefined

instance BindsNames Decl where
  traverseFreeNamesBinders = traverseFreeNamesBindersFromBindsNamesCore
  asScopeFrag = undefined

instance BindsNamesCore Decl where
  traverseNamesCoreBinders _ _ _= undefined
  asBindingsFrag = undefined

instance Semigroup (SourceNameMap n) where
  (<>) = undefined

instance Monoid (SourceNameMap n) where
  mempty = undefined

instance (Show n) => Show (UExpr' n) where
  show = undefined

instance Semigroup (LabeledItems a) where
  LabeledItems items <> LabeledItems items' =
    LabeledItems $ M.unionWith (<>) items items'

instance Monoid (LabeledItems a) where
  mempty = NoLabeledItems

instance Show (UDecl n l) where
  show = undefined

-- shorthand for instances
tfn :: HasNames e => Monad m => Scope o -> NameTraversal m i o -> e i -> m (e o)
tfn = traverseFreeNames

-- shorthand for instances
tfnb :: BindsNames b => Monad m => Scope o -> NameTraversal m i o -> b i i' -> m (Fresh b i i' o)
tfnb = traverseFreeNamesBinders

wtfnb
  :: BindsNames b => Monad m
  =>             Scope o  -> NameTraversal m i  o  -> b i i'
  -> (forall o'. Scope o' -> NameTraversal m i' o' -> b o o' -> m a)
  -> m a
wtfnb = withTraverseFreeNamesBinders

instance HasNames UExpr' where
  traverseFreeNames s t expr = case expr of
    UVar v -> UVar <$> tfn s t v
    ULam p arr e -> wtfnb s t p \s' t' p' -> ULam p' arr <$> tfn s' t' e
    UPi  p arr ty -> wtfnb s t p \s' t' p' ->
      UPi p' <$> mapM (tfn s' t') arr <*> tfn s' t' ty
    UApp arr f x -> UApp arr <$> tfn s t f <*> tfn s t x
    UDecl d e -> wtfnb s t d \s' t' d' -> UDecl d' <$> tfn s' t' e
    UFor d p e -> wtfnb s t p \s' t' p' -> UFor d p' <$> tfn s' t' e
    UCase scrut alts -> UCase <$> tfn s t scrut <*> mapM (tfn s t) alts
    UHole -> return UHole
    UTypeAnn e ann-> UTypeAnn <$> tfn s t e <*> tfn s t ann
    UTabCon  xs -> UTabCon <$> mapM (tfn s t) xs
    UIndexRange l h -> UIndexRange <$> mapM (tfn s t) l <*> mapM (tfn s t) h
    UPrimExpr e -> UPrimExpr <$> mapM (tfn s t) e
    URecord _ -> undefined
    UVariant _ _ _ -> undefined
    UVariantLift _ _ -> undefined
    URecordTy  _  -> undefined
    UVariantTy _  -> undefined
    UIntLit   x -> return $ UIntLit   x
    UFloatLit x -> return $ UFloatLit x

instance BindsNames UDecl where
  traverseFreeNamesBinders s t decl = case decl of
    ULet ann pat expr -> do
      expr' <- traverseFreeNames s t expr
      tfnb s t pat >>= \case
        Fresh ext pat' renamer ->
          return $ Fresh ext (ULet ann pat' expr') renamer
    UDataDefDecl dataDef tcBinder dcBinders -> do
      dataDef' <- tfn s t dataDef
      tfnb s t (   NestPair tcBinder  dcBinders) >>= \case
        Fresh ext (NestPair tcBinder' dcBinders') renamer ->
          return $ Fresh ext (UDataDefDecl dataDef' tcBinder' dcBinders') renamer
    UInterface params scTys methodTys classBinder methodBinders -> do
      Abs  params' (PairH (H scTys') (H methodTys')) <- tfn s t $
       Abs params  (PairH (H scTys ) (H methodTys ))
      tfnb s t (   NestPair classBinder  methodBinders ) >>= \case
        Fresh ext (NestPair classBinder' methodBinders') renamer ->
          return $ Fresh ext (UInterface params' scTys' methodTys' classBinder' methodBinders') renamer
    UInstance args dictTy methods b -> do
      Abs  args' (PairH dictTy' (H methods')) <- tfn s t $
       Abs args  (PairH dictTy  (H methods ))
      tfnb s t b >>= \case
        Fresh ext b' renamer ->
          return $ Fresh ext (UInstance args' dictTy' methods' b') renamer

  asScopeFrag decl = case decl of
    ULet _ pat _ -> asScopeFrag pat
    UDataDefDecl _ tcBinder dcBinders -> asScopeFrag $ NestPair tcBinder dcBinders
    UInterface _ _ _ classBinder methodBinders -> asScopeFrag $ NestPair classBinder  methodBinders
    UInstance _ _ _ b -> asScopeFrag b

instance HasNames UAlt where
  traverseFreeNames s t alt = undefined

instance HasNames UDataDef where
  traverseFreeNames s t def = undefined

instance HasNames UMethodDef where
  traverseFreeNames s t def = undefined

instance BindsNames UPat' where
  traverseFreeNamesBinders s t pat = case pat of
    UPatUnit -> return $ Fresh id UPatUnit id
    UPatBinder b -> fmapFresh UPatBinder <$> tfnb s t b
    UPatPair p1 p2 -> do
      pair <- tfnb s t $ NestPair p1 p2
      return $ fmapFresh (\(NestPair p1' p2') -> UPatPair p1' p2') pair
    UPatCon c args -> do
      c' <- tfn s t c
      tfnb s t args >>= \case
        Fresh ext args' renamer -> return $ Fresh ext (UPatCon c' args') renamer
    -- UPatRecord :: ExtLabeledItems () () ->  Nest UPat n l   -> UPat' n l-- {a=x, b=y, ...rest}
    -- UPatVariant     :: LabeledItems () -> Label -> UPat n l -> UPat' n l  -- {|a|b| a=x |}
    -- UPatVariantLift :: LabeledItems () -> UPat n l          -> UPat' n l  -- {|a|b| ...rest |}
    -- UPatTable :: Nest UPat n l -> UPat' n l
  asScopeFrag = undefined

instance Show n => Show (UAlt n) where
  show = undefined

instance Show (UModule n) where
  show = undefined

instance (Show n, Show l) => Show (UPat' n l) where
  show = undefined

instance IsString (UExpr' SourceNS) where
  fromString s = UVar $ SourceName $ fromString s

instance Semigroup (EffectRow n) where
  EffectRow effs t <> EffectRow effs' t' =
    EffectRow (S.union effs effs') newTail
    where
      newTail = case (t, t') of
        (Nothing, effTail) -> effTail
        (effTail, Nothing) -> effTail
        _ | t == t' -> t
          | otherwise -> error "Can't combine effect rows with mismatched tails"

instance Monoid (EffectRow n) where
  mempty = EffectRow mempty Nothing

instance IsBool IsCUDARequired where
  toBool CUDARequired = True
  toBool CUDANotRequired = False

instance Show (ImpFunction n) where
  show = undefined

instance Show (ImpBlock n) where
  show = undefined

instance Semigroup Result where
  (<>) = undefined

instance Monoid    Result where
  mempty = undefined

instance Exception Err

instance BindsNames b => BindsNames (WithSrcH2 b) where
  traverseFreeNamesBinders scope t (WithSrcH2 ctx b) =
    fmapFresh (WithSrcH2 ctx) <$> traverseFreeNamesBinders scope t b

  asScopeFrag = undefined

instance HasNames e => HasNames (WithSrcH e) where
  traverseFreeNames scope t (WithSrcH ctx e) =
    WithSrcH ctx <$> traverseFreeNames scope t e
