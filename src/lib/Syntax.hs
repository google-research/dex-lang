-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}

module Syntax (
  Atom (..), Expr (..), Decl (..), Alt, BlockSummary, Block (..), Module (..),
  Type, Kind, Val, Arrow (..), InlineHint (..), LetAnn (..),
  DataConRefBinding (..), IRVariant (..), UExpr' (..), UExpr, UType,
  UDecl, WithUDecls, UMethodDef (..), UAlt,
  UModule (..), UPat' (..), UPat, UPat, UPat',
  WithSrc (..), PrimExpr (..), PrimTC (..), PrimCon (..),
  PrimOp (..), PrimHof (..), BaseMonoidP (..), BaseMonoid, PrimEffect (..),
  BinOp (..), UnOp (..), CmpOp (..), Direction (..), ForAnn (..), Limit (..),
  PrimName, IndexStructure, EffectRow (..), RWS (..), Effect (..), pattern Pure,
  SourceBlock' (..), ReachedEOF, ModuleName, SourceBlock (..), CmdName (..),
  LogLevel (..), IExpr (..), Size, IType, IFunName, IFunType (..),
  IsCUDARequired (..), CallingConvention (..), ImpFunction (..), ImpBlock,
  ImpDecl (..), ImpInstr (..), Backend (..), CUDAKernel (..), LitVal (..),
  ScalarBaseType (..), BaseType (..), Device (..), AddressSpace (..), PtrType,
  sizeOf, ptrSize, vectorWidth, PassName (..), LitProg, TopResult (..), BenchStats,
  Output (..), OutFormat (..), strToPrimName, primNameToStr, showPrimName,
  builtinNames, pattern WithSrcH, WithSrcH,
  AtomSubst, DeferredAtomSubst, MaySubstAtoms, UMethodDef (..),
  -- ExtLabeledItems (..), prefixExtLabeledItems,
  -- fromLabeledRow, traverseExtLabeledItems,
  pattern (:-->), pattern (:--@), pattern (:==>), pattern PureNonDepFunTy,
  pattern IntLitExpr, pattern FloatLitExpr, pattern IdxRepTy, pattern IdxRepVal,
  pattern IIdxRepVal, pattern IIdxRepTy, pattern TagRepTy, pattern TagRepVal,
  pattern Word8Ty, pattern PairVal, pattern PairTy, pattern UnitVal,
  pattern UnitTy, pattern BaseTy, pattern PtrTy, pattern RefTy, pattern RawRefTy,
  pattern TyKind, pattern EffKind, pattern LabeledRowKind, pattern FixedIntRange,
  pattern Fin,
  -- pattern TabTy, pattern TabVal, pattern LamVal, -- pattern NoExt,
  -- pattern RWSActionTy, RWSActionTy, pattern RWSActionVal, RWSActionVal,
  -- pattern TabGet
  ) where

import qualified Data.ByteString.Char8 as B
import qualified Data.Set as S
import Data.Int
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import Data.Tuple (swap)
import Data.Word
import Foreign.Ptr

import Preamble
import Base

-- === core IR ===

data Atom n =
   Var (AtomName n)
 | Lam Arrow (EffectAbs n) (AtomAbs Block n)
 | Pi  Arrow (EffectAbs n) (AtomAbs Type  n)
 | TyCon   (Name TyConDef   n) [Atom n]
 | DataCon (Name DataConDef n) [Atom n]
 -- | LabeledRow (ExtLabeledItems Type n)
 | Record (LabeledItems (Atom n))
 -- | RecordTy  (ExtLabeledItems Type n)
 -- | Variant   (ExtLabeledItems Type n) Label Int (Atom n)
 -- | VariantTy (ExtLabeledItems Type n)
 | PrimCon (PrimCon (Atom n))
 | PrimTC  (PrimTC  (Atom n))
 | Eff (EffectRow n)
 | ACase (Atom n) [AAlt n] (Type n)
   -- single-constructor only for now
 -- | DataConRef (NonInlinableName DataConDef n) [Atom n] (NestedAbs DataConRefBinding UnitH n)
 | BoxedRef (Atom n) (Block n) (AtomAbs Atom n)
 -- access a nested member of a binder
 -- XXX: Variable name must not be an alias for another name or for
 -- a statically-known atom. This is because the variable name used
 -- here may also appear in the type of the atom. (We maintain this
 -- invariant during substitution and in Builder.hs.)
 | ProjectElt (NE.NonEmpty Int) (AtomName n)
   deriving (Show, Generic, Generic1, HasNames)

data Expr n =
   App Arrow (Atom n) (Atom n)
 | Case (Atom n) [Alt n] (Type n)
 | Atom (Atom n)
 | Op  (PrimOp  (Atom n))
 | Hof (PrimHof (Atom n))
   deriving (Show, Generic, Generic1, HasNames)

data AtomBinderInfo n =
   PiBinder   Arrow (Type n)
 | LamBinder  Arrow (Type n)
 | LetBinder  LetInfo (Type n) (Expr n)
 | MiscBinder (Type n)

type AtomBinder = AnnBinder AtomBinderInfo Type
type AtomName   = Name      AtomBinderInfo
type AtomAbs = Abs AtomBinder

type EffectAbs = Abs (Binder AtomBinderInfo) EffectRow

type LetInfo = (LetAnn, InlineHint)
data Decl i n = Let (AtomBinder i n) LetInfo (Expr n)
     deriving (Show, Generic)

type Alt  = Abs (Nest (Binder Type)) Block
type AAlt = Abs (Nest (Binder Type)) Atom

type BlockSummary = Type  -- TODO: add effects too?
type WithDecls = Abs (Nest Decl)
data Block n = Block (Maybe (BlockSummary n)) (WithDecls Atom n)
     deriving (Show, Generic, Generic1, HasNames)

data Module n = Module IRVariant (WithDecls SourceNameMap n)
     deriving (Show, Generic, Generic1, HasNames)

data DataConRefBinding n = DataConRefBinding (AtomAbs Atom n)
     deriving (Show, Generic, Generic1, HasNames)

data DataConDef n = DataConDef
  { dataConSourceName     :: SourceName
  , dataConTyCon          :: Name TyConDef n
  , dataConConstructorIdx :: Int }
  -- , dataConType           :: NaryAbs AtomBindingInfo (WithLamBindings UnitH) n }
  deriving (Show, Generic, Generic1)

data TyConDef n = TyConDef
  { tyConSourceName :: SourceName
  , tyConTyDataCons :: [Name DataConDef n]
  , tyConParamTys   :: [Type n] }
  deriving (Show, Generic, Generic1)

type Type = Atom
type Kind = Type
type Val = Atom Void

data Arrow = PlainArrow | ImplicitArrow | ClassArrow | TabArrow | LinArrow
     deriving (Show, Eq, Generic)

data InlineHint = NoHint | CanInline | NoInline
     deriving (Show, Eq, Generic)

data LetAnn = PlainLet | InstanceLet | SuperclassLet | NoInlineLet | TopLet
     deriving (Show, Eq, Generic)

data IRVariant = Surface | Typed | Core | Simp | Evaluated
     deriving (Show, Eq, Ord, Generic)

-- === front-end language AST ===

type SourceName = String

data UName n =
   UNameSource  SourceName
 | UNameRenamed (Name UnitH n)
   deriving (Show, Generic, Generic1)

data UBinder n i =
   UBinderSource SourceName
 | UBinderRenamed (Binder UnitH n i)
   deriving (Show, Generic, Generic1)

newtype SourceNameMap n = SourceNameMap (M.Map SourceName (Name UnitH n))
        deriving (Show, Generic, Generic1)

type UExpr = WithSrcH UExpr'
data UExpr' n =
   UVar (UName n)
 | ULam (UAnnArrow n) (UPatAbs UExpr n)
 | UPi  Arrow (UPatAbs UEffectRow n) (UType n) (UPatAbs UType n)
 | UApp Arrow (UExpr n) (UExpr n)
 | UBlock (WithUDecls UExpr n)
 | UFor Direction (Maybe (UType n)) (UPatAbs UExpr n)
 | UCase (UExpr n) [UAlt n]
 | UHole
 | UTypeAnn (UExpr n) (UExpr n)
 | UTabCon [UExpr n]
 | UIndexRange (Limit (UExpr n)) (Limit (UExpr n))
 | UPrimExpr (PrimExpr (UExpr n))
 -- | URecord (ExtLabeledItems UExpr n)         -- {a=x, b=y, ...rest}
 | UVariant     (LabeledItems ()) Label  (UExpr n)  -- {|a|b| a=x |}
 | UVariantLift (LabeledItems ())        (UExpr n)  -- {|a|b| ...rest |}
 -- | URecordTy  (ExtLabeledItems UExpr n)      -- {a:X & b:Y & ...rest}
 -- | UVariantTy (ExtLabeledItems UExpr n)      -- {a:X | b:Y | ...rest}
 | UIntLit  Int
 | UFloatLit Double
   deriving (Show, Generic, Generic1, HasNames)

type UType = UExpr

data UDecl n i =
   ULet LetAnn  (UPat n i) (Maybe (UType n))(UExpr n)
 -- | UData (WithUAnnBinders (ListH (WithUAnnBinders UnitH)) n) (UAbs (NaryAbs e) n)
   -- superclasses, type param binders, methods, continuation
 -- | UInferface [UType n] (WithUAnnBinders (ListH UType) n) (UAbs (NaryAbs e) n)
 -- | UInstance (Nest UAnnArrow UPatAbs (PairH UType (ListH UMethodDef)) n) (UAbs e n)
   deriving (Show, Generic, Generic1, HasNames)

data UAnnArrow n = UAnnArrow (Maybe (UType n)) Arrow
     deriving (Show, Generic, Generic1, HasNames)

data UMethodDef n = UMethodDef (UName n) (UExpr n)
     deriving (Show, Generic, Generic1, HasNames)

type UAlt = UPatAbs UExpr
data UModule n = UModule (WithUDecls SourceNameMap n)
     deriving (Show, Generic, Generic1)

data UPat n i = UPat (WithSrc (UPat' i n))
     deriving (Show, Generic)

data UPat' n i =
   UPatIgnore
 | UPatBinder (UBinder n i)
 -- | UPatCon (UName n) (NestedUPatAbs e n)
 -- | UPatPair (UPatAbs (UPatAbs e) n)
 -- | UPatUnit (e n)
 -- -- | UPatAbsRecord (ExtLabeledItems (UPat n) (UPat n))    -- {a=x, b=y, ...rest}
 -- | UPatVariant     (LabeledItems ()) Label (UPatAbs e n)  -- {|a|b| a=x |}
 -- | UPatVariantLift (LabeledItems ())       (UPatAbs e n)  -- {|a|b| ...rest |}
 -- | UPatTable (NestedUPatAbs e n)
   deriving (Show, Generic, HasNames)


type UPatAbs    = Abs UPat
type WithUDecls = Abs (Nest UDecl)

type WithSrcH = H WithSrc
pattern WithSrcH :: SrcCtx -> e n -> H WithSrc e n
pattern WithSrcH ctx x = H (WithSrc ctx x)

data UEffectRow n = UEffectRow (S.Set (Effect n)) (Maybe (UName n))
     deriving (Show, Generic)

-- instance IsString (Name SourceNS) where
--   fromString s = UnsafeMakeName (fromString s) 0

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
 -- Sliced index set, slice length. Note that this is no longer an index set!
 | IndexSlice e e
 | PairType e e
 | UnitType
 | RefType (Maybe e) e
 | TypeKind
 | DataConKind
 | TypeConKind
 | EffectRowKind
 | LabeledRowKindTC
 | ParIndexRange e e e  -- Full index set, global thread id, thread count
   deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

data PrimCon e =
   Lit LitVal
 | PairCon e e
 | UnitCon
 | ClassDictHole SrcCtx e   -- Only used during type inference
 -- type, tag, payload (only used during Imp lowering)
 | SumAsProd e e [[e]]
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
 -- accumulator monoids, index set, thread body
 | PTileReduce [BaseMonoidP e] e e
   deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

type BaseMonoid n = BaseMonoidP (Atom n)
data BaseMonoidP e = BaseMonoid { baseEmpty :: e, baseCombine :: e}
  deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

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

data Direction = Fwd | Rev                        deriving (Show, Eq, Generic)
data ForAnn = RegularFor Direction | ParallelFor  deriving (Show, Eq, Generic)

data Limit e = InclusiveLim e | ExclusiveLim e | Unlimited
  deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

type PrimName = PrimExpr ()
type IndexStructure n = Nest (Binder Type) n Void

-- === effects ===

data EffectRow n = EffectRow (S.Set (Effect n)) (Maybe (AtomName n))
     deriving (Show, Eq, Generic)

data RWS = Reader | Writer | State  deriving (Show, Eq, Ord, Generic)
data Effect n = RWSEffect RWS (AtomName n) | ExceptionEffect | IOEffect
                deriving (Show, Eq, Ord, Generic, Generic1,
                          HasNames, MaySubst Atom)

pattern Pure :: EffectRow n
pattern Pure <- ((\(EffectRow effs t) -> (S.null effs, t)) -> (True, Nothing))
 where  Pure = mempty

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

-- === top-level constructs ===

data SourceBlock = SourceBlock
  { sbLine     :: Int
  , sbOffset   :: Int
  , sbLogLevel :: LogLevel
  , sbText     :: String
  , sbContents :: SourceBlock' }  deriving (Show)

type ReachedEOF = Bool
type ModuleName = String
data SourceBlock' = RunModule (UModule Void)
                  | Command CmdName (SourceName, (UModule Void))
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

data IExpr n =
   ILit LitVal
 | IVar (IName n)
   deriving (Show, Generic, Generic1, HasNames)

data IType n = IType BaseType
     deriving (Show, Generic, Generic1, HasNames)

type Size = IExpr
type IName = Name IType

type IFunName n = Name IFunType n
data IFunType n = IFunType CallingConvention [IType n] [IType n] -- args, results
     deriving (Show, Generic)

data IsCUDARequired = CUDARequired | CUDANotRequired
     deriving (Show, Generic)

instance IsBool IsCUDARequired where
  toBool CUDARequired = True
  toBool CUDANotRequired = False

data CallingConvention = CEntryFun
                       | EntryFun IsCUDARequired
                       | FFIFun
                       | FFIMultiResultFun
                       | CUDAKernelLaunch
                       | MCThreadLaunch
                         deriving (Show, Generic)

data ImpFunction n = ImpFunction [IType n] (NaryAbs IType ImpBlock n) deriving (Show, Generic)
type ImpBlock = Name UnitH -- Nest Decl NaryAbs IType IExpr  -- TODO (maybe give them single return val)

data ImpDecl  n = ImpLet [IType n] (ImpInstr n)  deriving (Show, Generic)
data ImpInstr n =
   IFor Direction (Size n) (Abs (Binder IType) ImpBlock n)
 | IWhile (ImpBlock n)
 | ICond (IExpr n) (ImpBlock n) (ImpBlock n)
 | IQueryParallelism (IFunName n) (IExpr n) -- returns the number of available concurrent threads
 | ISyncWorkgroup
 | ILaunch (IFunName n) (Size n) [IExpr n]
 | ICall   (IFunName n) [IExpr n]
 | Store (IExpr n) (IExpr n)           -- dest, val
 | Alloc AddressSpace (IType n) (Size n)
 | MemCopy (IExpr n) (IExpr n) (IExpr n)   -- dest, source, numel
 | Free (IExpr n)
 | IThrowError  -- TODO: parameterize by a run-time string
 | ICastOp (IType n) (IExpr n)
 | IPrimOp (PrimOp (IExpr n))
   deriving (Show, Generic)

data Backend = LLVM | LLVMCUDA | LLVMMC | Interpreter
     deriving (Show, Generic)

newtype CUDAKernel = CUDAKernel B.ByteString deriving (Show, Generic)

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

data Device = CPU | GPU                 deriving (Show, Eq, Ord, Generic)
data AddressSpace = Stack | Heap Device deriving (Show, Eq, Ord, Generic)
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

-- === extensible labeled items ===

-- -- Extensible version of LabeledItems, which allows an optional object in tail
-- -- position. The items of the tail object will always be interpreted as a
-- -- "suffix" in the sense that for any field label, the object represented by
-- -- an ExtLabeledItems contains first the values in the (LabeledItems a) for that
-- -- field, followed by the values in the (Maybe b) for that field if they exist.
-- data ExtLabeledItems e v n = Ext (LabeledItems (e n)) (Maybe (v n))
--   deriving (Eq, Show, Generic, Generic1, HasNames)

-- -- Adds more items to the front of an ExtLabeledItems.
-- prefixExtLabeledItems :: LabeledItems (e n) -> ExtLabeledItems e n -> ExtLabeledItems e n
-- prefixExtLabeledItems items (Ext items' rest) = Ext (items <> items') rest

-- traverseExtLabeledItems :: Applicative m
--                         => ExtLabeledItems e n
--                         -> (Name n -> m (ExtLabeledItems e' n'))
--                         -> (e n -> m (e' n'))
--                         -> m (ExtLabeledItems e' n')
-- traverseExtLabeledItems (Ext items Nothing) _ f =
--   Ext <$> traverse f items <*> pure Nothing
-- traverseExtLabeledItems (Ext items (Just v)) fName f =
--   prefixExtLabeledItems <$> traverse f items <*> fName v

-- fromLabeledRow :: Atom n -> ExtLabeledItems Type n
-- -- fromLabeledRow (LabeledRow row) = row
-- fromLabeledRow  _ = error "Not a labeled row"

-- -- pattern NoExt :: LabeledItems (e n) -> ExtLabeledItems e n
-- -- pattern NoExt a = Ext a Nothing

-- === passes ===

data PassName = Parse | TypePass | SynthPass | SimpPass | ImpPass | JitPass
              | LLVMOpt | AsmPass | JAXPass | JAXSimpPass | LLVMEval
              | ResultPass | JaxprAndHLO | OptimPass
                deriving (Ord, Eq, Bounded, Enum, Generic)

instance Show PassName where
  show p = case p of
    Parse    -> "parse" ; TypePass -> "typed"   ; SynthPass -> "synth"
    SimpPass -> "simp"  ; ImpPass  -> "imp"     ; JitPass   -> "llvm"
    LLVMOpt  -> "llvmopt" ; AsmPass   -> "asm"
    JAXPass  -> "jax"   ; JAXSimpPass -> "jsimp"; ResultPass -> "result"
    LLVMEval -> "llvmeval" ; JaxprAndHLO -> "jaxprhlo"; OptimPass -> "optimized"

-- === outputs ===

type LitProg = [(SourceBlock, TopResult)]
data TopResult = TopResult [Output] (Except ())  deriving (Show, Generic)

type BenchStats = (Int, Double) -- number of runs, total benchmarking time
data Output = TextOut String
            | HtmlOut String
            | PassInfo PassName String
            | EvalTime  Double (Maybe BenchStats)
            | TotalTime Double
            | BenchResult String Double Double (Maybe BenchStats) -- name, compile time, eval time
            | MiscLog String
            | ExportedFun String (Atom ())
              deriving (Show, Generic)

data OutFormat = Printed | RenderHtml  deriving (Show, Generic)

-- === Synonyms ===

infixr 1 :-->
infixr 1 :--@
infixr 2 :==>

pattern (:-->) :: Type n -> Type n -> Type n
pattern (:-->) a b = PureNonDepFunTy PlainArrow a b

pattern (:--@) :: Type n -> Type n -> Type n
pattern (:--@) a b = PureNonDepFunTy LinArrow a b

pattern (:==>) :: Type n -> Type n -> Type n
pattern (:==>) a b = PureNonDepFunTy TabArrow a b

pattern PureEffectAbs :: EffectAbs n
pattern PureEffectAbs = Abs Ignore Pure

pattern PureNonDepFunTy :: Arrow -> Type n -> Type n -> Type n
pattern PureNonDepFunTy arrow a b = Pi arrow PureEffectAbs (Abs (Ignore:>a) b)

pattern IntLitExpr :: Int -> UExpr' n
pattern IntLitExpr x = UIntLit x

pattern FloatLitExpr :: Double -> UExpr' n
pattern FloatLitExpr x = UFloatLit x

-- Type used to represent indices at run-time
pattern IdxRepTy :: Type n
pattern IdxRepTy = PrimTC (BaseType (Scalar Int32Type))

pattern IdxRepVal :: Int32 -> Atom n
pattern IdxRepVal x = PrimCon (Lit (Int32Lit x))

pattern IIdxRepVal :: Int32 -> IExpr n
pattern IIdxRepVal x = ILit (Int32Lit x)

pattern IIdxRepTy :: IType n
pattern IIdxRepTy = IType (Scalar Int32Type)

-- Type used to represent sum type tags at run-time
pattern TagRepTy :: Type n
pattern TagRepTy = PrimTC (BaseType (Scalar Word8Type))

pattern TagRepVal :: Word8 -> Atom n
pattern TagRepVal x = PrimCon (Lit (Word8Lit x))

pattern Word8Ty :: Type n
pattern Word8Ty = PrimTC (BaseType (Scalar Word8Type))

pattern PairVal :: Atom n -> Atom n -> Atom n
pattern PairVal x y = PrimCon (PairCon x y)

pattern PairTy :: Type n -> Type n -> Type n
pattern PairTy x y = PrimTC (PairType x y)

pattern UnitVal :: Atom n
pattern UnitVal = PrimCon UnitCon

pattern UnitTy :: Type n
pattern UnitTy = PrimTC UnitType

pattern BaseTy :: BaseType -> Type n
pattern BaseTy b = PrimTC (BaseType b)

pattern PtrTy :: PtrType -> Type n
pattern PtrTy ty = BaseTy (PtrType ty)

pattern RefTy :: Atom n -> Type n -> Type n
pattern RefTy r a = PrimTC (RefType (Just r) a)

pattern RawRefTy :: Type n -> Type n
pattern RawRefTy a = PrimTC (RefType Nothing a)

pattern TyKind :: Kind n
pattern TyKind = PrimTC TypeKind

pattern EffKind :: Kind n
pattern EffKind = PrimTC EffectRowKind

pattern LabeledRowKind :: Kind n
pattern LabeledRowKind = PrimTC LabeledRowKindTC

pattern FixedIntRange :: Int32 -> Int32 -> Type n
pattern FixedIntRange low high = PrimTC (IntRange (IdxRepVal low) (IdxRepVal high))

pattern Fin :: Atom n -> Type n
pattern Fin n = PrimTC (IntRange (IdxRepVal 0) n)

-- pattern TabTy :: Type n -> Abs Type n -> Type n
-- pattern TabTy idxTy abs = Pi TabArrow (ConstAbs Pure) idxTy abs

-- pattern TabVal :: Type n -> Abs Block n -> Atom n
-- pattern TabVal ty abs <- (Lam TabArrow _ ty abs)
--  where  TabVal ty abs = (Lam TabArrow (ConstAbs Pure) ty abs)

-- pattern LamVal :: Type n -> AtomAbs Block n -> Atom n
-- pattern LamVal ty abs <- (Lam _ _ ty abs)

-- type    RWSActionTy n = (AtomAbs EffectRow n, Type n, Type n)
-- pattern RWSActionTy :: RWSActionTy n -> Type n
-- pattern RWSActionTy ty <- (checkRWSActionTy -> Just ty)

-- checkRWSActionTy :: Type n -> Maybe (RWSActionTy n)
-- checkRWSActionTy = undefined

-- type    RWSActionVal n = (Abs EffectRow n, Type n, Abs (Abs Block) n)
-- pattern RWSActionVal :: RWSActionVal n  -> Atom n
-- pattern RWSActionVal val  <- (checkRWSActionVal -> Just val)

-- checkRWSActionVal :: Type n -> Maybe (RWSActionVal n)
-- checkRWSActionVal = undefined

-- pattern TabGet :: Atom n -> Atom n -> Expr n
-- pattern TabGet tab i = App TabArrow tab i

-- isTabTy (TabTy _ _) = True
-- isTabTy _ = False

-- -- === built-in names ===

strToPrimName :: String -> Maybe PrimName
strToPrimName s = M.lookup s builtinNames

primNameToStr :: PrimName -> String
primNameToStr = undefined
-- primNameToStr prim = case lookup prim $ map swap $ M.toList builtinNames of
--   Just s  -> s
--   Nothing -> show prim

showPrimName :: PrimExpr e -> String
showPrimName = undefined
-- showPrimName prim = primNameToStr $ fmapH (const UnitH) prim

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

-- === instances ===

type AtomSubst         = Subst         Atom
type MaySubstAtoms     = MaySubst      Atom
type DeferredAtomSubst = DeferredSubst Atom

appSub :: MaySubstAtoms e => (Scope n, AtomSubst i n) -> e i -> e n
appSub = undefined
-- appSub = applySubst'

-- instance FromName Atom where
--   fromName v = Var v

instance MaySubst Atom Atom where
  applySubst' = undefined
  -- applySubst env atom = case atom of
  --   Var v -> lookupSubst v (snd env)
  --   Lam arr eff ty abs -> Lam arr (appSub env eff) (appSub env ty) (appSub env abs)
  --   Pi  arr eff ty abs -> Pi  arr (appSub env eff) (appSub env ty) (appSub env abs)
  --   -- Con con args -> Con (appSub env con) (map (appSub env) args)
  --   PrimTC  tc  -> PrimTC  $ fmap (appSub env) tc
  --   PrimCon con -> PrimCon $ fmap (appSub env) con
  --   Eff eff -> Eff $ appSub env eff
    -- DataCon def params con args ->
    --   DataCon def (appSub env params) con (appSub env args)
    -- TypeCon def params -> TypeCon def (appSub env params)
    -- LabeledRow row -> LabeledRow $ appSub env row
    -- Record la -> Record $ appSub env la
    -- Variant row label i val -> Variant (appSub env row) label i (appSub env val)
    -- RecordTy row -> RecordTy $ appSub env row
    -- VariantTy row -> VariantTy $ appSub env row
    -- ACase v alts rty -> ACase (appSub env v) (appSub env alts) (appSub env rty)
    -- DataConRef def params args -> DataConRef def (appSub env params) args'
    --   where Abs args' () = appSub env $ Abs args ()
    -- BoxedRef b ptr size body -> BoxedRef b' (appSub env ptr) (appSub env size) body'
    --     where Abs b' body' = appSub env $ Abs b body
    -- ProjectElt idxs v -> getProjection (toList idxs) $ substVar env v

instance MaySubst Atom EffectRow where
  applySubst' = undefined
  -- applySubst' env (EffectRow row t) = extendEffRow row' t'
  --  where
  --    row' = S.map (appSub env) row
  --    t' = substEffTail (snd env) t

-- substEffTail :: AtomSubst i n -> Maybe (Var i) -> EffectRow n
-- substEffTail _ Nothing = EffectRow mempty Nothing
-- substEffTail env (Just v) = case lookupSubst v env of
--   Var v' -> EffectRow mempty (Just v')
--   Eff r  -> r
--   _ -> error "Not a valid effect substitution"

extendEffRow :: S.Set (Effect n) -> EffectRow n -> EffectRow n
extendEffRow effs (EffectRow effs' t) = EffectRow (effs <> effs') t

deriving instance MaySubst Atom Expr
deriving instance MaySubst Atom Block

instance HasNames EffectRow where
  freeNames' = undefined

-- instance AlphaEq EffectRow where
--   alphaEq' = undefined

-- === pretty-print instances ===

instance Pretty Arrow
instance Pretty Direction
instance Pretty ForAnn
instance Pretty RWS
instance Pretty UnOp
instance Pretty BinOp
instance Pretty CmpOp
instance Pretty LetAnn
instance Pretty LitVal
instance Pretty ScalarBaseType
instance Pretty BaseType
instance Pretty AddressSpace
instance Pretty Device
instance Pretty InlineHint
instance Pretty Output

instance Pretty (Atom n)
instance Pretty (Expr n)
instance Pretty (Block n)
instance Pretty (EffectRow n)
instance Pretty (Effect n)
instance Pretty (DataConRefBinding n)

instance (Show e, Pretty e) => Pretty (PrimOp  e)
instance (Show e, Pretty e) => Pretty (PrimCon e)
instance (Show e, Pretty e) => Pretty (PrimTC  e)
instance (Show e, Pretty e) => Pretty (PrimHof e)
instance (Show e, Pretty e) => Pretty (Limit   e)
instance (Show e, Pretty e) => Pretty (PrimEffect  e)
instance (Show e, Pretty e) => Pretty (BaseMonoidP e)

instance PrettyH Atom
instance PrettyH Expr
instance PrettyH Block
instance PrettyH EffectRow
instance PrettyH Effect
instance PrettyH DataConRefBinding
