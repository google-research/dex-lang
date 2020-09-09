{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE Rank2Types #-}

module Syntax (
    Type, Kind, BaseType (..), ScalarBaseType (..),
    Effect, EffectName (..), EffectRow (..),
    ClassName (..), TyQual (..), SrcPos, Var, Binder, Block (..), Decl (..),
    Expr (..), Atom (..), ArrowP (..), Arrow, PrimTC (..), Abs (..),
    PrimExpr (..), PrimCon (..), LitVal (..),
    PrimEffect (..), PrimOp (..), EffectSummary (..),
    PrimHof (..), LamExpr, PiType, WithSrc (..), srcPos, LetAnn (..),
    BinOp (..), UnOp (..), CmpOp (..), SourceBlock (..),
    ReachedEOF, SourceBlock' (..), SubstEnv, Scope, CmdName (..), HasIVars (..),
    Val, TopEnv, Op, Con, Hof, TC, Module (..), ImpFunction (..), IStmt (..),
    IProg, IProgVal, ImpProgram, ImpStatement, ImpInstr (..), IExpr (..), IVal,
    IPrimOp, IVar, IBinder, IType (..), ArrayType, SetVal (..), MonMap (..), LitProg,
    UAlt (..), Alt, binderBinding, Label, LabeledItems (..), labeledSingleton,
    reflectLabels, withLabels, ExtLabeledItems (..), prefixExtLabeledItems,
    MDImpFunction (..), MDImpProgram, MDImpInstr (..), MDImpStatement,
    ImpKernel (..), CUDAKernel (..), IScope,
    ScalarTableType, ScalarTableBinder, BinderInfo (..),Bindings,
    SrcCtx, Result (..), Output (..), OutFormat (..), DataFormat (..),
    Err (..), ErrType (..), Except, throw, throwIf, modifyErr, addContext,
    addSrcContext, catchIOExcept, liftEitherIO, (-->), (--@), (==>),
    boundUVars, PassName (..), boundVars, bindingsAsVars,
    freeVars, freeUVars, Subst, HasVars, BindsVars,
    strToName, nameToStr, showPrimName,
    monMapSingle, monMapLookup, Direction (..), ArrayRef, Array, Limit (..),
    UExpr, UExpr' (..), UType, UPatAnn, UAnnBinder, UVar,
    UPat, UPat' (..), UModule (..), UDecl (..), UArrow, arrowEff,
    DataDef (..), DataConDef (..), UConDef (..), Nest (..), toNest,
    subst, deShadow, scopelessSubst, absArgType, applyAbs, makeAbs,
    applyNaryAbs, applyDataDefParams, freshSkolemVar,
    mkConsList, mkConsListTy, fromConsList, fromConsListTy, extendEffRow,
    scalarTableBaseType, varType, binderType, isTabTy, LogLevel (..), IRVariant (..),
    applyIntBinOp, applyIntCmpOp, applyFloatBinOp, applyFloatUnOp,
    getIntLit, getFloatLit, pattern CharLit,
    pattern IdxRepTy, pattern IdxRepVal, pattern TagRepTy, pattern TagRepVal,
    pattern IntLitExpr, pattern FloatLitExpr,
    pattern UnitTy, pattern PairTy, pattern FunTy,
    pattern FixedIntRange, pattern RefTy,
    pattern BaseTy, pattern UnitVal,
    pattern PairVal, pattern PureArrow, pattern ArrayVal,
    pattern TyKind, pattern LamVal,
    pattern TabTy, pattern TabTyAbs, pattern TabVal, pattern TabValA,
    pattern Pure, pattern BinaryFunTy, pattern BinaryFunVal, pattern CharTy,
    pattern Unlabeled, pattern NoExt, pattern LabeledRowKind,
    pattern NoLabeledItems, pattern InternalSingletonLabel,
    pattern EffKind, pattern JArrayTy, pattern ArrayTy, pattern IDo)
  where

import qualified Data.Map.Strict as M
import Control.Exception hiding (throw)
import Control.Monad.Fail
import Control.Monad.Identity
import Control.Monad.Writer hiding (Alt)
import Control.Monad.Except hiding (Except)
import qualified Data.Vector.Storable  as V
import qualified Data.ByteString.Char8 as B
import Data.List (sort)
import qualified Data.List.NonEmpty as NE
import Data.Store (Store)
import Data.Tuple (swap)
import Data.Foldable (toList)
import Data.Int
import GHC.Generics

import Env
import Array
import Util (enumerate, (...))

-- === core IR ===

data Atom = Var Var
          | Lam LamExpr
          | Pi  PiType
          | DataCon DataDef [Atom] Int [Atom]
          | TypeCon DataDef [Atom]
          | LabeledRow (ExtLabeledItems Type Name)
          | Record (LabeledItems Atom)
          | RecordTy (ExtLabeledItems Type Name)
          | Variant (ExtLabeledItems Type Name) Label Int Atom
          | VariantTy (ExtLabeledItems Type Name)
          | Con Con
          | TC  TC
          | Eff EffectRow
            deriving (Show, Generic)

data Expr = App Atom Atom
          | Case Atom [Alt] Type
          | Atom Atom
          | Op  Op
          | Hof Hof
            deriving (Show, Generic)

data Decl = Let LetAnn Binder Expr
          | Unpack (Nest Binder) Expr  deriving (Show, Generic)

data Block = Block (Nest Decl) Expr    deriving (Show, Generic)
type Alt = Abs (Nest Binder) Block

type Var    = VarP Type
type Binder = BinderP Type

data DataDef = DataDef Name (Nest Binder) [DataConDef]  deriving (Show, Generic)
data DataConDef = DataConDef Name (Nest Binder)    deriving (Show, Generic)

data Abs b body = Abs b body               deriving (Show, Generic)
data Nest a = Nest a (Nest a) | Empty
              deriving (Show, Generic, Functor, Foldable, Traversable)

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
            | SuperclassLet
              deriving (Show, Eq, Generic)

type Val  = Atom
type Type = Atom
type Kind = Type

type TC  = PrimTC  Atom
type Con = PrimCon Atom
type Op  = PrimOp  Atom
type Hof = PrimHof Atom

data Module = Module IRVariant (Nest Decl) Bindings  deriving Show
type TopEnv = Scope

data IRVariant = Surface | Typed | Core | Simp | Evaluated
                 deriving (Show, Eq, Ord, Generic)

-- A subset of Type generated by the following grammar:
-- data ScalarTableType = TabType (Pi ScalarTableType) | Scalar BaseType
type ScalarTableType = Type
type ScalarTableBinder  = BinderP ScalarTableType

scalarTableBaseType :: ScalarTableType -> BaseType
scalarTableBaseType t = case t of
  TabTy _ a -> scalarTableBaseType a
  BaseTy b  -> b
  _         -> error $ "Not a scalar table: " ++ show t


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
  flip M.mapWithKey items $ \k xs -> fmap (\(i,_) -> (k,i)) (enumerate xs)

withLabels :: LabeledItems a -> LabeledItems (Label, Int, a)
withLabels (LabeledItems items) = LabeledItems $
  flip M.mapWithKey items $ \k xs -> fmap (\(i,a) -> (k,i,a)) (enumerate xs)

instance Semigroup (LabeledItems a) where
  LabeledItems items <> LabeledItems items' =
    LabeledItems $ M.unionWith (<>) items items'

instance Monoid (LabeledItems a) where
  mempty = NoLabeledItems

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

type UExpr = WithSrc UExpr'
data UExpr' = UVar UVar
            | ULam UPatAnn UArrow UExpr
            | UPi  UAnnBinder Arrow UType
            | UApp UArrow UExpr UExpr
            | UDecl UDecl UExpr
            | UFor Direction UPatAnn UExpr
            | UCase UExpr [UAlt]
            | UHole
            | UTabCon [UExpr] (Maybe UExpr)
            | UIndexRange (Limit UExpr) (Limit UExpr)
            | UPrimExpr (PrimExpr Name)
            | URecord (ExtLabeledItems UExpr UExpr)     -- {a=x, b=y, ...rest}
            | UVariant (LabeledItems ()) Label UExpr    -- {|a|b| a=x |}
            | UVariantLift (LabeledItems ()) UExpr      -- {|a|b| ...rest |}
            | URecordTy (ExtLabeledItems UExpr UExpr)   -- {a:X & b:Y & ...rest}
            | UVariantTy (ExtLabeledItems UExpr UExpr)  -- {a:X | b:Y | ...rest}
            | UIntLit  Int
            | UCharLit Char
            | UFloatLit Double
              deriving (Show, Generic)

data UConDef = UConDef Name (Nest UAnnBinder)  deriving (Show, Generic)
data UDecl = ULet LetAnn UPatAnn UExpr
           | UData UConDef [UConDef]
             deriving (Show, Generic)

type UType  = UExpr
type UArrow = ArrowP ()
type UVar    = VarP ()
type UBinder = BinderP ()

type UPatAnn   = (UPat, Maybe UType)
type UAnnBinder = BinderP UType

data UAlt = UAlt UPat UExpr deriving (Show, Generic)

data UModule = UModule (Nest UDecl)  deriving (Show)
type SrcPos = (Int, Int)

type UPat  = WithSrc UPat'
data UPat' = UPatBinder UBinder
           | UPatCon Name (Nest UPat)
           | UPatPair UPat UPat
           | UPatUnit
           | UPatRecord (ExtLabeledItems UPat UPat)     -- {a=x, b=y, ...rest}
           | UPatVariant (LabeledItems ()) Label UPat   -- {|a|b| a=x |}
           | UPatVariantLift (LabeledItems ()) UPat     -- {|a|b| ...rest |}
             deriving (Show)

data WithSrc a = WithSrc SrcCtx a
                 deriving (Show, Functor, Foldable, Traversable)

srcPos :: WithSrc a -> SrcCtx
srcPos (WithSrc pos _) = pos

-- === primitive constructors and operators ===

data PrimExpr e =
        TCExpr  (PrimTC  e)
      | ConExpr (PrimCon e)
      | OpExpr  (PrimOp  e)
      | HofExpr (PrimHof e)
        deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

data PrimTC e =
        BaseType  BaseType
      | CharType
      | ArrayType e         -- A pointer to memory storing a ScalarTableType value
      | IntRange e e
      | IndexRange e (Limit e) (Limit e)
      | IndexSlice e e      -- Sliced index set, slice length. Note that this is no longer an index set!
      | PairType e e
      | UnitType
      | RefType e e
      | TypeKind
      | EffectRowKind
      | LabeledRowKindTC
        -- NOTE: This is just a hack so that we can construct an Atom from an Imp or Jax expression.
        --       In the future it might make sense to parametrize Atoms by the types
        --       of values they can hold.
        -- XXX: This one can temporarily also appear in the fully evaluated terms in TopLevel.
      | JArrayType [Int] ScalarBaseType
        deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

data PrimCon e =
        Lit LitVal
      | CharCon e         -- Wraps an Int8 value
      | ArrayLit e Array  -- Used to store results of module evaluation
      | AnyValue e        -- Produces an arbitrary value of a given type
      | PairCon e e
      | UnitCon
      | Coerce e e        -- Type, then value. See Type.hs for valid coercions.
      | ClassDictHole SrcCtx e   -- Only used during type inference
      | SumAsProd e e [[e]] -- type, tag, payload (only used during Imp lowering)
        deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

data PrimOp e =
        Fst e
      | Snd e
      | TabCon e [e]                 -- table type elements
      | ScalarBinOp BinOp e e
      | ScalarUnOp UnOp e
      | Select e e e                 -- predicate, val-if-true, val-if-false
      | PrimEffect e (PrimEffect e)
      | IndexRef e e
      | FstRef e
      | SndRef e
      | FFICall String BaseType [e]
      | Inject e
      | ArrayOffset e e e            -- Second argument is the index for type checking,
                                     -- Third argument is the linear offset for evaluation
      | ArrayLoad e
      | SliceOffset e e              -- Index slice first, inner index second
      | SliceCurry  e e              -- Index slice first, curried index second
      -- SIMD operations
      | VectorBinOp BinOp e e
      | VectorPack [e]               -- List should have exactly vectorWidth elements
      | VectorIndex e e              -- Vector first, index second
      -- Idx (survives simplification, because we allow it to be backend-dependent)
      | IntAsIndex e e   -- index set, ordinal index
      | IndexAsInt e
      | IdxSetSize e
      | ThrowError e
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
        deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

data PrimHof e =
        For Direction e
      | Tile Int e e          -- dimension number, tiled body, scalar body
      | While e e
      | RunReader e e
      | RunWriter e
      | RunState  e e
      | Linearize e
      | Transpose e
        deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

data PrimEffect e = MAsk | MTell e | MGet | MPut e
    deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

data BinOp = IAdd | ISub | IMul | IDiv | ICmp CmpOp
           | FAdd | FSub | FMul | FDiv | FCmp CmpOp | FPow
           | BAnd | BOr | IRem
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

data Limit a = InclusiveLim a
             | ExclusiveLim a
             | Unlimited
               deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

data ClassName = DataClass | VSpace | IdxSet | Eq | Ord deriving (Show, Eq, Generic)

data TyQual = TyQual Var ClassName  deriving (Show, Eq, Generic)

type PrimName = PrimExpr ()

strToName :: String -> Maybe PrimName
strToName s = M.lookup s builtinNames

nameToStr :: PrimName -> String
nameToStr prim = case lookup prim $ map swap $ M.toList builtinNames of
  Just s  -> s
  Nothing -> show prim

showPrimName :: PrimExpr e -> String
showPrimName prim = nameToStr $ fmap (const ()) prim

-- === effects ===

type Effect = (EffectName, Name)
data EffectRow = EffectRow [Effect] (Maybe Name)
                 deriving (Show, Generic)
data EffectName = Reader | Writer | State  deriving (Show, Eq, Ord, Generic)

data EffectSummary = NoEffects | SomeEffects  deriving (Show, Eq, Ord, Generic)

pattern Pure :: EffectRow
pattern Pure = EffectRow [] Nothing

instance Eq EffectRow where
  EffectRow effs t == EffectRow effs' t' =
    sort effs == sort effs' && t == t'

instance Semigroup EffectSummary where
  NoEffects <> NoEffects = NoEffects
  _ <> _ = SomeEffects

instance Monoid EffectSummary where
  mempty = NoEffects

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
data SourceBlock' = RunModule UModule
                  | Command CmdName (Name, UModule)
                  | GetNameType Name
                  | IncludeSourceFile String
                  | LoadData UPatAnn DataFormat String
                  | ProseBlock String
                  | CommentLine
                  | EmptyLines
                  | UnParseable ReachedEOF String
                    deriving (Show, Generic)

data CmdName = GetType | EvalExpr OutFormat | Dump DataFormat String
                deriving  (Show, Generic)

data LogLevel = LogNothing | PrintEvalTime | PrintBench String
              | LogPasses [PassName] | LogAll
                deriving  (Show, Generic)

-- === imperative IR ===

type IProg instr = Nest (IStmt instr)
type IProgVal instr = (IProg instr, Maybe IExpr)
data IStmt instr = IInstr (IBinder, instr)
                 | IFor Direction IBinder Size (IProg instr)
                 | IWhile (IProgVal instr) (IProg instr)  -- cond block, body block
                 | ICond IExpr (IProg instr) (IProg instr)
                 deriving (Show, Functor, Foldable, Traversable)

data IExpr = ILit LitVal
           | IVar IVar
             deriving (Show)

type IPrimOp = PrimOp IExpr
type IVal = IExpr  -- only ILit and IRef constructors
type IBinder = BinderP IType
type IVar = VarP IType
data IType = IValType BaseType
           | IRefType ScalarTableType -- This represents ArrayType (ScalarTableType)
           | IVoidType
             deriving (Show, Eq)

type Size  = IExpr

-- Destinations first, arguments second
data ImpFunction = ImpFunction [ScalarTableBinder] [ScalarTableBinder] ImpProgram
                   deriving (Show)
type ImpProgram   = IProg ImpInstr
type ImpStatement = IStmt ImpInstr

data ImpInstr = Load  IExpr
              | Store IExpr IExpr           -- Destination first
              | Alloc ScalarTableType Size  -- Second argument is the size of the table
              | Free IVar
                                            -- Second argument is the linear offset for code generation
                                            -- Third argument is the result type for type checking
              | IOffset IExpr IExpr ScalarTableType
              | IThrowError  -- TODO: parameterize by a run-time string
              | ICastOp IType IExpr
              | IPrimOp IPrimOp
                deriving (Show)

-- === multi-device imperative IR ===

-- Destinations first, arguments second
data MDImpFunction k = MDImpFunction [ScalarTableBinder] [ScalarTableBinder] (MDImpProgram k)
                       deriving (Show, Functor, Foldable, Traversable)
type MDImpProgram k   = IProg (MDImpInstr k)
type MDImpStatement k = IStmt (MDImpInstr k)

data MDImpInstr k = MDLaunch Size [IVar] k
                  | MDAlloc ScalarTableType Size
                  | MDFree IVar
                  | MDLoadScalar  IVar
                  | MDStoreScalar IVar IExpr
                  | MDHostInstr ImpInstr
                    deriving (Show, Functor, Foldable, Traversable)

-- Parameters, linear thread index, kernel body
data ImpKernel = ImpKernel [IBinder] IBinder ImpProgram
                 deriving (Show)
newtype CUDAKernel = CUDAKernel B.ByteString deriving (Show)

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
              | Flops | LLVMOpt | AsmPass | JAXPass | JAXSimpPass | LLVMEval
              | ResultPass | JaxprAndHLO | OptimPass
                deriving (Ord, Eq, Bounded, Enum)

instance Show PassName where
  show p = case p of
    Parse    -> "parse" ; TypePass -> "typed"   ; SynthPass -> "synth"
    SimpPass -> "simp"  ; ImpPass  -> "imp"     ; JitPass   -> "llvm"
    Flops    -> "flops" ; LLVMOpt  -> "llvmopt" ; AsmPass   -> "asm"
    JAXPass  -> "jax"   ; JAXSimpPass -> "jsimp"; ResultPass -> "result"
    LLVMEval -> "llvmeval" ; JaxprAndHLO -> "jaxprhlo"; OptimPass -> "optimized"

-- === outputs ===

type LitProg = [(SourceBlock, Result)]
type SrcCtx = Maybe SrcPos
data Result = Result [Output] (Except ())  deriving (Show, Eq)

data Output = TextOut String
            | HeatmapOut Bool Int Int (V.Vector Double)  -- Bool indicates if color
            | ScatterOut (V.Vector Double) (V.Vector Double)
            | PassInfo PassName String
            | EvalTime  Double
            | TotalTime Double
            | BenchResult String Double Double  -- name, compile time, eval time
            | MiscLog String
              deriving (Show, Eq, Generic)

data OutFormat = Printed | Heatmap Bool | ColorHeatmap | Scatter
                 deriving (Show, Eq, Generic)
data DataFormat = DexObject | DexBinaryObject  deriving (Show, Eq, Generic)

data Err = Err ErrType SrcCtx String  deriving (Show, Eq)
instance Exception Err

data ErrType = NoErr
             | ParseErr
             | TypeErr
             | KindErr
             | LinErr
             | UnboundVarErr
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
modifyErr m f = catchError m $ \e -> throwError (f e)

addContext :: MonadError Err m => String -> m a -> m a
addContext s m = modifyErr m $ \(Err e p s') -> Err e p (s' ++ "\n" ++ s)

addSrcContext :: MonadError Err m => SrcCtx -> m a -> m a
addSrcContext ctx m = modifyErr m updateErr
  where
    updateErr :: Err -> Err
    updateErr (Err e ctx' s) = case ctx' of Nothing -> Err e ctx  s
                                            Just _  -> Err e ctx' s

catchIOExcept :: (MonadIO m , MonadError Err m) => IO a -> m a
catchIOExcept m = (liftIO >=> liftEither) $ (liftM Right m) `catches`
  [ Handler $ \(e::Err)           -> return $ Left e
  , Handler $ \(e::IOError)       -> return $ Left $ Err DataIOErr   Nothing $ show e
  , Handler $ \(e::SomeException) -> return $ Left $ Err CompilerErr Nothing $ show e
  ]

liftEitherIO :: (Exception e, MonadIO m) => Either e a -> m a
liftEitherIO (Left err) = liftIO $ throwIO err
liftEitherIO (Right x ) = return x

instance MonadFail (Either Err) where
  fail s = Left $ Err CompilerErr Nothing s

-- === UExpr free variables ===

type UVars = Env ()

uVarsAsGlobal :: UVars -> UVars
uVarsAsGlobal vs = foldMap (\v -> asGlobal v @> ()) $ envNames vs

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
    UVar v -> v @>()
    ULam (pat,ty) _ body -> freeUVars ty <> freeUVars (Abs pat body)
    UPi b arr ty -> freeUVars $ Abs b (arr, ty)
    -- TODO: maybe distinguish table arrow application
    -- (otherwise `x.i` and `x i` are the same)
    UApp _ f x -> freeUVars f <> freeUVars x
    UDecl decl body -> freeUVars $ Abs decl body
    UFor _ (pat,ty) body -> freeUVars ty <> freeUVars (Abs pat body)
    UHole -> mempty
    UTabCon xs n -> foldMap freeUVars xs <> foldMap freeUVars n
    UIndexRange low high -> foldMap freeUVars low <> foldMap freeUVars high
    UPrimExpr _ -> mempty
    UCase e alts -> freeUVars e <> foldMap freeUVars alts
    URecord ulr -> freeUVars ulr
    UVariant types _ val -> freeUVars types <> freeUVars val
    URecordTy ulr -> freeUVars ulr
    UVariantTy ulr -> freeUVars ulr
    UVariantLift skip val -> freeUVars skip <> freeUVars val
    UIntLit  _ -> mempty
    UCharLit _ -> mempty
    UFloatLit _ -> mempty

instance HasUVars UAlt where
  freeUVars (UAlt p body) = freeUVars $ Abs p body

instance HasUVars () where
  freeUVars = mempty

instance HasUVars UPat' where
  freeUVars pat = case pat of
    UPatBinder _   -> mempty
    UPatCon con ps -> con @> () <> foldMap freeUVars ps
    UPatPair p1 p2 -> freeUVars p1 <> freeUVars p2
    UPatUnit       -> mempty
    UPatRecord items -> freeUVars items
    UPatVariant _ _ p -> freeUVars p
    UPatVariantLift _ p -> freeUVars p

instance BindsUVars UPat' where
  boundUVars pat = case pat of
    UPatBinder v   -> v @> ()
    UPatCon _ ps   -> foldMap boundUVars ps
    UPatPair p1 p2 -> boundUVars p1 <> boundUVars p2
    UPatUnit       -> mempty
    UPatRecord items -> boundUVars items
    UPatVariant _ _ p -> boundUVars p
    UPatVariantLift _ p -> boundUVars p

instance HasUVars UDecl where
  freeUVars (ULet _ p expr) = freeUVars p <> freeUVars expr
  freeUVars (UData (UConDef _ bs) dataCons) = freeUVars $ Abs bs dataCons

instance BindsUVars UDecl where
  boundUVars decl = case decl of
   ULet _ (p,_) _ -> boundUVars p
   UData tyCon dataCons -> boundUVars tyCon <> foldMap boundUVars dataCons

instance HasUVars UModule where
  freeUVars (UModule decls) = freeUVars decls

instance BindsUVars UModule where
  boundUVars (UModule decls) = boundUVars decls

instance HasUVars SourceBlock where
  freeUVars block = uVarsAsGlobal $
    case sbContents block of
      RunModule (   m) -> freeUVars m
      Command _ (_, m) -> freeUVars m
      GetNameType v -> v @> ()
      _ -> mempty

instance BindsUVars SourceBlock where
  boundUVars block = uVarsAsGlobal $
    case sbContents block of
      RunModule (   m) -> boundUVars m
      _ -> mempty

instance HasUVars EffectRow where
  freeUVars (EffectRow effs tailVar) =
    foldMap (nameAsEnv . snd) effs <> foldMap nameAsEnv tailVar

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

instance HasUVars a => HasUVars (BinderP a) where
  freeUVars b = freeUVars $ binderAnn b

instance HasUVars a => BindsUVars (BinderP a) where
  boundUVars b = b @> ()

instance HasUVars UConDef where
  freeUVars (UConDef _ bs) = freeUVars bs

instance BindsUVars UConDef where
  boundUVars (UConDef con _) = con @>()

instance BindsUVars a => BindsUVars (WithSrc a) where
  boundUVars (WithSrc _ x) = boundUVars x

instance BindsUVars a => BindsUVars (LabeledItems a) where
  boundUVars items = foldMap boundUVars items

instance BindsUVars a => BindsUVars (ExtLabeledItems a a) where
  boundUVars (Ext items rest) = boundUVars items <> boundUVars rest

instance BindsUVars a => BindsUVars (Maybe a) where
  boundUVars Nothing = mempty
  boundUVars (Just x) = boundUVars x

nameAsEnv :: Name -> UVars
nameAsEnv v = v@>()

-- === Expr free variables and substitutions ===

data BinderInfo =
        LamBound (ArrowP ())
        -- TODO: make the expression optional, for when it's effectful?
        -- (or we could put the effect tag on the let annotation)
      | PatBound
      | LetBound LetAnn Expr
      | DataBoundDataCon DataDef Int
      | DataBoundTypeCon DataDef
      | PiBound
      | UnknownBinder
        deriving (Show, Generic)

type SubstEnv = Env Atom
type Bindings = Env (Type, BinderInfo)
type Scope = Bindings  -- when we only care about the names, not the payloads
type ScopedSubstEnv = (SubstEnv, Bindings)

scopelessSubst :: Subst a => SubstEnv -> a -> a
scopelessSubst env x = subst (env, scope) x
  where scope = foldMap freeVars env <> (freeVars x `envDiff` env)

bindingsAsVars :: Bindings -> [Var]
bindingsAsVars env = [v:>ty | (v, (ty, _)) <- envPairs env]

binderBinding :: Binder -> Bindings
binderBinding b = b @> (binderType b, UnknownBinder)

class HasVars a where
  freeVars :: a -> Scope

class HasVars a => Subst a where
  subst :: ScopedSubstEnv -> a -> a

class HasVars a => BindsVars a where
  boundVars :: a -> Scope
  renamingSubst :: ScopedSubstEnv -> a -> (a, ScopedSubstEnv)

instance (BindsVars b, HasVars body) => HasVars (Abs b body) where
  freeVars (Abs b body) = freeVars b <> (freeVars body `envDiff` boundVars b)

instance (BindsVars b, Subst body) => Subst (Abs b body) where
  subst env (Abs b body) = Abs b' body'
    where (b', env') = renamingSubst env b
          body' = subst (env <> env') body

instance BindsVars a => HasVars (Nest a) where
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
  boundVars b = b @> (binderType b, UnknownBinder)
  renamingSubst env (Ignore ty) = (Ignore (subst env ty), mempty)
  renamingSubst env@(_, scope) b@(Bind (v:>ty)) = (b', env')
    where v' = genFresh v scope
          b' = Bind (v':>ty')
          ty' = subst env ty
          env' = (b@>Var (v':>ty'), b'@>(ty', UnknownBinder))

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
  _ == _ = False

instance Eq DataDef where
  DataDef name _ _ == DataDef name' _ _ = name == name'

instance (Show a, Subst a, Eq a) => Eq (Abs Binder a) where
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

applyAbs :: Subst a => Abs Binder a -> Atom -> a
applyAbs (Abs b body) x = scopelessSubst (b@>x) body

applyNaryAbs :: Subst a => Abs (Nest Binder) a -> [Atom] -> a
applyNaryAbs (Abs Empty body) [] = body
applyNaryAbs (Abs (Nest b bs) body) (x:xs) = applyNaryAbs ab xs
  where ab = applyAbs (Abs b (Abs bs body)) x
applyNaryAbs _ _ = error "wrong number of arguments"

applyDataDefParams :: DataDef -> [Type] -> [DataConDef]
applyDataDefParams (DataDef _ paramBs cons) params =
  applyNaryAbs (Abs paramBs cons) params

makeAbs :: HasVars a => Binder -> a -> Abs Binder a
makeAbs b body | b `isin` freeVars body = Abs b body
               | otherwise = Abs (Ignore (binderType b)) body

absArgType :: Abs Binder a -> Type
absArgType (Abs b _) = binderType b

toNest :: [a] -> Nest a
toNest (x:xs) = Nest x $ toNest xs
toNest [] = Empty

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
substVar env@(sub, scope) v = case envLookup sub v of
  Nothing -> Var $ fmap (subst env) v
  Just x' -> deShadow x' scope

deShadow :: Subst a => a -> Scope -> a
deShadow x scope = subst (mempty, scope) x

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
    Unpack bs expr -> freeVars expr <> freeVars bs

instance Subst Decl where
  subst env decl = case decl of
    Let ann b expr -> Let ann (fmap (subst env) b) $ subst env expr
    Unpack bs expr -> Unpack (subst env bs) $ subst env expr

instance BindsVars Decl where
  boundVars decl = case decl of
    Let ann b expr -> b @> (binderType b, LetBound ann expr)
    Unpack bs _ -> boundVars bs

  renamingSubst env decl = case decl of
    Let ann b expr -> (Let ann b' expr', env')
      where expr' = subst env expr
            (b', env') = renamingSubst env b
    Unpack bs expr -> (Unpack bs' expr', env')
      where expr' = subst env expr
            (bs', env') = renamingSubst env bs

instance HasVars Block where
  freeVars (Block decls result) = freeVars $ Abs decls result
instance Subst Block where
  subst env (Block decls result) = Block decls' result'
    where Abs decls' result' = subst env $ Abs decls result

instance HasVars Atom where
  freeVars atom = case atom of
    Var v@(_:>t) -> (v @> (t, UnknownBinder)) <> freeVars t
    Lam lam -> freeVars lam
    Pi  ty  -> freeVars ty
    Con con -> foldMap freeVars con
    TC  tc  -> foldMap freeVars tc
    Eff eff -> freeVars eff
    -- TODO: think about these cases. We don't want to needlessly traverse the
    --       data definition but we might need to know the free Vars.
    DataCon _ params _ args -> freeVars params <> freeVars args
    TypeCon _ params        -> freeVars params
    LabeledRow la -> freeVars la
    Record la -> freeVars la
    Variant la _ _ val -> freeVars la <> freeVars val
    RecordTy row -> freeVars row
    VariantTy row -> freeVars row

instance Subst Atom where
  subst env atom = case atom of
    Var v   -> substVar env v
    Lam lam -> Lam $ subst env lam
    Pi  ty  -> Pi  $ subst env ty
    TC  tc  -> TC  $ fmap (subst env) tc
    Con con -> Con $ fmap (subst env) con
    Eff eff -> Eff $ subst env eff
    DataCon def params con args -> DataCon def (subst env params) con (subst env args)
    TypeCon def params          -> TypeCon def (subst env params)
    LabeledRow row -> LabeledRow $ subst env row
    Record la -> Record $ subst env la
    Variant row label i val -> Variant (subst env row) label i (subst env val)
    RecordTy row -> RecordTy $ subst env row
    VariantTy row -> VariantTy $ subst env row

instance HasVars Module where
  freeVars (Module _ decls bindings) = freeVars $ Abs decls bindings
instance Subst Module where
  subst env (Module variant decls bindings) = Module variant decls' bindings'
    where Abs decls' bindings' = subst env $ Abs decls bindings

instance HasVars EffectRow where
  freeVars (EffectRow row t) =
       foldMap (\(_,v) -> v@>(TyKind , UnknownBinder)) row
    <> foldMap (\v     -> v@>(EffKind, UnknownBinder)) t
instance Subst EffectRow where
  subst (env, _) (EffectRow row t) = extendEffRow
    (fmap (\(effName, v) -> (effName, substName env v)) row)
    (substEffTail env t)

instance HasVars BinderInfo where
  freeVars binfo = case binfo of
   LetBound _ expr -> freeVars expr
   _ -> mempty

instance Subst BinderInfo where
  subst env binfo = case binfo of
   LetBound a expr -> LetBound a $ subst env expr
   _ -> binfo

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
    freeVars items <> (v @> (LabeledRowKind, UnknownBinder))

instance Subst (ExtLabeledItems Type Name) where
  subst env@(env', _) (Ext items rest) =
    prefixExtLabeledItems (subst env items) (substExtLabeledItemsTail env' rest)

substEffTail :: SubstEnv -> Maybe Name -> EffectRow
substEffTail _ Nothing = EffectRow [] Nothing
substEffTail env (Just v) = case envLookup env (v:>()) of
  Nothing -> EffectRow [] (Just v)
  Just (Var (v':>_)) -> EffectRow [] (Just v')
  Just (Eff r) -> r
  _ -> error "Not a valid effect substitution"

substName :: SubstEnv -> Name -> Name
substName env v = case envLookup env (v:>()) of
  Nothing -> v
  Just (Var (v':>_)) -> v'
  _ -> error "Should only substitute with a name"

extendEffRow :: [Effect] -> EffectRow -> EffectRow
extendEffRow effs (EffectRow effs' t) = EffectRow (effs <> effs') t

substExtLabeledItemsTail :: SubstEnv -> Maybe Name -> ExtLabeledItems Type Name
substExtLabeledItemsTail _ Nothing = NoExt NoLabeledItems
substExtLabeledItemsTail env (Just v) = case envLookup env (v:>()) of
  Nothing -> Ext NoLabeledItems $ Just v
  Just (Var (v':>_)) -> Ext NoLabeledItems $ Just v'
  Just (LabeledRow row) -> row
  _ -> error "Not a valid labeled row substitution"

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

class BindsIVars a where
  boundIVars :: a -> IScope

-- XXX: Only for ScalarTableType!
instance HasIVars Type where
  freeIVars t = fmap (\(BaseTy bt, _) -> IValType bt) $ freeVars t

instance HasIVars IExpr where
  freeIVars e = case e of
    ILit _        -> mempty
    IVar v@(_:>t) -> v @> t <> freeIVars t

instance HasIVars IType where
  freeIVars t = case t of
    IValType _  -> mempty
    IRefType rt -> freeIVars rt
    IVoidType   -> mempty

instance HasIVars instr => HasIVars (IProg instr) where
  freeIVars Empty = mempty
  freeIVars (Nest stmt cont) = stmtFree <> (freeIVars cont `envDiff` boundIVars stmt)
    where
      stmtFree = case stmt of
        IInstr (_, instr) -> freeIVars instr
        IFor _ b n p      -> freeIVars n <> (freeIVars p `envDiff` (b @> ()))
        IWhile c p        -> freeIVars c <> freeIVars p
        ICond  c t f      -> freeIVars c <> freeIVars t <> freeIVars f

instance BindsIVars (IStmt instr) where
  boundIVars stmt = case stmt of
    IInstr (b, _) -> binderAsEnv b
    IFor _ _ _ _  -> mempty
    IWhile _ _    -> mempty
    ICond _ _ _   -> mempty

instance BindsIVars (IProg instr) where
  boundIVars prog = foldMap boundIVars prog

instance HasIVars ImpInstr where
  freeIVars i = case i of
    Load  e       -> freeIVars e
    Store d e     -> freeIVars d <> freeIVars e
    Alloc t s     -> freeIVars t <> freeIVars s
    Free  v       -> varAsEnv v
    IOffset a o t -> freeIVars a <> freeIVars o <> freeIVars t
    ICastOp t x   -> freeIVars t <> freeIVars x
    IPrimOp op    -> foldMap freeIVars op
    IThrowError   -> mempty

instance HasIVars instr => HasIVars (IProgVal instr) where
  freeIVars (prog, val) = freeIVars prog <> (maybe mempty freeIVars val `envDiff` boundIVars prog)

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
  (Con (Lit (Int8Lit xv)) , Con (Lit (Int8Lit  yv))) -> f (Con . Lit . Int8Lit ) xv yv
  _ -> error "Expected integer atoms"

applyIntBinOp :: (forall a. (Num a, Integral a) => a -> a -> a) -> Atom -> Atom -> Atom
applyIntBinOp f x y = applyIntBinOp' (\w -> w ... f) x y

applyIntCmpOp :: (forall a. (Eq a, Ord a) => a -> a -> Bool) -> Atom -> Atom -> Atom
applyIntCmpOp f x y = applyIntBinOp' (\_ -> (Con . Lit . Int8Lit . fromIntegral . fromEnum) ... f) x y

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
  Int8Lit  i -> fromIntegral i
  _ -> error $ "Expected an integer literal"

getFloatLit :: LitVal -> Double
getFloatLit l = case l of
  Float64Lit f -> f
  Float32Lit f -> realToFrac f
  _ -> error $ "Expected a floating-point literal"

pattern CharLit :: Int8 -> Atom
pattern CharLit x = Con (CharCon (Con (Lit (Int8Lit x))))

-- Type used to represent indices at run-time
pattern IdxRepTy :: Type
pattern IdxRepTy = TC (BaseType (Scalar Int32Type))

pattern IdxRepVal :: Int32 -> Atom
pattern IdxRepVal x = Con (Lit (Int32Lit x))

-- Type used to represent sum type tags at run-time
pattern TagRepTy :: Type
pattern TagRepTy = TC (BaseType (Scalar Int64Type))

pattern TagRepVal :: Int64 -> Atom
pattern TagRepVal x = Con (Lit (Int64Lit x))

pattern ArrayVal :: Type -> Array -> Atom
pattern ArrayVal t arr = Con (ArrayLit t arr)

pattern PairVal :: Atom -> Atom -> Atom
pattern PairVal x y = Con (PairCon x y)

pattern PairTy :: Type -> Type -> Type
pattern PairTy x y = TC (PairType x y)

pattern UnitVal :: Atom
pattern UnitVal = Con UnitCon

pattern UnitTy :: Type
pattern UnitTy = TC UnitType

pattern JArrayTy :: [Int] -> ScalarBaseType -> Type
pattern JArrayTy shape b = TC (JArrayType shape b)

pattern BaseTy :: BaseType -> Type
pattern BaseTy b = TC (BaseType b)

pattern RefTy :: Atom -> Type -> Type
pattern RefTy r a = TC (RefType r a)

pattern CharTy :: Type
pattern CharTy = TC CharType

pattern TyKind :: Kind
pattern TyKind = TC TypeKind

pattern EffKind :: Kind
pattern EffKind = TC EffectRowKind

pattern LabeledRowKind :: Kind
pattern LabeledRowKind = TC LabeledRowKindTC

pattern FixedIntRange :: Int32 -> Int32 -> Type
pattern FixedIntRange low high = TC (IntRange (IdxRepVal low) (IdxRepVal high))

pattern PureArrow :: Arrow
pattern PureArrow = PlainArrow Pure

pattern ArrayTy :: Type -> Type
pattern ArrayTy t = TC (ArrayType t)

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

isTabTy :: Type -> Bool
isTabTy (TabTy _ _) = True
isTabTy _ = False

mkConsListTy :: [Type] -> Type
mkConsListTy tys = foldr PairTy UnitTy tys

mkConsList :: [Atom] -> Atom
mkConsList xs = foldr PairVal UnitVal xs

fromConsListTy :: MonadError Err m => Type -> m [Type]
fromConsListTy ty = case ty of
  UnitTy         -> return []
  PairTy t rest -> (t:) <$> fromConsListTy rest
  _              -> throw CompilerErr $ "Not a pair or unit: " ++ show ty

fromConsList :: MonadError Err m => Atom -> m [Atom]
fromConsList xs = case xs of
  UnitVal        -> return []
  PairVal x rest -> (x:) <$> fromConsList rest
  _              -> throw CompilerErr $ "Not a pair or unit: " ++ show xs

pattern FunTy :: Binder -> EffectRow -> Type -> Type
pattern FunTy b eff bodyTy = Pi (Abs b (PlainArrow eff, bodyTy))

pattern BinaryFunTy :: Binder -> Binder -> EffectRow -> Type -> Type
pattern BinaryFunTy b1 b2 eff bodyTy = FunTy b1 Pure (FunTy b2 eff bodyTy)

pattern BinaryFunVal :: Binder -> Binder -> EffectRow -> Block -> Type
pattern BinaryFunVal b1 b2 eff body =
          Lam (Abs b1 (PureArrow, Block Empty (Atom (
          Lam (Abs b2 (PlainArrow eff, body))))))

pattern IDo :: BinderP IType
pattern IDo = Ignore IVoidType

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
_getUnlabeled (LabeledItems items) = case (length items) of
  0 -> Just []
  1 -> NE.toList <$> M.lookup InternalSingletonLabel items
  _ -> Nothing

pattern Unlabeled :: [a] -> LabeledItems a
pattern Unlabeled as <- (_getUnlabeled -> Just as)
  where Unlabeled as = case NE.nonEmpty as of
          Just ne -> LabeledItems (M.singleton InternalSingletonLabel ne)
          Nothing -> NoLabeledItems

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
  , ("asint"       , OpExpr $ IndexAsInt ())
  , ("idxSetSize"  , OpExpr $ IdxSetSize ())
  , ("asidx"       , OpExpr $ IntAsIndex () ())
  , ("throwError" , OpExpr $ ThrowError ())
  , ("ask"        , OpExpr $ PrimEffect () $ MAsk)
  , ("tell"       , OpExpr $ PrimEffect () $ MTell ())
  , ("get"        , OpExpr $ PrimEffect () $ MGet)
  , ("put"        , OpExpr $ PrimEffect () $ MPut  ())
  , ("indexRef"   , OpExpr $ IndexRef () ())
  , ("inject"     , OpExpr $ Inject ())
  , ("select"     , OpExpr $ Select () () ())
  , ("while"           , HofExpr $ While () ())
  , ("linearize"       , HofExpr $ Linearize ())
  , ("linearTranspose" , HofExpr $ Transpose ())
  , ("runReader"       , HofExpr $ RunReader () ())
  , ("runWriter"       , HofExpr $ RunWriter    ())
  , ("runState"        , HofExpr $ RunState  () ())
  , ("tiled"           , HofExpr $ Tile 0 () ())
  , ("tiledd"          , HofExpr $ Tile 1 () ())
  , ("TyKind"  , TCExpr $ TypeKind)
  , ("Float64" , TCExpr $ BaseType $ Scalar Float64Type)
  , ("Float32" , TCExpr $ BaseType $ Scalar Float32Type)
  , ("Int64"   , TCExpr $ BaseType $ Scalar Int64Type)
  , ("Int32"   , TCExpr $ BaseType $ Scalar Int32Type)
  , ("Int8"    , TCExpr $ BaseType $ Scalar Int8Type)
  , ("IntRange", TCExpr $ IntRange () ())
  , ("Ref"     , TCExpr $ RefType () ())
  , ("PairType", TCExpr $ PairType () ())
  , ("UnitType", TCExpr $ UnitType)
  , ("EffKind" , TCExpr $ EffectRowKind)
  , ("LabeledRowKind", TCExpr $ LabeledRowKindTC)
  , ("IndexSlice", TCExpr $ IndexSlice () ())
  , ("pair", ConExpr $ PairCon () ())
  , ("fst", OpExpr $ Fst ())
  , ("snd", OpExpr $ Snd ())
  , ("fstRef", OpExpr $ FstRef ())
  , ("sndRef", OpExpr $ SndRef ())
  , ("anyVal", ConExpr $ AnyValue ())
  -- TODO: Lift vectors to constructors
  --, ("VectorFloatType",  TCExpr $ BaseType $ Vector FloatType)
  , ("vectorPack", OpExpr $ VectorPack $ replicate vectorWidth ())
  , ("vectorIndex", OpExpr $ VectorIndex () ())
  , ("unsafeAsIndex", ConExpr $ Coerce   () ())
  , ("cast", OpExpr  $ CastOp () ())
  , ("sliceOffset", OpExpr $ SliceOffset () ())
  , ("sliceCurry", OpExpr $ SliceCurry () ())
  ]
  where
    vbinOp op = OpExpr $ VectorBinOp op () ()
    binOp  op = OpExpr $ ScalarBinOp op () ()
    unOp   op = OpExpr $ ScalarUnOp  op ()

instance Store a => Store (PrimOp  a)
instance Store a => Store (PrimCon a)
instance Store a => Store (PrimTC  a)
instance Store a => Store (PrimHof a)
instance (Store a, Store b) => Store (Abs a b)
instance Store a => Store (Nest a)
instance Store a => Store (ArrowP a)
instance Store a => Store (Limit a)
instance Store a => Store (PrimEffect a)
instance Store a => Store (LabeledItems a)
instance (Store a, Store b) => Store (ExtLabeledItems a b)
instance Store Atom
instance Store Expr
instance Store Block
instance Store Decl
instance Store EffectName
instance Store EffectRow
instance Store Direction
instance Store UnOp
instance Store BinOp
instance Store CmpOp
instance Store LetAnn
instance Store BinderInfo
instance Store DataDef
instance Store DataConDef
