{-# LANGUAGE OverloadedStrings #-}

-- | A module that eases the construction of Core Futhark programs.
-- This module is derived from the compiler IR definition itself,
-- although simplified, and supports only the SOACS representation.
--
-- In the long term it may be useful to use the compiler IR
-- representation directly, but right now the Haskell-level 'futhark'
-- package is a monolith with some fairly troublesome dependencies
-- (e.g. lsp) that users likely do not want to depend on, just to
-- obtain the AST definition.
module Futhark.IR
  ( -- * Names
    Name,
    nameToString,
    nameFromString,
    nameToText,
    nameFromText,
    VName (..),

    -- * Attributes
    Attr,
    Attrs,
    oneAttr,

    -- * Primitive
    PrimType (..),
    IntType (..),
    FloatType (..),
    Overflow (..),
    BinOp (..),
    CmpOp (..),
    ConvOp (..),
    UnOp (..),

    -- * Types
    Ext (..),
    ExtSize,
    ShapeBase (..),
    Shape,
    TypeBase (..),
    Type,
    ExtType,
    Uniqueness (..),
    NoUniqueness (..),
    DeclType,
    DeclExtType,
    Rank,

    -- * Patterns
    PatElem (..),
    Pat (..),

    -- * Parameters
    Param (..),
    LParam,
    FParam,

    -- * Expressions
    SubExp (..),
    Slice (..),
    RetAls (..),
    Lambda (..),
    ScremaForm (..),
    Reduce (..),
    Scan (..),
    SOAC (..),
    Exp (..),

    -- * Statements
    StmAux (..),
    Stm (..),
    Stms,

    -- * Bodies
    SubExpRes (..),
    Result,
    subExpRes,
    varRes,
    subExpsRes,
    varsRes,
    Body (..),

    -- * Programs
    FunDef (..),
    Prog (..),
  )
where

import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Foldable (toList)
import Data.Int
import Data.List (intersperse)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Set qualified as S
import Data.String
import Data.Text qualified as T
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text qualified
import Data.Traversable
import Numeric.Half

--- Primitive types and values

data IntType
  = Int8
  | Int16
  | Int32
  | Int64
  deriving (Eq, Ord, Show, Enum, Bounded)

data FloatType
  = Float16
  | Float32
  | Float64
  deriving (Eq, Ord, Show, Enum, Bounded)

data PrimType
  = IntType IntType
  | FloatType FloatType
  | Bool
  | -- | An informationless type - An array of this type takes up no space.
    Unit
  deriving (Eq, Ord, Show)

data IntValue
  = Int8Value !Int8
  | Int16Value !Int16
  | Int32Value !Int32
  | Int64Value !Int64
  deriving (Eq, Ord, Show)

data FloatValue
  = Float16Value !Half
  | Float32Value !Float
  | Float64Value !Double
  deriving (Show)

instance Eq FloatValue where
  Float16Value x == Float16Value y = isNaN x && isNaN y || x == y
  Float32Value x == Float32Value y = isNaN x && isNaN y || x == y
  Float64Value x == Float64Value y = isNaN x && isNaN y || x == y
  _ == _ = False

-- The derived Ord instance does not handle NaNs correctly.
instance Ord FloatValue where
  Float16Value x <= Float16Value y = x <= y
  Float32Value x <= Float32Value y = x <= y
  Float64Value x <= Float64Value y = x <= y
  Float16Value _ <= Float32Value _ = True
  Float16Value _ <= Float64Value _ = True
  Float32Value _ <= Float16Value _ = False
  Float32Value _ <= Float64Value _ = True
  Float64Value _ <= Float16Value _ = False
  Float64Value _ <= Float32Value _ = False

  Float16Value x < Float16Value y = x < y
  Float32Value x < Float32Value y = x < y
  Float64Value x < Float64Value y = x < y
  Float16Value _ < Float32Value _ = True
  Float16Value _ < Float64Value _ = True
  Float32Value _ < Float16Value _ = False
  Float32Value _ < Float64Value _ = True
  Float64Value _ < Float16Value _ = False
  Float64Value _ < Float32Value _ = False

  (>) = flip (<)
  (>=) = flip (<=)

-- | Non-array values.
data PrimValue
  = IntValue !IntValue
  | FloatValue !FloatValue
  | BoolValue !Bool
  | -- | The only value of type 'Unit'.
    UnitValue
  deriving (Eq, Ord, Show)

instance Pretty PrimValue where
  pretty (IntValue v) = pretty v
  pretty (BoolValue True) = "true"
  pretty (BoolValue False) = "false"
  pretty (FloatValue v) = pretty v
  pretty UnitValue = "()"

-- | The size of a value of a given integer type in eight-bit bytes.
intByteSize :: (Num a) => IntType -> a
intByteSize Int8 = 1
intByteSize Int16 = 2
intByteSize Int32 = 4
intByteSize Int64 = 8

-- | The size of a value of a given floating-point type in eight-bit bytes.
floatByteSize :: (Num a) => FloatType -> a
floatByteSize Float16 = 2
floatByteSize Float32 = 4
floatByteSize Float64 = 8

-- | The size of a value of a given primitive type in eight-bit bytes.
--
-- Warning: note that this is 0 for 'Unit', but a 'Unit' takes up a
-- byte in the binary data format.
primByteSize :: (Num a) => PrimType -> a
primByteSize (IntType t) = intByteSize t
primByteSize (FloatType t) = floatByteSize t
primByteSize Bool = 1
primByteSize Unit = 0

-- | The size of a value of a given primitive type in bits.
primBitSize :: PrimType -> Int
primBitSize = (* 8) . primByteSize

--- Primitive operations

-- | What to do in case of arithmetic overflow.  Futhark's semantics
-- are that overflow does wraparound, but for generated code (like
-- address arithmetic), it can be beneficial for overflow to be
-- undefined behaviour, as it allows better optimisation of things
-- such as GPU kernels.
--
-- Note that all values of this type are considered equal for 'Eq' and
-- 'Ord'.
data Overflow = OverflowWrap | OverflowUndef
  deriving (Show)

instance Eq Overflow where
  _ == _ = True

instance Ord Overflow where
  _ `compare` _ = EQ

-- | Whether something is safe or unsafe (mostly function calls, and
-- in the context of whether operations are dynamically checked).
-- When we inline an 'Unsafe' function, we remove all safety checks in
-- its body.  The 'Ord' instance picks 'Unsafe' as being less than
-- 'Safe'.
--
-- For operations like integer division, a safe division will not
-- explode the computer in case of division by zero, but instead
-- return some unspecified value.  This always involves a run-time
-- check, so generally the unsafe variant is what the compiler will
-- insert, but guarded by an explicit assertion elsewhere.  Safe
-- operations are useful when the optimiser wants to move e.g. a
-- division to a location where the divisor may be zero, but where the
-- result will only be used when it is non-zero (so it doesn't matter
-- what result is provided with a zero divisor, as long as the program
-- keeps running).
data Safety = Unsafe | Safe deriving (Eq, Ord, Show)

-- | Binary operators.  These correspond closely to the binary operators in
-- LLVM.  Most are parametrised by their expected input and output
-- types.
data BinOp
  = -- | Integer addition.
    Add IntType Overflow
  | -- | Floating-point addition.
    FAdd FloatType
  | -- | Integer subtraction.
    Sub IntType Overflow
  | -- | Floating-point subtraction.
    FSub FloatType
  | -- | Integer multiplication.
    Mul IntType Overflow
  | -- | Floating-point multiplication.
    FMul FloatType
  | -- | Unsigned integer division.  Rounds towards
    -- negativity infinity.  Note: this is different
    -- from LLVM.
    UDiv IntType Safety
  | -- | Unsigned integer division.  Rounds towards positive
    -- infinity.
    UDivUp IntType Safety
  | -- | Signed integer division.  Rounds towards
    -- negativity infinity.  Note: this is different
    -- from LLVM.
    SDiv IntType Safety
  | -- | Signed integer division.  Rounds towards positive
    -- infinity.
    SDivUp IntType Safety
  | -- | Floating-point division.
    FDiv FloatType
  | -- | Floating-point modulus.
    FMod FloatType
  | -- | Unsigned integer modulus; the countepart to 'UDiv'.
    UMod IntType Safety
  | -- | Signed integer modulus; the countepart to 'SDiv'.
    SMod IntType Safety
  | -- | Signed integer division.  Rounds towards zero.  This
    -- corresponds to the @sdiv@ instruction in LLVM and
    -- integer division in C.
    SQuot IntType Safety
  | -- | Signed integer division.  Rounds towards zero.  This
    -- corresponds to the @srem@ instruction in LLVM and
    -- integer modulo in C.
    SRem IntType Safety
  | -- | Returns the smallest of two signed integers.
    SMin IntType
  | -- | Returns the smallest of two unsigned integers.
    UMin IntType
  | -- | Returns the smallest of two floating-point numbers.
    FMin FloatType
  | -- | Returns the greatest of two signed integers.
    SMax IntType
  | -- | Returns the greatest of two unsigned integers.
    UMax IntType
  | -- | Returns the greatest of two floating-point numbers.
    FMax FloatType
  | -- | Left-shift.
    Shl IntType
  | -- | Logical right-shift, zero-extended.
    LShr IntType
  | -- | Arithmetic right-shift, sign-extended.
    AShr IntType
  | -- | Bitwise and.
    And IntType
  | -- | Bitwise or.
    Or IntType
  | -- | Bitwise exclusive-or.
    Xor IntType
  | -- | Integer exponentiation.
    Pow IntType
  | -- | Floating-point exponentiation.
    FPow FloatType
  | -- | Boolean and - not short-circuiting.
    LogAnd
  | -- | Boolean or - not short-circuiting.
    LogOr
  deriving (Eq, Ord, Show)

-- | Comparison operators are like 'BinOp's, but they always return a
-- boolean value.  The somewhat ugly constructor names are straight
-- out of LLVM.
data CmpOp
  = -- | All types equality.
    CmpEq PrimType
  | -- | Unsigned less than.
    CmpUlt IntType
  | -- | Unsigned less than or equal.
    CmpUle IntType
  | -- | Signed less than.
    CmpSlt IntType
  | -- | Signed less than or equal.
    CmpSle IntType
  | -- Comparison operators for floating-point values.  TODO: extend
    -- this to handle NaNs and such, like the LLVM fcmp instruction.

    -- | Floating-point less than.
    FCmpLt FloatType
  | -- | Floating-point less than or equal.
    FCmpLe FloatType
  | -- Boolean comparison.

    -- | Boolean less than.
    CmpLlt
  | -- | Boolean less than or equal.
    CmpLle
  deriving (Eq, Ord, Show)

-- | Conversion operators try to generalise the @from t0 x to t1@
-- instructions from LLVM.
data ConvOp
  = -- | Zero-extend the former integer type to the latter.
    -- If the new type is smaller, the result is a
    -- truncation.
    ZExt IntType IntType
  | -- | Sign-extend the former integer type to the latter.
    -- If the new type is smaller, the result is a
    -- truncation.
    SExt IntType IntType
  | -- | Convert value of the former floating-point type to
    -- the latter.  If the new type is smaller, the result
    -- is a truncation.
    FPConv FloatType FloatType
  | -- | Convert a floating-point value to the nearest
    -- unsigned integer (rounding towards zero).
    FPToUI FloatType IntType
  | -- | Convert a floating-point value to the nearest
    -- signed integer (rounding towards zero).
    FPToSI FloatType IntType
  | -- | Convert an unsigned integer to a floating-point value.
    UIToFP IntType FloatType
  | -- | Convert a signed integer to a floating-point value.
    SIToFP IntType FloatType
  | -- | Convert an integer to a boolean value.  Zero
    -- becomes false; anything else is true.
    IToB IntType
  | -- | Convert a boolean to an integer.  True is converted
    -- to 1 and False to 0.
    BToI IntType
  | -- | Convert a float to a boolean value.  Zero becomes false;
    -- | anything else is true.
    FToB FloatType
  | -- | Convert a boolean to a float.  True is converted
    -- to 1 and False to 0.
    BToF FloatType
  deriving (Eq, Ord, Show)

-- | Various unary operators.  It is a bit ad-hoc what is a unary
-- operator and what is a built-in function.  Perhaps these should all
-- go away eventually.
data UnOp
  = -- | E.g., @! True == False@.
    Not
  | -- | E.g., @~(~1) = 1@.
    Complement IntType
  | -- | @abs(-2) = 2@.
    Abs IntType
  | -- | @fabs(-2.0) = 2.0@.
    FAbs FloatType
  | -- | Signed sign function: @ssignum(-2)@ = -1.
    SSignum IntType
  | -- | Unsigned sign function: @usignum(2)@ = 1.
    USignum IntType
  | -- | Floating-point sign function.
    FSignum FloatType
  deriving (Eq, Ord, Show)

-- | The input and output types of a conversion operator.
convOpType :: ConvOp -> (PrimType, PrimType)
convOpType (ZExt from to) = (IntType from, IntType to)
convOpType (SExt from to) = (IntType from, IntType to)
convOpType (FPConv from to) = (FloatType from, FloatType to)
convOpType (FPToUI from to) = (FloatType from, IntType to)
convOpType (FPToSI from to) = (FloatType from, IntType to)
convOpType (UIToFP from to) = (IntType from, FloatType to)
convOpType (SIToFP from to) = (IntType from, FloatType to)
convOpType (IToB from) = (IntType from, Bool)
convOpType (BToI to) = (Bool, IntType to)
convOpType (FToB from) = (FloatType from, Bool)
convOpType (BToF to) = (Bool, FloatType to)

-- | The human-readable name for a 'ConvOp'.  This is used to expose
-- the 'ConvOp' in the @intrinsics@ module of a Futhark program.
convOpFun :: ConvOp -> String
convOpFun ZExt {} = "zext"
convOpFun SExt {} = "sext"
convOpFun FPConv {} = "fpconv"
convOpFun FPToUI {} = "fptoui"
convOpFun FPToSI {} = "fptosi"
convOpFun UIToFP {} = "uitofp"
convOpFun SIToFP {} = "sitofp"
convOpFun IToB {} = "itob"
convOpFun BToI {} = "btoi"
convOpFun FToB {} = "ftob"
convOpFun BToF {} = "btof"

--- AST proper

newtype Name = Name T.Text
  deriving (Show, Eq, Ord, IsString, Semigroup)

-- | Convert a name to the corresponding list of characters.
nameToString :: Name -> String
nameToString (Name t) = T.unpack t

-- | Convert a list of characters to the corresponding name.
nameFromString :: String -> Name
nameFromString = Name . T.pack

-- | Convert a name to the corresponding 'T.Text'.
nameToText :: Name -> T.Text
nameToText (Name t) = t

-- | Convert a 'T.Text' to the corresponding name.
nameFromText :: T.Text -> Name
nameFromText = Name

-- | The uniqueness attribute of a type.  This essentially indicates
-- whether or not in-place modifications are acceptable.  With respect
-- to ordering, 'Unique' is greater than 'Nonunique'.
data Uniqueness = Nonunique | Unique
  deriving (Eq, Ord, Show)

-- | A fancier name for @()@ - encodes no uniqueness information.
-- Also has a different prettyprinting instance.
data NoUniqueness = NoUniqueness
  deriving (Eq, Ord, Show)

instance Semigroup Uniqueness where
  (<>) = min

instance Monoid Uniqueness where
  mempty = Unique

-- | A name tagged with some integer.  Only the integer is used in
-- comparisons, no matter the type of @vn@.
data VName = VName !Name !Int
  deriving (Show)

instance IsString VName where
  fromString s =
    let (bef, aft) = break (== '_') s
     in VName (nameFromString bef) (read (tail aft))

instance Eq VName where
  VName _ x == VName _ y = x == y

instance Ord VName where
  VName _ x `compare` VName _ y = x `compare` y

data Commutativity
  = Noncommutative
  | Commutative
  deriving (Eq, Ord, Show)

data SubExp
  = Constant PrimValue
  | Var VName
  deriving (Show, Eq, Ord)

-- | Something that may be existential.
data Ext a
  = Ext Int
  | Free a
  deriving (Eq, Ord, Show)

instance Functor Ext where
  fmap = fmapDefault

instance Foldable Ext where
  foldMap = foldMapDefault

instance Traversable Ext where
  traverse _ (Ext i) = pure $ Ext i
  traverse f (Free v) = Free <$> f v

-- | The size of an array type as merely the number of dimensions,
-- with no further information.
newtype Rank = Rank Int
  deriving (Show, Eq, Ord)

-- | The size of this dimension.
type ExtSize = Ext SubExp

newtype ShapeBase d = Shape {shapeDims :: [d]}
  deriving (Eq, Ord, Show)

type Shape = ShapeBase SubExp

type ExtShape = ShapeBase ExtSize

-- | How to index a single dimension of an array.
data DimIndex
  = -- | Fix index in this dimension.
    DimFix SubExp
  | -- | @DimSlice start_offset num_elems stride@.
    DimSlice SubExp SubExp SubExp
  deriving (Eq, Ord, Show)

-- | A list of 'DimIndex's, indicating how an array should be sliced.
-- Whenever a function accepts a 'Slice', that slice should be total,
-- i.e, cover all dimensions of the array.  Deviators should be
-- indicated by taking a list of 'DimIndex'es instead.
newtype Slice = Slice {unSlice :: [DimIndex]}
  deriving (Eq, Ord, Show)

-- | The type of a value.  When comparing types for equality with
-- '==', shapes must match.
data TypeBase shape u
  = Prim PrimType
  | -- | Token, index space, element type, and uniqueness.
    Acc VName Shape [Type] u
  | Array PrimType shape u
  deriving (Show, Eq, Ord)

instance Bitraversable TypeBase where
  bitraverse f g (Array t shape u) = Array t <$> f shape <*> g u
  bitraverse _ _ (Prim pt) = pure $ Prim pt
  bitraverse _ g (Acc arrs ispace ts u) = Acc arrs ispace ts <$> g u

instance Functor (TypeBase shape) where
  fmap = fmapDefault

instance Foldable (TypeBase shape) where
  foldMap = foldMapDefault

instance Traversable (TypeBase shape) where
  traverse = bitraverse pure

instance Bifunctor TypeBase where
  bimap = bimapDefault

instance Bifoldable TypeBase where
  bifoldMap = bifoldMapDefault

-- | A type with shape information, used for describing the type of
-- variables.
type Type = TypeBase Shape NoUniqueness

-- | A type with existentially quantified shapes - used as part of
-- function (and function-like) return types.  Generally only makes
-- sense when used in a list.
type ExtType = TypeBase ExtShape NoUniqueness

-- | A type with shape and uniqueness information, used declaring
-- return- and parameters types.
type DeclType = TypeBase Shape Uniqueness

-- | An 'ExtType' with uniqueness information, used for function
-- return types.
type DeclExtType = TypeBase ExtShape Uniqueness

-- | An element of a pattern - consisting of a name and a type.
data PatElem = PatElem
  { -- | The name being bound.
    patElemName :: VName,
    -- | Pat element decoration.
    patElemDec :: Type
  }
  deriving (Ord, Show, Eq)

-- | A pattern is conceptually just a list of names and their types.
newtype Pat = Pat {patElems :: [PatElem]}
  deriving (Ord, Show, Eq)

-- | A function or lambda parameter.
data Param dec = Param
  { -- | Attributes of the parameter.  When constructing a parameter,
    -- feel free to just pass 'mempty'.
    paramAttrs :: Attrs,
    -- | Name of the parameter.
    paramName :: VName,
    -- | Function parameter decoration.
    paramDec :: dec
  }
  deriving (Ord, Show, Eq)

type LParam = Param Type

type FParam = Param DeclType

-- | Anonymous function for use in a SOAC.
data Lambda = Lambda
  { lambdaParams :: [LParam],
    lambdaReturnType :: [Type],
    lambdaBody :: Body
  }
  deriving (Eq, Ord, Show)

-- | Information about computing a single histogram.
data HistOp = HistOp
  { histShape :: Shape,
    -- | Race factor @RF@ means that only @1/RF@
    -- bins are used.
    histRaceFactor :: SubExp,
    histDest :: [VName],
    histNeutral :: [SubExp],
    histOp :: Lambda
  }
  deriving (Eq, Ord, Show)

-- | How to compute a single scan result.
data Scan = Scan
  { scanLambda :: Lambda,
    scanNeutral :: [SubExp]
  }
  deriving (Eq, Ord, Show)

-- | How to compute a single reduction result.
data Reduce = Reduce
  { redComm :: Commutativity,
    redLambda :: Lambda,
    redNeutral :: [SubExp]
  }
  deriving (Eq, Ord, Show)

-- | The essential parts of a 'Screma' factored out (everything
-- except the input arrays).
data ScremaForm
  = ScremaForm
      [Scan]
      [Reduce]
      Lambda
  deriving (Eq, Ord, Show)

-- | A Second-Order Array Combinator.
data SOAC
  = Stream SubExp [VName] [SubExp] Lambda
  | -- | @Scatter <length> <inputs> <lambda> <outputs>@
    --
    -- Scatter maps values from a set of input arrays to indices and values of a
    -- set of output arrays. It is able to write multiple values to multiple
    -- outputs each of which may have multiple dimensions.
    --
    -- <inputs> is a list of input arrays, all having size <length>, elements of
    -- which are applied to the <lambda> function. For instance, if there are
    -- two arrays, <lambda> will get two values as input, one from each array.
    --
    -- <outputs> specifies the result of the <lambda> and which arrays to write
    -- to. Each element of the list consists of a <VName> specifying which array
    -- to scatter to, a <Shape> describing the shape of that array, and an <Int>
    -- describing how many elements should be written to that array for each
    -- invocation of the <lambda>.
    --
    -- <lambda> is a function that takes inputs from <inputs> and returns values
    -- according to the output-specification in <outputs>. It returns values in
    -- the following manner:
    --
    --     [index_0, index_1, ..., index_n, value_0, value_1, ..., value_m]
    --
    -- For each output in <outputs>, <lambda> returns <i> * <j> index values and
    -- <j> output values, where <i> is the number of dimensions (rank) of the
    -- given output, and <j> is the number of output values written to the given
    -- output.
    --
    -- For example, given the following output specification:
    --
    --     [([x1, y1, z1], 2, arr1), ([x2, y2], 1, arr2)]
    --
    -- <lambda> will produce 6 (3 * 2) index values and 2 output values for
    -- <arr1>, and 2 (2 * 1) index values and 1 output value for
    -- arr2. Additionally, the results are grouped, so the first 6 index values
    -- will correspond to the first two output values, and so on. For this
    -- example, <lambda> should return a total of 11 values, 8 index values and
    -- 3 output values.  See also 'splitScatterResults'.
    Scatter SubExp [VName] Lambda [(Shape, Int, VName)]
  | -- | @Hist <length> <input arrays> <dest-arrays-and-ops> <bucket fun>@
    --
    -- The final lambda produces indexes and values for the 'HistOp's.
    Hist SubExp [VName] [HistOp] Lambda
  | -- | A combination of scan, reduction, and map.  The first
    -- t'SubExp' is the size of the input arrays.
    Screma SubExp [VName] ScremaForm
  deriving (Eq, Ord, Show)

-- | Information about which parts of a value/type are consumed.  For
-- example, we might say that a function taking three arguments of
-- types @([int], *[int], [int])@ has diet @[Observe, Consume,
-- Observe]@.
data Diet
  = -- | Consumes this value.
    Consume
  | -- | Only observes value in this position, does
    -- not consume.  A result may alias this.
    Observe
  | -- | As 'Observe', but the result will not
    -- alias, because the parameter does not carry
    -- aliases.
    ObservePrim
  deriving (Eq, Ord, Show)

-- | Apart from being Opaque, what else is going on here?
data OpaqueOp
  = -- | No special operation.
    OpaqueNil
  | -- | Print the argument, prefixed by this string.
    OpaqueTrace T.Text
  deriving (Eq, Ord, Show)

-- | Which kind of reshape is this?
data ReshapeKind
  = -- | New shape is dynamically same as original.
    ReshapeCoerce
  | -- | Any kind of reshaping.
    ReshapeArbitrary
  deriving (Eq, Ord, Show)

-- | Information about the possible aliases of a function result.
data RetAls = RetAls
  { -- | Which of the parameters may be aliased, numbered from zero.
    paramAls :: [Int],
    -- | Which of the other results may be aliased, numbered from
    -- zero.  This must be a reflexive relation.
    otherAls :: [Int]
  }
  deriving (Eq, Ord, Show)

instance Monoid RetAls where
  mempty = RetAls mempty mempty

instance Semigroup RetAls where
  RetAls pals1 rals1 <> RetAls pals2 rals2 =
    RetAls (pals1 <> pals2) (rals1 <> rals2)

-- | A non-default case in a 'Match' statement.  The number of
-- elements in the pattern must match the number of scrutinees.  A
-- 'Nothing' value indicates that we don't care about it (i.e. a
-- wildcard).
data Case = Case {casePat :: [Maybe PrimValue], caseBody :: Body}
  deriving (Eq, Ord, Show)

-- | For-loop or while-loop?
data LoopForm
  = ForLoop
      VName
      -- ^ The loop iterator var
      IntType
      -- ^ The type of the loop iterator var
      SubExp
      -- ^ The number of iterations.
      [(LParam, VName)]
  | WhileLoop VName
  deriving (Eq, Ord, Show)

-- | The root Futhark expression type.
data Exp
  = -- | A variable or constant.
    SubExp SubExp
  | -- | Semantically and operationally just identity, but is
    -- invisible/impenetrable to optimisations (hopefully).  This
    -- partially a hack to avoid optimisation (so, to work around
    -- compiler limitations), but is also used to implement tracing
    -- and other operations that are semantically invisible, but have
    -- some sort of effect (brrr).
    Opaque OpaqueOp SubExp
  | -- | Array literals, e.g., @[ [1+x, 3], [2, 1+4] ]@.
    -- Second arg is the element type of the rows of the array.
    ArrayLit [SubExp] Type
  | -- | Unary operation.
    UnOp UnOp SubExp
  | -- | Binary operation.
    BinOp BinOp SubExp SubExp
  | -- | Comparison - result type is always boolean.
    CmpOp CmpOp SubExp SubExp
  | -- | Conversion "casting".
    ConvOp ConvOp SubExp
  | -- | Turn a boolean into a certificate, halting the program with the
    -- given error message if the boolean is false.
    Assert SubExp T.Text
  | -- | The certificates for bounds-checking are part of the 'Stm'.
    Index VName Slice
  | -- | An in-place update of the given array at the given position.
    -- Consumes the array.  If 'Safe', perform a run-time bounds check
    -- and ignore the write if out of bounds (like @Scatter@).
    Update Safety VName Slice SubExp
  | -- | @concat(0, [1] :| [[2, 3, 4], [5, 6]], 6) = [1, 2, 3, 4, 5, 6]@
    --
    -- Concatenates the non-empty list of 'VName' resulting in an
    -- array of length t'SubExp'. The 'Int' argument is used to
    -- specify the dimension along which the arrays are
    -- concatenated. For instance:
    --
    -- @concat(1, [[1,2], [3, 4]] :| [[[5,6]], [[7, 8]]], 4) = [[1, 2, 5, 6], [3, 4, 7, 8]]@
    Concat Int (NonEmpty VName) SubExp
  | -- | Manifest an array with dimensions represented in the given
    -- order.  The result will not alias anything.
    Manifest [Int] VName
  | -- Array construction.

    -- | @iota(n, x, s) = [x,x+s,..,x+(n-1)*s]@.
    --
    -- The t'IntType' indicates the type of the array returned and the
    -- offset/stride arguments, but not the length argument.
    Iota SubExp SubExp SubExp IntType
  | -- | @replicate([3][2],1) = [[1,1], [1,1], [1,1]]@.  The result
    -- has no aliases.  Copy a value by passing an empty shape.
    Replicate Shape SubExp
  | -- | Create array of given type and shape, with undefined elements.
    Scratch PrimType [SubExp]
  | -- | 1st arg is the new shape, 2nd arg is the input array.
    Reshape ReshapeKind Shape VName
  | -- | Permute the dimensions of the input array.  The list
    -- of integers is a list of dimensions (0-indexed), which
    -- must be a permutation of @[0,n-1]@, where @n@ is the
    -- number of dimensions in the input array.
    Rearrange [Int] VName
  | -- | Update an accumulator at the given index with the given value.
    -- Consumes the accumulator and produces a new one.
    UpdateAcc VName [SubExp] [SubExp]
  | -- Now for the complicated cases.
    Apply Name [(SubExp, Diet)] [(DeclExtType, RetAls)] Safety
  | Match [SubExp] [Case] Body [ExtType]
  | Loop [(FParam, SubExp)] LoopForm Body
  | SOAC SOAC
  deriving (Eq, Ord, Show)

-- | A pairing of a subexpression and some certificates.
data SubExpRes = SubExpRes
  { resCerts :: Certs,
    resSubExp :: SubExp
  }
  deriving (Eq, Ord, Show)

-- | Construct a 'SubExpRes' with no certificates.
subExpRes :: SubExp -> SubExpRes
subExpRes = SubExpRes mempty

-- | Construct a 'SubExpRes' from a variable name.
varRes :: VName -> SubExpRes
varRes = subExpRes . Var

-- | Construct a 'Result' from subexpressions.
subExpsRes :: [SubExp] -> Result
subExpsRes = map subExpRes

-- | Construct a 'Result' from variable names.
varsRes :: [VName] -> Result
varsRes = map varRes

-- | The result of a body is a sequence of subexpressions.
type Result = [SubExpRes]

-- | A list of names used for certificates in some expressions.
newtype Certs = Certs {unCerts :: [VName]}
  deriving (Eq, Ord, Show)

instance Semigroup Certs where
  Certs x <> Certs y = Certs (x <> filter (`notElem` x) y)

instance Monoid Certs where
  mempty = Certs mempty

-- | A single attribute.
data Attr
  = AttrName Name
  | AttrInt Integer
  | AttrComp Name [Attr]
  deriving (Ord, Show, Eq)

instance IsString Attr where
  fromString = AttrName . fromString

-- | Every statement is associated with a set of attributes, which can
-- have various effects throughout the compiler.
newtype Attrs = Attrs {unAttrs :: S.Set Attr}
  deriving (Ord, Show, Eq, Monoid, Semigroup)

-- | Construct 'Attrs' from a single 'Attr'.
oneAttr :: Attr -> Attrs
oneAttr = Attrs . S.singleton

-- | Auxilliary Information associated with a statement.
data StmAux = StmAux
  { stmAuxCerts :: !Certs,
    stmAuxAttrs :: Attrs
  }
  deriving (Ord, Show, Eq)

-- | A variable binding.
data Stm = Let
  { -- | Pat.
    stmPat :: Pat,
    -- | Auxiliary information statement.
    stmAux :: StmAux,
    -- | Expression.
    stmExp :: Exp
  }
  deriving (Eq, Ord, Show)

type Stms = [Stm]

-- | A body consists of a sequence of statements, terminating in a
-- list of result values.
data Body = Body
  { bodyStms :: Stms,
    bodyResult :: Result
  }
  deriving (Eq, Ord, Show)

-- | Since the core language does not care for signedness, but the
-- source language does, entry point input/output information has
-- metadata for integer types (and arrays containing these) that
-- indicate whether they are really unsigned integers.  This doesn't
-- matter for non-integer types.
data Signedness
  = Unsigned
  | Signed
  deriving (Eq, Ord, Show)

-- | An actual non-opaque type that can be passed to and from Futhark
-- programs, or serve as the contents of opaque types.  Scalars are
-- represented with zero rank.
data ValueType
  = ValueType Signedness Rank PrimType
  deriving (Eq, Ord, Show)

-- | Every entry point argument and return value has an annotation
-- indicating how it maps to the original source program type.
data EntryPointType
  = -- | An opaque type of this name.
    TypeOpaque Name
  | -- | A transparent type, which is scalar if the rank is zero.
    TypeTransparent ValueType
  deriving (Eq, Show, Ord)

-- | The representation of an opaque type.
data OpaqueType
  = OpaqueType [ValueType]
  | -- | Note that the field ordering here denote the actual
    -- representation - make sure it is preserved.
    OpaqueRecord [(Name, EntryPointType)]
  deriving (Eq, Ord, Show)

-- | Names of opaque types and their representation.
newtype OpaqueTypes = OpaqueTypes [(Name, OpaqueType)]
  deriving (Eq, Ord, Show)

instance Monoid OpaqueTypes where
  mempty = OpaqueTypes mempty

instance Semigroup OpaqueTypes where
  OpaqueTypes x <> OpaqueTypes y =
    OpaqueTypes $ x <> filter ((`notElem` map fst x) . fst) y

-- | An entry point parameter, comprising its name and original type.
data EntryParam = EntryParam
  { entryParamName :: Name,
    entryParamUniqueness :: Uniqueness,
    entryParamType :: EntryPointType
  }
  deriving (Eq, Show, Ord)

-- | An entry point result type.
data EntryResult = EntryResult
  { entryResultUniqueness :: Uniqueness,
    entryResultType :: EntryPointType
  }
  deriving (Eq, Show, Ord)

-- | Information about the inputs and outputs (return value) of an entry
-- point.
type EntryPoint = (Name, [EntryParam], [EntryResult])

-- | Function definitions.
data FunDef = FunDef
  { -- | Contains a value if this function is
    -- an entry point.
    funDefEntryPoint :: Maybe EntryPoint,
    funDefAttrs :: Attrs,
    funDefName :: Name,
    funDefRetType :: [(DeclExtType, RetAls)],
    funDefParams :: [FParam],
    funDefBody :: Body
  }
  deriving (Eq, Ord, Show)

-- | An entire Futhark program.
data Prog = Prog
  { -- | The opaque types used in entry points.  This information is
    -- used to generate extra API functions for
    -- construction and deconstruction of values of these types.
    progTypes :: OpaqueTypes,
    -- | Top-level constants that are computed at program startup, and
    -- which are in scope inside all functions.
    progConsts :: Stms,
    -- | The functions comprising the program.  All functions are also
    -- available in scope in the definitions of the constants, so be
    -- careful not to introduce circular dependencies (not currently
    -- checked).
    progFuns :: [FunDef]
  }
  deriving (Eq, Ord, Show)

--- Prettyprinting instances

-- | Convert a 'Doc' to text.  This ignores any annotations (i.e. it
-- will be non-coloured output).
docText :: Doc a -> T.Text
docText = Data.Text.Prettyprint.Doc.Render.Text.renderStrict . layouter
  where
    layouter =
      layoutSmart defaultLayoutOptions {layoutPageWidth = Unbounded}

-- | Prettyprint a value to a 'Text', appropriately wrapped.
prettyText :: (Pretty a) => a -> T.Text
prettyText = docText . pretty

-- | Separate with commas.
commasep :: [Doc a] -> Doc a
commasep = hsep . punctuate comma

-- | Like 'commasep', but a newline after every comma.
commastack :: [Doc a] -> Doc a
commastack = align . vsep . punctuate comma

ppTuple' :: [Doc a] -> Doc a
ppTuple' ets = braces $ commasep $ map align ets

ppTupleLines' :: [Doc a] -> Doc a
ppTupleLines' ets = braces $ commastack $ map align ets

-- | Surround the given document with enclosers and add linebreaks and
-- indents.
nestedBlock :: Doc a -> Doc a -> Doc a -> Doc a
nestedBlock pre post body = vsep [pre, indent 2 body, post]

-- | The document @'apply' ds@ separates @ds@ with commas and encloses
-- them with parentheses.
apply :: [Doc a] -> Doc a
apply = parens . align . commasep . map align

-- | Stack and prepend a list of 'Doc's to another 'Doc', separated by
-- a linebreak.  If the list is empty, the second 'Doc' will be
-- returned without a preceding linebreak.
annot :: [Doc a] -> Doc a -> Doc a
annot [] s = s
annot l s = vsep (l ++ [s])

(</>) :: Doc a -> Doc a -> Doc a
a </> b = a <> line <> b

-- | Separate with linebreaks.
stack :: [Doc a] -> Doc a
stack = align . mconcat . punctuate line

instance Pretty IntType where
  pretty Int8 = "i8"
  pretty Int16 = "i16"
  pretty Int32 = "i32"
  pretty Int64 = "i64"

instance Pretty FloatType where
  pretty Float16 = "f16"
  pretty Float32 = "f32"
  pretty Float64 = "f64"

instance Pretty PrimType where
  pretty (IntType t) = pretty t
  pretty (FloatType t) = pretty t
  pretty Bool = "bool"
  pretty Unit = "unit"

instance Pretty IntValue where
  pretty (Int8Value v) = pretty $ show v ++ "i8"
  pretty (Int16Value v) = pretty $ show v ++ "i16"
  pretty (Int32Value v) = pretty $ show v ++ "i32"
  pretty (Int64Value v) = pretty $ show v ++ "i64"

instance Pretty FloatValue where
  pretty (Float16Value v)
    | isInfinite v, v >= 0 = "f16.inf"
    | isInfinite v, v < 0 = "-f16.inf"
    | isNaN v = "f16.nan"
    | otherwise = pretty $ show v ++ "f16"
  pretty (Float32Value v)
    | isInfinite v, v >= 0 = "f32.inf"
    | isInfinite v, v < 0 = "-f32.inf"
    | isNaN v = "f32.nan"
    | otherwise = pretty $ show v ++ "f32"
  pretty (Float64Value v)
    | isInfinite v, v >= 0 = "f64.inf"
    | isInfinite v, v < 0 = "-f64.inf"
    | isNaN v = "f64.nan"
    | otherwise = pretty $ show v ++ "f64"

instance Pretty Name where
  pretty = pretty . nameToString

instance Pretty Uniqueness where
  pretty Unique = "*"
  pretty Nonunique = mempty

instance Pretty NoUniqueness where
  pretty _ = mempty

instance Pretty VName where
  pretty (VName vn i) = pretty vn <> "_" <> pretty (show i)

instance Pretty SubExp where
  pretty (Var v) = pretty v
  pretty (Constant v) = pretty v

instance Pretty Commutativity where
  pretty Commutative = "commutative"
  pretty Noncommutative = "noncommutative"

instance Pretty Shape where
  pretty = mconcat . map (brackets . pretty) . shapeDims

instance Pretty Rank where
  pretty (Rank r) = mconcat $ replicate r "[]"

instance (Pretty a) => Pretty (Ext a) where
  pretty (Free e) = pretty e
  pretty (Ext x) = "?" <> pretty (show x)

instance Pretty ExtShape where
  pretty = mconcat . map (brackets . pretty) . shapeDims

instance (Pretty u) => Pretty (TypeBase Shape u) where
  pretty (Prim t) = pretty t
  pretty (Acc acc ispace ts u) =
    pretty u
      <> "acc"
      <> apply
        [ pretty acc,
          pretty ispace,
          ppTuple' $ map pretty ts
        ]
  pretty (Array et (Shape ds) u) =
    pretty u <> mconcat (map (brackets . pretty) ds) <> pretty et

instance (Pretty u) => Pretty (TypeBase ExtShape u) where
  pretty (Prim t) = pretty t
  pretty (Acc acc ispace ts u) =
    pretty u
      <> "acc"
      <> apply
        [ pretty acc,
          pretty ispace,
          ppTuple' $ map pretty ts
        ]
  pretty (Array et (Shape ds) u) =
    pretty u <> mconcat (map (brackets . pretty) ds) <> pretty et

instance (Pretty u) => Pretty (TypeBase Rank u) where
  pretty (Prim t) = pretty t
  pretty (Acc acc ispace ts u) =
    pretty u
      <> "acc"
      <> apply
        [ pretty acc,
          pretty ispace,
          ppTuple' $ map pretty ts
        ]
  pretty (Array et (Rank n) u) =
    pretty u <> mconcat (replicate n $ brackets mempty) <> pretty et

instance Pretty Certs where
  pretty (Certs []) = mempty
  pretty (Certs cs) = "#" <> braces (commasep (map pretty cs))

instance Pretty Attr where
  pretty (AttrName v) = pretty v
  pretty (AttrInt x) = pretty x
  pretty (AttrComp f attrs) = pretty f <> parens (commasep $ map pretty attrs)

attrAnnots :: Attrs -> [Doc a]
attrAnnots = map f . toList . unAttrs
  where
    f v = "#[" <> pretty v <> "]"

stmAttrAnnots :: Stm -> [Doc a]
stmAttrAnnots = attrAnnots . stmAuxAttrs . stmAux

certAnnots :: Certs -> [Doc a]
certAnnots cs
  | cs == mempty = []
  | otherwise = [pretty cs]

stmCertAnnots :: Stm -> [Doc a]
stmCertAnnots = certAnnots . stmAuxCerts . stmAux

instance Pretty Attrs where
  pretty = hsep . attrAnnots

instance Pretty Pat where
  pretty (Pat xs) = braces $ commastack $ map pretty xs

instance Pretty PatElem where
  pretty (PatElem name t) = pretty name <+> colon <+> align (pretty t)

instance (Pretty t) => Pretty (Param t) where
  pretty (Param attrs name t) =
    annot (attrAnnots attrs) $ pretty name <+> colon <+> align (pretty t)

instance Pretty DimIndex where
  pretty (DimFix i) = pretty i
  pretty (DimSlice i n s) = pretty i <+> ":+" <+> pretty n <+> "*" <+> pretty s

instance Pretty Slice where
  pretty (Slice xs) = brackets (commasep (map pretty xs))

taggedF :: String -> FloatType -> Doc a
taggedF s Float16 = pretty $ s ++ "16"
taggedF s Float32 = pretty $ s ++ "32"
taggedF s Float64 = pretty $ s ++ "64"

taggedI :: String -> IntType -> Doc a
taggedI s Int8 = pretty $ s ++ "8"
taggedI s Int16 = pretty $ s ++ "16"
taggedI s Int32 = pretty $ s ++ "32"
taggedI s Int64 = pretty $ s ++ "64"

instance Pretty UnOp where
  pretty Not = "not"
  pretty (Abs t) = taggedI "abs" t
  pretty (FAbs t) = taggedF "fabs" t
  pretty (SSignum t) = taggedI "ssignum" t
  pretty (USignum t) = taggedI "usignum" t
  pretty (FSignum t) = taggedF "fsignum" t
  pretty (Complement t) = taggedI "complement" t

instance Pretty BinOp where
  pretty (Add t OverflowWrap) = taggedI "add" t
  pretty (Add t OverflowUndef) = taggedI "add_nw" t
  pretty (Sub t OverflowWrap) = taggedI "sub" t
  pretty (Sub t OverflowUndef) = taggedI "sub_nw" t
  pretty (Mul t OverflowWrap) = taggedI "mul" t
  pretty (Mul t OverflowUndef) = taggedI "mul_nw" t
  pretty (FAdd t) = taggedF "fadd" t
  pretty (FSub t) = taggedF "fsub" t
  pretty (FMul t) = taggedF "fmul" t
  pretty (UDiv t Safe) = taggedI "udiv_safe" t
  pretty (UDiv t Unsafe) = taggedI "udiv" t
  pretty (UDivUp t Safe) = taggedI "udiv_up_safe" t
  pretty (UDivUp t Unsafe) = taggedI "udiv_up" t
  pretty (UMod t Safe) = taggedI "umod_safe" t
  pretty (UMod t Unsafe) = taggedI "umod" t
  pretty (SDiv t Safe) = taggedI "sdiv_safe" t
  pretty (SDiv t Unsafe) = taggedI "sdiv" t
  pretty (SDivUp t Safe) = taggedI "sdiv_up_safe" t
  pretty (SDivUp t Unsafe) = taggedI "sdiv_up" t
  pretty (SMod t Safe) = taggedI "smod_safe" t
  pretty (SMod t Unsafe) = taggedI "smod" t
  pretty (SQuot t Safe) = taggedI "squot_safe" t
  pretty (SQuot t Unsafe) = taggedI "squot" t
  pretty (SRem t Safe) = taggedI "srem_safe" t
  pretty (SRem t Unsafe) = taggedI "srem" t
  pretty (FDiv t) = taggedF "fdiv" t
  pretty (FMod t) = taggedF "fmod" t
  pretty (SMin t) = taggedI "smin" t
  pretty (UMin t) = taggedI "umin" t
  pretty (FMin t) = taggedF "fmin" t
  pretty (SMax t) = taggedI "smax" t
  pretty (UMax t) = taggedI "umax" t
  pretty (FMax t) = taggedF "fmax" t
  pretty (Shl t) = taggedI "shl" t
  pretty (LShr t) = taggedI "lshr" t
  pretty (AShr t) = taggedI "ashr" t
  pretty (And t) = taggedI "and" t
  pretty (Or t) = taggedI "or" t
  pretty (Xor t) = taggedI "xor" t
  pretty (Pow t) = taggedI "pow" t
  pretty (FPow t) = taggedF "fpow" t
  pretty LogAnd = "logand"
  pretty LogOr = "logor"

instance Pretty CmpOp where
  pretty (CmpEq t) = "eq_" <> pretty t
  pretty (CmpUlt t) = taggedI "ult" t
  pretty (CmpUle t) = taggedI "ule" t
  pretty (CmpSlt t) = taggedI "slt" t
  pretty (CmpSle t) = taggedI "sle" t
  pretty (FCmpLt t) = taggedF "lt" t
  pretty (FCmpLe t) = taggedF "le" t
  pretty CmpLlt = "llt"
  pretty CmpLle = "lle"

instance Pretty ConvOp where
  pretty op = convOp $ convOpFun op
    where
      (from, to) = convOpType op
      convOp s = pretty s <> "_" <> pretty from <> "_" <> pretty to

prettyRet :: (Pretty t) => (t, RetAls) -> Doc a
prettyRet (t, RetAls pals rals)
  | pals == mempty,
    rals == mempty =
      pretty t
  | otherwise =
      pretty t <> "#" <> parens (pl pals <> comma <+> pl rals)
  where
    pl = brackets . commasep . map pretty

instance Pretty Lambda where
  pretty (Lambda [] [] (Body stms [])) | stms == mempty = "nilFn"
  pretty (Lambda params rettype body) =
    "\\"
      <+> braces (commastack $ map pretty params)
      </> indent 2 (colon <+> ppTupleLines' (map pretty rettype) <+> "->")
      </> indent 2 (pretty body)

-- | Prettyprint the given Screma.
ppScrema ::
  (Pretty inp) => SubExp -> [inp] -> ScremaForm -> Doc ann
ppScrema w arrs (ScremaForm scans reds map_lam) =
  "screma"
    <> (parens . align)
      ( pretty w
          <> comma
          </> ppTuple' (map pretty arrs)
            <> comma
          </> braces (mconcat $ intersperse (comma <> line) $ map pretty scans)
            <> comma
          </> braces (mconcat $ intersperse (comma <> line) $ map pretty reds)
            <> comma
          </> pretty map_lam
      )

-- | Prettyprint the given Stream.
ppStream ::
  (Pretty inp) => SubExp -> [inp] -> [SubExp] -> Lambda -> Doc ann
ppStream size arrs acc lam =
  "streamSeq"
    <> (parens . align)
      ( pretty size
          <> comma
          </> ppTuple' (map pretty arrs)
            <> comma
          </> ppTuple' (map pretty acc)
            <> comma
          </> pretty lam
      )

-- | Prettyprint the given Scatter.
ppScatter ::
  (Pretty inp) => SubExp -> [inp] -> Lambda -> [(Shape, Int, VName)] -> Doc ann
ppScatter w arrs lam dests =
  "scatter"
    <> (parens . align)
      ( pretty w
          <> comma
          </> ppTuple' (map pretty arrs)
            <> comma
          </> pretty lam
            <> comma
          </> commasep (map pretty dests)
      )

instance Pretty Scan where
  pretty (Scan scan_lam scan_nes) =
    pretty scan_lam <> comma </> braces (commasep $ map pretty scan_nes)

ppComm :: Commutativity -> Doc ann
ppComm Noncommutative = mempty
ppComm Commutative = "commutative "

instance Pretty Reduce where
  pretty (Reduce comm red_lam red_nes) =
    ppComm comm
      <> pretty red_lam
      <> comma
      </> braces (commasep $ map pretty red_nes)

-- | Prettyprint the given histogram operation.
ppHist ::
  (Pretty inp) =>
  SubExp ->
  [inp] ->
  [HistOp] ->
  Lambda ->
  Doc ann
ppHist w arrs ops bucket_fun =
  "hist"
    <> parens
      ( pretty w
          <> comma
          </> ppTuple' (map pretty arrs)
            <> comma
          </> braces (mconcat $ intersperse (comma <> line) $ map ppOp ops)
            <> comma
          </> pretty bucket_fun
      )
  where
    ppOp (HistOp dest_w rf dests nes op) =
      pretty dest_w
        <> comma
        <+> pretty rf
          <> comma
        <+> braces (commasep $ map pretty dests)
          <> comma
        </> ppTuple' (map pretty nes)
          <> comma
        </> pretty op

instance Pretty SOAC where
  pretty (Stream size arrs acc lam) =
    ppStream size arrs acc lam
  pretty (Scatter w arrs lam dests) =
    ppScatter w arrs lam dests
  pretty (Hist w arrs ops bucket_fun) =
    ppHist w arrs ops bucket_fun
  pretty (Screma w arrs (ScremaForm scans reds map_lam))
    | null scans,
      null reds =
        "map"
          <> (parens . align)
            ( pretty w
                <> comma
                </> ppTuple' (map pretty arrs)
                  <> comma
                </> pretty map_lam
            )
    | null scans =
        "redomap"
          <> (parens . align)
            ( pretty w
                <> comma
                </> ppTuple' (map pretty arrs)
                  <> comma
                </> braces (mconcat $ intersperse (comma <> line) $ map pretty reds)
                  <> comma
                </> pretty map_lam
            )
    | null reds =
        "scanomap"
          <> (parens . align)
            ( pretty w
                <> comma
                </> ppTuple' (map pretty arrs)
                  <> comma
                </> braces (mconcat $ intersperse (comma <> line) $ map pretty scans)
                  <> comma
                </> pretty map_lam
            )
  pretty (Screma w arrs form) = ppScrema w arrs form

maybeNest :: Body -> Doc a
maybeNest b
  | null $ bodyStms b = pretty b
  | otherwise = nestedBlock "{" "}" $ pretty b

instance Pretty Case where
  pretty (Case vs b) =
    "case" <+> ppTuple' (map (maybe "_" pretty) vs) <+> "->" <+> maybeNest b

instance Pretty Exp where
  pretty (SubExp se) = pretty se
  pretty (Opaque OpaqueNil e) = "opaque" <> apply [pretty e]
  pretty (Opaque (OpaqueTrace s) e) = "trace" <> apply [pretty (show s), pretty e]
  pretty (ArrayLit es rt) =
    case rt of
      Array {} -> brackets $ commastack $ map pretty es
      _ -> brackets $ commasep $ map pretty es
      <+> colon
      <+> "[]" <> pretty rt
  pretty (BinOp bop x y) = pretty bop <> parens (pretty x <> comma <+> pretty y)
  pretty (CmpOp op x y) = pretty op <> parens (pretty x <> comma <+> pretty y)
  pretty (ConvOp conv x) =
    pretty (convOpFun conv) <+> pretty fromtype <+> pretty x <+> "to" <+> pretty totype
    where
      (fromtype, totype) = convOpType conv
  pretty (UnOp op e) = pretty op <+> pretty e
  pretty (Index v slice) = pretty v <> pretty slice
  pretty (Update safety src slice se) =
    pretty src <+> with <+> pretty slice <+> "=" <+> pretty se
    where
      with = case safety of
        Unsafe -> "with"
        Safe -> "with?"
  pretty (Iota e x s et) =
    "iota" <> et' <> apply [pretty e, pretty x, pretty s]
    where
      et' = pretty $ show $ primBitSize $ IntType et
  pretty (Replicate (Shape []) e) = "copy" <> parens (pretty e)
  pretty (Replicate ne ve) =
    "replicate" <> apply [pretty ne, align (pretty ve)]
  pretty (Scratch t shape) =
    "scratch" <> apply (pretty t : map pretty shape)
  pretty (Reshape ReshapeArbitrary shape e) =
    "reshape" <> apply [pretty shape, pretty e]
  pretty (Reshape ReshapeCoerce shape e) =
    "coerce" <> apply [pretty shape, pretty e]
  pretty (Rearrange perm e) =
    "rearrange" <> apply [apply (map pretty perm), pretty e]
  pretty (Concat i (x :| xs) w) =
    "concat" <> "@" <> pretty i <> apply (pretty w : pretty x : map pretty xs)
  pretty (Manifest perm e) = "manifest" <> apply [apply (map pretty perm), pretty e]
  pretty (Assert e msg) =
    "assert" <> apply [pretty e, pretty msg, "\"\""]
  pretty (UpdateAcc acc is v) =
    "update_acc"
      <> apply
        [ pretty acc,
          ppTuple' $ map pretty is,
          ppTuple' $ map pretty v
        ]
  pretty (Match [c] [Case [Just (BoolValue True)] t] f ret) =
    "if"
      <+> pretty c
      </> "then"
      <+> maybeNest t
      <+> "else"
      <+> maybeNest f
      </> colon
      <+> ppTupleLines' (map pretty ret)
  pretty (Match ses cs defb ret) =
    ("match" <+> ppTuple' (map pretty ses))
      </> stack (map pretty cs)
      </> "default"
      <+> "->"
      <+> maybeNest defb
      </> colon
      <+> ppTupleLines' (map pretty ret)
  pretty (Apply fname args ret safety) =
    applykw
      <+> pretty (nameToString fname)
        <> apply (map (align . prettyArg) args)
      </> colon
      <+> braces (commasep $ map prettyRet ret)
    where
      prettyArg (arg, Consume) = "*" <> pretty arg
      prettyArg (arg, _) = pretty arg
      applykw = case safety of
        Unsafe -> "apply <unsafe>"
        Safe -> "apply"
  pretty (Loop merge form loopbody) =
    "loop"
      <+> braces (commastack $ map pretty params)
      <+> equals
      <+> ppTuple' (map pretty args)
      </> ( case form of
              ForLoop i it bound [] ->
                "for"
                  <+> align
                    ( pretty i <> ":" <> pretty it
                        <+> "<"
                        <+> align (pretty bound)
                    )
              ForLoop i it bound loop_vars ->
                "for"
                  <+> align
                    ( pretty i
                        <> ":"
                        <> pretty it
                        <+> "<"
                        <+> align (pretty bound)
                        </> stack (map prettyLoopVar loop_vars)
                    )
              WhileLoop cond ->
                "while" <+> pretty cond
          )
      <+> "do"
      <+> nestedBlock "{" "}" (pretty loopbody)
    where
      (params, args) = unzip merge
      prettyLoopVar (p, a) = pretty p <+> "in" <+> pretty a
  pretty (SOAC soac) = pretty soac

instance Pretty Stm where
  pretty stm@(Let pat _ e) =
    align . hang 2 $
      "let"
        <+> align (pretty pat)
        <+> case stmannot of
          [] -> equals </> pretty e
          _ -> equals </> (stack stmannot </> pretty e)
    where
      stmannot =
        concat
          [ stmAttrAnnots stm,
            stmCertAnnots stm
          ]

instance Pretty SubExpRes where
  pretty (SubExpRes cs se) = hsep $ certAnnots cs ++ [pretty se]

instance Pretty Body where
  pretty (Body stms res)
    | null stms = braces (commasep $ map pretty res)
    | otherwise =
        stack (map pretty stms)
          </> "in"
          <+> braces (commasep $ map pretty res)

instance Pretty FunDef where
  pretty (FunDef entry attrs name rettype fparams body) =
    annot (attrAnnots attrs) $
      fun
        </> indent 2 (pretty (nameToString name))
        <+> parens (commastack $ map pretty fparams)
        </> indent 2 (colon <+> align (ppTupleLines' $ map prettyRet rettype))
        <+> equals
        <+> nestedBlock "{" "}" (pretty body)
    where
      fun = case entry of
        Nothing -> "fun"
        Just (p_name, p_entry, ret_entry) ->
          "entry"
            <> (parens . align)
              ( "\""
                  <> pretty p_name
                  <> "\""
                  <> comma
                  </> ppTupleLines' (map pretty p_entry)
                    <> comma
                  </> ppTupleLines' (map pretty ret_entry)
              )

instance Pretty Signedness where
  pretty Signed = "signed"
  pretty Unsigned = "unsigned"

-- | True if signed.  Only makes a difference for integer types.
prettySigned :: Bool -> PrimType -> T.Text
prettySigned True (IntType it) = T.cons 'u' (T.drop 1 (prettyText it))
prettySigned _ t = prettyText t

instance Pretty ValueType where
  pretty (ValueType s (Rank r) t) =
    mconcat (replicate r "[]") <> pretty (prettySigned (s == Unsigned) t)

instance Pretty EntryPointType where
  pretty (TypeTransparent t) = pretty t
  pretty (TypeOpaque desc) = "opaque" <+> dquotes (pretty desc)

instance Pretty EntryParam where
  pretty (EntryParam name u t) = pretty name <> colon <+> pretty u <> pretty t

instance Pretty EntryResult where
  pretty (EntryResult u t) = pretty u <> pretty t

instance Pretty OpaqueType where
  pretty (OpaqueType ts) =
    "opaque" <+> nestedBlock "{" "}" (stack $ map pretty ts)
  pretty (OpaqueRecord fs) =
    "record" <+> nestedBlock "{" "}" (stack $ map p fs)
    where
      p (f, et) = pretty f <> ":" <+> pretty et

instance Pretty OpaqueTypes where
  pretty (OpaqueTypes ts) = "types" <+> nestedBlock "{" "}" (stack $ map p ts)
    where
      p (name, t) = "type" <+> dquotes (pretty name) <+> equals <+> pretty t

instance Pretty Prog where
  pretty (Prog types consts funs) =
    stack $
      punctuate line $
        pretty types
          : stack (map pretty consts)
          : map pretty funs
