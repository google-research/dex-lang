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

module Types.Primitives where

import qualified Data.ByteString       as BS
import qualified Data.Set              as S
import Data.Int
import Data.Word
import Data.Hashable
import Data.Store (Store (..))
import Data.Text.Prettyprint.Doc (Pretty (..))
import qualified Data.Store.Internal as SI
import Foreign.Ptr
import GHC.Exts (inline)

import GHC.Generics (Generic (..))

import Name
import Err
import LabeledItems

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
      | Fin e
      | RefType (Maybe e) e
      | TypeKind
      | EffectRowKind
      | LabeledRowKindTC
      | LabelType
        deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

traversePrimTC :: Applicative f => (e -> f e') -> PrimTC e -> f (PrimTC e')
traversePrimTC = inline traverse
{-# INLINABLE traversePrimTC #-}

data PrimCon e =
        Lit LitVal
      | ProdCon [e]
      | SumCon    e Int e     -- type, tag, payload
      | SumAsProd e e   [[e]] -- type, tag, payload
      | LabelCon String
      | FinVal e e
      -- References
      | BaseTypeRef e
      | TabRef e
      | ConRef (PrimCon e)
      | RecordRef (LabeledItems e)
      -- Misc hacks
      | ExplicitDict e e  -- Dict type, method. Used in prelude for `run_accum`.
      | DictHole (AlwaysEqual SrcPosCtx) e -- Only used during type inference
        deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

newtype AlwaysEqual a = AlwaysEqual a
        deriving (Show, Generic, Functor, Foldable, Traversable, Hashable, Store)
instance Eq (AlwaysEqual a) where
  _ == _ = True

traversePrimCon :: Applicative f => (e -> f e') -> PrimCon e -> f (PrimCon e')
traversePrimCon = inline traverse
{-# INLINABLE traversePrimCon #-}

data PrimOp e =
        TabCon e [e]                 -- table type elements
      | BinOp BinOp e e
      | UnOp  UnOp  e
      | Select e e e                 -- predicate, val-if-true, val-if-false
      | CastOp e e                   -- Type, then value. See Type.hs for valid coercions.
      -- Effects
      | PrimEffect e (PrimEffect e)
      | ThrowError e                 -- Hard error (parameterized by result type)
      | ThrowException e             -- Catchable exceptions (unlike `ThrowError`)
      | Resume e e                   -- Resume from effect handler (type, arg)
      -- References
      | IndexRef e e
      | ProjRef Int e
      -- Low-level memory operations
      | IOAlloc BaseType e
      | IOFree e
      | PtrOffset e e
      | PtrLoad e
      | PtrStore e e
      -- Destination ops
      | AllocDest e  -- type
      | Place e e    -- reference, value
      | Freeze e     -- reference
      -- Vector operations
      | VectorBroadcast e e  -- value, vector type
      | VectorIota e  -- vector type
      | VectorSubref e e e -- ref, base ix, vector type
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
      -- Odds, ends and hacks.
      | ProjMethod e Int  -- project a method from the dict
      | ExplicitApply e e
      | MonoLiteral e
        deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

traversePrimOp :: Applicative f => (e -> f e') -> PrimOp e -> f (PrimOp e')
traversePrimOp = inline traverse
{-# INLINABLE traversePrimOp #-}

data PrimHof e =
        For ForAnn e e        -- ix dict, body lambda
      | While e
      | RunReader e e
      | RunWriter (BaseMonoidP e) e
      | RunState  e e
      | RunIO e
      | CatchException e
      | Linearize e
      | Transpose e
      -- Dex abstract machine ops
      | Seq Direction e e e   -- ix dict, carry dests, body lambda
        deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

data BaseMonoidP e = BaseMonoid { baseEmpty :: e, baseCombine :: e }
                     deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

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
type ForAnn = Direction

data RWS = Reader | Writer | State  deriving (Show, Eq, Ord, Generic)

data EffectP (name::E) (n::S) =
  RWSEffect RWS (Maybe (name n)) | ExceptionEffect | IOEffect
  deriving (Show, Eq, Ord, Generic)


data EffectRowP (name::E) (n::S) =
  EffectRow (S.Set (EffectP name n)) (Maybe (name n))
  deriving (Show, Eq, Ord, Generic)

pattern Pure :: Ord (name n) => EffectRowP name n
pattern Pure <- ((\(EffectRow effs t) -> (S.null effs, t)) -> (True, Nothing))
 where  Pure = EffectRow mempty Nothing

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

extendEffRow :: Ord (name n) => S.Set (EffectP name n) -> EffectRowP name n -> EffectRowP name n
extendEffRow effs (EffectRow effs' t) = EffectRow (effs <> effs') t
{-# INLINE extendEffRow #-}

singletonEffRow :: EffectP name n -> EffectRowP name n
singletonEffRow eff = EffectRow (S.singleton eff) Nothing

data Arrow =
   PlainArrow
 | ImplicitArrow
 | ClassArrow
 | LinArrow
   deriving (Show, Eq, Generic)

instance Pretty Arrow where
  pretty arr = case arr of
    PlainArrow     -> "->"
    LinArrow       -> "--o"
    ImplicitArrow  -> "?->"
    ClassArrow     -> "?=>"

data LetAnn = PlainLet
            | NoInlineLet
              deriving (Show, Eq, Generic)

-- === Primitive scalar values and base types ===

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
              deriving (Show, Eq, Ord, Generic)

data ScalarBaseType = Int64Type | Int32Type
                    | Word8Type | Word32Type | Word64Type
                    | Float64Type | Float32Type
                      deriving (Show, Eq, Ord, Generic)
data BaseType = Scalar  ScalarBaseType
              | Vector  [Word32] ScalarBaseType
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
  Vector _ _         -> error "Not implemented"
  PtrType _          -> ptrSize

ptrSize :: Int
ptrSize = 8

isIntegral :: ScalarBaseType -> Bool
isIntegral = \case
  Float64Type -> False
  Float32Type -> False
  _           -> True

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

-- === Typeclass instances ===

instance GenericE (EffectP name) where
  type RepE (EffectP name) =
    EitherE (PairE (LiftE RWS) (MaybeE name))
            (LiftE (Either () ()))
  fromE = \case
    RWSEffect rws name -> LeftE  (PairE (LiftE rws) $ toMaybeE name)
    ExceptionEffect -> RightE (LiftE (Left  ()))
    IOEffect        -> RightE (LiftE (Right ()))
  {-# INLINE fromE #-}
  toE = \case
    LeftE  (PairE (LiftE rws) name) -> RWSEffect rws $ fromMaybeE name
    RightE (LiftE (Left  ())) -> ExceptionEffect
    RightE (LiftE (Right ())) -> IOEffect
  {-# INLINE toE #-}

instance Color c => SinkableE      (EffectP (Name c))
instance Color c => HoistableE     (EffectP (Name c))
instance Color c => AlphaEqE       (EffectP (Name c))
instance Color c => AlphaHashableE (EffectP (Name c))
instance Color c => SubstE Name    (EffectP (Name c))

instance OrdE name => GenericE (EffectRowP name) where
  type RepE (EffectRowP name) = PairE (ListE (EffectP name)) (MaybeE name)
  fromE (EffectRow effs ext) = ListE (S.toList effs) `PairE` ext'
    where ext' = case ext of Just v  -> JustE v
                             Nothing -> NothingE
  {-# INLINE fromE #-}
  toE (ListE effs `PairE` ext) = EffectRow (S.fromList effs) ext'
    where ext' = case ext of JustE v  -> Just v
                             NothingE -> Nothing
                             _ -> error "impossible"
  {-# INLINE toE #-}

instance Color c => SinkableE         (EffectRowP (Name c))
instance Color c => HoistableE        (EffectRowP (Name c))
instance Color c => SubstE Name       (EffectRowP (Name c))
instance Color c => AlphaEqE          (EffectRowP (Name c))
instance Color c => AlphaHashableE    (EffectRowP (Name c))

instance Store Arrow
instance Store LetAnn
instance Store AddressSpace
instance Store RWS
instance Store Direction
instance Store UnOp
instance Store BinOp
instance Store CmpOp
instance Store BaseType
instance Store LitVal
instance Store ScalarBaseType
instance Store Device

instance Color c => Store (EffectRowP (Name c) n)
instance Color c => Store (EffectP    (Name c) n)

instance Store a => Store (PrimOp  a)
instance Store a => Store (PrimCon a)
instance Store a => Store (PrimTC  a)
instance Store a => Store (PrimHof a)
instance Store a => Store (PrimEffect a)
instance Store a => Store (BaseMonoidP a)

instance Hashable AddressSpace
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
instance Hashable LetAnn
instance Hashable Arrow

instance Hashable a => Hashable (PrimOp  a)
instance Hashable a => Hashable (PrimCon a)
instance Hashable a => Hashable (PrimTC  a)
instance Hashable a => Hashable (PrimHof a)
instance Hashable a => Hashable (PrimEffect a)
instance Hashable a => Hashable (BaseMonoidP a)
