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
import Data.Int
import Data.Word
import Data.Hashable
import Data.Store (Store (..))
import Data.Text.Prettyprint.Doc (Pretty (..))
import qualified Data.Store.Internal as SI
import Foreign.Ptr
import GHC.Exts (inline)

import GHC.Generics (Generic (..))

import Occurrence
import IRVariants

data PrimTC (r::IR) (e:: *) where
  BaseType         :: BaseType       -> PrimTC r e
  ProdType         :: [e]            -> PrimTC r e
  SumType          :: [e]            -> PrimTC r e
  RefType          :: e -> e         -> PrimTC r e
  -- TODO: `HasCore r` constraint
  TypeKind         ::                   PrimTC r e
  HeapType         ::                   PrimTC r e
  deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

traversePrimTC :: Applicative f => (e -> f e') -> PrimTC r e -> f (PrimTC r e')
traversePrimTC = inline traverse
{-# INLINABLE traversePrimTC #-}

data PrimCon (r::IR) (e:: *) where
  Lit          :: LitVal            -> PrimCon r e
  ProdCon      :: [e]               -> PrimCon r e
  SumCon       :: [e] -> Int -> e   -> PrimCon r e -- type, tag, payload
  HeapVal      ::                      PrimCon r e
  deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

data MemOp e =
   IOAlloc BaseType e
 | IOFree e
 | PtrOffset e e
 | PtrLoad e
 | PtrStore e e
   deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

data RecordOp e =
 -- Concatenate two records.
   RecordCons e e
 -- Split off a labeled row from the front of the record.
 | RecordSplit  e e
 -- Add a dynamically named field to a record (on the left).
 -- Args are as follows: label, value, record.
 | RecordConsDynamic e e e
 -- Splits a label from the record.
 | RecordSplitDynamic e e
   deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

data PrimOp e =
   UnOp     UnOp  e
 | BinOp    BinOp e e
 | MemOp    (MemOp e)
 | VectorOp (VectorOp e)
 | MiscOp   (MiscOp e)
   deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

traversePrimOp :: Applicative f => (e -> f e') -> PrimOp e -> f (PrimOp e')
traversePrimOp = inline traverse
{-# INLINABLE traversePrimOp #-}

data MiscOp e =
   Select e e e                 -- (3) predicate, val-if-true, val-if-false
 | CastOp e e                   -- (2) Type, then value. See CheckType.hs for valid coercions.
 | BitcastOp e e                -- (2) Type, then value. See CheckType.hs for valid coercions.
 | UnsafeCoerce e e             -- type, then value. Assumes runtime representation is the same.
 | GarbageVal e                 -- type of value (assume `Data` constraint)
 -- Effects
 | ThrowError e                 -- (1) Hard error (parameterized by result type)
 | ThrowException e             -- (1) Catchable exceptions (unlike `ThrowError`)
 -- Tag of a sum type
 | SumTag e
 -- Create an enum (payload-free ADT) from a Word8
 | ToEnum e e
 -- printing
 | OutputStream
 | ShowAny e    -- implemented in Simplify
 | ShowScalar e -- Implemented in Imp. Result is a pair of an `IdxRepValTy`
                -- giving the logical size of the result and a fixed-size table,
                -- `Fin showStringBufferSize => Char`, assumed to have sufficient space.
   deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

showStringBufferSize :: Word32
showStringBufferSize = 32

data VectorOp e =
   VectorBroadcast e e  -- value, vector type
 | VectorIota e  -- vector type
 | VectorSubref e e e -- ref, base ix, vector type
   deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

newtype AlwaysEqual a = AlwaysEqual a
        deriving (Show, Generic, Functor, Foldable, Traversable, Hashable, Store)
instance Eq (AlwaysEqual a) where
  _ == _ = True

traversePrimCon :: Applicative f => (e -> f e') -> PrimCon r e -> f (PrimCon r e')
traversePrimCon = inline traverse
{-# INLINABLE traversePrimCon #-}

data BinOp = IAdd | ISub | IMul | IDiv | ICmp CmpOp
           | FAdd | FSub | FMul | FDiv | FCmp CmpOp | FPow
           | BAnd | BOr | BShL | BShR | IRem | BXor
             deriving (Show, Eq, Generic)

data UnOp = Exp | Exp2
          | Log | Log2 | Log10 | Log1p
          | Sin | Cos | Tan | Sqrt
          | Floor | Ceil | Round
          | LGamma | Erf | Erfc
          | FNeg | BNot
            deriving (Show, Eq, Generic)

data CmpOp = Less | Greater | Equal | LessEqual | GreaterEqual
             deriving (Show, Eq, Generic)

data Direction = Fwd | Rev  deriving (Show, Eq, Generic)
type ForAnn = Direction

data RWS = Reader | Writer | State  deriving (Show, Eq, Ord, Generic)

data Arrow =
   PlainArrow
 | ImplicitArrow
 | ClassArrow
 | LinArrow
   deriving (Show, Eq, Ord, Generic)

plainArrows :: [(Arrow, a)] -> [a]
plainArrows = map snd . filter (\(arr, _) -> arr == PlainArrow)

instance Pretty Arrow where
  pretty arr = case arr of
    PlainArrow     -> "->"
    LinArrow       -> "--o"
    ImplicitArrow  -> "?->"
    ClassArrow     -> "?=>"

data LetAnn =
  -- Binding with no additional information
    PlainLet
  -- Binding explicitly tagged "do not inline"
  | NoInlineLet
  -- Bound expression is pure, and the binding's occurrences are summarized by
  -- the UsageInfo
  | OccInfoPure UsageInfo
  -- Bound expression is impure, and the binding's occurrences are summarized by
  -- the UsageInfo.  For now, the inliner does not distinguish different effects,
  -- so no additional information on effects is needed.
  | OccInfoImpure UsageInfo
  deriving (Show, Eq, Generic)

-- === Primitive scalar values and base types ===

-- TODO: we could consider using some mmap-able instead of ByteString
data PtrSnapshot = ByteArray BS.ByteString
                 | PtrArray [PtrLitVal]
                   deriving (Show, Eq, Ord, Generic)

data PtrLitVal = PtrLitVal (Ptr ())
               | PtrSnapshot PtrSnapshot
               | NullPtr
                 deriving (Show, Eq, Ord, Generic)

type PtrStoreRep = Maybe PtrSnapshot
instance Store PtrSnapshot where
instance Store PtrLitVal where
  size = SI.VarSize \case
    PtrSnapshot p -> SI.getSize (Just p  :: PtrStoreRep)
    NullPtr       -> SI.getSize (Nothing :: PtrStoreRep)
    PtrLitVal p   -> error $ "can't serialize pointer literal: " ++ show p
  peek = do
    peek >>= \case
      Just p  -> return $ PtrSnapshot p
      Nothing -> return $ NullPtr
  poke (PtrSnapshot p) = poke (Just p  :: PtrStoreRep)
  poke (NullPtr)       = poke (Nothing :: PtrStoreRep)
  poke (PtrLitVal _)   = error "can't serialize pointer literals"

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
            | PtrLit PtrType PtrLitVal
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
type AddressSpace = Device
type PtrType = (AddressSpace, BaseType)

-- TODO: give this a different name, because it could easily get confused with
-- Foreign.Storable.SizeOf which can have the same type!
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

emptyLit :: BaseType -> LitVal
emptyLit = \case
  Scalar b -> case b of
    Int64Type   -> Int64Lit 0
    Int32Type   -> Int32Lit 0
    Word8Type   -> Word8Lit 0
    Word32Type  -> Word32Lit 0
    Word64Type  -> Word64Lit 0
    Float64Type -> Float64Lit 0
    Float32Type -> Float32Lit 0
  PtrType t -> PtrLit t NullPtr
  Vector _ _ -> error "not implemented"

-- === Typeclass instances ===

instance Store Arrow
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

instance Store a => Store (PrimCon r a)
instance Store a => Store (PrimTC  r a)
instance Store a => Store (PrimOp    a)
instance Store a => Store (MemOp     a)
instance Store a => Store (VectorOp  a)
instance Store a => Store (MiscOp    a)
instance Store a => Store (RecordOp a)

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

instance Hashable a => Hashable (PrimCon r a)
instance Hashable a => Hashable (PrimTC  r a)
instance Hashable a => Hashable (PrimOp    a)
instance Hashable a => Hashable (MemOp     a)
instance Hashable a => Hashable (VectorOp  a)
instance Hashable a => Hashable (MiscOp    a)
instance Hashable a => Hashable (RecordOp a)
