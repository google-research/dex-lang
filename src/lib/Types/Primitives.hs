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

module Types.Primitives (
  module Types.Primitives, UnOp (..), BinOp (..),
  CmpOp (..), Projection (..)) where

import qualified Data.ByteString       as BS
import Data.Int
import Data.String (IsString (..))
import Data.Word
import Data.Hashable
import Data.Store (Store (..))
import qualified Data.Store.Internal as SI
import Foreign.Ptr
import Numeric

import GHC.Float
import GHC.Generics (Generic (..))

import PPrint
-- import Occurrence
import Name

-- === Primitive ops ===

data BinOp =
   IAdd | ISub | IMul | IDiv | ICmp CmpOp | FAdd | FSub | FMul
 | FDiv | FCmp CmpOp | FPow | BAnd | BOr | BShL | BShR | IRem | BXor
 deriving (Show, Eq, Ord, Generic)
instance Hashable BinOp
instance Store    BinOp

data UnOp =
   Exp | Exp2 | Log | Log2 | Log10 | Log1p | Sin | Cos | Tan | Sqrt | Floor
 | Ceil | Round | LGamma | Erf | Erfc | FNeg | BNot
 deriving (Show, Eq, Ord, Generic)
instance Hashable UnOp
instance Store    UnOp

data CmpOp = Less | Greater | Equal | LessEqual | GreaterEqual
     deriving (Show, Eq, Ord, Generic)
instance Hashable CmpOp
instance Store    CmpOp

data Projection =
   UnwrapNewtype -- TODO: add `HasCore r` constraint
 | ProjectProduct Int
   deriving (Show, Eq, Ord, Generic)
instance Hashable Projection
instance Store    Projection

data PrimOp a =
   UnOp     UnOp   a
 | BinOp    BinOp a a
 | MemOp    (MemOp a)
 | VectorOp (VectorOp a)
 | MiscOp   (MiscOp a)
 | RefOp    a (RefOp a)
   deriving (Show, Eq, Ord, Generic, Functor, Foldable, Traversable)
instance Hashable a => Hashable (PrimOp a)
instance Store    a => Store    (PrimOp a)

data MemOp a =
   IOAlloc a
 | IOFree a
 | PtrOffset a a
 | PtrLoad a
 | PtrStore a a
   deriving (Show, Eq, Ord, Generic, Functor, Foldable, Traversable)
instance Hashable a => Hashable (MemOp a)
instance Store    a => Store    (MemOp a)

data MiscOp a =
   Select a a a        -- (3) predicate, val-if-true, val-if-false
 | CastOp a                              -- (2) See CheckType.hs for valid coercions.
 | BitcastOp a                -- (2) See CheckType.hs for valid coercions.
 | UnsafeCoerce a             -- type, then value. Assumes runtime representation is the same.
 | GarbageVal                          -- (TODO: redundant with NewRef)
 | NewRef
 | ThrowError
 -- Tag of a sum type
 | SumTag a
 -- Create an enum (payload-free ADT) from a Word8
 | ToEnum a
 -- printing
 | OutputStream
 | ShowAny a    -- implemented in Simplify
 | ShowScalar a -- Implemented in Imp. Result is a pair of an `IdxRepValTy`
                -- giving the logical size of the result and a fixed-size table,
                -- `Fin showStringBufferSize => Char`, assumed to have sufficient space.
   deriving (Show, Eq, Ord, Generic, Functor, Foldable, Traversable)
instance Hashable a => Hashable (MiscOp a)
instance Store    a => Store    (MiscOp a)

data VectorOp a =
   VectorBroadcast a
 | VectorIota
 | VectorIdx a a             -- table, base ix
 | VectorSubref a a          -- ref, base ix
   deriving (Show, Eq, Ord, Generic, Functor, Foldable, Traversable)
instance Hashable a => Hashable (VectorOp a)
instance Store    a => Store    (VectorOp a)

data RefOp a =
   MGet
 | MPut a
 | IndexRef a
 | ProjRef Projection
   deriving (Show, Eq, Ord, Generic, Functor, Foldable, Traversable)
instance Hashable a => Hashable (RefOp a)
instance Store    a => Store    (RefOp a)

-- === various things ===

type TopNameHint = String
type ModuleName = SourceName
data TopName = TopGenName TopNameHint Int
             | TopSourceName ModuleName SourceName
             deriving (Show, Eq, Ord, Generic)
instance Hashable TopName
instance Store    TopName

newtype SourceName = MkSourceName String  deriving (Show, Eq, Ord, Generic)

newtype AlwaysEqual a = AlwaysEqual a
        deriving (Show, Generic, Functor, Foldable, Traversable, Hashable, Store)
instance Eq (AlwaysEqual a) where
  _ == _ = True

data Direction = Fwd | Rev  deriving (Show, Eq, Generic)
type ForAnn = Direction

-- TODO: add optional argument
data InferenceMechanism = Unify | Synth RequiredMethodAccess deriving (Show, Eq, Ord, Generic)
data Explicitness =
    Explicit
  | Inferred (Maybe SourceName) InferenceMechanism  deriving (Show, Eq, Ord, Generic)
data AppExplicitness = ExplicitApp | ImplicitApp  deriving (Show, Generic, Eq)
data DepPairExplicitness = ExplicitDepPair | ImplicitDepPair  deriving (Show, Generic, Eq)

data RequiredMethodAccess = Full | Partial Int deriving (Show, Eq, Ord, Generic)

data LetAnn =
  -- Binding with no additional information
    PlainLet
  -- Binding explicitly tagged "inline immediately"
  | InlineLet
  -- Binding explicitly tagged "do not inline"
  | NoInlineLet
  | LinearLet
  -- Bound expression is pure, and the binding's occurrences are summarized by
  -- the UsageInfo
  -- | OccInfoPure UsageInfo
  -- Bound expression is impure, and the binding's occurrences are summarized by
  -- the UsageInfo.  For now, the inliner does not distinguish different effects,
  -- so no additional information on effects is needed.
  -- | OccInfoImpure UsageInfo
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

instance HasNameHint SourceName where
  getNameHint (MkSourceName v) = getNameHint v

instance Pretty SourceName where
  pr (MkSourceName v) = pr v

instance Pretty TopName where
  pr _ = undefined

instance IsString SourceName where
  fromString v = MkSourceName v

instance Store SourceName
instance Store RequiredMethodAccess
instance Store LetAnn
instance Store Direction
instance Store BaseType
instance Store LitVal
instance Store ScalarBaseType
instance Store Device
instance Store Explicitness
instance Store AppExplicitness
instance Store DepPairExplicitness
instance Store InferenceMechanism

instance Hashable SourceName
instance Hashable Direction
instance Hashable BaseType
instance Hashable PtrLitVal
instance Hashable PtrSnapshot
instance Hashable LitVal
instance Hashable ScalarBaseType
instance Hashable Device
instance Hashable LetAnn
instance Hashable Explicitness
instance Hashable AppExplicitness
instance Hashable DepPairExplicitness
instance Hashable InferenceMechanism
instance Hashable RequiredMethodAccess

-- === Pretty instances ===

instance Pretty AppExplicitness where
  pr ExplicitApp = "->"
  pr ImplicitApp = "->>"

instance Pretty LetAnn where
  pr ann = case ann of
    PlainLet        -> ""
    InlineLet       -> "%inline"
    NoInlineLet     -> "%noinline"
    LinearLet       -> "%linear"
    -- OccInfoPure   u -> pretty u <> hardline
    -- OccInfoImpure u -> pretty u <> ", impure" <> hardline

instance Pretty Direction where
  pr d = case d of
    Fwd -> "fwd"
    Rev -> "rev"

printDouble :: Double -> Doc
printDouble x = pr (double2Float x)

printFloat :: Float -> Doc
printFloat x = pr $ reverse $ dropWhile (=='0') $ reverse $
  showFFloat (Just 6) x ""

instance Pretty LitVal where
  pr = \case
    Int64Lit   x -> pr x
    Int32Lit   x -> pr x
    Float64Lit x -> printDouble x
    Float32Lit x -> printFloat  x
    Word8Lit   x -> pr $ show $ toEnum @Char $ fromIntegral x
    Word32Lit  x -> pr $ "0x" ++ showHex x ""
    Word64Lit  x -> pr $ "0x" ++ showHex x ""
    PtrLit ty (PtrLitVal x) -> app "Ptr" [pr ty, pr (show x)]
    PtrLit _ NullPtr -> "NullPtr"
    PtrLit _ (PtrSnapshot _) -> "<ptr snapshot>"

instance Pretty Device where
  pr = fromString . show

instance Pretty BaseType where
  pr b = case b of
    Scalar sb -> pr sb
    Vector _ _ -> undefined
    PtrType ty -> app "Ptr" [pr ty]

instance Pretty ScalarBaseType where
  pr sb = case sb of
    Int64Type   -> "Int64"
    Int32Type   -> "Int32"
    Float64Type -> "Float64"
    Float32Type -> "Float32"
    Word8Type   -> "Word8"
    Word32Type  -> "Word32"
    Word64Type  -> "Word64"

instance Pretty a => Pretty (PrimOp a) where
  pr = \case
    MemOp    op -> pr op
    VectorOp op -> pr op
    RefOp ref eff -> case eff of
      MGet        -> app "get" [pr ref]
      MPut x      -> app "(:=)" [pr ref, pr x]
      IndexRef i  -> app "(!)"  [pr ref, pr i]
      ProjRef i   -> app "proj_ref" [pr ref, pr i]
    UnOp  op x   -> undefined
    BinOp op x y -> undefined
    MiscOp op -> undefined

instance Pretty Projection where
  pr = \case
    UnwrapNewtype -> "u"
    ProjectProduct i -> pr i

instance Pretty a => Pretty (MemOp a) where
  pr = \case
    PtrOffset ptr idx -> app "(+>)" [pr idx]
    PtrLoad   ptr     -> app "load" [pr ptr]
    op -> undefined

instance Pretty a => Pretty (VectorOp a) where
  pr = \case
    VectorBroadcast v -> app "vbroadcast"  [pr v]
    VectorIota -> app "viota" []
    VectorIdx tbl i -> app "vslice" [pr tbl, pr i]
    VectorSubref ref i -> app "vrefslice" [pr ref, pr i]

instance Pretty Explicitness where
  pr expl = pr (show expl)
