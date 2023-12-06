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
import Occurrence
import Types.OpNames (UnOp (..), BinOp (..), CmpOp (..), Projection (..))
import Name

newtype SourceName = MkSourceName String  deriving (Show, Eq, Ord, Generic)

newtype AlwaysEqual a = AlwaysEqual a
        deriving (Show, Generic, Functor, Foldable, Traversable, Hashable, Store)
instance Eq (AlwaysEqual a) where
  _ == _ = True

data Direction = Fwd | Rev  deriving (Show, Eq, Generic)
type ForAnn = Direction

data RWS = Reader | Writer | State  deriving (Show, Eq, Ord, Generic)

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

instance HasNameHint SourceName where
  getNameHint (MkSourceName v) = getNameHint v

instance Pretty SourceName where
  pretty (MkSourceName v) = pretty v

instance IsString SourceName where
  fromString v = MkSourceName v

instance Store SourceName
instance Store RequiredMethodAccess
instance Store LetAnn
instance Store RWS
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
instance Hashable RWS
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
  pretty ExplicitApp = "->"
  pretty ImplicitApp = "->>"

instance Pretty RWS where
  pretty eff = case eff of
    Reader -> "Read"
    Writer -> "Accum"
    State  -> "State"

instance Pretty LetAnn where
  pretty ann = case ann of
    PlainLet        -> ""
    InlineLet       -> "%inline"
    NoInlineLet     -> "%noinline"
    LinearLet       -> "%linear"
    OccInfoPure   u -> pretty u <> hardline
    OccInfoImpure u -> pretty u <> ", impure" <> hardline

instance PrettyPrec Direction where
  prettyPrec d = atPrec ArgPrec $ case d of
    Fwd -> "fwd"
    Rev -> "rev"

printDouble :: Double -> Doc ann
printDouble x = pretty (double2Float x)

printFloat :: Float -> Doc ann
printFloat x = pretty $ reverse $ dropWhile (=='0') $ reverse $
  showFFloat (Just 6) x ""

instance Pretty LitVal where pretty = prettyFromPrettyPrec
instance PrettyPrec LitVal where
  prettyPrec = \case
    Int64Lit   x -> atPrec ArgPrec $ p x
    Int32Lit   x -> atPrec ArgPrec $ p x
    Float64Lit x -> atPrec ArgPrec $ printDouble x
    Float32Lit x -> atPrec ArgPrec $ printFloat  x
    Word8Lit   x -> atPrec ArgPrec $ p $ show $ toEnum @Char $ fromIntegral x
    Word32Lit  x -> atPrec ArgPrec $ p $ "0x" ++ showHex x ""
    Word64Lit  x -> atPrec ArgPrec $ p $ "0x" ++ showHex x ""
    PtrLit ty (PtrLitVal x) -> atPrec ArgPrec $ "Ptr" <+> p ty <+> p (show x)
    PtrLit _ NullPtr -> atPrec ArgPrec $ "NullPtr"
    PtrLit _ (PtrSnapshot _) -> atPrec ArgPrec "<ptr snapshot>"
    where p :: Pretty a => a -> Doc ann
          p = pretty

instance Pretty Device where pretty = fromString . show

instance Pretty BaseType where pretty = prettyFromPrettyPrec
instance PrettyPrec BaseType where
  prettyPrec b = case b of
    Scalar sb -> prettyPrec sb
    Vector shape sb -> atPrec ArgPrec $ encloseSep "<" ">" "x" $ (pretty <$> shape) ++ [pretty sb]
    PtrType ty -> atPrec AppPrec $ "Ptr" <+> pretty ty

instance Pretty ScalarBaseType where pretty = prettyFromPrettyPrec
instance PrettyPrec ScalarBaseType where
  prettyPrec sb = atPrec ArgPrec $ case sb of
    Int64Type   -> "Int64"
    Int32Type   -> "Int32"
    Float64Type -> "Float64"
    Float32Type -> "Float32"
    Word8Type   -> "Word8"
    Word32Type  -> "Word32"
    Word64Type  -> "Word64"

instance Pretty Explicitness where
  pretty expl = pretty (show expl)
