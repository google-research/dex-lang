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

import Name
import qualified Data.ByteString       as BS
import Control.Monad
import Data.Int
import Data.Word
import Data.Hashable
import Data.Store (Store (..))
import qualified Data.Store.Internal as SI
import Foreign.Ptr

import GHC.Generics (Generic (..))

import Occurrence
import Util (zipErr)
import Types.OpNames (UnOp (..), BinOp (..), CmpOp (..), Projection (..))

type SourceName = String

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

data WithExpl (b::B) (n::S) (l::S) =
  WithExpl { getExpl :: Explicitness , withoutExpl :: b n l }
  deriving (Show, Generic)

unzipExpls :: Nest (WithExpl b) n l -> ([Explicitness], Nest b n l)
unzipExpls Empty = ([], Empty)
unzipExpls (Nest (WithExpl expl b) rest) = (expl:expls, Nest b bs)
  where (expls, bs) = unzipExpls rest

zipExpls :: [Explicitness] -> Nest b n l -> Nest (WithExpl b) n l
zipExpls [] Empty = Empty
zipExpls (expl:expls) (Nest b bs) = Nest (WithExpl expl b) (zipExpls expls bs)
zipExpls _ _ = error "zip error"

addExpls :: Explicitness -> Nest b n l -> Nest (WithExpl b) n l
addExpls expl bs = fmapNest (\b -> WithExpl expl b) bs

data RequiredMethodAccess = Full | Partial Int deriving (Show, Eq, Ord, Generic)

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

instance Store (b n l) => Store (WithExpl b n l)

instance (Color c, BindsOneName b c) => BindsOneName (WithExpl b) c where
  binderName (WithExpl _ b) = binderName b
  asNameBinder (WithExpl _ b) = asNameBinder b

instance (Color c, BindsAtMostOneName b c) => BindsAtMostOneName (WithExpl b) c where
  WithExpl _ b @> x = b @> x
  {-# INLINE (@>) #-}

instance AlphaEqB b => AlphaEqB (WithExpl b) where
  withAlphaEqB (WithExpl a1 b1) (WithExpl a2 b2) cont = do
    unless (a1 == a2) zipErr
    withAlphaEqB b1 b2 cont

instance AlphaHashableB b => AlphaHashableB (WithExpl b) where
  hashWithSaltB env salt (WithExpl expl b) = do
    let h = hashWithSalt salt expl
    hashWithSaltB env h b

instance BindsNames b => ProvesExt  (WithExpl b) where
instance BindsNames b => BindsNames (WithExpl b) where
  toScopeFrag (WithExpl _ b) = toScopeFrag b

instance (SinkableB b) => SinkableB (WithExpl b) where
  sinkingProofB fresh (WithExpl a b) cont =
    sinkingProofB fresh b \fresh' b' ->
      cont fresh' (WithExpl a b')

instance (BindsNames b, RenameB b) => RenameB (WithExpl b) where
  renameB env (WithExpl a b) cont =
      renameB env b \env' b' ->
        cont env' $ WithExpl a b'

instance HoistableB b => HoistableB (WithExpl b) where
  freeVarsB (WithExpl _ b) = freeVarsB b
