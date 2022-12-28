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
import Occurrence
import IRVariants

data PrimTC (r::IR) (e:: *) where
  BaseType         :: BaseType       -> PrimTC r e
  ProdType         :: [e]            -> PrimTC r e
  SumType          :: [e]            -> PrimTC r e
  Nat              ::                   PrimTC r e
  Fin              :: e              -> PrimTC r e
  RefType          :: (Maybe e) -> e -> PrimTC r e
  TypeKind         ::                   PrimTC r e
  EffectRowKind    ::                   PrimTC r e
  LabeledRowKindTC ::                   PrimTC r e
  LabelType        ::                   PrimTC r e
  deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

traversePrimTC :: Applicative f => (e -> f e') -> PrimTC r e -> f (PrimTC r e')
traversePrimTC = inline traverse
{-# INLINABLE traversePrimTC #-}

data PrimCon (r::IR) (e:: *) where
  Lit          :: LitVal            -> PrimCon r e
  ProdCon      :: [e]               -> PrimCon r e
  SumCon       :: [e] -> Int -> e   -> PrimCon r e -- type, tag, payload
  SumAsProd    :: [e] -> e   -> [e] -> PrimCon r e -- type, tag, payload
  LabelCon     :: String            -> PrimCon r e
  Newtype      :: e -> e            -> PrimCon r e      -- type, payload
  -- Misc hacks
  -- Dict type, method. Used in prelude for `run_accum`.
  ExplicitDict :: e -> e            -> PrimCon r e
  -- Only used during type inference
  DictHole     :: AlwaysEqual SrcPosCtx -> e -> PrimCon r e
        deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

data MemOp e =
   IOAlloc BaseType e
 | IOFree e
 | PtrOffset e e
 | PtrLoad e
 | PtrStore e e
   deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

data RecordVariantOp e =
 -- Concatenate two records.
   RecordCons e e
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
 -- type, label, how deeply shadowed, payload
 | VariantMake e Label Int e
 -- Ask which constructor was used, as its Word8 index
 -- Converts sum types returned by primitives to variant-types that
 -- can be scrutinized in the surface language.
 | SumToVariant e
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
 -- Effects
 | ThrowError e                 -- (1) Hard error (parameterized by result type)
 | ThrowException e             -- (1) Catchable exceptions (unlike `ThrowError`)
 -- Tag of a sum type
 | SumTag e
 -- Create an enum (payload-free ADT) from a Word8
 | ToEnum e e
 -- stdout-like output stream
 | OutputStream
   deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

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

data EffectP (name::V) (n::S) = RWSEffect RWS (Maybe (name AtomNameC n))
                              | ExceptionEffect
                              | IOEffect
                              | UserEffect (name EffectNameC n)
                              | InitEffect
                                deriving (Generic)

deriving instance ShowV name => Show (EffectP name n)
deriving instance EqV name => Eq (EffectP name n)
deriving instance OrdV name => Ord (EffectP name n)

data EffectRowP (name::V) (n::S) =
  EffectRow (S.Set (EffectP name n)) (Maybe (name AtomNameC n))
  deriving (Generic)

deriving instance ShowV name => Show (EffectRowP name n)
deriving instance EqV name => Eq (EffectRowP name n)
deriving instance OrdV name => Ord (EffectRowP name n)

pattern Pure :: OrdV name => EffectRowP name n
pattern Pure <- ((\(EffectRow effs t) -> (S.null effs, t)) -> (True, Nothing))
  where Pure = EffectRow mempty Nothing

pattern OneEffect :: OrdV name => EffectP name n -> EffectRowP name n
pattern OneEffect eff <- ((\(EffectRow effs t) -> (S.toList effs, t)) -> ([eff], Nothing))
  where OneEffect eff = EffectRow (S.singleton eff) Nothing

instance OrdV name => Semigroup (EffectRowP name n) where
  EffectRow effs t <> EffectRow effs' t' =
    EffectRow (S.union effs effs') newTail
    where
      newTail = case (t, t') of
        (Nothing, effTail) -> effTail
        (effTail, Nothing) -> effTail
        _ | t == t' -> t
          | otherwise -> error "Can't combine effect rows with mismatched tails"

instance OrdV name => Monoid (EffectRowP name n) where
  mempty = EffectRow mempty Nothing

extendEffRow :: OrdV name => S.Set (EffectP name n) -> EffectRowP name n -> EffectRowP name n
extendEffRow effs (EffectRow effs' t) = EffectRow (effs <> effs') t
{-# INLINE extendEffRow #-}

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

-- === Typeclass instances ===

instance GenericE (EffectP name) where
  type RepE (EffectP name) =
    EitherE4 (PairE (LiftE RWS) (MaybeE (name AtomNameC)))
             (LiftE (Either () ()))
             (name EffectNameC)
             UnitE
  fromE = \case
    RWSEffect rws name -> Case0 (PairE (LiftE rws) $ toMaybeE name)
    ExceptionEffect    -> Case1 (LiftE (Left  ()))
    IOEffect           -> Case1 (LiftE (Right ()))
    UserEffect name    -> Case2 name
    InitEffect         -> Case3 UnitE
  {-# INLINE fromE #-}
  toE = \case
    Case0 (PairE (LiftE rws) name) -> RWSEffect rws $ fromMaybeE name
    Case1 (LiftE (Left  ())) -> ExceptionEffect
    Case1 (LiftE (Right ())) -> IOEffect
    Case2 name -> UserEffect name
    Case3 UnitE -> InitEffect
    _ -> error "unreachable"
  {-# INLINE toE #-}

instance SinkableE      (EffectP Name)
instance HoistableE     (EffectP Name)
instance AlphaEqE       (EffectP Name)
instance AlphaHashableE (EffectP Name)
instance RenameE        (EffectP Name)

instance OrdV name => GenericE (EffectRowP name) where
  type RepE (EffectRowP name) = PairE (ListE (EffectP name)) (MaybeE (name AtomNameC))
  fromE (EffectRow effs ext) = ListE (S.toList effs) `PairE` ext'
    where ext' = case ext of Just v  -> JustE v
                             Nothing -> NothingE
  {-# INLINE fromE #-}
  toE (ListE effs `PairE` ext) = EffectRow (S.fromList effs) ext'
    where ext' = case ext of JustE v  -> Just v
                             NothingE -> Nothing
                             _ -> error "impossible"
  {-# INLINE toE #-}

instance SinkableE         (EffectRowP Name)
instance HoistableE        (EffectRowP Name)
instance RenameE           (EffectRowP Name)
instance AlphaEqE          (EffectRowP Name)
instance AlphaHashableE    (EffectRowP Name)

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

instance Store (EffectRowP Name n)
instance Store (EffectP    Name n)

instance Store a => Store (PrimCon r a)
instance Store a => Store (PrimTC  r a)
instance Store a => Store (PrimOp    a)
instance Store a => Store (MemOp     a)
instance Store a => Store (VectorOp  a)
instance Store a => Store (MiscOp    a)
instance Store a => Store (RecordVariantOp a)

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
instance Hashable a => Hashable (RecordVariantOp a)
