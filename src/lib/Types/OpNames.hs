-- Copyright 2023 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

-- This module contains payload-free versions of the ops defined in Types.Core.
-- It uses the same constructor names so it should be imported qualified.

module Types.OpNames where

import IRVariants
import Data.Hashable
import GHC.Generics (Generic (..))
import Data.Store (Store (..))

import PPrint

data TC = ProdType | SumType | RefType | TypeKind | HeapType
data Con = ProdCon | SumCon Int | HeapVal

data BinOp =
   IAdd | ISub | IMul | IDiv | ICmp CmpOp | FAdd | FSub | FMul
 | FDiv | FCmp CmpOp | FPow | BAnd | BOr | BShL | BShR | IRem | BXor

data UnOp =
   Exp | Exp2 | Log | Log2 | Log10 | Log1p | Sin | Cos | Tan | Sqrt | Floor
 | Ceil | Round | LGamma | Erf | Erfc | FNeg | BNot

data CmpOp = Less | Greater | Equal | LessEqual | GreaterEqual

data MemOp = IOAlloc | IOFree | PtrOffset | PtrLoad | PtrStore

data MiscOp =
   Select | CastOp | BitcastOp | UnsafeCoerce | GarbageVal | Effects
 | ThrowError | ThrowException | Tag | SumTag | Create | ToEnum
 | OutputStream | ShowAny | ShowScalar

data VectorOp  = VectorBroadcast | VectorIota | VectorIdx | VectorSubref

data Hof  (r::IR) =
   While | RunReader | RunWriter | RunState | RunIO | RunInit
 | CatchException | Linearize | Transpose

data DAMOp = Seq | RememberDest | AllocDest | Place | Freeze

data RefOp = MAsk | MExtend | MGet | MPut | IndexRef | ProjRef Projection

data Projection =
   UnwrapNewtype -- TODO: add `HasCore r` constraint
 | ProjectProduct Int
   deriving (Show, Eq, Generic)

data UserEffectOp = Handle | Resume | Perform

deriving instance Generic BinOp
deriving instance Generic UnOp
deriving instance Generic CmpOp
deriving instance Generic TC
deriving instance Generic Con
deriving instance Generic MemOp
deriving instance Generic MiscOp
deriving instance Generic VectorOp
deriving instance Generic (Hof r)
deriving instance Generic DAMOp
deriving instance Generic RefOp
deriving instance Generic UserEffectOp

instance Hashable BinOp
instance Hashable UnOp
instance Hashable CmpOp
instance Hashable TC
instance Hashable Con
instance Hashable MemOp
instance Hashable MiscOp
instance Hashable VectorOp
instance Hashable (Hof r)
instance Hashable DAMOp
instance Hashable RefOp
instance Hashable UserEffectOp
instance Hashable Projection

instance Store BinOp
instance Store UnOp
instance Store CmpOp
instance Store TC
instance Store Con
instance Store MemOp
instance Store MiscOp
instance Store VectorOp
instance IRRep r => Store (Hof r)
instance Store DAMOp
instance Store RefOp
instance Store UserEffectOp
instance Store Projection

deriving instance Show BinOp
deriving instance Show UnOp
deriving instance Show CmpOp
deriving instance Show TC
deriving instance Show Con
deriving instance Show MemOp
deriving instance Show MiscOp
deriving instance Show VectorOp
deriving instance Show (Hof r)
deriving instance Show DAMOp
deriving instance Show RefOp
deriving instance Show UserEffectOp

deriving instance Eq BinOp
deriving instance Eq UnOp
deriving instance Eq CmpOp
deriving instance Eq TC
deriving instance Eq Con
deriving instance Eq MemOp
deriving instance Eq MiscOp
deriving instance Eq VectorOp
deriving instance Eq (Hof r)
deriving instance Eq DAMOp
deriving instance Eq RefOp
deriving instance Eq UserEffectOp

instance Pretty Projection where
  pretty = \case
    UnwrapNewtype -> "u"
    ProjectProduct i -> pretty i
