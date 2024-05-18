
-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StrictData #-}

module Types.Simple (module Types.Simple) where

import Data.Word
import Data.Foldable (toList)
import Data.Hashable
import Data.String (fromString)
import Data.Text.Prettyprint.Doc
import Data.Text (Text, unsnoc, uncons)
import qualified Data.Map.Strict       as M

import GHC.Generics (Generic (..))
import Data.Store (Store (..))

import Name
import Util (Tree (..))
import PPrint

import Types.Primitives
import Types.Source (HasSourceName (..))
import Types.Imp

-- === SimpIR ===

data Expr (n::S) =
   Block  (Type n) (Block n)
 | TopApp (Type n) (TopFunName n) [Atom n]
 | Case   (Type n) (Atom n) [LamExpr n]
 | For    (Atom n) (LamExpr n)
 | While  (Expr n)
 | PrimOp (Type n) (PrimOp (Atom n))
   deriving (Show, Generic)

data Atom (n::S) =
   Var (Name n) (Type n)
 | Lit LitVal deriving (Show, Generic)

data Type (n::S) =
   BaseType BaseType
 | ProdType [Type n]
 | SumType  [Type n]
 | RefType  (Type n)
 | DepPairTy (DepPairType n)
 | TabPi     (TabPiType n)
   deriving (Show, Generic)

type TopFunName = Name
type Binder = BinderP Type :: B
data Decl (n::S) (l::S) = Let (NameBinder n l) (Expr n)
     deriving (Show, Generic)
type Block = Abs (Nest Decl) Expr

data TabPiType (n::S) = TabPiType (Atom n) (Abs Binder Type n) -- length, element type
     deriving (Show, Generic)

type DepPairType = Abs Binder Type
type LamExpr = Abs (Nest Binder) Expr :: E
type PiType = Abs (Nest Binder) Type :: E

-- === type classes ===

instance GenericE Expr where
  type RepE Expr = UnitE
instance Pretty (Expr n)
instance SinkableE      Expr
instance HoistableE     Expr
instance RenameE        Expr
instance AlphaEqE       Expr
instance AlphaHashableE Expr
instance Store (Expr n)

instance GenericE Atom where
  type RepE Atom = UnitE
instance Pretty (Atom n)
instance SinkableE      Atom
instance HoistableE     Atom
instance RenameE        Atom
instance AlphaEqE       Atom
instance AlphaHashableE Atom
instance Store (Atom n)

instance GenericE Type where
  type RepE Type = UnitE
instance Pretty (Type n)
instance SinkableE      Type
instance HoistableE     Type
instance RenameE        Type
instance AlphaEqE       Type
instance AlphaHashableE Type
instance Store (Type n)

instance GenericE TabPiType where
  type RepE TabPiType = UnitE
instance Pretty (TabPiType n)
instance SinkableE      TabPiType
instance HoistableE     TabPiType
instance RenameE        TabPiType
instance AlphaEqE       TabPiType
instance AlphaHashableE TabPiType
instance Store (TabPiType n)

instance GenericB Decl where
  type RepB Decl = BinderP Expr
  fromB (Let b expr) = b :> expr
  {-# INLINE fromB #-}
  toB   (b :> expr) = Let b expr
  {-# INLINE toB #-}
instance Pretty (Decl n l)
instance SinkableB      Decl
instance HoistableB     Decl
instance RenameB        Decl
instance AlphaEqB       Decl
instance AlphaHashableB Decl
instance ProvesExt      Decl
instance BindsNames     Decl
instance Store (Decl n l)
