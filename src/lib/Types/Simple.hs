
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
import qualified Data.Map.Strict       as M

import GHC.Generics (Generic (..))
import Data.Store (Store (..))

import Name
import Util (Tree (..))
import PPrint

import Types.Primitives
import Types.Source (HasSourceName (..))

-- === SimpIR ===

data Expr (n::S) =
   Block  (Type n) (Block n)
 | TopApp (Type n) TopName [Atom n]
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

type TopFunName = TopName
type Binder = BinderP Type :: B
data Decl (n::S) (l::S) = Let (NameBinder n l) (Expr n)
     deriving (Show, Generic)
type Decls = Nest Decl
type Block = Abs (Nest Decl) Expr

data TabPiType (n::S) = TabPiType (Atom n) (Abs Binder Type n) -- length, element type
     deriving (Show, Generic)

type DepPairType = Abs Binder Type
type LamExpr = Abs (Nest Binder) Expr :: E
type PiType = Abs (Nest Binder) Type :: E

-- === type classes ===

instance GenericE Expr where
  type RepE Expr = EitherE6
  {- Block  -} (Type `PairE` Block)
  {- TopApp -} (Type `PairE` LiftE TopName `PairE` ListE Atom)
  {- Case   -} (Type `PairE` Atom          `PairE` ListE LamExpr)
  {- For    -} (Atom `PairE` LamExpr)
  {- While  -} (Expr)
  {- PrimOp -} (Type `PairE` ComposeE PrimOp Atom)
  fromE = \case
    Block  t b    -> Case0 $ t `PairE` b
    TopApp t f xs -> Case1 $ t `PairE` LiftE f `PairE` ListE xs
    Case   t x fs -> Case2 $ t `PairE` x `PairE` ListE fs
    For    n f    -> Case3 $ n `PairE` f
    While  e      -> Case4 e
    PrimOp t op   -> Case5 $ t `PairE` ComposeE op
  {-# INLINE fromE #-}

instance Pretty (Expr n) where
  pr = \case
    Block _ (Abs decls result) ->
      vcat (nestToList' pr decls ++ [pr result])
    TopApp _ _ _ -> undefined
    Case   _ _ _ -> undefined
    For    _ _ -> undefined
    While  _ -> undefined
    PrimOp _ op -> pr op

instance SinkableE      Expr
instance HoistableE     Expr
instance RenameE        Expr
instance AlphaEqE       Expr
instance AlphaHashableE Expr
instance Store (Expr n)

instance GenericE Atom where
  type RepE Atom = EitherE (LiftE LitVal) (Name `PairE` Type)

instance Pretty (Atom n) where
  pr = \case
    Var v _ -> pr v
    Lit l -> pr l

instance SinkableE      Atom
instance HoistableE     Atom
instance RenameE        Atom
instance AlphaEqE       Atom
instance AlphaHashableE Atom
instance Store (Atom n)

instance GenericE Type where
  type RepE Type = EitherE6
 {- BaseType  -} (LiftE BaseType)
 {- ProdType  -} (ListE Type)
 {- SumType   -} (ListE Type)
 {- RefType   -} (Type)
 {- DepPairTy -} (DepPairType)
 {- TabPi     -} (TabPiType)
  fromE = \case
    BaseType t  -> Case0 $ LiftE t
    ProdType ts -> Case1 $ ListE ts
    SumType ts  -> Case2 $ ListE ts
    RefType t   -> Case3 $ t
    DepPairTy p -> Case4 $ p
    TabPi t     -> Case5 $ t

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

instance Pretty (Decl n l) where
  pr (Let b expr) = hcat [pr b, " = ", pr expr]

instance SinkableB      Decl
instance HoistableB     Decl
instance RenameB        Decl
instance AlphaEqB       Decl
instance AlphaHashableB Decl
instance ProvesExt      Decl
instance BindsNames     Decl
instance Store (Decl n l)
