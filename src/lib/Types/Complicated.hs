-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StrictData #-}

module Types.Complicated (module Types.Complicated) where

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

import Types.Source (HasSourceName (..))
import Types.Primitives

data CExpr (n::S) =
   CBlock  (CType n) (CBlock n)
 | CVar    (Name n) (CType n)
 | CLit    LitVal
 | CPrimOp (CType n) (PrimOp (CExpr n))
 | CTyCon  (CTyCon n)
 | Lam         (CoreLamExpr n)
 | NewtypeCon  (NewtypeCon n) (CExpr n)
 | Dict        (DictCon n)
   deriving (Show, Generic)

data CTyCon (n::S) =
   CBaseType BaseType
 | CProdType [CType n]
 | CSumType  [CType n]
 | CRefType  (CType n)
 | DictTy       (DictType n)
 | Pi           (CorePiType  n)
 | NewtypeTyCon (NewtypeTyCon n)
 | CTabPi       (CTabPiType   n)
 | CDepPairTy   (CDepPairType n)
 | Kind         Kind
   deriving (Show, Generic)

type CType = CExpr

type CBinder = BinderP CType :: B

data CDecl (n::S) (l::S) = CLet (NameBinder n l) (CExpr n) deriving (Show, Generic)
type CBlock = Abs (Nest CDecl) CExpr

data CorePiType (n::S) = CorePiType AppExplicitness [Explicitness] (Abs (Nest CBinder) CType n)
     deriving (Show, Generic)

type IxDict = CExpr
data CTabPiType (n::S) = CTabPiType (IxDict n) (Abs CBinder CType n)
     deriving (Show, Generic)

data CDepPairType (n::S) = CDepPairType DepPairExplicitness (Abs CBinder CType n)
     deriving (Show, Generic)

data CoreLamExpr (n::S) = CoreLamExpr (CorePiType n) (Abs (Nest CBinder) CExpr n)
     deriving (Show, Generic)

data Kind = DataKind | RefKind | TypeKind | FunKind | DictKind | OtherKind
     deriving (Show, Generic, Eq, Ord)
instance Store    Kind
instance Hashable Kind

type ClassName = Name
data DictType (n::S) =
   DictType SourceName (ClassName n) [CExpr n]
 | IxDictType   (CType n)
   deriving (Show, Generic)

type InstanceName = Name
data DictCon (n::S) =
   InstanceDict (CType n) (InstanceName n) [CExpr n]
 | IxFin        (CExpr n)
   deriving (Show, Generic)

-- Describes how to lift the "shallow" representation type to the newtype.
data NewtypeCon (n::S) =
   UserADTData SourceName (TyConName n) (TyConParams n) -- source name is for the type
 | NatCon
 | FinCon (CExpr n)
   deriving (Show, Generic)

type TyConName = Name
data NewtypeTyCon (n::S) =
   Nat
 | Fin (CExpr n)
 | UserADTType SourceName (TyConName n) (TyConParams n)
   deriving (Show, Generic)

-- We track the explicitness information because we need it for the equality
-- check since we skip equality checking on dicts.
data TyConParams n = TyConParams [Explicitness] [CExpr n]
     deriving (Show, Generic)

-- === top-level definitions ===

data ClassDef (n::S) where
  ClassDef
    :: SourceName            -- name of class
    -> Maybe BuiltinClassName
    -> [SourceName]          -- method source names
    -> [Maybe SourceName]    -- parameter source names
    -> [Explicitness]        -- parameter info
    -> Nest CBinder n1 n2    -- parameters
    ->   Nest CBinder n2 n3  -- superclasses
    ->   [CorePiType n3]     -- method types
    -> ClassDef n1

data BuiltinClassName = Ix  deriving (Show, Generic, Eq)
instance Hashable BuiltinClassName
instance Store    BuiltinClassName

data InstanceDef (n::S) where
  InstanceDef
    :: ClassName n1
    -> [Explicitness]        -- parameter info
    -> Nest CBinder n1 n2    -- parameters (types and dictionaries)
    ->   [CExpr n2]          -- class parameters
    ->   [CExpr n2]          -- superclasses dicts
    ->   [CExpr n2]          -- method definitions
    -> InstanceDef n1

newtype DotMethods n = DotMethods (M.Map SourceName (Name n))
        deriving (Show, Generic, Monoid, Semigroup)

data TyConDef n = TyConDef
  SourceName -- just for pretty-printing
  [Explicitness]
  (Abs (Nest CBinder) DataConDefs n)
  deriving (Show, Generic)

data DataConDefs n =
   ADTCons [DataConDef n]
 | StructFields [(SourceName, CType n)]
   deriving (Show, Generic)

data DataConDef n =
  -- Name for pretty printing, constructor elements, representation type,
  -- list of projection indices that recovers elements from the representation.
  DataConDef SourceName (EmptyAbs (Nest CBinder) n) (CType n) [[Projection]]
  deriving (Show, Generic)

-- === type classes ===

instance GenericE CExpr where
  type RepE CExpr = UnitE
instance Pretty (CExpr n)
instance SinkableE      CExpr
instance HoistableE     CExpr
instance RenameE        CExpr
instance AlphaEqE       CExpr
instance AlphaHashableE CExpr
instance Store (CExpr n)

instance GenericE DictType where
  type RepE DictType = UnitE
instance Pretty (DictType n)
instance SinkableE      DictType
instance HoistableE     DictType
instance RenameE        DictType
instance AlphaEqE       DictType
instance AlphaHashableE DictType
instance Store (DictType n)

instance GenericE CDepPairType where
  type RepE CDepPairType = UnitE
instance Pretty (CDepPairType n)
instance SinkableE      CDepPairType
instance HoistableE     CDepPairType
instance RenameE        CDepPairType
instance AlphaEqE       CDepPairType
instance AlphaHashableE CDepPairType
instance Store (CDepPairType n)

instance GenericE CTabPiType where
  type RepE CTabPiType = UnitE
instance Pretty (CTabPiType n)
instance SinkableE      CTabPiType
instance HoistableE     CTabPiType
instance RenameE        CTabPiType
instance AlphaEqE       CTabPiType
instance AlphaHashableE CTabPiType
instance Store (CTabPiType n)

instance GenericE NewtypeTyCon where
  type RepE NewtypeTyCon = UnitE
instance Pretty (NewtypeTyCon n)
instance SinkableE      NewtypeTyCon
instance HoistableE     NewtypeTyCon
instance RenameE        NewtypeTyCon
instance AlphaEqE       NewtypeTyCon
instance AlphaHashableE NewtypeTyCon
instance Store (NewtypeTyCon n)

instance GenericE CTyCon where
  type RepE CTyCon = UnitE
instance Pretty (CTyCon n)
instance SinkableE      CTyCon
instance HoistableE     CTyCon
instance RenameE        CTyCon
instance AlphaEqE       CTyCon
instance AlphaHashableE CTyCon
instance Store (CTyCon n)

instance GenericE DictCon where
  type RepE DictCon = UnitE
instance Pretty (DictCon n)
instance SinkableE      DictCon
instance HoistableE     DictCon
instance RenameE        DictCon
instance AlphaEqE       DictCon
instance AlphaHashableE DictCon
instance Store (DictCon n)

instance GenericE TyConDef where
  type RepE TyConDef = UnitE
instance Pretty (TyConDef n)
instance SinkableE      TyConDef
instance HoistableE     TyConDef
instance RenameE        TyConDef
instance AlphaEqE       TyConDef
instance AlphaHashableE TyConDef
instance Store (TyConDef n)

instance GenericE DataConDef where
  type RepE DataConDef = UnitE
instance Pretty (DataConDef n)
instance SinkableE      DataConDef
instance HoistableE     DataConDef
instance RenameE        DataConDef
instance AlphaEqE       DataConDef
instance AlphaHashableE DataConDef
instance Store (DataConDef n)

instance GenericE DataConDefs where
  type RepE DataConDefs = UnitE
instance Pretty (DataConDefs n)
instance SinkableE      DataConDefs
instance HoistableE     DataConDefs
instance RenameE        DataConDefs
instance AlphaEqE       DataConDefs
instance AlphaHashableE DataConDefs
instance Store (DataConDefs n)

instance GenericE NewtypeCon where
  type RepE NewtypeCon = UnitE
instance Pretty (NewtypeCon n)
instance SinkableE      NewtypeCon
instance HoistableE     NewtypeCon
instance RenameE        NewtypeCon
instance AlphaEqE       NewtypeCon
instance AlphaHashableE NewtypeCon
instance Store (NewtypeCon n)

instance GenericE CoreLamExpr where
  type RepE CoreLamExpr = UnitE
instance Pretty (CoreLamExpr n)
instance SinkableE      CoreLamExpr
instance HoistableE     CoreLamExpr
instance RenameE        CoreLamExpr
instance AlphaEqE       CoreLamExpr
instance AlphaHashableE CoreLamExpr
instance Store (CoreLamExpr n)

instance GenericE TyConParams where
  type RepE TyConParams = UnitE
instance Pretty (TyConParams n)
instance SinkableE      TyConParams
instance HoistableE     TyConParams
instance RenameE        TyConParams
instance AlphaEqE       TyConParams
instance AlphaHashableE TyConParams
instance Store (TyConParams n)

instance GenericE CorePiType where
  type RepE CorePiType = UnitE
instance Pretty (CorePiType n)
instance SinkableE      CorePiType
instance HoistableE     CorePiType
instance RenameE        CorePiType
instance AlphaEqE       CorePiType
instance AlphaHashableE CorePiType
instance Store (CorePiType n)

instance GenericE DotMethods where
  type RepE DotMethods = UnitE
instance Pretty (DotMethods n)
instance SinkableE      DotMethods
instance HoistableE     DotMethods
instance RenameE        DotMethods
instance AlphaEqE       DotMethods
instance AlphaHashableE DotMethods
instance Store (DotMethods n)

instance GenericE ClassDef where
  type RepE ClassDef =
    LiftE (SourceName, Maybe BuiltinClassName, [SourceName], [Maybe SourceName], [Explicitness])
     `PairE` Abs (Nest CBinder) (Abs (Nest CBinder) (ListE CorePiType))
  fromE (ClassDef name builtin names paramNames roleExpls b scs tys) =
    LiftE (name, builtin, names, paramNames, roleExpls) `PairE` Abs b (Abs scs (ListE tys))
  {-# INLINE fromE #-}
  toE (LiftE (name, builtin, names, paramNames, roleExpls) `PairE` Abs b (Abs scs (ListE tys))) =
    ClassDef name builtin names paramNames roleExpls b scs tys
  {-# INLINE toE #-}
instance Pretty (ClassDef n)
instance SinkableE ClassDef
instance HoistableE  ClassDef
instance AlphaEqE ClassDef
instance AlphaHashableE ClassDef
instance RenameE     ClassDef
deriving instance Show (ClassDef n)
deriving via WrapE ClassDef n instance Generic (ClassDef n)
instance Store (ClassDef n)
instance HasSourceName (ClassDef n) where
  getSourceName = \case ClassDef name _ _ _ _ _ _ _ -> name

instance GenericE InstanceDef where
  type RepE InstanceDef = UnitE
instance Pretty (InstanceDef n)
instance SinkableE      InstanceDef
instance HoistableE     InstanceDef
instance RenameE        InstanceDef
instance AlphaEqE       InstanceDef
instance AlphaHashableE InstanceDef
instance Store (InstanceDef n)
deriving instance Show (InstanceDef n)
deriving via WrapE InstanceDef n instance Generic (InstanceDef n)

instance GenericB CDecl where
  type RepB CDecl = BinderP CExpr
  fromB (CLet b expr) = b :> expr
  {-# INLINE fromB #-}
  toB   (b :> expr) = CLet b expr
  {-# INLINE toB #-}
instance Pretty (CDecl n l)
instance SinkableB      CDecl
instance HoistableB     CDecl
instance RenameB        CDecl
instance AlphaEqB       CDecl
instance AlphaHashableB CDecl
instance ProvesExt      CDecl
instance BindsNames     CDecl
instance Store (CDecl n l)
