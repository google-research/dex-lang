-- (Copyright 2023 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module QueryTypePure where

import Types.Primitives
import Types.Simple
import Types.Complicated
import Types.Top2
import Name

class HasType (e::E) where
  getType :: e n -> Type n

-- === querying types implementation ===

litType :: LitVal -> BaseType
litType v = case v of
  Int64Lit   _ -> Scalar Int64Type
  Int32Lit   _ -> Scalar Int32Type
  Word8Lit   _ -> Scalar Word8Type
  Word32Lit  _ -> Scalar Word32Type
  Word64Lit  _ -> Scalar Word64Type
  Float64Lit _ -> Scalar Float64Type
  Float32Lit _ -> Scalar Float32Type
  PtrLit ty _  -> PtrType ty

typeBinOp :: BinOp -> BaseType -> BaseType
typeBinOp binop xTy = case binop of
  IAdd   -> xTy;  ISub   -> xTy
  IMul   -> xTy;  IDiv   -> xTy
  IRem   -> xTy;
  ICmp _ -> Scalar Word8Type
  FAdd   -> xTy;  FSub   -> xTy
  FMul   -> xTy;  FDiv   -> xTy;
  FPow   -> xTy
  FCmp _ -> Scalar Word8Type
  BAnd   -> xTy;  BOr    -> xTy
  BXor   -> xTy
  BShL   -> xTy;  BShR   -> xTy

typeUnOp :: UnOp -> BaseType -> BaseType
typeUnOp = const id  -- All unary ops preserve the type of the input

getKind :: Type n -> Kind
getKind = undefined
-- getKind = \case
--   StuckTy k _ -> k
--   TyCon con -> case con of
--     BaseType _     -> TypeKind
--     ProdType _     -> TypeKind
--     SumType  _     -> TypeKind
--     TabPi _        -> TypeKind
--     DepPairTy _    -> TypeKind
--     NewtypeTyCon _ -> TypeKind
--     RefType _  -> RefKind
--     Pi _       -> FunKind
--     DictTy _   -> DictKind
--     Kind _     -> OtherKind

instance HasType Atom where
  getType = undefined
  -- getType = \case
  --   Stuck t _ -> t
  --   Con e -> getType e

instance HasType DictCon where
  getType = undefined
  -- getType = \case
  --   InstanceDict t _ _ -> t
  --   IxFin n -> toType $ IxDictType (FinTy n)

instance HasType NewtypeTyCon where
  getType _ = undefined -- TyCon $ Kind TypeKind

getNewtypeType :: NewtypeCon n -> CType n
getNewtypeType con = undefined
-- getNewtypeType con = case con of
--   NatCon              -> TyCon $ NewtypeTyCon Nat
--   FinCon n            -> TyCon $ NewtypeTyCon $ Fin n
--   UserADTData sn d xs -> TyCon $ NewtypeTyCon $ UserADTType sn d xs

-- instance HasType Con where
--   getType = undefined
  -- getType = \case
    -- Lit l          -> toType $ BaseType $ litType l
    -- ProdCon xs     -> toType $ ProdType $ map getType xs
    -- SumCon tys _ _ -> toType $ SumType tys
    -- Lam (CoreLamExpr piTy _) -> toType $ Pi piTy
    -- DepPair _ _ ty -> toType $ DepPairTy ty
    -- DictConAtom d -> getType d
    -- NewtypeCon con _ -> getNewtypeType con
    -- TyConAtom k -> TyCon $ Kind $ getKind $ TyCon k

getSuperclassType :: RNest CBinder n l -> Nest CBinder l l' -> Int -> CType n
getSuperclassType _ Empty = error "bad index"
getSuperclassType bsAbove (Nest b@(_:>t) bs) = \case
  0 -> ignoreHoistFailure $ hoist bsAbove t
  i -> getSuperclassType (RNest bsAbove b) bs (i-1)

instance HasType Expr where
  getType expr = undefined
  -- getType expr = case expr of
    -- App (EffTy _ ty) _ _ -> ty
    -- TopApp (EffTy _ ty) _ _ -> ty
    -- TabApp t _ _ -> t
    -- Atom x   -> getType x
    -- Block (EffTy _ ty) _ -> ty
    -- TabCon ty _ -> ty
    -- PrimOp ty _ -> ty
    -- Case _ _ (EffTy _ resultTy) -> resultTy
    -- ApplyMethod (EffTy _ t) _ _ _ -> t
    -- Project t _ _ -> t
    -- Unwrap t _ -> t
    -- Hof  (TypedHof (EffTy _ ty) _) -> ty

-- instance HasType MemOp where
--   getType = \case
--     IOAlloc _ -> PtrTy (CPU, Scalar Word8Type)
--     IOFree _ -> UnitTy
--     PtrOffset arr _ -> getType arr
--     PtrLoad ptr -> do
--       let PtrTy (_, t) = getType ptr
--       toType $ BaseType t
--     PtrStore _ _ -> UnitTy

-- === Complicated IR ===

class HasCType (e::E) where
  getCType :: e n -> CType n

instance HasCType CExpr where
  getCType = \case
    CBlock ty _ -> ty
    CVar   _ ty -> ty
    CLit   l    -> CTyCon $ CBaseType $ litType l
    -- CPrimOp (CType n) (PrimOp (CExpr n))
    -- CTyCon  (CTyCon n)
    -- Lam         (CoreLamExpr n)
    -- NewtypeCon  (NewtypeCon n) (CExpr n)
    -- Dict        (DictCon n)

