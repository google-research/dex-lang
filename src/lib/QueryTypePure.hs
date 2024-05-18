-- (Copyright 2023 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module QueryTypePure where

import Types.Primitives
import Types.Simple
import Types.Complicated
import Types.Top
import Name

class HasType (e::E) where
  getType :: e n -> Type n

class HasEffects (e::E) where
  getEffects :: e n -> Effects n

getTyCon :: HasType e => e n -> TyCon n
getTyCon e = con where TyCon con = getType e

isPure :: HasEffects e => e n -> Bool
isPure e = case getEffects e of
  Pure      -> True
  Effectful -> False

-- === querying types implementation ===

instance HasType AtomBinding where
  getType = \case
    LetBound    (DeclBinding _ e)  -> getType e
    MiscBound   ty                 -> ty
    SolverBound (InfVarBound ty)   -> ty
    SolverBound (SkolemBound ty)   -> ty
    SolverBound (DictBound   ty)   -> ty
    NoinlineFun ty _               -> ty
    FFIFunBound piTy _ -> TyCon $ Pi piTy

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
getKind = \case
  StuckTy k _ -> k
  TyCon con -> case con of
    BaseType _     -> TypeKind
    ProdType _     -> TypeKind
    SumType  _     -> TypeKind
    TabPi _        -> TypeKind
    DepPairTy _    -> TypeKind
    NewtypeTyCon _ -> TypeKind
    RefType _  -> RefKind
    Pi _       -> FunKind
    DictTy _   -> DictKind
    Kind _     -> OtherKind

instance HasType AtomVar where
  getType (AtomVar _ ty) = ty
  {-# INLINE getType #-}

instance HasType Atom where
  getType = \case
    Stuck t _ -> t
    Con e -> getType e

instance HasType Dict where
  getType = \case
    StuckDict t _ -> t
    DictCon e -> getType e

instance HasType DictCon where
  getType = \case
    InstanceDict t _ _ -> t
    IxFin n -> toType $ IxDictType (FinTy n)
    IxRawFin _ -> toType $ IxDictType IdxRepTy

instance HasType NewtypeTyCon where
  getType _ = TyCon $ Kind TypeKind

getNewtypeType :: NewtypeCon n -> CType n
getNewtypeType con = case con of
  NatCon              -> TyCon $ NewtypeTyCon Nat
  FinCon n            -> TyCon $ NewtypeTyCon $ Fin n
  UserADTData sn d xs -> TyCon $ NewtypeTyCon $ UserADTType sn d xs

instance HasType Con where
  getType = \case
    Lit l          -> toType $ BaseType $ litType l
    ProdCon xs     -> toType $ ProdType $ map getType xs
    SumCon tys _ _ -> toType $ SumType tys
    Lam (CoreLamExpr piTy _) -> toType $ Pi piTy
    DepPair _ _ ty -> toType $ DepPairTy ty
    DictConAtom d -> getType d
    NewtypeCon con _ -> getNewtypeType con
    TyConAtom k -> TyCon $ Kind $ getKind $ TyCon k

getSuperclassType :: RNest CBinder n l -> Nest CBinder l l' -> Int -> CType n
getSuperclassType _ Empty = error "bad index"
getSuperclassType bsAbove (Nest b@(_:>t) bs) = \case
  0 -> ignoreHoistFailure $ hoist bsAbove t
  i -> getSuperclassType (RNest bsAbove b) bs (i-1)

instance HasType Expr where
  getType expr = case expr of
    App (EffTy _ ty) _ _ -> ty
    TopApp (EffTy _ ty) _ _ -> ty
    TabApp t _ _ -> t
    Atom x   -> getType x
    Block (EffTy _ ty) _ -> ty
    TabCon ty _ -> ty
    PrimOp ty _ -> ty
    Case _ _ (EffTy _ resultTy) -> resultTy
    ApplyMethod (EffTy _ t) _ _ _ -> t
    Project t _ _ -> t
    Unwrap t _ -> t
    Hof  (TypedHof (EffTy _ ty) _) -> ty

instance HasType RepVal where
  getType (RepVal ty _) = ty

getTypeBaseType :: HasType e => e n -> BaseType
getTypeBaseType e = case getType e of
  TyCon (BaseType b) -> b
  ty -> error $ "Expected a base type. Got: " ++ show ty

-- instance HasType MemOp where
--   getType = \case
--     IOAlloc _ -> PtrTy (CPU, Scalar Word8Type)
--     IOFree _ -> UnitTy
--     PtrOffset arr _ -> getType arr
--     PtrLoad ptr -> do
--       let PtrTy (_, t) = getType ptr
--       toType $ BaseType t
--     PtrStore _ _ -> UnitTy

rawStrType :: Type n
rawStrType = case newName "n" of
  Abs b v -> do
    let tabTy = rawFinTabType (toAtom $ AtomVar v IdxRepTy) CharRepTy
    TyCon $ DepPairTy $ DepPairType ExplicitDepPair (b:>IdxRepTy) tabTy

-- `n` argument is IdxRepVal, not Nat
rawFinTabType :: Atom n -> Type n -> Type n
rawFinTabType n eltTy = IxType IdxRepTy (DictCon (IxRawFin n)) ==> eltTy

tabIxType :: TabPiType n -> IxType n
tabIxType (TabPiType d (_:>t) _) = IxType t d

typesAsBinderNest
  :: (SinkableE e, HoistableE e)
  => [Type n] -> e n -> Abs (Nest Binder) e n
typesAsBinderNest types body = toConstBinderNest types body

nonDepPiType :: [CType n] -> CType n -> CorePiType n
nonDepPiType argTys resultTy = case typesAsBinderNest argTys resultTy of
  Abs bs resultTy' -> do
    let expls = nestToList (const Explicit) bs
    CorePiType ExplicitApp expls bs resultTy'

nonDepTabPiType :: IxType n -> Type n -> TabPiType n
nonDepTabPiType (IxType t d) resultTy =
  case toConstAbsPure resultTy of
    Abs b resultTy' -> TabPiType d (b:>t) resultTy'

corePiTypeToPiType :: CorePiType n -> PiType n
corePiTypeToPiType (CorePiType _ _ bs effTy) = PiType bs effTy

coreLamToTopLam :: CoreLamExpr n -> TopLam n
coreLamToTopLam (CoreLamExpr ty f) = TopLam False (corePiTypeToPiType ty) f

(==>) :: IxType n -> Type n -> Type n
a ==> b = TyCon $ TabPi $ nonDepTabPiType a b

litFinIxTy :: Int -> IxType n
litFinIxTy n = finIxTy $ IdxRepVal $ fromIntegral n

finIxTy :: Atom n -> IxType n
finIxTy n = IxType IdxRepTy (DictCon (IxRawFin n))

-- === querying effects implementation ===

instance HasEffects Expr where
  getEffects = \case
    Atom _ -> Pure
    Block (EffTy eff _) _ -> eff
    App (EffTy eff _) _ _ -> eff
    TopApp (EffTy eff _) _ _ -> eff
    TabApp _ _ _ -> Pure
    Case _ _ (EffTy effs _) -> effs
    TabCon _ _      -> Pure
    ApplyMethod (EffTy eff _) _ _ _ -> eff
    -- PrimOp _ primOp -> getEffects primOp
    Project _ _ _ -> Pure
    Unwrap _ _ -> Pure
    Hof (TypedHof (EffTy eff _) _) -> eff

instance HasEffects DeclBinding where
  getEffects (DeclBinding _ expr) = getEffects expr
  {-# INLINE getEffects #-}

-- instance HasEffects PrimOp r where
--   getEffects = \case
--     UnOp  _ _   -> Pure
--     BinOp _ _ _ -> Pure
--     VectorOp _  -> Pure
--     MemOp op -> case op of
--       IOAlloc  _    -> Effectful
--       IOFree   _    -> Effectful
--       PtrLoad  _    -> Effectful
--       PtrStore _ _  -> Effectful
--       PtrOffset _ _ -> Pure
--     MiscOp op -> case op of
--       Select _ _ _     -> Pure
--       ThrowError       -> Pure
--       CastOp _         -> Pure
--       UnsafeCoerce _   -> Pure
--       GarbageVal       -> Pure
--       BitcastOp _      -> Pure
--       SumTag _         -> Pure
--       ToEnum _         -> Pure
--       OutputStream     -> Pure
--       ShowAny _        -> Pure
--       ShowScalar _     -> Pure
--     RefOp _ m -> case m of
--       MGet      -> Effectful
--       MPut    _ -> Effectful
--       IndexRef _ -> Pure
--       ProjRef _  -> Pure
--   {-# INLINE getEffects #-}
