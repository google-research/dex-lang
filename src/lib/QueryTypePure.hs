-- Copyright 2023 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module QueryTypePure where

import Types.Primitives
import Types.Core
import IRVariants
import Name

class HasType (r::IR) (e::E) | e -> r where
  getType :: e n -> Type r n

class HasEffects (e::E) (r::IR) | e -> r where
  getEffects :: e n -> EffectRow r n

isPure :: (IRRep r, HasEffects e r) => e n -> Bool
isPure e = case getEffects e of
  Pure -> True
  _    -> False

-- === querying types implementation ===

instance IRRep r => HasType r (AtomBinding r) where
  getType = \case
    LetBound    (DeclBinding _ e)  -> getType e
    MiscBound   ty                 -> ty
    SolverBound (InfVarBound ty _) -> ty
    SolverBound (SkolemBound ty)   -> ty
    SolverBound (DictBound   ty)   -> ty
    NoinlineFun ty _               -> ty
    TopDataBound (RepVal ty _)     -> ty
    FFIFunBound piTy _ -> Pi piTy

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


instance IRRep r => HasType r (AtomVar r) where
  getType (AtomVar _ ty) = ty
  {-# INLINE getType #-}

instance IRRep r => HasType r (Atom r) where
  getType atom = case atom of
    Stuck e -> getType e
    Lam (CoreLamExpr piTy _) -> Pi piTy
    DepPair _ _ ty -> DepPairTy ty
    Con con -> getType con
    Eff _ -> EffKind
    PtrVar t _ -> PtrTy t
    DictCon d -> getType d
    NewtypeCon con _ -> getNewtypeType con
    RepValAtom (RepVal ty _) -> ty
    SimpInCore x -> getType x
    TypeAsAtom ty -> getType ty

instance HasType CoreIR DictCon where
  getType = \case
    InstanceDict t _ _ -> t
    IxFin t _ -> t
    DataData t _ -> t

instance IRRep r => HasType r (Type r) where
  getType = \case
    NewtypeTyCon con -> getType con
    Pi _        -> TyKind
    TabPi _     -> TyKind
    DepPairTy _ -> TyKind
    TC _        -> TyKind
    DictTy _    -> TyKind
    StuckTy e   -> getType e

instance IRRep r => HasType r (Stuck r) where
  getType = \case
    StuckVar (AtomVar _ t)  -> t
    StuckProject t _ _      -> t
    StuckUnwrap  t _        -> t
    InstantiatedGiven t _ _ -> t
    SuperclassProj t _ _    -> t

instance HasType CoreIR SimpInCore where
  getType = \case
    LiftSimp t _       -> t
    LiftSimpFun piTy _ -> Pi $ piTy
    TabLam t _         -> TabPi $ t
    ACase _ _ t        -> t

instance HasType CoreIR NewtypeTyCon where
  getType _ = TyKind

getNewtypeType :: NewtypeCon n -> CType n
getNewtypeType con = case con of
  NatCon          -> NewtypeTyCon Nat
  FinCon n        -> NewtypeTyCon $ Fin n
  UserADTData sn d params -> NewtypeTyCon $ UserADTType sn d params

instance IRRep r => HasType r (Con r) where
  getType = \case
    Lit l          -> BaseTy $ litType l
    ProdCon xs     -> ProdTy $ map getType xs
    SumCon tys _ _ -> SumTy tys
    HeapVal        -> TC HeapType

getSuperclassType :: RNest CBinder n l -> Nest CBinder l l' -> Int -> CType n
getSuperclassType _ Empty = error "bad index"
getSuperclassType bsAbove (Nest b@(_:>t) bs) = \case
  0 -> ignoreHoistFailure $ hoist bsAbove t
  i -> getSuperclassType (RNest bsAbove b) bs (i-1)

instance IRRep r => HasType r (Expr r) where
  getType expr = case expr of
    App (EffTy _ ty) _ _ -> ty
    TopApp (EffTy _ ty) _ _ -> ty
    TabApp t _ _ -> t
    Atom x   -> getType x
    Block (EffTy _ ty) _ -> ty
    TabCon _ ty _ -> ty
    PrimOp op -> getType op
    Case _ _ (EffTy _ resultTy) -> resultTy
    ApplyMethod (EffTy _ t) _ _ _ -> t
    Project t _ _ -> t
    Unwrap t _ -> t

instance IRRep r => HasType r (DAMOp r) where
  getType = \case
    AllocDest ty -> RawRefTy ty
    Place _ _ -> UnitTy
    Freeze ref -> case getType ref of
      RawRefTy ty -> ty
      ty -> error $ "Not a reference type: " ++ show ty
    Seq _ _ _ cinit _ -> getType cinit
    RememberDest _ d _ -> getType d

instance IRRep r => HasType r (PrimOp r) where
  getType primOp = case primOp of
    BinOp op x _ -> TC $ BaseType $ typeBinOp op $ getTypeBaseType x
    UnOp  op x   -> TC $ BaseType $ typeUnOp  op $ getTypeBaseType x
    Hof  (TypedHof (EffTy _ ty) _) -> ty
    MemOp op -> getType op
    MiscOp op -> getType op
    VectorOp op -> getType op
    DAMOp           op -> getType op
    RefOp ref m -> case getType ref of
      TC (RefType _ s) -> case m of
        MGet        -> s
        MPut _      -> UnitTy
        MAsk        -> s
        MExtend _ _ -> UnitTy
        IndexRef t _ -> t
        ProjRef t _ -> t
      _ -> error "not a reference type"

getTypeBaseType :: (IRRep r, HasType r e) => e n -> BaseType
getTypeBaseType e = case getType e of
  TC (BaseType b) -> b
  ty -> error $ "Expected a base type. Got: " ++ show ty

instance IRRep r => HasType r (MemOp r) where
  getType = \case
    IOAlloc _ -> PtrTy (CPU, Scalar Word8Type)
    IOFree _ -> UnitTy
    PtrOffset arr _ -> getType arr
    PtrLoad ptr -> do
      let PtrTy (_, t) = getType ptr
      BaseTy t
    PtrStore _ _ -> UnitTy

instance IRRep r => HasType r (VectorOp r) where
  getType = \case
    VectorBroadcast _ vty -> vty
    VectorIota vty -> vty
    VectorIdx _ _ vty -> vty
    VectorSubref ref _ vty -> case getType ref of
      TC (RefType h _) -> TC $ RefType h vty
      ty -> error $ "Not a reference type: " ++ show ty

instance IRRep r => HasType r (MiscOp r) where
  getType = \case
    Select _ x _ -> getType x
    ThrowError t     -> t
    ThrowException t -> t
    CastOp t _       -> t
    BitcastOp t _    -> t
    UnsafeCoerce t _ -> t
    GarbageVal t -> t
    SumTag _     -> TagRepTy
    ToEnum t _   -> t
    OutputStream -> BaseTy $ hostPtrTy $ Scalar Word8Type
      where hostPtrTy ty = PtrType (CPU, ty)
    ShowAny _ -> rawStrType -- TODO: constrain `ShowAny` to have `HasCore r`
    ShowScalar _ -> PairTy IdxRepTy $ rawFinTabType (IdxRepVal showStringBufferSize) CharRepTy

rawStrType :: IRRep r => Type r n
rawStrType = case newName "n" of
  Abs b v -> do
    let tabTy = rawFinTabType (Var $ AtomVar v IdxRepTy) CharRepTy
    DepPairTy $ DepPairType ExplicitDepPair (b:>IdxRepTy) tabTy

-- `n` argument is IdxRepVal, not Nat
rawFinTabType :: IRRep r => Atom r n -> Type r n -> Type r n
rawFinTabType n eltTy = IxType IdxRepTy (IxDictRawFin n) ==> eltTy

tabIxType :: TabPiType r n -> IxType r n
tabIxType (TabPiType d (_:>t) _) = IxType t d

typesAsBinderNest
  :: (SinkableE e, HoistableE e, IRRep r)
  => [Type r n] -> e n -> Abs (Nest (Binder r)) e n
typesAsBinderNest types body = toConstBinderNest types body

nonDepPiType :: [CType n] -> EffectRow CoreIR n -> CType n -> CorePiType n
nonDepPiType argTys eff resultTy = case typesAsBinderNest argTys (PairE eff resultTy) of
  Abs bs (PairE eff' resultTy') -> do
    let expls = nestToList (const Explicit) bs
    CorePiType ExplicitApp expls bs $ EffTy eff' resultTy'

nonDepTabPiType :: IRRep r => IxType r n -> Type r n -> TabPiType r n
nonDepTabPiType (IxType t d) resultTy =
  case toConstAbsPure resultTy of
    Abs b resultTy' -> TabPiType d (b:>t) resultTy'

corePiTypeToPiType :: CorePiType n -> PiType CoreIR n
corePiTypeToPiType (CorePiType _ _ bs effTy) = PiType bs effTy

coreLamToTopLam :: CoreLamExpr n -> TopLam CoreIR n
coreLamToTopLam (CoreLamExpr ty f) = TopLam False (corePiTypeToPiType ty) f

(==>) :: IRRep r => IxType r n -> Type r n -> Type r n
a ==> b = TabPi $ nonDepTabPiType a b

litFinIxTy :: Int -> IxType r n
litFinIxTy n = finIxTy $ IdxRepVal $ fromIntegral n

finIxTy :: Atom r n -> IxType r n
finIxTy n = IxType IdxRepTy (IxDictRawFin n)

ixTyFromDict :: IRRep r => IxDict r n -> IxType r n
ixTyFromDict ixDict = flip IxType ixDict $ case ixDict of
  IxDictAtom dict -> case getType dict of
    DictTy (DictType "Ix" _ [Type iTy]) -> iTy
    _ -> error $ "Not an Ix dict: " ++ show dict
  IxDictRawFin _ -> IdxRepTy
  IxDictSpecialized n _ _ -> n

-- === querying effects implementation ===

instance IRRep r => HasEffects (Expr r) r where
  getEffects = \case
    Atom _ -> Pure
    Block (EffTy eff _) _ -> eff
    App (EffTy eff _) _ _ -> eff
    TopApp (EffTy eff _) _ _ -> eff
    TabApp _ _ _ -> Pure
    Case _ _ (EffTy effs _) -> effs
    TabCon _ _ _      -> Pure
    ApplyMethod (EffTy eff _) _ _ _ -> eff
    PrimOp primOp -> getEffects primOp
    Project _ _ _ -> Pure
    Unwrap _ _ -> Pure

instance IRRep r => HasEffects (DeclBinding r) r where
  getEffects (DeclBinding _ expr) = getEffects expr
  {-# INLINE getEffects #-}

instance IRRep r => HasEffects (PrimOp r) r where
  getEffects = \case
    UnOp  _ _   -> Pure
    BinOp _ _ _ -> Pure
    VectorOp _  -> Pure
    MemOp op -> case op of
      IOAlloc  _    -> OneEffect IOEffect
      IOFree   _    -> OneEffect IOEffect
      PtrLoad  _    -> OneEffect IOEffect
      PtrStore _ _  -> OneEffect IOEffect
      PtrOffset _ _ -> Pure
    MiscOp op -> case op of
      ThrowException _ -> OneEffect ExceptionEffect
      Select _ _ _     -> Pure
      ThrowError _     -> Pure
      CastOp _ _       -> Pure
      UnsafeCoerce _ _ -> Pure
      GarbageVal _     -> Pure
      BitcastOp _ _    -> Pure
      SumTag _         -> Pure
      ToEnum _ _       -> Pure
      OutputStream     -> Pure
      ShowAny _        -> Pure
      ShowScalar _     -> Pure
    RefOp ref m -> case getType ref of
      TC (RefType h _) -> case m of
        MGet      -> OneEffect (RWSEffect State  h)
        MPut    _ -> OneEffect (RWSEffect State  h)
        MAsk      -> OneEffect (RWSEffect Reader h)
        -- XXX: We don't verify the base monoid. See note about RunWriter.
        MExtend _ _ -> OneEffect (RWSEffect Writer h)
        IndexRef _ _ -> Pure
        ProjRef _ _  -> Pure
      _ -> error "not a ref"
    DAMOp op -> case op of
      Place    _ _  -> OneEffect InitEffect
      Seq eff _ _ _ _        -> eff
      RememberDest eff _ _ -> eff
      AllocDest _ -> Pure -- is this correct?
      Freeze _    -> Pure -- is this correct?
    Hof (TypedHof (EffTy eff _) _) -> eff
  {-# INLINE getEffects #-}
