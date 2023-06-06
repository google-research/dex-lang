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
    Var name -> getType name
    Lam (CoreLamExpr piTy _) -> Pi piTy
    DepPair _ _ ty -> DepPairTy ty
    Con con -> getType con
    Eff _ -> EffKind
    PtrVar t _ -> PtrTy t
    DictCon ty _ -> ty
    NewtypeCon con _ -> getNewtypeType con
    RepValAtom (RepVal ty _) -> ty
    ProjectElt t _ _ -> t
    SimpInCore x -> getType x
    DictHole _ ty _ -> ty
    TypeAsAtom ty -> getType ty

instance IRRep r => HasType r (Type r) where
  getType = \case
    NewtypeTyCon con -> getType con
    Pi _        -> TyKind
    TabPi _     -> TyKind
    DepPairTy _ -> TyKind
    TC _        -> TyKind
    DictTy _    -> TyKind
    TyVar v     -> getType v
    ProjectEltTy t _ _ -> t

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
getSuperclassType bsAbove (Nest b bs) = \case
  0 -> ignoreHoistFailure $ hoist bsAbove $ binderType b
  i -> getSuperclassType (RNest bsAbove b) bs (i-1)

instance IRRep r => HasType r (Expr r) where
  getType expr = case expr of
    App (EffTy _ ty) _ _ -> ty
    TopApp (EffTy _ ty) _ _ -> ty
    TabApp t _ _ -> t
    Atom x   -> getType x
    TabCon _ ty _ -> ty
    PrimOp op -> getType op
    Case _ _ resultTy _ -> resultTy
    ApplyMethod (EffTy _ t) _ _ _ -> t

instance IRRep r => HasType r (DAMOp r) where
  getType = \case
    AllocDest ty -> RawRefTy ty
    Place _ _ -> UnitTy
    Freeze ref -> case getType ref of
      RawRefTy ty -> ty
      ty -> error $ "Not a reference type: " ++ show ty
    Seq _ _ cinit _ -> getType cinit
    RememberDest d _ -> getType d

instance HasType CoreIR UserEffectOp where
  getType = \case
    Handle _ _ _ -> undefined
    Perform _ _ -> undefined
    Resume retTy _ -> retTy

instance IRRep r => HasType r (PrimOp r) where
  getType primOp = case primOp of
    BinOp op x _ -> TC $ BaseType $ typeBinOp op $ getTypeBaseType x
    UnOp  op x   -> TC $ BaseType $ typeUnOp  op $ getTypeBaseType x
    Hof  hof -> getType hof
    MemOp op -> getType op
    MiscOp op -> getType op
    VectorOp op -> getType op
    DAMOp           op -> getType op
    UserEffectOp    op -> getType op
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

instance IRRep r => HasType r (Hof r) where
  getType = undefined  -- TODO: cache effects and type uniformly, with Hof'/Hof
  -- getType = \case
  --   For _ dict f -> undefined
  --   -- case getLamExprType f of
  --   --   PiType (UnaryNest (b:>_)) _ eltTy ->
  --   --     TabTy (b:>ixTyFromDict dict) eltTy
  --   --   _ -> error "expected a unary pi type"
  --   While _ -> UnitTy
  --   Linearize f _ -> case getLamExprType f of
  --     PiType (UnaryNest (binder:>a)) Pure b -> do
  --       let b' = ignoreHoistFailure $ hoist binder b
  --       let fLinTy = Pi $ nonDepPiType [a] Pure b'
  --       PairTy b' fLinTy
  --     _ -> error "expected a unary pi type"
  --   Transpose f _ -> case getLamExprType f of
  --     PiType (UnaryNest (_:>a)) _ _ -> a
  --     _ -> error "expected a unary pi type"
  --   RunReader _ f -> resultTy
  --     where (resultTy, _) = getTypeRWSAction f
  --   RunWriter _ _ f -> uncurry PairTy $ getTypeRWSAction f
  --   RunState _ _ f -> PairTy resultTy stateTy
  --     where (resultTy, stateTy) = getTypeRWSAction f
  --   RunIO f -> getType f
  --   RunInit f -> getType f
  --   CatchException ty _ -> ty

rawStrType :: IRRep r => Type r n
rawStrType = case newName "n" of
  Abs b v -> do
    let tabTy = rawFinTabType (Var $ AtomVar v IdxRepTy) CharRepTy
    DepPairTy $ DepPairType ExplicitDepPair (b:>IdxRepTy) tabTy

-- `n` argument is IdxRepVal, not Nat
rawFinTabType :: IRRep r => Atom r n -> Type r n -> Type r n
rawFinTabType n eltTy = IxType IdxRepTy (IxDictRawFin n) ==> eltTy

typesAsBinderNest
  :: (SinkableE e, HoistableE e, IRRep r)
  => [Type r n] -> e n -> Abs (Nest (Binder r)) e n
typesAsBinderNest types body = toConstBinderNest types body

nonDepPiType :: [CType n] -> EffectRow CoreIR n -> CType n -> CorePiType n
nonDepPiType argTys eff resultTy = undefined
-- nonDepPiType argTys eff resultTy = case typesAsBinderNest argTys (PairE eff resultTy) of
--   Abs bs (PairE eff' resultTy') -> do
--     let bs' = fmapNest (WithExpl Explicit) bs
--     CorePiType ExplicitApp bs' eff' resultTy'

nonDepTabPiType :: IRRep r => IxType r n -> Type r n -> TabPiType r n
nonDepTabPiType argTy resultTy = undefined
-- nonDepTabPiType argTy resultTy =
--   case toConstAbsPure resultTy of
--     Abs b resultTy' -> TabPiType (b:>argTy) resultTy'

(==>) :: IRRep r => IxType r n -> Type r n -> Type r n
a ==> b = TabPi $ nonDepTabPiType a b

finIxTy :: Int -> IxType r n
finIxTy n = IxType IdxRepTy (IxDictRawFin (IdxRepVal $ fromIntegral n))

ixTyFromDict :: IRRep r => IxDict r n -> IxType r n
ixTyFromDict ixDict = flip IxType ixDict $ case ixDict of
  IxDictAtom dict -> case getType dict of
    DictTy (DictType "Ix" _ [Type iTy]) -> iTy
    _ -> error $ "Not an Ix dict: " ++ show dict
  IxDictRawFin _ -> IdxRepTy
  IxDictSpecialized n _ _ -> n

getLamExprType :: IRRep r => LamExpr r n -> PiType r n
getLamExprType (LamExpr bs body) = undefined -- PiType bs (getEffects body) (getType body)

getDestLamExprType :: IRRep r => DestLamExpr r n -> PiType r n
getDestLamExprType = undefined -- (DestLamExpr bs body) = PiType bs (getEffects body) (getType body)

getTypeRWSAction :: IRRep r => LamExpr r n -> (Type r n, Type r n)
getTypeRWSAction f = undefined
-- getTypeRWSAction f = case getLamExprType f of
--   PiType (BinaryNest regionBinder refBinder) _ resultTy -> do
--     case binderType refBinder of
--       RefTy _ referentTy -> do
--         let referentTy' = ignoreHoistFailure $ hoist regionBinder referentTy
--         let resultTy' = ignoreHoistFailure $ hoist (PairB regionBinder refBinder) resultTy
--         (resultTy', referentTy')
--       _ -> error "expected a ref"
--   _ -> error "expected a pi type"

instance IRRep r => HasType r (Block r) where
  getType (Block NoBlockAnn Empty result) = getType result
  getType (Block (BlockAnn ty _) _ _) = ty
  getType _ = error "impossible"

instance IRRep r => HasType r (DestBlock r) where
  getType (DestBlock (_:>RawRefTy ansTy) _) = ansTy
  getType _ = error "not a valid dest block"

-- === querying effects implementation ===

instance IRRep r => HasEffects (Expr r) r where
  getEffects = \case
    Atom _ -> Pure
    App (EffTy eff _) _ _ -> eff
    TopApp (EffTy eff _) _ _ -> eff
    TabApp _ _ _ -> Pure
    Case _ _ _ effs -> effs
    TabCon _ _ _      -> Pure
    ApplyMethod (EffTy eff _) _ _ _ -> eff
    PrimOp primOp -> getEffects primOp

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
    UserEffectOp _ -> undefined
    DAMOp op -> case op of
      Place    _ _  -> OneEffect InitEffect
      Seq _ _ _ f      -> functionEffs f
      RememberDest _ f -> functionEffs f
      AllocDest _ -> Pure -- is this correct?
      Freeze _    -> Pure -- is this correct?
    Hof hof -> case hof of
      For _ _ f     -> functionEffs f
      While body    -> getEffects body
      Linearize _ _ -> Pure  -- Body has to be a pure function
      Transpose _ _ -> Pure  -- Body has to be a pure function
      RunReader _ f -> rwsFunEffects Reader f
      RunWriter d _ f -> maybeInit d $ rwsFunEffects Writer f
      RunState  d _ f -> maybeInit d $ rwsFunEffects State  f
      RunIO          f -> deleteEff IOEffect        $ getEffects f
      RunInit        f -> deleteEff InitEffect      $ getEffects f
      CatchException _ f -> deleteEff ExceptionEffect $ getEffects f
      where maybeInit :: IRRep r => Maybe (Atom r i) -> (EffectRow r o -> EffectRow r o)
            maybeInit d = case d of Just _ -> (<>OneEffect InitEffect); Nothing -> id
  {-# INLINE getEffects #-}


instance IRRep r => HasEffects (Block r) r where
  getEffects (Block (BlockAnn _ effs) _ _) = effs
  getEffects (Block NoBlockAnn _ _) = Pure
  {-# INLINE getEffects #-}

instance IRRep r => HasEffects (DestBlock r) r where
  getEffects (DestBlock b (Block ann _ _)) = case ann of
    BlockAnn _ effs -> ignoreHoistFailure $ hoist b effs
    NoBlockAnn -> Pure
  {-# INLINE getEffects #-}

instance IRRep r => HasEffects (Alt r) r where
  getEffects (Abs bs body) = ignoreHoistFailure $ hoist bs (getEffects body)
  {-# INLINE getEffects #-}

-- wrapper to allow checking the effects of an applied nullary dest lambda
data NullaryDestLamApp r n = NullaryDestLamApp (DestLamExpr r n)
-- XXX: this should only be used for nullary lambdas
instance IRRep r => HasEffects (NullaryDestLamApp r) r where
  getEffects (NullaryDestLamApp (NullaryDestLamExpr block)) = getEffects block
  getEffects _ = error "not a nullary lambda"
  {-# INLINE getEffects #-}

functionEffs :: IRRep r => LamExpr r n -> EffectRow r n
functionEffs f = undefined
-- functionEffs f = case getLamExprType f of
--   PiType b effs _ -> ignoreHoistFailure $ hoist b effs

rwsFunEffects :: IRRep r => RWS -> LamExpr r n -> EffectRow r n
rwsFunEffects rws f = undefined -- TODO: cache EffTy on op instead
-- case getLamExprType f of
-- rwsFunEffects rws f = case getLamExprType f of
--    PiType (BinaryNest h ref) effs _ -> do
--      let effs' = ignoreHoistFailure $ hoist ref effs
--      let hVal = Var $ AtomVar (binderName h) (TC HeapType)
--      let effs'' = deleteEff (RWSEffect rws hVal) effs'
--      ignoreHoistFailure $ hoist h effs''
--    _ -> error "Expected a binary function type"

deleteEff :: IRRep r => Effect r n -> EffectRow r n -> EffectRow r n
deleteEff eff (EffectRow effs t) = EffectRow (effs `eSetDifference` eSetSingleton eff) t
