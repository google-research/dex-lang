-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module CheckType (CheckableE (..), CheckableB (..), checkTypes, checkTypeIs) where

import Prelude hiding (id)
import Control.Category ((>>>))
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State.Class
import Data.Functor

import CheapReduction
import Core
import Err
import IRVariants
import MTL1
import Name
import Subst
import PPrint
import QueryType
import Types.Core
import Types.Primitives
import Types.Source
import Types.Top

-- === top-level API ===

checkTypes :: (EnvReader m, Fallible1 m, CheckableE r e) => e n -> m n ()
checkTypes e = liftTyperM (void $ checkE e) >>= liftExcept

checkTypeIs :: (EnvReader m, Fallible1 m, CheckableE r e, IRRep r, HasType r e) => e n -> Type r n -> m n ()
checkTypeIs e ty = liftTyperM (void $ e |: ty) >>= liftExcept

-- === the type checking/querying monad ===

newtype TyperM (r::IR) (i::S) (o::S) (a :: *) =
  TyperM { runTyperT' :: SubstReaderT Name (StateT1 (NameMap (AtomNameC r) Int) (EnvReaderT Except)) i o a }
  deriving ( Functor, Applicative, Monad , SubstReader Name , MonadFail , Fallible , ScopeReader
           , EnvReader, EnvExtender, Catchable)

liftTyperM :: EnvReader m => TyperM r n n a -> m n (Except a)
liftTyperM cont = liftEnvReaderT $ flip evalStateT1 mempty $ runSubstReaderT idSubst $ runTyperT' cont
{-# INLINE liftTyperM #-}

-- I can't make up my mind whether a `Seq` loop should be allowed to
-- close over a dest from an enclosing scope.  Status quo permits this.
affineUsed :: AtomName r o -> TyperM r i o ()
affineUsed name = TyperM $ do
  affines <- get
  case lookupNameMapE name affines of
    Just (LiftE n) ->
        if n > 0 then
          throwInternal $ "Affine name " ++ pprint name ++ " used " ++ show (n + 1) ++ " times."
        else
          put $ insertNameMapE name (LiftE $ n + 1) affines
    Nothing -> put $ insertNameMapE name (LiftE 1) affines

parallelAffines :: [TyperM r i o a] -> TyperM r i o [a]
parallelAffines actions = TyperM $ do
  -- This method permits using an affine variable in each branch of a `case`.
  -- We check each `case` branch in isolation, detecting affine overuse within
  -- the branch; then we check whether the union of the variables used in the
  -- branches reuses a variable from outside that it shouldn't.
  -- This has the down-side of localizing such an error to the case rather
  -- than to the offending in-branch use, but that can be improved later.
  affines <- get
  (results, isolateds) <- unzip <$> forM actions \act -> do
    put mempty
    result <- runTyperT' act
    (result,) <$> get
  put affines
  forM_ (toListNameMapE $ unionsWithNameMapE max isolateds) \(name, (LiftE ct)) ->
    case ct of
      0 -> return ()
      1 -> runTyperT' $ affineUsed name
      _ -> error $ "Unexpected multi-used affine name " ++ show name ++ " from case branches."
  return results

-- === typeable things ===

checkTypesEq :: IRRep r => Type r o -> Type r o -> TyperM r i o ()
checkTypesEq reqTy ty = alphaEq reqTy ty >>= \case
  True  -> return ()
  False -> {-# SCC typeNormalization #-} do
    alphaEq reqTy ty >>= \case
      True  -> return ()
      False -> throwInternal $ pprint reqTy ++ " != " ++ pprint ty
{-# INLINE checkTypesEq #-}

class SinkableE e => CheckableE (r::IR) (e::E) | e -> r where
  checkE :: e i -> TyperM r i o (e o)

class HasNamesB b => CheckableB (r::IR) (b::B) | b -> r where
  checkB :: b i i'
         -> (forall o'. DExt o o' => b o o' -> TyperM r i' o' a)
         -> TyperM r i o a

class SinkableE e => CheckableWithEffects (r::IR) (e::E) | e -> r where
  checkWithEffects :: EffectRow r o -> e i -> TyperM r i o (e o)

checkBEvidenced :: CheckableB r b
                => b i i'
                -> (forall o'. Distinct o' => ExtEvidence o o' -> b o o' -> TyperM r i' o' a)
                -> TyperM r i o a
checkBEvidenced b cont = checkB b \b' -> cont getExtEvidence b'

-- === convenience functions ===

infixr 7 |:
(|:) :: (HasType r e, CheckableE r e, IRRep r) => e i -> Type r o -> TyperM r i o (e o)
(|:) x reqTy = do
  x' <- checkE x
  checkTypesEq reqTy (getType x')
  return x'

checkAndGetType :: (HasType r e, CheckableE r e, IRRep r) => e i -> TyperM r i o (e o, Type r o)
checkAndGetType x = do
  x' <- checkE x
  return (x', getType x')

checkWithEffTy :: (CheckableWithEffects r e, HasType r e, IRRep r) => EffTy r o -> e i -> TyperM r i o (e o)
checkWithEffTy (EffTy effs ty) e = do
  e' <- checkWithEffects effs e
  checkTypesEq ty (getType e')
  return e'

instance CheckableE CoreIR SourceMap where
  checkE sm = renameM sm -- TODO?

instance (CheckableE r e1, CheckableE r e2) => CheckableE r (PairE e1 e2) where
  checkE (PairE e1 e2) = PairE <$> checkE e1 <*> checkE e2

instance (CheckableE r e1, CheckableE r e2) => CheckableE r (EitherE e1 e2) where
  checkE ( LeftE e) = LeftE  <$> checkE e
  checkE (RightE e) = RightE <$> checkE e

instance (CheckableB r b, CheckableE r e) => CheckableE r (Abs b e) where
  checkE (Abs b e) = checkB b \b' -> Abs b' <$> checkE e

-- === type checking core ===

checkStuck :: IRRep r => Type r i -> Stuck r i -> TyperM r i o (Type r o, Stuck r o)
checkStuck ty e = do
   e' <- checkE e
   ty' <- checkE ty
   ty'' <- queryStuckType e'
   checkTypesEq ty' ty''
   return (ty', e')

instance IRRep r => CheckableE r (TopLam r) where
  checkE (TopLam destFlag piTy lam) = do
    -- TODO: check destination-passing flag
    piTy' <- checkE piTy
    lam' <- checkLamExpr piTy' lam
    return $ TopLam destFlag piTy' lam'

instance IRRep r => CheckableE r (AtomName r) where
  checkE = renameM

instance IRRep r => CheckableE r (Atom r) where
  checkE = \case
    Stuck ty e -> uncurry Stuck <$> checkStuck ty e
    Con e -> Con <$> checkE e

instance IRRep r => CheckableE r (AtomVar r) where
  checkE (AtomVar v t1) = do
    t1' <- renameM t1
    v' <- renameM v
    t2 <- getType <$> lookupAtomName v'
    checkTypesEq t1' t2
    return $ AtomVar v' t1'

instance IRRep r => CheckableE r (Type r) where
  checkE = \case
    StuckTy ty e -> uncurry StuckTy <$> checkStuck ty e
    TyCon e -> TyCon <$> checkE e

instance (ToBinding ann c, Color c, CheckableE r ann) => CheckableB r (BinderP c ann) where
  checkB (b:>ann) cont = do
    ann' <- checkE ann
    withFreshBinder (getNameHint b) ann' \b' ->
      extendRenamer (b@>binderName b') $
        cont b'

checkBinderType
  :: (IRRep r) => Type r o -> Binder r i i'
  -> (forall o'. DExt o o' => Binder r o o' -> TyperM r i' o' a)
  -> TyperM r i o a
checkBinderType ty b cont = do
  checkB b \b' -> do
    checkTypesEq (sink $ binderType b') (sink ty)
    cont b'

instance IRRep r => CheckableWithEffects r (Expr r) where
  checkWithEffects allowedEffs expr = case expr of
    App effTy f xs -> do
      effTy' <- checkEffTy allowedEffs effTy
      f' <- checkE f
      TyCon (Pi piTy) <- return $ getType f'
      xs' <- mapM checkE xs
      effTy'' <- checkInstantiation piTy xs'
      checkAlphaEq  effTy' effTy''
      return $ App effTy' f' xs'
    TabApp reqTy f x -> do
      reqTy' <- checkE reqTy
      (f', tabTy) <- checkAndGetType f
      x' <- checkE x
      ty' <- checkTabApp tabTy x'
      checkTypesEq reqTy' ty'
      return $ TabApp reqTy' f' x'
    TopApp effTy f xs -> do
      f' <- renameM f
      effTy' <- checkEffTy allowedEffs effTy
      piTy <- getTypeTopFun f'
      xs' <- mapM checkE xs
      effTy'' <- checkInstantiation piTy xs'
      checkAlphaEq  effTy' effTy''
      return $ TopApp effTy' f' xs'
    Atom x -> Atom <$> checkE x
    PrimOp op -> PrimOp <$> checkWithEffects allowedEffs op
    Block effTy (Abs decls body) -> do
      effTy'@(EffTy effs ty) <- checkEffTy allowedEffs effTy
      checkDecls effs decls \decls' -> do
        body' <- checkWithEffects (sink effs) body
        checkTypesEq (sink ty) (getType body')
        return $ Block effTy' $ Abs decls' body'
    Case scrut alts effTy -> do
      effTy' <- checkEffTy allowedEffs effTy
      scrut' <- checkE scrut
      TyCon (SumType altsBinderTys) <- return $ getType scrut'
      assertEq (length altsBinderTys) (length alts) ""
      alts' <- parallelAffines $ (zip alts altsBinderTys) <&> \(Abs b body, reqBinderTy) -> do
        checkB b \b' -> do
          checkTypesEq (sink reqBinderTy) (sink $ binderType b')
          Abs b' <$> checkWithEffTy (sink effTy') body
      return $ Case scrut' alts' effTy'
    ApplyMethod effTy dict i args -> do
      effTy' <- checkEffTy allowedEffs effTy
      Just dict' <- toMaybeDict <$> checkE dict
      args' <- mapM checkE args
      methodTy <- getMethodType dict' i
      effTy'' <- checkInstantiation methodTy args'
      checkAlphaEq  effTy' effTy''
      return $ ApplyMethod effTy' (toAtom dict') i args'
    TabCon maybeD ty xs -> do
      ty'@(TyCon (TabPi (TabPiType _ b restTy))) <- checkE ty
      maybeD' <- mapM renameM maybeD -- TODO: check
      xs' <- case fromConstAbs (Abs b restTy) of
        HoistSuccess elTy -> forM xs (|: elTy)
        -- XXX: in the dependent case we don't check that the element types
        -- match the annotation because that would require concretely evaluating
        -- each index from the ix dict.
        HoistFailure _    -> forM xs checkE
      return $ TabCon maybeD' ty' xs'
    Project resultTy i x -> do
      x' <-checkE x
      resultTy' <- checkE resultTy
      resultTy'' <- checkProject i x'
      checkTypesEq resultTy' resultTy''
      return $ Project resultTy' i x'
    Unwrap resultTy x -> do
      resultTy' <- checkE resultTy
      (x', TyCon (NewtypeTyCon con)) <- checkAndGetType x
      resultTy'' <- snd <$> unwrapNewtypeType con
      checkTypesEq resultTy' resultTy''
      return $ Unwrap resultTy' x'

instance CheckableE CoreIR TyConParams where
  checkE (TyConParams expls params) = TyConParams expls <$> mapM checkE params

instance IRRep r => CheckableE r (Stuck r) where
  checkE = \case
    Var name -> do
      name' <- checkE name
      case getType name' of
        RawRefTy _ -> affineUsed $ atomVarName name'
        _ -> return ()
      return $ Var name'
    StuckUnwrap x -> do
      x' <- checkE x
      TyCon (NewtypeTyCon _) <- queryStuckType x'
      return $ StuckUnwrap x'
    StuckProject i x -> do
      x' <-checkE x
      x'' <- mkStuck x'
      void $ checkProject i x''
      return $ StuckProject i x'
    StuckTabApp f x -> do
      f' <- checkE f
      tabTy <- queryStuckType f'
      x'  <- checkE x
      void $ checkTabApp tabTy x'
      return $ StuckTabApp f' x'
    InstantiatedGiven given args -> do
      given' <- checkE given
      TyCon (Pi piTy) <- queryStuckType given'
      args' <- mapM checkE args
      EffTy Pure _ <- checkInstantiation piTy args'
      return $ InstantiatedGiven given' args'
    SuperclassProj i d -> SuperclassProj <$> pure i <*> checkE d -- TODO: check index in range
    PtrVar t v -> PtrVar t <$> renameM v
    RepValAtom repVal -> RepValAtom <$> renameM repVal -- TODO: check
    LiftSimp t x -> LiftSimp <$> checkE t <*> renameM x -- TODO: check
    LiftSimpFun t x -> LiftSimpFun <$> checkE t <*> renameM x -- TODO: check
    ACase scrut alts resultTy -> ACase <$> renameM scrut <*> mapM renameM alts <*> checkE resultTy -- TODO: check
    TabLam lam -> TabLam <$> renameM lam -- TODO: check

depPairLeftTy :: DepPairType r n -> Type r n
depPairLeftTy (DepPairType _ (_:>ty) _) = ty
{-# INLINE depPairLeftTy #-}

instance IRRep r => CheckableE r (DictCon r) where
  checkE = \case
    InstanceDict ty instanceName args -> do
      ty' <- checkE ty
      instanceName' <- renameM instanceName
      args' <- mapM checkE args
      instanceDef <- lookupInstanceDef instanceName'
      void $ checkInstantiation instanceDef args'
      return $ InstanceDict ty' instanceName' args'
    IxFin n -> IxFin <$> n |: NatTy
    DataData dataTy -> DataData <$> checkE dataTy
    IxRawFin n -> IxRawFin <$> n |: IdxRepTy
    IxSpecialized v params -> IxSpecialized <$> renameM v <*> mapM checkE params

instance IRRep r => CheckableE r (DepPairType r) where
  checkE (DepPairType expl b ty) = do
    checkB b \b' -> do
      ty' <- checkE ty
      return $ DepPairType expl b' ty'

instance CheckableE CoreIR CorePiType where
  checkE (CorePiType expl expls bs effTy) = do
    checkB bs \bs' -> do
      effTy' <- checkE effTy
      return $ CorePiType expl expls bs' effTy'

instance IRRep r => CheckableE r (PiType r) where
  checkE (PiType bs effTy) = do
    checkB bs \bs' -> do
      effTy' <- checkE effTy
      return $ PiType bs' effTy'

instance IRRep r => CheckableE r (IxDict r) where
  checkE = renameM -- TODO: check

instance IRRep r => CheckableE r (IxType r) where
  checkE (IxType t d) = IxType <$> checkE t <*> checkE d

instance IRRep r => CheckableE r (TabPiType r) where
  checkE (TabPiType d b resultTy) = do
    d' <- checkE d
    checkB b \b' -> do
      resultTy' <- checkE resultTy
      return $ TabPiType d' b' resultTy'

instance (BindsNames b, CheckableB r b) => CheckableB r (Nest b) where
  checkB nest cont = case nest of
    Empty -> getDistinct >>= \Distinct -> cont Empty
    Nest b rest ->
      checkBEvidenced b \ext1 b' ->
        checkBEvidenced rest \ext2 rest' ->
          withExtEvidence (ext1 >>> ext2) $
            cont $ Nest b' rest'

instance CheckableE CoreIR CoreLamExpr where
  checkE (CoreLamExpr piTy lamExpr) = do
     CorePiType expl expls bs effTy <- checkE piTy
     lamExpr' <- checkLamExpr (PiType bs effTy) lamExpr
     return $ CoreLamExpr (CorePiType expl expls bs effTy) lamExpr'

instance IRRep r => CheckableE r (TyCon r) where
  checkE = \case
    BaseType b       -> return $ BaseType b
    ProdType tys     -> ProdType <$> mapM checkE tys
    SumType  cs      -> SumType  <$> mapM checkE cs
    RefType r a      -> RefType <$> r|:TyCon HeapType <*> checkE a
    TypeKind         -> return TypeKind
    HeapType         -> return HeapType
    Pi t           -> Pi           <$> checkE t
    TabPi t        -> TabPi        <$> checkE t
    NewtypeTyCon t -> NewtypeTyCon <$> checkE t
    DepPairTy t    -> DepPairTy    <$> checkE t
    DictTy t       -> DictTy       <$> checkE t


instance CheckableE CoreIR DictType where
  checkE = \case
    DictType sn className params -> do
      className' <- renameM className
      ClassDef _ Nothing _ _ _ paramBs _ _ <- lookupClassDef className'
      params' <- mapM checkE params
      void $ checkInstantiation (Abs paramBs UnitE) params'
      return $ DictType sn className' params'
    IxDictType   t -> IxDictType   <$> checkE t
    DataDictType t -> DataDictType <$> checkE t

instance IRRep r => CheckableE r (Con r) where
  checkE = \case
    Lit l -> return $ Lit l
    ProdCon xs -> ProdCon <$> mapM checkE xs
    SumCon tys tag payload -> do
      tys' <- mapM checkE tys
      unless (0 <= tag && tag < length tys') $ throwInternal "Invalid SumType tag"
      payload' <- payload |: (tys' !! tag)
      return $ SumCon tys' tag payload'
    HeapVal -> return HeapVal
    Lam lam -> Lam <$> checkE lam
    DepPair l r ty -> do
      l' <- checkE l
      ty' <- checkE ty
      rTy <- checkInstantiation ty' [l']
      r' <- r |: rTy
      return $ DepPair l' r' ty'
    Eff eff  -> Eff <$> checkE eff
    -- TODO: check against cached type
    DictConAtom con -> DictConAtom <$> checkE con
    NewtypeCon con x -> do
      (x', xTy) <- checkAndGetType x
      con' <- typeCheckNewtypeCon con xTy
      return $ NewtypeCon con' x'
    TyConAtom tyCon -> TyConAtom <$> checkE tyCon

typeCheckNewtypeCon
  :: NewtypeCon i -> CType o -> TyperM CoreIR i o (NewtypeCon o)
typeCheckNewtypeCon con xTy = case con of
  NatCon   -> checkAlphaEq IdxRepTy xTy >> return NatCon
  FinCon n -> do
    n' <- n|:NatTy
    checkAlphaEq xTy NatTy
    return $ FinCon n'
  UserADTData sn d params -> do
    d' <- renameM d
    TyConParams expls params' <- checkE params
    def <- lookupTyCon d'
    void $ checkInstantiation def params'
    return $ UserADTData sn d' (TyConParams expls params')

instance CheckableE CoreIR NewtypeTyCon where
  checkE = \case
    Nat -> return Nat
    Fin n -> Fin <$> n|:NatTy
    EffectRowKind -> return EffectRowKind
    UserADTType sn d params -> do
      d' <- renameM d
      TyConParams expls params' <- checkE params
      def <- lookupTyCon d'
      void $ checkInstantiation def params'
      return $ UserADTType sn d' (TyConParams expls params')

instance IRRep r => CheckableWithEffects r (PrimOp r) where
  checkWithEffects effs = \case
    Hof (TypedHof effTy hof) -> do
      effTy'@(EffTy effs' resultTy) <- checkE effTy
      checkExtends effs effs'
      -- TODO: we should be able to use the `effTy` from the `TypedHof`, which
      -- might have fewer effects than `effs`. But that exposes an error in
      -- which we under-report the `Init` effect in the `TypedHof` effect
      -- annotation. We should fix that.
      hof' <- checkHof (EffTy effs resultTy) hof
      return $ Hof (TypedHof effTy' hof')
    VectorOp vOp -> VectorOp <$> checkE vOp
    BinOp binop x y -> do
      x' <- checkE x
      y' <- checkE y
      TyCon (BaseType xTy) <- return $ getType x'
      TyCon (BaseType yTy) <- return $ getType y'
      checkBinOp binop xTy yTy
      return $ BinOp binop x' y'
    UnOp  unop  x -> do
      x' <- checkE x
      TyCon (BaseType xTy) <- return $ getType x'
      checkUnOp unop xTy
      return $ UnOp unop x'
    MiscOp op -> MiscOp <$> checkWithEffects effs op
    MemOp  op -> MemOp  <$> checkWithEffects effs op
    DAMOp  op -> DAMOp  <$> checkWithEffects effs op
    RefOp ref m -> do
      (ref', TyCon (RefType h s)) <- checkAndGetType ref
      m' <- case m of
        MGet -> declareEff effs (RWSEffect State  h) $> MGet
        MPut x -> do
          x' <- x|:s
          declareEff effs (RWSEffect State  h)
          return $ MPut x'
        MAsk -> declareEff effs (RWSEffect Reader h) $> MAsk
        MExtend b x -> do
          b' <- checkE b
          x' <- x|:s
          declareEff effs (RWSEffect Writer h)
          return $ MExtend b' x'
        IndexRef givenTy i -> do
          givenTy' <- checkE givenTy
          TyCon (TabPi tabTy) <- return s
          i' <- checkE i
          eltTy' <- checkInstantiation tabTy [i']
          checkTypesEq givenTy' (TyCon $ RefType h eltTy')
          return $ IndexRef givenTy' i'
        ProjRef givenTy p -> do
          givenTy' <- checkE givenTy
          resultEltTy <- case p of
            ProjectProduct i -> do
              TyCon (ProdType tys) <- return s
              return $ tys !! i
            UnwrapNewtype -> do
              TyCon (NewtypeTyCon tc) <- return s
              snd <$> unwrapNewtypeType tc
          checkTypesEq givenTy' (TyCon $ RefType h resultEltTy)
          return $ ProjRef givenTy' p
      return $ RefOp ref' m'

instance IRRep r => CheckableE r (EffTy r) where
  checkE (EffTy effs ty) = EffTy <$> checkE effs <*> checkE ty

instance IRRep r => CheckableE r (BaseMonoid r) where
  checkE = renameM -- TODO: check

instance IRRep r => CheckableWithEffects r (MemOp r) where
  checkWithEffects effs = \case
    IOAlloc n -> do
      declareEff effs IOEffect
      IOAlloc <$> (n |: IdxRepTy)
    IOFree ptr -> do
      declareEff effs IOEffect
      IOFree <$> checkIsPtr ptr
    PtrOffset ptr off -> do
      ptr' <- checkIsPtr ptr
      off' <- off |: IdxRepTy
      return $ PtrOffset ptr' off'
    PtrLoad ptr -> do
      declareEff effs IOEffect
      PtrLoad <$> checkIsPtr ptr
    PtrStore ptr val -> do
      declareEff effs IOEffect
      ptr' <- checkE ptr
      PtrTy (_, t)  <- return $ getType ptr'
      val' <- val |: BaseTy t
      return $ PtrStore ptr' val'

checkIsPtr :: IRRep r => Atom r i -> TyperM r i o (Atom r o)
checkIsPtr ptr = do
  ptr' <- checkE ptr
  PtrTy _ <- return $ getType ptr'
  return ptr'

instance IRRep r => CheckableWithEffects r (MiscOp r) where
  checkWithEffects effs = \case
    Select p x y -> do
      p' <- p |: (BaseTy $ Scalar Word8Type)
      x' <- checkE x
      y' <- y |: getType x'
      return $ Select p' x' y'
    CastOp t@(StuckTy _ (Var _)) e -> CastOp <$> checkE t <*> renameM e
    CastOp destTy e -> do
      e' <- checkE e
      destTy' <- checkE destTy
      checkValidCast (getType e') destTy'
      return $ CastOp destTy' e'
    BitcastOp t@(StuckTy _ (Var _)) e -> BitcastOp <$> checkE t <*> renameM e
    BitcastOp destTy e -> do
      destTy' <- checkE destTy
      e' <- checkE e
      let sourceTy = getType e'
      case (destTy', sourceTy) of
        (BaseTy dbt@(Scalar _), BaseTy sbt@(Scalar _)) | sizeOf sbt == sizeOf dbt ->
          return $ BitcastOp destTy' e'
        _ -> throwInternal $ "Invalid bitcast: " ++ pprint sourceTy ++ " -> " ++ pprint destTy
    UnsafeCoerce t e -> UnsafeCoerce <$> checkE t <*> renameM e
    GarbageVal t -> GarbageVal <$> checkE t
    SumTag x -> do
      x' <- checkE x
      void $ checkSomeSumType $ getType x'
      return $ SumTag x'
    ToEnum t x -> do
      t' <- checkE t
      x' <- x |: Word8Ty
      cases <- checkSomeSumType t'
      forM_ cases \cty -> checkTypesEq cty UnitTy
      return $ ToEnum t' x'
    OutputStream -> return OutputStream
    ShowAny x -> ShowAny <$> checkE x
    ShowScalar x -> do
      x' <- checkE x
      BaseTy (Scalar _) <- return $ getType x'
      return $ ShowScalar x'
    ThrowError ty -> ThrowError <$> checkE ty
    ThrowException ty -> ThrowException <$> do
      declareEff effs ExceptionEffect
      checkE ty

checkSomeSumType :: IRRep r => Type r o -> TyperM r i o [Type r o]
checkSomeSumType = \case
  TyCon (SumType cases) -> return cases
  TyCon (NewtypeTyCon con) -> do
    (_, TyCon (SumType cases)) <- unwrapNewtypeType con
    return cases
  t -> error $ "not some sum type: " ++ pprint t

instance IRRep r => CheckableE r (VectorOp r) where
  checkE = \case
    VectorBroadcast v ty -> do
      ty'@(BaseTy (Vector _ sbt)) <- checkE ty
      v' <- v |: BaseTy (Scalar sbt)
      return $ VectorBroadcast v' ty'
    VectorIota ty -> do
      ty'@(BaseTy (Vector _ _)) <- checkE ty
      return $ VectorIota ty'
    VectorIdx tbl i ty -> do
      tbl' <- checkE tbl
      TabTy _ b (BaseTy (Scalar sbt)) <- return $ getType tbl'
      i' <- i |: binderType b
      ty'@(BaseTy (Vector _ sbt')) <- checkE ty
      unless (sbt == sbt') $ throwInternal "Scalar type mismatch"
      return $ VectorIdx tbl' i' ty'
    VectorSubref ref i ty -> do
      ref' <- checkE ref
      RefTy _ (TabTy _ b (BaseTy (Scalar sbt))) <- return $ getType ref'
      i' <- i |: binderType b
      ty'@(BaseTy (Vector _ sbt')) <- checkE ty
      unless (sbt == sbt') $ throwInternal "Scalar type mismatch"
      return $ VectorSubref ref' i' ty'

checkHof :: IRRep r => EffTy r o -> Hof r i -> TyperM r i o (Hof r o)
checkHof (EffTy effs reqTy) = \case
  For dir ixTy f -> do
    IxType t d <- checkE ixTy
    LamExpr (UnaryNest b) body <- return f
    TyCon (TabPi tabTy) <- return reqTy
    checkBinderType t b \b' -> do
      resultTy <- checkInstantiation (sink tabTy) [toAtom $ binderVar b']
      body' <- checkWithEffTy (EffTy (sink effs) resultTy) body
      return $ For dir (IxType t d) (LamExpr (UnaryNest b') body')
  While body -> do
    let effTy = EffTy effs (BaseTy $ Scalar Word8Type)
    checkTypesEq reqTy UnitTy
    While <$> checkWithEffTy effTy body
  Linearize f x -> do
    (x', xTy) <- checkAndGetType x
    LamExpr (UnaryNest b) body <- return f
    checkBinderType xTy b \b' -> do
      PairTy resultTy fLinTy <- sinkM reqTy
      body' <- checkWithEffTy (EffTy Pure resultTy) body
      checkTypesEq fLinTy (toType $ nonDepPiType [sink xTy] Pure resultTy)
      return $ Linearize (LamExpr (UnaryNest b') body') x'
  Transpose f x -> do
    (x', xTy) <- checkAndGetType x
    LamExpr (UnaryNest b) body <- return f
    checkB b \b' -> do
      body' <- checkWithEffTy (EffTy Pure (sink xTy)) body
      checkTypesEq (sink $ binderType b') (sink reqTy)
      return $ Transpose (LamExpr (UnaryNest b') body') x'
  RunReader r f -> do
    (r', rTy) <- checkAndGetType r
    f' <- checkRWSAction reqTy rTy effs Reader f
    return $ RunReader r' f'
  RunWriter d bm f -> do
    -- XXX: We can't verify compatibility between the base monoid and f, because
    --      the only way in which they are related in the runAccum definition is via
    --      the AccumMonoid typeclass. The frontend constraints should be sufficient
    --      to ensure that only well typed programs are accepted, but it is a bit
    --      disappointing that we cannot verify that internally. We might want to consider
    --      e.g. only disabling this check for prelude.
    bm' <- checkE bm
    PairTy resultTy accTy <- return reqTy
    f' <- checkRWSAction resultTy accTy effs Writer f
    d' <- case d of
      Nothing -> return Nothing
      Just dest -> do
        dest' <- dest |: RawRefTy accTy
        declareEff effs InitEffect
        return $ Just dest'
    return $ RunWriter d' bm' f'
  RunState d s f -> do
    (s', sTy) <- checkAndGetType s
    PairTy resultTy sTy' <- return reqTy
    checkTypesEq sTy sTy'
    f' <- checkRWSAction resultTy sTy effs State f
    d' <- case d of
      Nothing -> return Nothing
      Just dest -> do
        declareEff effs InitEffect
        Just <$> dest |: RawRefTy sTy
    return $ RunState d' s' f'
  RunIO   body -> RunIO   <$> checkWithEffTy (EffTy (extendEffect IOEffect   effs) reqTy) body
  RunInit body -> RunInit <$> checkWithEffTy (EffTy (extendEffect InitEffect effs) reqTy) body
  CatchException reqTy' body -> do
    reqTy'' <- checkE reqTy'
    checkTypesEq reqTy reqTy''
    -- TODO: take more care in unpacking Maybe
    TyCon (NewtypeTyCon (UserADTType _ _ (TyConParams _ [ty]))) <- return reqTy''
    Just ty' <- return $ toMaybeType ty
    body' <- checkWithEffTy (EffTy (extendEffect ExceptionEffect effs) ty') body
    return $ CatchException reqTy'' body'

instance IRRep r => CheckableWithEffects r (DAMOp r) where
  checkWithEffects effs = \case
    Seq effAnn dir ixTy carry lam -> do
      LamExpr (UnaryNest b) body <- return lam
      effAnn' <- checkE effAnn
      checkExtends effs effAnn'
      ixTy' <- checkE ixTy
      (carry', carryTy') <- checkAndGetType carry
      let badCarry = throwInternal $ "Seq carry should be a product of raw references, got: " ++ pprint carryTy'
      case carryTy' of
        TyCon (ProdType refTys) -> forM_ refTys \case RawRefTy _ -> return (); _ -> badCarry
        _ -> badCarry
      let binderReqTy = PairTy (ixTypeType ixTy') carryTy'
      checkBinderType binderReqTy b \b' -> do
        body' <- checkWithEffTy (EffTy (sink effAnn') UnitTy) body
        return $ Seq effAnn' dir ixTy' carry' $ LamExpr (UnaryNest b') body'
    RememberDest effAnn d lam -> do
      LamExpr (UnaryNest b) body <- return lam
      effAnn' <- checkE effAnn
      checkExtends effs effAnn'
      (d', dTy@(RawRefTy _)) <- checkAndGetType d
      checkBinderType dTy b \b' -> do
        body' <- checkWithEffTy (EffTy (sink effAnn') UnitTy) body
        return $ RememberDest effAnn' d' $ LamExpr (UnaryNest b') body'
    AllocDest ty -> AllocDest <$> checkE ty
    Place ref val -> do
      val' <- checkE val
      ref' <- ref |: RawRefTy (getType val')
      declareEff effs InitEffect
      return $ Place ref' val'
    Freeze ref -> do
      ref' <- checkE ref
      RawRefTy _ <- return $ getType ref'
      return $ Freeze ref'

checkLamExpr :: IRRep r => PiType r o -> LamExpr r i -> TyperM r i o (LamExpr r o)
checkLamExpr piTy (LamExpr bs body) =
  checkB bs \bs' -> do
    effTy <- checkInstantiation (sink piTy) (toAtom <$> bindersVars bs')
    body' <- checkWithEffTy effTy body
    return $ LamExpr bs' body'

checkDecls
  :: IRRep r
  => EffectRow r o -> Decls r i i'
  -> (forall o'. DExt o o' => Decls r o o' -> TyperM r i' o' a)
  -> TyperM r i o a
checkDecls _ Empty cont = getDistinct >>= \Distinct -> cont Empty
checkDecls effs (Nest (Let b (DeclBinding ann expr)) decls) cont = do
  rhs <- DeclBinding ann <$> checkWithEffects effs expr
  withFreshBinder (getNameHint b) rhs \(b':>_) -> do
    extendRenamer (b@>binderName b') do
      let decl' = Let b' rhs
      checkDecls (sink effs) decls \decls' -> cont $ Nest decl' decls'

checkRWSAction
  :: IRRep r => Type r o -> Type r o -> EffectRow r o
  -> RWS -> LamExpr r i -> TyperM r i o (LamExpr r o)
checkRWSAction resultTy referentTy effs rws f = do
  BinaryLamExpr bH bR body <- return f
  checkBinderType (TyCon HeapType) bH \bH' -> do
    let h = toAtom $ binderVar bH'
    let refTy = RefTy h (sink referentTy)
    checkBinderType refTy bR \bR' -> do
      let effs' = extendEffect (RWSEffect rws $ sink h) (sink effs)
      body' <- checkWithEffTy (EffTy effs' (sink resultTy)) body
      return $ BinaryLamExpr bH' bR' body'

checkProject :: (IRRep r) => Int -> Atom r o -> TyperM r i o (Type r o)
checkProject i x = case getType x of
  TyCon (ProdType tys) -> return $ tys !! i
  TyCon (DepPairTy t) | i == 0 -> return $ depPairLeftTy t
  TyCon (DepPairTy t) | i == 1 -> do
    xFst <- reduceProj 0 x
    checkInstantiation t [xFst]
  xTy -> throwInternal $ "Not a product type:" ++ pprint xTy

checkTabApp :: (IRRep r) => Type r o -> Atom r o -> TyperM r i o (Type r o)
checkTabApp ty i = do
  TyCon (TabPi tabTy) <- return ty
  checkInstantiation tabTy [i]

checkInstantiation
  :: forall r e body i o .
     (IRRep r, SinkableE body, SubstE AtomSubstVal body, ToBindersAbs e body r)
  => e o -> [Atom r o] -> TyperM r i o (body o)
checkInstantiation abTop xsTop = do
  Abs bs body <- return $ toAbs abTop
  go (Abs bs body) xsTop
 where
  go :: Abs (Nest (Binder r)) body o' -> [Atom r o'] -> TyperM r i o' (body o')
  go (Abs Empty body) [] = return body
  go (Abs (Nest b bs) body) (x:xs) = do
    checkTypesEq (getType x) (binderType b)
    rest <- applySubst (b@>SubstVal x) (Abs bs body)
    go rest xs
  go _ _ = throwInternal "Wrong number of args"

checkIntBaseType :: Fallible m => BaseType -> m ()
checkIntBaseType t = case t of
  Scalar sbt   -> checkSBT sbt
  Vector _ sbt -> checkSBT sbt
  _ -> notInt
  where
    checkSBT sbt = case sbt of
      Int64Type  -> return ()
      Int32Type  -> return ()
      Word8Type  -> return ()
      Word32Type -> return ()
      Word64Type -> return ()
      _          -> notInt
    notInt = throwInternal $
      "Expected a fixed-width scalar integer type, but found: " ++ pprint t

checkFloatBaseType :: Fallible m => BaseType -> m ()
checkFloatBaseType t = case t of
  Scalar sbt   -> checkSBT sbt
  Vector _ sbt -> checkSBT sbt
  _            -> notFloat
  where
    checkSBT sbt = case sbt of
      Float64Type -> return ()
      Float32Type -> return ()
      _           -> notFloat
    notFloat = throwInternal $
      "Expected a fixed-width scalar floating-point type, but found: " ++ pprint t

checkValidCast :: (Fallible1 m, IRRep r) => Type r n -> Type r n -> m n ()
checkValidCast (TyCon (BaseType l)) (TyCon (BaseType r)) = checkValidBaseCast l r
checkValidCast sourceTy destTy =
  throwInternal $ "Can't cast " ++ pprint sourceTy ++ " to " ++ pprint destTy

checkValidBaseCast :: Fallible m => BaseType -> BaseType -> m ()
checkValidBaseCast (PtrType _) (PtrType _) = return ()
checkValidBaseCast (PtrType _) (Scalar Int64Type) = return ()
checkValidBaseCast (Scalar Int64Type) (PtrType _) = return ()
checkValidBaseCast (Scalar _) (Scalar _) = return ()
checkValidBaseCast sourceTy@(Vector sourceSizes _) destTy@(Vector destSizes _) =
  assertEq sourceSizes destSizes $ "Can't cast " ++ pprint sourceTy ++ " to " ++ pprint destTy
checkValidBaseCast sourceTy destTy =
  throwInternal $ "Can't cast " ++ pprint sourceTy ++ " to " ++ pprint destTy

scalarOrVectorLike :: Fallible m => BaseType -> ScalarBaseType -> m BaseType
scalarOrVectorLike x sbt = case x of
  Scalar _ -> return $ Scalar sbt
  Vector sizes _ -> return $ Vector sizes sbt
  _ -> throwInternal $ "only scalar or vector base types should occur here"

data ArgumentType = SomeFloatArg | SomeIntArg | SomeUIntArg

checkOpArgType :: Fallible m => ArgumentType -> BaseType -> m ()
checkOpArgType argTy x =
  case argTy of
    SomeIntArg   -> checkIntBaseType   x
    SomeUIntArg  -> do x' <- scalarOrVectorLike x Word8Type
                       assertEq x x' ""
    SomeFloatArg -> checkFloatBaseType x

checkBinOp :: Fallible m => BinOp -> BaseType -> BaseType -> m ()
checkBinOp op x y = do
  checkOpArgType argTy x
  assertEq x y ""
  where
    argTy = case op of
      IAdd   -> ia;  ISub   -> ia
      IMul   -> ia;  IDiv   -> ia
      IRem   -> ia;
      ICmp _ -> ia
      FAdd   -> fa;  FSub   -> fa
      FMul   -> fa;  FDiv   -> fa;
      FPow   -> fa
      FCmp _ -> fa
      BAnd   -> ia;  BOr    -> ia
      BXor   -> ia
      BShL   -> ia;  BShR   -> ia
      where
        ia = SomeIntArg; fa = SomeFloatArg

checkUnOp :: Fallible m => UnOp -> BaseType -> m ()
checkUnOp op x = checkOpArgType argTy x
  where
    argTy = case op of
      Exp              -> f
      Exp2             -> f
      Log              -> f
      Log2             -> f
      Log10            -> f
      Log1p            -> f
      Sin              -> f
      Cos              -> f
      Tan              -> f
      Sqrt             -> f
      Floor            -> f
      Ceil             -> f
      Round            -> f
      LGamma           -> f
      Erf              -> f
      Erfc             -> f
      FNeg             -> f
      BNot             -> u
      where
        u = SomeUIntArg; f = SomeFloatArg;

-- === effects ===

instance IRRep r => CheckableE r (EffectRow r) where
  checkE (EffectRow effs effTail) = do
    effs' <- eSetFromList <$> forM (eSetToList effs) \eff -> case eff of
      RWSEffect rws v -> do
        v' <- v |: TyCon HeapType
        return $ RWSEffect rws v'
      ExceptionEffect -> return ExceptionEffect
      IOEffect        -> return IOEffect
      InitEffect      -> return InitEffect
    effTail' <- case effTail of
      NoTail -> return NoTail
      EffectRowTail v -> do
        v' <- renameM v
        ty <- getType <$> lookupAtomName (atomVarName v')
        checkTypesEq EffKind ty
        return $ EffectRowTail v'
    return $ EffectRow effs' effTail'

declareEff :: IRRep r => EffectRow r o -> Effect r o -> TyperM r i o ()
declareEff allowedEffs eff = checkExtends allowedEffs $ OneEffect eff

checkEffTy :: IRRep r => EffectRow r o -> EffTy r i -> TyperM r i o (EffTy r o)
checkEffTy allowedEffs effTy = do
  EffTy declaredEffs resultTy <- checkE effTy
  checkExtends allowedEffs declaredEffs
  return $ EffTy declaredEffs resultTy
