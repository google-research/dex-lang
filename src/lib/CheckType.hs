-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module CheckType (
  CheckableE (..), CheckableB (..),
  checkTypes, checkTypesM, checkHasType,
  checkExtends, tryGetType, isData, asFFIFunType
  ) where

import Prelude hiding (id)
import Control.Category ((>>>))
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State.Class
import Data.Maybe (isJust)
import Data.Foldable (toList)
import Data.Functor

import CheapReduction
import Core
import Err
import IRVariants
import MTL1
import Name
import Subst
import PPrint ()
import QueryType hiding (HasType, getTypeE)
import Types.Core
import Types.Imp
import Types.Primitives
import Types.Source

-- === top-level API ===

checkTypes :: (EnvReader m, CheckableE r e) => e n -> m n (Except ())
checkTypes e = liftTyperT $ checkE e
{-# SCC checkTypes #-}

checkTypesM :: (EnvReader m, Fallible1 m, CheckableE r e) => e n -> m n ()
checkTypesM e = liftExcept =<< checkTypes e

tryGetType :: (EnvReader m, Fallible1 m, HasType r e) => e n -> m n (Type r n)
tryGetType e = liftExcept =<< liftTyperT (getTypeE e)
{-# INLINE tryGetType #-}

checkHasType :: (EnvReader m, HasType r e) => e n -> Type r n -> m n (Except ())
checkHasType e ty = liftTyperT $ e |: ty
{-# INLINE checkHasType #-}

-- === the type checking/querying monad ===

-- TODO: not clear why we need the explicit `Monad2` here since it should
-- already be a superclass, transitively, through both Fallible2 and
-- MonadAtomSubst.
class ( Monad2 m, Fallible2 m, SubstReader Name m
      , EnvReader2 m, EnvExtender2 m)
     => Typer (m::MonadKind2) (r::IR) | m -> r where
  affineUsed :: AtomName r o -> m i o ()
  parallelAffines_ :: [m i o ()] -> m i o ()

newtype TyperT (m::MonadKind) (r::IR) (i::S) (o::S) (a :: *) =
  TyperT { runTyperT' :: SubstReaderT Name (StateT1 (NameMap (AtomNameC r) Int) (EnvReaderT m)) i o a }
  deriving ( Functor, Applicative, Monad
           , SubstReader Name
           , MonadFail
           , Fallible
           , ScopeReader
           , EnvReader, EnvExtender)

liftTyperT :: (EnvReader m', Fallible m) => TyperT m r n n a -> m' n (m a)
liftTyperT cont =
  liftEnvReaderT $
    flip evalStateT1 mempty $
      runSubstReaderT idSubst $
        runTyperT' cont
{-# INLINE liftTyperT #-}

instance Fallible m => Typer (TyperT m r) r where
  -- I can't make up my mind whether a `Seq` loop should be allowed to
  -- close over a dest from an enclosing scope.  Status quo permits this.
  affineUsed name = TyperT $ do
    affines <- get
    case lookupNameMap name affines of
      Just n -> if n > 0 then
                  throw TypeErr $ "Affine name " ++ pprint name ++ " used " ++ show (n + 1) ++ " times."
                else
                  put $ insertNameMap name (n + 1) affines
      Nothing -> put $ insertNameMap name 1 affines
  parallelAffines_ actions = TyperT $ do
    -- This method permits using an affine variable in each branch of a `case`.
    -- We check each `case` branch in isolation, detecting affine overuse within
    -- the branch; then we check whether the union of the variables used in the
    -- branches reuses a variable from outside that it shouldn't.
    -- This has the down-side of localizing such an error to the case rather
    -- than to the offending in-branch use, but that can be improved later.
    affines <- get
    isolateds <- forM actions \act -> do
      put mempty
      runTyperT' act
      get
    put affines
    forM_ (toListNameMap $ unionsWithNameMap max isolateds) \(name, ct) ->
      case ct of
        0 -> return ()
        1 -> runTyperT' $ affineUsed name
        _ -> error $ "Unexpected multi-used affine name " ++ show name ++ " from case branches."

-- === typeable things ===

class (SinkableE e, RenameE e, PrettyE e, IRRep r) => HasType (r::IR) (e::E) | e -> r where
  getTypeE   :: Typer m r => e i -> m i o (Type r o)

checkTypeE :: (HasType r e, Typer m r) => Type r o -> e i -> m i o (e o)
checkTypeE reqTy e = do
  e |: reqTy
  renameM e

checkTypesEq :: (Typer m r, IRRep r) => Type r o -> Type r o -> m i o ()
checkTypesEq reqTy ty = alphaEq reqTy ty >>= \case
  True  -> return ()
  False -> {-# SCC typeNormalization #-} do
    reqTy' <- cheapNormalize reqTy
    ty'    <- cheapNormalize ty
    alphaEq reqTy' ty' >>= \case
      True  -> return ()
      False -> throw TypeErr $ pprint reqTy' ++ " != " ++ pprint ty'
{-# INLINE checkTypesEq #-}

class (SinkableE e) => CheckableE (r::IR) (e::E) | e -> r where
  checkE :: Typer m r => e i -> m i o ()

class HasNamesB b => CheckableB (r::IR) (b::B) | b -> r where
  checkB :: Typer m r
         => b i i'
         -> (forall o'. Ext o o' => b o o' -> m i' o' ())
         -> m i o ()

checkBEvidenced :: (CheckableB r b, Typer m r)
                => b i i'
                -> (forall o'. ExtEvidence o o' -> b o o' -> m i' o' ())
                -> m i o ()
checkBEvidenced b cont = checkB b \b' -> cont getExtEvidence b'

-- === convenience functions ===

infixr 7 |:
(|:) :: (Typer m r, HasType r e) => e i -> Type r o -> m i o ()
(|:) x reqTy = do
  ty <- getTypeE x
  -- TODO: Write an alphaEq variant that works modulo an equivalence
  -- relation on names.
  checkTypesEq reqTy ty

instance CheckableE CoreIR SourceMap where
  checkE _ = return ()

instance (CheckableE r e1, CheckableE r e2) => CheckableE r (PairE e1 e2) where
  checkE (PairE e1 e2) = checkE e1 >> checkE e2

instance (CheckableE r e1, CheckableE r e2) => CheckableE r (EitherE e1 e2) where
  checkE ( LeftE e) = checkE e
  checkE (RightE e) = checkE e

instance (CheckableB r b, CheckableE r e) => CheckableE r (Abs b e) where
  checkE (Abs b e) = checkB b \_ -> checkE e

instance (IRRep r) => CheckableE r (LamExpr r) where
  checkE (LamExpr bs body) = checkB bs \_ ->  void $ getTypeE body

instance (IRRep r) => CheckableE r (DestLamExpr r) where
  checkE (DestLamExpr bs block) = checkB bs \_ -> do
    DestBlock destb body <- return block
    checkB destb \_ -> void $ getTypeE body

-- === type checking core ===

instance IRRep r => CheckableE r (Atom r) where
  checkE atom = void $ getTypeE atom

instance IRRep r => CheckableE r (Type r) where
  checkE atom = void $ getTypeE atom

instance IRRep r => HasType r (AtomName r) where
  getTypeE name = do
    name' <- renameM name
    atomBindingType <$> lookupAtomName name'
  {-# INLINE getTypeE #-}

instance IRRep r => CheckableE r (Block r) where
  checkE block = void $ getTypeE block

instance IRRep r => HasType r (Atom r) where
  getTypeE atom = case atom of
    Var name -> do
      ty <- getTypeE name
      case ty of
        RawRefTy _ -> renameM name >>= affineUsed
        _ -> return ()
      return ty
    Lam (CoreLamExpr piTy lam) -> do
      Pi piTy' <- checkTypeE TyKind $ Pi piTy
      checkCoreLam piTy' lam
      return $ Pi piTy'
    DepPair l r ty -> do
      ty' <- checkTypeE TyKind ty
      l'  <- checkTypeE (depPairLeftTy ty') l
      rTy <- instantiateDepPairTy ty' l'
      r |: rTy
      return $ DepPairTy ty'
    Con con  -> typeCheckPrimCon con
    Eff eff  -> checkE eff $> EffKind
    PtrVar v -> renameM v >>= lookupEnv >>= \case
      PtrBinding ty _ -> return $ PtrTy ty
    DictCon dictExpr -> getTypeE dictExpr
    RepValAtom (RepVal ty _) -> renameM ty
    NewtypeCon con x -> NewtypeTyCon <$> typeCheckNewtypeCon con x
    SimpInCore x -> getTypeE x
    DictHole _ ty _ -> checkTypeE TyKind ty
    ProjectElt UnwrapNewtype x -> do
      NewtypeTyCon con <- getTypeE x
      snd <$> unwrapNewtypeType con
    ProjectElt (ProjectProduct i) x -> do
      ty <- getTypeE x
      case ty of
        ProdTy tys -> return $ tys !! i
        DepPairTy t | i == 0 -> return $ depPairLeftTy t
        DepPairTy t | i == 1 -> do
          x' <- renameM x
          xFst <- normalizeProj (ProjectProduct 0) x'
          instantiateDepPairTy t xFst
        _ -> throw TypeErr $ "Not a product type:" ++ pprint ty
    TypeAsAtom ty -> getTypeE ty

instance IRRep r => HasType r (Type r) where
  getTypeE atom = case atom of
    Pi piType -> getTypeE piType
    TabPi piType -> getTypeE piType
    NewtypeTyCon t   -> typeCheckNewtypeTyCon t
    TC tyCon -> typeCheckPrimTC  tyCon
    DepPairTy ty -> getTypeE ty
    DictTy (DictType _ className params) -> do
      ClassDef _ _ _ paramBs _ _ <- renameM className >>= lookupClassDef
      params' <- mapM renameM params
      checkArgTys paramBs params'
      return TyKind
    TyVar v -> getTypeE v
    ProjectEltTy UnwrapNewtype x -> do
      NewtypeTyCon con <- getTypeE x
      snd <$> unwrapNewtypeType con
    ProjectEltTy (ProjectProduct i) x -> do
      ty <- getTypeE x
      case ty of
        ProdTy tys -> return $ tys !! i
        DepPairTy t | i == 0 -> return $ depPairLeftTy t
        DepPairTy t | i == 1 -> do
          x' <- renameM x
          xFst <- normalizeProj (ProjectProduct 0) x'
          instantiateDepPairTy t xFst
        _ -> throw TypeErr $ "Not a product type:" ++ pprint ty

instance HasType CoreIR SimpInCore where
  getTypeE = \case
    LiftSimp ty _ -> renameM ty  -- TODO: check
    LiftSimpFun piTy _ -> Pi <$> renameM piTy -- TODO: check
    ACase _ _ ty -> renameM ty -- TODO: check
    TabLam t _ -> TabPi <$> renameM t -- TODO: check

instance (ToBinding ann c, Color c, CheckableE r ann) => CheckableB r (BinderP c ann) where
  checkB (b:>ann) cont = do
    checkE ann
    ann' <- renameM ann
    withFreshBinder (getNameHint b) ann' \b' ->
      extendRenamer (b@>binderName b') $
        cont b'

instance (BindsNames b, CheckableB r b) => CheckableB r (WithExpl b) where
  checkB (WithExpl expl b) cont = checkB b \b' -> cont (WithExpl expl b')

typeCheckExpr :: (Typer m r, IRRep r) => EffectRow r o -> Expr r i -> m i o (Type r o)
typeCheckExpr effs expr = case expr of
  App f xs -> do
    fTy <- getTypeE f
    checkApp effs fTy $ toList xs
  TabApp f xs -> do
    fTy <- getTypeE f
    checkTabApp fTy xs
  -- TODO: check!
  TopApp f xs -> do
    PiType bs _ resultTy <- getTypeTopFun =<< renameM f
    xs' <- mapM renameM xs
    checkedApplyNaryAbs (Abs bs resultTy) xs'
  Atom x   -> getTypeE x
  PrimOp op -> typeCheckPrimOp effs op
  Case e alts resultTy caseEffs -> do
    caseEffs' <- renameM caseEffs
    resultTy'  <- renameM resultTy
    checkCase e alts resultTy' caseEffs'
    checkExtends effs caseEffs'
    return resultTy'
  ApplyMethod dict i args -> do
    DictTy (DictType _ className params) <- getTypeE dict
    def@(ClassDef _ _ _ paramBs classBs methodTys) <- lookupClassDef className
    let methodTy = methodTys !! i
    superclassDicts <- getSuperclassDicts def <$> renameM dict
    let subst = (    paramBs @@> map SubstVal params
                 <.> classBs @@> map SubstVal superclassDicts)
    methodTy' <- applySubst subst methodTy
    checkApp effs (Pi methodTy') args
  TabCon _ ty xs -> do
    ty'@(TabPi (TabPiType b restTy)) <- checkTypeE TyKind ty
    case fromConstAbs (Abs b restTy) of
      HoistSuccess elTy -> forM_ xs (|: elTy)
      -- XXX: in the dependent case we don't check that the element types
      -- match the annotation because that would require concretely evaluating
      -- each index from the ix dict.
      HoistFailure _    -> forM_ xs checkE
    return ty'

instance IRRep r => HasType r (Block r) where
  getTypeE = \case
    Block NoBlockAnn Empty atom -> getTypeE atom
    Block (BlockAnn reqTy effs') decls result -> do
      effs <- renameM effs'
      reqTy' <- renameM reqTy
      go effs reqTy' decls result
      return reqTy'
    Block _ _ _ -> error "impossible"
   where
    go :: Typer m r => EffectRow r o -> Type r o -> Nest (Decl r) i i' -> Atom r i' -> m i o ()
    go _ reqTy Empty result = result |: reqTy
    go effs reqTy (Nest (Let b rhs@(DeclBinding _ tyAnn expr)) decls) result = do
      tyAnn |: TyKind
      tyAnn' <- renameM tyAnn
      tyExpr <- typeCheckExpr effs expr
      checkTypesEq tyAnn' tyExpr
      rhs' <- renameM rhs
      withFreshBinder (getNameHint b) rhs' \(b':>_) -> do
        extendRenamer (b@>binderName b') do
          go (sink effs) (sink reqTy) decls result

instance CheckableE CoreIR TyConParams where
  checkE (TyConParams _ params) = mapM_ checkE params

dictExprType :: Typer m CoreIR => DictExpr i -> m i o (CType o)
dictExprType e = case e of
  InstanceDict instanceName args -> do
    instanceName' <- renameM instanceName
    InstanceDef className bs params _ <- lookupInstanceDef instanceName'
    ClassDef sourceName _ _ _ _ _ <- lookupClassDef className
    args' <- mapM renameM args
    checkArgTys bs args'
    ListE params' <- applySubst (bs@@>(SubstVal<$>args')) (ListE params)
    return $ DictTy $ DictType sourceName className params'
  InstantiatedGiven given args -> do
    givenTy <- getTypeE given
    checkApp Pure givenTy (toList args)
  SuperclassProj d i -> do
    DictTy (DictType _ className params) <- getTypeE d
    ClassDef _ _ _ bs superclasses _ <- lookupClassDef className
    let scType = getSuperclassType REmpty superclasses i
    checkedApplyNaryAbs (Abs bs scType) params
  IxFin n -> do
    n' <- checkTypeE NatTy n
    liftM DictTy $ ixDictType $ NewtypeTyCon $ Fin n'
  DataData ty -> DictTy <$> (dataDictType =<< checkTypeE TyKind ty)

instance HasType CoreIR DictExpr where
  getTypeE e = dictExprType e

instance IRRep r => HasType r (DepPairType r) where
  getTypeE (DepPairType _ b ty) = do
    checkB b \_ -> ty |: TyKind
    return TyKind

instance HasType CoreIR CorePiType where
  getTypeE (CorePiType _ bs eff resultTy) = do
    checkB bs \_ -> do
      void $ checkE eff
      resultTy|:TyKind
    return TyKind

instance IRRep r => CheckableE r (IxType r) where
  checkE (IxType t _) = checkE t

instance IRRep r => HasType r (TabPiType r) where
  getTypeE (TabPiType b resultTy) = do
    checkB b \_ -> resultTy|:TyKind
    return TyKind

instance (BindsNames b, CheckableB r b) => CheckableB r (Nest b) where
  checkB nest cont = case nest of
    Empty -> cont Empty
    Nest b rest ->
      checkBEvidenced b \ext1 b' ->
        checkBEvidenced rest \ext2 rest' ->
          withExtEvidence (ext1 >>> ext2) $
            cont $ Nest b' rest'

checkCoreLam :: Typer m CoreIR => CorePiType o -> LamExpr CoreIR i -> m i o ()
checkCoreLam (CorePiType _ Empty effs resultTy) (LamExpr Empty body) = do
  resultTy' <- checkBlockWithEffs effs body
  checkTypesEq resultTy resultTy'
checkCoreLam (CorePiType expl (Nest piB piBs) effs resultTy) (LamExpr (Nest lamB lamBs) body) = do
  argTy <- renameM $ binderType lamB
  checkTypesEq (binderType piB) argTy
  withFreshBinder (getNameHint lamB) argTy \b -> do
    piTy <- applyRename (piB@>binderName b) (CorePiType expl piBs effs resultTy)
    extendRenamer (lamB@>binderName b) do
      checkCoreLam piTy (LamExpr lamBs body)
checkCoreLam _ _ = throw TypeErr "zip error"

typeCheckPrimTC :: (Typer m r, IRRep r) => TC r i -> m i o (Type r o)
typeCheckPrimTC tc = case tc of
  BaseType _       -> return TyKind
  ProdType tys     -> mapM_ (|:TyKind) tys >> return TyKind
  SumType  cs      -> mapM_ (|:TyKind) cs  >> return TyKind
  RefType r a      ->  r|:TC HeapType >> a|:TyKind >> return TyKind
  TypeKind         -> return TyKind
  HeapType         -> return TyKind

typeCheckPrimCon :: (Typer m r, IRRep r) => Con r i -> m i o (Type r o)
typeCheckPrimCon con = case con of
  Lit l -> return $ BaseTy $ litType l
  ProdCon xs -> ProdTy <$> mapM getTypeE xs
  SumCon tys tag payload -> do
    caseTys <- traverse renameM tys
    unless (0 <= tag && tag < length caseTys) $ throw TypeErr "Invalid SumType tag"
    payload |: (caseTys !! tag)
    return $ SumTy caseTys
  HeapVal -> return $ TC HeapType

typeCheckNewtypeCon
  :: Typer m CoreIR => NewtypeCon i -> CAtom i -> m i o (NewtypeTyCon o)
typeCheckNewtypeCon con x = case con of
  NatCon   -> x|:IdxRepTy          >> return Nat
  FinCon n -> n|:NatTy >> x|:NatTy >> renameM (Fin n)
  UserADTData d params -> do
    d' <- renameM d
    def@(TyConDef sn _ _) <- lookupTyCon d'
    params' <- renameM params
    void $ checkedInstantiateTyConDef def params'
    return $ UserADTType sn d' params'

typeCheckNewtypeTyCon :: Typer m CoreIR => NewtypeTyCon i -> m i o (CType o)
typeCheckNewtypeTyCon = \case
  Nat        -> return TyKind
  Fin n      -> checkTypeE NatTy n >> return TyKind
  EffectRowKind    -> return TyKind
  UserADTType _ d params -> do
    def <- lookupTyCon =<< renameM d
    params' <- renameM params
    void $ checkedInstantiateTyConDef def params'
    return TyKind

typeCheckPrimOp :: (Typer m r, IRRep r) => EffectRow r o -> PrimOp r i -> m i o (Type r o)
typeCheckPrimOp effs op = case op of
  Hof  hof -> typeCheckPrimHof effs hof
  VectorOp vOp -> typeCheckVectorOp vOp
  BinOp binop x y -> do
    xTy <- typeCheckBaseType x
    yTy <- typeCheckBaseType y
    TC <$> BaseType <$> checkBinOp binop xTy yTy
  UnOp  unop  x -> do
    xTy <- typeCheckBaseType x
    TC <$> BaseType <$> checkUnOp unop xTy
  MiscOp x -> typeCheckMiscOp effs x
  MemOp x -> typeCheckMemOp effs x
  DAMOp op' -> typeCheckDAMOp effs op'
  UserEffectOp op' -> typeCheckUserEffect op'
  RefOp ref m -> do
    TC (RefType h s) <- getTypeE ref
    case m of
      MGet      ->           declareEff effs (RWSEffect State  h) $> s
      MPut  x   -> x|:s   >> declareEff effs (RWSEffect State  h) $> UnitTy
      MAsk      ->           declareEff effs (RWSEffect Reader h) $> s
      MExtend _ x -> x|:s >> declareEff effs (RWSEffect Writer h) $> UnitTy
      IndexRef i -> do
        TabTy (b:>IxType iTy _) eltTy <- return s
        i' <- checkTypeE iTy i
        eltTy' <- applyAbs (Abs b eltTy) (SubstVal i')
        return $ TC $ RefType h eltTy'
      ProjRef p -> TC . RefType h <$> case p of
        ProjectProduct i -> do
          ProdTy tys <- return s
          return $ tys !! i
        UnwrapNewtype -> do
          NewtypeTyCon tc <- return s
          snd <$> unwrapNewtypeType tc

typeCheckMemOp :: forall r m i o. (Typer m r, IRRep r) => EffectRow r o -> MemOp r i -> m i o (Type r o)
typeCheckMemOp effs = \case
  IOAlloc n -> do
    n |: IdxRepTy
    declareEff effs IOEffect
    return $ PtrTy (CPU, Scalar Word8Type)
  IOFree ptr -> do
    PtrTy _ <- getTypeE ptr
    declareEff effs IOEffect
    return UnitTy
  PtrOffset arr off -> do
    PtrTy (a, b) <- getTypeE arr
    off |: IdxRepTy
    return $ PtrTy (a, b)
  PtrLoad ptr -> do
    PtrTy (_, t) <- getTypeE ptr
    declareEff effs IOEffect
    return $ BaseTy t
  PtrStore ptr val -> do
    PtrTy (_, t)  <- getTypeE ptr
    val |: BaseTy t
    declareEff effs IOEffect
    return $ UnitTy

typeCheckMiscOp :: forall r m i o. (Typer m r, IRRep r) => EffectRow r o -> MiscOp r i -> m i o (Type r o)
typeCheckMiscOp effs = \case
  Select p x y -> do
    p |: (BaseTy $ Scalar Word8Type)
    ty <- getTypeE x
    y |: ty
    return ty
  CastOp t@(TyVar _) _ -> t |: TyKind >> renameM t
  CastOp destTy e -> do
    sourceTy' <- getTypeE e
    destTy |: TyKind
    destTy' <- renameM destTy
    checkValidCast sourceTy' destTy'
    return $ destTy'
  BitcastOp t@(TyVar _) _ -> t |: TyKind >> renameM t
  BitcastOp destTy e -> do
    sourceTy <- getTypeE e
    case (destTy, sourceTy) of
      (BaseTy dbt@(Scalar _), BaseTy sbt@(Scalar _)) | sizeOf sbt == sizeOf dbt ->
        return $ BaseTy dbt
      _ -> throw TypeErr $ "Invalid bitcast: " ++ pprint sourceTy ++ " -> " ++ pprint destTy
  UnsafeCoerce t _ -> renameM t
  GarbageVal t -> renameM t
  SumTag x -> do
    void $ getTypeE x >>= checkSomeSumType
    return TagRepTy
  ToEnum t x -> do
    x |: Word8Ty
    t' <- checkTypeE TyKind t
    cases <- checkSomeSumType t'
    forM_ cases \cty -> checkTypesEq cty UnitTy
    return t'
  OutputStream ->
    return $ BaseTy $ hostPtrTy $ Scalar Word8Type
    where hostPtrTy ty = PtrType (CPU, ty)
  ShowAny x ->
    -- TODO: constrain `ShowAny` to have `HasCore r`
    checkE x >> rawStrType
  ShowScalar x -> do
    BaseTy (Scalar _) <- getTypeE x
    PairTy IdxRepTy <$> rawFinTabType (IdxRepVal showStringBufferSize) CharRepTy
  ThrowError ty -> ty|:TyKind >> renameM ty
  ThrowException ty -> do
    declareEff effs ExceptionEffect
    ty|:TyKind >> renameM ty

checkSomeSumType :: (Typer m r, IRRep r) => Type r o -> m i o [Type r o]
checkSomeSumType = \case
  SumTy cases -> return cases
  NewtypeTyCon con -> do
    (_, SumTy cases) <- unwrapNewtypeType con
    return cases
  t -> error $ "not some sum type: " ++ pprint t

typeCheckVectorOp :: (Typer m r, IRRep r) => VectorOp r i -> m i o (Type r o)
typeCheckVectorOp = \case
  VectorBroadcast v ty -> do
    ty'@(BaseTy (Vector _ sbt)) <- checkTypeE TyKind ty
    v |: BaseTy (Scalar sbt)
    return ty'
  VectorIota ty -> do
    ty'@(BaseTy (Vector _ _)) <- checkTypeE TyKind ty
    return ty'
  VectorSubref ref i ty -> do
    RawRefTy (TabTy b (BaseTy (Scalar sbt))) <- getTypeE ref
    i |: binderType b
    ty'@(BaseTy (Vector _ sbt')) <- checkTypeE TyKind ty
    unless (sbt == sbt') $ throw TypeErr "Scalar type mismatch"
    return $ RawRefTy ty'

typeCheckUserEffect :: Typer m CoreIR => UserEffectOp i -> m i o (CType o)
typeCheckUserEffect = \case
  -- TODO(alex): check the argument
  Resume retTy _argTy -> do
    checkTypeE TyKind retTy
  -- TODO(alex): actually check something here? this is a QueryType copy/paste
  Handle hndName [] body -> do
    hndName' <- renameM hndName
    r <- getTypeE body
    instantiateHandlerType hndName' r []
  -- TODO(alex): implement
  Handle _ _ _  -> error "not implemented"
  Perform eff i -> do
    Eff (OneEffect (UserEffect effName)) <- return eff
    EffectDef _ ops <- renameM effName >>= lookupEffectDef
    let (_, EffectOpType _pol lamTy) = ops !! i
    return lamTy

typeCheckPrimHof :: forall r m i o. (Typer m r, IRRep r) => EffectRow r o -> Hof r i -> m i o (Type r o)
typeCheckPrimHof effs hof = addContext ("Checking HOF:\n" ++ pprint hof) case hof of
  For _ ixDict f -> do
    ixTy <- ixTyFromDict =<< renameM ixDict
    PiType (UnaryNest (b:>argTy)) _ eltTy <- checkLamExpr f
    checkTypesEq (ixTypeType ixTy) argTy
    return $ TabTy (b:>ixTy) eltTy
  While body -> do
    condTy <- getTypeE body
    checkTypesEq (BaseTy $ Scalar Word8Type) condTy
    return UnitTy
  Linearize f x -> do
    PiType (UnaryNest (binder:>a)) Pure b <- checkLamExpr f
    b' <- liftHoistExcept $ hoist binder b
    fLinTy <- Pi <$> nonDepPiType [a] Pure b'
    x |: a
    return $ PairTy b' fLinTy
  Transpose f x -> do
    PiType (UnaryNest (binder:>a)) Pure b <- checkLamExpr f
    b' <- liftHoistExcept $ hoist binder b
    x |: b'
    return a
  RunReader r f -> do
    (resultTy, readTy) <- checkRWSAction effs Reader f
    r |: readTy
    return resultTy
  RunWriter d _ f -> do
    -- XXX: We can't verify compatibility between the base monoid and f, because
    --      the only way in which they are related in the runAccum definition is via
    --      the AccumMonoid typeclass. The frontend constraints should be sufficient
    --      to ensure that only well typed programs are accepted, but it is a bit
    --      disappointing that we cannot verify that internally. We might want to consider
    --      e.g. only disabling this check for prelude.
    (resultTy, accTy) <- checkRWSAction effs Writer f
    case d of
      Nothing -> return ()
      Just dest -> do
        dest |: RawRefTy accTy
        declareEff effs InitEffect
    return $ PairTy resultTy accTy
  RunState d s f -> do
    (resultTy, stateTy) <- checkRWSAction effs State f
    s |: stateTy
    case d of
      Nothing -> return ()
      Just dest -> do
        dest |: RawRefTy stateTy
        declareEff effs InitEffect
    return $ PairTy resultTy stateTy
  RunIO   body -> checkBlockWithEffs  (extendEffect IOEffect   effs) body
  RunInit body -> checkBlockWithEffs  (extendEffect InitEffect effs) body
  CatchException body -> do
    ty <- checkBlockWithEffs (extendEffect ExceptionEffect effs) body
    makePreludeMaybeTy ty

typeCheckDAMOp :: forall r m i o . (Typer m r, IRRep r) => EffectRow r o -> DAMOp r i -> m i o (Type r o)
typeCheckDAMOp effs op = addContext ("Checking DAMOp:\n" ++ show op) case op of
  Seq _ ixDict carry f -> do
    ixTy <- ixTyFromDict =<< renameM ixDict
    carryTy' <- getTypeE carry
    let badCarry = throw TypeErr $ "Seq carry should be a product of raw references, got: " ++ pprint carryTy'
    case carryTy' of
      ProdTy refTys -> forM_ refTys \case RawRefTy _ -> return (); _ -> badCarry
      _ -> badCarry
    PiType (UnaryNest b) _ _ <- checkLamExprWithEffs effs f
    checkTypesEq (PairTy (ixTypeType ixTy) carryTy') (binderType b)
    return carryTy'
  RememberDest d body -> do
    dTy@(RawRefTy _) <- getTypeE d
    PiType (UnaryNest b) _ UnitTy <- checkLamExpr body

    checkTypesEq (binderType b) dTy
    return dTy
  AllocDest ty -> RawRefTy <$> checkTypeE TyKind ty
  Place ref val -> do
    ty <- getTypeE val
    ref |: RawRefTy ty
    declareEff effs InitEffect
    return UnitTy
  Freeze ref -> do
    RawRefTy ty <- getTypeE ref
    return ty

checkLamExpr :: (Typer m r, IRRep r) => LamExpr r i -> m i o (PiType r o)
checkLamExpr (LamExpr bsTop body) = case bsTop of
  Empty -> do
    resultTy <- getTypeE body
    effs <- renameM $ blockEffects body
    return $ PiType Empty effs resultTy
  Nest (b:>ty) bs -> do
    ty' <- checkTypeE TyKind ty
    withFreshBinder (getNameHint b) ty' \b' ->
      extendRenamer (b@>binderName b') do
        PiType bs' eff resultTy <- checkLamExpr (LamExpr bs body)
        return $ PiType (Nest b' bs') eff resultTy

checkLamExprWithEffs :: (Typer m r, IRRep r) => EffectRow r o -> LamExpr r i -> m i o (PiType r o)
checkLamExprWithEffs allowedEffs lam = do
  piTy@(PiType bs effs _) <- checkLamExpr lam
  effs' <- liftHoistExcept $ hoist bs effs
  checkExtends allowedEffs effs'
  return piTy

checkBlockWithEffs :: (Typer m r, IRRep r) => EffectRow r o -> Block r i -> m i o (Type r o)
checkBlockWithEffs allowedEffs block = do
  ty <- getTypeE block
  effs <- renameM $ blockEffects block
  checkExtends allowedEffs effs
  return ty

checkRWSAction :: (Typer m r, IRRep r) => EffectRow r o -> RWS -> LamExpr r i -> m i o (Type r o, Type r o)
checkRWSAction effs rws f = do
  BinaryLamExpr bH bR body <- return f
  renameBinders bH \bH' -> renameBinders bR \bR' -> do
    h <- sinkM $ binderName bH'
    let effs' = extendEffect (RWSEffect rws $ Var h) (sink effs)
    RefTy _ referentTy <- sinkM $ binderType bR'
    resultTy <- checkBlockWithEffs effs' body
    liftM fromPairE $ liftHoistExcept $ hoist (PairB bH' bR') $ PairE resultTy referentTy

checkCase :: (Typer m r, IRRep r) => Atom r i -> [Alt r i] -> Type r o -> EffectRow r o -> m i o ()
checkCase scrut alts resultTy effs = do
  scrutTy <- getTypeE scrut
  altsBinderTys <- checkCaseAltsBinderTys scrutTy
  parallelAffines_ $ zipWith (\alt bs ->
    checkAlt resultTy bs effs alt) alts altsBinderTys

checkCaseAltsBinderTys :: (Fallible1 m, EnvReader m, IRRep r) => Type r n -> m n [Type r n]
checkCaseAltsBinderTys ty = case ty of
  SumTy types -> return types
  NewtypeTyCon t -> case t of
    UserADTType _ defName params -> do
      def <- lookupTyCon defName
      ADTCons cons <- checkedInstantiateTyConDef def params
      return [repTy | DataConDef _ _ repTy _ <- cons]
    _ -> fail msg
  _ -> fail msg
  where msg = "Case analysis only supported on ADTs, not on " ++ pprint ty

checkAlt :: (Typer m r, IRRep r) => Type r o -> Type r o -> EffectRow r o -> Alt r i -> m i o ()
checkAlt resultTyReq bTyReq effs (Abs b body) = do
  bTy <- renameM $ binderType b
  checkTypesEq bTyReq bTy
  renameBinders b \_ -> do
    resultTy <- checkBlockWithEffs (sink effs) body
    checkTypesEq (sink resultTyReq) resultTy

checkApp :: (Typer m r, IRRep r) => EffectRow r o -> Type r o -> [Atom r i] -> m i o (Type r o)
checkApp allowedEffs fTy xs = case fTy of
  Pi (CorePiType _ bs effs resultTy) -> do
    xs' <- mapM renameM xs
    checkArgTys bs xs'
    let subst = bs @@> fmap SubstVal xs'
    PairE effs' resultTy' <- applySubst subst $ PairE effs resultTy
    checkExtends allowedEffs effs'
    return resultTy'
  _ -> throw TypeErr $
    "Not a type: " ++ pprint fTy ++ " (tried to apply it to: " ++ pprint xs ++ ")"

checkTabApp :: (Typer m r, IRRep r) => Type r o -> [Atom r i] -> m i o (Type r o)
checkTabApp ty [] = return ty
checkTabApp ty (i:rest) = do
  TabTy (b :> IxType ixTy _) resultTy <- return ty
  i' <- checkTypeE ixTy i
  resultTy' <- applySubst (b@>SubstVal i') resultTy
  checkTabApp resultTy' rest

checkArgTys
  :: (Typer m r, SubstB AtomSubstVal b, BindsNames b, BindsOneAtomName r b, IRRep r)
  => Nest b o o'
  -> [Atom r o]
  -> m i o ()
checkArgTys Empty [] = return ()
checkArgTys (Nest b bs) (x:xs) = do
  dropSubst $ x |: binderType b
  Abs bs' UnitE <- applySubst (b@>SubstVal x) (EmptyAbs bs)
  checkArgTys bs' xs
checkArgTys _ _ = throw TypeErr $ "wrong number of args"
{-# INLINE checkArgTys #-}

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
    notInt = throw TypeErr $
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
    notFloat = throw TypeErr $
      "Expected a fixed-width scalar floating-point type, but found: " ++ pprint t

checkValidCast :: (Fallible1 m, IRRep r) => Type r n -> Type r n -> m n ()
checkValidCast (BaseTy l) (BaseTy r) = checkValidBaseCast l r
checkValidCast sourceTy destTy =
  throw TypeErr $ "Can't cast " ++ pprint sourceTy ++ " to " ++ pprint destTy

checkValidBaseCast :: Fallible m => BaseType -> BaseType -> m ()
checkValidBaseCast (PtrType _) (PtrType _) = return ()
checkValidBaseCast (PtrType _) (Scalar Int64Type) = return ()
checkValidBaseCast (Scalar Int64Type) (PtrType _) = return ()
checkValidBaseCast (Scalar _) (Scalar _) = return ()
checkValidBaseCast sourceTy@(Vector sourceSizes _) destTy@(Vector destSizes _) =
  assertEq sourceSizes destSizes $ "Can't cast " ++ pprint sourceTy ++ " to " ++ pprint destTy
checkValidBaseCast sourceTy destTy =
  throw TypeErr $ "Can't cast " ++ pprint sourceTy ++ " to " ++ pprint destTy

typeCheckBaseType :: Typer m r => HasType r e => e i -> m i o BaseType
typeCheckBaseType e =
  getTypeE e >>= \case
    TC (BaseType b) -> return b
    ty -> throw TypeErr $ "Expected a base type. Got: " ++ pprint ty

scalarOrVectorLike :: Fallible m => BaseType -> ScalarBaseType -> m BaseType
scalarOrVectorLike x sbt = case x of
  Scalar _ -> return $ Scalar sbt
  Vector sizes _ -> return $ Vector sizes sbt
  _ -> throw CompilerErr "only scalar or vector base types should occur here"

data ArgumentType = SomeFloatArg | SomeIntArg | SomeUIntArg
data ReturnType   = SameReturn | Word8Return

checkOpArgType :: Fallible m => ArgumentType -> BaseType -> m ()
checkOpArgType argTy x =
  case argTy of
    SomeIntArg   -> checkIntBaseType   x
    SomeUIntArg  -> do x' <- scalarOrVectorLike x Word8Type
                       assertEq x x' ""
    SomeFloatArg -> checkFloatBaseType x

checkBinOp :: Fallible m => BinOp -> BaseType -> BaseType -> m BaseType
checkBinOp op x y = do
  checkOpArgType argTy x
  assertEq x y ""
  case retTy of
    SameReturn -> return x
    Word8Return -> scalarOrVectorLike x Word8Type
  where
    (argTy, retTy) = case op of
      IAdd   -> (ia, sr);  ISub   -> (ia, sr)
      IMul   -> (ia, sr);  IDiv   -> (ia, sr)
      IRem   -> (ia, sr);
      ICmp _ -> (ia, br)
      FAdd   -> (fa, sr);  FSub   -> (fa, sr)
      FMul   -> (fa, sr);  FDiv   -> (fa, sr);
      FPow   -> (fa, sr)
      FCmp _ -> (fa, br)
      BAnd   -> (ia, sr);  BOr    -> (ia, sr)
      BXor   -> (ia, sr)
      BShL   -> (ia, sr);  BShR   -> (ia, sr)
      where
        ia = SomeIntArg; fa = SomeFloatArg
        br = Word8Return; sr = SameReturn

checkUnOp :: Fallible m => UnOp -> BaseType -> m BaseType
checkUnOp op x = do
  checkOpArgType argTy x
  case retTy of
    SameReturn -> return x
    _ -> throw CompilerErr "all supported unary operations have the same argument and return type"
  where
    (argTy, retTy) = case op of
      Exp              -> (f, sr)
      Exp2             -> (f, sr)
      Log              -> (f, sr)
      Log2             -> (f, sr)
      Log10            -> (f, sr)
      Log1p            -> (f, sr)
      Sin              -> (f, sr)
      Cos              -> (f, sr)
      Tan              -> (f, sr)
      Sqrt             -> (f, sr)
      Floor            -> (f, sr)
      Ceil             -> (f, sr)
      Round            -> (f, sr)
      LGamma           -> (f, sr)
      Erf              -> (f, sr)
      Erfc             -> (f, sr)
      FNeg             -> (f, sr)
      BNot             -> (u, sr)
      where
        u = SomeUIntArg; f = SomeFloatArg; sr = SameReturn

-- === various helpers for querying types ===

checkedInstantiateTyConDef
  :: (EnvReader m, Fallible1 m)
  => TyConDef n -> TyConParams n -> m n (DataConDefs n)
checkedInstantiateTyConDef (TyConDef _ bs cons) (TyConParams _ xs) = do
  checkedApplyNaryAbs (Abs bs cons) xs

checkedApplyNaryAbs
  :: forall b r e o m
  .  ( BindsOneAtomName r b, EnvReader m, Fallible1 m, SinkableE e
     , SubstE AtomSubstVal e, IRRep r, SubstB AtomSubstVal b)
  => Abs (Nest b) e o -> [Atom r o] -> m o (e o)
checkedApplyNaryAbs (Abs bsTop e) xsTop = do
  go (EmptyAbs bsTop) xsTop
  applySubst (bsTop@@>(SubstVal<$>xsTop)) e
 where
   go :: EmptyAbs (Nest b) o -> [Atom r o] -> m o ()
   go (Abs Empty UnitE) [] = return ()
   go (Abs (Nest b bs) UnitE) (x:xs) = do
     xTy <- getType x
     checkAlphaEq (binderType b) xTy
     bs' <- applySubst (b@>SubstVal x) (Abs bs UnitE)
     go bs' xs
   go _ _ = throw TypeErr "wrong number of arguments"

-- === effects ===

instance IRRep r => CheckableE r (EffectRow r) where
  checkE (EffectRow effs effTail) = do
    forM_ (eSetToList effs) \eff -> case eff of
      RWSEffect _ v -> v |: TC HeapType
      ExceptionEffect -> return ()
      IOEffect        -> return ()
      UserEffect _    -> return ()
      InitEffect      -> return ()
    case effTail of
      NoTail -> return ()
      EffectRowTail v -> do
        v' <- renameM v
        ty <- atomBindingType <$> lookupAtomName v'
        checkTypesEq EffKind ty

declareEff :: forall r m i o. (IRRep r, Typer m r) => EffectRow r o -> Effect r o -> m i o ()
declareEff allowedEffs eff = checkExtends allowedEffs $ OneEffect eff

checkExtends :: (Fallible m, IRRep r) => EffectRow r n -> EffectRow r n -> m ()
checkExtends allowed (EffectRow effs effTail) = do
  let (EffectRow allowedEffs allowedEffTail) = allowed
  case effTail of
    EffectRowTail _ -> assertEq allowedEffTail effTail ""
    NoTail -> return ()
  forM_ (eSetToList effs) \eff -> unless (eff `eSetMember` allowedEffs) $
    throw CompilerErr $ "Unexpected effect: " ++ pprint eff ++
                      "\nAllowed: " ++ pprint allowed

-- === "Data" type class ===

runCheck
  :: (EnvReader m, SinkableE e)
  => (forall l. DExt n l => TyperT Maybe r l l (e l))
  -> m n (Maybe (e n))
runCheck cont = do
  Distinct <- getDistinct
  liftTyperT $ cont

asFFIFunType :: EnvReader m => CType n -> m n (Maybe (IFunType, CorePiType n))
asFFIFunType ty = return do
  Pi piTy <- return ty
  impTy <- checkFFIFunTypeM piTy
  return (impTy, piTy)

checkFFIFunTypeM :: Fallible m => CorePiType n -> m IFunType
checkFFIFunTypeM (CorePiType appExpl (Nest b bs) eff resultTy) = do
  argTy <- checkScalar $ binderType b
  case bs of
    Empty -> do
      resultTys <- checkScalarOrPairType resultTy
      let cc = case length resultTys of
                 0 -> error "Not implemented"
                 1 -> FFICC
                 _ -> FFIMultiResultCC
      return $ IFunType cc [argTy] resultTys
    Nest b' rest -> do
      let naryPiRest = CorePiType appExpl (Nest b' rest) eff resultTy
      IFunType cc argTys resultTys <- checkFFIFunTypeM naryPiRest
      return $ IFunType cc (argTy:argTys) resultTys
checkFFIFunTypeM _ = error "expected at least one argument"

checkScalar :: (IRRep r, Fallible m) => Type r n -> m BaseType
checkScalar (BaseTy ty) = return ty
checkScalar ty = throw TypeErr $ pprint ty

checkScalarOrPairType :: (IRRep r, Fallible m) => Type r n -> m [BaseType]
checkScalarOrPairType (PairTy a b) = do
  tys1 <- checkScalarOrPairType a
  tys2 <- checkScalarOrPairType b
  return $ tys1 ++ tys2
checkScalarOrPairType (BaseTy ty) = return [ty]
checkScalarOrPairType ty = throw TypeErr $ pprint ty

isData :: EnvReader m => Type CoreIR n -> m n Bool
isData ty = liftM isJust $ runCheck do
  checkDataLike (sink ty)
  return UnitE

checkDataLike :: Typer m r => Type CoreIR i -> m i o ()
checkDataLike ty = case ty of
  TyVar _ -> notData
  TabPi (TabPiType b eltTy) -> do
    renameBinders b \_ ->
      checkDataLike eltTy
  DepPairTy (DepPairType _ b@(_:>l) r) -> do
    recur l
    renameBinders b \_ -> checkDataLike r
  NewtypeTyCon nt -> do
    (_, ty') <- unwrapNewtypeType =<< renameM nt
    dropSubst $ recur ty'
  TC con -> case con of
    BaseType _       -> return ()
    ProdType as      -> mapM_ recur as
    SumType  cs      -> mapM_ recur cs
    RefType _ _      -> return ()
    HeapType         -> return ()
    _ -> notData
  _   -> notData
  where
    recur = checkDataLike
    notData = throw TypeErr $ pprint ty
