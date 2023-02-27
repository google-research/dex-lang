-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module CheckType (
  CheckableE (..), CheckableB (..),
  checkTypes, checkTypesM, checkHasType,
  checkExtends, checkedApplyClassParams,
  tryGetType, checkUnOp, checkBinOp,
  isData, asFirstOrderFunction, asFFIFunType,
  asNaryPiType
  ) where

import Prelude hiding (id)
import Control.Category ((>>>))
import Control.Monad
import Control.Monad.Reader
import Data.List.NonEmpty (NonEmpty (..))
import Data.Maybe (isJust)
import Data.Foldable (toList)
import Data.Functor
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M

import CheapReduction
import Core
import Err
import IRVariants
import LabeledItems
import Name
import Subst
import PPrint ()
import QueryType hiding (HasType)
import Types.Core
import Types.Imp
import Types.Primitives
import Types.Source
import Util (forMZipped_, onSndM, restructure)

-- === top-level API ===

checkTypes :: (EnvReader m, CheckableE e) => e n -> m n (Except ())
checkTypes e = liftTyperT $ checkE e
{-# SCC checkTypes #-}

checkTypesM :: (EnvReader m, Fallible1 m, CheckableE e) => e n -> m n ()
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
     => Typer (m::MonadKind2)

newtype TyperT (m::MonadKind) (i::S) (o::S) (a :: *) =
  TyperT { runTyperT' :: SubstReaderT Name (EnvReaderT m) i o a }
  deriving ( Functor, Applicative, Monad
           , SubstReader Name
           , MonadFail
           , Fallible
           , ScopeReader
           , EnvReader, EnvExtender)

liftTyperT :: (EnvReader m', Fallible m) => TyperT m n n a -> m' n (m a)
liftTyperT cont =
  liftEnvReaderT $
    runSubstReaderT idSubst $
      runTyperT' cont
{-# INLINE liftTyperT #-}

instance Fallible m => Typer (TyperT m)

-- === typeable things ===

class (SinkableE e, RenameE e, PrettyE e, IRRep r) => HasType (r::IR) (e::E) | e -> r where
  getTypeE   :: Typer m => e i -> m i o (Type r o)

checkTypeE :: (HasType r e, Typer m) => Type r o -> e i -> m i o (e o)
checkTypeE reqTy e = do
  e |: reqTy
  renameM e

checkTypesEq :: (Typer m, IRRep r) => Type r o -> Type r o -> m i o ()
checkTypesEq reqTy ty = alphaEq reqTy ty >>= \case
  True  -> return ()
  False -> {-# SCC typeNormalization #-} do
    reqTy' <- cheapNormalize reqTy
    ty'    <- cheapNormalize ty
    alphaEq reqTy' ty' >>= \case
      True  -> return ()
      False -> throw TypeErr $ pprint reqTy' ++ " != " ++ pprint ty'
{-# INLINE checkTypesEq #-}

class SinkableE e => CheckableE (e::E) where
  checkE :: Typer m => e i -> m i o ()

class HasNamesB b => CheckableB (b::B) where
  checkB :: Typer m
         => b i i'
         -> (forall o'. Ext o o' => b o o' -> m i' o' ())
         -> m i o ()

checkBEvidenced :: (CheckableB b, Typer m)
                => b i i'
                -> (forall o'. ExtEvidence o o' -> b o o' -> m i' o' ())
                -> m i o ()
checkBEvidenced b cont = checkB b \b' -> cont getExtEvidence b'

-- === convenience functions ===

infixr 7 |:
(|:) :: (Typer m, HasType r e) => e i -> Type r o -> m i o ()
(|:) x reqTy = do
  ty <- getTypeE x
  -- TODO: Write an alphaEq variant that works modulo an equivalence
  -- relation on names.
  checkTypesEq reqTy ty

instance CheckableE SourceMap where
  checkE _ = return ()

instance (CheckableE e1, CheckableE e2) => CheckableE (PairE e1 e2) where
  checkE (PairE e1 e2) = checkE e1 >> checkE e2

instance (CheckableE e1, CheckableE e2) => CheckableE (EitherE e1 e2) where
  checkE ( LeftE e) = checkE e
  checkE (RightE e) = checkE e

instance (CheckableB b, CheckableE e) => CheckableE (Abs b e) where
  checkE (Abs b e) = checkB b \_ -> checkE e

instance (IRRep r) => CheckableE (LamExpr r) where
  checkE (LamExpr bs body) = checkB bs \_ ->  void $ getTypeE body

instance (IRRep r) => CheckableE (DestLamExpr r) where
  checkE (DestLamExpr bs block) = checkB bs \_ -> do
    DestBlock destb body <- return block
    checkB destb \_ -> void $ getTypeE body

-- === type checking core ===

instance IRRep r => CheckableE (Atom r) where
  checkE atom = void $ getTypeE atom

instance IRRep r => HasType r (AtomName r) where
  getTypeE name = do
    name' <- renameM name
    atomBindingType <$> lookupAtomName name'
  {-# INLINE getTypeE #-}

instance IRRep r => CheckableE (Block r) where
  checkE block = void $ getTypeE block

instance IRRep r => HasType r (Atom r) where
  getTypeE atom = case atom of
    Var name -> getTypeE name
    Lam lam arr (Abs bEff effs) -> do
      UnaryLamExpr (b:>ty) body <- return lam
      ty' <- checkTypeE TyKind ty
      withFreshBinder (getNameHint b) ty' \b' -> do
        effs' <- extendSubst (bEff@>binderName b') $ renameM effs
        extendRenamer (b@>binderName b') do
          resultTy <- checkBlockWithEffs effs' body
          return $ Pi $ PiType b' arr effs' resultTy
    Pi piType -> getTypeE piType
    TabPi piType -> getTypeE piType
    DepPair l r ty -> do
      ty' <- checkTypeE TyKind ty
      l'  <- checkTypeE (depPairLeftTy ty') l
      rTy <- instantiateDepPairTy ty' l'
      r |: rTy
      return $ DepPairTy ty'
    DepPairTy ty -> getTypeE ty
    Con con  -> typeCheckPrimCon con
    TC tyCon -> typeCheckPrimTC  tyCon
    Eff eff  -> checkE eff $> EffKind
    PtrVar v -> renameM v >>= lookupEnv >>= \case
      PtrBinding ty _ -> return $ PtrTy ty
    DictCon dictExpr -> getTypeE dictExpr
    DictTy (DictType _ className params) -> do
      ClassDef _ _ paramBs _ _ <- renameM className >>= lookupClassDef
      params' <- mapM renameM params
      checkArgTys paramBs params'
      return TyKind
    RepValAtom (RepVal ty _) -> renameM ty
    NewtypeCon con x -> NewtypeTyCon <$> typeCheckNewtypeCon con x
    NewtypeTyCon t   -> typeCheckNewtypeTyCon t
    SimpInCore x -> getTypeE x
    DictHole _ ty -> checkTypeE TyKind ty
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

instance HasType CoreIR SimpInCore where
  getTypeE = \case
    LiftSimp ty _ -> renameM ty  -- TODO: check
    LiftSimpFun piTy _ -> Pi <$> renameM piTy -- TODO: check
    ACase _ _ ty -> renameM ty -- TODO: check
    TabLam t _ -> TabPi <$> renameM t -- TODO: check

instance (ToBinding ann c, Color c, CheckableE ann) => CheckableB (BinderP c ann) where
  checkB (b:>ann) cont = do
    checkE ann
    ann' <- renameM ann
    withFreshBinder (getNameHint b) ann' \b' ->
      extendRenamer (b@>binderName b') $
        cont b'

typeCheckExpr :: (Typer m, IRRep r) => EffectRow r o -> Expr r i -> m i o (Type r o)
typeCheckExpr effs expr = case expr of
  App f xs -> do
    fTy <- getTypeE f
    checkApp effs fTy $ toList xs
  TabApp f xs -> do
    fTy <- getTypeE f
    checkTabApp fTy xs
  -- TODO: check!
  TopApp f xs -> do
    NaryPiType bs _ resultTy <- getTypeTopFun =<< renameM f
    xs' <- mapM renameM xs
    checkedApplyNaryAbs (Abs bs resultTy) xs'
  Atom x   -> getTypeE x
  PrimOp op -> typeCheckPrimOp effs op
  Hof  hof -> typeCheckPrimHof effs hof
  Case e alts resultTy caseEffs -> do
    caseEffs' <- renameM caseEffs
    resultTy'  <- renameM resultTy
    checkCase e alts resultTy' caseEffs'
    checkExtends effs caseEffs'
    return resultTy'
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
      ProjRef i -> do
        ProdTy tys <- return s
        return $ TC $ RefType h $ tys !! i
  ProjMethod dict i -> do
    DictTy (DictType _ className params) <- getTypeE dict
    def@(ClassDef _ _ paramBs classBs methodTys) <- lookupClassDef className
    let MethodType _ methodTy = methodTys !! i
    superclassDicts <- getSuperclassDicts def <$> renameM dict
    let subst = (    paramBs @@> map SubstVal params
                 <.> classBs @@> map SubstVal superclassDicts)
    applySubst subst methodTy
  TabCon _ ty xs -> do
    ty'@(TabPi (TabPiType b restTy)) <- checkTypeE TyKind ty
    case fromConstAbs (Abs b restTy) of
      HoistSuccess elTy -> forM_ xs (|: elTy)
      -- XXX: in the dependent case we don't check that the element types
      -- match the annotation because that would require concretely evaluating
      -- each index from the ix dict.
      HoistFailure _    -> forM_ xs checkE
    return ty'
  RecordOp x -> typeCheckRecordOp x
  DAMOp op -> typeCheckDAMOp effs op
  UserEffectOp op -> typeCheckUserEffect op

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
    go :: Typer m => EffectRow r o -> Type r o -> Nest (Decl r) i i' -> Atom r i' -> m i o ()
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

instance CheckableE DataDefParams where
  checkE (DataDefParams params) = mapM_ (onSndM checkE) params

dictExprType :: Typer m => DictExpr i -> m i o (CType o)
dictExprType e = case e of
  InstanceDict instanceName args -> do
    instanceName' <- renameM instanceName
    InstanceDef className bs params _ <- lookupInstanceDef instanceName'
    ClassDef sourceName _ _ _ _ <- lookupClassDef className
    args' <- mapM renameM args
    checkArgTys bs args'
    ListE params' <- applySubst (bs@@>(SubstVal<$>args')) (ListE params)
    return $ DictTy $ DictType sourceName className params'
  InstantiatedGiven given args -> do
    givenTy <- getTypeE given
    checkApp Pure givenTy (toList args)
  SuperclassProj d i -> do
    DictTy (DictType _ className params) <- getTypeE d
    ClassDef _ _ bs superclasses _ <- lookupClassDef className
    checkedApplyNaryAbs
      (Abs (toBinderNest bs) (superclassTypes superclasses !! i))
      params
  IxFin n -> do
    n' <- checkTypeE NatTy n
    liftM DictTy $ ixDictType $ NewtypeTyCon $ Fin n'
  DataData ty -> DictTy <$> (dataDictType =<< checkTypeE TyKind ty)

instance HasType CoreIR DictExpr where
  getTypeE e = dictExprType e

instance IRRep r => HasType r (DepPairType r) where
  getTypeE (DepPairType b ty) = do
    checkB b \_ -> ty |: TyKind
    return TyKind

instance HasType CoreIR PiType where
  getTypeE (PiType b arr eff resultTy) = do
    checkArrowAndEffects arr eff
    checkB b \_ -> do
      void $ checkE eff
      resultTy|:TyKind
    return TyKind

instance IRRep r => CheckableE (IxType r) where
  checkE (IxType t _) = checkE t

instance IRRep r => HasType r (TabPiType r) where
  getTypeE (TabPiType b resultTy) = do
    checkB b \_ -> resultTy|:TyKind
    return TyKind

instance (BindsNames b, CheckableB b) => CheckableB (Nest b) where
  checkB nest cont = case nest of
    Empty -> cont Empty
    Nest b rest ->
      checkBEvidenced b \ext1 b' ->
        checkBEvidenced rest \ext2 rest' ->
          withExtEvidence (ext1 >>> ext2) $
            cont $ Nest b' rest'

typeCheckPrimTC :: (Typer m, IRRep r) => PrimTC r (Atom r i) -> m i o (Type r o)
typeCheckPrimTC tc = case tc of
  BaseType _       -> return TyKind
  ProdType tys     -> mapM_ (|:TyKind) tys >> return TyKind
  SumType  cs      -> mapM_ (|:TyKind) cs  >> return TyKind
  RefType r a      ->  r|:TC HeapType >> a|:TyKind >> return TyKind
  TypeKind         -> return TyKind
  HeapType         -> return TyKind

typeCheckPrimCon :: (Typer m, IRRep r) => PrimCon r (Atom r i) -> m i o (Type r o)
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
  :: Typer m => NewtypeCon i -> CAtom i -> m i o (NewtypeTyCon o)
typeCheckNewtypeCon con x = case con of
  NatCon   -> x|:IdxRepTy          >> return Nat
  FinCon n -> n|:NatTy >> x|:NatTy >> renameM (Fin n)
  RecordCon  labels -> do
    TC (ProdType tys) <- getTypeE x
    return $ StaticRecordTyCon $ restructure tys labels
  UserADTData d params -> do
    d' <- renameM d
    def@(DataDef sn _ _) <- lookupDataDef d'
    params' <- renameM params
    void $ checkedInstantiateDataDef def params'
    return $ UserADTType sn d' params'

typeCheckNewtypeTyCon :: Typer m => NewtypeTyCon i -> m i o (CType o)
typeCheckNewtypeTyCon = \case
  Nat        -> return TyKind
  Fin n      -> checkTypeE NatTy n >> return TyKind
  LabelCon _ -> return $ NewtypeTyCon $ LabelType
  LabelType  -> return TyKind
  EffectRowKind    -> return TyKind
  RecordTyCon   elems -> checkFieldRowElems elems $> TyKind
  LabeledRowCon elems -> checkFieldRowElems elems $> LabeledRowKind
  LabeledRowKindTC -> return TyKind
  UserADTType _ d params -> do
    def <- lookupDataDef =<< renameM d
    params' <- renameM params
    void $ checkedInstantiateDataDef def params'
    return TyKind

typeCheckPrimOp :: (Typer m, IRRep r) => EffectRow r o -> PrimOp (Atom r i) -> m i o (Type r o)
typeCheckPrimOp effs op = case op of
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

typeCheckMemOp :: forall r m i o. (Typer m, IRRep r) => EffectRow r o -> MemOp (Atom r i) -> m i o (Type r o)
typeCheckMemOp effs = \case
  IOAlloc t n -> do
    n |: IdxRepTy
    declareEff effs IOEffect
    return $ PtrTy (CPU, t)
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

typeCheckMiscOp :: forall r m i o. (Typer m, IRRep r) => EffectRow r o -> MiscOp (Atom r i) -> m i o (Type r o)
typeCheckMiscOp effs = \case
  Select p x y -> do
    p |: (BaseTy $ Scalar Word8Type)
    ty <- getTypeE x
    y |: ty
    return ty

  CastOp t@(Var _) _ -> t |: TyKind >> renameM t
  CastOp destTy e -> do
    sourceTy' <- getTypeE e
    destTy |: TyKind
    destTy' <- renameM destTy
    checkValidCast sourceTy' destTy'
    return $ destTy'
  BitcastOp t@(Var _) _ -> t |: TyKind >> renameM t
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

checkSomeSumType :: (Typer m, IRRep r) => Type r o -> m i o [Type r o]
checkSomeSumType = \case
  SumTy cases -> return cases
  NewtypeTyCon con -> do
    (_, SumTy cases) <- unwrapNewtypeType con
    return cases
  t -> error $ "not some sum type: " ++ pprint t

typeCheckVectorOp :: (Typer m, IRRep r) => VectorOp (Atom r i) -> m i o (Type r o)
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

typeCheckUserEffect :: Typer m => UserEffectOp i -> m i o (CType o)
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

typeCheckPrimHof :: forall r m i o. (Typer m, IRRep r) => EffectRow r o -> Hof r i -> m i o (Type r o)
typeCheckPrimHof effs hof = addContext ("Checking HOF:\n" ++ pprint hof) case hof of
  For _ ixDict f -> do
    ixTy <- ixTyFromDict =<< renameM ixDict
    NaryPiType (UnaryNest (b:>argTy)) _ eltTy <- checkLamExpr f
    checkTypesEq (ixTypeType ixTy) argTy
    return $ TabTy (b:>ixTy) eltTy
  While body -> do
    condTy <- getTypeE body
    checkTypesEq (BaseTy $ Scalar Word8Type) condTy
    return UnitTy
  Linearize f x -> do
    NaryPiType (UnaryNest (binder:>a)) Pure b <- checkLamExpr f
    b' <- liftHoistExcept $ hoist binder b
    fLinTy <- a --@ b'
    x |: a
    return $ PairTy b' fLinTy
  Transpose f x -> do
    NaryPiType (UnaryNest (binder:>a)) Pure b <- checkLamExpr f
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

typeCheckDAMOp :: forall r m i o . (Typer m, IRRep r) => EffectRow r o -> DAMOp r i -> m i o (Type r o)
typeCheckDAMOp effs op = addContext ("Checking DAMOp:\n" ++ show op) case op of
  Seq _ ixDict carry f -> do
    ixTy <- ixTyFromDict =<< renameM ixDict
    carryTy' <- getTypeE carry
    let badCarry = throw TypeErr $ "Seq carry should be a product of raw references, got: " ++ pprint carryTy'
    case carryTy' of
      ProdTy refTys -> forM_ refTys \case RawRefTy _ -> return (); _ -> badCarry
      _ -> badCarry
    NaryPiType (UnaryNest b) _ _ <- checkLamExprWithEffs effs f
    checkTypesEq (PairTy (ixTypeType ixTy) carryTy') (binderType b)
    return carryTy'
  RememberDest d body -> do
    dTy@(RawRefTy _) <- getTypeE d
    NaryPiType (UnaryNest b) _ UnitTy <- checkLamExpr body

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

checkLamExpr :: (Typer m, IRRep r) => LamExpr r i -> m i o (NaryPiType r o)
checkLamExpr (LamExpr bsTop body) = case bsTop of
  Empty -> do
    resultTy <- getTypeE body
    effs <- renameM $ blockEffects body
    return $ NaryPiType Empty effs resultTy
  Nest (b:>ty) bs -> do
    ty' <- checkTypeE TyKind ty
    withFreshBinder (getNameHint b) ty' \b' ->
      extendRenamer (b@>binderName b') do
        NaryPiType bs' eff resultTy <- checkLamExpr (LamExpr bs body)
        return $ NaryPiType (Nest b' bs') eff resultTy

checkLamExprWithEffs :: (Typer m, IRRep r) => EffectRow r o -> LamExpr r i -> m i o (NaryPiType r o)
checkLamExprWithEffs allowedEffs lam = do
  piTy@(NaryPiType bs effs _) <- checkLamExpr lam
  effs' <- liftHoistExcept $ hoist bs effs
  checkExtends allowedEffs effs'
  return piTy

checkBlockWithEffs :: (Typer m, IRRep r) => EffectRow r o -> Block r i -> m i o (Type r o)
checkBlockWithEffs allowedEffs block = do
  ty <- getTypeE block
  effs <- renameM $ blockEffects block
  checkExtends allowedEffs effs
  return ty

checkRWSAction :: (Typer m, IRRep r) => EffectRow r o -> RWS -> LamExpr r i -> m i o (Type r o, Type r o)
checkRWSAction effs rws f = do
  BinaryLamExpr bH bR body <- return f
  renameBinders bH \bH' -> renameBinders bR \bR' -> do
    h <- sinkM $ binderName bH'
    let effs' = extendEffect (RWSEffect rws $ Var h) (sink effs)
    RefTy _ referentTy <- sinkM $ binderType bR'
    resultTy <- checkBlockWithEffs effs' body
    liftM fromPairE $ liftHoistExcept $ hoist (PairB bH' bR') $ PairE resultTy referentTy

checkCase :: (Typer m, IRRep r) => Atom r i -> [Alt r i] -> Type r o -> EffectRow r o -> m i o ()
checkCase scrut alts resultTy effs = do
  scrutTy <- getTypeE scrut
  altsBinderTys <- checkCaseAltsBinderTys scrutTy
  forMZipped_ alts altsBinderTys \alt bs ->
    checkAlt resultTy bs effs alt

checkCaseAltsBinderTys :: (Fallible1 m, EnvReader m, IRRep r) => Type r n -> m n [Type r n]
checkCaseAltsBinderTys ty = case ty of
  SumTy types -> return types
  NewtypeTyCon t -> case t of
    UserADTType _ defName params -> do
      def <- lookupDataDef defName
      cons <- checkedInstantiateDataDef def params
      return [repTy | DataConDef _ _ repTy _ <- cons]
    _ -> fail msg
  _ -> fail msg
  where msg = "Case analysis only supported on ADTs, not on " ++ pprint ty

checkAlt :: (Typer m, IRRep r) => Type r o -> Type r o -> EffectRow r o -> Alt r i -> m i o ()
checkAlt resultTyReq bTyReq effs (Abs b body) = do
  bTy <- renameM $ binderType b
  checkTypesEq bTyReq bTy
  renameBinders b \_ -> do
    resultTy <- checkBlockWithEffs (sink effs) body
    checkTypesEq (sink resultTyReq) resultTy

checkApp :: (Typer m, IRRep r) => EffectRow r o -> Type r o -> [Atom r i] -> m i o (Type r o)
checkApp _ fTy [] = return fTy
checkApp allowedEffs fTy xs = case fromNaryPiType (length xs) fTy of
  Just (NaryPiType bs effs resultTy) -> do
    xs' <- mapM renameM xs
    checkArgTys bs xs'
    let subst = bs @@> fmap SubstVal xs'
    PairE effs' resultTy' <- applySubst subst $ PairE effs resultTy
    checkExtends allowedEffs effs'
    return resultTy'
  Nothing -> throw TypeErr $
    "Not a " ++ show (length xs) ++ "-argument pi type: " ++ pprint fTy
      ++ " (tried to apply it to: " ++ pprint xs ++ ")"

checkTabApp :: (Typer m, IRRep r) => Type r o -> NonEmpty (Atom r i) -> m i o (Type r o)
checkTabApp tabTy xs = go tabTy $ toList xs
  where
    go :: (Typer m, IRRep r) => Type r o -> [Atom r i] -> m i o (Type r o)
    go ty [] = return ty
    go ty (i:rest) = do
      TabTy (b :> IxType ixTy _) resultTy <- return ty
      i' <- checkTypeE ixTy i
      resultTy' <- applySubst (b@>SubstVal i') resultTy
      go resultTy' rest

asNaryPiType :: IRRep r => Type r n -> Maybe ([Arrow], NaryPiType r n)
asNaryPiType piTy = case piTy of
  Pi (PiType b arr effs resultTy) -> case effs of
   Pure -> case asNaryPiType resultTy of
     Just (arrs, NaryPiType bs effs' resultTy') ->
        Just (arr:arrs, NaryPiType (Nest b bs) effs' resultTy')
     Nothing -> Just ([arr], NaryPiType (Nest b Empty) Pure resultTy)
   _ -> Just ([arr], NaryPiType (Nest b Empty) effs resultTy)
  _ -> Nothing

checkArgTys
  :: (Typer m, SubstB AtomSubstVal b, BindsNames b, BindsOneAtomName r b, IRRep r)
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

checkArrowAndEffects :: (Fallible m, IRRep r) => Arrow -> EffectRow r n -> m ()
checkArrowAndEffects PlainArrow _ = return ()
checkArrowAndEffects _ Pure = return ()
checkArrowAndEffects _ _ = throw TypeErr $ "Only plain arrows may have effects"

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

typeCheckBaseType :: Typer m => HasType r e => e i -> m i o BaseType
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

typeCheckRecordOp :: Typer m => RecordOp (CAtom i) -> m i o (CType o)
typeCheckRecordOp = \case
  RecordCons l r -> do
    lty <- getTypeE l
    rty <- getTypeE r
    case (lty, rty) of
      (RecordTyWithElems lelems, RecordTyWithElems relems) ->
        return $ RecordTyWithElems $ lelems ++ relems
      _ -> throw TypeErr $ "Can't concatenate " <> pprint lty <> " and " <> pprint rty <> " as records"
  RecordConsDynamic lab val record -> do
    lab' <- checkTypeE (NewtypeTyCon LabelType) lab
    vty <- getTypeE val
    rty <- getTypeE record
    case rty of
      RecordTy rest -> case lab' of
        NewtypeTyCon (LabelCon l) -> return $ RecordTy $ prependFieldRowElem (StaticFields (labeledSingleton l vty)) rest
        Var labVar       -> return $ RecordTy $ prependFieldRowElem (DynField labVar vty) rest
        _ -> error "Unexpected label atom"
      _ -> throw TypeErr $ "Can't add a dynamic field to a non-record value of type " <> pprint rty
  RecordSplitDynamic lab record -> do
    lab' <- cheapNormalize =<< checkTypeE (NewtypeTyCon LabelType) lab
    rty <- getTypeE record
    case (lab', rty) of
      (NewtypeTyCon (LabelCon l), RecordTyWithElems (StaticFields items:rest)) -> do
        -- We could cheap normalize the rest to increase the chance of this
        -- succeeding, but no need to for now.
        unless (isJust $ lookupLabelHead items l) $ throw TypeErr "Label not immediately present in record"
        let (h, items') = splitLabeledItems (labeledSingleton l ()) items
        return $ PairTy (head $ toList h) $ RecordTyWithElems (StaticFields items':rest)
      (Var labVar', RecordTyWithElems (DynField labVar'' ty:rest)) | labVar' == labVar'' ->
        return $ PairTy ty $ RecordTyWithElems rest
      -- There are more cases we could implement, but do we need to?
      _ -> throw TypeErr $ "Can't split a label " <> pprint lab' <> " from atom of type " <> pprint rty
  RecordSplit fields record -> do
    fields' <- cheapNormalize =<< checkTypeE LabeledRowKind fields
    fullty  <- cheapNormalize =<< getTypeE record
    let splitFailed = throw TypeErr $ "Invalid record split: " <> pprint fields' <> " from " <> pprint fullty
    case (fields', fullty) of
      (LabeledRow els, RecordTyWithElems els') ->
        stripPrefix (fromFieldRowElems els) els' >>= \case
          Just rest -> return $ PairTy (RecordTy els) (RecordTyWithElems rest)
          Nothing -> splitFailed
      (Var v, RecordTyWithElems (DynFields v':rest)) | v == v' ->
        return $ PairTy (RecordTyWithElems [DynFields v']) (RecordTyWithElems rest)
      _ -> splitFailed
    where
      stripPrefix = curry \case
        ([]  , ys  ) -> return $ Just ys
        (x:xs, y:ys) -> alphaEq x y >>= \case
          True  -> stripPrefix xs ys
          False -> case (x, y) of
            (StaticFields xf, StaticFields yf) -> do
              NoExt rest <- labeledRowDifference (NoExt yf) (NoExt xf)
              return $ Just $ StaticFields rest : ys
            _ -> return Nothing
        _ -> return Nothing

-- === various helpers for querying types ===

checkedInstantiateDataDef
  :: (EnvReader m, Fallible1 m)
  => DataDef n -> DataDefParams n -> m n [DataConDef n]
checkedInstantiateDataDef (DataDef _ bs cons) (DataDefParams xs) = do
  fromListE <$> checkedApplyNaryAbs
    (Abs (fmapNest (\(RolePiBinder b ty _ _) -> b:>ty) bs) (ListE cons))
    (map snd xs)

checkedApplyClassParams
  :: (EnvReader m, Fallible1 m) => ClassDef n -> [CType n]
  -> m n (Abs SuperclassBinders (ListE MethodType) n)
checkedApplyClassParams (ClassDef _ _ bs superclassBs methodTys) params = do
  let body = Abs superclassBs (ListE methodTys)
  checkedApplyNaryAbs (Abs (toBinderNest bs) body) params

-- TODO: Subst all at once, not one at a time!
checkedApplyNaryAbs :: (EnvReader m, Fallible1 m, SinkableE e, SubstE AtomSubstVal e, IRRep r)
                    => Abs (Nest (Binder r)) e o -> [Atom r o] -> m o (e o)
checkedApplyNaryAbs (Abs nest e) args = case (nest, args) of
  (Empty    , []) -> return e
  (Nest b@(_:>bTy) bs, x:t) -> do
    xTy <- getType x
    checkAlphaEq bTy xTy
    flip checkedApplyNaryAbs t =<< applyAbs (Abs b $ Abs bs e) (SubstVal x)
  (_        , _  ) -> throw CompilerErr $ "Length mismatch in checkedApplyNaryAbs"

-- === effects ===

instance IRRep r => CheckableE (EffectRow r) where
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

declareEff :: forall r m i o. (IRRep r, Typer m) => EffectRow r o -> Effect r o -> m i o ()
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

-- === labeled row types ===

checkFieldRowElems :: forall m i o. Typer m => FieldRowElems i -> m i o ()
checkFieldRowElems els = mapM_ checkElem elemList
  where
    elemList = fromFieldRowElems els
    checkElem :: FieldRowElem i -> m i o ()
    checkElem = \case
      StaticFields items -> checkLabeledRow $ NoExt items
      DynField labVar ty -> do
        Var labVar |: (NewtypeTyCon LabelType :: CType o)
        ty |: TyKind
      DynFields row -> checkLabeledRow $ Ext mempty $ Just row

checkLabeledRow :: forall m i o. Typer m => ExtLabeledItems (CType i) (CAtomName i) -> m i o ()
checkLabeledRow (Ext items rest) = do
  mapM_ (|: TyKind) items
  forM_ rest \name -> do
    name' <- lookupSubstM name
    ty <- atomBindingType <$> lookupAtomName name'
    checkTypesEq LabeledRowKind ty

labeledRowDifference :: Typer m
                     => ExtLabeledItems (CType o) (AtomName r o)
                     -> ExtLabeledItems (CType o) (AtomName r o)
                     -> m i o (ExtLabeledItems (CType o) (AtomName r o))
labeledRowDifference (Ext (LabeledItems items) rest)
                     (Ext (LabeledItems subitems) subrest) = do
  -- Check types in the right.
  _ <- flip M.traverseWithKey subitems \label subtypes ->
    case M.lookup label items of
      Just types -> forMZipped_
          subtypes
          (NE.fromList $ NE.take (length subtypes) types)
          checkTypesEq
      Nothing -> throw TypeErr $ "Extracting missing label " ++ show label
  -- Extract remaining types from the left.
  let
    neDiff xs ys = NE.nonEmpty $ NE.drop (length ys) xs
    diffitems = M.differenceWith neDiff items subitems
  -- Check tail.
  diffrest <- case (subrest, rest) of
    (Nothing, _) -> return rest
    (Just v, Just v') | v == v' -> return Nothing
    _ -> throw TypeErr $ "Row tail " ++ pprint subrest
      ++ " is not known to be a subset of " ++ pprint rest
  return $ Ext (LabeledItems diffitems) diffrest

-- === "Data" type class ===

runCheck
  :: (EnvReader m, SinkableE e)
  => (forall l. DExt n l => TyperT Maybe l l (e l))
  -> m n (Maybe (e n))
runCheck cont = do
  Distinct <- getDistinct
  liftTyperT $ cont

asFFIFunType :: EnvReader m => CType n -> m n (Maybe (IFunType, NaryPiType CoreIR n))
asFFIFunType ty = return do
  (_, naryPiTy) <- asNaryPiType ty
  impTy <- checkFFIFunTypeM naryPiTy
  return (impTy, naryPiTy)

checkFFIFunTypeM :: (IRRep r, Fallible m) => NaryPiType r n -> m  IFunType
checkFFIFunTypeM (NaryPiType (Nest b bs) eff resultTy) = do
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
      let naryPiRest = NaryPiType (Nest b' rest) eff resultTy
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

-- TODO: consider effects
asFirstOrderFunction :: EnvReader m => Type CoreIR n -> m n (Maybe ([Arrow], NaryPiType CoreIR n))
asFirstOrderFunction ty = do
  result <- runCheck (asFirstOrderFunctionM (sink ty))
  forM result \(LiftE arrs `PairE` piTy) -> return (arrs, piTy)

asFirstOrderFunctionM :: Typer m => Type CoreIR i -> m i o (PairE (LiftE [Arrow]) (NaryPiType CoreIR) o)
asFirstOrderFunctionM ty = case asNaryPiType ty of
  Nothing -> throw TypeErr "Not a monomorphic first-order function"
  Just (arrs, naryPi@(NaryPiType bs eff resultTy)) -> do
    renameBinders bs \bs' -> do
      ts <- mapM sinkM $ bindersTypes bs'
      dropSubst $ mapM_ checkDataLike ts
      Pure <- return eff
      checkDataLike resultTy
    naryPi' <- renameM naryPi
    return $ LiftE arrs `PairE` naryPi'

isData :: EnvReader m => Type CoreIR n -> m n Bool
isData ty = liftM isJust $ runCheck do
  checkDataLike (sink ty)
  return UnitE

checkDataLike :: Typer m => Type CoreIR i -> m i o ()
checkDataLike ty = case ty of
  Var _ -> notData
  TabPi (TabPiType b eltTy) -> do
    renameBinders b \_ ->
      checkDataLike eltTy
  DepPairTy (DepPairType b@(_:>l) r) -> do
    recur l
    renameBinders b \_ -> checkDataLike r
  NewtypeTyCon LabelType -> notData
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
