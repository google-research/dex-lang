-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module QueryType (module QueryType, module QueryTypePure, toAtomVar) where

import Control.Category ((>>>))
import Control.Monad
import Data.List (elemIndex)
import Data.Functor ((<&>))

import Types.Primitives
import Types.Core
import Types.Source
import Types.Imp
import IRVariants
import Core
import Err
import Name hiding (withFreshM)
import Subst
import Util
import PPrint ()
import QueryTypePure
import CheapReduction

sourceNameType :: (EnvReader m, Fallible1 m) => SourceName -> m n (Type CoreIR n)
sourceNameType v = do
  lookupSourceMap v >>= \case
    Nothing -> throw UnboundVarErr $ pprint v
    Just uvar -> getUVarType uvar

-- === Exposed helpers for querying types and effects ===

caseAltsBinderTys :: (EnvReader m,  IRRep r) => Type r n -> m n [Type r n]
caseAltsBinderTys ty = case ty of
  SumTy types -> return types
  NewtypeTyCon t -> case t of
    UserADTType _ defName params -> do
      def <- lookupTyCon defName
      ~(ADTCons cons) <- instantiateTyConDef def params
      return [repTy | DataConDef _ _ repTy _ <- cons]
    _ -> error msg
  _ -> error msg
  where msg = "Case analysis only supported on ADTs, not on " ++ pprint ty

extendEffect :: IRRep r => Effect r n -> EffectRow r n -> EffectRow r n
extendEffect eff (EffectRow effs t) = EffectRow (effs <> eSetSingleton eff) t

blockEffTy :: (EnvReader m, IRRep r) => Block r n -> m n (EffTy r n)
blockEffTy block = liftEnvReaderM $ refreshAbs block \decls result -> do
  effs <- declsEffects decls mempty
  return $ ignoreHoistFailure $ hoist decls $ EffTy effs $ getType result
  where
    declsEffects :: IRRep r => Nest (Decl r) n l -> EffectRow r l -> EnvReaderM l (EffectRow r l)
    declsEffects Empty !acc = return acc
    declsEffects n@(Nest (Let _ (DeclBinding _ expr)) rest) !acc = withExtEvidence n do
      expr' <- sinkM expr
      declsEffects rest $ acc <> getEffects expr'

blockTy :: (EnvReader m, IRRep r) => Block r n -> m n (Type r n)
blockTy b = blockEffTy b <&> \(EffTy _ t) -> t

piTypeWithoutDest :: PiType SimpIR n -> PiType SimpIR n
piTypeWithoutDest (PiType bsRefB _) =
  case popNest bsRefB of
    Just (PairB bs (_:>RawRefTy ansTy)) -> do
      PiType bs $ EffTy Pure ansTy  -- XXX: we ignore the effects here
    _ -> error "expected trailing dest binder"

blockEff :: (EnvReader m, IRRep r) => Block r n -> m n (EffectRow r n)
blockEff b = blockEffTy b <&> \(EffTy eff _) -> eff

typeOfApp  :: (IRRep r, EnvReader m) => Type r n -> [Atom r n] -> m n (Type r n)
typeOfApp (Pi piTy) xs = withSubstReaderT $
  withInstantiated piTy xs \(EffTy _ ty) -> substM ty
typeOfApp _ _ = error "expected a pi type"

typeOfTabApp :: (IRRep r, EnvReader m) => Type r n -> [Atom r n] -> m n (Type r n)
typeOfTabApp t [] = return t
typeOfTabApp (TabPi tabTy) (i:rest) = do
  resultTy <- instantiate tabTy [i]
  typeOfTabApp resultTy rest
typeOfTabApp ty _ = error $ "expected a table type. Got: " ++ pprint ty

typeOfApplyMethod :: EnvReader m => CAtom n -> Int -> [CAtom n] -> m n (EffTy CoreIR n)
typeOfApplyMethod d i args = do
  ty <- Pi <$> getMethodType d i
  appEffTy ty args

typeOfDictExpr :: EnvReader m => DictExpr n -> m n (CType n)
typeOfDictExpr e = liftM ignoreExcept $ liftEnvReaderT $ case e of
  InstanceDict instanceName args -> do
    instanceDef@(InstanceDef className _ _ _ _) <- lookupInstanceDef instanceName
    sourceName <- getSourceName <$> lookupClassDef className
    PairE (ListE params) _ <- instantiate instanceDef args
    return $ DictTy $ DictType sourceName className params
  InstantiatedGiven given args -> typeOfApp (getType given) args
  SuperclassProj d i -> do
    DictTy (DictType _ className params) <- return $ getType d
    classDef <- lookupClassDef className
    withSubstReaderT $ withInstantiated classDef params \(Abs superclasses _) -> do
      substM $ getSuperclassType REmpty superclasses i
  IxFin n -> liftM DictTy $ ixDictType $ NewtypeTyCon $ Fin n
  DataData ty -> DictTy <$> dataDictType ty

typeOfTopApp :: EnvReader m => TopFunName n -> [SAtom n] -> m n (EffTy SimpIR n)
typeOfTopApp f xs = do
  piTy <- getTypeTopFun f
  instantiate piTy xs

typeOfIndexRef :: (EnvReader m, Fallible1 m, IRRep r) => Type r n -> Atom r n -> m n (Type r n)
typeOfIndexRef (TC (RefType h s)) i = do
  TabPi tabPi <- return s
  eltTy <- instantiate tabPi [i]
  return $ TC $ RefType h eltTy
typeOfIndexRef _ _ = error "expected a ref type"

typeOfProjRef :: EnvReader m => Type r n -> Projection -> m n (Type r n)
typeOfProjRef (TC (RefType h s)) p = do
  TC . RefType h <$> case p of
    ProjectProduct i -> do
      ~(ProdTy tys) <- return s
      return $ tys !! i
    UnwrapNewtype -> do
      case s of
        NewtypeTyCon tc -> snd <$> unwrapNewtypeType tc
        _ -> error "expected a newtype"
typeOfProjRef _ _ = error "expected a reference"

appEffTy  :: (IRRep r, EnvReader m) => Type r n -> [Atom r n] -> m n (EffTy r n)
appEffTy (Pi piTy) xs = instantiate piTy xs
appEffTy t _ = error $ "expected a pi type, got: " ++ pprint t

partialAppType  :: (IRRep r, EnvReader m) => Type r n -> [Atom r n] -> m n (Type r n)
partialAppType (Pi (CorePiType appExpl expls bs effTy)) xs = do
  (_, expls2) <- return $ splitAt (length xs) expls
  PairB bs1 bs2 <- return $ splitNestAt (length xs) bs
  instantiate (Abs bs1 (Pi $ CorePiType appExpl expls2 bs2 effTy)) xs
partialAppType _ _ = error "expected a pi type"

effTyOfHof :: (EnvReader m, IRRep r) => Hof r n -> m n (EffTy r n)
effTyOfHof hof = EffTy <$> hofEffects hof <*> typeOfHof hof

typeOfHof :: (EnvReader m, IRRep r) => Hof r n -> m n (Type r n)
typeOfHof = \case
  For _ ixTy f -> getLamExprType f >>= \case
    PiType (UnaryNest b) (EffTy _ eltTy) -> return $ TabTy (ixTypeDict ixTy) b eltTy
    _ -> error "expected a unary pi type"
  While _ -> return UnitTy
  Linearize f _ -> getLamExprType f >>= \case
    PiType (UnaryNest (binder:>a)) (EffTy Pure b) -> do
      let b' = ignoreHoistFailure $ hoist binder b
      let fLinTy = Pi $ nonDepPiType [a] Pure b'
      return $ PairTy b' fLinTy
    _ -> error "expected a unary pi type"
  Transpose f _ -> getLamExprType f >>= \case
    PiType (UnaryNest (_:>a)) _ -> return a
    _ -> error "expected a unary pi type"
  RunReader _ f -> do
    (resultTy, _) <- getTypeRWSAction f
    return resultTy
  RunWriter _ _ f -> uncurry PairTy <$> getTypeRWSAction f
  RunState _ _ f -> do
    (resultTy, stateTy) <- getTypeRWSAction f
    return $ PairTy resultTy stateTy
  RunIO f -> blockTy f
  RunInit f -> blockTy f
  CatchException ty _ -> return ty

hofEffects :: (EnvReader m, IRRep r) => Hof r n -> m n (EffectRow r n)
hofEffects = \case
  For _ _ f     -> functionEffs f
  While body    -> blockEff body
  Linearize _ _ -> return Pure  -- Body has to be a pure function
  Transpose _ _ -> return Pure  -- Body has to be a pure function
  RunReader _ f -> rwsFunEffects Reader f
  RunWriter d _ f -> maybeInit d <$> rwsFunEffects Writer f
  RunState  d _ f -> maybeInit d <$> rwsFunEffects State  f
  RunIO            f -> deleteEff IOEffect        <$> blockEff f
  RunInit          f -> deleteEff InitEffect      <$> blockEff f
  CatchException _ f -> deleteEff ExceptionEffect <$> blockEff f
  where maybeInit :: IRRep r => Maybe (Atom r i) -> (EffectRow r o -> EffectRow r o)
        maybeInit d = case d of Just _ -> (<>OneEffect InitEffect); Nothing -> id

deleteEff :: IRRep r => Effect r n -> EffectRow r n -> EffectRow r n
deleteEff eff (EffectRow effs t) = EffectRow (effs `eSetDifference` eSetSingleton eff) t

getMethodIndex :: EnvReader m => ClassName n -> SourceName -> m n Int
getMethodIndex className methodSourceName = do
  ClassDef _ methodNames _ _ _ _ _ <- lookupClassDef className
  case elemIndex methodSourceName methodNames of
    Nothing -> error $ methodSourceName ++ " is not a method of " ++ pprint className
    Just i -> return i
{-# INLINE getMethodIndex #-}

getUVarType :: EnvReader m => UVar n -> m n (CType n)
getUVarType = \case
  UAtomVar v -> getType <$> toAtomVar v
  UTyConVar   v -> getTyConNameType v
  UDataConVar v -> getDataConNameType v
  UPunVar     v -> getStructDataConType v
  UClassVar v -> do
    ClassDef _ _ _ roleExpls bs _ _ <- lookupClassDef v
    return $ Pi $ CorePiType ExplicitApp (map snd roleExpls) bs $ EffTy Pure TyKind
  UMethodVar  v -> getMethodNameType v

getMethodNameType :: EnvReader m => MethodName n -> m n (CType n)
getMethodNameType v = liftEnvReaderM $ lookupEnv v >>= \case
  MethodBinding className i -> do
    ClassDef _ _ paramNames _ paramBs scBinders methodTys <- lookupClassDef className
    refreshAbs (Abs paramBs $ Abs scBinders (methodTys !! i)) \paramBs' absPiTy -> do
      let params = Var <$> bindersVars paramBs'
      dictTy <- DictTy <$> dictType (sink className) params
      withFreshBinder noHint dictTy \dictB -> do
        scDicts <- getSuperclassDicts (Var $ binderVar dictB)
        CorePiType appExpl methodExpls methodBs effTy <- instantiate (sink absPiTy) scDicts
        let paramExpls = paramNames <&> \name -> Inferred name Unify
        let expls = paramExpls <> [Inferred Nothing (Synth $ Partial $ succ i)] <> methodExpls
        return $ Pi $ CorePiType appExpl expls (paramBs' >>> UnaryNest dictB >>> methodBs) effTy

getMethodType :: EnvReader m => Dict n -> Int -> m n (CorePiType n)
getMethodType dict i = liftEnvReaderM $ withSubstReaderT do
  ~(DictTy (DictType _ className params)) <- return $ getType dict
  superclassDicts <- getSuperclassDicts dict
  classDef <- lookupClassDef className
  withInstantiated classDef params \ab -> do
    withInstantiated ab superclassDicts \(ListE methodTys) ->
      substM $ methodTys !! i

getTyConNameType :: EnvReader m => TyConName n -> m n (Type CoreIR n)
getTyConNameType v = do
  TyConDef _ expls bs _ <- lookupTyCon v
  case bs of
    Empty -> return TyKind
    _ -> return $ Pi $ CorePiType ExplicitApp (snd <$> expls) bs $ EffTy Pure TyKind

getDataConNameType :: EnvReader m => DataConName n -> m n (Type CoreIR n)
getDataConNameType dataCon = liftEnvReaderM $ withSubstReaderT do
  (tyCon, i) <- lookupDataCon dataCon
  tyConDef <- lookupTyCon tyCon
  buildDataConType tyConDef \expls paramBs' paramVs params -> do
    withInstantiatedNames tyConDef paramVs \(ADTCons dataCons) -> do
      DataConDef _ ab _ _ <- renameM (dataCons !! i)
      refreshAbs ab \dataBs UnitE -> do
        let appExpl = case dataBs of Empty -> ImplicitApp
                                     _     -> ExplicitApp
        let resultTy = NewtypeTyCon $ UserADTType (getSourceName tyConDef) (sink tyCon) (sink params)
        let dataExpls = nestToList (const $ Explicit) dataBs
        return $ Pi $ CorePiType appExpl (expls <> dataExpls) (paramBs' >>> dataBs) (EffTy Pure resultTy)

getStructDataConType :: EnvReader m => TyConName n -> m n (CType n)
getStructDataConType tyCon = liftEnvReaderM $ withSubstReaderT do
  tyConDef <- lookupTyCon tyCon
  buildDataConType tyConDef \expls paramBs' paramVs params -> do
    withInstantiatedNames tyConDef paramVs \(StructFields fields) -> do
      fieldTys <- forM fields \(_, t) -> renameM t
      let resultTy = NewtypeTyCon $ UserADTType (getSourceName tyConDef) (sink tyCon) params
      Abs dataBs resultTy' <- return $ typesAsBinderNest fieldTys resultTy
      let dataExpls = nestToList (const Explicit) dataBs
      return $ Pi $ CorePiType ExplicitApp (expls <> dataExpls) (paramBs' >>> dataBs) (EffTy Pure resultTy')

buildDataConType
  :: (EnvReader m, EnvExtender m)
  => TyConDef n
  -> (forall l. DExt n l => [Explicitness] -> Nest CBinder n l -> [CAtomName l] -> TyConParams l -> m l a)
  -> m n a
buildDataConType (TyConDef _ roleExpls bs _) cont = do
  let expls = snd <$> roleExpls
  expls' <- forM expls \case
    Explicit -> return $ Inferred Nothing Unify
    expl     -> return $ expl
  refreshAbs (Abs bs UnitE) \bs' UnitE -> do
    let vs = nestToNames bs'
    vs' <- mapM toAtomVar vs
    cont expls' bs' vs $ TyConParams expls (Var <$> vs')

makeTyConParams :: EnvReader m => TyConName n -> [CAtom n] -> m n (TyConParams n)
makeTyConParams tc params = do
  TyConDef _ expls _ _ <- lookupTyCon tc
  return $ TyConParams (map snd expls) params

getDataClassName :: (Fallible1 m, EnvReader m) => m n (ClassName n)
getDataClassName = lookupSourceMap "Data" >>= \case
  Nothing -> throw CompilerErr $ "Data interface needed but not defined!"
  Just (UClassVar v) -> return v
  Just _ -> error "not a class var"

dataDictType :: (Fallible1 m, EnvReader m) => CType n -> m n (DictType n)
dataDictType ty = do
  dataClassName <- getDataClassName
  dictType dataClassName [Type ty]

getIxClassName :: (Fallible1 m, EnvReader m) => m n (ClassName n)
getIxClassName = lookupSourceMap "Ix" >>= \case
  Nothing -> throw CompilerErr $ "Ix interface needed but not defined!"
  Just (UClassVar v) -> return v
  Just _ -> error "not a class var"

dictType :: EnvReader m => ClassName n -> [CAtom n] -> m n (DictType n)
dictType className params = do
  ClassDef sourceName _ _ _ _ _ _ <- lookupClassDef className
  return $ DictType sourceName className params

ixDictType :: (Fallible1 m, EnvReader m) => CType n -> m n (DictType n)
ixDictType ty = do
  ixClassName <- getIxClassName
  dictType ixClassName [Type ty]

makePreludeMaybeTy :: EnvReader m => CType n -> m n (CType n)
makePreludeMaybeTy ty = do
  ~(Just (UTyConVar tyConName)) <- lookupSourceMap "Maybe"
  return $ TypeCon "Maybe" tyConName $ TyConParams [Explicit] [Type ty]

-- === computing effects ===

functionEffs :: (IRRep r, EnvReader m) => LamExpr r n -> m n (EffectRow r n)
functionEffs f = getLamExprType f >>= \case
  PiType b (EffTy effs _) -> return $ ignoreHoistFailure $ hoist b effs

rwsFunEffects :: (IRRep r, EnvReader m) => RWS -> LamExpr r n -> m n (EffectRow r n)
rwsFunEffects rws f = getLamExprType f >>= \case
   PiType (BinaryNest h ref) et -> do
     let effs' = ignoreHoistFailure $ hoist ref (etEff et)
     let hVal = Var $ AtomVar (binderName h) (TC HeapType)
     let effs'' = deleteEff (RWSEffect rws hVal) effs'
     return $ ignoreHoistFailure $ hoist h effs''
   _ -> error "Expected a binary function type"

getLamExprType :: (IRRep r, EnvReader m) => LamExpr r n -> m n (PiType r n)
getLamExprType (LamExpr bs body) = liftEnvReaderM $
  refreshAbs (Abs bs body) \bs' body' -> do
    effTy <- blockEffTy body'
    return $ PiType bs' effTy

getTypeRWSAction :: (IRRep r, EnvReader m) => LamExpr r n -> m n (Type r n, Type r n)
getTypeRWSAction f = getLamExprType f >>= \case
  PiType (BinaryNest regionBinder refBinder) (EffTy _ resultTy) -> do
    case binderType refBinder of
      RefTy _ referentTy -> do
        let referentTy' = ignoreHoistFailure $ hoist regionBinder referentTy
        let resultTy' = ignoreHoistFailure $ hoist (PairB regionBinder refBinder) resultTy
        return (resultTy', referentTy')
      _ -> error "expected a ref"
  _ -> error "expected a pi type"

getSuperclassDicts :: EnvReader m => CAtom n -> m n ([CAtom n])
getSuperclassDicts dict = do
  case getType dict of
    DictTy dTy -> do
      ts <- getSuperclassTys dTy
      forM (enumerate ts) \(i, t) -> return $ DictCon t $ SuperclassProj dict i
    _ -> error "expected a dict type"

getSuperclassTys :: EnvReader m => DictType n -> m n [CType n]
getSuperclassTys (DictType _ className params) = do
  ClassDef _ _ _ _ bs superclasses _ <- lookupClassDef className
  forM [0 .. nestLength superclasses - 1] \i -> do
    instantiate (Abs bs $ getSuperclassType REmpty superclasses i) params

getTypeTopFun :: EnvReader m => TopFunName n -> m n (PiType SimpIR n)
getTypeTopFun f = lookupTopFun f >>= \case
  DexTopFun _ (TopLam _ piTy _) _ -> return piTy
  FFITopFun _ iTy -> liftIFunType iTy

asTopLam :: (EnvReader m, IRRep r) => LamExpr r n -> m n (TopLam r n)
asTopLam lam = do
  piTy <- getLamExprType lam
  return $ TopLam False piTy lam

liftIFunType :: (IRRep r, EnvReader m) => IFunType -> m n (PiType r n)
liftIFunType (IFunType _ argTys resultTys) = liftEnvReaderM $ go argTys where
  go :: IRRep r => [BaseType] -> EnvReaderM n (PiType r n)
  go = \case
    [] -> return $ PiType Empty (EffTy (OneEffect IOEffect) resultTy)
      where resultTy = case resultTys of
              [] -> UnitTy
              [t] -> BaseTy t
              [t1, t2] -> PairTy (BaseTy t1) (BaseTy t2)
              _ -> error $ "Not a valid FFI return type: " ++ pprint resultTys
    t:ts -> withFreshBinder noHint (BaseTy t) \b -> do
      PiType bs effTy <- go ts
      return $ PiType (Nest b bs) effTy

-- === Data constraints ===

isData :: EnvReader m => Type CoreIR n -> m n Bool
isData ty = do
  result <- liftEnvReaderT $ withSubstReaderT $ checkDataLike ty
  case runFallibleM result of
    Success () -> return True
    Failure _  -> return False

checkDataLike :: Type CoreIR i -> SubstReaderT Name FallibleEnvReaderM i o ()
checkDataLike ty = case ty of
  TyVar _ -> notData
  TabPi (TabPiType _ b eltTy) -> do
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

checkExtends :: (Fallible m, IRRep r) => EffectRow r n -> EffectRow r n -> m ()
checkExtends allowed (EffectRow effs effTail) = do
  let (EffectRow allowedEffs allowedEffTail) = allowed
  case effTail of
    EffectRowTail _ -> assertEq allowedEffTail effTail ""
    NoTail -> return ()
  forM_ (eSetToList effs) \eff -> unless (eff `eSetMember` allowedEffs) $
    throw CompilerErr $ "Unexpected effect: " ++ pprint eff ++
                      "\nAllowed: " ++ pprint allowed
{-# INLINE checkExtends #-}
