-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module QueryType (module QueryType, module QueryTypePure, toAtomVar) where

import Control.Category ((>>>))
import Control.Monad
import Data.List (elemIndex)

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

getDestLamExprType :: LamExpr SimpIR n -> PiType SimpIR n
getDestLamExprType (LamExpr bsRefB body) =
  case popNest bsRefB of
    Just (PairB bs (bDest:>RawRefTy ansTy)) -> do
      let resultEffs = ignoreHoistFailure $ hoist bDest $ getEffects body
      PiType bs $ EffTy resultEffs ansTy
    _ -> error "expected trailing dest binder"

typeOfApp  :: (IRRep r, EnvReader m) => Type r n -> [Atom r n] -> m n (Type r n)
typeOfApp (Pi (CorePiType _ bs (EffTy _ resultTy))) xs = do
  let subst = bs @@> fmap SubstVal xs
  applySubst subst resultTy
typeOfApp _ _ = error "expected a pi type"

typeOfTabApp :: (IRRep r, EnvReader m) => Type r n -> [Atom r n] -> m n (Type r n)
typeOfTabApp t [] = return t
typeOfTabApp (TabTy _ (b:>_) resultTy) (i:rest) = do
  resultTy' <- applySubst (b@>SubstVal i) resultTy
  typeOfTabApp resultTy' rest
typeOfTabApp ty _ = error $ "expected a table type. Got: " ++ pprint ty

typeOfApplyMethod :: EnvReader m => CAtom n -> Int -> [CAtom n] -> m n (EffTy CoreIR n)
typeOfApplyMethod d i args = do
  ty <- Pi <$> getMethodType d i
  appEffTy ty args

typeOfDictExpr :: EnvReader m => DictExpr n -> m n (CType n)
typeOfDictExpr e = liftM ignoreExcept $ liftEnvReaderT $ case e of
  InstanceDict instanceName args -> do
    InstanceDef className bs params _ <- lookupInstanceDef instanceName
    ClassDef sourceName _ _ _ _ _ <- lookupClassDef className
    ListE params' <- applySubst (bs @@> map SubstVal args) $ ListE params
    return $ DictTy $ DictType sourceName className params'
  InstantiatedGiven given args -> typeOfApp (getType given) args
  SuperclassProj d i -> do
    DictTy (DictType _ className params) <- return $ getType d
    ClassDef _ _ _ bs superclasses _ <- lookupClassDef className
    applySubst (bs @@> map SubstVal params) $
      getSuperclassType REmpty superclasses i
  IxFin n -> liftM DictTy $ ixDictType $ NewtypeTyCon $ Fin n
  DataData ty -> DictTy <$> dataDictType ty

typeOfTopApp :: EnvReader m => TopFunName n -> [SAtom n] -> m n (EffTy SimpIR n)
typeOfTopApp f xs = do
  PiType bs effTy <- getTypeTopFun f
  applySubst (bs @@> map SubstVal xs) effTy

typeOfIndexRef :: (EnvReader m, Fallible1 m, IRRep r) => Type r n -> Atom r n -> m n (Type r n)
typeOfIndexRef (TC (RefType h s)) i = do
  TabTy _ (b:>_) eltTy <- return s
  eltTy' <- applyAbs (Abs b eltTy) (SubstVal i)
  return $ TC $ RefType h eltTy'
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
appEffTy (Pi (CorePiType _ bs effTy)) xs = do
  let subst = bs @@> fmap SubstVal xs
  applySubst subst effTy
appEffTy t _ = error $ "expected a pi type, got: " ++ pprint t

partialAppType  :: (IRRep r, EnvReader m) => Type r n -> [Atom r n] -> m n (Type r n)
partialAppType (Pi (CorePiType expl bs effTy)) xs = do
  PairB bs1 bs2 <- return $ splitNestAt (length xs) bs
  let subst = bs1 @@> fmap SubstVal xs
  applySubst subst $ Pi $ CorePiType expl bs2 effTy
partialAppType _ _ = error "expected a pi type"

appEffects :: (EnvReader m, IRRep r) => Type r n -> [Atom r n] -> m n (EffectRow r n)
appEffects (Pi (CorePiType _ bs (EffTy effs _))) xs = do
  let subst = bs @@> fmap SubstVal xs
  applySubst subst effs
appEffects _ _ = error "expected a pi type"

effTyOfHof :: (EnvReader m, IRRep r) => Hof r n -> m n (EffTy r n)
effTyOfHof hof = EffTy <$> hofEffects hof <*> typeOfHof hof

typeOfHof :: (EnvReader m, IRRep r) => Hof r n -> m n (Type r n)
typeOfHof = \case
  For _ ixTy f -> case getLamExprType f of
    PiType (UnaryNest b) (EffTy _ eltTy) -> return $ TabTy (ixTypeDict ixTy) b eltTy
    _ -> error "expected a unary pi type"
  While _ -> return UnitTy
  Linearize f _ -> case getLamExprType f of
    PiType (UnaryNest (binder:>a)) (EffTy Pure b) -> do
      let b' = ignoreHoistFailure $ hoist binder b
      let fLinTy = Pi $ nonDepPiType [a] Pure b'
      return $ PairTy b' fLinTy
    _ -> error "expected a unary pi type"
  Transpose f _ -> case getLamExprType f of
    PiType (UnaryNest (_:>a)) _ -> return a
    _ -> error "expected a unary pi type"
  RunReader _ f -> return resultTy
    where (resultTy, _) = getTypeRWSAction f
  RunWriter _ _ f -> return $ uncurry PairTy $ getTypeRWSAction f
  RunState _ _ f -> return $ PairTy resultTy stateTy
    where (resultTy, stateTy) = getTypeRWSAction f
  RunIO f -> return $ getType f
  RunInit f -> return $ getType f
  CatchException ty _ -> return ty

hofEffects :: (EnvReader m, IRRep r) => Hof r n -> m n (EffectRow r n)
hofEffects = \case
  For _ _ f     -> functionEffs f
  While body    -> return $ getEffects body
  Linearize _ _ -> return Pure  -- Body has to be a pure function
  Transpose _ _ -> return Pure  -- Body has to be a pure function
  RunReader _ f -> rwsFunEffects Reader f
  RunWriter d _ f -> maybeInit d <$> rwsFunEffects Writer f
  RunState  d _ f -> maybeInit d <$> rwsFunEffects State  f
  RunIO          f -> return $ deleteEff IOEffect        $ getEffects f
  RunInit        f -> return $ deleteEff InitEffect      $ getEffects f
  CatchException _ f -> return $ deleteEff ExceptionEffect $ getEffects f
  where maybeInit :: IRRep r => Maybe (Atom r i) -> (EffectRow r o -> EffectRow r o)
        maybeInit d = case d of Just _ -> (<>OneEffect InitEffect); Nothing -> id

deleteEff :: IRRep r => Effect r n -> EffectRow r n -> EffectRow r n
deleteEff eff (EffectRow effs t) = EffectRow (effs `eSetDifference` eSetSingleton eff) t

getMethodIndex :: EnvReader m => ClassName n -> SourceName -> m n Int
getMethodIndex className methodSourceName = do
  ClassDef _ methodNames _ _ _ _ <- lookupClassDef className
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
    ClassDef _ _ _ bs _ _ <- lookupClassDef v
    let bs' = fmapNest (\(RolePiBinder _ b) -> b) bs
    return $ Pi $ CorePiType ExplicitApp bs' $ EffTy Pure TyKind
  UMethodVar  v -> getMethodNameType v
  UEffectVar   _ -> error "not implemented"
  UEffectOpVar _ -> error "not implemented"

getMethodNameType :: EnvReader m => MethodName n -> m n (CType n)
getMethodNameType v = liftEnvReaderM $ lookupEnv v >>= \case
  MethodBinding className i -> do
    ClassDef _ _ paramNames paramBs scBinders methodTys <- lookupClassDef className
    let paramBs' = zipWithNest paramBs paramNames \(RolePiBinder _ (WithExpl _ b)) paramName ->
          WithExpl (Inferred paramName Unify) b
    refreshAbs (Abs paramBs' $ Abs scBinders (methodTys !! i)) \paramBs'' (Abs scBinders' piTy) -> do
      let params = Var <$> nestToAtomVars (fmapNest withoutExpl paramBs'')
      dictTy <- DictTy <$> dictType (sink className) params
      withFreshBinder noHint dictTy \dictB -> do
        scDicts <- getSuperclassDicts (Var $ binderVar dictB)
        piTy' <- applySubst (scBinders'@@>(SubstVal<$>scDicts)) piTy
        CorePiType appExpl methodBs effTy <- return piTy'
        let dictBs = UnaryNest $ WithExpl (Inferred Nothing (Synth $ Partial $ succ i)) dictB
        return $ Pi $ CorePiType appExpl (paramBs'' >>> dictBs >>> methodBs) effTy

getMethodType :: EnvReader m => Dict n -> Int -> m n (CorePiType n)
getMethodType dict i = do
  ~(DictTy (DictType _ className params)) <- return $ getType dict
  ClassDef _ _ _ paramBs classBs methodTys <- lookupClassDef className
  let methodTy = methodTys !! i
  superclassDicts <- getSuperclassDicts dict
  let subst = (    paramBs @@> map SubstVal params
               <.> classBs @@> map SubstVal superclassDicts)
  applySubst subst methodTy
{-# INLINE getMethodType #-}


getTyConNameType :: EnvReader m => TyConName n -> m n (Type CoreIR n)
getTyConNameType v = do
  TyConDef _ bs _ <- lookupTyCon v
  case bs of
    Empty -> return TyKind
    _ -> do
      let bs' = fmapNest (\(RolePiBinder _ b) -> b) bs
      return $ Pi $ CorePiType ExplicitApp bs' $ EffTy Pure TyKind

getDataConNameType :: EnvReader m => DataConName n -> m n (Type CoreIR n)
getDataConNameType dataCon = liftEnvReaderM do
  (tyCon, i) <- lookupDataCon dataCon
  lookupTyCon tyCon >>= \case
    tyConDef@(TyConDef tcSn paramBs ~(ADTCons dataCons)) ->
      buildDataConType tyConDef \paramBs' paramVs params -> do
        DataConDef _ ab _ _ <- applyRename (paramBs @@> paramVs) (dataCons !! i)
        refreshAbs ab \dataBs UnitE -> do
          let appExpl = case dataBs of Empty -> ImplicitApp
                                       _     -> ExplicitApp
          let resultTy = NewtypeTyCon $ UserADTType tcSn (sink tyCon) (sink params)
          let dataBs' = fmapNest (WithExpl Explicit) dataBs
          return $ Pi $ CorePiType appExpl (paramBs' >>> dataBs') (EffTy Pure resultTy)

getStructDataConType :: EnvReader m => TyConName n -> m n (CType n)
getStructDataConType tyCon = liftEnvReaderM do
  tyConDef@(TyConDef tcSn paramBs ~(StructFields fields)) <- lookupTyCon tyCon
  buildDataConType tyConDef \paramBs' paramVs params -> do
    fieldTys <- forM fields \(_, t) -> applyRename (paramBs @@> paramVs) t
    let resultTy = NewtypeTyCon $ UserADTType tcSn (sink tyCon) params
    Abs dataBs resultTy' <- return $ typesAsBinderNest fieldTys resultTy
    let dataBs' = fmapNest (WithExpl Explicit) dataBs
    return $ Pi $ CorePiType ExplicitApp (paramBs' >>> dataBs') (EffTy Pure resultTy')

buildDataConType
  :: (EnvReader m, EnvExtender m)
  => TyConDef n
  -> (forall l. DExt n l => Nest (WithExpl CBinder) n l -> [CAtomName l] -> TyConParams l -> m l a)
  -> m n a
buildDataConType (TyConDef _ bs _) cont = do
  bs' <- return $ forNest bs \(RolePiBinder _ (WithExpl expl b)) -> case expl of
    Explicit -> WithExpl (Inferred Nothing Unify) b
    _        -> WithExpl expl b
  refreshAbs (Abs bs' UnitE) \bs'' UnitE -> do
    let expls = nestToList (\(RolePiBinder _ b) -> getExpl b) bs
    let vs = nestToNames bs''
    vs' <- mapM toAtomVar vs
    cont bs'' vs $ TyConParams expls (Var <$> vs')

makeTyConParams :: EnvReader m => TyConName n -> [CAtom n] -> m n (TyConParams n)
makeTyConParams tc params = do
  TyConDef _ paramBs _ <- lookupTyCon tc
  let expls = nestToList (\(RolePiBinder _ b) -> getExpl b) paramBs
  return $ TyConParams expls params

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
  ClassDef sourceName _ _ _ _ _ <- lookupClassDef className
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
functionEffs f = case getLamExprType f of
  PiType b (EffTy effs _) -> return $ ignoreHoistFailure $ hoist b effs

rwsFunEffects :: (IRRep r, EnvReader m) => RWS -> LamExpr r n -> m n (EffectRow r n)
rwsFunEffects rws f = return case getLamExprType f of
   PiType (BinaryNest h ref) et -> do
     let effs' = ignoreHoistFailure $ hoist ref (etEff et)
     let hVal = Var $ AtomVar (binderName h) (TC HeapType)
     let effs'' = deleteEff (RWSEffect rws hVal) effs'
     ignoreHoistFailure $ hoist h effs''
   _ -> error "Expected a binary function type"

getLamExprType :: IRRep r => LamExpr r n -> PiType r n
getLamExprType (LamExpr bs body) = PiType bs (EffTy (getEffects body) (getType body))

getTypeRWSAction :: IRRep r => LamExpr r n -> (Type r n, Type r n)
getTypeRWSAction f = case getLamExprType f of
  PiType (BinaryNest regionBinder refBinder) (EffTy _ resultTy) -> do
    case binderType refBinder of
      RefTy _ referentTy -> do
        let referentTy' = ignoreHoistFailure $ hoist regionBinder referentTy
        let resultTy' = ignoreHoistFailure $ hoist (PairB regionBinder refBinder) resultTy
        (resultTy', referentTy')
      _ -> error "expected a ref"
  _ -> error "expected a pi type"

computeAbsEffects :: (IRRep r, EnvExtender m, RenameE e)
  => Abs (Nest (Decl r)) e n -> m n (Abs (Nest (Decl r)) (EffectRow r `PairE` e) n)
computeAbsEffects it = refreshAbs it \decls result -> do
  effs <- declNestEffects decls
  return $ Abs decls (effs `PairE` result)
{-# INLINE computeAbsEffects #-}

declNestEffects :: (IRRep r, EnvReader m) => Nest (Decl r) n l -> m l (EffectRow r l)
declNestEffects decls = liftEnvReaderM $ declNestEffectsRec decls mempty
{-# INLINE declNestEffects #-}

declNestEffectsRec :: IRRep r => Nest (Decl r) n l -> EffectRow r l -> EnvReaderM l (EffectRow r l)
declNestEffectsRec Empty !acc = return acc
declNestEffectsRec n@(Nest decl rest) !acc = withExtEvidence n do
  expr <- sinkM $ declExpr decl
  acc' <- sinkM $ acc <> (getEffects expr)
  declNestEffectsRec rest acc'
  where
    declExpr :: Decl r n l -> Expr r n
    declExpr (Let _ (DeclBinding _ expr)) = expr

instantiateHandlerType :: EnvReader m => HandlerName n -> CType n -> [CAtom n] -> m n (CType n)
instantiateHandlerType hndName r args = do
  HandlerDef _ rb bs _effs retTy _ _ <- lookupHandlerDef hndName
  applySubst (rb @> (SubstVal (Type r)) <.> bs @@> (map SubstVal args)) retTy

getSuperclassDicts :: EnvReader m => CAtom n -> m n ([CAtom n])
getSuperclassDicts dict = do
  case getType dict of
    DictTy dTy -> do
      ts <- getSuperclassTys dTy
      forM (enumerate ts) \(i, t) -> return $ DictCon t $ SuperclassProj dict i
    _ -> error "expected a dict type"

getSuperclassTys :: EnvReader m => DictType n -> m n [CType n]
getSuperclassTys (DictType _ className params) = do
  ClassDef _ _ _ bs superclasses _ <- lookupClassDef className
  forM [0 .. nestLength superclasses - 1] \i -> do
    applySubst (bs @@> map SubstVal params) $
      getSuperclassType REmpty superclasses i

getTypeTopFun :: EnvReader m => TopFunName n -> m n (PiType SimpIR n)
getTypeTopFun f = lookupTopFun f >>= \case
  DexTopFun _ piTy _ _ -> return piTy
  FFITopFun _ iTy -> liftIFunType iTy

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
