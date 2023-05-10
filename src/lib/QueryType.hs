-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module QueryType where

import Control.Category ((>>>))
import Control.Monad
import Data.Foldable (toList)
import Data.Functor ((<&>))
import Data.List (elemIndex)
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M

import Types.Primitives
import Types.Core
import Types.Source
import Types.Imp
import IRVariants
import Core
import CheapReduction
import Err
import LabeledItems
import Name hiding (withFreshM)
import Subst
import Util
import PPrint ()

-- === Main API for querying types ===

getTypeSubst :: (SubstReader AtomSubstVal m, EnvReader2 m, HasType r e)
             => e i -> m i o (Type r o)
getTypeSubst e = do
  subst <- getSubst
  liftTypeQueryM subst $ getTypeE e
{-# INLINE getTypeSubst #-}

getType :: (EnvReader m, HasType r e) => e n -> m n (Type r n)
getType e = liftTypeQueryM idSubst $ getTypeE e
{-# INLINE getType #-}

getLamExprType :: (IRRep r, EnvReader m) => LamExpr r n -> m n (PiType r n)
getLamExprType lam = liftTypeQueryM idSubst $ getLamExprTypeE lam
{-# INLINE getLamExprType #-}

-- TODO: Fold this into a real HasType instance
getDestBlockType :: (IRRep r, EnvReader m) => DestBlock r n -> m n (Type r n)
getDestBlockType (DestBlock (_:>RawRefTy ansTy) _) = return ansTy
getDestBlockType _ = error "Expected a reference type for body destination"
{-# INLINE getDestBlockType #-}

getNaryDestLamExprType :: (IRRep r, EnvReader m) => DestLamExpr r n -> m n (PiType r n)
getNaryDestLamExprType lam = liftTypeQueryM idSubst $ getDestLamExprType lam
{-# INLINE getNaryDestLamExprType #-}

getReferentTypeRWSAction :: (EnvReader m, IRRep r) => LamExpr r o -> m o (Type r o)
getReferentTypeRWSAction f = liftTypeQueryM idSubst $ liftM snd $ getTypeRWSAction f

sourceNameType :: (EnvReader m, Fallible1 m) => SourceName -> m n (Type CoreIR n)
sourceNameType v = do
  lookupSourceMap v >>= \case
    Nothing -> throw UnboundVarErr $ pprint v
    Just uvar -> liftTypeQueryM idSubst $ getTypeE uvar

-- === Querying effects ===

isPure :: (IRRep r, EnvReader m, HasEffectsE e r) => e n -> m n Bool
isPure e = getEffects e <&> \case
  Pure -> True
  _    -> False

getEffects :: (EnvReader m, HasEffectsE e r) => e n -> m n (EffectRow r n)
getEffects e = liftTypeQueryM idSubst $ getEffectsImpl e
{-# INLINE getEffects #-}

getEffectsSubst :: (EnvReader2 m, SubstReader AtomSubstVal m, HasEffectsE e r)
                => e i -> m i o (EffectRow r o)
getEffectsSubst e = do
  subst <- getSubst
  liftTypeQueryM subst $ getEffectsImpl e
{-# INLINE getEffectsSubst #-}

-- === Exposed helpers for querying types and effects ===

caseAltsBinderTys :: (IRRep r, Fallible1 m, EnvReader m)
                  => Type r n -> m n [Type r n]
caseAltsBinderTys ty = case ty of
  SumTy types -> return types
  NewtypeTyCon t -> case t of
    UserADTType _ defName params -> do
      def <- lookupTyCon defName
      cons <- instantiateTyConDef def params
      return [repTy | DataConDef _ _ repTy _ <- cons]
    _ -> fail msg
  _ -> fail msg
  where msg = "Case analysis only supported on ADTs, not on " ++ pprint ty

extendEffect :: IRRep r => Effect r n -> EffectRow r n -> EffectRow r n
extendEffect eff (EffectRow effs t) = EffectRow (effs <> eSetSingleton eff) t

getAppType :: (IRRep r, EnvReader m) => Type r n -> [Atom r n] -> m n (Type r n)
getAppType f xs = liftTypeQueryM idSubst $ appType f xs
{-# INLINE getAppType #-}

getTabAppType :: (IRRep r, EnvReader m) => Type r n -> [Atom r n] -> m n (Type r n)
getTabAppType f xs = liftTypeQueryM idSubst $ typeTabApp f xs
{-# INLINE getTabAppType #-}

getReferentTy :: (IRRep r, MonadFail m) => EmptyAbs (PairB (Binder r) (Binder r)) n -> m (Type r n)
getReferentTy (Abs (PairB hB refB) UnitE) = do
  RefTy _ ty <- return $ binderType refB
  HoistSuccess ty' <- return $ hoist hB ty
  return ty'
{-# INLINE getReferentTy #-}

getMethodIndex :: EnvReader m => ClassName n -> SourceName -> m n Int
getMethodIndex className methodSourceName = do
  ClassDef _ methodNames _ _ _ _ <- lookupClassDef className
  case elemIndex methodSourceName methodNames of
    Nothing -> error $ methodSourceName ++ " is not a method of " ++ pprint className
    Just i -> return i
{-# INLINE getMethodIndex #-}

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

instance HasType CoreIR UVar where
  getTypeE = \case
    UAtomVar    v -> getTypeE $ Var v
    UTyConVar   v -> getTypeE v
    UDataConVar v -> getTypeE v
    UClassVar   v -> getTypeE v
    UMethodVar  v -> getTypeE v
    UEffectVar   _ -> error "not implemented"
    UEffectOpVar _ -> error "not implemented"
    UHandlerVar  _ -> error "not implemented"

instance HasType CoreIR ClassName where
  getTypeE v = do
    ClassDef _ _ _ bs _ _ <- substM v >>= lookupClassDef
    let bs' = fmapNest (\(RolePiBinder _ b) -> b) bs
    return $ Pi $ CorePiType ExplicitApp bs' Pure TyKind

instance HasType CoreIR MethodName where
  getTypeE v = substM v >>= lookupEnv >>= \case
    MethodBinding className i -> do
      classDef@(ClassDef _ _ paramNames paramBs scBinders methodTys) <- lookupClassDef className
      let paramBs' = zipWithNest paramBs paramNames \(RolePiBinder _ (WithExpl _ b)) paramName ->
            WithExpl (Inferred paramName Unify) b
      refreshAbs (Abs paramBs' $ Abs scBinders (methodTys !! i)) \paramBs'' (Abs scBinders' piTy) -> do
        let params = nestToList (Var . sink . binderName) paramBs''
        dictTy <- DictTy <$> dictType (sink className) params
        withFreshBinder noHint dictTy \dictB -> do
          let scDicts = getSuperclassDicts (sink classDef) (Var $ binderName dictB)
          piTy' <- applySubst (scBinders'@@>(SubstVal<$>scDicts)) piTy
          CorePiType appExpl methodBs effs resultTy <- return piTy'
          let dictBs = UnaryNest $ WithExpl (Inferred Nothing (Synth $ Partial $ succ i)) dictB
          return $ Pi $ CorePiType appExpl (paramBs'' >>> dictBs >>> methodBs) effs resultTy

getMethodType :: EnvReader m => Dict n -> Int -> m n (CorePiType n)
getMethodType dict i = do
  ~(DictTy (DictType _ className params)) <- getType dict
  def@(ClassDef _ _ _ paramBs classBs methodTys) <- lookupClassDef className
  let methodTy = methodTys !! i
  let superclassDicts = getSuperclassDicts def dict
  let subst = (    paramBs @@> map SubstVal params
               <.> classBs @@> map SubstVal superclassDicts)
  applySubst subst methodTy
{-# INLINE getMethodType #-}

instance HasType CoreIR TyConName where
  getTypeE v = do
    TyConDef _ bs _ <- substM v >>= lookupTyCon
    case bs of
      Empty -> return TyKind
      _ -> do
        let bs' = fmapNest (\(RolePiBinder _ b) -> b) bs
        return $ Pi $ CorePiType ExplicitApp bs' Pure TyKind

instance HasType CoreIR DataConName where
  getTypeE dataCon = do
    (tyCon, i) <- lookupDataCon =<< substM dataCon
    dropSubst $ Pi <$> getDataConType tyCon i

getDataConType :: TyConName i -> Int -> TypeQueryM i o (CorePiType o)
getDataConType tyCon i = do
  tyCon' <- substM tyCon
  TyConDef tcSn paramBs dataCons <- lookupTyCon tyCon'
  DataConDef _ (Abs dataBs UnitE) _ _ <- return $ dataCons !! i
  paramBs' <- return $ forNest paramBs \(RolePiBinder _ (WithExpl expl b)) -> case expl of
    Explicit -> WithExpl (Inferred Nothing Unify) b
    _        -> WithExpl expl b
  let dataBs' = fmapNest (WithExpl Explicit) dataBs
  refreshAbs (Abs paramBs' (Abs dataBs' UnitE)) \paramBs'' ab -> do
    params <- makeTyConParams (sink tyCon') $ Var <$> nestToNames paramBs''
    refreshAbs ab \dataBs'' UnitE -> do
      let appExpl = case dataBs'' of Empty -> ImplicitApp
                                     _     -> ExplicitApp
      let resultTy = NewtypeTyCon $ UserADTType tcSn (sink tyCon') (sink params)
      return $ CorePiType appExpl (paramBs'' >>> dataBs'') Pure resultTy

makeTyConParams :: EnvReader m => TyConName n -> [CAtom n] -> m n (TyConParams n)
makeTyConParams tc params = do
  TyConDef _ paramBs _ <- lookupTyCon tc
  let expls = nestToList (\(RolePiBinder _ b) -> getExpl b) paramBs
  return $ TyConParams expls params

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

-- === computing effects ===

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
  deff <- getEffects expr
  acc' <- sinkM $ acc <> deff
  declNestEffectsRec rest acc'
  where
    declExpr :: Decl r n l -> Expr r n
    declExpr (Let _ (DeclBinding _ _ expr)) = expr

-- === implementation of querying types ===

newtype TypeQueryM (i::S) (o::S) (a :: *) = TypeQueryM {
  runTypeQueryM :: SubstReaderT AtomSubstVal EnvReaderM i o a }
  deriving ( Functor, Applicative, Monad
           , EnvReader, EnvExtender, ScopeReader
           , SubstReader AtomSubstVal)

liftTypeQueryM :: (EnvReader m) => Subst AtomSubstVal i o
               -> TypeQueryM i o a -> m o a
liftTypeQueryM subst act =
  liftEnvReaderM $
    runSubstReaderT subst $
      runTypeQueryM act
{-# INLINE liftTypeQueryM #-}

instance MonadFail (TypeQueryM i o) where
  fail = error
  {-# INLINE fail #-}

instance Fallible (TypeQueryM i o) where
  throwErrs err = error $ pprint err
  {-# INLINE throwErrs #-}
  addErrCtx = const id
  {-# INLINE addErrCtx #-}

class HasType (r::IR) (e::E) | e -> r where
  getTypeE :: e i -> TypeQueryM i o (Type r o)

instance IRRep r => HasType r (AtomName r) where
  getTypeE name = do
    substM (Var name) >>= \case
      Var name' -> atomBindingType <$> lookupAtomName name'
      atom -> getType atom
  {-# INLINE getTypeE #-}

instance IRRep r => HasType r (Atom r) where
  getTypeE :: forall i o. Atom r i -> TypeQueryM i o (Type r o)
  getTypeE atom = case atom of
    Var name -> getTypeE name
    Lam (CoreLamExpr piTy _) -> Pi <$> substM piTy
    Pi _ -> return TyKind
    TabPi _ -> return TyKind
    DepPair _ _ ty -> do
      ty' <- substM ty
      return $ DepPairTy ty'
    DepPairTy _ -> return TyKind
    Con con -> getTypePrimCon con
    TC _ -> return TyKind
    Eff _ -> return EffKind
    PtrVar v -> substM v >>= lookupEnv >>= \case
      PtrBinding ty _ -> return $ PtrTy ty
    DictCon dictExpr -> getTypeE dictExpr
    DictTy (DictType _ _ _) -> return TyKind
    NewtypeTyCon con -> getTypeE con
    NewtypeCon con x -> getNewtypeType con x
    RepValAtom repVal -> do RepVal ty _ <- substM repVal; return ty
    ProjectElt (ProjectProduct i) x -> do
      ty <- getTypeE x
      x' <- substM x
      projType i ty x'
    ProjectElt UnwrapNewtype x -> do
      getTypeE x >>= \case
        NewtypeTyCon tc -> snd <$> unwrapNewtypeType tc
        ty -> error $ "Not a newtype: " ++ pprint x ++ ":" ++ pprint ty
    SimpInCore x -> getTypeE x
    DictHole _ ty _ -> substM ty

instance HasType CoreIR SimpInCore where
  getTypeE = \case
    LiftSimp t _ -> substM t
    LiftSimpFun piTy _ -> Pi <$> substM piTy
    TabLam t _ -> TabPi <$> substM t
    ACase _ _ t -> substM t

instance HasType CoreIR NewtypeTyCon where
  getTypeE = \case
    Nat               -> return TyKind
    Fin _             -> return TyKind
    EffectRowKind     -> return TyKind
    LabelType         -> return TyKind
    RecordTyCon  _    -> return TyKind
    LabeledRowKindTC  -> return TyKind
    UserADTType _ _ _ -> return TyKind
    LabelCon _        -> return $ NewtypeTyCon LabelType
    LabeledRowCon _   -> return LabeledRowKind

getNewtypeType :: NewtypeCon i -> CAtom i -> TypeQueryM i o (CType o)
getNewtypeType con x = case con of
  NatCon          -> return $ NewtypeTyCon Nat
  FinCon n        -> NewtypeTyCon . Fin <$> substM n
  RecordCon labels -> do
    TC (ProdType tys) <- getTypeE x
    return $ StaticRecordTy $ restructure tys labels
  UserADTData d params -> do
    d' <- substM d
    params' <- substM params
    TyConDef sn _ _ <- lookupTyCon d'
    return $ NewtypeTyCon $ UserADTType sn d' params'

getTypePrimCon :: IRRep r => PrimCon r (Atom r i) -> TypeQueryM i o (Type r o)
getTypePrimCon con = case con of
  Lit l -> return $ BaseTy $ litType l
  ProdCon xs -> ProdTy <$> mapM getTypeE xs
  SumCon tys _ _ -> SumTy <$> traverse substM tys
  HeapVal       -> return $ TC HeapType

getIxClassName :: (Fallible1 m, EnvReader m) => m n (ClassName n)
getIxClassName = lookupSourceMap "Ix" >>= \case
  Nothing -> throw CompilerErr $ "Ix interface needed but not defined!"
  Just (UClassVar v) -> return v
  Just _ -> error "not a class var"

dictType :: (Fallible1 m, EnvReader m) => ClassName n -> [CType n] -> m n (DictType n)
dictType className params = do
  ClassDef sourceName _ _ _ _ _ <- lookupClassDef className
  return $ DictType sourceName className params

ixDictType :: (Fallible1 m, EnvReader m) => CType n -> m n (DictType n)
ixDictType ty = do
  ixClassName <- getIxClassName
  dictType ixClassName [ty]

getDataClassName :: (Fallible1 m, EnvReader m) => m n (ClassName n)
getDataClassName = lookupSourceMap "Data" >>= \case
  Nothing -> throw CompilerErr $ "Data interface needed but not defined!"
  Just (UClassVar v) -> return v
  Just _ -> error "not a class var"

dataDictType :: (Fallible1 m, EnvReader m) => CType n -> m n (DictType n)
dataDictType ty = do
  dataClassName <- getDataClassName
  dictType dataClassName [ty]

makePreludeMaybeTy :: EnvReader m => CType n -> m n (CType n)
makePreludeMaybeTy ty = do
  ~(Just (UTyConVar tyConName)) <- lookupSourceMap "Maybe"
  return $ TypeCon "Maybe" tyConName $ TyConParams [Explicit] [ty]

appType  :: IRRep r => Type r o -> [Atom r i] -> TypeQueryM i o (Type r o)
appType fTy xs = do
  Pi (CorePiType _ bs _ resultTy) <- return fTy
  xs' <- mapM substM xs
  let subst = bs @@> fmap SubstVal xs'
  applySubst subst resultTy

appEffects  :: IRRep r => Type r o -> [Atom r i] -> TypeQueryM i o (EffectRow r o)
appEffects fTy xs = do
  Pi (CorePiType _ bs effs _) <- return fTy
  xs' <- mapM substM xs
  let subst = bs @@> fmap SubstVal xs'
  applySubst subst effs

typeTabApp :: IRRep r => Type r o -> [Atom r i] -> TypeQueryM i o (Type r o)
typeTabApp ty [] = return ty
typeTabApp ty (i:rest) = do
  TabTy (b:>_) resultTy <- return ty
  i' <- substM i
  resultTy' <- applySubst (b@>SubstVal i') resultTy
  typeTabApp resultTy' rest

instance HasType CoreIR DictExpr where
  getTypeE e =  case e of
    InstanceDict instanceName args -> do
      instanceName' <- substM instanceName
      InstanceDef className bs params _ <- lookupInstanceDef instanceName'
      ClassDef sourceName _ _ _ _ _ <- lookupClassDef className
      args' <- mapM substM args
      ListE params' <- applySubst (bs @@> map SubstVal args') $ ListE params
      return $ DictTy $ DictType sourceName className params'
    InstantiatedGiven given args -> do
      givenTy <- getTypeE given
      appType givenTy (toList args)
    SuperclassProj d i -> do
      DictTy (DictType _ className params) <- getTypeE d
      ClassDef _ _ _ bs superclasses _ <- lookupClassDef className
      applySubst (bs @@> map SubstVal params) $
        getSuperclassType REmpty superclasses i
    IxFin n -> do
      n' <- substM n
      liftM DictTy $ ixDictType $ NewtypeTyCon $ Fin n'
    DataData ty -> DictTy <$> (dataDictType =<< substM ty)

getSuperclassType :: RNest CBinder n l -> Nest CBinder l l' -> Int -> CType n
getSuperclassType _ Empty = error "bad index"
getSuperclassType bsAbove (Nest b bs) = \case
  0 -> ignoreHoistFailure $ hoist bsAbove $ binderType b
  i -> getSuperclassType (RNest bsAbove b) bs (i-1)

instance IRRep r => HasType r (Expr r) where
  getTypeE expr = case expr of
    App f xs -> do
      fTy <- getTypeE f
      appType fTy $ toList xs
    TopApp f xs -> do
      PiType bs _ resultTy <- getTypeTopFun =<< substM f
      xs' <- mapM substM xs
      applySubst (bs @@> map SubstVal xs') resultTy
    TabApp f xs -> do
      fTy <- getTypeE f
      typeTabApp fTy xs
    Atom x   -> getTypeE x
    TabCon _ ty _ -> substM ty
    DAMOp           op -> getTypeE op
    UserEffectOp    op -> getTypeE op
    PrimOp          op -> getTypeE $ ComposeE op
    RecordOp        op -> getTypeE $ ComposeE op
    Hof  hof -> getTypeHof hof
    Case _ _ resultTy _ -> substM resultTy
    ApplyMethod dict i args -> do
      dict' <- substM dict
      methodTy <- getMethodType dict' i
      appType (Pi methodTy) args
    RefOp ref m -> do
      TC (RefType h s) <- getTypeE ref
      case m of
        MGet        -> return s
        MPut _      -> return UnitTy
        MAsk        -> return s
        MExtend _ _ -> return UnitTy
        IndexRef i -> do
          TabTy (b:>_) eltTy <- return s
          i' <- substM i
          eltTy' <- applyAbs (Abs b eltTy) (SubstVal i')
          return $ TC $ RefType h eltTy'
        ProjRef i -> do
          ProdTy tys <- return s
          return $ TC $ RefType h $ tys !! i

instance IRRep r => HasType r (DAMOp r) where
  getTypeE = \case
    AllocDest ty -> RawRefTy <$> substM ty
    Place _ _ -> return UnitTy
    Freeze ref -> getTypeE ref >>= \case
      RawRefTy ty -> return ty
      ty -> error $ "Not a reference type: " ++ pprint ty
    Seq _ _ cinit _ -> getTypeE cinit
    RememberDest d _ -> getTypeE d

instance HasType CoreIR UserEffectOp where
  getTypeE = \case
    Handle hndName [] body -> do
      hndName' <- substM hndName
      r <- getTypeE body
      instantiateHandlerType hndName' r []
    Handle _ _ _  -> error "not implemented"
    Perform eff i -> do
      Eff (OneEffect (UserEffect effName)) <- return eff
      EffectDef _ ops <- substM effName >>= lookupEffectDef
      let (_, EffectOpType _pol lamTy) = ops !! i
      return lamTy
    Resume retTy _ -> substM retTy

instance IRRep r => HasType r (ComposeE PrimOp (Atom r)) where
  getTypeE (ComposeE primOp) = case primOp of
    BinOp op x _ -> do
      xTy <- getTypeBaseType x
      return $ TC $ BaseType $ typeBinOp op xTy
    UnOp op x -> TC . BaseType . typeUnOp op <$> getTypeBaseType x
    MemOp op -> case op of
      IOAlloc t _ -> return $ PtrTy (CPU, t)
      IOFree _ -> return UnitTy
      PtrOffset arr _ -> getTypeE arr
      PtrLoad ptr -> do
        PtrTy (_, t) <- getTypeE ptr
        return $ BaseTy t
      PtrStore _ _ -> return UnitTy
    MiscOp op -> case op of
      Select _ x _ -> getTypeE x
      ThrowError ty -> substM ty
      ThrowException ty -> substM ty
      CastOp t _ -> substM t
      BitcastOp t _ -> substM t
      UnsafeCoerce t _ -> substM t
      GarbageVal t -> substM t
      SumTag _ -> return TagRepTy
      ToEnum t _ -> substM t
      OutputStream ->
        return $ BaseTy $ hostPtrTy $ Scalar Word8Type
        where hostPtrTy ty = PtrType (CPU, ty)
      ShowAny _ -> rawStrType -- TODO: constrain `ShowAny` to have `HasCore r`
      ShowScalar _ -> PairTy IdxRepTy <$> rawFinTabType (IdxRepVal showStringBufferSize) CharRepTy
    VectorOp op -> case op of
      VectorBroadcast _ vty -> substM vty
      VectorIota vty -> substM vty
      VectorSubref ref _ vty -> getTypeE ref >>= \case
        TC (RefType h _) -> TC . RefType h <$> substM vty
        ty -> error $ "Not a reference type: " ++ pprint ty

instance HasType CoreIR (ComposeE RecordOp CAtom) where
  getTypeE (ComposeE recordOp) = case recordOp of
    RecordCons l r -> do
      lty <- getTypeE l
      rty <- getTypeE r
      case (lty, rty) of
        (RecordTyWithElems lelems, RecordTyWithElems relems) ->
          return $ RecordTyWithElems $ lelems ++ relems
        _ -> throw TypeErr $ "Can't concatenate " <> pprint lty <> " and " <> pprint rty <> " as records"
    RecordConsDynamic lab val record -> do
      lab' <- substM lab
      vty <- getTypeE val
      rty <- getTypeE record
      case rty of
        RecordTy rest -> case lab' of
          NewtypeTyCon (LabelCon l) -> return $ RecordTy $ prependFieldRowElem
                                (StaticFields (labeledSingleton l vty)) rest
          Var labVar       -> return $ RecordTy $ prependFieldRowElem
                                (DynField labVar vty) rest
          _ -> error "Unexpected label atom"
        _ -> throw TypeErr
              $ "Can't add a dynamic field to a non-record value of type " <> pprint rty
    RecordSplitDynamic lab record -> do
      lab' <- cheapNormalize =<< substM lab
      rty <- getTypeE record
      case (lab', rty) of
        (NewtypeTyCon (LabelCon l), RecordTyWithElems (StaticFields items:rest)) -> do
          let (h, items') = splitLabeledItems (labeledSingleton l ()) items
          return $ PairTy (head $ toList h) $ RecordTyWithElems (StaticFields items':rest)
        (Var labVar', RecordTyWithElems (DynField labVar'' ty:rest)) | labVar' == labVar'' ->
          return $ PairTy ty $ RecordTyWithElems rest
        -- There are more cases we could implement, but do we need to?
        _ -> throw TypeErr $ "Can't split a label "
              <> pprint lab' <> " from atom of type " <> pprint rty
    RecordSplit fields record -> do
      fields' <- cheapNormalize =<< substM fields
      fullty  <- cheapNormalize =<< getTypeE record
      let splitFailed =
            throw TypeErr $ "Invalid record split: "
              <> pprint fields' <> " from " <> pprint fullty
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
                NoExt rest <- labeledRowDifference' (NoExt yf) (NoExt xf)
                return $ Just $ StaticFields rest : ys
              _ -> return Nothing
          _ -> return Nothing

instantiateHandlerType :: EnvReader m => HandlerName n -> CAtom n -> [CAtom n] -> m n (CType n)
instantiateHandlerType hndName r args = do
  HandlerDef _ rb bs _effs retTy _ _ <- lookupHandlerDef hndName
  applySubst (rb @> (SubstVal r) <.> bs @@> (map SubstVal args)) retTy

getSuperclassDicts :: ClassDef n -> CAtom n -> [CAtom n]
getSuperclassDicts (ClassDef _ _ _ _ classBs _) dict =
  for [0 .. nestLength classBs - 1] \i -> DictCon $ SuperclassProj dict i

getTypeBaseType :: (IRRep r, HasType r e) => e i -> TypeQueryM i o BaseType
getTypeBaseType e =
  getTypeE e >>= \case
    TC (BaseType b) -> return b
    ty -> throw TypeErr $ "Expected a base type. Got: " ++ pprint ty

labeledRowDifference'
  :: IRRep r
  => ExtLabeledItems (Type r o) (AtomName r o)
  -> ExtLabeledItems (Type r o) (AtomName r o)
  -> TypeQueryM i o (ExtLabeledItems (Type r o) (AtomName r o))
labeledRowDifference' (Ext (LabeledItems items) rest)
                      (Ext (LabeledItems subitems) subrest) = do
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

getTypeTopFun :: EnvReader m => TopFunName n -> m n (PiType SimpIR n)
getTypeTopFun f = lookupTopFun f >>= \case
  DexTopFun _ piTy _ _ -> return piTy
  FFITopFun _ iTy -> liftIFunType iTy

liftIFunType :: (IRRep r, EnvReader m) => IFunType -> m n (PiType r n)
liftIFunType (IFunType _ argTys resultTys) = liftEnvReaderM $ go argTys where
  go :: IRRep r => [BaseType] -> EnvReaderM n (PiType r n)
  go = \case
    [] -> return $ PiType Empty (OneEffect IOEffect) resultTy
      where resultTy = case resultTys of
              [] -> UnitTy
              [t] -> BaseTy t
              [t1, t2] -> PairTy (BaseTy t1) (BaseTy t2)
              _ -> error $ "Not a valid FFI return type: " ++ pprint resultTys
    t:ts -> withFreshBinder noHint (BaseTy t) \b -> do
      PiType bs effs resultTy <- go ts
      return $ PiType (Nest b bs) effs resultTy

getTypeHof :: IRRep r => Hof r i -> TypeQueryM i o (Type r o)
getTypeHof hof = addContext ("Checking HOF:\n" ++ pprint hof) case hof of
  For _ dict f -> do
    PiType (UnaryNest (b:>_)) _ eltTy <- getLamExprTypeE f
    ixTy <- ixTyFromDict =<< substM dict
    return $ TabTy (b:>ixTy) eltTy
  While _ -> return UnitTy
  Linearize f _ -> do
    PiType (UnaryNest (binder:>a)) Pure b <- getLamExprTypeE f
    let b' = ignoreHoistFailure $ hoist binder b
    fLinTy <- Pi <$> nonDepPiType [a] Pure b'
    return $ PairTy b' fLinTy
  Transpose f _ -> do
    PiType (UnaryNest (_:>a)) _ _ <- getLamExprTypeE f
    return a
  RunReader _ f -> do
    (resultTy, _) <- getTypeRWSAction f
    return resultTy
  RunWriter _ _ f -> do
    uncurry PairTy <$> getTypeRWSAction f
  RunState _ _ f -> do
    (resultTy, stateTy) <- getTypeRWSAction f
    return $ PairTy resultTy stateTy
  RunIO f -> getTypeE f
  RunInit f -> getTypeE f
  CatchException f -> getTypeE f >>= makePreludeMaybeTy

getLamExprTypeE :: IRRep r => LamExpr r i -> TypeQueryM i o (PiType r o)
getLamExprTypeE (LamExpr bs body) =
  substBinders bs \bs' -> do
    effs <- substM $ blockEffects body
    resultTy <- getTypeE body
    return $ PiType bs' effs resultTy

getDestLamExprType :: IRRep r => DestLamExpr r i -> TypeQueryM i o (PiType r o)
getDestLamExprType (DestLamExpr bs body) =
  substBinders bs \bs' -> do
    resultTy <- getDestBlockType =<< substM body
    effs <- substM $ destBlockEffects body
    return $ PiType bs' effs resultTy

getTypeRWSAction :: IRRep r => LamExpr r i -> TypeQueryM i o (Type r o, Type r o)
getTypeRWSAction f = do
  PiType (BinaryNest regionBinder refBinder) _ resultTy <- getLamExprTypeE f
  RefTy _ referentTy <- return $ binderType refBinder
  let referentTy' = ignoreHoistFailure $ hoist regionBinder referentTy
  let resultTy' = ignoreHoistFailure $ hoist (PairB regionBinder refBinder) resultTy
  return (resultTy', referentTy')

instance IRRep r => HasType r (Block r) where
  getTypeE (Block NoBlockAnn Empty result) = getTypeE result
  getTypeE (Block (BlockAnn ty _) _ _) = substM ty
  getTypeE _ = error "impossible"

ixTyFromDict :: IRRep r => EnvReader m => IxDict r n -> m n (IxType r n)
ixTyFromDict ixDict = flip IxType ixDict <$> case ixDict of
  IxDictAtom dict -> getType dict >>= \case
    DictTy (DictType "Ix" _ [iTy]) -> return iTy
    _ -> error $ "Not an Ix dict: " ++ pprint dict
  IxDictRawFin _ -> return IdxRepTy
  IxDictSpecialized n _ _ -> return n

rawStrType :: IRRep r => EnvReader m => m n (Type r n)
rawStrType = liftEnvReaderM do
  withFreshBinder "n" IdxRepTy \b -> do
    tabTy <- rawFinTabType (Var $ binderName b) CharRepTy
    return $ DepPairTy $ DepPairType b tabTy

-- `n` argument is IdxRepVal, not Nat
rawFinTabType :: IRRep r => EnvReader m => Atom r n -> Atom r n -> m n (Type r n)
rawFinTabType n eltTy = IxType IdxRepTy (IxDictRawFin n) ==> eltTy

-- === querying effects implementation ===

class HasEffectsE (e::E) (r::IR) | e -> r where
  getEffectsImpl :: e i -> TypeQueryM i o (EffectRow r o)

instance IRRep r => HasEffectsE (Expr r) r where
  getEffectsImpl = exprEffects
  {-# INLINE getEffectsImpl #-}

instance IRRep r => HasEffectsE (DeclBinding r) r where
  getEffectsImpl (DeclBinding _ _ expr) = getEffectsImpl expr
  {-# INLINE getEffectsImpl #-}

exprEffects :: IRRep r => Expr r i -> TypeQueryM i o (EffectRow r o)
exprEffects expr = case expr of
  Atom _  -> return Pure
  App f xs -> do
    fTy <- getTypeSubst f
    appEffects fTy xs
  TopApp f xs -> do
    PiType bs effs _ <- getTypeTopFun =<< substM f
    xs' <- mapM substM xs
    applySubst (bs @@> fmap SubstVal xs') effs
  TabApp _ _ -> return Pure
  RefOp ref m -> do
    TC (RefType h _) <- getTypeSubst ref
    return case m of
      MGet      -> OneEffect (RWSEffect State  h)
      MPut    _ -> OneEffect (RWSEffect State  h)
      MAsk      -> OneEffect (RWSEffect Reader h)
      -- XXX: We don't verify the base monoid. See note about RunWriter.
      MExtend _ _ -> OneEffect (RWSEffect Writer h)
      IndexRef _ -> Pure
      ProjRef _  -> Pure
  UserEffectOp op -> case op of
    Handle v _ body -> do
      HandlerDef eff _ _ _ _ _ _ <- substM v >>= lookupHandlerDef
      deleteEff (UserEffect eff) <$> getEffectsImpl body
    Resume _ _  -> return Pure
    Perform effVal _ -> do
      Eff eff <- return effVal
      substM eff
  PrimOp primOp -> case primOp of
    UnOp  _ _   -> return Pure
    BinOp _ _ _ -> return Pure
    VectorOp _  -> return Pure
    MemOp op -> case op of
      IOAlloc  _ _  -> return $ OneEffect IOEffect
      IOFree   _    -> return $ OneEffect IOEffect
      PtrLoad  _    -> return $ OneEffect IOEffect
      PtrStore _ _  -> return $ OneEffect IOEffect
      PtrOffset _ _ -> return Pure
    MiscOp op -> case op of
      ThrowException _ -> return $ OneEffect ExceptionEffect
      Select _ _ _     -> return Pure
      ThrowError _     -> return Pure
      CastOp _ _       -> return Pure
      UnsafeCoerce _ _ -> return Pure
      GarbageVal _     -> return Pure
      BitcastOp _ _    -> return Pure
      SumTag _         -> return Pure
      ToEnum _ _       -> return Pure
      OutputStream     -> return Pure
      ShowAny _        -> return Pure
      ShowScalar _     -> return Pure
  DAMOp op -> case op of
    Place    _ _  -> return $ OneEffect InitEffect
    Seq _ _ _ f      -> functionEffs f
    RememberDest _ f -> functionEffs f
    AllocDest _ -> return Pure -- is this correct?
    Freeze _    -> return Pure -- is this correct?
  Hof hof -> case hof of
    For _ _ f     -> functionEffs f
    While body    -> getEffectsImpl body
    Linearize _ _ -> return Pure  -- Body has to be a pure function
    Transpose _ _ -> return Pure  -- Body has to be a pure function
    RunReader _ f -> rwsFunEffects Reader f
    RunWriter d _ f -> rwsFunEffects Writer f <&> maybeInit d
    RunState  d _ f -> rwsFunEffects State  f <&> maybeInit d
    RunIO          f -> deleteEff IOEffect        <$> getEffectsImpl f
    RunInit        f -> deleteEff InitEffect      <$> getEffectsImpl f
    CatchException f -> deleteEff ExceptionEffect <$> getEffectsImpl f
    where maybeInit :: IRRep r => Maybe (Atom r i) -> (EffectRow r o -> EffectRow r o)
          maybeInit d = case d of Just _ -> (<>OneEffect InitEffect); Nothing -> id
  Case _ _ _ effs -> substM effs
  TabCon _ _ _      -> return Pure
  ApplyMethod dict i args -> do
    dict' <- substM dict
    methodTy <- getMethodType dict' i
    appEffects (Pi methodTy) args
  RecordOp _        -> return Pure

instance IRRep r => HasEffectsE (Block r) r where
  getEffectsImpl (Block (BlockAnn _ effs) _ _) = substM effs
  getEffectsImpl (Block NoBlockAnn _ _) = return Pure
  {-# INLINE getEffectsImpl #-}

instance IRRep r => HasEffectsE (DestBlock r) r where
  getEffectsImpl (DestBlock b (Block ann _ _)) = case ann of
    BlockAnn _ effs -> substM $ ignoreHoistFailure $ hoist b effs
    NoBlockAnn -> return Pure
  {-# INLINE getEffectsImpl #-}

instance IRRep r => HasEffectsE (Alt r) r where
  getEffectsImpl (Abs bs body) =
    substBinders bs \bs' ->
      ignoreHoistFailure . hoist bs' <$> getEffectsImpl body
  {-# INLINE getEffectsImpl #-}

-- wrapper to allow checking the effects of an applied nullary lambda
data NullaryLamApp r n = NullaryLamApp (LamExpr r n)
-- XXX: this should only be used for nullary lambdas
instance IRRep r => HasEffectsE (NullaryLamApp r) r where
  getEffectsImpl (NullaryLamApp (NullaryLamExpr block)) = getEffectsImpl block
  getEffectsImpl _ = error "not a nullary lambda"
  {-# INLINE getEffectsImpl #-}

-- wrapper to allow checking the effects of an applied nullary dest lambda
data NullaryDestLamApp r n = NullaryDestLamApp (DestLamExpr r n)
-- XXX: this should only be used for nullary lambdas
instance IRRep r => HasEffectsE (NullaryDestLamApp r) r where
  getEffectsImpl (NullaryDestLamApp (NullaryDestLamExpr block)) = getEffectsImpl block
  getEffectsImpl _ = error "not a nullary lambda"
  {-# INLINE getEffectsImpl #-}

functionEffs :: IRRep r => LamExpr r i -> TypeQueryM i o (EffectRow r o)
functionEffs f = getLamExprTypeE f >>= \case
  PiType b effs _ -> return $ ignoreHoistFailure $ hoist b effs

rwsFunEffects :: IRRep r => RWS -> LamExpr r i -> TypeQueryM i o (EffectRow r o)
rwsFunEffects rws f = getLamExprTypeE f >>= \case
   PiType (BinaryNest h ref) effs _ -> do
     let effs' = ignoreHoistFailure $ hoist ref effs
     let effs'' = deleteEff (RWSEffect rws (Var $ binderName h)) effs'
     return $ ignoreHoistFailure $ hoist h effs''
   _ -> error "Expected a binary function type"

deleteEff :: IRRep r => Effect r n -> EffectRow r n -> EffectRow r n
deleteEff eff (EffectRow effs t) = EffectRow (effs `eSetDifference` eSetSingleton eff) t
