-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module QueryType (
  getType, getTypeSubst, HasType,
  getEffects, getEffectsSubst, isPure,
  computeAbsEffects, declNestEffects,
  caseAltsBinderTys, depPairLeftTy, extendEffect,
  getAppType, getTabAppType, getBaseMonoidType, getReferentTy,
  getMethodIndex,
  instantiateDataDef, applyDataConAbs, dataDefRep,
  instantiateNaryPi, instantiateDepPairTy, instantiatePi, instantiateTabPi,
  litType,
  numNaryPiArgs,
  sourceNameType, typeBinOp, typeUnOp,
  ixDictType, dataDictType, getSuperclassDicts,
  ixTyFromDict, instantiateHandlerType, getDestBlockType, getNaryDestLamExprType,
  getNaryLamExprType, unwrapNewtypeType, unwrapLeadingNewtypesType, wrapNewtypesData,
  rawStrType, rawFinTabType, getReferentTypeRWSAction, liftIFunType, getTypeTopFun,
  HasEffectsE (..), NullaryLamApp (..), NullaryDestLamApp (..),
  makePreludeMaybeTy
  ) where

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

getNaryLamExprType :: (IRRep r, EnvReader m) => LamExpr r n -> m n (NaryPiType r n)
getNaryLamExprType lam = liftTypeQueryM idSubst $ getLamExprType lam
{-# INLINE getNaryLamExprType #-}

-- TODO: Fold this into a real HasType instance
getDestBlockType :: (IRRep r, EnvReader m) => DestBlock r n -> m n (Type r n)
getDestBlockType (DestBlock (_:>RawRefTy ansTy) _) = return ansTy
getDestBlockType _ = error "Expected a reference type for body destination"
{-# INLINE getDestBlockType #-}

getNaryDestLamExprType :: (IRRep r, EnvReader m) => DestLamExpr r n -> m n (NaryPiType r n)
getNaryDestLamExprType lam = liftTypeQueryM idSubst $ getDestLamExprType lam
{-# INLINE getNaryDestLamExprType #-}

getReferentTypeRWSAction :: (EnvReader m, IRRep r) => LamExpr r o -> m o (Type r o)
getReferentTypeRWSAction f = liftTypeQueryM idSubst $ liftM snd $ getTypeRWSAction f

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
      def <- lookupDataDef defName
      cons <- instantiateDataDef def params
      return [repTy | DataConDef _ _ repTy _ <- cons]
    _ -> fail msg
  _ -> fail msg
  where msg = "Case analysis only supported on ADTs, not on " ++ pprint ty

extendEffect :: IRRep r => Effect r n -> EffectRow r n -> EffectRow r n
extendEffect eff (EffectRow effs t) = EffectRow (effs <> eSetSingleton eff) t

getAppType :: (IRRep r, EnvReader m) => Type r n -> [Atom r n] -> m n (Type r n)
getAppType f xs = liftTypeQueryM idSubst $ typeApp f xs
{-# INLINE getAppType #-}

getTabAppType :: (IRRep r, EnvReader m) => Type r n -> [Atom r n] -> m n (Type r n)
getTabAppType f xs = case NE.nonEmpty xs of
  Nothing -> getType f
  Just xs' -> liftTypeQueryM idSubst $ typeTabApp f xs'
{-# INLINE getTabAppType #-}

getBaseMonoidType :: (IRRep r, Fallible1 m) => ScopeReader m => Type r n -> m n (Type r n)
getBaseMonoidType ty = case ty of
  Pi (PiType b _ _ resultTy) -> liftHoistExcept $ hoist b resultTy
  _     -> return ty
{-# INLINE getBaseMonoidType #-}

getReferentTy :: (IRRep r, MonadFail m) => EmptyAbs (PairB (Binder r) (Binder r)) n -> m (Type r n)
getReferentTy (Abs (PairB hB refB) UnitE) = do
  RefTy _ ty <- return $ binderType refB
  HoistSuccess ty' <- return $ hoist hB ty
  return ty'
{-# INLINE getReferentTy #-}

getMethodIndex :: EnvReader m => ClassName n -> SourceName -> m n Int
getMethodIndex className methodSourceName = do
  ClassDef _ methodNames _ _ _ <- lookupClassDef className
  case elemIndex methodSourceName methodNames of
    Nothing -> error $ methodSourceName ++ " is not a method of " ++ pprint className
    Just i -> return i
{-# INLINE getMethodIndex #-}

instantiateNaryPi :: (IRRep r, EnvReader m) => NaryPiType r n  -> [Atom r n] -> m n (NaryPiType r n)
instantiateNaryPi (NaryPiType bs eff resultTy) args = do
  PairB bs1 bs2 <- return $ splitNestAt (length args) bs
  applySubst (bs1 @@> map SubstVal args) (NaryPiType bs2 eff resultTy)
{-# INLINE instantiateNaryPi #-}

instantiatePi :: EnvReader m => PiType n -> CAtom n -> m n (EffectRow CoreIR n, CType n)
instantiatePi (PiType b _ eff body) x = do
  PairE eff' body' <- applyAbs (Abs b (PairE eff body)) (SubstVal x)
  return (eff', body')
{-# INLINE instantiatePi #-}

instantiateTabPi :: (IRRep r, EnvReader m) => TabPiType r n -> Atom r n -> m n (Type r n)
instantiateTabPi (TabPiType b body) x = applyAbs (Abs b body) (SubstVal x)
{-# INLINE instantiateTabPi #-}

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

numNaryPiArgs :: NaryPiType r n -> Int
numNaryPiArgs (NaryPiType bs _ _) = nestLength bs

userEffect :: EffectName n -> CAtom n
userEffect v = Eff (OneEffect (UserEffect v))

sourceNameType :: (EnvReader m, Fallible1 m) => SourceName -> m n (Type CoreIR n)
sourceNameType v = do
  lookupSourceMap v >>= \case
    Nothing -> throw UnboundVarErr $ pprint v
    Just uvar -> case uvar of
      UAtomVar    v' -> getType $ Var v'
      UTyConVar   v' -> lookupEnv v' >>= \case TyConBinding _     e -> getType e
      UDataConVar v' -> lookupEnv v' >>= \case DataConBinding _ _ e -> getType e
      UClassVar   v' -> lookupEnv v' >>= \case ClassBinding  def    -> return $ getClassTy def
      UMethodVar  v' -> lookupEnv v' >>= \case MethodBinding _ _ e  -> getType e
      UEffectVar  v' -> getType $ userEffect v'
      UEffectOpVar _ -> error "not implemented: sourceNameType::UEffectOpVar"  -- TODO(alex): implement
      UHandlerVar  _ -> error "not implemented: sourceNameType::UHandlerVar"   -- TODO(alex): implement

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
    Lam (UnaryLamExpr (b:>ty) body) arr (Abs (bEff:>_) effs) -> do
      ty' <- substM ty
      withFreshBinder (getNameHint b) ty' \b' -> do
        effs' <- extendRenamer (bEff@>binderName b') $ substM effs
        extendRenamer (b@>binderName b') do
          bodyTy <- getTypeE body
          return $ Pi $ PiType b' arr effs' bodyTy
    Lam _ _ _ -> error "expected a unary lambda expression"
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
    DictHole _ ty -> substM ty

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
    (DataDef sn _ _) <- lookupDataDef d'
    return $ NewtypeTyCon $ UserADTType sn d' params'

getTypePrimCon :: IRRep r => PrimCon r (Atom r i) -> TypeQueryM i o (Type r o)
getTypePrimCon con = case con of
  Lit l -> return $ BaseTy $ litType l
  ProdCon xs -> ProdTy <$> mapM getTypeE xs
  SumCon tys _ _ -> SumTy <$> traverse substM tys
  HeapVal       -> return $ TC HeapType

dictExprType :: DictExpr i -> TypeQueryM i o (CType o)
dictExprType e = case e of
  InstanceDict instanceName args -> do
    instanceName' <- substM instanceName
    InstanceDef className bs params _ <- lookupInstanceDef instanceName'
    ClassDef sourceName _ _ _ _ <- lookupClassDef className
    args' <- mapM substM args
    let bs' = fmapNest (\(RolePiBinder b _ _ _) -> b) bs
    ListE params' <- applySubst (bs' @@> map SubstVal args') $ ListE params
    return $ DictTy $ DictType sourceName className params'
  InstantiatedGiven given args -> do
    givenTy <- getTypeE given
    typeApp givenTy (toList args)
  SuperclassProj d i -> do
    DictTy (DictType _ className params) <- getTypeE d
    ClassDef _ _ bs superclasses _ <- lookupClassDef className
    applySubst (bs @@> map SubstVal params) $
      superclassTypes superclasses !! i
  IxFin n -> do
    n' <- substM n
    liftM DictTy $ ixDictType $ NewtypeTyCon $ Fin n'
  DataData ty -> DictTy <$> (dataDictType =<< substM ty)

getIxClassName :: (Fallible1 m, EnvReader m) => m n (ClassName n)
getIxClassName = lookupSourceMap "Ix" >>= \case
  Nothing -> throw CompilerErr $ "Ix interface needed but not defined!"
  Just (UClassVar v) -> return v
  Just _ -> error "not a class var"

ixDictType :: (Fallible1 m, EnvReader m) => CType n -> m n (DictType n)
ixDictType ty = do
  ixClassName <- getIxClassName
  return $ DictType "Ix" ixClassName [ty]

getDataClassName :: (Fallible1 m, EnvReader m) => m n (ClassName n)
getDataClassName = lookupSourceMap "Data" >>= \case
  Nothing -> throw CompilerErr $ "Data interface needed but not defined!"
  Just (UClassVar v) -> return v
  Just _ -> error "not a class var"

dataDictType :: (Fallible1 m, EnvReader m) => CType n -> m n (DictType n)
dataDictType ty = do
  dataClassName <- getDataClassName
  return $ DictType "Data" dataClassName [ty]

makePreludeMaybeTy :: EnvReader m => CType n -> m n (CType n)
makePreludeMaybeTy ty = do
  ~(Just (UTyConVar tyConName)) <- lookupSourceMap "Maybe"
  ~(TyConBinding dataDefName _) <- lookupEnv tyConName
  return $ TypeCon "Maybe" dataDefName $ DataDefParams [(PlainArrow, ty)]

typeApp  :: IRRep r => Type r o -> [Atom r i] -> TypeQueryM i o (Type r o)
typeApp fTy [] = return fTy
typeApp fTy xs = case fromNaryPiType (length xs) fTy of
  Just (NaryPiType bs _ resultTy) -> do
    xs' <- mapM substM xs
    let subst = bs @@> fmap SubstVal xs'
    applySubst subst resultTy
  Nothing -> throw TypeErr $
    "Not a " ++ show (length xs) ++ "-argument pi type: " ++ pprint fTy
      ++ " (tried to apply it to: " ++ pprint xs ++ ")"

typeTabApp :: IRRep r => Type r o -> NE.NonEmpty (Atom r i) -> TypeQueryM i o (Type r o)
typeTabApp tabTy xs = go tabTy $ toList xs
  where
    go :: IRRep r => Type r o -> [Atom r i] -> TypeQueryM i o (Type r o)
    go ty [] = return ty
    go ty (i:rest) = do
      TabTy (b:>_) resultTy <- return ty
      i' <- substM i
      resultTy' <- applySubst (b@>SubstVal i') resultTy
      go resultTy' rest

instance HasType CoreIR DictExpr where
  getTypeE e = dictExprType e

instance IRRep r => HasType r (Expr r) where
  getTypeE expr = case expr of
    App f xs -> do
      fTy <- getTypeE f
      typeApp fTy $ toList xs
    TopApp f xs -> do
      NaryPiType bs _ resultTy <- getTypeTopFun =<< substM f
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
    ProjMethod dict i -> do
      DictTy (DictType _ className params) <- getTypeE dict
      def@(ClassDef _ _ paramBs classBs methodTys) <- lookupClassDef className
      let MethodType _ methodTy = methodTys !! i
      superclassDicts <- getSuperclassDicts def <$> substM dict
      let subst = (    paramBs @@> map SubstVal params
                   <.> classBs @@> map SubstVal superclassDicts)
      applySubst subst methodTy
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
getSuperclassDicts (ClassDef _ _ _ (SuperclassBinders classBs _) _) dict =
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

getTypeTopFun :: EnvReader m => TopFunName n -> m n (NaryPiType SimpIR n)
getTypeTopFun f = lookupTopFun f >>= \case
  DexTopFun _ piTy _ _ -> return piTy
  FFITopFun _ iTy -> liftIFunType iTy

liftIFunType :: (IRRep r, EnvReader m) => IFunType -> m n (NaryPiType r n)
liftIFunType (IFunType _ argTys resultTys) = liftEnvReaderM $ go argTys where
  go :: IRRep r => [BaseType] -> EnvReaderM n (NaryPiType r n)
  go = \case
    [] -> return $ NaryPiType Empty (OneEffect IOEffect) resultTy
      where resultTy = case resultTys of
              [] -> UnitTy
              [t] -> BaseTy t
              [t1, t2] -> PairTy (BaseTy t1) (BaseTy t2)
              _ -> error $ "Not a valid FFI return type: " ++ pprint resultTys
    t:ts -> withFreshBinder noHint (BaseTy t) \b -> do
      NaryPiType bs effs resultTy <- go ts
      return $ NaryPiType (Nest b bs) effs resultTy

getTypeHof :: IRRep r => Hof r i -> TypeQueryM i o (Type r o)
getTypeHof hof = addContext ("Checking HOF:\n" ++ pprint hof) case hof of
  For _ dict f -> do
    NaryPiType (UnaryNest (b:>_)) _ eltTy <- getLamExprType f
    ixTy <- ixTyFromDict =<< substM dict
    return $ TabTy (b:>ixTy) eltTy
  While _ -> return UnitTy
  Linearize f _ -> do
    NaryPiType (UnaryNest (binder:>a)) Pure b <- getLamExprType f
    let b' = ignoreHoistFailure $ hoist binder b
    fLinTy <- a --@ b'
    return $ PairTy b' fLinTy
  Transpose f _ -> do
    NaryPiType (UnaryNest (_:>a)) _ _ <- getLamExprType f
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

getLamExprType :: IRRep r => LamExpr r i -> TypeQueryM i o (NaryPiType r o)
getLamExprType (LamExpr bs body) =
  substBinders bs \bs' -> do
    effs <- substM $ blockEffects body
    resultTy <- getTypeE body
    return $ NaryPiType bs' effs resultTy

getDestLamExprType :: IRRep r => DestLamExpr r i -> TypeQueryM i o (NaryPiType r o)
getDestLamExprType (DestLamExpr bs body) =
  substBinders bs \bs' -> do
    resultTy <- getDestBlockType =<< substM body
    effs <- substM $ destBlockEffects body
    return $ NaryPiType bs' effs resultTy

getTypeRWSAction :: IRRep r => LamExpr r i -> TypeQueryM i o (Type r o, Type r o)
getTypeRWSAction f = do
  NaryPiType (BinaryNest regionBinder refBinder) _ resultTy <- getLamExprType f
  RefTy _ referentTy <- return $ binderType refBinder
  let referentTy' = ignoreHoistFailure $ hoist regionBinder referentTy
  let resultTy' = ignoreHoistFailure $ hoist (PairB regionBinder refBinder) resultTy
  return (resultTy', referentTy')

instance IRRep r => HasType r (Block r) where
  getTypeE (Block NoBlockAnn Empty result) = getTypeE result
  getTypeE (Block (BlockAnn ty _) _ _) = substM ty
  getTypeE _ = error "impossible"

getClassTy :: ClassDef n -> Type CoreIR n
getClassTy (ClassDef _ _ bs _ _) = go bs
  where
    go :: Nest RolePiBinder n l -> CType n
    go Empty = TyKind
    go (Nest (RolePiBinder b ty arr _) rest) = Pi $ PiType (b:>ty) arr Pure $ go rest

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
    case fromNaryPiType (length xs) fTy of
      Just (NaryPiType bs effs _) -> do
        xs' <- mapM substM xs
        let subst = bs @@> fmap SubstVal xs'
        applySubst subst effs
      Nothing -> error $
        "Not a " ++ show (length xs + 1) ++ "-argument pi type: " ++ pprint expr
  TopApp f xs -> do
    NaryPiType bs effs _ <- getTypeTopFun =<< substM f
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
  ProjMethod _ _    -> return Pure
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
functionEffs f = getLamExprType f >>= \case
  NaryPiType b effs _ -> return $ ignoreHoistFailure $ hoist b effs

rwsFunEffects :: IRRep r => RWS -> LamExpr r i -> TypeQueryM i o (EffectRow r o)
rwsFunEffects rws f = getLamExprType f >>= \case
   NaryPiType (BinaryNest h ref) effs _ -> do
     let effs' = ignoreHoistFailure $ hoist ref effs
     let effs'' = deleteEff (RWSEffect rws (Var $ binderName h)) effs'
     return $ ignoreHoistFailure $ hoist h effs''
   _ -> error "Expected a binary function type"

deleteEff :: IRRep r => Effect r n -> EffectRow r n -> EffectRow r n
deleteEff eff (EffectRow effs t) = EffectRow (effs `eSetDifference` eSetSingleton eff) t
