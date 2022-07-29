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
  instantiateDataDef, instantiateNaryPi, instantiateDepPairTy, instantiatePi, instantiateTabPi,
  litType, lamExprTy,
  numNaryPiArgs, naryLamExprType, specializedFunType,
  oneEffect, projectLength, sourceNameType, typeAsBinderNest, typeBinOp, typeUnOp,
  isSingletonType, singletonTypeVal, ixDictType, getSuperclassDicts, ixTyFromDict
  ) where

import Control.Category ((>>>))
import Control.Monad
import Data.Foldable (toList)
import Data.Functor ((<&>))
import Data.List (elemIndex)
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import Data.Maybe (isJust, fromJust)
import qualified Data.Set        as S

import Types.Primitives
import Types.Core
import Types.Source
import Core
import CheapReduction (cheapNormalize)
import Err
import LabeledItems
import Name
import Util
import PPrint ()

-- === Main API for querying types ===

getTypeSubst :: (SubstReader AtomSubstVal m
                , EnvReader2 m, HasType e)
             => e i -> m i o (Type o)
getTypeSubst e = do
  subst <- getSubst
  liftTypeQueryM subst $ getTypeE e
{-# INLINE getTypeSubst #-}

getType :: (EnvReader m, HasType e) => e n -> m n (Type n)
getType e = liftTypeQueryM idSubst $ getTypeE e
{-# INLINE getType #-}

-- === Querying effects ===

isPure :: (EnvReader m, HasEffectsE e) => e n -> m n Bool
isPure e = getEffects e <&> \case
  Pure -> True
  _    -> False

getEffects :: (EnvReader m, HasEffectsE e) => e n -> m n (EffectRow n)
getEffects e = liftTypeQueryM idSubst $ getEffectsImpl e
{-# INLINE getEffects #-}

getEffectsSubst :: (EnvReader2 m, SubstReader AtomSubstVal m, HasEffectsE e)
              => e i -> m i o (EffectRow o)
getEffectsSubst e = do
  subst <- getSubst
  liftTypeQueryM subst $ getEffectsImpl e
{-# INLINE getEffectsSubst #-}

-- === Exposed helpers for querying types and effects ===

caseAltsBinderTys :: (Fallible1 m, EnvReader m)
                  => Type n -> m n [EmptyAbs (Nest Binder) n]
caseAltsBinderTys ty = case ty of
  TypeCon _ defName params -> do
    def <- lookupDataDef defName
    cons <- instantiateDataDef def params
    return [bs | DataConDef _ bs <- cons]
  VariantTy (NoExt types) -> do
    mapM typeAsBinderNest $ toList types
  VariantTy _ -> fail "Can't pattern-match partially-known variants"
  SumTy cases -> mapM typeAsBinderNest cases
  _ -> fail $ "Case analysis only supported on ADTs and variants, not on " ++ pprint ty

depPairLeftTy :: DepPairType n -> Type n
depPairLeftTy (DepPairType (_:>ty) _) = ty
{-# INLINE depPairLeftTy #-}

extendEffect :: Effect n -> EffectRow n -> EffectRow n
extendEffect eff (EffectRow effs t) = EffectRow (S.insert eff effs) t

getAppType :: EnvReader m => Type n -> [Atom n] -> m n (Type n)
getAppType f xs = liftTypeQueryM idSubst $ typeApp f xs
{-# INLINE getAppType #-}

getTabAppType :: EnvReader m => Type n -> [Atom n] -> m n (Type n)
getTabAppType f xs = case NE.nonEmpty xs of
  Nothing -> getType f
  Just xs' -> liftTypeQueryM idSubst $ typeTabApp f xs'
{-# INLINE getTabAppType #-}

getBaseMonoidType :: Fallible1 m => ScopeReader m => Type n -> m n (Type n)
getBaseMonoidType ty = case ty of
  Pi (PiType b _ resultTy) -> liftHoistExcept $ hoist b resultTy
  _     -> return ty
{-# INLINE getBaseMonoidType #-}

getReferentTy :: MonadFail m => EmptyAbs (PairB LamBinder LamBinder) n -> m (Type n)
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

instantiateDataDef :: ScopeReader m => DataDef n -> DataDefParams n -> m n [DataConDef n]
instantiateDataDef (DataDef _ (DataDefBinders bs1 bs2) cons) (DataDefParams xs1 xs2) = do
  fromListE <$> applyNaryAbs (Abs (bs1 >>> bs2) (ListE cons)) (map SubstVal $ xs1 <> xs2)
{-# INLINE instantiateDataDef #-}

instantiateNaryPi :: EnvReader m => NaryPiType n -> [Atom n] -> m n (NaryPiType n)
instantiateNaryPi (NaryPiType bs eff resultTy) args = do
  PairB bs1 bs2 <- return $ splitNestAt (length args) $ nonEmptyToNest bs
  let bs2' = case bs2 of
               Empty -> error "expected a nonempty list of runtime args"
               Nest x y -> NonEmptyNest x y
  applySubst (bs1 @@> map SubstVal args) (NaryPiType bs2' eff resultTy)
{-# INLINE instantiateNaryPi #-}

instantiateDepPairTy :: ScopeReader m => DepPairType n -> Atom n -> m n (Type n)
instantiateDepPairTy (DepPairType b rhsTy) x = applyAbs (Abs b rhsTy) (SubstVal x)
{-# INLINE instantiateDepPairTy #-}

instantiatePi :: ScopeReader m => PiType n -> Atom n -> m n (EffectRow n, Type n)
instantiatePi (PiType b eff body) x = do
  PairE eff' body' <- applyAbs (Abs b (PairE eff body)) (SubstVal x)
  return (eff', body')
{-# INLINE instantiatePi #-}

instantiateTabPi :: ScopeReader m => TabPiType n -> Atom n -> m n (Type n)
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
  PtrLit (PtrSnapshot t _) -> PtrType t
  PtrLit (PtrLitVal   t _) -> PtrType t

lamExprTy :: LamBinder n l -> Type l -> Type n
lamExprTy (LamBinder b ty arr eff) bodyTy =
  Pi $ PiType (PiBinder b ty arr) eff bodyTy

numNaryPiArgs :: NaryPiType n -> Int
numNaryPiArgs (NaryPiType (NonEmptyNest _ bs) _ _) = 1 + nestLength bs

naryLamExprType :: EnvReader m => NaryLamExpr n -> m n (NaryPiType n)
naryLamExprType (NaryLamExpr (NonEmptyNest b bs) eff body) = liftTypeQueryM idSubst do
  substBinders b \b' -> do
    substBinders bs \bs' -> do
      let b''  = binderToPiBinder b'
      let bs'' = fmapNest binderToPiBinder bs'
      eff' <- substM eff
      bodyTy <- getTypeE body
      return $ NaryPiType (NonEmptyNest b'' bs'') eff' bodyTy
  where
    binderToPiBinder :: Binder n l -> PiBinder n l
    binderToPiBinder (nameBinder:>ty) = PiBinder nameBinder ty PlainArrow

specializedFunType :: EnvReader m => SpecializationSpec n -> m n (NaryPiType n)
specializedFunType (AppSpecialization f ab) = liftEnvReaderM $
  refreshAbs ab \extraArgBs (ListE staticArgs) -> do
    let extraArgBs' = fmapNest plainPiBinder extraArgBs
    lookupAtomName (sink f) >>= \case
      TopFunBound fTy _ -> do
        NaryPiType dynArgBs effs resultTy <- instantiateNaryPi fTy staticArgs
        let allBs = fromJust $ nestToNonEmpty $ extraArgBs' >>> nonEmptyToNest dynArgBs
        return $ NaryPiType allBs effs resultTy
      _ -> error "should only be specializing top-level functions"

oneEffect :: Effect n -> EffectRow n
oneEffect eff = EffectRow (S.singleton eff) Nothing

projectLength :: (Fallible1 m, EnvReader m) => Type n -> m n Int
projectLength ty = case ty of
  TypeCon _ defName params -> do
    def <- lookupDataDef defName
    [DataConDef _ (Abs bs UnitE)] <- instantiateDataDef def params
    return $ nestLength bs
  StaticRecordTy types -> return $ length types
  ProdTy tys -> return $ length tys
  _ -> error $ "Projecting a type that doesn't support projecting: " ++ pprint ty

sourceNameType :: (EnvReader m, Fallible1 m)
               => SourceName -> m n (Type n)
sourceNameType v = do
  lookupSourceMap v >>= \case
    Nothing -> throw UnboundVarErr $ pprint v
    Just uvar -> case uvar of
      UAtomVar    v' -> getType $ Var v'
      UTyConVar   v' -> lookupEnv v' >>= \case TyConBinding _     e -> getType e
      UDataConVar v' -> lookupEnv v' >>= \case DataConBinding _ _ e -> getType e
      UClassVar   v' -> lookupEnv v' >>= \case ClassBinding  def -> return $ getClassTy def
      UMethodVar  v' -> lookupEnv v' >>= \case MethodBinding _ _ e  -> getType e
      UEffectVar   _ -> error "not implemented: sourceNameType::UEffectVar"
      UEffectOpVar _ -> error "not implemented: sourceNameType::UEffectOpVar"
      UHandlerVar  _ -> error "not implemented: sourceNameType::UHandlerVar"

typeAsBinderNest :: ScopeReader m => Type n -> m n (Abs (Nest Binder) UnitE n)
typeAsBinderNest ty = do
  Abs ignored body <- toConstAbs UnitE
  return $ Abs (Nest (ignored:>ty) Empty) body
{-# INLINE typeAsBinderNest #-}

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

computeAbsEffects :: (EnvExtender m, SubstE Name e)
  => Abs (Nest Decl) e n -> m n (Abs (Nest Decl) (EffectRow `PairE` e) n)
computeAbsEffects it = refreshAbs it \decls result -> do
  effs <- declNestEffects decls
  return $ Abs decls (effs `PairE` result)
{-# INLINE computeAbsEffects #-}

declNestEffects :: (EnvReader m) => Nest Decl n l -> m l (EffectRow l)
declNestEffects decls = liftEnvReaderM $ declNestEffectsRec decls mempty
{-# INLINE declNestEffects #-}

declNestEffectsRec :: Nest Decl n l -> EffectRow l -> EnvReaderM l (EffectRow l)
declNestEffectsRec Empty !acc = return acc
declNestEffectsRec n@(Nest decl rest) !acc = withExtEvidence n do
  expr <- sinkM $ declExpr decl
  deff <- getEffects expr
  acc' <- sinkM $ acc <> deff
  declNestEffectsRec rest acc'
  where
    declExpr :: Decl n l -> Expr n
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

class HasType (e::E) where
  getTypeE :: e i -> TypeQueryM i o (Type o)

instance HasType AtomName where
  getTypeE name = do
    substM (Var name) >>= \case
      Var name' -> atomBindingType <$> lookupEnv name'
      atom -> getType atom
  {-# INLINE getTypeE #-}

instance HasType Atom where
  getTypeE atom = case atom of
    Var name -> getTypeE name
    Lam lamExpr -> getTypeE lamExpr
    Pi _ -> return TyKind
    TabLam lamExpr -> getTypeE lamExpr
    TabPi _ -> return TyKind
    DepPair _ _ ty -> do
      ty' <- substM ty
      return $ DepPairTy ty'
    DepPairTy _ -> return TyKind
    Con con -> getTypePrimCon con
    TC _ -> return TyKind
    Eff _ -> return EffKind
    DataCon _ defName params _ _ -> do
      defName' <- substM defName
      (DataDef sourceName _ _) <- lookupDataDef defName'
      params' <- substM params
      return $ TypeCon sourceName defName' params'
    TypeCon _ _ _ -> return TyKind
    DictCon dictExpr -> getTypeE dictExpr
    DictTy (DictType _ _ _) -> return TyKind
    LabeledRow _ -> return LabeledRowKind
    Record items -> StaticRecordTy <$> mapM getTypeE items
    RecordTy _ -> return TyKind
    Variant vtys _ _ _ -> substM $ VariantTy vtys
    VariantTy _ -> return TyKind
    ACase _ _ resultTy -> substM resultTy
    DataConRef defName params _ -> do
      defName' <- substM defName
      DataDef sourceName _ _ <- lookupDataDef defName'
      params' <- substM params
      return $ RawRefTy $ TypeCon sourceName defName' params'
    DepPairRef _ _ ty -> do
      ty' <- substM ty
      return $ RawRefTy $ DepPairTy ty'
    BoxedRef (Abs (NonDepNest bs ptrsAndSizes) body) -> do
      ptrTys <- forM ptrsAndSizes \(BoxPtr ptr _) -> getTypeE ptr
      withFreshBinders ptrTys \bs' vs -> do
        extendSubst (bs @@> map Rename vs) do
          bodyTy <- getTypeE body
          return $ ignoreHoistFailure $ hoist bs' bodyTy
    ProjectElt (i NE.:| is) v -> do
      ty <- getTypeE $ case NE.nonEmpty is of
              Nothing -> Var v
              Just is' -> ProjectElt is' v
      case ty of
        TypeCon _ defName params -> do
          v' <- substM (Var v) >>= \case
            (Var v') -> return v'
            _ -> error "!??"
          def <- lookupDataDef defName
          [DataConDef _ (Abs bs' UnitE)] <- instantiateDataDef def params
          PairB bsInit (Nest (_:>bTy) _) <- return $ splitNestAt i bs'
          -- `ty` can depend on earlier binders from this constructor. Rewrite
          -- it to also use projections.
          dropSubst $
            applyNaryAbs (Abs bsInit bTy)
              [ SubstVal (ProjectElt (j NE.:| is) v')
              | j <- iota $ nestLength bsInit]
        StaticRecordTy types -> return $ toList types !! i
        RecordTy _ -> throw CompilerErr "Can't project partially-known records"
        ProdTy xs -> return $ xs !! i
        DepPairTy t | i == 0 -> return $ depPairLeftTy t
        DepPairTy t | i == 1 -> do v' <- substM (Var v) >>= \case
                                     (Var v') -> return v'
                                     _ -> error "!?"
                                   instantiateDepPairTy t (ProjectElt (0 NE.:| is) v')
        Var _ -> throw CompilerErr $ "Tried to project value of unreduced type " <> pprint ty
        _ -> throw TypeErr $
              "Only single-member ADTs and record types can be projected. Got " <> pprint ty <> "   " <> pprint v

getTypeRef :: HasType e => e i -> TypeQueryM i o (Type o)
getTypeRef x = do
  TC (RefType _ a) <- getTypeE x
  return a

instance HasType LamExpr where
  getTypeE (LamExpr (LamBinder b ty arr effs) body) = do
    ty' <- substM ty
    let binding = toBinding $ LamBinding arr ty'
    withFreshBinder (getNameHint b) binding \b' -> do
      extendRenamer (b@>binderName b') do
        effs' <- substM effs
        bodyTy <- getTypeE body
        return $ lamExprTy (LamBinder b' ty' arr effs') bodyTy

instance HasType TabLamExpr where
  getTypeE (TabLamExpr (b:>ann) body) = do
    ann' <- substM ann
    withFreshBinder (getNameHint b) (toBinding ann') \b' ->
      extendRenamer (b@>binderName b') $ do
        bodyTy <- getTypeE body
        return $ TabTy (b':>ann') bodyTy

getTypePrimCon :: PrimCon (Atom i) -> TypeQueryM i o (Type o)
getTypePrimCon con = case con of
  Lit l -> return $ BaseTy $ litType l
  ProdCon xs -> ProdTy <$> mapM getTypeE xs
  SumCon ty _ _ -> substM ty
  SumAsProd ty _ _ -> substM ty
  FinVal n _ -> substM $ TC $ Fin n
  BaseTypeRef p -> do
    (PtrTy (_, b)) <- getTypeE p
    return $ RawRefTy $ BaseTy b
  TabRef tabTy -> do
    TabTy binder (RawRefTy a) <- getTypeE tabTy
    return $ RawRefTy $ TabTy binder a
  ConRef conRef -> case conRef of
    ProdCon xs -> RawRefTy <$> (ProdTy <$> mapM getTypeRef xs)
    FinVal n _ -> substM $ RawRefTy $ TC $ Fin n
    SumAsProd ty _ _ -> do
      RawRefTy <$> substM ty
    _ -> error $ "Not a valid ref: " ++ pprint conRef
  RecordRef xs -> (RawRefTy . StaticRecordTy) <$> traverse getTypeRef xs
  LabelCon _   -> return $ TC $ LabelType
  ExplicitDict dictTy _ -> substM dictTy
  DictHole _ ty -> substM ty

dictExprType :: DictExpr i -> TypeQueryM i o (DictType o)
dictExprType e = case e of
  InstanceDict instanceName args -> do
    instanceName' <- substM instanceName
    InstanceDef className bs params _ <- lookupInstanceDef instanceName'
    ClassDef sourceName _ _ _ _ <- lookupClassDef className
    args' <- mapM substM args
    ListE params' <- applyNaryAbs (Abs bs (ListE params)) (map SubstVal args')
    return $ DictType sourceName className params'
  InstantiatedGiven given args -> do
    givenTy <- getTypeE given
    DictTy dTy <- typeApp givenTy (toList args)
    return dTy
  SuperclassProj d i -> do
    DictTy (DictType _ className params) <- getTypeE d
    ClassDef _ _ bs superclasses _ <- lookupClassDef className
    DictTy dTy <- applySubst (bs @@> map SubstVal params) $
                    superclassTypes superclasses !! i
    return dTy
  IxFin n -> do
    n' <- substM n
    ixDictType $ TC $ Fin n'

getIxClassName :: (Fallible1 m, EnvReader m) => m n (ClassName n)
getIxClassName = lookupSourceMap "Ix" >>= \case
  Nothing -> throw CompilerErr $ "Ix interface needed but not defined!"
  Just (UClassVar v) -> return v
  Just _ -> error "not a class var"

ixDictType :: (Fallible1 m, EnvReader m) => Type n -> m n (DictType n)
ixDictType ty = do
  ixClassName <- getIxClassName
  return $ DictType "Ix" ixClassName [ty]

typeApp  :: Type o -> [Atom i] -> TypeQueryM i o (Type o)
typeApp fTy [] = return fTy
typeApp fTy xs = case fromNaryPiType (length xs) fTy of
  Just (NaryPiType bs _ resultTy) -> do
    xs' <- mapM substM xs
    let subst = bs @@> fmap SubstVal xs'
    applySubst subst resultTy
  Nothing -> throw TypeErr $
    "Not a " ++ show (length xs) ++ "-argument pi type: " ++ pprint fTy
      ++ " (tried to apply it to: " ++ pprint xs ++ ")"

typeTabApp :: Type o -> NE.NonEmpty (Atom i) -> TypeQueryM i o (Type o)
typeTabApp tabTy xs = go tabTy $ toList xs
  where
    go :: Type o -> [Atom i] -> TypeQueryM i o (Type o)
    go ty [] = return ty
    go ty (i:rest) = do
      TabTy (b:>_) resultTy <- return ty
      i' <- substM i
      resultTy' <- applySubst (b@>SubstVal i') resultTy
      go resultTy' rest

instance HasType DictExpr where
  getTypeE e = DictTy <$> dictExprType e

instance HasType Expr where
  getTypeE expr = case expr of
    App f xs -> do
      fTy <- getTypeE f
      typeApp fTy $ toList xs
    TabApp f xs -> do
      fTy <- getTypeE f
      typeTabApp fTy xs
    Atom x   -> getTypeE x
    Op   op  -> getTypePrimOp op
    Hof  hof -> getTypePrimHof hof
    Case _ _ resultTy _ -> substM resultTy

getTypePrimOp :: PrimOp (Atom i) -> TypeQueryM i o (Type o)
getTypePrimOp op = case op of
  TabCon ty _ -> substM ty
  BinOp binop x _ -> do
    xTy <- getTypeBaseType x
    return $ TC $ BaseType $ typeBinOp binop xTy
  UnOp unop x -> TC . BaseType . typeUnOp unop <$> getTypeBaseType x
  Select _ x _ -> getTypeE x
  PrimEffect ref m -> do
    TC (RefType ~(Just (Var _)) s) <- getTypeE ref
    return case m of
      MGet        -> s
      MPut _      -> UnitTy
      MAsk        -> s
      MExtend _ _ -> UnitTy
  IndexRef ref i -> do
    getTypeE ref >>= \case
      TC (RefType h (TabTy (b:>_) eltTy)) -> do
        i' <- substM i
        eltTy' <- applyAbs (Abs b eltTy) (SubstVal i')
        return $ TC $ RefType h eltTy'
      ty -> error $ "Not a reference to a table: " ++
                       pprint (Op op) ++ " : " ++ pprint ty
  ProjRef i ref -> do
    getTypeE ref >>= \case
      RefTy h (ProdTy tys) -> return $ RefTy h $ tys !! i
      ty -> error $ "Not a reference to a product: " ++ pprint ty
  IOAlloc t _ -> return $ PtrTy (Heap CPU, t)
  IOFree _ -> return UnitTy
  PtrOffset arr _ -> getTypeE arr
  PtrLoad ptr -> do
    PtrTy (_, t) <- getTypeE ptr
    return $ BaseTy t
  PtrStore _ _ -> return UnitTy
  ThrowError ty -> substM ty
  ThrowException ty -> substM ty
  CastOp t _ -> substM t
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
        Con (LabelCon l) -> return $ RecordTy $ prependFieldRowElem
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
      (Con (LabelCon l), RecordTyWithElems (StaticFields items:rest)) -> do
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
          Just rest -> return $ StaticRecordTy $ Unlabeled
            [ RecordTy els, RecordTyWithElems rest ]
          Nothing -> splitFailed
      (Var v, RecordTyWithElems (DynFields v':rest)) | v == v' ->
        return $ StaticRecordTy $ Unlabeled
          [ RecordTyWithElems [DynFields v'], RecordTyWithElems rest ]
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
  VariantLift types variant -> do
    types' <- mapM substM types
    rty <- getTypeE variant
    rest <- case rty of
      VariantTy rest -> return rest
      _ -> throw TypeErr $ "Can't add alternatives to a non-variant object "
                        <> pprint variant <> " (of type " <> pprint rty <> ")"
    return $ VariantTy $ prefixExtLabeledItems types' rest
  VariantSplit types variant -> do
    types' <- mapM substM types
    fullty <- getTypeE variant
    full <- case fullty of
      VariantTy full -> return full
      _ -> throw TypeErr $ "Can't split a non-variant object "
                          <> pprint variant <> " (of type " <> pprint fullty
                          <> ")"
    diff <- labeledRowDifference' full (NoExt types')
    return $ VariantTy $ NoExt $
      Unlabeled [ VariantTy $ NoExt types', VariantTy diff ]
  DataConTag _ -> return TagRepTy
  ToEnum t _ -> substM t
  SumToVariant x -> getTypeE x >>= \case
    SumTy cases -> return $ VariantTy $ NoExt $ foldMap (labeledSingleton "c") cases
    ty -> error $ "Not a sum type: " ++ pprint ty
  OutputStreamPtr ->
    return $ BaseTy $ hostPtrTy $ hostPtrTy $ Scalar Word8Type
    where hostPtrTy ty = PtrType (Heap CPU, ty)
  ProjMethod dict i -> do
    DictTy (DictType _ className params) <- getTypeE dict
    def@(ClassDef _ _ paramBs classBs methodTys) <- lookupClassDef className
    let MethodType _ methodTy = methodTys !! i
    superclassDicts <- getSuperclassDicts def <$> substM dict
    let subst = (    paramBs @@> map SubstVal params
                 <.> classBs @@> map SubstVal superclassDicts)
    applySubst subst methodTy
  ExplicitApply _ _ -> error "shouldn't appear after inference"
  MonoLiteral _ -> error "shouldn't appear after inference"
  AllocDest ty -> RawRefTy <$> substM ty
  Place _ _ -> return UnitTy
  Freeze ref -> getTypeE ref >>= \case
    RawRefTy ty -> return ty
    ty -> error $ "Not a reference type: " ++ pprint ty
  VectorBroadcast _ vty -> substM vty
  VectorIota vty -> substM vty
  VectorSubref ref _ vty -> getTypeE ref >>= \case
    TC (RefType h _) -> TC . RefType h <$> substM vty
    ty -> error $ "Not a reference type: " ++ pprint ty
  Resume _ _ -> throw NotImplementedErr "getTypePrimOp.Resume"

getSuperclassDicts :: ClassDef n -> Atom n -> [Atom n]
getSuperclassDicts (ClassDef _ _ _ (SuperclassBinders classBs _) _) dict =
  for [0 .. nestLength classBs - 1] \i -> DictCon $ SuperclassProj dict i

getTypeBaseType :: HasType e => e i -> TypeQueryM i o BaseType
getTypeBaseType e =
  getTypeE e >>= \case
    TC (BaseType b) -> return b
    ty -> throw TypeErr $ "Expected a base type. Got: " ++ pprint ty

labeledRowDifference' :: ExtLabeledItems (Type o) (AtomName o)
                      -> ExtLabeledItems (Type o) (AtomName o)
                      -> TypeQueryM i o (ExtLabeledItems (Type o) (AtomName o))
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

getTypePrimHof :: PrimHof (Atom i) -> TypeQueryM i o (Type o)
getTypePrimHof hof = addContext ("Checking HOF:\n" ++ pprint hof) case hof of
  For _ dict f -> do
    Pi (PiType (PiBinder b _ _) _ eltTy) <- getTypeE f
    ixTy <- ixTyFromDict =<< substM dict
    return $ TabTy (b:>ixTy) eltTy
  While _ -> return UnitTy
  Linearize f -> do
    Pi (PiType (PiBinder binder a PlainArrow) Pure b) <- getTypeE f
    let b' = ignoreHoistFailure $ hoist binder b
    fLinTy <- a --@ b'
    a --> PairTy b' fLinTy
  Transpose f -> do
    Pi (PiType (PiBinder binder a LinArrow) Pure b) <- getTypeE f
    let b' = ignoreHoistFailure $ hoist binder b
    b' --@ a
  RunReader _ f -> do
    (resultTy, _) <- getTypeRWSAction f
    return resultTy
  RunWriter _ f -> do
    uncurry PairTy <$> getTypeRWSAction f
  RunState _ f -> do
    (resultTy, stateTy) <- getTypeRWSAction f
    return $ PairTy resultTy stateTy
  RunIO f -> do
    Pi (PiType (PiBinder b _ _) _ resultTy) <- getTypeE f
    return $ ignoreHoistFailure $ hoist b resultTy
  CatchException f -> do
    Pi (PiType (PiBinder b _ _) _ resultTy) <- getTypeE f
    return $ MaybeTy $ ignoreHoistFailure $ hoist b resultTy
  Seq _ _ cinit _ -> getTypeE cinit

getTypeRWSAction :: Atom i -> TypeQueryM i o (Type o, Type o)
getTypeRWSAction f = do
  BinaryFunTy regionBinder refBinder _ resultTy <- getTypeE f
  PiBinder _ (RefTy _ referentTy) _ <- return refBinder
  let referentTy' = ignoreHoistFailure $ hoist regionBinder referentTy
  let resultTy' = ignoreHoistFailure $ hoist (PairB regionBinder refBinder) resultTy
  return (resultTy', referentTy')

instance HasType Block where
  getTypeE (Block NoBlockAnn Empty result) = getTypeE result
  getTypeE (Block (BlockAnn ty _) _ _) = substM ty
  getTypeE _ = error "impossible"

getClassTy :: ClassDef n -> Type n
getClassTy (ClassDef _ _ bs _ _) = go bs
  where
    go :: Nest Binder n l -> Type n
    go Empty = TyKind
    go (Nest (b:>ty) rest) = Pi $ PiType (PiBinder b ty PlainArrow) Pure $ go rest

ixTyFromDict :: EnvReader m => Atom n -> m n (IxType n)
ixTyFromDict dict = do
  getType dict >>= \case
    DictTy (DictType "Ix" _ [iTy]) -> return $ IxType iTy dict
    _ -> error $ "Not an Ix dict: " ++ pprint dict

-- === querying effects implementation ===

class HasEffectsE (e::E) where
  getEffectsImpl :: e i -> TypeQueryM i o (EffectRow o)

instance HasEffectsE Expr where
  getEffectsImpl = exprEffects
  {-# INLINE getEffectsImpl #-}

instance HasEffectsE DeclBinding where
  getEffectsImpl (DeclBinding _ _ expr) = getEffectsImpl expr
  {-# INLINE getEffectsImpl #-}

exprEffects :: Expr i -> TypeQueryM i o (EffectRow o)
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
  TabApp _ _ -> return Pure
  Op op   -> case op of
    PrimEffect ref m -> do
      getTypeSubst ref >>= \case
        RefTy (Var h) _ ->
          return $ case m of
            MGet      -> oneEffect (RWSEffect State  $ Just h)
            MPut    _ -> oneEffect (RWSEffect State  $ Just h)
            MAsk      -> oneEffect (RWSEffect Reader $ Just h)
            -- XXX: We don't verify the base monoid. See note about RunWriter.
            MExtend _ _ -> oneEffect (RWSEffect Writer $ Just h)
        _ -> error "References must have reference type"
    ThrowException _ -> return $ oneEffect ExceptionEffect
    IOAlloc  _ _  -> return $ oneEffect IOEffect
    IOFree   _    -> return $ oneEffect IOEffect
    PtrLoad  _    -> return $ oneEffect IOEffect
    PtrStore _ _  -> return $ oneEffect IOEffect
    _ -> return Pure
  Hof hof -> case hof of
    For _ _ f     -> functionEffs f
    While body    -> functionEffs body
    Linearize _   -> return Pure  -- Body has to be a pure function
    Transpose _   -> return Pure  -- Body has to be a pure function
    RunWriter _ f -> rwsFunEffects Writer f
    RunReader _ f -> rwsFunEffects Reader f
    RunState  _ f -> rwsFunEffects State  f
    RunIO f -> do
      effs <- functionEffs f
      return $ deleteEff IOEffect effs
    CatchException f -> do
      effs <- functionEffs f
      return $ deleteEff ExceptionEffect effs
    Seq _ _ _ f   -> functionEffs f
  Case _ _ _ effs -> substM effs

instance HasEffectsE Block where
  getEffectsImpl (Block (BlockAnn _ effs) _ _) = substM effs
  getEffectsImpl (Block NoBlockAnn _ _) = return Pure
  {-# INLINE getEffectsImpl #-}

instance HasEffectsE Alt where
  getEffectsImpl (Abs bs body) =
    substBinders bs \bs' ->
      ignoreHoistFailure . hoist bs' <$> getEffectsImpl body
  {-# INLINE getEffectsImpl #-}

functionEffs :: Atom i -> TypeQueryM i o (EffectRow o)
functionEffs f = getTypeSubst f >>= \case
  Pi (PiType b effs _) -> return $ ignoreHoistFailure $ hoist b effs
  _ -> error "Expected a function type"

rwsFunEffects :: RWS -> Atom i -> TypeQueryM i o (EffectRow o)
rwsFunEffects rws f = getTypeSubst f >>= \case
   BinaryFunTy h ref effs _ -> do
     let effs' = ignoreHoistFailure $ hoist ref effs
     let effs'' = deleteEff (RWSEffect rws (Just (binderName h))) effs'
     return $ ignoreHoistFailure $ hoist h effs''
   _ -> error "Expected a binary function type"

deleteEff :: Effect n -> EffectRow n -> EffectRow n
deleteEff eff (EffectRow effs t) = EffectRow (S.delete eff effs) t

-- === singleton types ===

-- The following implementation should be valid:
--   isSingletonType :: EnvReader m => Type n -> m n Bool
--   isSingletonType ty =
--     singletonTypeVal ty >>= \case
--       Nothing -> return False
--       Just _  -> return True
-- But a separate implementation doesn't have to go under binders,
-- because it doesn't have to reconstruct the singleton value (which
-- may be type annotated and whose type may refer to names).

isSingletonType :: Type n -> Bool
isSingletonType topTy = isJust $ checkIsSingleton topTy
  where
    checkIsSingleton :: Type n -> Maybe ()
    checkIsSingleton ty = case ty of
      Pi (PiType _ Pure body) -> checkIsSingleton body
      TabPi (TabPiType _ body) -> checkIsSingleton body
      StaticRecordTy items -> mapM_ checkIsSingleton items
      TC con -> case con of
        ProdType tys -> mapM_ checkIsSingleton tys
        _ -> Nothing
      _ -> Nothing

singletonTypeVal :: EnvReader m => Type n -> m n (Maybe (Atom n))
singletonTypeVal ty = liftEnvReaderT $
  runSubstReaderT idSubst $ singletonTypeValRec ty
{-# INLINE singletonTypeVal #-}

-- TODO: TypeCon with a single case?
singletonTypeValRec :: Type i
  -> SubstReaderT Name (EnvReaderT Maybe) i o (Atom o)
singletonTypeValRec ty = case ty of
  Pi (PiType b Pure body) ->
    substBinders b \(PiBinder b' ty' arr) -> do
      body' <- singletonTypeValRec body
      return $ Lam $ LamExpr (LamBinder b' ty' arr Pure) $ AtomicBlock body'
  TabPi (TabPiType b body) ->
    substBinders b \b' -> do
      body' <- singletonTypeValRec body
      return $ TabLam $ TabLamExpr b' $ AtomicBlock body'
  StaticRecordTy items -> Record <$> traverse singletonTypeValRec items
  TC con -> case con of
    ProdType tys -> ProdVal <$> traverse singletonTypeValRec tys
    _            -> notASingleton
  _ -> notASingleton
  where notASingleton = fail "not a singleton type"

