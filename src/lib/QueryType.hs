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
  numNaryPiArgs, specializedFunType,
  projectionIndices, sourceNameType, typeBinOp, typeUnOp,
  isSingletonType, singletonTypeVal, ixDictType, getSuperclassDicts,
  ixTyFromDict,
  isNewtype, instantiateHandlerType, getDestBlockType, forceDRepVal, toDRepVal,
  getNaryLamExprType
  ) where

import Control.Category ((>>>))
import Control.Monad
import Data.Foldable (toList)
import Data.Functor ((<&>))
import Data.List (elemIndex)
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import Data.Maybe (isJust)
import qualified Data.Set        as S

import Types.Primitives
import Types.Core
import Types.Source
import IRVariants
import Core
import CheapReduction (cheapNormalize)
import Err
import LabeledItems
import Name
import Util
import PPrint ()

-- === Main API for querying types ===

getTypeSubst :: (SubstReader (AtomSubstVal r) m
                , EnvReader2 m, HasType r e)
             => e i -> m i o (Type r o)
getTypeSubst e = do
  subst <- getSubst
  liftTypeQueryM subst $ getTypeE e
{-# INLINE getTypeSubst #-}

getType :: (EnvReader m, HasType r e) => e n -> m n (Type r n)
getType e = liftTypeQueryM idSubst $ getTypeE e
{-# INLINE getType #-}

getNaryLamExprType :: EnvReader m => LamExpr r n -> m n (NaryPiType r n)
getNaryLamExprType lam = liftTypeQueryM idSubst $ getLamExprType lam
{-# INLINE getNaryLamExprType #-}

-- TODO: make `DestBlock` a newtype with a real `HasType` instance
type DestBlock r = Abs (Binder r) (Block r)
getDestBlockType :: EnvReader m => DestBlock r n -> m n (Type r n)
getDestBlockType (Abs (_:>RawRefTy ansTy) _) = return ansTy
getDestBlockType _ = error "Expected a reference type for body destination"
{-# INLINE getDestBlockType #-}

-- === Querying effects ===

isPure :: (EnvReader m, HasEffectsE e r) => e n -> m n Bool
isPure e = getEffects e <&> \case
  Pure -> True
  _    -> False

getEffects :: (EnvReader m, HasEffectsE e r) => e n -> m n (EffectRow n)
getEffects e = liftTypeQueryM idSubst $ getEffectsImpl e
{-# INLINE getEffects #-}

getEffectsSubst :: (EnvReader2 m, SubstReader (AtomSubstVal r) m, HasEffectsE e r)
              => e i -> m i o (EffectRow o)
getEffectsSubst e = do
  subst <- getSubst
  liftTypeQueryM subst $ getEffectsImpl e
{-# INLINE getEffectsSubst #-}

-- === Exposed helpers for querying types and effects ===

caseAltsBinderTys :: (Fallible1 m, EnvReader m)
                  => Type r n -> m n [Type r n]
caseAltsBinderTys ty = case ty of
  TypeCon _ defName params -> do
    def <- lookupDataDef defName
    cons <- instantiateDataDef def params
    return [unsafeCoerceIRE repTy | DataConDef _ repTy _ <- cons]
  SumTy types -> return types
  VariantTy (NoExt types) -> return $ toList types
  VariantTy _ -> fail "Can't pattern-match partially-known variants"
  _ -> fail $ "Case analysis only supported on ADTs and variants, not on " ++ pprint ty

depPairLeftTy :: DepPairType r n -> Type r n
depPairLeftTy (DepPairType (_:>ty) _) = ty
{-# INLINE depPairLeftTy #-}

extendEffect :: Effect n -> EffectRow n -> EffectRow n
extendEffect eff (EffectRow effs t) = EffectRow (S.insert eff effs) t

getAppType :: EnvReader m => Type r n -> [Atom r n] -> m n (Type r n)
getAppType f xs = liftTypeQueryM idSubst $ typeApp f xs
{-# INLINE getAppType #-}

getTabAppType :: EnvReader m => Type r n -> [Atom r n] -> m n (Type r n)
getTabAppType f xs = case NE.nonEmpty xs of
  Nothing -> getType f
  Just xs' -> liftTypeQueryM idSubst $ typeTabApp f xs'
{-# INLINE getTabAppType #-}

getBaseMonoidType :: Fallible1 m => ScopeReader m => Type r n -> m n (Type r n)
getBaseMonoidType ty = case ty of
  Pi (PiType b _ resultTy) -> liftHoistExcept $ hoist b resultTy
  _     -> return ty
{-# INLINE getBaseMonoidType #-}

getReferentTy :: MonadFail m => EmptyAbs (PairB (Binder r) (Binder r)) n -> m (Type r n)
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

instantiateDataDef :: ScopeReader m => DataDef n -> DataDefParams r n -> m n [DataConDef n]
instantiateDataDef (DataDef _ bs cons) (DataDefParams params) = do
  let dataDefParams' = DataDefParams [(arr, unsafeCoerceIRE x) | (arr, x) <- params]
  fromListE <$> applyDataConAbs (Abs bs $ ListE cons) dataDefParams'
{-# INLINE instantiateDataDef #-}

applyDataConAbs :: (SubstE (AtomSubstVal r) e, SinkableE e, ScopeReader m)
                => Abs (Nest (RolePiBinder r)) e n -> DataDefParams r n -> m n (e n)
applyDataConAbs (Abs bs e) (DataDefParams xs) =
  applySubst (bs @@> (SubstVal <$> map snd xs)) e
{-# INLINE applyDataConAbs #-}

-- Returns a representation type (type of an TypeCon-typed Newtype payload)
-- given a list of instantiated DataConDefs.
dataDefRep :: [DataConDef n] -> Type r n
dataDefRep = \case
  [] -> error "unreachable"  -- There's no representation for a void type
  [DataConDef _ ty _] -> unsafeCoerceIRE ty
  tys -> SumTy $ tys <&> \(DataConDef _ ty _) -> unsafeCoerceIRE ty

instantiateNaryPi :: EnvReader m => NaryPiType r n  -> [Atom r n] -> m n (NaryPiType r n)
instantiateNaryPi (NaryPiType bs eff resultTy) args = do
  PairB bs1 bs2 <- return $ splitNestAt (length args) bs
  applySubst (bs1 @@> map SubstVal args) (NaryPiType bs2 eff resultTy)
{-# INLINE instantiateNaryPi #-}

instantiateDepPairTy :: ScopeReader m => DepPairType r n -> Atom r n -> m n (Type r n)
instantiateDepPairTy (DepPairType b rhsTy) x = applyAbs (Abs b rhsTy) (SubstVal x)
{-# INLINE instantiateDepPairTy #-}

instantiatePi :: ScopeReader m => PiType r n -> Atom r n -> m n (EffectRow n, Type r n)
instantiatePi (PiType b eff body) x = do
  PairE eff' body' <- applyAbs (Abs b (PairE eff body)) (SubstVal x)
  return (eff', body')
{-# INLINE instantiatePi #-}

instantiateTabPi :: ScopeReader m => TabPiType r n -> Atom r n -> m n (Type r n)
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

specializedFunType :: EnvReader m => SpecializationSpec n -> m n (NaryPiType CoreIR n)
specializedFunType (AppSpecialization f ab) = liftEnvReaderM $
  refreshAbs ab \extraArgBs (ListE staticArgs) -> do
    let extraArgBs' = fmapNest (plainPiBinder . (\(b:>ty) -> b :> unsafeCoerceIRE ty)) extraArgBs
    lookupAtomName (sink f) >>= \case
      TopFunBound fTy _ -> do
        NaryPiType dynArgBs effs resultTy <- instantiateNaryPi fTy staticArgs
        let allBs = extraArgBs' >>> dynArgBs
        return $ NaryPiType allBs effs resultTy
      _ -> error "should only be specializing top-level functions"

userEffect :: EffectName n -> Atom r n
userEffect v = Eff (OneEffect (UserEffect v))

projectionIndices :: (Fallible1 m, EnvReader m) => Type r n -> m n [[Projection]]
projectionIndices ty = case ty of
  TypeCon _ defName _ -> do
    DataDef _ _ cons <- lookupDataDef defName
    case cons of
      [DataConDef _ _ idxs] -> return idxs
      _ -> unsupported
  StaticRecordTy types -> return $ iota (length types) <&> \i ->
    [ProjectProduct i, UnwrapCompoundNewtype]
  ProdTy tys -> return $ iota (length tys) <&> \i -> [ProjectProduct i]
  DepPairTy _ -> return $ [[ProjectProduct 0], [ProjectProduct 1]]
  _ -> unsupported
  where unsupported = error $ "Projecting a type that doesn't support projecting: " ++ pprint ty

sourceNameType :: (EnvReader m, Fallible1 m)
               => SourceName -> m n (Type r n)
sourceNameType v = do
  lookupSourceMap v >>= \case
    Nothing -> throw UnboundVarErr $ pprint v
    Just uvar -> case uvar of
      UAtomVar    v' -> getType $ Var v'
      UTyConVar   v' -> lookupEnv v' >>= \case TyConBinding _     e -> unsafeCoerceIRE <$> getType e
      UDataConVar v' -> lookupEnv v' >>= \case DataConBinding _ _ e -> unsafeCoerceIRE <$> getType e
      UClassVar   v' -> lookupEnv v' >>= \case ClassBinding  def    -> return $ unsafeCoerceIRE $ getClassTy def
      UMethodVar  v' -> lookupEnv v' >>= \case MethodBinding _ _ e  -> unsafeCoerceIRE <$> getType e
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

computeAbsEffects :: (EnvExtender m, SubstE Name e)
  => Abs (Nest (Decl r)) e n -> m n (Abs (Nest (Decl r)) (EffectRow `PairE` e) n)
computeAbsEffects it = refreshAbs it \decls result -> do
  effs <- declNestEffects decls
  return $ Abs decls (effs `PairE` result)
{-# INLINE computeAbsEffects #-}

declNestEffects :: (EnvReader m) => Nest (Decl r) n l -> m l (EffectRow l)
declNestEffects decls = liftEnvReaderM $ declNestEffectsRec decls mempty
{-# INLINE declNestEffects #-}

declNestEffectsRec :: Nest (Decl r) n l -> EffectRow l -> EnvReaderM l (EffectRow l)
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

newtype TypeQueryM (r::IR) (i::S) (o::S) (a :: *) = TypeQueryM {
  runTypeQueryM :: SubstReaderT (AtomSubstVal r) EnvReaderM i o a }
  deriving ( Functor, Applicative, Monad
           , EnvReader, EnvExtender, ScopeReader
           , SubstReader (AtomSubstVal r))

liftTypeQueryM :: (EnvReader m) => Subst (AtomSubstVal r) i o
               -> TypeQueryM r i o a -> m o a
liftTypeQueryM subst act =
  liftEnvReaderM $
    runSubstReaderT subst $
      runTypeQueryM act
{-# INLINE liftTypeQueryM #-}

instance MonadFail (TypeQueryM r i o) where
  fail = error
  {-# INLINE fail #-}

instance Fallible (TypeQueryM r i o) where
  throwErrs err = error $ pprint err
  {-# INLINE throwErrs #-}
  addErrCtx = const id
  {-# INLINE addErrCtx #-}

class HasType (r::IR) (e::E) | e -> r where
  getTypeE :: e i -> TypeQueryM r i o (Type r o)

instance HasType r (AtomName r) where
  getTypeE name = do
    substM (Var name) >>= \case
      --- XXX: unsafe. fix!  The issue is that we have no way to statically check that
      --- a name occurring in SimpIR is not referring to a CoreIR binding, or anything
      --- like that.
      Var name' -> (unsafeCoerceIRE . atomBindingType) <$> lookupAtomName name'
      atom -> getType atom
  {-# INLINE getTypeE #-}

instance HasType r (Atom r) where
  getTypeE :: forall i o. Atom r i -> TypeQueryM r i o (Type r o)
  getTypeE atom = case atom of
    Var name -> getTypeE name
    Lam (UnaryLamExpr (b:>ty) body) arr effs -> do
      ty' <- substM ty
      effs' <- substM effs
      withFreshBinder (getNameHint b) (LamBinding arr ty') \b' -> do
        effs'' <- applyAbs (sink effs') (binderName b')
        extendRenamer (b@>binderName b') do
          bodyTy <- getTypeE body
          return $ Pi $ PiType (PiBinder b' ty' arr) effs'' bodyTy
    Lam _ _ _ -> error "expected a unary lambda expression"
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
    PtrVar v -> substM v >>= lookupEnv >>= \case
      PtrBinding ty _ -> return $ PtrTy ty
    TypeCon _ _ _ -> return TyKind
    DictCon dictExpr -> getTypeE dictExpr
    DictTy (DictType _ _ _) -> return TyKind
    LabeledRow _ -> return LabeledRowKind
    RecordTy _ -> return TyKind
    VariantTy _ -> return TyKind
    ACase _ _ resultTy -> substM resultTy
    RepValAtom dRepVal -> do
      RepVal ty _ <- substM dRepVal >>= forceDRepVal
      return ty
    ProjectElt (i NE.:| is) v -> do
      ty <- getTypeE $ case NE.nonEmpty is of
              Nothing -> Var v
              Just is' -> ProjectElt is' v
      case ty of
        ProdTy xs -> return $ xs !! iProj
        DepPairTy t | iProj == 0 -> return $ depPairLeftTy t
        DepPairTy t | iProj == 1 -> do
          v' <- substM (Var v :: Atom r i) >>= \case
            (Var v') -> return v'
            _ -> error "!?"
          instantiateDepPairTy t (ProjectElt (ProjectProduct 0 NE.:| is) v')
        _ | isNewtype ty -> projectNewtype ty
        Var _ -> throw CompilerErr $ "Tried to project value of unreduced type " <> pprint ty
        _ -> throw TypeErr $
              "Only single-member ADTs and record types can be projected. Got " <> pprint ty
        where
          iProj = case i of
            ProjectProduct i' -> i'
            _ -> error "Not a product projection"

-- === newtype conversion ===

isNewtype :: Type r n -> Bool
isNewtype ty = case ty of
  TC Nat        -> True
  TC (Fin _)    -> True
  TypeCon _ _ _ -> True
  RecordTy _    -> True
  VariantTy _   -> True
  _ -> False

projectNewtype :: Type r o -> TypeQueryM r i o (Type r o)
projectNewtype ty = case ty of
  TC Nat     -> return IdxRepTy
  TC (Fin _) -> return NatTy
  TypeCon _ defName params -> do
    def <- lookupDataDef defName
    dataDefRep <$> instantiateDataDef def params
  StaticRecordTy types -> return $ ProdTy $ toList types
  RecordTy _ -> throw CompilerErr "Can't project partially-known records"
  _ -> error $ "not a newtype: " ++ pprint ty

forceDRepVal
  :: (r `Sat` Is SimpToImpIR, EnvReader m)
  => DRepVal r n -> m n (RepVal r n)
forceDRepVal repVal = liftTypeQueryM idSubst $ forceDRepVal' repVal

forceDRepVal'
  :: r `Sat` Is SimpToImpIR
  => DRepVal r n -> TypeQueryM r i n (RepVal r n)
forceDRepVal' (DRepVal [] ty tree) = return $ RepVal ty tree
forceDRepVal' (DRepVal (p:ps) ty tree) = do
  RepVal ty' tree' <- forceDRepVal' (DRepVal ps ty tree)
  case p of
    ProjectProduct i -> do
      case ty' of
        ProdTy tys -> do
          Branch trees <- return tree'
          return $ RepVal (tys!!i) (trees!!i)
        DepPairTy t -> do
          Branch [leftTree, rightTree] <- return tree'
          let leftVal = RepVal (depPairLeftTy t) leftTree
          case i of
            0 -> return leftVal
            1 -> do
              rightTy <- instantiateDepPairTy t (RepValAtom $ toDRepVal leftVal)
              return $ RepVal rightTy rightTree
            _ -> error "bad dependent pair projection index"
        _ -> error $ "not a product type: " ++ pprint ty'
    UnwrapCompoundNewtype -> RepVal <$> projectNewtype ty' <*> pure tree'
    UnwrapBaseNewtype     -> RepVal <$> projectNewtype ty' <*> pure tree'

toDRepVal ::  RepVal r n -> DRepVal r n
toDRepVal (RepVal ty tree) = DRepVal [] ty tree

instance HasType r (TabLamExpr r) where
  getTypeE (TabLamExpr (b:>ann) body) = do
    ann' <- substM ann
    withFreshBinder (getNameHint b) (toBinding ann') \b' ->
      extendRenamer (b@>binderName b') $ do
        bodyTy <- getTypeE body
        return $ TabTy (b':>ann') bodyTy

getTypePrimCon :: PrimCon r (Atom r i) -> TypeQueryM r i o (Type r o)
getTypePrimCon con = case con of
  Lit l -> return $ BaseTy $ litType l
  ProdCon xs -> ProdTy <$> mapM getTypeE xs
  SumCon tys _ _ -> SumTy <$> traverse substM tys
  SumAsProd tys _ _ -> SumTy <$> traverse substM tys
  Newtype ty _ -> substM ty
  LabelCon _   -> return $ TC $ LabelType
  ExplicitDict dictTy _ -> substM dictTy
  DictHole _ ty -> substM ty

dictExprType :: IsCore r => DictExpr r i -> TypeQueryM r i o (Type r o)
dictExprType e = case e of
  InstanceDict instanceName args -> do
    instanceName' <- substM instanceName
    InstanceDef className bs params _ <- lookupInstanceDef instanceName'
    ClassDef sourceName _ _ _ _ <- lookupClassDef className
    args' <- mapM substM args
    let bs' = fmapNest (\(RolePiBinder b _ _ _) -> b) bs
    ListE params' <- applyNaryAbs (Abs bs' (ListE (map unsafeCoerceIRE params))) (map SubstVal args')
    return $ DictTy $ DictType sourceName className params'
  InstantiatedGiven given args -> do
    givenTy <- getTypeE given
    typeApp givenTy (toList args)
  SuperclassProj d i -> do
    DictTy (DictType _ className params) <- getTypeE d
    ClassDef _ _ bs superclasses _ <- lookupClassDef className
    applySubst (bs @@> map SubstVal params) $ unsafeCoerceIRE (superclassTypes superclasses !! i)
  IxFin n -> do
    n' <- substM n
    liftM DictTy $ ixDictType $ TC $ Fin n'

getIxClassName :: (Fallible1 m, EnvReader m) => m n (ClassName n)
getIxClassName = lookupSourceMap "Ix" >>= \case
  Nothing -> throw CompilerErr $ "Ix interface needed but not defined!"
  Just (UClassVar v) -> return v
  Just _ -> error "not a class var"

ixDictType :: (Fallible1 m, EnvReader m) => Type r n -> m n (DictType r n)
ixDictType ty = do
  ixClassName <- getIxClassName
  return $ DictType "Ix" ixClassName [ty]

typeApp  :: Type r o -> [Atom r i] -> TypeQueryM r i o (Type r o)
typeApp fTy [] = return fTy
typeApp fTy xs = case fromNaryPiType (length xs) fTy of
  Just (NaryPiType bs _ resultTy) -> do
    xs' <- mapM substM xs
    let subst = bs @@> fmap SubstVal xs'
    applySubst subst resultTy
  Nothing -> throw TypeErr $
    "Not a " ++ show (length xs) ++ "-argument pi type: " ++ pprint fTy
      ++ " (tried to apply it to: " ++ pprint xs ++ ")"

typeTabApp :: Type r o -> NE.NonEmpty (Atom r i) -> TypeQueryM r i o (Type r o)
typeTabApp tabTy xs = go tabTy $ toList xs
  where
    go :: Type r o -> [Atom r i] -> TypeQueryM r i o (Type r o)
    go ty [] = return ty
    go ty (i:rest) = do
      TabTy (b:>_) resultTy <- return ty
      i' <- substM i
      resultTy' <- applySubst (b@>SubstVal i') resultTy
      go resultTy' rest

instance IsCore r => HasType r (DictExpr r) where
  getTypeE e = dictExprType e

instance HasType r (Expr r) where
  getTypeE expr = case expr of
    App f xs -> do
      fTy <- getTypeE f
      typeApp fTy $ toList xs
    TabApp f xs -> do
      fTy <- getTypeE f
      typeTabApp fTy xs
    Atom x   -> getTypeE x
    TabCon ty _ -> substM ty
    DAMOp           op -> getTypeE op
    UserEffectOp    op -> getTypeE op
    PrimOp          op -> getTypeE $ ComposeE op
    RecordVariantOp op -> getTypeE $ ComposeE op
    Hof  hof -> getTypeHof hof
    Case _ _ resultTy _ -> substM resultTy
    ProjMethod dict i -> do
      DictTy (DictType _ className params) <- getTypeE dict
      def@(ClassDef _ _ paramBs classBs methodTys) <- lookupClassDef className
      let MethodType _ methodTy = methodTys !! i
      superclassDicts <- getSuperclassDicts def <$> substM dict
      let subst = (    paramBs @@> map SubstVal params
                   <.> classBs @@> map SubstVal superclassDicts)
      applySubst subst (unsafeCoerceIRE methodTy)
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

instance HasType r (DAMOp r) where
  getTypeE = \case
    AllocDest ty -> RawRefTy <$> substM ty
    Place _ _ -> return UnitTy
    Freeze ref -> getTypeE ref >>= \case
      RawRefTy ty -> return ty
      ty -> error $ "Not a reference type: " ++ pprint ty
    Seq _ _ cinit _ -> getTypeE cinit
    RememberDest d _ -> getTypeE d

instance HasType r (UserEffectOp r) where
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
      return $ unsafeCoerceIRE lamTy
    Resume retTy _ -> substM retTy

instance HasType r (ComposeE PrimOp (Atom r)) where
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
      SumTag _ -> return TagRepTy
      ToEnum t _ -> substM t
      OutputStream ->
        return $ BaseTy $ hostPtrTy $ Scalar Word8Type
        where hostPtrTy ty = PtrType (CPU, ty)
    VectorOp op -> case op of
      VectorBroadcast _ vty -> substM vty
      VectorIota vty -> substM vty
      VectorSubref ref _ vty -> getTypeE ref >>= \case
        TC (RefType h _) -> TC . RefType h <$> substM vty
        ty -> error $ "Not a reference type: " ++ pprint ty

instance HasType r (ComposeE RecordVariantOp (Atom r)) where
  getTypeE (ComposeE recordVariantOp) = case recordVariantOp of
    SumToVariant x -> getTypeE x >>= \case
      SumTy cases -> return $ VariantTy $ NoExt $ foldMap (labeledSingleton "c") cases
      ty -> error $ "Not a sum type: " ++ pprint ty
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
      return $ SumTy [ VariantTy $ NoExt types', VariantTy diff ]
    VariantMake ty _ _ _ -> substM ty

instantiateHandlerType :: EnvReader m => HandlerName n -> Atom r n -> [Atom r n] -> m n (Type r n)
instantiateHandlerType hndName r args = do
  HandlerDef _ rb bs _effs retTy _ _ <- lookupHandlerDef hndName
  applySubst (rb @> (SubstVal r) <.> bs @@> (map SubstVal args)) (unsafeCoerceIRE retTy)

getSuperclassDicts :: IsCore r => ClassDef n -> Atom r n -> [Atom r n]
getSuperclassDicts (ClassDef _ _ _ (SuperclassBinders classBs _) _) dict =
  for [0 .. nestLength classBs - 1] \i -> DictCon $ SuperclassProj dict i

getTypeBaseType :: HasType r e => e i -> TypeQueryM r i o BaseType
getTypeBaseType e =
  getTypeE e >>= \case
    TC (BaseType b) -> return b
    ty -> throw TypeErr $ "Expected a base type. Got: " ++ pprint ty

labeledRowDifference' :: ExtLabeledItems (Type r o) (AtomName r o)
                      -> ExtLabeledItems (Type r o) (AtomName r o)
                      -> TypeQueryM r i o (ExtLabeledItems (Type r o) (AtomName r o))
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

getTypeHof :: Hof r i -> TypeQueryM r i o (Type r o)
getTypeHof hof = addContext ("Checking HOF:\n" ++ pprint hof) case hof of
  For _ dict f -> do
    NaryPiType (UnaryNest (PiBinder b _ _)) _ eltTy <- getLamExprType f
    ixTy <- ixTyFromDict =<< substM dict
    return $ TabTy (b:>ixTy) eltTy
  While _ -> return UnitTy
  Linearize f -> do
    NaryPiType (UnaryNest (PiBinder binder a _)) Pure b <- getLamExprType f
    let b' = ignoreHoistFailure $ hoist binder b
    fLinTy <- a --@ b'
    a --> PairTy b' fLinTy
  Transpose f -> do
    NaryPiType (UnaryNest (PiBinder binder a _)) Pure b <- getLamExprType f
    let b' = ignoreHoistFailure $ hoist binder b
    b' --@ a
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
  CatchException f -> MaybeTy <$> getTypeE f

getLamExprType :: LamExpr r i -> TypeQueryM r i o (NaryPiType r o)
getLamExprType (LamExpr bs body) =
  substBinders bs \bs' -> do
    effs <- substM $ blockEffects body
    resultTy <- getTypeE body
    let piBinders = fmapNest (\(b:>ty) -> PiBinder b ty PlainArrow) bs'
    return $ NaryPiType piBinders effs resultTy

getTypeRWSAction :: LamExpr r i -> TypeQueryM r i o (Type r o, Type r o)
getTypeRWSAction f = do
  NaryPiType (BinaryNest regionBinder refBinder) _ resultTy <- getLamExprType f
  PiBinder _ (RefTy _ referentTy) _ <- return refBinder
  let referentTy' = ignoreHoistFailure $ hoist regionBinder referentTy
  let resultTy' = ignoreHoistFailure $ hoist (PairB regionBinder refBinder) resultTy
  return (resultTy', referentTy')

instance HasType r (Block r) where
  getTypeE (Block NoBlockAnn Empty result) = getTypeE result
  getTypeE (Block (BlockAnn ty _) _ _) = substM ty
  getTypeE _ = error "impossible"

getClassTy :: ClassDef n -> Type CoreIR n
getClassTy (ClassDef _ _ bs _ _) = go bs
  where
    go :: Nest (RolePiBinder CoreIR) n l -> Type CoreIR n
    go Empty = TyKind
    go (Nest (RolePiBinder b ty arr _) rest) = Pi $ PiType (PiBinder b ty arr) Pure $ go rest

ixTyFromDict :: EnvReader m => IxDict r n -> m n (IxType r n)
ixTyFromDict ixDict = flip IxType ixDict <$> case ixDict of
  IxDictAtom dict -> getType dict >>= \case
    DictTy (DictType "Ix" _ [iTy]) -> return iTy
    _ -> error $ "Not an Ix dict: " ++ pprint dict
  IxDictFin n -> return $ TC $ Fin n
  IxDictSpecialized n _ _ -> return n

-- === querying effects implementation ===

class HasEffectsE (e::E) (r::IR) | e -> r where
  getEffectsImpl :: e i -> TypeQueryM r i o (EffectRow o)

instance HasEffectsE (Expr r) r where
  getEffectsImpl = exprEffects
  {-# INLINE getEffectsImpl #-}

instance HasEffectsE (DeclBinding r) r where
  getEffectsImpl (DeclBinding _ _ expr) = getEffectsImpl expr
  {-# INLINE getEffectsImpl #-}

exprEffects :: Expr r i -> TypeQueryM r i o (EffectRow o)
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
  RefOp ref m -> do
    h <- getMaybeHeapVar <$> getTypeSubst ref
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
    Perform ~(Eff eff) _ -> substM eff
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
      BitcastOp _ _    -> return Pure
      SumTag _         -> return Pure
      ToEnum _ _       -> return Pure
      OutputStream     -> return Pure
  DAMOp op -> case op of
    Place    _ _  -> return $ OneEffect InitEffect
    Seq _ _ _ f      -> functionEffs f
    RememberDest _ f -> functionEffs f
    AllocDest _ -> return Pure -- is this correct?
    Freeze _    -> return Pure -- is this correct?
  Hof hof -> case hof of
    For _ _ f     -> functionEffs f
    While body    -> getEffectsImpl body
    Linearize _   -> return Pure  -- Body has to be a pure function
    Transpose _   -> return Pure  -- Body has to be a pure function
    RunReader _ f -> rwsFunEffects Reader f
    RunWriter d _ f -> rwsFunEffects Writer f <&> maybeInit d
    RunState  d _ f -> rwsFunEffects State  f <&> maybeInit d
    RunIO          f -> deleteEff IOEffect        <$> getEffectsImpl f
    RunInit        f -> deleteEff InitEffect      <$> getEffectsImpl f
    CatchException f -> deleteEff ExceptionEffect <$> getEffectsImpl f
    where maybeInit :: Maybe (Atom r i) -> (EffectRow o -> EffectRow o)
          maybeInit d = case d of Just _ -> (<>OneEffect InitEffect); Nothing -> id
  Case _ _ _ effs -> substM effs
  TabCon _ _        -> return Pure
  ProjMethod _ _    -> return Pure
  RecordVariantOp _ -> return Pure

instance HasEffectsE (Block r) r where
  getEffectsImpl (Block (BlockAnn _ effs) _ _) = substM effs
  getEffectsImpl (Block NoBlockAnn _ _) = return Pure
  {-# INLINE getEffectsImpl #-}

instance HasEffectsE (Alt r) r where
  getEffectsImpl (Abs bs body) =
    substBinders bs \bs' ->
      ignoreHoistFailure . hoist bs' <$> getEffectsImpl body
  {-# INLINE getEffectsImpl #-}

functionEffs :: LamExpr r i -> TypeQueryM r i o (EffectRow o)
functionEffs f = getLamExprType f >>= \case
  NaryPiType b effs _ -> return $ ignoreHoistFailure $ hoist b effs

rwsFunEffects :: RWS -> LamExpr r i -> TypeQueryM r i o (EffectRow o)
rwsFunEffects rws f = getLamExprType f >>= \case
   NaryPiType (BinaryNest h ref) effs _ -> do
     let effs' = ignoreHoistFailure $ hoist ref effs
     let effs'' = deleteEff (RWSEffect rws (Just (binderName h))) effs'
     return $ ignoreHoistFailure $ hoist h effs''
   _ -> error "Expected a binary function type"

deleteEff :: Effect n -> EffectRow n -> EffectRow n
deleteEff eff (EffectRow effs t) = EffectRow (S.delete eff effs) t

getMaybeHeapVar :: Type r o -> Maybe (AtomName r o)
getMaybeHeapVar (TC (RefType h _)) = case h of
  Just (Var h') -> Just h'
  Just UnitTy   -> Nothing
  Nothing       -> Nothing
  _ -> error "expect heap parameter to be a var or UnitTy"
getMaybeHeapVar refTy = error $ "not a ref type: " ++ pprint refTy

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

isSingletonType :: Type r n -> Bool
isSingletonType topTy = isJust $ checkIsSingleton topTy
  where
    checkIsSingleton :: Type r n -> Maybe ()
    checkIsSingleton ty = case ty of
      Pi (PiType _ Pure body) -> checkIsSingleton body
      TabPi (TabPiType _ body) -> checkIsSingleton body
      StaticRecordTy items -> mapM_ checkIsSingleton items
      TC con -> case con of
        ProdType tys -> mapM_ checkIsSingleton tys
        _ -> Nothing
      _ -> Nothing

singletonTypeVal :: EnvReader m => Type r n -> m n (Maybe (Atom r n))
singletonTypeVal ty = liftEnvReaderT $
  runSubstReaderT idSubst $ singletonTypeValRec ty
{-# INLINE singletonTypeVal #-}

-- TODO: TypeCon with a single case?
singletonTypeValRec :: Type r i
  -> SubstReaderT Name (EnvReaderT Maybe) i o (Atom r o)
singletonTypeValRec ty = case ty of
  Pi (PiType b Pure body) -> do
    effs <- toConstAbs Pure
    substBinders b \(PiBinder b' ty' arr) -> do
      body' <- singletonTypeValRec body
      return $ Lam (LamExpr (UnaryNest (b':>ty')) $ AtomicBlock body') arr effs
  TabPi (TabPiType b body) ->
    substBinders b \b' -> do
      body' <- singletonTypeValRec body
      return $ TabLam $ TabLamExpr b' $ AtomicBlock body'
  StaticRecordTy items -> do
    StaticRecordTy items' <- substM ty
    Record items' <$> traverse singletonTypeValRec (toList items)
  TC con -> case con of
    ProdType tys -> ProdVal <$> traverse singletonTypeValRec tys
    _            -> notASingleton
  _ -> notASingleton
  where notASingleton = fail "not a singleton type"

