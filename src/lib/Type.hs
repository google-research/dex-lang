-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Type (
  HasType (..), CheckableE (..), CheckableB (..),
  checkTypes, checkTypesM,
  getType, getAppType, getTabAppType, getTypeSubst, litType, getBaseMonoidType,
  instantiatePi, instantiateTabPi, instantiateDepPairTy,
  checkExtends, checkedApplyDataDefParams, checkedApplyClassParams,
  instantiateDataDef,
  caseAltsBinderTys, tryGetType, projectLength,
  sourceNameType, getMethodType,
  checkUnOp, checkBinOp,
  oneEffect, lamExprTy, isData, asFirstOrderFunction, asFFIFunType,
  isSingletonType, singletonTypeVal, asNaryPiType,
  numNaryPiArgs, naryLamExprType, getMethodIndex,
  extendEffect, exprEffects, declNestEffects, computeAbsEffects, getReferentTy) where

import Prelude hiding (id)
import Control.Category ((>>>))
import Control.Monad
import Control.Monad.Reader
import Data.Maybe (isJust)
import Data.Foldable (toList)
import Data.Functor
import Data.List (elemIndex)
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import qualified Data.Set        as S

import LabeledItems

import Err
import Util (forMZipped, forMZipped_, iota)

import CheapReduction
import {-# SOURCE #-} Interpreter
import Syntax
import Name
import PPrint ()

-- === top-level API ===

checkTypes :: (EnvReader m, CheckableE e) => e n -> m n (Except ())
checkTypes e = liftTyperT $ void $ checkE e
{-# SCC checkTypes #-}

checkTypesM :: (EnvReader m, Fallible1 m, CheckableE e) => e n -> m n ()
checkTypesM e = liftExcept =<< checkTypes e

getType :: (EnvReader m, HasType e) => e n -> m n (Type n)
getType e = liftHardFailTyperT $ getTypeE e
{-# INLINE getType #-}

getAppType :: EnvReader m => Type n -> [Atom n] -> m n (Type n)
getAppType f xs = liftHardFailTyperT $ checkApp f xs

getTabAppType :: EnvReader m => Type n -> [Atom n] -> m n (Type n)
getTabAppType f xs = case nonEmpty xs of
  Nothing -> getType f
  Just xs' -> liftHardFailTyperT $ checkTabApp f xs'

getTypeSubst :: (SubstReader Name m, EnvReader2 m, HasType e)
             => e i -> m i o (Type o)
getTypeSubst e = do
  subst <- getSubst
  liftM runHardFail $ liftEnvReaderT $
    runSubstReaderT subst $
      runTyperT' $ getTypeE e

tryGetType :: (EnvReader m, Fallible1 m, HasType e) => e n -> m n (Type n)
tryGetType e = liftExcept =<< liftTyperT (getTypeE e)

depPairLeftTy :: DepPairType n -> Type n
depPairLeftTy (DepPairType (_:>ty) _) = ty

instantiateDepPairTy :: ScopeReader m => DepPairType n -> Atom n -> m n (Type n)
instantiateDepPairTy (DepPairType b rhsTy) x = applyAbs (Abs b rhsTy) (SubstVal x)

instantiatePi :: ScopeReader m => PiType n -> Atom n -> m n (EffectRow n, Type n)
instantiatePi (PiType b eff body) x = do
  PairE eff' body' <- applyAbs (Abs b (PairE eff body)) (SubstVal x)
  return (eff', body')

instantiateTabPi :: ScopeReader m => TabPiType n -> Atom n -> m n (Type n)
instantiateTabPi (TabPiType b body) x = applyAbs (Abs b body) (SubstVal x)

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

getReferentTy :: MonadFail m => EmptyAbs (PairB LamBinder LamBinder) n -> m (Type n)
getReferentTy (Abs (PairB hB refB) UnitE) = do
  RefTy _ ty <- return $ binderType refB
  HoistSuccess ty' <- return $ hoist hB ty
  return ty'

getClassTy :: ClassDef n -> Type n
getClassTy (ClassDef _ _ bs _ _) = go bs
  where
    go :: Nest Binder n l -> Type n
    go Empty = TyKind
    go (Nest (b:>ty) rest) = Pi $ PiType (PiBinder b ty PlainArrow) Pure $ go rest

-- === querying effects ===

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
  deff <- exprEffects expr
  acc' <- sinkM $ acc <> deff
  declNestEffectsRec rest acc'
  where
    declExpr :: Decl n l -> Expr n
    declExpr (Let _ (DeclBinding _ _ expr)) = expr

exprEffects :: (EnvReader m) => Expr n -> m n (EffectRow n)
exprEffects expr = case expr of
  Atom _  -> return Pure
  App f xs -> do
    fTy <- getType f
    case fromNaryPiType (length xs) fTy of
      Just (NaryPiType bs effs _) -> do
        let subst = bs @@> fmap SubstVal xs
        applySubst subst effs
      Nothing -> error $
        "Not a " ++ show (length xs + 1) ++ "-argument pi type: " ++ pprint expr
  TabApp _ _ -> return Pure
  Op op   -> case op of
    PrimEffect ref m -> do
      getType ref >>= \case
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
    For _ f         -> functionEffs f
    -- The tiled and scalar bodies should have the same effects, but
    -- that's checked elsewhere.  If they are the same, merging them
    -- with <> is a noop.
    Tile _ tiled scalar -> liftM2 (<>) (functionEffs tiled) $ functionEffs scalar
    While body      -> functionEffs body
    Linearize _     -> return Pure  -- Body has to be a pure function
    Transpose _     -> return Pure  -- Body has to be a pure function
    RunWriter _ f -> rwsFunEffects Writer f
    RunReader _ f -> rwsFunEffects Reader f
    RunState  _ f -> rwsFunEffects State  f
    PTileReduce _ _ _ -> return mempty
    RunIO f -> do
      effs <- functionEffs f
      return $ deleteEff IOEffect effs
    CatchException f -> do
      effs <- functionEffs f
      return $ deleteEff ExceptionEffect effs
  Case _ _ _ effs -> return effs
{-# SPECIALIZE exprEffects :: Expr n -> EnvReaderM n (EffectRow n) #-}

functionEffs :: EnvReader m => Atom n -> m n (EffectRow n)
functionEffs f = getType f >>= \case
  Pi (PiType b effs _) -> return $ ignoreHoistFailure $ hoist b effs
  _ -> error "Expected a function type"

rwsFunEffects :: EnvReader m => RWS -> Atom n -> m n (EffectRow n)
rwsFunEffects rws f = getType f >>= \case
   BinaryFunTy h ref effs _ -> do
     let effs' = ignoreHoistFailure $ hoist ref effs
     let effs'' = deleteEff (RWSEffect rws (Just (binderName h))) effs'
     return $ ignoreHoistFailure $ hoist h effs''
   _ -> error "Expected a binary function type"

deleteEff :: Effect n -> EffectRow n -> EffectRow n
deleteEff eff (EffectRow effs t) = EffectRow (S.delete eff effs) t

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

liftHardFailTyperT :: EnvReader m' => TyperT HardFailM n n a -> m' n a
liftHardFailTyperT cont = liftM runHardFail $ liftTyperT cont
{-# INLINE liftHardFailTyperT #-}

instance Fallible m => Typer (TyperT m)

-- === typeable things ===

-- Minimal complete definition: getTypeE | getTypeAndSubstE
-- (Usually we just implement `getTypeE` but for big things like blocks it can
-- be worth implementing the specialized versions too, as optimizations.)
class (SinkableE e, SubstE Name e, PrettyE e) => HasType (e::E) where
  getTypeE   :: Typer m => e i -> m i o (Type o)
  getTypeE e = snd <$> getTypeAndSubstE e

  getTypeAndSubstE :: Typer m => e i -> m i o (e o, Type o)
  getTypeAndSubstE e = (,) <$> substM e <*> getTypeE e

  checkTypeE :: Typer m => Type o -> e i -> m i o (e o)
  checkTypeE reqTy e = do
    (e', ty) <- getTypeAndSubstE e
    -- TODO: Write an alphaEq variant that works modulo an equivalence
    -- relation on names.
    alphaEq reqTy ty >>= \case
      True  -> return ()
      False -> {-# SCC typeNormalization #-} do
        reqTy' <- cheapNormalize reqTy
        ty'    <- cheapNormalize ty
        alphaEq reqTy' ty' >>= \case
          True  -> return ()
          False -> throw TypeErr $ pprint reqTy' ++ " != " ++ pprint ty'
    return e'

class SinkableE e => CheckableE (e::E) where
  checkE :: Typer m => e i -> m i o (e o)

checkFromHasType :: HasType e => Typer m => e i -> m i o (e o)
checkFromHasType e = fst <$> getTypeAndSubstE e

class HasNamesB b => CheckableB (b::B) where
  checkB :: Typer m
         => b i i'
         -> (forall o'. Ext o o' => b o o' -> m i' o' a)
         -> m i o a

checkBEvidenced :: (CheckableB b, Typer m)
                => b i i'
                -> (forall o'. ExtEvidence o o' -> b o o' -> m i' o' a)
                -> m i o a
checkBEvidenced b cont = checkB b \b' -> cont getExtEvidence b'

-- === convenience functions ===

infixr 7 |:
(|:) :: (Typer m, HasType e) => e i -> Type o -> m i o ()
(|:) x reqTy = void $ checkTypeE reqTy x

-- === top-level env ===

instance CheckableE Block where
  checkE = checkFromHasType

instance CheckableE SourceMap where
  checkE sourceMap = substM sourceMap

instance CheckableE SynthCandidates where
  checkE scs = substM scs

instance CheckableB (RecSubstFrag Binding) where
  checkB frag cont = do
    substBinders frag \frag' -> do
      void $ dropSubst $ traverseSubstFrag checkE $ fromRecSubstFrag frag'
      cont frag'

instance CheckableB EnvFrag where
  checkB (EnvFrag frag effs) cont = do
    checkB frag \frag' -> do
      effs' <- mapM checkE effs
      cont $ EnvFrag frag' effs'

instance Color c => CheckableE (Binding c) where
  checkE binding = case binding of
    AtomNameBinding   atomNameBinding   -> AtomNameBinding <$> checkE atomNameBinding
    DataDefBinding    dataDef           -> DataDefBinding  <$> checkE dataDef
    TyConBinding      dataDefName     e -> TyConBinding    <$> substM dataDefName              <*> substM e
    DataConBinding    dataDefName idx e -> DataConBinding  <$> substM dataDefName <*> pure idx <*> substM e
    ClassBinding      classDef          -> ClassBinding    <$> substM classDef
    InstanceBinding   instanceDef       -> InstanceBinding <$> substM instanceDef
    SuperclassBinding className   idx   -> SuperclassBinding <$> substM className <*> pure idx
    MethodBinding className idx f       -> MethodBinding     <$> substM className <*> pure idx <*> substM f
    ImpFunBinding     f                 -> ImpFunBinding     <$> substM f
    ObjectFileBinding objfile           -> ObjectFileBinding <$> substM objfile
    ModuleBinding     md                -> ModuleBinding     <$> substM md
    PtrBinding        ptr               -> PtrBinding        <$> return ptr

instance CheckableE AtomBinding where
  checkE binding = case binding of
    LetBound letBinding -> LetBound    <$> checkE letBinding
    LamBound lamBinding -> LamBound    <$> checkE lamBinding
    PiBound  piBinding  -> PiBound     <$> checkE piBinding
    MiscBound ty        -> MiscBound   <$> checkTypeE TyKind ty
    SolverBound b       -> SolverBound <$> checkE b
    PtrLitBound ty ptr  -> PtrLitBound ty <$> substM ptr
    -- TODO: check the type actually matches the lambda term
    SimpLamBound ty lam -> do
      lam' <- substM lam
      ty' <- substM ty
      dropSubst $ checkNaryLamExpr lam' ty'
      return $ SimpLamBound ty' lam'
    FFIFunBound ty name -> do
      _ <- checkFFIFunTypeM ty
      FFIFunBound <$> substM ty <*> substM name

instance CheckableE SolverBinding where
  checkE (InfVarBound  ty ctx) = InfVarBound  <$> checkTypeE TyKind ty <*> pure ctx
  checkE (SkolemBound  ty    ) = SkolemBound  <$> checkTypeE TyKind ty

instance CheckableE DataDef where
  checkE = substM -- TODO

instance (CheckableE e1, CheckableE e2) => CheckableE (PairE e1 e2) where
  checkE (PairE e1 e2) = PairE <$> checkE e1 <*> checkE e2

instance (CheckableB b, CheckableE e) => CheckableE (Abs b e) where
  checkE (Abs b e) = checkB b \b' -> Abs b' <$> checkE e

-- === type checking core ===

instance CheckableE Atom where
  checkE atom = fst <$> getTypeAndSubstE atom

instance CheckableE Expr where
  checkE expr = fst <$> getTypeAndSubstE expr

instance HasType AtomName where
  getTypeE name = do
    name' <- substM name
    atomBindingType <$> lookupEnv name'
  {-# INLINE getTypeE #-}

instance HasType Atom where
  getTypeE atom = case atom of
    Var name -> getTypeE name
    Lam lamExpr -> getTypeE lamExpr
    Pi piType -> getTypeE piType
    TabLam lamExpr -> getTypeE lamExpr
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
    DataCon _ defName params conIx args -> do
      defName' <- substM defName
      (DataDef sourceName tyParamNest' absCons') <- lookupDataDef defName'
      params' <- traverse checkE params
      ListE cons' <- checkedApplyNaryAbs (Abs tyParamNest' (ListE absCons')) params'
      let DataConDef _ conParamAbs' = cons' !! conIx
      args'   <- traverse checkE args
      void $ checkedApplyNaryAbs conParamAbs' args'
      return $ TypeCon sourceName defName' params'
    TypeCon _ defName params -> do
      DataDef _ tyParamNest' absCons' <- lookupDataDef =<< substM defName
      params' <- traverse checkE params
      void $ checkedApplyNaryAbs (Abs tyParamNest' (ListE absCons')) params'
      return TyKind
    DictCon dictExpr -> getTypeE dictExpr
    DictTy (DictType _ className params) -> do
      ClassDef _ _ paramBs _ _ <- substM className >>= lookupClassDef
      params' <- mapM substM params
      checkArgTys paramBs params'
      return TyKind
    LabeledRow elems -> checkFieldRowElems elems $> LabeledRowKind
    Record items -> StaticRecordTy <$> mapM getTypeE items
    RecordTy elems -> checkFieldRowElems elems $> TyKind
    Variant vtys@(Ext (LabeledItems types) _) label i arg -> do
      let ty = VariantTy vtys
      let maybeArgTy = do
            labelTys <- M.lookup label types
            guard $ i < length labelTys
            return $ labelTys NE.!! i
      case maybeArgTy of
        Just argTy -> do
          argTy' <- substM argTy
          arg |: argTy'
        Nothing -> throw TypeErr $ "Bad variant: " <> pprint atom
                                   <> " with type " <> pprint ty
      checkTypeE TyKind ty
    VariantTy row -> checkLabeledRow row $> TyKind
    ACase e alts resultTy -> checkCase e alts resultTy Pure
    DataConRef defName params args -> do
      defName' <- substM defName
      DataDef sourceName paramBs [DataConDef _ argBs] <- lookupDataDef defName'
      paramTys <- nonDepBinderNestTypes paramBs
      params' <- forMZipped paramTys params checkTypeE
      argBs' <- applyNaryAbs (Abs paramBs argBs) (map SubstVal params')
      checkDataConRefEnv argBs' args
      return $ RawRefTy $ TypeCon sourceName defName' params'
    DepPairRef l (Abs b r) ty -> do
      ty' <- checkTypeE TyKind ty
      l |: RawRefTy (depPairLeftTy ty')
      checkB b \b' -> do
        ty'' <- sinkM ty'
        rTy <- instantiateDepPairTy ty'' $ Var (binderName b')
        r |: RawRefTy rTy
      return $ RawRefTy $ DepPairTy ty'
    BoxedRef ptrsAndSizes (Abs bs body) -> do
      ptrTys <- forM ptrsAndSizes \(ptr, numel) -> do
        numel |: IdxRepTy
        ty@(PtrTy _) <- getTypeE ptr
        return ty
      withFreshBinders ptrTys \bs' vs -> do
        extendSubst (bs @@> vs) do
          bodyTy <- getTypeE body
          liftHoistExcept $ hoist bs' bodyTy
    ProjectElt (i NE.:| is) v -> do
      ty <- getTypeE $ case NE.nonEmpty is of
              Nothing -> Var v
              Just is' -> ProjectElt is' v
      case ty of
        TypeCon _ defName params -> do
          v' <- substM v
          def <- lookupDataDef defName
          [DataConDef _ (Abs bs' UnitE)] <- checkedApplyDataDefParams def params
          PairB bsInit (Nest (_:>bTy) _) <- return $ splitNestAt i bs'
          -- `ty` can depends on earlier binders from this constructor. Rewrite
          -- it to also use projections.
          dropSubst $
            applyNaryAbs (Abs bsInit bTy) [ SubstVal (ProjectElt (j NE.:| is) v')
                                          | j <- iota $ nestLength bsInit]
        StaticRecordTy types -> return $ toList types !! i
        RecordTy _ -> throw CompilerErr "Can't project partially-known records"
        ProdTy xs -> return $ xs !! i
        DepPairTy t | i == 0 -> return $ depPairLeftTy t
        DepPairTy t | i == 1 -> do v' <- substM v
                                   instantiateDepPairTy t (ProjectElt (0 NE.:| is) v')
        Var _ -> throw CompilerErr $ "Tried to project value of unreduced type " <> pprint ty
        _ -> throw TypeErr $
              "Only single-member ADTs and record types can be projected. Got " <> pprint ty <> "   " <> pprint v

instance (Color c, ToBinding ann c, CheckableE ann)
         => CheckableB (BinderP c ann) where
  checkB (b:>ann) cont = do
    ann' <- checkE ann
    withFreshBinder (getNameHint b) (toBinding ann') \b' ->
      extendRenamer (b@>binderName b') $
        cont $ b' :> ann'

instance HasType Expr where
  getTypeE expr = case expr of
    App f xs -> do
      fTy <- getTypeE f
      checkApp fTy $ toList xs
    TabApp f xs -> do
      fTy <- getTypeE f
      checkTabApp fTy xs
    Atom x   -> getTypeE x
    Op   op  -> typeCheckPrimOp op
    Hof  hof -> typeCheckPrimHof hof
    Case e alts resultTy effs -> checkCase e alts resultTy effs

instance HasType Block where
  getTypeE (Block NoBlockAnn Empty expr) = do
    getTypeE expr
  getTypeE (Block (BlockAnn ty _) decls expr) = do
    tyReq <- substM ty
    checkB decls \_ -> do
      tyReq' <- sinkM tyReq
      expr |: tyReq'
    return tyReq
  getTypeE _ = error "impossible"

instance CheckableB Decl where
  checkB (Let b binding) cont =
    checkB (b:>binding) \(b':>binding') -> cont $ Let b' binding'

instance CheckableE DeclBinding where
  checkE rhs@(DeclBinding ann ty expr) = addContext msg do
    ty' <- checkTypeE TyKind ty
    expr' <- checkTypeE ty' expr
    return $ DeclBinding ann ty' expr'
    where msg = "Checking decl rhs:\n" ++ pprint rhs

instance CheckableE LamBinding where
  checkE (LamBinding arr ty) = do
    ty' <- checkTypeE TyKind ty
    return $ LamBinding arr ty'

instance CheckableE PiBinding where
  checkE (PiBinding arr ty) = do
    ty' <- checkTypeE TyKind ty
    return $ PiBinding arr ty'

instance CheckableB LamBinder where
  checkB (LamBinder b ty arr effs) cont = do
    ty' <- checkTypeE TyKind ty
    let binding = toBinding $ LamBinding arr ty'
    withFreshBinder (getNameHint b) binding \b' -> do
      extendRenamer (b@>binderName b') do
        effs' <- checkE effs
        withAllowedEffects effs' $
          cont $ LamBinder b' ty' arr effs'

instance HasType LamExpr where
  getTypeE (LamExpr b body) = do
    checkB b \b' -> do
      bodyTy <- getTypeE body
      return $ lamExprTy b' bodyTy

instance HasType TabLamExpr where
  getTypeE (TabLamExpr b body) = do
    checkB b \b' -> do
      bodyTy <- getTypeE body
      return $ TabTy b' bodyTy

dictExprType :: Typer m => DictExpr i -> m i o (DictType o)
dictExprType e = case e of
  InstanceDict instanceName args -> do
    instanceName' <- substM instanceName
    InstanceDef className bs params _ <- lookupInstanceDef instanceName'
    ClassDef sourceName _ _ _ _ <- lookupClassDef className
    args' <- mapM substM args
    checkArgTys bs args'
    ListE params' <- applyNaryAbs (Abs bs (ListE params)) (map SubstVal args')
    return $ DictType sourceName className params'
  InstantiatedGiven given args -> do
    givenTy <- getTypeE given
    DictTy dTy <- checkApp givenTy (toList args)
    return dTy
  SuperclassProj d i -> do
    DictTy (DictType _ className params) <- getTypeE d
    ClassDef _ _ bs superclasses _ <- lookupClassDef className
    DictTy dTy <- checkedApplyNaryAbs (Abs bs (superclasses !! i)) params
    return dTy

instance HasType DictExpr where
  getTypeE e = DictTy <$> dictExprType e

instance HasType DepPairType where
  getTypeE (DepPairType b ty) = do
    checkB b \_ -> ty |: TyKind
    return TyKind

lamExprTy :: LamBinder n l -> Type l -> Type n
lamExprTy (LamBinder b ty arr eff) bodyTy =
  Pi $ PiType (PiBinder b ty arr) eff bodyTy

instance HasType PiType where
  getTypeE (PiType b@(PiBinder _ _ arr) eff resultTy) = do
    checkArrowAndEffects arr eff
    checkB b \_ -> do
      void $ checkE eff
      resultTy|:TyKind
    return TyKind

instance HasType TabPiType where
  getTypeE (TabPiType b resultTy) = do
    checkB b \_ -> resultTy|:TyKind
    return TyKind

instance CheckableB PiBinder where
  checkB (PiBinder b ty arr) cont = do
    ty' <- checkTypeE TyKind ty
    let binding = toBinding $ PiBinding arr ty'
    withFreshBinder (getNameHint b) binding \b' -> do
      extendRenamer (b@>binderName b') do
        withAllowedEffects Pure do
          cont $ PiBinder b' ty' arr

instance (BindsNames b, CheckableB b) => CheckableB (Nest b) where
  checkB nest cont = case nest of
    Empty -> cont Empty
    Nest b rest ->
      checkBEvidenced b \ext1 b' ->
        checkBEvidenced rest \ext2 rest' ->
          withExtEvidence (ext1 >>> ext2) $
            cont $ Nest b' rest'

typeCheckPrimTC :: Typer m => PrimTC (Atom i) -> m i o (Type o)
typeCheckPrimTC tc = case tc of
  BaseType _       -> return TyKind
  IntRange a b     -> a|:IdxRepTy >> b|:IdxRepTy >> return TyKind
  IndexRange t a b -> do
    t' <- checkTypeE TyKind t
    mapM_ (|:t') a >> mapM_ (|:t') b >> return TyKind
  IndexSlice n l   -> n|:TyKind >> l|:TyKind >> return TyKind
  ProdType tys     -> mapM_ (|:TyKind) tys >> return TyKind
  SumType  cs      -> mapM_ (|:TyKind) cs  >> return TyKind
  RefType r a      -> mapM_ (|:TyKind) r >> a|:TyKind >> return TyKind
  TypeKind         -> return TyKind
  EffectRowKind    -> return TyKind
  LabeledRowKindTC -> return TyKind
  ParIndexRange t gtid nthr -> gtid|:IdxRepTy >> nthr|:IdxRepTy >> t|:TyKind >> return TyKind
  LabelType        -> return TyKind

typeCheckPrimCon :: Typer m => PrimCon (Atom i) -> m i o (Type o)
typeCheckPrimCon con = case con of
  Lit l -> return $ BaseTy $ litType l
  ProdCon xs -> ProdTy <$> mapM getTypeE xs
  SumCon ty tag payload -> do
    ty'@(SumTy caseTys) <- substM ty
    unless (0 <= tag && tag < length caseTys) $ throw TypeErr "Invalid SumType tag"
    payload |: (caseTys !! tag)
    return ty'
  SumAsProd ty tag _ -> tag |:TagRepTy >> substM ty  -- TODO: check!
  IntRangeVal     l h i -> i|:IdxRepTy >> substM (TC $ IntRange     l h)
  IndexRangeVal t l h i -> i|:IdxRepTy >> substM (TC $ IndexRange t l h)
  IndexSliceVal _ _ _ -> error "not implemented"
  BaseTypeRef p -> do
    (PtrTy (_, b)) <- getTypeE p
    return $ RawRefTy $ BaseTy b
  TabRef tabTy -> do
    TabTy binder (RawRefTy a) <- getTypeE tabTy
    return $ RawRefTy $ TabTy binder a
  ConRef conRef -> case conRef of
    ProdCon xs -> RawRefTy <$> (ProdTy <$> mapM typeCheckRef xs)
    IntRangeVal     l h i -> do
      l' <- substM l
      h' <- substM h
      i|:(RawRefTy IdxRepTy) >> return (RawRefTy $ TC $ IntRange     l' h')
    IndexRangeVal t l h i -> do
      t' <- substM t
      l' <- mapM substM l
      h' <- mapM substM h
      i|:(RawRefTy IdxRepTy)
      return $ RawRefTy $ TC $ IndexRange t' l' h'
    SumAsProd ty tag _ -> do    -- TODO: check args!
      tag |:(RawRefTy TagRepTy)
      RawRefTy <$> substM ty
    _ -> error $ "Not a valid ref: " ++ pprint conRef
  ParIndexCon t v -> t|:TyKind >> v|:IdxRepTy >> substM t
  RecordRef xs -> (RawRefTy . StaticRecordTy) <$> traverse typeCheckRef xs
  LabelCon _   -> return $ TC $ LabelType
  ExplicitDict dictTy method  -> do
    dictTy'@(DictTy (DictType _ className params)) <- checkTypeE TyKind dictTy
    classDef <- lookupClassDef className
    ([], [MethodType _ methodTy]) <- checkedApplyClassParams classDef params
    method |: methodTy
    return dictTy'
  DictHole _ ty -> checkTypeE TyKind ty

typeCheckPrimOp :: Typer m => PrimOp (Atom i) -> m i o (Type o)
typeCheckPrimOp op = case op of
  TabCon ty xs -> do
    ty'@(TabPi tabPi@(TabPiType b restTy)) <- checkTypeE TyKind ty
    case fromConstAbs (Abs b restTy) of
      HoistSuccess elTy -> forM_ xs (|: elTy)
      HoistFailure _    -> do
        idxs <- indices $ argType tabPi
        forMZipped_ xs idxs \x i -> do
          eltTy <- instantiateTabPi tabPi i
          x |: eltTy
    return ty'
  ScalarBinOp binop x y -> do
    xTy <- typeCheckBaseType x
    yTy <- typeCheckBaseType y
    TC <$> BaseType <$> checkBinOp binop xTy yTy
  ScalarUnOp  unop  x -> do
    xTy <- typeCheckBaseType x
    TC <$> BaseType <$> checkUnOp unop xTy
  Select p x y -> do
    p |: (BaseTy $ Scalar Word8Type)
    ty <- getTypeE x
    y |: ty
    return ty
  UnsafeFromOrdinal ty i -> ty|:TyKind >> i|:IdxRepTy >> substM ty
  ToOrdinal i -> getTypeE i $> IdxRepTy
  IdxSetSize i -> getTypeE i $> IdxRepTy
  Inject i -> do
    TC tc <- getTypeE i
    case tc of
      IndexRange ty _ _ -> return ty
      ParIndexRange ty _ _ -> return ty
      _ -> throw TypeErr $ "Unsupported inject argument type: " ++ pprint (TC tc)
  PrimEffect ref m -> do
    TC (RefType ~(Just (Var h')) s) <- getTypeE ref
    case m of
      MGet      ->         declareEff (RWSEffect State  $ Just h') $> s
      MPut  x   -> x|:s >> declareEff (RWSEffect State  $ Just h') $> UnitTy
      MAsk      ->         declareEff (RWSEffect Reader $ Just h') $> s
      MExtend _ x -> x|:s >> declareEff (RWSEffect Writer $ Just h') $> UnitTy
  IndexRef ref i -> do
    getTypeE ref >>= \case
      RefTy h (TabTy (b:>iTy) eltTy) -> do
        i' <- checkTypeE iTy i
        eltTy' <- applyAbs (Abs b eltTy) (SubstVal i')
        return $ RefTy h eltTy'
      ty -> error $ "Not a reference to a table: " ++
                       pprint (Op op) ++ " : " ++ pprint ty
  ProjRef i ref -> do
    getTypeE ref >>= \case
      RefTy h (ProdTy tys) -> return $ RefTy h $ tys !! i
      ty -> error $ "Not a reference to a product: " ++ pprint ty
  IOAlloc t n -> do
    n |: IdxRepTy
    declareEff IOEffect
    return $ PtrTy (Heap CPU, t)
  IOFree ptr -> do
    PtrTy _ <- getTypeE ptr
    declareEff IOEffect
    return UnitTy
  PtrOffset arr off -> do
    PtrTy (a, b) <- getTypeE arr
    off |: IdxRepTy
    return $ PtrTy (a, b)
  PtrLoad ptr -> do
    PtrTy (_, t) <- getTypeE ptr
    declareEff IOEffect
    return $ BaseTy t
  PtrStore ptr val -> do
    PtrTy (_, t)  <- getTypeE ptr
    val |: BaseTy t
    declareEff IOEffect
    return $ UnitTy
  SliceOffset s i -> do
    TC (IndexSlice n l) <- getTypeE s
    l' <- getTypeE i
    checkAlphaEq l l'
    return n
  SliceCurry s i -> do
    TC (IndexSlice n (PairTy u v)) <- getTypeE s
    u' <- getTypeE i
    checkAlphaEq u u'
    return $ TC $ IndexSlice n v
  VectorBinOp _ _ _ -> throw CompilerErr "Vector operations are not supported at the moment"
  VectorPack xs -> do
    unless (length xs == vectorWidth) $ throw TypeErr lengthMsg
    BaseTy (Scalar sb) <- getTypeE $ head xs
    mapM_ (|: (BaseTy (Scalar sb))) xs
    return $ BaseTy $ Vector sb
    where lengthMsg = "VectorBroadcast should have exactly " ++ show vectorWidth ++
                      " elements: " ++ pprint op
  VectorIndex x i -> do
    BaseTy (Vector sb) <- getTypeE x
    i |: TC (IntRange (IdxRepVal 0) (IdxRepVal $ fromIntegral vectorWidth))
    return $ BaseTy $ Scalar sb
  ThrowError ty -> ty|:TyKind >> substM ty
  ThrowException ty -> do
    declareEff ExceptionEffect
    ty|:TyKind >> substM ty
  CastOp t@(Var _) _ -> t |: TyKind >> substM t
  CastOp destTy e -> do
    sourceTy' <- getTypeE e
    destTy |: TyKind
    destTy' <- substM destTy
    checkValidCast sourceTy' destTy'
    return $ destTy'
  RecordCons l r -> do
    lty <- getTypeE l
    rty <- getTypeE r
    case (lty, rty) of
      (RecordTyWithElems lelems, RecordTyWithElems relems) ->
        return $ RecordTyWithElems $ lelems ++ relems
      _ -> throw TypeErr $ "Can't concatenate " <> pprint lty <> " and " <> pprint rty <> " as records"
  RecordConsDynamic lab val record -> do
    lab' <- checkTypeE (TC LabelType) lab
    vty <- getTypeE val
    rty <- getTypeE record
    case rty of
      RecordTy rest -> case lab' of
        Con (LabelCon l) -> return $ RecordTy $ prependFieldRowElem (StaticFields (labeledSingleton l vty)) rest
        Var labVar       -> return $ RecordTy $ prependFieldRowElem (DynField labVar vty) rest
        _ -> error "Unexpected label atom"
      _ -> throw TypeErr $ "Can't add a dynamic field to a non-record value of type " <> pprint rty
  RecordSplitDynamic lab record -> do
    lab' <- cheapNormalize =<< checkTypeE (TC LabelType) lab
    rty <- getTypeE record
    case (lab', rty) of
      (Con (LabelCon l), RecordTyWithElems (StaticFields items:rest)) -> do
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
              NoExt rest <- labeledRowDifference (NoExt yf) (NoExt xf)
              return $ Just $ StaticFields rest : ys
            _ -> return Nothing
        _ -> return Nothing
  VariantLift types variant -> do
    mapM_ (|: TyKind) types
    types' <- mapM substM types
    rty <- getTypeE variant
    rest <- case rty of
      VariantTy rest -> return rest
      _ -> throw TypeErr $ "Can't add alternatives to a non-variant object "
                        <> pprint variant <> " (of type " <> pprint rty <> ")"
    return $ VariantTy $ prefixExtLabeledItems types' rest
  VariantSplit types variant -> do
    mapM_ (|: TyKind) types
    types' <- mapM substM types
    fullty <- getTypeE variant
    full <- case fullty of
      VariantTy full -> return full
      _ -> throw TypeErr $ "Can't split a non-variant object "
                          <> pprint variant <> " (of type " <> pprint fullty
                          <> ")"
    diff <- labeledRowDifference full (NoExt types')
    return $ VariantTy $ NoExt $
      Unlabeled [ VariantTy $ NoExt types', VariantTy diff ]
  DataConTag x -> do
    TypeCon _ _ _ <- getTypeE x
    return TagRepTy
  ToEnum t x -> do
    x |: Word8Ty
    t' <- checkTypeE TyKind t
    case t' of
      TypeCon _ dataDefName [] -> do
        DataDef _ _ dataConDefs <- lookupDataDef dataDefName
        forM_ dataConDefs \(DataConDef _ (Abs binders _)) -> checkEmptyNest binders
      VariantTy _ -> return ()  -- TODO: check empty payload
      SumTy cases -> forM_ cases \cty -> checkAlphaEq cty UnitTy
      _ -> error $ "Not a sum type: " ++ pprint t'
    return t'
  SumToVariant x -> getTypeE x >>= \case
    SumTy cases -> return $ VariantTy $ NoExt $ foldMap (labeledSingleton "c") cases
    ty -> error $ "Not a sum type: " ++ pprint ty
  OutputStreamPtr ->
    return $ BaseTy $ hostPtrTy $ hostPtrTy $ Scalar Word8Type
    where hostPtrTy ty = PtrType (Heap CPU, ty)
  ProjMethod dict i -> do
    DictTy (DictType _ className params) <- getTypeE dict
    methodTy <- getMethodType className i
    dropSubst $ checkApp methodTy params
  ExplicitApply _ _ -> error "shouldn't appear after inference"

getMethodIndex :: EnvReader m => ClassName n -> SourceName -> m n Int
getMethodIndex className methodSourceName = do
  ClassDef _ methodNames _ _ _ <- lookupClassDef className
  case elemIndex methodSourceName methodNames of
    Nothing -> error $ methodSourceName ++ " is not a method of " ++ pprint className
    Just i -> return i

getMethodType :: EnvReader m => ClassName n -> Int -> m n (Type n)
getMethodType className i = do
  ClassDef _ _ bs _ methodTys <- lookupClassDef className
  let MethodType explicits methodTy = methodTys !! i
  return $ addParamBinders explicits bs methodTy
  where
    addParamBinders :: [Bool] -> Nest Binder n l -> Type l -> Type n
    addParamBinders [] Empty ty = ty
    addParamBinders (explicit:explicits) (Nest (b:>argTy) bs) ty =
      Pi $ PiType (PiBinder b argTy arr) Pure $ addParamBinders explicits bs ty
      where arr = if explicit then PlainArrow else ImplicitArrow
    addParamBinders _ _ _ = error "arg/binder mismatch"

typeCheckPrimHof :: Typer m => PrimHof (Atom i) -> m i o (Type o)
typeCheckPrimHof hof = addContext ("Checking HOF:\n" ++ pprint hof) case hof of
  For _ f -> do
    Pi (PiType (PiBinder b argTy PlainArrow) eff eltTy) <- getTypeE f
    eff' <- liftHoistExcept $ hoist b eff
    declareEffs eff'
    return $ TabTy (b:>argTy) eltTy
  Tile dim fT fS -> do
    (TC (IndexSlice n l), effT, tr) <- getTypeE fT >>= fromNonDepPiType PlainArrow
    (sTy                , effS, sr) <- getTypeE fS >>= fromNonDepPiType PlainArrow
    checkAlphaEq n sTy
    checkAlphaEq effT effS
    declareEffs effT
    (leadingIdxTysT, resultTyT) <- fromNaryNonDepTabType (replicate dim ()) tr
    (leadingIdxTysS, resultTyS) <- fromNaryNonDepTabType (replicate dim ()) sr
    (dvTy, resultTyT') <- fromNonDepTabType resultTyT
    checkAlphaEq l dvTy
    checkAlphaEq (ListE leadingIdxTysT) (ListE leadingIdxTysS)
    checkAlphaEq resultTyT' resultTyS
    naryNonDepTabPiType (leadingIdxTysT ++ [n]) resultTyT'
  PTileReduce baseMonoids n mapping -> do
    -- mapping : gtid:IdxRepTy -> nthr:IdxRepTy -> (...((ParIndexRange n gtid nthr)=>a, acc{n})..., acc1)
    ([_gtid, _nthr], Pure, mapResultTy) <-
      getTypeE mapping >>= fromNaryNonDepPiType [PlainArrow, PlainArrow]
    (tiledArrTy, accTys) <- fromLeftLeaningConsListTy (length baseMonoids) mapResultTy
    (_, tileElemTy) <- fromNonDepTabType tiledArrTy
    -- TOOD: figure out what's going on with threadRange
    --   let threadRange = TC $ ParIndexRange n (binderAsVar gtid) (binderAsVar nthr)
    --   checkAlphaEq threadRange threadRange'
    -- TODO: Check compatibility of baseMonoids and accTys (need to be careful about lifting!)
    -- PTileReduce n mapping : (n=>a, (acc1, ..., acc{n}))
    n' <- substM n
    tabTy <- n' ==> tileElemTy
    -- PTileReduce n mapping : (n=>a, (acc1, ..., acc{n}))
    return $ PairTy tabTy $ mkConsListTy accTys
  While body -> do
    Pi (PiType (PiBinder b UnitTy PlainArrow) eff condTy) <- getTypeE body
    PairE eff' condTy' <- liftHoistExcept $ hoist b $ PairE eff condTy
    declareEffs eff'
    checkAlphaEq (BaseTy $ Scalar Word8Type) condTy'
    return UnitTy
  Linearize f -> do
    Pi (PiType (PiBinder binder a PlainArrow) Pure b) <- getTypeE f
    b' <- liftHoistExcept $ hoist binder b
    fLinTy <- a --@ b'
    a --> PairTy b' fLinTy
  Transpose f -> do
    Pi (PiType (PiBinder binder a LinArrow) Pure b) <- getTypeE f
    b' <- liftHoistExcept $ hoist binder b
    b' --@ a
  RunReader r f -> do
    (resultTy, readTy) <- checkRWSAction Reader f
    r |: readTy
    return resultTy
  RunWriter _ f -> do
    -- XXX: We can't verify compatibility between the base monoid and f, because
    --      the only way in which they are related in the runAccum definition is via
    --      the AccumMonoid typeclass. The frontend constraints should be sufficient
    --      to ensure that only well typed programs are accepted, but it is a bit
    --      disappointing that we cannot verify that internally. We might want to consider
    --      e.g. only disabling this check for prelude.
    uncurry PairTy <$> checkRWSAction Writer f
  RunState s f -> do
    (resultTy, stateTy) <- checkRWSAction State f
    s |: stateTy
    return $ PairTy resultTy stateTy
  RunIO f -> do
    Pi (PiType (PiBinder b UnitTy PlainArrow) eff resultTy) <- getTypeE f
    PairE eff' resultTy' <- liftHoistExcept $ hoist b $ PairE eff resultTy
    extendAllowedEffect IOEffect $ declareEffs eff'
    return resultTy'
  CatchException f -> do
    Pi (PiType (PiBinder b UnitTy PlainArrow) eff resultTy) <- getTypeE f
    PairE eff' resultTy' <- liftHoistExcept $ hoist b $ PairE eff resultTy
    extendAllowedEffect ExceptionEffect $ declareEffs eff'
    return $ MaybeTy resultTy'

checkRWSAction :: Typer m => RWS -> Atom i -> m i o (Type o, Type o)
checkRWSAction rws f = do
  BinaryFunTy regionBinder refBinder eff resultTy <- getTypeE f
  allowed <- getAllowedEffects
  dropSubst $
    substBinders regionBinder \regionBinder' -> do
      substBinders refBinder \_ -> do
        allowed'   <- sinkM allowed
        eff'       <- substM eff
        regionName <- sinkM $ binderName regionBinder'
        withAllowedEffects allowed' $
          extendAllowedEffect (RWSEffect rws $ Just regionName) $
            declareEffs eff'
  PiBinder _ (RefTy _ referentTy) _ <- return refBinder
  referentTy' <- liftHoistExcept $ hoist regionBinder referentTy
  resultTy' <- liftHoistExcept $ hoist (PairB regionBinder refBinder) resultTy
  return (resultTy', referentTy')

-- Having this as a separate helper function helps with "'b0' is untouchable" errors
-- from GADT+monad type inference.
checkEmptyNest :: Fallible m => Nest b n l -> m ()
checkEmptyNest Empty = return ()
checkEmptyNest _  = throw TypeErr "Not empty"

nonDepBinderNestTypes :: Typer m => Nest Binder o o' -> m i o [Type o]
nonDepBinderNestTypes Empty = return []
nonDepBinderNestTypes (Nest (b:>ty) rest) = do
  Abs rest' UnitE <- liftHoistExcept $ hoist b $ Abs rest UnitE
  restTys <- nonDepBinderNestTypes rest'
  return $ ty : restTys

checkCase :: Typer m => HasType body
          => Atom i -> [AltP body i] -> Type i -> EffectRow i -> m i o (Type o)
checkCase scrut alts resultTy effs = do
  declareEffs =<< substM effs
  resultTy' <- substM resultTy
  scrutTy <- getTypeE scrut
  altsBinderTys <- caseAltsBinderTys scrutTy
  forMZipped_ alts altsBinderTys \alt bs ->
    checkAlt resultTy' bs alt
  return resultTy'

caseAltsBinderTys :: (Fallible1 m, EnvReader m)
                  => Type n -> m n [EmptyAbs (Nest Binder) n]
caseAltsBinderTys ty = case ty of
  TypeCon _ defName params -> do
    def <- lookupDataDef defName
    cons <- checkedApplyDataDefParams def params
    return [bs | DataConDef _ bs <- cons]
  VariantTy (NoExt types) -> do
    mapM typeAsBinderNest $ toList types
  VariantTy _ -> fail "Can't pattern-match partially-known variants"
  SumTy cases -> mapM typeAsBinderNest cases
  _ -> fail $ "Case analysis only supported on ADTs and variants, not on " ++ pprint ty

checkDataConRefEnv :: Typer m
                        => EmptyAbs (Nest Binder) o
                        -> EmptyAbs (Nest DataConRefBinding) i
                        -> m i o ()
checkDataConRefEnv (EmptyAbs Empty) (Abs Empty UnitE) = return ()
checkDataConRefEnv (EmptyAbs (Nest b restBs)) (EmptyAbs (Nest refBinding restRefs)) = do
  let DataConRefBinding b' ref = refBinding
  ref |: RawRefTy (binderAnn b)
  bAnn' <- substM $ binderAnn b'
  checkAlphaEq (binderAnn b) bAnn'
  checkB b' \b'' -> do
    ab <- sinkM $ Abs b (EmptyAbs restBs)
    restBs' <- applyAbs ab (binderName b'')
    checkDataConRefEnv restBs' (EmptyAbs restRefs)
checkDataConRefEnv _ _ = throw CompilerErr $ "Mismatched args and binders"

typeAsBinderNest :: ScopeReader m => Type n -> m n (Abs (Nest Binder) UnitE n)
typeAsBinderNest ty = do
  Abs ignored body <- toConstAbs UnitE
  return $ Abs (Nest (ignored:>ty) Empty) body

checkAlt :: HasType body => Typer m
         => Type o -> EmptyAbs (Nest Binder) o -> AltP body i -> m i o ()
checkAlt resultTyReq reqBs (Abs bs body) = do
  bs' <- substM (EmptyAbs bs)
  checkAlphaEq reqBs bs'
  substBinders bs \_ -> do
    resultTyReq' <- sinkM resultTyReq
    body |: resultTyReq'

checkApp :: Typer m => Type o -> [Atom i] -> m i o (Type o)
checkApp fTy [] = return fTy
checkApp fTy xs = case fromNaryPiType (length xs) fTy of
  Just (NaryPiType bs effs resultTy) -> do
    xs' <- mapM substM xs
    checkArgTys (nonEmptyToNest bs) xs'
    let subst = bs @@> fmap SubstVal xs'
    PairE effs' resultTy' <- applySubst subst $ PairE effs resultTy
    declareEffs effs'
    return resultTy'
  Nothing -> throw TypeErr $
    "Not a " ++ show (length xs) ++ "-argument pi type: " ++ pprint fTy
      ++ " (tried to apply it to: " ++ pprint xs ++ ")"

checkTabApp :: Typer m => Type o -> NonEmpty (Atom i) -> m i o (Type o)
checkTabApp tabTy xs = go tabTy $ toList xs
  where
    go :: Typer m => Type o -> [Atom i] -> m i o (Type o)
    go ty [] = return ty
    go ty (i:rest) = do
      TabTy (b:>ixTy) resultTy <- return ty
      i' <- checkTypeE ixTy i
      resultTy' <- applySubst (b@>SubstVal i') resultTy
      go resultTy' rest

numNaryPiArgs :: NaryPiType n -> Int
numNaryPiArgs (NaryPiType (NonEmptyNest _ bs) _ _) = 1 + nestLength bs

naryLamExprType :: EnvReader m => NaryLamExpr n -> m n (NaryPiType n)
naryLamExprType (NaryLamExpr (NonEmptyNest b bs) eff body) = liftHardFailTyperT do
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

checkNaryLamExpr :: Typer m => NaryLamExpr i -> NaryPiType o -> m i o ()
checkNaryLamExpr lam ty = naryLamExprAsAtom lam |: naryPiTypeAsType ty

asNaryPiType :: Type n -> Maybe (NaryPiType n)
asNaryPiType ty = case ty of
  Pi (PiType b effs resultTy) -> case effs of
   Pure -> case asNaryPiType resultTy of
     Just (NaryPiType (NonEmptyNest b' bs) effs' resultTy') ->
        Just $ NaryPiType (NonEmptyNest b (Nest b' bs)) effs' resultTy'
     Nothing -> Just $ NaryPiType (NonEmptyNest b Empty) Pure resultTy
   _ -> Just $ NaryPiType (NonEmptyNest b Empty) effs resultTy
  _ -> Nothing

checkArgTys
  :: (Typer m, SubstB AtomSubstVal b, BindsNames b, BindsOneAtomName b)
  => Nest b o o'
  -> [Atom o]
  -> m i o ()
checkArgTys Empty [] = return ()
checkArgTys (Nest b bs) (x:xs) = do
  dropSubst $ x |: binderType b
  Abs bs' UnitE <- applySubst (b@>SubstVal x) (EmptyAbs bs)
  checkArgTys bs' xs
checkArgTys _ _ = throw TypeErr $ "wrong number of args"
{-# INLINE checkArgTys #-}

typeCheckRef :: Typer m => HasType e => e i -> m i o (Type o)
typeCheckRef x = do
  TC (RefType _ a) <- getTypeE x
  return a

checkArrowAndEffects :: Fallible m => Arrow -> EffectRow n -> m ()
checkArrowAndEffects PlainArrow _ = return ()
checkArrowAndEffects _ Pure = return ()
checkArrowAndEffects _ _ = throw TypeErr $ "Only plain arrows may have effects"

checkIntBaseType :: Fallible m => Bool -> BaseType -> m ()
checkIntBaseType allowVector t = case t of
  Scalar sbt               -> checkSBT sbt
  Vector sbt | allowVector -> checkSBT sbt
  _ -> notInt
  where
    checkSBT sbt = case sbt of
      Int64Type -> return ()
      Int32Type -> return ()
      Word8Type  -> return ()
      Word32Type -> return ()
      Word64Type -> return ()
      _         -> notInt
    notInt = throw TypeErr $ "Expected a fixed-width " ++ (if allowVector then "" else "scalar ") ++
                             "integer type, but found: " ++ pprint t

checkFloatBaseType :: Fallible m => Bool -> BaseType -> m ()
checkFloatBaseType allowVector t = case t of
  Scalar sbt               -> checkSBT sbt
  Vector sbt | allowVector -> checkSBT sbt
  _ -> notFloat
  where
    checkSBT sbt = case sbt of
      Float64Type -> return ()
      Float32Type -> return ()
      _           -> notFloat
    notFloat = throw TypeErr $ "Expected a fixed-width " ++ (if allowVector then "" else "scalar ") ++
                               "floating-point type, but found: " ++ pprint t

checkValidCast :: Fallible1 m => Type n -> Type n -> m n ()
checkValidCast (TC (IntRange _ _)) IdxRepTy = return ()
checkValidCast IdxRepTy (TC (IntRange _ _)) = return ()
checkValidCast (TC (IndexRange _ _ _)) IdxRepTy = return ()
checkValidCast IdxRepTy (TC (IndexRange _ _ _)) = return ()
checkValidCast (BaseTy l) (BaseTy r) = checkValidBaseCast l r
checkValidCast sourceTy destTy =
  throw TypeErr $ "Can't cast " ++ pprint sourceTy ++ " to " ++ pprint destTy

checkValidBaseCast :: Fallible m => BaseType -> BaseType -> m ()
checkValidBaseCast (PtrType _) (PtrType _) = return ()
checkValidBaseCast (PtrType _) (Scalar Int64Type) = return ()
checkValidBaseCast (Scalar Int64Type) (PtrType _) = return ()
checkValidBaseCast sourceTy destTy =
  checkScalarType sourceTy >> checkScalarType destTy
  where
    checkScalarType ty = case ty of
      Scalar Int64Type   -> return ()
      Scalar Int32Type   -> return ()
      Scalar Word8Type   -> return ()
      Scalar Word32Type  -> return ()
      Scalar Word64Type  -> return ()
      Scalar Float64Type -> return ()
      Scalar Float32Type -> return ()
      _ -> throw TypeErr $ "Can't cast " ++ pprint sourceTy ++ " to " ++ pprint destTy

typeCheckBaseType :: Typer m => HasType e => e i -> m i o BaseType
typeCheckBaseType e =
  getTypeE e >>= \case
    TC (BaseType b) -> return b
    ty -> throw TypeErr $ "Expected a base type. Got: " ++ pprint ty

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
  VecLit  l -> Vector sb
    where Scalar sb = litType $ head l

data ArgumentType = SomeFloatArg | SomeIntArg | SomeUIntArg
data ReturnType   = SameReturn | Word8Return

checkOpArgType :: Fallible m => ArgumentType -> BaseType -> m ()
checkOpArgType argTy x =
  case argTy of
    SomeIntArg   -> checkIntBaseType   True x
    SomeUIntArg  -> assertEq x (Scalar Word8Type) ""
    SomeFloatArg -> checkFloatBaseType True x

checkBinOp :: Fallible m => BinOp -> BaseType -> BaseType -> m BaseType
checkBinOp op x y = do
  checkOpArgType argTy x
  assertEq x y ""
  return $ case retTy of
    SameReturn -> x
    Word8Return -> Scalar Word8Type
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
  return $ case retTy of
    SameReturn -> x
    Word8Return -> Scalar Word8Type
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
      FNeg             -> (f, sr)
      BNot             -> (u, sr)
      where
        u = SomeUIntArg; f = SomeFloatArg; sr = SameReturn

-- === singleton types ===

-- TODO: the following implementation should be valid:
--   isSingletonType :: EnvReader m => Type n -> m n Bool
--   isSingletonType ty =
--     singletonTypeVal ty >>= \case
--       Nothing -> return False
--       Just _  -> return True
-- But we want to be able to query the singleton-ness of types that we haven't
-- implemented tangent types for. So instead we do a separate case analysis.
isSingletonType :: EnvReader m => Type n -> m n Bool
isSingletonType topTy =
  case checkIsSingleton topTy of
    Just () -> return True
    Nothing -> return False
  where
    checkIsSingleton :: Type n -> Maybe ()
    checkIsSingleton ty = case ty of
      Pi (PiType _ _ body) -> checkIsSingleton body
      StaticRecordTy items -> mapM_ checkIsSingleton items
      TC con -> case con of
        ProdType tys -> mapM_ checkIsSingleton tys
        _ -> Nothing
      _ -> Nothing


singletonTypeVal :: EnvReader m => Type n -> m n (Maybe (Atom n))
singletonTypeVal ty = liftTyperT do
  singletonTypeVal' ty

-- TODO: TypeCon with a single case?
singletonTypeVal'
  :: (MonadFail2 m, SubstReader Name m, EnvReader2 m, EnvExtender2 m)
  => Type i -> m i o (Atom o)
singletonTypeVal' ty = case ty of
  TabPi (TabPiType b body) ->
    substBinders b \b' -> do
      body' <- singletonTypeVal' body
      return $ TabLam $ TabLamExpr b' $ AtomicBlock body'
  StaticRecordTy items -> Record <$> traverse singletonTypeVal' items
  TC con -> case con of
    ProdType tys -> ProdVal <$> traverse singletonTypeVal' tys
    _            -> notASingleton
  _ -> notASingleton
  where notASingleton = fail "not a singleton type"

-- === various helpers for querying types ===

getBaseMonoidType :: Fallible1 m => ScopeReader m => Type n -> m n (Type n)
getBaseMonoidType ty = case ty of
  Pi (PiType b _ resultTy) -> liftHoistExcept $ hoist b resultTy
  _     -> return ty

instantiateDataDef :: ScopeReader m => DataDef n -> [Type n] -> m n [DataConDef n]
instantiateDataDef (DataDef _ bs cons) params =
  fromListE <$> applyNaryAbs (Abs bs (ListE cons)) (map SubstVal params)

checkedApplyDataDefParams :: (EnvReader m, Fallible1 m) => DataDef n -> [Type n] -> m n [DataConDef n]
checkedApplyDataDefParams (DataDef _ bs cons) params =
  fromListE <$> checkedApplyNaryAbs (Abs bs (ListE cons)) params

checkedApplyClassParams
  :: (EnvReader m, Fallible1 m) => ClassDef n -> [Type n] -> m n ([Type n], [MethodType n])
checkedApplyClassParams (ClassDef _ _ bs superclassTys methodTys) params = do
  let body = PairE (ListE superclassTys) (ListE methodTys)
  body' <- checkedApplyNaryAbs (Abs bs body) params
  PairE (ListE superclassTys') (ListE methodTys') <- return body'
  return (superclassTys', methodTys')

-- TODO: Subst all at once, not one at a time!
checkedApplyNaryAbs :: (EnvReader m, Fallible1 m, SinkableE e, SubstE AtomSubstVal e)
                    => Abs (Nest Binder) e o -> [Atom o] -> m o (e o)
checkedApplyNaryAbs (Abs nest e) args = case (nest, args) of
  (Empty    , []) -> return e
  (Nest b@(_:>bTy) bs, x:t) -> do
    xTy <- getType x
    checkAlphaEq bTy xTy
    flip checkedApplyNaryAbs t =<< applyAbs (Abs b $ Abs bs e) (SubstVal x)
  (_        , _  ) -> throw CompilerErr $ "Length mismatch in checkedApplyNaryAbs"

-- === effects ===

instance CheckableE EffectRow where
  checkE effRow@(EffectRow effs effTail) = do
    forM_ effs \eff -> case eff of
      RWSEffect _ (Just v) -> Var v |: TyKind
      RWSEffect _ Nothing -> return ()
      ExceptionEffect -> return ()
      IOEffect        -> return ()
    forM_ effTail \v -> do
      v' <- substM v
      ty <- atomBindingType <$> lookupEnv v'
      checkAlphaEq EffKind ty
    substM effRow

declareEff :: Typer m => Effect o -> m i o ()
declareEff eff = declareEffs $ oneEffect eff

declareEffs :: Typer m => EffectRow o -> m i o ()
declareEffs effs = do
  allowed <- getAllowedEffects
  checkExtends allowed effs

extendAllowedEffect :: Typer m => Effect o -> m i o () -> m i o ()
extendAllowedEffect newEff cont = do
  effs <- getAllowedEffects
  withAllowedEffects (extendEffect newEff effs) cont

checkExtends :: Fallible m => EffectRow n -> EffectRow n -> m ()
checkExtends allowed (EffectRow effs effTail) = do
  let (EffectRow allowedEffs allowedEffTail) = allowed
  case effTail of
    Just _ -> assertEq allowedEffTail effTail ""
    Nothing -> return ()
  forM_ effs \eff -> unless (eff `elem` allowedEffs) $
    throw CompilerErr $ "Unexpected effect: " ++ pprint eff ++
                      "\nAllowed: " ++ pprint allowed

extendEffect :: Effect n -> EffectRow n -> EffectRow n
extendEffect eff (EffectRow effs t) = EffectRow (S.insert eff effs) t

oneEffect :: Effect n -> EffectRow n
oneEffect eff = EffectRow (S.singleton eff) Nothing

-- === labeled row types ===

checkFieldRowElems :: Typer m => FieldRowElems i -> m i o ()
checkFieldRowElems els = mapM_ checkElem elemList
  where
    elemList = fromFieldRowElems els
    checkElem = \case
      StaticFields items -> checkLabeledRow $ NoExt items
      DynField labVar ty -> do
        Var labVar |: TC LabelType
        ty |: TyKind
      DynFields row -> checkLabeledRow $ Ext mempty $ Just row

checkLabeledRow :: Typer m => ExtLabeledItems (Type i) (AtomName i) -> m i o ()
checkLabeledRow (Ext items rest) = do
  mapM_ (|: TyKind) items
  forM_ rest \name -> do
    name' <- lookupSubstM name
    ty <- atomBindingType <$> lookupEnv name'
    checkAlphaEq LabeledRowKind ty

labeledRowDifference :: Typer m
                     => ExtLabeledItems (Type o) (AtomName o)
                     -> ExtLabeledItems (Type o) (AtomName o)
                     -> m i o (ExtLabeledItems (Type o) (AtomName o))
labeledRowDifference (Ext (LabeledItems items) rest)
                     (Ext (LabeledItems subitems) subrest) = do
  -- Check types in the right.
  _ <- flip M.traverseWithKey subitems \label subtypes ->
    case M.lookup label items of
      Just types -> forMZipped_
          subtypes
          (NE.fromList $ NE.take (length subtypes) types)
          checkAlphaEq
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

projectLength :: (Fallible1 m, EnvReader m) => Type n -> m n Int
projectLength ty = case ty of
  TypeCon _ defName params -> do
    def <- lookupDataDef defName
    [DataConDef _ (Abs bs UnitE)] <- instantiateDataDef def params
    return $ nestLength bs
  StaticRecordTy types -> return $ length types
  ProdTy tys -> return $ length tys
  _ -> error $ "Projecting a type that doesn't support projecting: " ++ pprint ty

-- === "Data" type class ===

runCheck
  :: (EnvReader m, SinkableE e)
  => (forall l. DExt n l => TyperT Maybe l l (e l))
  -> m n (Maybe (e n))
runCheck cont = do
  Distinct <- getDistinct
  liftTyperT $ cont

asFFIFunType :: EnvReader m => Type n -> m n (Maybe (IFunType, NaryPiType n))
asFFIFunType ty = return do
  naryPiTy <- asNaryPiType ty
  impTy <- checkFFIFunTypeM naryPiTy
  return (impTy, naryPiTy)

checkFFIFunTypeM :: Fallible m => NaryPiType n -> m  IFunType
checkFFIFunTypeM (NaryPiType (NonEmptyNest b bs) eff resultTy) = do
  argTy <- checkScalar $ binderType b
  case bs of
    Empty -> do
      assertEq eff (oneEffect IOEffect) ""
      resultTys <- checkScalarOrPairType resultTy
      let cc = case length resultTys of
                 0 -> error "Not implemented"
                 1 -> FFIFun
                 _ -> FFIMultiResultFun
      return $ IFunType cc [argTy] resultTys
    Nest b' rest -> do
      let naryPiRest = NaryPiType (NonEmptyNest b' rest) eff resultTy
      IFunType cc argTys resultTys <- checkFFIFunTypeM naryPiRest
      return $ IFunType cc (argTy:argTys) resultTys

checkScalar :: Fallible m => Type n -> m BaseType
checkScalar (BaseTy ty) = return ty
checkScalar ty = throw TypeErr $ pprint ty

checkScalarOrPairType :: Fallible m => Type n -> m [BaseType]
checkScalarOrPairType (PairTy a b) = do
  tys1 <- checkScalarOrPairType a
  tys2 <- checkScalarOrPairType b
  return $ tys1 ++ tys2
checkScalarOrPairType (BaseTy ty) = return [ty]
checkScalarOrPairType ty = throw TypeErr $ pprint ty

-- TODO: consider effects
asFirstOrderFunction :: EnvReader m => Type n -> m n (Maybe (NaryPiType n))
asFirstOrderFunction ty = runCheck $ asFirstOrderFunctionM (sink ty)

asFirstOrderFunctionM :: Typer m => Type i -> m i o (NaryPiType o)
asFirstOrderFunctionM ty = case asNaryPiType ty of
  Nothing -> throw TypeErr "Not a monomorphic first-order function"
  Just naryPi@(NaryPiType bs eff resultTy) -> do
    substBinders bs \(NonEmptyNest b' bs') -> do
      ts <- mapM sinkM $ bindersTypes $ Nest b' bs'
      dropSubst $ mapM_ checkDataLike ts
      Pure <- return eff
      checkDataLike resultTy
    substM naryPi

isData :: EnvReader m => Type n -> m n Bool
isData ty = liftM isJust $ runCheck do
  checkDataLike (sink ty)
  return UnitE

checkDataLike :: Typer m => Type i -> m i o ()
checkDataLike ty = case ty of
  Var _ -> error "Not implemented"
  TabPi (TabPiType b eltTy) -> do
    substBinders b \_ ->
      checkDataLike eltTy
  StaticRecordTy items -> mapM_ recur items
  VariantTy (NoExt items) -> mapM_ recur items
  DepPairTy (DepPairType b@(_:>l) r) -> do
    recur l
    substBinders b \_ -> checkDataLike r
  TypeCon _ defName params -> do
    params' <- mapM substM params
    def <- lookupDataDef =<< substM defName
    dataCons <- instantiateDataDef def params'
    dropSubst $ forM_ dataCons \(DataConDef _ bs) ->
      checkDataLikeBinderNest bs
  TC con -> case con of
    BaseType _       -> return ()
    ProdType as      -> mapM_ recur as
    SumType  cs      -> mapM_ recur cs
    IntRange _ _     -> return ()
    IndexRange _ _ _ -> return ()
    IndexSlice _ _   -> return ()
    _ -> throw TypeErr $ pprint ty
  _   -> throw TypeErr $ pprint ty
  where recur = checkDataLike

checkDataLikeBinderNest :: Typer m => EmptyAbs (Nest Binder) i -> m i o ()
checkDataLikeBinderNest (Abs Empty UnitE) = return ()
checkDataLikeBinderNest (Abs (Nest b rest) UnitE) = do
  checkDataLike $ binderType b
  substBinders b \_ -> checkDataLikeBinderNest $ Abs rest UnitE
