-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

module Type (
  HasType (..), CheckableE (..), CheckableB (..),
  checkModule, checkTypes, checkTypesM,
  getType, getTypeSubst, litType, getBaseMonoidType,
  instantiatePi, instantiateDepPairTy,
  checkExtends, checkedApplyDataDefParams, indices,
  instantiateDataDef,
  caseAltsBinderTys, tryGetType, projectLength,
  sourceNameType, substEvaluatedModuleM,
  checkUnOp, checkBinOp,
  oneEffect, lamExprTy, isData, isSingletonType, singletonTypeVal,
  extendEffect, exprEffects, getReferentTy) where

import Prelude hiding (id)
import Control.Category ((>>>), id)
import Control.Monad
import Control.Monad.Reader
import Data.Foldable (toList)
import Data.Functor
import Data.Int
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import qualified Data.Set        as S

import LabeledItems

import Err
import Util (forMZipped, forMZipped_, iota, scan, restructure)

import Syntax
import Name
import PPrint ()

-- === top-level API ===

checkModule :: (Distinct n, Fallible m) => Env n -> Module n -> m ()
checkModule bindings m =
  addContext ("Checking module:\n" ++ pprint m) $ asCompilerErr $
    runEnvReaderT bindings $
      checkTypesM m

checkTypes :: (EnvReader m, CheckableE e) => e n -> m n (Except ())
checkTypes e = fromLiftE <$> liftImmut do
  DB bindings <- getDB
  return $ LiftE $ runTyperT bindings $ void $ checkE e

checkTypesM :: (EnvReader m, Fallible1 m, CheckableE e)
           => e n -> m n ()
checkTypesM e = liftExcept =<< checkTypes e

getType :: (EnvReader m, HasType e)
           => e n -> m n (Type n)
getType e = liftImmut do
  DB bindings <- getDB
  return $ runHardFail $ runTyperT bindings $ getTypeE e

getTypeSubst :: (SubstReader Name m, EnvReader2 m, HasType e)
             => e i -> m i o (Type o)
getTypeSubst e = liftImmut do
  DB bindings <- getDB
  subst <- getSubst
  return $ runHardFail $
    runEnvReaderT bindings $
      runSubstReaderT subst $
        runTyperT' $ getTypeE e

tryGetType :: (EnvReader m, Fallible1 m, HasType e) => e n -> m n (Type n)
tryGetType e = liftImmut do
  DB bindings <- getDB
  liftExcept $ runTyperT bindings $ getTypeE e

depPairLeftTy :: DepPairType n -> Type n
depPairLeftTy (DepPairType (_:>ty) _) = ty

instantiateDepPairTy :: ScopeReader m => DepPairType n -> Atom n -> m n (Type n)
instantiateDepPairTy (DepPairType b rhsTy) x = applyAbs (Abs b rhsTy) (SubstVal x)

instantiatePi :: ScopeReader m => PiType n -> Atom n -> m n (EffectRow n, Type n)
instantiatePi (PiType b eff body) x = do
  PairE eff' body' <- applyAbs (Abs b (PairE eff body)) (SubstVal x)
  return (eff', body')

sourceNameType :: (EnvReader m, Fallible1 m)
               => SourceName -> m n (Type n)
sourceNameType v = do
  sm <- getSourceMapM
  case M.lookup v $ fromSourceMap sm of
    Nothing -> throw UnboundVarErr $ pprint v
    Just (WithColor c v') ->
      withNameColorRep c $ lookupEnv v' >>= bindingType

  where
    bindingType :: (NameColor c, EnvReader m, Fallible1 m)
                => Binding c n -> m n (Type n)
    bindingType binding = liftImmut case binding of
      AtomNameBinding b    -> return $ atomBindingType $ toBinding b
      TyConBinding   _   e -> getType e
      DataConBinding _ _ e -> getType e
      MethodBinding  _ _ e -> getType e
      ClassBinding   _   e -> getType e
      _ -> throw TypeErr $ pprint v  ++ " doesn't have a type"

getReferentTy :: MonadFail m => EmptyAbs (PairB LamBinder LamBinder) n -> m (Type n)
getReferentTy (Abs (PairB hB refB) UnitE) = do
  RefTy _ ty <- return $ binderType refB
  HoistSuccess ty' <- return $ hoist hB ty
  return ty'

-- === querying effects ===

exprEffects :: (MonadFail1 m, EnvReader m) => Expr n -> m n (EffectRow n)
exprEffects expr = case expr of
  Atom _  -> return $ Pure
  App f _ -> functionEffs f
  Op op   -> case op of
    PrimEffect ref m -> do
      RefTy (Var h) _ <- getType ref
      return $ case m of
        MGet      -> oneEffect (RWSEffect State  $ Just h)
        MPut    _ -> oneEffect (RWSEffect State  $ Just h)
        MAsk      -> oneEffect (RWSEffect Reader $ Just h)
        -- XXX: We don't verify the base monoid. See note about RunWriter.
        MExtend _ _ -> oneEffect (RWSEffect Writer $ Just h)
    ThrowException _ -> return $ oneEffect ExceptionEffect
    IOAlloc  _ _  -> return $ oneEffect IOEffect
    IOFree   _    -> return $ oneEffect IOEffect
    PtrLoad  _    -> return $ oneEffect IOEffect
    PtrStore _ _  -> return $ oneEffect IOEffect
    FFICall _ _ _ -> return $ oneEffect IOEffect
    _ -> return Pure
  Hof hof -> case hof of
    For _ f         -> functionEffs f
    Tile _ _ _      -> error "not implemented"
    While body      -> functionEffs body
    Linearize _     -> return Pure  -- Body has to be a pure function
    Transpose _     -> return Pure  -- Body has to be a pure function
    RunWriter _ f -> rwsFunEffects Writer f
    RunReader _ f -> rwsFunEffects Reader f
    RunState  _ f -> rwsFunEffects State  f
    _ -> error $ "not implemented:" ++ pprint expr
  Case _ _ _ effs -> return effs

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
      , EnvReader2 m, EnvExtender2 m, AlwaysImmut2 m)
     => Typer (m::MonadKind2)

newtype TyperT (m::MonadKind) (i::S) (o::S) (a :: *) =
  TyperT { runTyperT' :: SubstReaderT Name (EnvReaderT m) i o a }
  deriving ( Functor, Applicative, Monad
           , SubstReader Name
           , MonadFail
           , Fallible
           , AlwaysImmut
           , ScopeReader
           , EnvReader, EnvExtender)

runTyperT :: (Fallible m, Distinct n)
          => Env n -> TyperT m n n a -> m a
runTyperT bindings m = do
  runEnvReaderT bindings $
    runSubstReaderT idSubst $
      runTyperT' m

instance Fallible m => Typer (TyperT m)

-- === typeable things ===

-- Minimal complete definition: getTypeE | getTypeAndSubstE
-- (Usually we just implement `getTypeE` but for big things like blocks it can
-- be worth implementing the specialized versions too, as optimizations.)
class (SinkableE e, SubstE Name e) => HasType (e::E) where
  getTypeE   :: Typer m => e i -> m i o (Type o)
  getTypeE e = snd <$> getTypeAndSubstE e

  getTypeAndSubstE :: Typer m => e i -> m i o (e o, Type o)
  getTypeAndSubstE e = (,) <$> substM e <*> getTypeE e

  checkTypeE :: Typer m => Type o -> e i -> m i o (e o)
  checkTypeE reqTy e = do
    (e', ty) <- getTypeAndSubstE e
    checkAlphaEq reqTy ty
    return e'

class (SinkableE e, SubstE Name e) => CheckableE (e::E) where
  checkE :: Typer m => e i -> m i o (e o)

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

-- === Module interfaces ===

instance CheckableE Module where
  checkE (Module ir decls evaluated) = do
    -- TODO: need to add back the IR check. Should we just do it alongside type checking
    -- instead of as a separate pass?
    -- addContext "Checking IR variant" $ checkModuleVariant m
    addContext "Checking module body" $
      checkB decls \decls' -> do
        addContext "Checking module result" do
          evaluated' <- checkE evaluated
          return $ Module ir decls' evaluated'

instance CheckableE EvaluatedModule where
  checkE (Abs (TopEnvFrag bindings scs sourceMap) UnitE) =
    checkB bindings \bindings' -> do
      sourceMap' <- checkE sourceMap
      scs'       <- checkE scs
      return $ Abs (TopEnvFrag bindings' scs' sourceMap') UnitE

instance CheckableE SourceMap where
  checkE sourceMap = substM sourceMap

instance CheckableE SynthCandidates where
  checkE (SynthCandidates xs ys zs) = undefined
    SynthCandidates <$> mapM checkE xs
                    <*> mapM checkE ys
                    <*> (M.fromList <$> forM (M.toList zs) \(k, vs) ->
                          (,) <$> substM k <*> mapM checkE vs)

instance CheckableB (RecSubstFrag Binding) where
  checkB frag cont = do
    Immut <- getImmut
    scope <- getScope
    env <- getSubst
    Distinct <- getDistinct
    DistinctAbs frag' env' <- return $ refreshRecSubstFrag scope env frag
    extendEnv (EnvFrag frag' Nothing) do
      void $ dropSubst $ traverseSubstFrag checkE $ fromRecSubstFrag frag'
      withSubst env' do
        cont frag'

instance CheckableB EnvFrag where
  checkB (EnvFrag frag effs) cont = do
    checkB frag \frag' -> do
      effs' <- mapM checkE effs
      cont $ EnvFrag frag' effs'

instance NameColor c => CheckableE (Binding c) where
  checkE binding = case binding of
    AtomNameBinding   atomNameBinding   -> AtomNameBinding <$> checkE atomNameBinding
    DataDefBinding    dataDef           -> DataDefBinding  <$> checkE dataDef
    TyConBinding      dataDefName     e -> TyConBinding    <$> substM dataDefName              <*> substM e
    DataConBinding    dataDefName idx e -> DataConBinding  <$> substM dataDefName <*> pure idx <*> substM e
    ClassBinding      classDef        e -> ClassBinding    <$> substM classDef                 <*> substM e
    SuperclassBinding className   idx e -> SuperclassBinding <$> substM className <*> pure idx <*> substM e
    MethodBinding     className   idx e -> MethodBinding     <$> substM className <*> pure idx <*> substM e

instance CheckableE AtomBinding where
  checkE binding = case binding of
    LetBound letBinding -> LetBound    <$> checkE letBinding
    LamBound lamBinding -> LamBound    <$> checkE lamBinding
    PiBound  piBinding  -> PiBound     <$> checkE piBinding
    MiscBound ty        -> MiscBound   <$> checkTypeE TyKind ty
    SolverBound b       -> SolverBound <$> checkE b
    PtrLitBound ty ptr  -> return $ PtrLitBound ty ptr

instance CheckableE SolverBinding where
  checkE (InfVarBound  ty ctx) = InfVarBound  <$> checkTypeE TyKind ty <*> pure ctx
  checkE (SkolemBound  ty    ) = SkolemBound  <$> checkTypeE TyKind ty

instance CheckableE DataDef where
  checkE = substM -- TODO

-- === type checking core ===

instance CheckableE Atom where
  checkE atom = fst <$> getTypeAndSubstE atom

instance CheckableE Expr where
  checkE expr = fst <$> getTypeAndSubstE expr

instance HasType AtomName where
  getTypeE name = do
    name' <- substM name
    atomBindingType <$> lookupEnv name'

instance HasType Atom where
  getTypeE atom = liftImmut $ case atom of
    Var name -> getTypeE name
    Lam lamExpr -> getTypeE lamExpr
    Pi piType -> getTypeE piType
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
    LabeledRow row -> checkLabeledRow row $> LabeledRowKind
    Record items -> do
      types <- mapM getTypeE items
      return $ RecordTy (NoExt types)
    RecordTy row -> checkLabeledRow row $> TyKind
    Variant vtys@(Ext (LabeledItems types) _) label i arg -> do
      let ty = VariantTy vtys
      let argTy = do
            labelTys <- M.lookup label types
            guard $ i < length labelTys
            return $ labelTys NE.!! i
      case argTy of
        Just argType -> do
          argType' <- substM argType
          arg |: argType'
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
      withFreshBinders (zip (repeat NoHint) ptrTys) \bs' vs -> do
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
        RecordTy (NoExt types) -> return $ toList types !! i
        RecordTy _ -> throw CompilerErr "Can't project partially-known records"
        ProdTy xs -> return $ xs !! i
        DepPairTy t | i == 0 -> return $ depPairLeftTy t
        DepPairTy t | i == 1 -> do v' <- substM v
                                   instantiateDepPairTy t (ProjectElt (0 NE.:| is) v')
        Var _ -> throw CompilerErr $ "Tried to project value of unreduced type " <> pprint ty
        _ -> throw TypeErr $
              "Only single-member ADTs and record types can be projected. Got " <> pprint ty <> "   " <> pprint v

instance (NameColor c, ToBinding ann c, CheckableE ann)
         => CheckableB (BinderP c ann) where
  checkB (b:>ann) cont = do
    ann' <- checkE ann
    Immut <- getImmut
    withFreshBinder (getNameHint b) (toBinding ann') \b' ->
      extendRenamer (b@>binderName b') $
        cont $ b' :> ann'

instance HasType Expr where
  getTypeE expr = case expr of
    App f x -> do
      fTy <- getTypeE f
      checkApp fTy x
    Atom x   -> getTypeE x
    Op   op  -> typeCheckPrimOp op
    Hof  hof -> typeCheckPrimHof hof
    Case e alts resultTy effs -> checkCase e alts resultTy effs

instance HasType Block where
  getTypeE (Block NoBlockAnn Empty expr) = do
    getTypeE expr
  getTypeE (Block (BlockAnn ty) decls expr) = do
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
    Immut <- getImmut
    withFreshBinder (getNameHint b) binding \b' -> do
      extendRenamer (b@>binderName b') do
        effs' <- checkE effs
        extendEnv (EnvFrag emptyOutFrag (Just effs')) $
          cont $ LamBinder b' ty' arr effs'

instance HasType LamExpr where
  getTypeE (LamExpr b body) = do
    checkB b \b' -> do
      bodyTy <- getTypeE body
      return $ lamExprTy b' bodyTy

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

instance CheckableB PiBinder where
  checkB (PiBinder b ty arr) cont = do
    ty' <- checkTypeE TyKind ty
    let binding = toBinding $ PiBinding arr ty'
    Immut <- getImmut
    withFreshBinder (getNameHint b) binding \b' -> do
      extendRenamer (b@>binderName b') do
        extendEnv (EnvFrag emptyOutFrag (Just Pure)) $
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
  ClassDictHole _ ty  -> ty |:TyKind   >> substM ty
  IntRangeVal     l h i -> i|:IdxRepTy >> substM (TC $ IntRange     l h)
  IndexRangeVal t l h i -> i|:IdxRepTy >> substM (TC $ IndexRange t l h)
  IndexSliceVal _ _ _ -> error "not implemented"
  BaseTypeRef p -> do
    (PtrTy (_, b)) <- getTypeE p
    return $ RawRefTy $ BaseTy b
  TabRef tabTy -> do
    Pi (PiType binder Pure (RawRefTy a)) <- getTypeE tabTy
    PiBinder _ _ TabArrow <- return binder
    return $ RawRefTy $ Pi $ PiType binder Pure a
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
  RecordRef xs -> (RawRefTy . RecordTy . NoExt) <$> traverse typeCheckRef xs

typeCheckPrimOp :: Typer m => PrimOp (Atom i) -> m i o (Type o)
typeCheckPrimOp op = case op of
  TabCon ty xs -> do
    ty'@(TabTyAbs piTy) <- checkTypeE TyKind ty
    idxs <- indices $ piArgType piTy
    forMZipped_ xs idxs \x i -> do
      (_, eltTy) <- instantiatePi piTy i
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
  FFICall _ ansTy args -> do
    forM_ args \arg -> do
      argTy <- getTypeE arg
      case argTy of
        BaseTy _ -> return ()
        _        -> throw TypeErr $ "All arguments of FFI calls have to be " ++
                                    "fixed-width base types, but got: " ++ pprint argTy
    declareEff IOEffect
    substM ansTy
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
    RefTy h (Pi (PiType (PiBinder b iTy TabArrow) Pure eltTy)) <- getTypeE ref
    i' <- checkTypeE iTy i
    eltTy' <- applyAbs (Abs b eltTy) (SubstVal i')
    return $ RefTy h eltTy'
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
    sourceTy <- typeCheckBaseType e
    destTy  |: TyKind
    (TC (BaseType destTy')) <- substM destTy
    checkValidCast sourceTy destTy'
    return $ TC $ BaseType $ destTy'
  RecordCons items record -> do
    types <- mapM getTypeE items
    rty <- getTypeE record
    rest <- case rty of
      RecordTy rest -> return rest
      _ -> throw TypeErr $ "Can't add fields to a non-record object "
                        <> pprint record <> " (of type " <> pprint rty <> ")"
    return $ RecordTy $ prefixExtLabeledItems types rest
  RecordSplit types record -> do
    mapM_ (|: TyKind) types
    types' <- mapM substM types
    fullty <- getTypeE record
    full <- case fullty of
      RecordTy full -> return full
      _ -> throw TypeErr $ "Can't split a non-record object " <> pprint record
                        <> " (of type " <> pprint fullty <> ")"
    diff <- labeledRowDifference full (NoExt types')
    return $ RecordTy $ NoExt $
      Unlabeled [ RecordTy $ NoExt types', RecordTy diff ]
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
    TypeCon sourceName dataDefName [] <- checkTypeE TyKind t
    DataDef _ _ dataConDefs <- lookupDataDef dataDefName
    forM_ dataConDefs \(DataConDef _ (Abs binders _)) -> checkEmptyNest binders
    return $ TypeCon sourceName dataDefName []
  SumToVariant x -> do
    SumTy cases <- getTypeE x
    return $ VariantTy $ NoExt $ foldMap (labeledSingleton "c") cases
  OutputStreamPtr ->
    return $ BaseTy $ hostPtrTy $ hostPtrTy $ Scalar Word8Type
    where hostPtrTy ty = PtrType (Heap CPU, ty)
  SynthesizeDict _ ty -> checkTypeE TyKind ty

typeCheckPrimHof :: Typer m => PrimHof (Atom i) -> m i o (Type o)
typeCheckPrimHof hof = addContext ("Checking HOF:\n" ++ pprint hof) case hof of
  For _ f -> do
    Pi (PiType (PiBinder b argTy PlainArrow) eff eltTy) <- getTypeE f
    eff' <- liftHoistExcept $ hoist b eff
    declareEffs eff'
    return $ Pi $ PiType (PiBinder b argTy TabArrow) Pure eltTy
  Tile dim fT fS -> do
    (TC (IndexSlice n l), effT, tr) <- getTypeE fT >>= fromNonDepPiType PlainArrow
    (sTy                , effS, sr) <- getTypeE fS >>= fromNonDepPiType PlainArrow
    checkAlphaEq n sTy
    checkAlphaEq effT effS
    declareEffs effT
    (leadingIdxTysT, Pure, resultTyT) <- fromNaryNonDepPiType (replicate dim TabArrow) tr
    (leadingIdxTysS, Pure, resultTyS) <- fromNaryNonDepPiType (replicate dim TabArrow) sr
    (dvTy, Pure, resultTyT') <- fromNonDepPiType TabArrow resultTyT
    checkAlphaEq l dvTy
    checkAlphaEq (ListE leadingIdxTysT) (ListE leadingIdxTysS)
    checkAlphaEq resultTyT' resultTyS
    naryNonDepPiType TabArrow Pure (leadingIdxTysT ++ [n]) resultTyT'
  PTileReduce baseMonoids n mapping -> do
    -- mapping : gtid:IdxRepTy -> nthr:IdxRepTy -> (...((ParIndexRange n gtid nthr)=>a, acc{n})..., acc1)
    ([_gtid, _nthr], Pure, mapResultTy) <-
      getTypeE mapping >>= fromNaryNonDepPiType [PlainArrow, PlainArrow]
    (tiledArrTy, accTys) <- fromLeftLeaningConsListTy (length baseMonoids) mapResultTy
    (_, tileElemTy) <- fromNonDepTabTy tiledArrTy
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
    substBindersI regionBinder \regionBinder' -> do
      substBindersI refBinder \_ -> do
        allowed'   <- sinkM allowed
        eff'       <- substM eff
        regionName <- sinkM $ binderName regionBinder'
        Immut <- getImmut
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
  Abs ignored body <- toConstAbs AtomNameRep UnitE
  return $ Abs (Nest (ignored:>ty) Empty) body

checkAlt :: HasType body => Typer m
         => Type o -> EmptyAbs (Nest Binder) o -> AltP body i -> m i o ()
checkAlt resultTyReq reqBs (Abs bs body) = do
  bs' <- substM (EmptyAbs bs)
  checkAlphaEq reqBs bs'
  substBindersI bs \_ -> do
    resultTyReq' <- sinkM resultTyReq
    body |: resultTyReq'

checkApp :: Typer m => Type o -> Atom i -> m i o (Type o)
checkApp fTy x = do
  Pi (PiType (PiBinder b argTy _) eff resultTy) <- return fTy
  x' <- checkTypeE argTy x
  PairE eff' resultTy' <- applyAbs (Abs b (PairE eff resultTy)) (SubstVal x')
  declareEffs eff'
  return resultTy'

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

checkValidCast :: Fallible m => BaseType -> BaseType -> m ()
checkValidCast (PtrType _) (PtrType _) = return ()
checkValidCast (PtrType _) (Scalar Int64Type) = return ()
checkValidCast (Scalar Int64Type) (PtrType _) = return ()
checkValidCast sourceTy destTy =
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
  PtrLit t _   -> PtrType t
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
      RecordTy (NoExt items) -> mapM_ checkIsSingleton items
      TC con -> case con of
        ProdType tys -> mapM_ checkIsSingleton tys
        _ -> Nothing
      _ -> Nothing


singletonTypeVal :: EnvReader m => Type n -> m n (Maybe (Atom n))
singletonTypeVal ty = fromMaybeE <$> liftImmut do
  DB env <- getDB
  return $ toMaybeE $ runEnvReaderT env $ runSubstReaderT idSubst $
    singletonTypeVal' ty

-- TODO: TypeCon with a single case?
singletonTypeVal'
  :: (Immut o, MonadFail2 m, SubstReader Name m, EnvReader2 m, EnvExtender2 m)
  => Type i -> m i o (Atom o)
singletonTypeVal' ty = case ty of
  Pi (PiType b@(PiBinder _ _ TabArrow) Pure body) ->
    substBinders b \b' -> do
      body' <- singletonTypeVal' body
      return $ Pi $ PiType b' Pure body'
  RecordTy (NoExt items) -> Record <$> traverse singletonTypeVal' items
  TC con -> case con of
    ProdType tys -> ProdVal <$> traverse singletonTypeVal' tys
    _            -> notASingleton
  _ -> notASingleton
  where notASingleton = fail "not a singleton type"

-- === built-in index set type class ===

-- These only work for index set types without free variables. It's redundant
-- with the more general index set classs in Builder but this way we avoid the
-- dependency cycle. And we intend to make index sets a user-defined thing soon
-- anyway. One solution might be to define a monad class, a subset of Builder,
-- that can be instantiated with both an interpreter and a builder.

indices :: forall n m. EnvReader m => Type n -> m n [Atom n]
indices ty = do
  Distinct <- getDistinct
  withExtEvidence (absurdExtEvidence :: ExtEvidence VoidS n) do
    case hoistToTop ty of
      HoistSuccess ty' ->
        return $ map (sink . litFromOrdinal ty') [0 .. litIdxSetSize ty' - 1]
      HoistFailure _ -> error "can't get index literals from type with free vars"

litIdxSetSize :: Type VoidS -> Int32
litIdxSetSize ty = case ty of
  TC (IntRange (IdxRepVal low) (IdxRepVal high)) ->
    fromIntegral $ high - low
  TC (IndexRange n low high) -> high' - low'
    where
      low' = case low of
        InclusiveLim x -> litToOrdinal x
        ExclusiveLim x -> litToOrdinal x + 1
        Unlimited      -> 0
      high' = case high of
        InclusiveLim x -> litToOrdinal x + 1
        ExclusiveLim x -> litToOrdinal x
        Unlimited      -> litIdxSetSize n
  TC (ProdType types)     -> product $ fmap litIdxSetSize types
  RecordTy (NoExt types)  -> product $ fmap litIdxSetSize types
  SumTy types             -> sum $ fmap litIdxSetSize types
  VariantTy (NoExt types) -> sum $ fmap litIdxSetSize types
  _ -> error $ "Not an (implemented) index set: " ++ pprint ty

data IterOrder = MinorToMajor | MajorToMinor

litToOrdinal :: Atom VoidS -> Int32
litToOrdinal idx = case idx of
  Con (IntRangeVal   _ _   (IdxRepVal i)) -> i
  Con (IndexRangeVal _ _ _ (IdxRepVal i)) -> i
  ProdTy           types  -> prodToInt MajorToMinor types
  RecordTy  (NoExt types) -> prodToInt MinorToMajor types
  Con (SumCon _ _ _) -> error "not implemented"
  Variant (NoExt tys) _ _ _ -> sumToInt tys
  _ -> error $ "Not an (implemented) index: " ++ pprint idx
  where
    prodToInt :: Traversable t => IterOrder -> t (Type VoidS) -> Int32
    prodToInt order types = do
      let sizes = toList $ fmap litIdxSetSize types
      let rev = case order of MinorToMajor -> id; MajorToMinor -> reverse
      let strides = rev $ fst $ scan (\sz prev -> (prev,) $ sz * prev) (rev sizes) 1
      -- Unpack and sum the strided contributions
      let subints = fmap litToOrdinal $ getUnpackedLitProd idx
      let scaled = map (uncurry (*)) $ zip strides subints
      sum scaled

    sumToInt :: Traversable t => t (Type VoidS) -> Int32
    sumToInt types = do
      let sizes = map litIdxSetSize $ toList types
      let offsets = fst $ scan (\sz prev -> (prev,) $ sz + prev) sizes 0
      case trySelectBranch idx of
        Nothing -> error "we're working with literals, so we should know the branch"
        Just (i, [subix]) -> offsets !! i + litToOrdinal subix
        Just _ -> error "expected a unary alt"

    getUnpackedLitProd :: Atom VoidS -> [Atom VoidS]
    getUnpackedLitProd prod = case prod of
      Record xs -> toList xs
      Con (ProdCon xs) -> xs
      _ -> error "expected a record or product type"

litFromOrdinal :: Type VoidS -> Int32 -> Atom VoidS
litFromOrdinal ty i = case ty of
  TC (IntRange low high) -> Con $ IntRangeVal low high $ IdxRepVal i
  TC (IndexRange n low high) -> Con $ IndexRangeVal n low high (IdxRepVal i)
  TC (ProdType types)    -> ProdVal $ reverse $ intToProd types
  RecordTy (NoExt types) -> Record $ intToProd types
  SumTy types             -> intToSum types [0..] $ SumVal ty
  VariantTy (NoExt types) -> intToSum types (reflectLabels types) $ uncurry $ Variant (NoExt types)
  _ -> error $ "Not an (implemented) index set: " ++ pprint ty
  where
    -- XXX: Expects that the types are in a minor-to-major order
    intToProd :: Traversable t => t (Type VoidS) -> t (Atom VoidS)
    intToProd types = do
      let sizes = fmap litIdxSetSize types
      let strides = fst $ scan (\sz prev -> let v = sz * prev in ((prev, v), v)) sizes 1
      let offsets = flip map (zip (toList types) (toList strides)) $
            \(ety, (s1, s2)) -> do
              let x = rem i s2
              let y = div x s1
              litFromOrdinal ety y
      restructure offsets types

    intToSum :: Traversable t => t (Type VoidS) -> t l -> (l -> Atom VoidS -> Atom VoidS) -> Atom VoidS
    intToSum types labels mkSum = do
      let sizes = fmap litIdxSetSize types
      let offsets = fst $ scan (\sz prev -> (prev,) $ sz + prev) sizes 0
      let
        -- Find the right index by looping through the possible offsets
        go prev (label, cty, offset) = do
          let shifted = i - offset
          -- TODO: This might run intToIndex on negative indices. Fix this!
          let index = litFromOrdinal cty shifted
          if i < offset
            then prev
            else mkSum label index
        (l, ty0, _):zs = zip3 (toList labels) (toList types) (toList offsets)
      let start = mkSum l $ litFromOrdinal ty0 i
      foldl go start zs

-- === substituting evaluated modules ===

-- A module's source map is a name-to-name mapping, so we can't replace the rhs
-- names with atoms. Instead, we create new bindings for the atoms we want to
-- substitute with, and then substitute with the names of those bindings in the
-- source map.
-- Unfortunately we can't make this the `SubstE AtomSubstVal` instance for
-- `EvaluatedModule` because we need the bindings (to query types), whereas
-- `substE` only gives us scopes.

substEvaluatedModuleM
  :: (SubstReader AtomSubstVal m, EnvReader2 m)
  => EvaluatedModule i
  -> m i o (EvaluatedModule o)
substEvaluatedModuleM m = liftImmut do
  Abs (TopEnvFrag (EnvFrag bs eff) sc sm) UnitE <- return m
  env <- getSubst
  DB bindings <- getDB
  let body = toMaybeE eff `PairE` sc `PairE` sm
  Abs bs' body' <- return $ atomSubstAbsEnvFrag bindings env $ Abs bs body
  eff' `PairE` sc' `PairE` sm' <- return body'
  return $ EmptyAbs (TopEnvFrag (EnvFrag bs' (fromMaybeE eff')) sc' sm')

atomSubstAbsEnvFrag
  :: (Distinct o, SinkableE e, SubstE Name e, HoistableE e)
  => Env o
  -> Subst AtomSubstVal i o
  -> Abs (RecSubstFrag Binding) e i
  -> Abs (RecSubstFrag Binding) e o
atomSubstAbsEnvFrag bindings env (Abs b e) =
  substB (toScope bindings, env) b \(scope', env') b' ->
    case substAnything scope' env' e of
      DistinctAbs bNew e' -> do
        let bindings' = extendOutMap bindings b'
        let bOut = catRecSubstFrags b' (atomNestToEnvFrag bindings' bNew)
        Abs bOut e'

atomNestToEnvFrag
  :: Distinct o'
  => Env o
  -> Nest (BinderP AtomNameC Atom) o o'
  -> RecSubstFrag Binding o o'
atomNestToEnvFrag _ Empty = emptyOutFrag
atomNestToEnvFrag bindings (Nest (b:>x) rest) =
  withSubscopeDistinct rest $
    withSubscopeDistinct b do
      let (EnvFrag frag _) = toEnvFrag (b :> atomToBinding bindings x)
      let frag' = atomNestToEnvFrag (bindings `extendOutMap` frag) rest
      catRecSubstFrags frag frag'

atomToBinding :: Distinct n => Env n -> Atom n -> Binding AtomNameC n
atomToBinding bindings x = do
  let ty = runEnvReaderM bindings $ getType x
  AtomNameBinding $ LetBound $ DeclBinding PlainLet ty (Atom x)

substAnything
  :: ( Distinct o, SinkableE atom
     , SinkableE e, SubstE Name e, HoistableE e)
  => Scope o
  -> Subst (SubstVal c atom) i o
  -> e i
  -> DistinctAbs (Nest (BinderP c atom)) e o
substAnything scope subst e =
  substAnythingRec scope subst emptyInMap $ collectFreeVars e

substAnythingRec
  :: (Distinct o, SinkableE atom, SinkableE e, SubstE Name e)
  => Scope o
  -> Subst (SubstVal c atom) i o
  -> Subst Name h o
  -> WithRenamer e h i
  -> DistinctAbs (Nest (BinderP c atom)) e o
substAnythingRec scope atomSubst nameSubst (WithRenamer renamer e) =
  case unConsSubst renamer of
    EmptySubst -> DistinctAbs Empty $ substE (scope, nameSubst) e
    ConsSubst b v rest -> case atomSubst ! v of
      Rename v' ->
        substAnythingRec scope atomSubst nameSubst' $ WithRenamer rest e
        where nameSubst' = nameSubst <>> b@>v'
      SubstVal x ->
        withFresh (getNameHint b) nameColorRep scope \b' -> do
          let scope'     = scope `extendOutMap` toScopeFrag b'
          let atomSubst' = sink atomSubst
          let nameSubst' = sink nameSubst <>> b@> binderName b'
          prependNestAbs (b':>x) $
            substAnythingRec scope' atomSubst' nameSubst' $ WithRenamer rest e

prependNestAbs :: b n l -> DistinctAbs (Nest b) e l -> DistinctAbs (Nest b) e n
prependNestAbs b (DistinctAbs bs e) = DistinctAbs (Nest b bs) e

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
  allowedEffects <- getAllowedEffects
  checkExtends allowedEffects effs

extendAllowedEffect :: Typer m => Effect o -> m i o () -> m i o ()
extendAllowedEffect newEff cont = do
  effs <- getAllowedEffects
  Immut <- getImmut
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
  RecordTy (NoExt types) -> return $ length types
  ProdTy tys -> return $ length tys
  _ -> error $ "Projecting a type that doesn't support projecting: " ++ pprint ty

-- === "Data" type class ===

isData :: EnvReader m => Type n -> m n Bool
isData ty = fromLiftE <$> liftImmut do
  ty' <- sinkM ty
  DB env <- getDB
  let s = " is not serializable"
  case runFallibleM $ runEnvReaderT env $ runSubstReaderT idSubst $ checkDataLike s ty' of
    Success () -> return $ LiftE True
    Failure _  -> return $ LiftE False

checkDataLike :: ( EnvReader2 m, EnvExtender2 m
                 , SubstReader Name m, Fallible2 m, Immut o)
              => String -> Type i -> m i o ()
checkDataLike msg ty = case ty of
  Var _ -> error "Not implemented"
  TabTy b eltTy ->
    substBinders b \_ ->
      checkDataLike msg eltTy
  RecordTy (NoExt items)  -> mapM_ recur items
  VariantTy (NoExt items) -> mapM_ recur items
  DepPairTy (DepPairType b@(_:>l) r) -> do
    recur l
    substBinders b \_ -> checkDataLike msg r
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
    _ -> throw TypeErr $ pprint ty ++ msg
  _   -> throw TypeErr $ pprint ty ++ msg

  where
    recur x = checkDataLike msg x

checkDataLikeBinderNest :: ( EnvReader2 m, EnvExtender2 m
                           , SubstReader Name m, Fallible2 m, Immut o)
                        => EmptyAbs (Nest Binder) i -> m i o ()
checkDataLikeBinderNest (Abs Empty UnitE) = return ()
checkDataLikeBinderNest (Abs (Nest b rest) UnitE) = do
  checkDataLike "data con binder" $ binderType b
  substBinders b \_ -> checkDataLikeBinderNest $ Abs rest UnitE
