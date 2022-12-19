-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Generalize (generalizeArgs, generalizeIxDict, Generalized) where

import Control.Monad

import Core
import Err
import Inference
import IRVariants
import QueryType
import Name
import MTL1
import LabeledItems
import Types.Core
import Types.Primitives

type Generalized (e::E) (n::S) = (Abs (Nest (Binder CoreIR)) e n, [CAtom n])

generalizeIxDict :: EnvReader m => Dict CoreIR n -> m n (Generalized (Dict CoreIR) n)
generalizeIxDict dict = liftGeneralizerM do
  dict' <- sinkM dict
  dictTy <- getType dict'
  dictTyGeneralized <- generalizeType dictTy
  dictGeneralized <- liftEnvReaderM $ generalizeDict dictTyGeneralized dict'
  return dictGeneralized
{-# INLINE generalizeIxDict #-}

generalizeArgs ::EnvReader m => Nest (PiBinder CoreIR) n l -> [CAtom n] -> m n (Generalized (ListE CAtom) n)
generalizeArgs reqTys allArgs =  liftGeneralizerM $ runSubstReaderT idSubst do
  PairE (Abs reqTys' UnitE) (ListE allArgs') <- sinkM $ PairE (Abs reqTys UnitE) (ListE allArgs)
  ListE <$> go reqTys' allArgs'
  where
    go :: Nest (PiBinder CoreIR) i i' -> [CAtom n]
       -> SubstReaderT (AtomSubstVal CoreIR) GeneralizerM i n [CAtom n]
    go Empty [] = return []
    go (Nest (PiBinder b ty arr) bs) (arg:args) = do
      ty' <- substM ty
      arg' <- case ty' of
        TyKind   -> liftSubstReaderT $ generalizeType arg
        DictTy _ | arr == ClassArrow -> generalizeDict ty' arg
        -- Unlike in `inferRoles` in `Inference`, it's ok to have non-data,
        -- non-type, non-dict arguments (e.g. a function). We just don't
        -- generalize in that case.
        _ -> return arg
      args'' <- extendSubst (b@>SubstVal arg') $ go bs args
      return $ arg' : args''
    go _ _ = error "zip error"
{-# INLINE generalizeArgs #-}

-- === generalizer monad plumbing ===

data GeneralizationEmission n l = GeneralizationEmission (Binder CoreIR n l) (CAtom n)
type GeneralizationEmissions = RNest GeneralizationEmission

newtype GeneralizerM n a = GeneralizerM {
  runGeneralizerM' :: DoubleInplaceT Env GeneralizationEmissions UnitB HardFailM n a }
  deriving (Functor, Applicative, Monad, MonadFail, Fallible, ScopeReader, EnvReader, EnvExtender)

liftGeneralizerM
  :: EnvReader m
  => (forall l. DExt n l => GeneralizerM l (e l))
  -> m n (Generalized e n)
liftGeneralizerM cont = do
  env <- unsafeGetEnv
  Distinct <- getDistinct
  Abs emissions (DoubleInplaceTResult UnitB e) <- return $ runHardFail $
    runDoubleInplaceT env $ runGeneralizerM' cont
  let (bs, vals) = hoistGeneralizationVals (unRNest emissions)
  return (Abs bs e, vals)
  where
    -- OPTIMIZE: something not O(N^2)
    hoistGeneralizationVals :: Nest GeneralizationEmission n l -> (Nest (Binder CoreIR) n l, [CAtom n])
    hoistGeneralizationVals Empty = (Empty, [])
    hoistGeneralizationVals (Nest (GeneralizationEmission b val) bs) = do
      let (bs', vals) = hoistGeneralizationVals bs
      case hoist b (ListE vals) of
        HoistSuccess (ListE vals') -> (Nest b bs', val:vals')
        HoistFailure _ -> error "should't happen" -- when we do the generalization,
        -- the "local" values we emit never mention the new generalization binders.
        -- TODO: consider trying to encode this constraint using scope parameters.
{-# INLINE liftGeneralizerM #-}

-- XXX: the supplied type may be more general than the type of the atom!
emitGeneralizationParameter :: CType n -> CAtom n -> GeneralizerM n (CAtomName n)
emitGeneralizationParameter ty val = GeneralizerM do
  Abs b v <- return $ newName noHint
  let emission = Abs (RNest REmpty (GeneralizationEmission (b:>ty) val)) v
  emitDoubleInplaceTHoisted emission >>= \case
    -- This will hoist above binders appearing in types (e.g. pi binders, and
    -- dependent pair binders). As long as those variables are only used in
    -- DataParam roles, this hoisting should succeed.
    Nothing -> error $ "expected atom to be hoistable " ++ pprint val
    Just v' -> return v'

-- === actual generalization traversal ===

-- Given a type (an Atom of type `Type`), abstracts over all data components
generalizeType :: CType n -> GeneralizerM n (CType n)
generalizeType ty = traverseTyParams ty \paramRole paramReqTy param -> case paramRole of
  TypeParam -> generalizeType param
  DictParam -> generalizeDict paramReqTy param
  DataParam -> Var <$> emitGeneralizationParameter paramReqTy param

-- === role-aware type traversal ===

-- This traverses the type parameters, with knowledge of their roles and
-- expected types. It's used here for generalization, but it may also be useful
-- for other operations on types, like newtype stripping.

traverseTyParams
  :: (EnvReader m, EnvExtender m)
  => CAtom n
  -> (forall l . DExt n l => ParamRole -> CType l -> CAtom l -> m l (CAtom l))
  -> m n (CAtom n)
traverseTyParams ty f = getDistinct >>= \Distinct -> case ty of
  TypeCon sn def (DataDefParams arrParams) -> do
    Abs roleBinders UnitE <- getDataDefRoleBinders def
    let (arrs, params) = unzip arrParams
    params' <- traverseRoleBinders f roleBinders params
    return $ TypeCon sn def $ DataDefParams $ zip arrs params'
  DictTy (DictType sn name params) -> do
    Abs paramRoles UnitE <- getClassRoleBinders name
    params' <- traverseRoleBinders f paramRoles params
    return $ DictTy $ DictType sn name params'
  TabPi (TabPiType (b:>(IxType iTy d)) resultTy) -> do
    iTy' <- f TypeParam TyKind iTy
    dictTy <- liftM ignoreExcept $ runFallibleT1 $ DictTy <$> ixDictType iTy'
    d'   <- f DictParam dictTy d
    withFreshBinder (getNameHint b) (toBinding iTy') \b' -> do
      resultTy' <- applySubst (b@>binderName b') resultTy >>= f TypeParam TyKind
      return $ TabTy (b':>IxType iTy' d') resultTy'
  RecordTy  elems -> RecordTy  <$> traverserseFieldRowElemTypes (f TypeParam TyKind) elems
  VariantTy (Ext elems Nothing) -> do
    elems' <- traverse (f TypeParam TyKind) elems
    return $ VariantTy $ Ext elems' Nothing
  TC tc -> TC <$> case tc of
    BaseType b -> return $ BaseType b
    ProdType tys -> ProdType <$> forM tys \t -> f TypeParam TyKind t
    SumType  tys -> SumType  <$> forM tys \t -> f TypeParam TyKind t
    Nat -> return Nat
    Fin n -> Fin <$> f DataParam NatTy n
    RefType _ _ -> error "not implemented" -- how should we handle the ParamRole for the heap parameter?
    TypeKind         -> return TypeKind
    EffectRowKind    -> return EffectRowKind
    LabeledRowKindTC -> return LabeledRowKindTC
    LabelType        -> return LabelType
  _ -> error $ "Not implemented: " ++ pprint ty
{-# INLINE traverseTyParams #-}

traverseRoleBinders
  :: forall m n n'. EnvReader m
  => (forall l . DExt n l => ParamRole -> CType l -> CAtom l -> m l (CAtom l))
  ->  Nest (RolePiBinder CoreIR) n n' -> [CAtom n] -> m n [CAtom n]
traverseRoleBinders f allBinders allParams =
  runSubstReaderT idSubst $ go allBinders allParams
  where
    go :: forall i i'. Nest (RolePiBinder CoreIR) i i' -> [CAtom n]
       -> SubstReaderT (AtomSubstVal CoreIR) m i n [CAtom n]
    go Empty [] = return []
    go (Nest (RolePiBinder b ty _ role) bs) (param:params) = do
      ty' <- substM ty
      Distinct <- getDistinct
      param' <- liftSubstReaderT $ f role ty' param
      params'' <- extendSubst (b@>SubstVal param') $ go bs params
      return $ param' : params''
    go _ _ = error "zip error"
{-# INLINE traverseRoleBinders #-}

traverserseFieldRowElemTypes
  :: Monad m => (CType n -> m (CType n))
  -> FieldRowElems CoreIR n -> m (FieldRowElems CoreIR n)
traverserseFieldRowElemTypes f els = fieldRowElemsFromList <$> traverse checkElem elemList
  where
    elemList = fromFieldRowElems els
    checkElem = \case
      StaticFields items -> StaticFields <$> traverse f items
      DynField _ _ -> error "shouldn't have dynamic fields post-simplification"
      DynFields _  -> error "shouldn't have dynamic fields post-simplification"

getDataDefRoleBinders :: EnvReader m => DataDefName n -> m n (Abs (Nest (RolePiBinder CoreIR)) UnitE n)
getDataDefRoleBinders def = do
  DataDef _ bs _ <- lookupDataDef def
  return $ Abs bs UnitE
{-# INLINE getDataDefRoleBinders #-}

getClassRoleBinders :: EnvReader m => ClassName n -> m n (Abs (Nest (RolePiBinder CoreIR)) UnitE n)
getClassRoleBinders def = do
  ClassDef _ _ bs _ _ <- lookupClassDef def
  return $ Abs bs UnitE
{-# INLINE getClassRoleBinders #-}

-- === instances ===

instance GenericB GeneralizationEmission where
  type RepB GeneralizationEmission = BinderP AtomNameC (PairE CType CAtom)
  fromB (GeneralizationEmission (b:>ty) x) = b :> PairE ty x
  {-# INLINE fromB #-}
  toB   (b :> PairE ty x) = GeneralizationEmission (b:>ty) x
  {-# INLINE toB #-}

instance SubstB Name GeneralizationEmission
instance HoistableB  GeneralizationEmission
instance ProvesExt   GeneralizationEmission
instance BindsNames  GeneralizationEmission
instance SinkableB   GeneralizationEmission

instance BindsEnv GeneralizationEmission where
  toEnvFrag (GeneralizationEmission b _) = toEnvFrag b
  {-# INLINE toEnvFrag #-}

instance ExtOutMap Env GeneralizationEmissions where
  extendOutMap bindings emissions =
    bindings `extendOutMap` toEnvFrag emissions
  {-# INLINE extendOutMap #-}
