-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Generalize (generalizeArgs, generalizeIxDict) where

import Control.Monad
import Data.Maybe (fromJust)

import Core
import Err
import PPrint
import Types.Core
import Inference
import IRVariants
import QueryType
import Name
import Subst
import Types.Primitives
import Types.Top

type RolePiBinder = WithAttrB RoleExpl CBinder
type RolePiBinders = Nest RolePiBinder

generalizeIxDict :: EnvReader m => CDict n -> m n (Generalized CoreIR CDict n)
generalizeIxDict dict = liftGeneralizerM do
  dict' <- sinkM dict
  dictTy <- return $ getType dict'
  dictTyGeneralized <- generalizeType dictTy
  liftEnvReaderM $ generalizeDict dictTyGeneralized dict'
{-# INLINE generalizeIxDict #-}

generalizeArgs ::EnvReader m => CorePiType n -> [Atom CoreIR n] -> m n (Generalized CoreIR (ListE CAtom) n)
generalizeArgs fTy argsTop = liftGeneralizerM $ runSubstReaderT idSubst do
  PairE (CorePiType _ expls bs _) (ListE argsTop') <- sinkM $ PairE fTy (ListE argsTop)
  ListE <$> go (zipAttrs expls bs) argsTop'
  where
    go :: Nest (WithAttrB Explicitness CBinder) i i' -> [Atom CoreIR n]
       -> SubstReaderT AtomSubstVal GeneralizerM i n [Atom CoreIR n]
    go (Nest (WithAttrB expl b) bs) (arg:args) = do
      ty' <- substM $ binderType b
      arg' <- liftSubstReaderT case (ty', expl) of
        (TyKind, _) -> toAtom <$> generalizeType (fromJust $ toMaybeType arg)
        (TyCon (DictTy _), Inferred Nothing (Synth _)) ->
          toAtom <$> generalizeDict ty' (fromJust $ toMaybeDict arg)
        _ -> isData ty' >>= \case
          True -> toAtom <$> emitGeneralizationParameter ty' arg
          False -> do
            -- Unlike in `inferRoles` in `Inference`, it's ok to have non-data,
            -- non-type, non-dict arguments (e.g. a function). We just don't
            -- generalize in that case.
            return arg
      args'' <- extendSubst (b@>SubstVal arg') $ go bs args
      return $ arg' : args''
    go Empty [] = return []
    go _ _ = error "zip error"
{-# INLINE generalizeArgs #-}

-- === generalizer monad plumbing ===

data GeneralizationEmission n l = GeneralizationEmission (Binder CoreIR n l) (Atom CoreIR n)
type GeneralizationEmissions = RNest GeneralizationEmission

newtype GeneralizerM n a = GeneralizerM {
  runGeneralizerM' :: DoubleInplaceT Env GeneralizationEmissions UnitB HardFailM n a }
  deriving (Functor, Applicative, Monad, MonadFail, Fallible, ScopeReader, EnvReader, EnvExtender)

liftGeneralizerM
  :: EnvReader m
  => (forall l. DExt n l => GeneralizerM l (e l))
  -> m n (Generalized CoreIR e n)
liftGeneralizerM cont = do
  env <- unsafeGetEnv
  Distinct <- getDistinct
  Abs emissions (DoubleInplaceTResult UnitB e) <- return $ runHardFail $
    runDoubleInplaceT env $ runGeneralizerM' cont
  let (bs, vals) = hoistGeneralizationVals (unRNest emissions)
  return (Abs bs e, vals)
  where
    -- OPTIMIZE: something not O(N^2)
    hoistGeneralizationVals :: Nest GeneralizationEmission n l -> (Nest (Binder CoreIR) n l, [Atom CoreIR n])
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
emitGeneralizationParameter :: Type CoreIR n -> Atom CoreIR n -> GeneralizerM n (AtomVar CoreIR n)
emitGeneralizationParameter ty val = GeneralizerM do
  Abs b v <- return $ newName noHint
  let emission = Abs (RNest REmpty (GeneralizationEmission (b:>ty) val)) v
  emitDoubleInplaceTHoisted emission >>= \case
    -- This will hoist above binders appearing in types (e.g. pi binders, and
    -- dependent pair binders). As long as those variables are only used in
    -- DataParam roles, this hoisting should succeed.
    Nothing -> error $ "expected atom to be hoistable " ++ pprint val
    Just v' -> return $ AtomVar v' ty

-- === actual generalization traversal ===

-- Given a type (an Atom of type `Type`), abstracts over all data components
generalizeType :: Type CoreIR n -> GeneralizerM n (Type CoreIR n)
generalizeType ty = traverseTyParams ty \paramRole paramReqTy param -> case paramRole of
  TypeParam -> toAtom <$> generalizeType (fromJust $ toMaybeType param)
  DictParam -> toAtom <$> generalizeDict paramReqTy (fromJust $ toMaybeDict param)
  DataParam -> toAtom <$> emitGeneralizationParameter paramReqTy param

-- === role-aware type traversal ===

-- This traverses the type parameters, with knowledge of their roles and
-- expected types. It's used here for generalization, but it may also be useful
-- for other operations on types, like newtype stripping.

traverseTyParams
  :: forall m n. (EnvReader m, EnvExtender m)
  => CType n
  -> (forall l . DExt n l => ParamRole -> CType l -> CAtom l -> m l (CAtom l))
  -> m n (CType n)
traverseTyParams (StuckTy _ _) _ = error "shouldn't have StuckTy left"
traverseTyParams (TyCon ty) f = liftM TyCon $ getDistinct >>= \Distinct -> case ty of
  DictTy dictTy -> DictTy <$> case dictTy of
    DictType sn name params -> do
      Abs paramRoles UnitE <- getClassRoleBinders name
      params' <- traverseRoleBinders f paramRoles params
      return $ DictType sn name params'
    IxDictType   t -> IxDictType   <$> f' TypeParam TyKind t
    DataDictType t -> DataDictType <$> f' TypeParam TyKind t
  TabPi (TabPiType d (b:>iTy) resultTy) -> do
    iTy' <- f' TypeParam TyKind iTy
    let dictTy = toType $ IxDictType iTy'
    d' <- fromJust . toMaybeDict <$> f DictParam dictTy (toAtom d)
    withFreshBinder (getNameHint b) iTy' \(b':>_) -> do
      resultTy' <- applyRename (b@>binderName b') resultTy >>= (f' TypeParam TyKind)
      return $ TabPi $ TabPiType d' (b':>iTy') resultTy'
  BaseType b -> return $ BaseType b
  ProdType tys -> ProdType <$> forM tys \t -> f' TypeParam TyKind t
  RefType _ _ -> error "not implemented" -- how should we handle the ParamRole for the heap parameter?
  SumType  tys -> SumType  <$> forM tys \t -> f' TypeParam TyKind t
  TypeKind     -> return TypeKind
  HeapType     -> return HeapType
  NewtypeTyCon con -> NewtypeTyCon <$> case con of
    Nat -> return Nat
    Fin n -> Fin <$> f DataParam NatTy n
    EffectRowKind    -> return EffectRowKind
    UserADTType sn def (TyConParams infs params) -> do
      Abs roleBinders UnitE <- getDataDefRoleBinders def
      params' <- traverseRoleBinders f roleBinders params
      return $ UserADTType sn def $ TyConParams infs params'
  _ -> error $ "Not implemented: " ++ pprint ty
  where
    f' :: forall l . DExt n l => ParamRole -> CType l -> CType l -> m l (CType l)
    f' r t x = fromJust <$> toMaybeType <$> f r t (toAtom x)
{-# INLINE traverseTyParams #-}

traverseRoleBinders
  :: forall m n n'. EnvReader m
  => (forall l . DExt n l => ParamRole -> Type CoreIR l -> Atom CoreIR l -> m l (Atom CoreIR l))
  ->  RolePiBinders n n' -> [Atom CoreIR n] -> m n [Atom CoreIR n]
traverseRoleBinders f allBinders allParams =
  runSubstReaderT idSubst $ go allBinders allParams
  where
    go :: forall i i'. RolePiBinders i i' -> [Atom CoreIR n]
       -> SubstReaderT AtomSubstVal m i n [Atom CoreIR n]
    go Empty [] = return []
    go (Nest (WithAttrB (role, _) b) bs) (param:params) = do
      ty' <- substM $ binderType b
      Distinct <- getDistinct
      param' <- liftSubstReaderT $ f role ty' param
      params'' <- extendSubst (b@>SubstVal param') $ go bs params
      return $ param' : params''
    go _ _ = error "zip error"
{-# INLINE traverseRoleBinders #-}

getDataDefRoleBinders :: EnvReader m => TyConName n -> m n (Abs RolePiBinders UnitE n)
getDataDefRoleBinders def = do
  TyConDef _ attrs bs _ <- lookupTyCon def
  return $ Abs (zipAttrs attrs bs) UnitE
{-# INLINE getDataDefRoleBinders #-}

getClassRoleBinders :: EnvReader m => ClassName n -> m n (Abs RolePiBinders UnitE n)
getClassRoleBinders def = do
  ClassDef _ _ _ _ roleExpls bs _ _ <- lookupClassDef def
  return $ Abs (zipAttrs roleExpls bs) UnitE
{-# INLINE getClassRoleBinders #-}

-- === instances ===

instance GenericB GeneralizationEmission where
  type RepB GeneralizationEmission = BinderP (AtomNameC CoreIR) (PairE CType CAtom)
  fromB (GeneralizationEmission (b:>ty) x) = b :> PairE ty x
  {-# INLINE fromB #-}
  toB   (b :> PairE ty x) = GeneralizationEmission (b:>ty) x
  {-# INLINE toB #-}

instance RenameB GeneralizationEmission
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
