-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DefaultSignatures #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Core where

import Control.Applicative
import Control.Monad.Except hiding (Except)
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.Writer.Strict hiding (Alt)
import Control.Monad.State
import qualified Data.List.NonEmpty    as NE
import qualified Data.Map.Strict       as M

import Name
import Err
import LabeledItems
import Util (enumerate)

import Types.Core
import Types.Imp
import Types.Primitives
import Types.Source

-- === Typeclasses for monads ===

class ScopeReader m => EnvReader (m::MonadKind1) where
  -- Unsafe because an in-place update to `n` would invalidate the env.
  unsafeGetEnv :: m n (Env n)

-- A safe version of unsafeGetEnv (thanks to SinkableE).
withEnv :: (SinkableE e, EnvReader m) => (Env n -> e n) -> m n (e n)
withEnv f = f <$> unsafeGetEnv
{-# INLINE withEnv #-}

-- Allows going under the binder with a guarantee that said binder is
-- distinct from everything else in scope, renaming if necessary.  To
-- wit, the binder in an (Abs b e n) may shadow names from the scope n
-- -- Abs makes no guarantees.  If we want to go under the binder to
-- operate on the `e`, we want to make sure it's fresh with respect to
-- the enclosing scope, which is what refreshAbs does for its
-- continuation (with DExt n l serving as proof thereof).
class (EnvReader m, Monad1 m) => EnvExtender (m::MonadKind1) where
  refreshAbs
    :: (BindsEnv b, SubstB Name b, SubstE Name e)
    => Abs b e n
    -> (forall l. DExt n l => b n l -> e l -> m l a)
    -> m n a

class Monad2 m => EnvReaderI (m::MonadKind2) where
   getEnvI :: m i o (Env i)
   getDistinctI :: m i o (DistinctEvidence i)
   withEnvI :: Distinct i' => Env i' -> m i' o a -> m i o a

type EnvReader2   (m::MonadKind2) = forall (n::S). EnvReader   (m n)
type EnvExtender2 (m::MonadKind2) = forall (n::S). EnvExtender (m n)

-- === EnvReader monad ===

newtype EnvReaderT (m::MonadKind) (n::S) (a:: *) =
  EnvReaderT {runEnvReaderT' :: ReaderT (DistinctEvidence n, Env n) m a }
  deriving ( Functor, Applicative, Monad, MonadFail
           , MonadWriter w, Fallible, Searcher, Alternative)

type EnvReaderM = EnvReaderT Identity

runEnvReaderM :: Distinct n => Env n -> EnvReaderM n a -> a
runEnvReaderM bindings m = runIdentity $ runEnvReaderT bindings m
{-# INLINE runEnvReaderM #-}

runEnvReaderT :: Distinct n => Env n -> EnvReaderT m n a -> m a
runEnvReaderT bindings cont =
  runReaderT (runEnvReaderT' cont) (Distinct, bindings)
{-# INLINE runEnvReaderT #-}

liftEnvReaderM :: EnvReader m => EnvReaderM n a -> m n a
liftEnvReaderM cont = liftM runIdentity $ liftEnvReaderT cont
{-# INLINE liftEnvReaderM #-}

liftExceptEnvReaderM :: (EnvReader m, Fallible1 m) => EnvReaderT Except n a -> m n a
liftExceptEnvReaderM cont = liftEnvReaderT cont >>= liftExcept
{-# INLINE liftExceptEnvReaderM #-}

liftEnvReaderT :: EnvReader m' => EnvReaderT m n a -> m' n (m a)
liftEnvReaderT cont = do
  env <- unsafeGetEnv
  Distinct <- getDistinct
  return $ runReaderT (runEnvReaderT' cont) (Distinct, env)
{-# INLINE liftEnvReaderT #-}

type SubstEnvReaderM v = SubstReaderT v EnvReaderM :: MonadKind2

liftSubstEnvReaderM
  :: (EnvReader m, FromName v)
  => SubstEnvReaderM v n n a
  -> m n a
liftSubstEnvReaderM cont = liftEnvReaderM $ runSubstReaderT idSubst $ cont
{-# INLINE liftSubstEnvReaderM #-}

instance Monad m => EnvReader (EnvReaderT m) where
  unsafeGetEnv = EnvReaderT $ asks snd
  {-# INLINE unsafeGetEnv #-}

instance Monad m => EnvExtender (EnvReaderT m) where
  refreshAbs ab cont = EnvReaderT $ ReaderT
    \(Distinct, env) -> refreshAbsPure (toScope env) ab
       \_ b e -> do
         let env' = extendOutMap env $ toEnvFrag b
         runReaderT (runEnvReaderT' $ cont b e) (Distinct, env')
  {-# INLINE refreshAbs #-}

instance Monad m => ScopeReader (EnvReaderT m) where
  getDistinct = EnvReaderT $ asks fst
  {-# INLINE getDistinct #-}
  unsafeGetScope = toScope <$> snd <$> EnvReaderT ask
  {-# INLINE unsafeGetScope #-}

instance MonadIO m => MonadIO (EnvReaderT m n) where
  liftIO m = EnvReaderT $ lift $ liftIO m
  {-# INLINE liftIO #-}

deriving instance (Monad m, MonadState s m) => MonadState s (EnvReaderT m o)

-- === EnvReaderI monad ===

newtype EnvReaderIT (m::MonadKind1) (i::S) (o::S) (a:: *) =
  EnvReaderIT { runEnvReaderIT' :: ReaderT (DistinctEvidence i, Env i) (m o) a }
  deriving (Functor, Applicative, Monad, MonadFail, Catchable, Fallible, CtxReader,
            Alternative)

runEnvReaderIT :: Distinct i => Env i -> EnvReaderIT m i o a -> m o a
runEnvReaderIT env m = runReaderT (runEnvReaderIT' m) (Distinct, env)
{-# INLINE runEnvReaderIT #-}

instance Monad1 m => EnvReaderI (EnvReaderIT m) where
  getEnvI = EnvReaderIT $ asks snd
  {-# INLINE getEnvI #-}
  getDistinctI = EnvReaderIT $ asks fst
  {-# INLINE getDistinctI #-}
  withEnvI env cont = EnvReaderIT $ withReaderT (const (Distinct, env)) $
    runEnvReaderIT' cont
  {-# INLINE withEnvI #-}

-- run a monadic EnvReaderM function over the in-space env
liftEnvReaderI :: EnvReaderI m => EnvReaderM i a -> m i o a
liftEnvReaderI cont = do
  env <- getEnvI
  Distinct <- getDistinctI
  return $ runEnvReaderM env cont
{-# INLINE liftEnvReaderI #-}

extendI :: (BindsEnv b, EnvReaderI m, Distinct i')
        => b i i' -> m i' o a -> m i o a
extendI b cont = do
  env <- getEnvI
  Distinct <- getDistinctI
  withEnvI (extendOutMap env $ toEnvFrag b) cont
{-# INLINE extendI #-}

refreshAbsI :: (EnvReaderI m, BindsEnv b, SubstB Name b, SubstE Name e)
            => Abs b e i
            -> (forall i'. DExt i i' => b i i' -> e i' -> m i' o a)
            -> m i o a
refreshAbsI ab cont = do
  env <- getEnvI
  Distinct <- getDistinctI
  refreshAbsPure (toScope env) ab \_ b e ->
    extendI b $ cont b e

refreshLamI :: EnvReaderI m
            => LamExpr i
            -> (forall i'. DExt i i' => LamBinder i i' -> Block i' -> m i' o a)
            -> m i o a
refreshLamI _ _ = undefined

instance EnvReader m => EnvReader (EnvReaderIT m i) where
  unsafeGetEnv = EnvReaderIT $ lift unsafeGetEnv
  {-# INLINE unsafeGetEnv #-}

instance (ScopeReader m, EnvExtender m)
         => EnvExtender (EnvReaderIT m i) where
  refreshAbs ab cont = EnvReaderIT $ ReaderT \env ->
    refreshAbs ab \b e -> do
      let EnvReaderIT (ReaderT cont') = cont b e
      cont' env

instance ScopeReader m => ScopeReader (EnvReaderIT m i) where
  unsafeGetScope = EnvReaderIT $ lift unsafeGetScope
  {-# INLINE unsafeGetScope #-}
  getDistinct = EnvReaderIT $ lift getDistinct
  {-# INLINE getDistinct #-}

instance (ScopeReader m, ScopeExtender m)
         => ScopeExtender (EnvReaderIT m i) where
  refreshAbsScope ab cont = EnvReaderIT $ ReaderT \env ->
    refreshAbsScope ab \b e -> do
      let EnvReaderIT (ReaderT cont') = cont b e
      cont' env

deriving instance MonadIO1 m => MonadIO (EnvReaderIT m i o)
deriving instance (Monad1 m, MonadState (s o) (m o))
                  => MonadState (s o) (EnvReaderIT m i o)

-- === Instances for Name monads ===

instance (SinkableE e, EnvReader m)
         => EnvReader (OutReaderT e m) where
  unsafeGetEnv = OutReaderT $ lift $ unsafeGetEnv
  {-# INLINE unsafeGetEnv #-}

instance (SinkableE e, ScopeReader m, EnvExtender m)
         => EnvExtender (OutReaderT e m) where
  refreshAbs ab cont = OutReaderT $ ReaderT \env ->
    refreshAbs ab \b e -> do
      let OutReaderT (ReaderT cont') = cont b e
      env' <- sinkM env
      cont' env'
  {-# INLINE refreshAbs #-}

instance (SinkableV v, EnvReader m) => EnvReader (SubstReaderT v m i) where
  unsafeGetEnv = SubstReaderT $ lift unsafeGetEnv
  {-# INLINE unsafeGetEnv #-}

instance (SinkableV v, ScopeReader m, EnvExtender m)
         => EnvExtender (SubstReaderT v m i) where
  refreshAbs ab cont = SubstReaderT $ ReaderT \subst ->
    refreshAbs ab \b e -> do
      subst' <- sinkM subst
      let SubstReaderT (ReaderT cont') = cont b e
      cont' subst'
  {-# INLINE refreshAbs #-}

instance (Monad m, ExtOutMap Env decls, OutFrag decls)
         => EnvReader (InplaceT Env decls m) where
  unsafeGetEnv = getOutMapInplaceT
  {-# INLINE unsafeGetEnv #-}

instance ( Monad m
         , ExtOutMap Env d1, OutFrag d1
         , ExtOutMap Env d2, OutFrag d2)
         => EnvReader (DoubleInplaceT Env d1 d2 m) where
  unsafeGetEnv = liftDoubleInplaceT $ getOutMapInplaceT
  {-# INLINE unsafeGetEnv #-}

instance (Monad m, ExtOutMap Env decls, OutFrag decls)
         => EnvExtender (InplaceT Env decls m) where
  refreshAbs ab cont = UnsafeMakeInplaceT \env decls ->
    refreshAbsPure (toScope env) ab \_ b e -> do
      let subenv = extendOutMap env $ toEnvFrag b
      (ans, d, _) <- unsafeRunInplaceT (cont b e) subenv emptyOutFrag
      case fabricateDistinctEvidence @UnsafeS of
        Distinct -> do
          let env' = extendOutMap (unsafeCoerceE env) d
          return (ans, catOutFrags (toScope env') decls d, env')
  {-# INLINE refreshAbs #-}

-- === Typeclasses for syntax ===

-- TODO: unify this with `HasNames` by parameterizing by the thing you bind,
-- like we do with `SubstE Name`, `SubstE AtomSubstVal`, etc?
class BindsNames b => BindsEnv (b::B) where
  toEnvFrag :: Distinct l => b n l -> EnvFrag n l

  default toEnvFrag :: (GenericB b, BindsEnv (RepB b))
                        => Distinct l => b n l -> EnvFrag n l
  toEnvFrag b = toEnvFrag $ fromB b

instance (Color c, SinkableE ann, ToBinding ann c) => BindsEnv (BinderP c ann) where
  toEnvFrag (b:>ann) = EnvFrag (RecSubstFrag (b @> toBinding ann')) Nothing
    where ann' = withExtEvidence b $ sink ann

instance (SinkableE ann, ToBinding ann AtomNameC) => BindsEnv (NonDepNest ann) where
  toEnvFrag (NonDepNest topBs topAnns) = toEnvFrag $ zipNest topBs topAnns
    where
      zipNest :: Distinct l => Nest AtomNameBinder n l -> [ann n] -> Nest (BinderP AtomNameC ann) n l
      zipNest Empty [] = Empty
      zipNest (Nest b bs) (a:anns) = withExtEvidence b $ withSubscopeDistinct bs $
        Nest (b:>a) $ zipNest bs $ sinkList anns
      zipNest _ _ = error "Mismatched lengths in NonDepNest"

instance BindsEnv EffectBinder where
  toEnvFrag (EffectBinder effs) = EnvFrag emptyOutFrag $ Just effs

instance BindsEnv LamBinder where
  toEnvFrag (LamBinder b ty arrow effects) =
    withExtEvidence b do
      let binding = toBinding $ sink $ LamBinding arrow ty
      EnvFrag (RecSubstFrag $ b @> binding)
                   (Just $ sink effects)

instance BindsEnv PiBinder where
  toEnvFrag (PiBinder b ty arr) =
    withExtEvidence b do
      let binding = toBinding $ sink $ PiBinding arr ty
      EnvFrag (RecSubstFrag $ b @> binding) (Just Pure)

instance BindsEnv Decl where
  toEnvFrag (Let b binding) = toEnvFrag $ b :> binding
  {-# INLINE toEnvFrag #-}

instance BindsEnv TopEnvFrag where
  toEnvFrag = undefined

instance BindsEnv EnvFrag where
  toEnvFrag frag = frag
  {-# INLINE toEnvFrag #-}

instance BindsEnv (RecSubstFrag Binding) where
  toEnvFrag frag = EnvFrag frag mempty

-- This is needed to be able to derive generic traversals over Atoms, and is
-- ok to be left unimplemented for as long as it's _dynamically_ unreachable.
-- Since references are only used in Imp lowering, we're generally ok.
instance BindsEnv DataConRefBinding where
  toEnvFrag = error "not implemented"

instance (BindsEnv b1, BindsEnv b2)
         => (BindsEnv (PairB b1 b2)) where
  toEnvFrag (PairB b1 b2) = do
    let bindings2 = toEnvFrag b2
    let ext = toExtEvidence bindings2
    withSubscopeDistinct ext do
      toEnvFrag b1 `catEnvFrags` bindings2

instance BindsEnv b => (BindsEnv (Nest b)) where
  toEnvFrag = nestToEnvFrag
  {-# INLINE toEnvFrag #-}

instance BindsEnv (LiftB e) where
  toEnvFrag (LiftB _) = EnvFrag emptyOutFrag mempty
  {-# INLINE toEnvFrag #-}

nestToEnvFragRec :: (BindsEnv b, Distinct l) => EnvFrag n h -> Nest b h l -> EnvFrag n l
nestToEnvFragRec f = \case
  Empty       -> f
  Nest b rest -> withSubscopeDistinct rest $ nestToEnvFragRec (f `catEnvFrags` toEnvFrag b) rest

nestToEnvFrag :: (BindsEnv b, Distinct l) => Nest b n l -> EnvFrag n l
nestToEnvFrag = nestToEnvFragRec emptyOutFrag
{-# NOINLINE [1] nestToEnvFrag #-}
-- The unsafeCoerceB is necessary for this rule to trigger for (>>=) of InplaceT.
-- Otherwise GHC core (on which the matching is performed) will include a coercion
-- that's impossible to match on in here.
{-# RULES
      "extendEnv * Empty"  forall env. extendEnv env (nestToEnvFrag (unsafeCoerceB Empty)) = env
  #-}

instance BindsEnv b => (BindsEnv (NonEmptyNest b)) where
  toEnvFrag (NonEmptyNest b rest) = toEnvFrag $ Nest b rest

instance BindsEnv b => (BindsEnv (RNest b)) where
  toEnvFrag n = rnestToEnvFragRec n emptyOutFrag
  {-# INLINE toEnvFrag #-}

rnestToEnvFragRec :: (BindsEnv b, Distinct l) => RNest b n h -> EnvFrag h l -> EnvFrag n l
rnestToEnvFragRec n f = case n of
  REmpty       -> f
  RNest rest b -> withSubscopeDistinct f $ rnestToEnvFragRec rest (toEnvFrag b `catEnvFrags` f)

instance (BindsEnv b1, BindsEnv b2)
         => (BindsEnv (EitherB b1 b2)) where
  toEnvFrag (LeftB  b) = toEnvFrag b
  toEnvFrag (RightB b) = toEnvFrag b

instance BindsEnv UnitB where
  toEnvFrag UnitB = emptyOutFrag

instance ExtOutMap Env (Nest Decl) where
  extendOutMap bindings emissions =
    bindings `extendOutMap` toEnvFrag emissions
  {-# INLINE extendOutMap #-}

instance ExtOutMap Env (RNest Decl) where
  extendOutMap bindings emissions =
    bindings `extendOutMap` toEnvFrag emissions
  {-# INLINE extendOutMap #-}

-- === Monadic helpers ===

lookupEnv :: (Color c, EnvReader m) => Name c o -> m o (Binding c o)
lookupEnv v = withEnv $ flip lookupEnvPure v
{-# INLINE lookupEnv #-}

lookupAtomName :: EnvReader m => AtomName n -> m n (AtomBinding n)
lookupAtomName name = lookupEnv name >>= \case AtomNameBinding x -> return x
{-# INLINE lookupAtomName #-}

lookupCustomRules :: EnvReader m => AtomName n -> m n (Maybe (AtomRules n))
lookupCustomRules name = liftM fromMaybeE $ withEnv $
  toMaybeE . M.lookup name . customRulesMap . envCustomRules . topEnv
{-# INLINE lookupCustomRules #-}

lookupImpFun :: EnvReader m => ImpFunName n -> m n (ImpFunction n)
lookupImpFun name = lookupEnv name >>= \case ImpFunBinding f -> return f
{-# INLINE lookupImpFun #-}

lookupModule :: EnvReader m => ModuleName n -> m n (Module n)
lookupModule name = lookupEnv name >>= \case ModuleBinding m -> return m
{-# INLINE lookupModule #-}

lookupDataDef :: EnvReader m => DataDefName n -> m n (DataDef n)
lookupDataDef name = lookupEnv name >>= \case DataDefBinding x -> return x
{-# INLINE lookupDataDef #-}

lookupClassDef :: EnvReader m => ClassName n -> m n (ClassDef n)
lookupClassDef name = lookupEnv name >>= \case ClassBinding x -> return x
{-# INLINE lookupClassDef #-}

lookupInstanceDef :: EnvReader m => InstanceName n -> m n (InstanceDef n)
lookupInstanceDef name = lookupEnv name >>= \case InstanceBinding x -> return x
{-# INLINE lookupInstanceDef #-}

lookupSourceMapPure :: SourceMap n -> SourceName -> [SourceNameDef n]
lookupSourceMapPure (SourceMap m) v = M.findWithDefault [] v m
{-# INLINE lookupSourceMapPure #-}

lookupSourceMap :: EnvReader m => SourceName -> m n (Maybe (UVar n))
lookupSourceMap sourceName = do
  sm <- withEnv $ envSourceMap . moduleEnv
  case lookupSourceMapPure sm sourceName of
    LocalVar x:_  -> return $ Just x
    [ModuleVar _ (Just x)] -> return $ Just x
    _   -> return Nothing

updateEnv :: Color c => Name c n -> Binding c n -> Env n -> Env n
updateEnv v rhs env =
  env { topEnv = (topEnv env) { envDefs = RecSubst $ updateSubstFrag v rhs bs } }
  where (RecSubst bs) = envDefs $ topEnv env

refreshBinders
  :: (EnvExtender m, BindsEnv b, SubstB Name b)
  => b n l
  -> (forall l'. DExt n l' => b n l' -> SubstFrag Name n l l' -> m l' a)
  -> m n a
refreshBinders b cont = refreshAbs (Abs b $ idSubstFrag b) cont
{-# INLINE refreshBinders #-}

substBinders
  :: ( SinkableV v, SubstV v v, EnvExtender2 m, FromName v
     , SubstReader v m, SubstB v b, SubstV Name v, SubstB Name b, BindsEnv b)
  => b i i'
  -> (forall o'. DExt o o' => b o o' -> m i' o' a)
  -> m i o a
substBinders b cont = do
  ab <- substM $ Abs b $ idSubstFrag b
  refreshAbs ab \b' subst ->
    extendSubst subst $ cont b'
{-# INLINE substBinders #-}

withFreshBinder
  :: (Color c, EnvExtender m, ToBinding binding c)
  => NameHint -> binding n
  -> (forall l. DExt n l => NameBinder c n l -> m l a)
  -> m n a
withFreshBinder hint binding cont = do
  Abs b v <- freshNameM hint
  refreshAbs (Abs (b:>binding) v) \(b':>_) _ -> cont b'
{-# INLINE withFreshBinder #-}

withFreshBinders
  :: (Color c, EnvExtender m, ToBinding binding c)
  => [binding n]
  -> (forall l. DExt n l => Nest (BinderP c binding) n l -> [Name c l] -> m l a)
  -> m n a
withFreshBinders [] cont = do
  Distinct <- getDistinct
  cont Empty []
withFreshBinders (binding:rest) cont = do
  withFreshBinder noHint binding \b -> do
    ListE rest' <- sinkM $ ListE rest
    withFreshBinders rest' \bs vs ->
      cont (Nest (b :> binding) bs)
           (sink (binderName b) : vs)

withFreshLamBinder
  :: (EnvExtender m)
  => NameHint -> LamBinding n
  -> Abs Binder EffectRow n
  -> (forall l. DExt n l => LamBinder n l -> m l a)
  -> m n a
withFreshLamBinder hint binding@(LamBinding arr ty) effAbs cont = do
  withFreshBinder hint binding \b -> do
    effs <- applyAbs (sink effAbs) (binderName b)
    withAllowedEffects effs do
      cont $ LamBinder b ty arr effs

withFreshPureLamBinder
  :: (EnvExtender m)
  => NameHint -> LamBinding n
  -> (forall l. DExt n l => LamBinder n l -> m l a)
  -> m n a
withFreshPureLamBinder hint binding@(LamBinding arr ty) cont = do
  withFreshBinder hint binding \b -> do
    withAllowedEffects Pure do
      cont $ LamBinder b ty arr Pure

withFreshPiBinder
  :: EnvExtender m
  => NameHint -> PiBinding n
  -> (forall l. DExt n l => PiBinder n l -> m l a)
  -> m n a
withFreshPiBinder hint binding@(PiBinding arr ty) cont = do
  withFreshBinder hint binding \b ->
    withAllowedEffects Pure $
      cont $ PiBinder b ty arr

plainPiBinder :: Binder n l -> PiBinder n l
plainPiBinder (b:>ty) = PiBinder b ty PlainArrow

withAllowedEffects :: EnvExtender m => EffectRow n -> m n a -> m n a
withAllowedEffects effs cont =
  refreshAbs (Abs (EffectBinder effs) UnitE) \(EffectBinder _) UnitE ->
    cont

getLambdaDicts :: EnvReader m => m n [AtomName n]
getLambdaDicts = do
  env <- withEnv moduleEnv
  return $ lambdaDicts $ envSynthCandidates env
{-# INLINE getLambdaDicts #-}

getInstanceDicts :: EnvReader m => ClassName n -> m n [InstanceName n]
getInstanceDicts name = do
  env <- withEnv moduleEnv
  return $ M.findWithDefault [] name $ instanceDicts $ envSynthCandidates env
{-# INLINE getInstanceDicts #-}

getAllowedEffects :: EnvReader m => m n (EffectRow n)
getAllowedEffects = withEnv $ allowedEffects . moduleEnv
{-# INLINE getAllowedEffects #-}

nonDepPiType :: ScopeReader m
             => Arrow -> Type n -> EffectRow n -> Type n -> m n (PiType n)
nonDepPiType arr argTy eff resultTy =
  toConstAbs (PairE eff resultTy) >>= \case
    Abs b (PairE eff' resultTy') ->
      return $ PiType (PiBinder b argTy arr) eff' resultTy'

nonDepTabPiType :: ScopeReader m => IxType n -> Type n -> m n (TabPiType n)
nonDepTabPiType argTy resultTy =
  toConstAbs resultTy >>= \case
    Abs b resultTy' -> return $ TabPiType (b:>argTy) resultTy'

considerNonDepPiType :: PiType n -> Maybe (Arrow, Type n, EffectRow n, Type n)
considerNonDepPiType (PiType (PiBinder b argTy arr) eff resultTy) = do
  HoistSuccess (PairE eff' resultTy') <- return $ hoist b (PairE eff resultTy)
  return (arr, argTy, eff', resultTy')

fromNonDepPiType :: (ScopeReader m, MonadFail1 m)
                 => Arrow -> Type n -> m n (Type n, EffectRow n, Type n)
fromNonDepPiType arr ty = do
  Pi (PiType (PiBinder b argTy arr') eff resultTy) <- return ty
  unless (arr == arr') $ fail "arrow type mismatch"
  HoistSuccess (PairE eff' resultTy') <- return $ hoist b (PairE eff resultTy)
  return $ (argTy, eff', resultTy')

naryNonDepPiType :: ScopeReader m =>  Arrow -> EffectRow n -> [Type n] -> Type n -> m n (Type n)
naryNonDepPiType _ Pure [] resultTy = return resultTy
naryNonDepPiType _ _    [] _        = error "nullary function can't have effects"
naryNonDepPiType arr eff [ty] resultTy = Pi <$> nonDepPiType arr ty eff resultTy
naryNonDepPiType arr eff (ty:tys) resultTy = do
  innerFunctionTy <- naryNonDepPiType arr eff tys resultTy
  Pi <$> nonDepPiType arr ty Pure innerFunctionTy

naryNonDepTabPiType :: ScopeReader m =>  [IxType n] -> Type n -> m n (Type n)
naryNonDepTabPiType [] resultTy = return resultTy
naryNonDepTabPiType (ty:tys) resultTy = do
  innerFunctionTy <- naryNonDepTabPiType tys resultTy
  ty ==> innerFunctionTy

fromNaryNonDepPiType :: (ScopeReader m, MonadFail1 m)
                     => [Arrow] -> Type n -> m n ([Type n], EffectRow n, Type n)
fromNaryNonDepPiType [] ty = return ([], Pure, ty)
fromNaryNonDepPiType [arr] ty = do
  (argTy, eff, resultTy) <- fromNonDepPiType arr ty
  return ([argTy], eff, resultTy)
fromNaryNonDepPiType (arr:arrs) ty = do
  (argTy, Pure, innerTy) <- fromNonDepPiType arr ty
  (argTys, eff, resultTy) <- fromNaryNonDepPiType arrs innerTy
  return (argTy:argTys, eff, resultTy)

fromNaryNonDepTabType :: (ScopeReader m, MonadFail1 m)
                      => [()] -> Type n -> m n ([IxType n], Type n)
fromNaryNonDepTabType [] ty = return ([], ty)
fromNaryNonDepTabType (():rest) ty = do
  (argTy, innerTy) <- fromNonDepTabType ty
  (argTys, resultTy) <- fromNaryNonDepTabType rest innerTy
  return (argTy:argTys, resultTy)

fromNonDepTabType :: (ScopeReader m, MonadFail1 m) => Type n -> m n (IxType n, Type n)
fromNonDepTabType ty = do
  TabPi (TabPiType (b :> ixTy) resultTy) <- return ty
  HoistSuccess resultTy' <- return $ hoist b resultTy
  return (ixTy, resultTy')

nonDepDataConTys :: DataConDef n -> Maybe [Type n]
nonDepDataConTys (DataConDef _ (Abs binders UnitE)) = go binders
  where
    go :: Nest Binder n l -> Maybe [Type n]
    go Empty = return []
    go (Nest (b:>ty) bs) = do
      tys <- go bs
      case hoist b (ListE tys) of
        HoistFailure _ -> Nothing
        HoistSuccess (ListE tys') -> return $ ty:tys'

infixr 1 ?-->
infixr 1 -->
infixr 1 --@

(?-->) :: ScopeReader m => Type n -> Type n -> m n (Type n)
a ?--> b = Pi <$> nonDepPiType ImplicitArrow a Pure b

(-->) :: ScopeReader m => Type n -> Type n -> m n (Type n)
a --> b = Pi <$> nonDepPiType PlainArrow a Pure b

(--@) :: ScopeReader m => Type n -> Type n -> m n (Type n)
a --@ b = Pi <$> nonDepPiType LinArrow a Pure b

(==>) :: ScopeReader m => IxType n -> Type n -> m n (Type n)
a ==> b = TabPi <$> nonDepTabPiType a b

-- first argument is the number of args expected
fromNaryLamExact :: Int -> Atom n -> Maybe (NaryLamExpr n)
fromNaryLamExact exactDepth _ | exactDepth <= 0 = error "expected positive number of args"
fromNaryLamExact exactDepth lam = do
  (realDepth, naryLam) <- fromNaryLam exactDepth lam
  guard $ realDepth == exactDepth
  return naryLam

fromNaryLam :: Int -> Atom n -> Maybe (Int, NaryLamExpr n)
fromNaryLam maxDepth | maxDepth <= 0 = error "expected positive number of args"
fromNaryLam maxDepth = \case
  (Lam (LamExpr (LamBinder b ty _ effs) body)) ->
    extend <|> (Just $ (1, NaryLamExpr (NonEmptyNest (b:>ty) Empty) effs body))
    where
      extend = case (effs, body) of
        (Pure, AtomicBlock lam) | maxDepth > 1 -> do
          (d, NaryLamExpr (NonEmptyNest b2 bs2) effs2 body2) <- fromNaryLam (maxDepth - 1) lam
          return $ (d + 1, NaryLamExpr (NonEmptyNest (b:>ty) (Nest b2 bs2)) effs2 body2)
        _ -> Nothing
  _ -> Nothing

fromNaryTabLam :: Int -> Atom n -> Maybe (Int, NaryLamExpr n)
fromNaryTabLam maxDepth | maxDepth <= 0 = error "expected positive number of args"
fromNaryTabLam maxDepth = \case
  (TabLam (TabLamExpr (b:>IxType ty _) body)) ->
    extend <|> (Just $ (1, NaryLamExpr (NonEmptyNest (b:>ty) Empty) Pure body))
    where
      extend = case body of
        AtomicBlock lam | maxDepth > 1 -> do
          (d, NaryLamExpr (NonEmptyNest b2 bs2) effs2 body2) <- fromNaryTabLam (maxDepth - 1) lam
          return $ (d + 1, NaryLamExpr (NonEmptyNest (b:>ty) (Nest b2 bs2)) effs2 body2)
        _ -> Nothing
  _ -> Nothing

-- first argument is the number of args expected
fromNaryTabLamExact :: Int -> Atom n -> Maybe (NaryLamExpr n)
fromNaryTabLamExact exactDepth _ | exactDepth <= 0 = error "expected positive number of args"
fromNaryTabLamExact exactDepth lam = do
  (realDepth, naryLam) <- fromNaryTabLam exactDepth lam
  guard $ realDepth == exactDepth
  return naryLam

-- first argument is the number of args expected
fromNaryPiType :: Int -> Type n -> Maybe (NaryPiType n)
fromNaryPiType n _ | n <= 0 = error "expected positive number of args"
fromNaryPiType 1 ty = case ty of
  Pi (PiType b effs resultTy) -> Just $ NaryPiType (NonEmptyNest b Empty) effs resultTy
  _ -> Nothing
fromNaryPiType n (Pi (PiType b1 Pure piTy)) = do
  NaryPiType (NonEmptyNest b2 bs) effs resultTy <- fromNaryPiType (n-1) piTy
  Just $ NaryPiType (NonEmptyNest b1 (Nest b2 bs)) effs resultTy
fromNaryPiType _ _ = Nothing

mkConsListTy :: [Type n] -> Type n
mkConsListTy = foldr PairTy UnitTy

mkConsList :: [Atom n] -> Atom n
mkConsList = foldr PairVal UnitVal

fromConsListTy :: Fallible m => Type n -> m [Type n]
fromConsListTy ty = case ty of
  UnitTy         -> return []
  PairTy t rest -> (t:) <$> fromConsListTy rest
  _              -> throw CompilerErr $ "Not a pair or unit: " ++ show ty

-- ((...((ans & x{n}) & x{n-1})... & x2) & x1) -> (ans, [x1, ..., x{n}])
fromLeftLeaningConsListTy :: Fallible m => Int -> Type n -> m (Type n, [Type n])
fromLeftLeaningConsListTy depth initTy = go depth initTy []
  where
    go 0        ty xs = return (ty, reverse xs)
    go remDepth ty xs = case ty of
      PairTy lt rt -> go (remDepth - 1) lt (rt : xs)
      _ -> throw CompilerErr $ "Not a pair: " ++ show xs

fromConsList :: Fallible m => Atom n -> m [Atom n]
fromConsList xs = case xs of
  UnitVal        -> return []
  PairVal x rest -> (x:) <$> fromConsList rest
  _              -> throw CompilerErr $ "Not a pair or unit: " ++ show xs

type BundleDesc = Int  -- length

bundleFold :: a -> (a -> a -> a) -> [a] -> (a, BundleDesc)
bundleFold emptyVal pair els = case els of
  []  -> (emptyVal, 0)
  [e] -> (e, 1)
  h:t -> (pair h tb, td + 1)
    where (tb, td) = bundleFold emptyVal pair t

mkBundleTy :: [Type n] -> (Type n, BundleDesc)
mkBundleTy = bundleFold UnitTy PairTy

mkBundle :: [Atom n] -> (Atom n, BundleDesc)
mkBundle = bundleFold UnitVal PairVal

trySelectBranch :: Atom n -> Maybe (Int, [Atom n])
trySelectBranch e = case e of
  DataCon _ _ _ con args -> return (con, args)
  Variant (NoExt types) label i value -> do
    let LabeledItems ixtypes = enumerate types
    let index = fst $ (ixtypes M.! label) NE.!! i
    return (index, [value])
  SumVal _ i value -> Just (i, [value])
  Con (SumAsProd _ (TagRepVal tag) vals) -> do
    let i = fromIntegral tag
    return (i , vals !! i)
  _ -> Nothing

freeAtomVarsList :: HoistableE e => e n -> [AtomName n]
freeAtomVarsList = freeVarsList

freshNameM :: (Color c, EnvReader m)
           => NameHint -> m n (Abs (NameBinder c) (Name c) n)
freshNameM hint = do
  scope    <- toScope <$> unsafeGetEnv
  Distinct <- getDistinct
  return $ withFresh hint scope \b -> Abs b (binderName b)
{-# INLINE freshNameM #-}

type AtomNameMap = NameMap AtomNameC
