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

-- Some monads (e.g. EnvReader) and syntactic helpers for operating on CoreIR.

module Core where

import Control.Applicative
import Control.Monad.Except hiding (Except)
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.Writer.Strict hiding (Alt)
import Control.Monad.State
import qualified Control.Monad.State.Strict as SS
import qualified Data.Map.Strict       as M

import Name
import Err
import IRVariants

import Types.Core
import Types.Top
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
    :: (BindsEnv b, RenameB b, RenameE e)
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
           , MonadWriter w, Fallible, Alternative)

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

instance (Monad m, Catchable m) => Catchable (EnvReaderT m o) where
  catchErr (EnvReaderT (ReaderT m)) f = EnvReaderT $ ReaderT \env ->
    m env `catchErr` \err -> runReaderT (runEnvReaderT' $ f err) env
  {-# INLINE catchErr #-}

-- === Instances for Name monads ===

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
          return (ans, catOutFrags decls d, env')
  {-# INLINE refreshAbs #-}

instance ( Monad m, ExtOutMap Env d1, ExtOutMap Env d2
         , OutFrag d1, OutFrag d2, RenameB d1, HoistableB d1)
         => EnvExtender (DoubleInplaceT Env d1 d2 m) where
  refreshAbs ab cont = do
    (ans, decls) <- UnsafeMakeDoubleInplaceT do
      SS.StateT \s@(topScope, _) -> do
        (ans, (_, decls)) <- refreshAbs ab \b e -> do
          flip SS.runStateT (topScope, emptyOutFrag) $
            unsafeRunDoubleInplaceT $ cont b e
        return ((ans, decls), s)
    unsafeEmitDoubleInplaceTHoisted decls
    return ans
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
  toEnvFrag (b:>ann) = EnvFrag (RecSubstFrag (b @> toBinding ann'))
    where ann' = withExtEvidence b $ sink ann

instance (IRRep r, SinkableE ann, ToBinding ann (AtomNameC r)) => BindsEnv (NonDepNest r ann) where
  toEnvFrag (NonDepNest topBs topAnns) = toEnvFrag $ zipNest topBs topAnns
    where
      zipNest :: Distinct l => Nest (AtomNameBinder r) n l -> [ann n] -> Nest (BinderP (AtomNameC r) ann) n l
      zipNest Empty [] = Empty
      zipNest (Nest b bs) (a:anns) = withExtEvidence b $ withSubscopeDistinct bs $
        Nest (b:>a) $ zipNest bs $ sinkList anns
      zipNest _ _ = error "Mismatched lengths in NonDepNest"

instance IRRep r => BindsEnv (Decl r) where
  toEnvFrag (Let b binding) = toEnvFrag $ b :> binding
  {-# INLINE toEnvFrag #-}

instance BindsEnv EnvFrag where
  toEnvFrag frag = frag
  {-# INLINE toEnvFrag #-}

instance BindsEnv (RecSubstFrag Binding) where
  toEnvFrag frag = EnvFrag frag

instance BindsEnv b => BindsEnv (WithAttrB a b) where
  toEnvFrag (WithAttrB _ b) = toEnvFrag b
  {-# INLINE toEnvFrag #-}

instance (BindsEnv b1, BindsEnv b2)
         => (BindsEnv (PairB b1 b2)) where
  toEnvFrag (PairB b1 b2) = do
    let bindings2 = toEnvFrag b2
    let ext = toExtEvidence bindings2
    withSubscopeDistinct ext do
      toEnvFrag b1 `catOutFrags` bindings2

instance BindsEnv b => (BindsEnv (Nest b)) where
  toEnvFrag = nestToEnvFrag
  {-# INLINE toEnvFrag #-}

instance BindsEnv (LiftB e) where
  toEnvFrag (LiftB _) = EnvFrag emptyOutFrag
  {-# INLINE toEnvFrag #-}

nestToEnvFragRec :: (BindsEnv b, Distinct l) => EnvFrag n h -> Nest b h l -> EnvFrag n l
nestToEnvFragRec f = \case
  Empty       -> f
  Nest b rest -> withSubscopeDistinct rest $ nestToEnvFragRec (f `catOutFrags` toEnvFrag b) rest

nestToEnvFrag :: (BindsEnv b, Distinct l) => Nest b n l -> EnvFrag n l
nestToEnvFrag = nestToEnvFragRec emptyOutFrag
{-# NOINLINE [1] nestToEnvFrag #-}
-- The unsafeCoerceB is necessary for this rule to trigger for (>>=) of InplaceT.
-- Otherwise GHC core (on which the matching is performed) will include a coercion
-- that's impossible to match on in here.
{-# RULES
      "extendEnv * Empty"  forall env. extendEnv env (nestToEnvFrag (unsafeCoerceB Empty)) = env
  #-}

instance BindsEnv b => (BindsEnv (RNest b)) where
  toEnvFrag n = rnestToEnvFragRec n emptyOutFrag
  {-# INLINE toEnvFrag #-}

rnestToEnvFragRec :: (BindsEnv b, Distinct l) => RNest b n h -> EnvFrag h l -> EnvFrag n l
rnestToEnvFragRec n f = case n of
  REmpty       -> f
  RNest rest b -> withSubscopeDistinct f $ rnestToEnvFragRec rest (toEnvFrag b `catOutFrags` f)

instance (BindsEnv b1, BindsEnv b2)
         => (BindsEnv (EitherB b1 b2)) where
  toEnvFrag (LeftB  b) = toEnvFrag b
  toEnvFrag (RightB b) = toEnvFrag b

instance BindsEnv UnitB where
  toEnvFrag UnitB = emptyOutFrag

instance IRRep r => ExtOutMap Env (Nest (Decl r)) where
  extendOutMap bindings emissions =
    bindings `extendOutMap` toEnvFrag emissions
  {-# INLINE extendOutMap #-}

instance IRRep r => ExtOutMap Env (RNest (Decl r)) where
  extendOutMap bindings emissions =
    bindings `extendOutMap` toEnvFrag emissions
  {-# INLINE extendOutMap #-}

instance ExtOutMap Env UnitB where
  extendOutMap bindings UnitB = bindings
  {-# INLINE extendOutMap #-}

-- === Monadic helpers ===

lookupEnv :: (Color c, EnvReader m) => Name c o -> m o (Binding c o)
lookupEnv v = withEnv $ flip lookupEnvPure v . topEnv
{-# INLINE lookupEnv #-}

lookupAtomName :: (IRRep r, EnvReader m) => AtomName r n -> m n (AtomBinding r n)
lookupAtomName name = bindingToAtomBinding <$> lookupEnv name
{-# INLINE lookupAtomName #-}

lookupCustomRules :: EnvReader m => AtomName CoreIR n -> m n (Maybe (AtomRules n))
lookupCustomRules name = liftM fromMaybeE $ withEnv $
  toMaybeE . M.lookup name . customRulesMap . envCustomRules . topEnv
{-# INLINE lookupCustomRules #-}

lookupTopFun :: EnvReader m => TopFunName n -> m n (TopFun n)
lookupTopFun name = lookupEnv name >>= \case TopFunBinding f -> return f
{-# INLINE lookupTopFun #-}

lookupModule :: EnvReader m => ModuleName n -> m n (Module n)
lookupModule name = lookupEnv name >>= \case ModuleBinding m -> return m
{-# INLINE lookupModule #-}

lookupSpecDict :: EnvReader m => SpecDictName n -> m n (SpecializedDictDef n)
lookupSpecDict name = lookupEnv name >>=
  \case SpecializedDictBinding m -> return m
{-# INLINE lookupSpecDict #-}

lookupFunObjCode :: EnvReader m => FunObjCodeName n -> m n (CFunction n)
lookupFunObjCode name = lookupEnv name >>= \case FunObjCodeBinding cFun -> return cFun
{-# INLINE lookupFunObjCode #-}

lookupTyCon :: EnvReader m => TyConName n -> m n (TyConDef n)
lookupTyCon name = lookupEnv name >>= \case
  TyConBinding (Just x) _ -> return x
  TyConBinding Nothing  _ -> error "TyCon not yet defined"
{-# INLINE lookupTyCon #-}

lookupDataCon :: EnvReader m => Name DataConNameC n -> m n (TyConName n, Int)
lookupDataCon v = do
  ~(DataConBinding defName idx) <- lookupEnv v
  return (defName, idx)
{-# INLINE lookupDataCon #-}

lookupClassDef :: EnvReader m => ClassName n -> m n (ClassDef n)
lookupClassDef name = lookupEnv name >>= \case ClassBinding x -> return x
{-# INLINE lookupClassDef #-}

lookupInstanceDef :: EnvReader m => InstanceName n -> m n (InstanceDef n)
lookupInstanceDef name = lookupEnv name >>= \case InstanceBinding x _ -> return x
{-# INLINE lookupInstanceDef #-}

lookupInstanceTy :: EnvReader m => InstanceName n -> m n (CorePiType n)
lookupInstanceTy name = lookupEnv name >>= \case InstanceBinding _ ty -> return ty
{-# INLINE lookupInstanceTy #-}

lookupSourceMapPure :: SourceMap n -> SourceName -> [SourceNameDef n]
lookupSourceMapPure (SourceMap m) v = M.findWithDefault [] v m
{-# INLINE lookupSourceMapPure #-}

lookupSourceMap :: EnvReader m => SourceName -> m n (Maybe (UVar n))
lookupSourceMap sourceName = do
  sm <- withEnv $ envSourceMap . moduleEnv
  case lookupSourceMapPure sm sourceName of
    LocalVar _ x:_  -> return $ Just x
    [ModuleVar _ (Just x)] -> return $ Just x
    _   -> return Nothing

refreshBinders
  :: (EnvExtender m, BindsEnv b, RenameB b)
  => b n l
  -> (forall l'. DExt n l' => b n l' -> SubstFrag Name n l l' -> m l' a)
  -> m n a
refreshBinders b cont = refreshAbs (Abs b $ idSubstFrag b) cont
{-# INLINE refreshBinders #-}

withFreshBinder
  :: (Color c, EnvExtender m, ToBinding binding c)
  => NameHint -> binding n
  -> (forall l. DExt n l => BinderP c binding n l -> m l a)
  -> m n a
withFreshBinder hint binding cont = do
  Abs b v <- freshNameM hint
  refreshAbs (Abs (b:>binding) v) \b' _ -> cont b'
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
      cont (Nest b bs)
           (sink (binderName b) : vs)

-- These `fromNary` functions traverse a chain of unary structures (LamExpr,
-- TabLamExpr, CorePiType, respectively) up to the given maxDepth, and return the
-- discovered binders packed as the nary structure (NaryLamExpr or PiType),
-- including a count of how many binders there were.
-- - If there are no binders, return Nothing.
-- - If there are more than maxDepth binders, only return maxDepth of them, and
--   leave the others in the unary structure.
-- - The `exact` versions only succeed if at least maxDepth binders were
--   present, in which case exactly maxDepth binders are packed into the nary
--   structure.  Excess binders, if any, are still left in the unary structures.

liftLamExpr :: (IRRep r, EnvReader m)
  => TopLam r n
  -> (forall l m2. EnvReader m2 => Expr r l -> m2 l (Expr r l))
  -> m n (TopLam r n)
liftLamExpr (TopLam d ty (LamExpr bs body)) f = liftM (TopLam d ty) $ liftEnvReaderM $
  refreshAbs (Abs bs body) \bs' body' -> LamExpr bs' <$> f body'

fromNaryForExpr :: IRRep r => Int -> Expr r n -> Maybe (Int, LamExpr r n)
fromNaryForExpr maxDepth | maxDepth <= 0 = error "expected non-negative number of args"
fromNaryForExpr maxDepth = \case
  PrimOp (Hof (TypedHof _ (For _ _ (UnaryLamExpr b body)))) ->
    extend <|> (Just $ (1, LamExpr (Nest b Empty) body))
    where
      extend = do
        guard $ maxDepth > 1
        (d, LamExpr bs body2) <- fromNaryForExpr (maxDepth - 1) body
        return (d + 1, LamExpr (Nest b bs) body2)
  _ -> Nothing

type BundleDesc = Int  -- length

bundleFold :: a -> (a -> a -> a) -> [a] -> (a, BundleDesc)
bundleFold emptyVal pair els = case els of
  []  -> (emptyVal, 0)
  [e] -> (e, 1)
  h:t -> (pair h tb, td + 1)
    where (tb, td) = bundleFold emptyVal pair t

mkBundleTy :: [Type r n] -> (Type r n, BundleDesc)
mkBundleTy = bundleFold UnitTy (\x y -> TyCon (ProdType [x, y]))

mkBundle :: [Atom r n] -> (Atom r n, BundleDesc)
mkBundle = bundleFold UnitVal (\x y -> Con (ProdCon [x, y]))

freeAtomVarsList :: forall r e n. (IRRep r, HoistableE e) => e n -> [Name (AtomNameC r) n]
freeAtomVarsList = freeVarsList

freshNameM :: (Color c, EnvReader m) => NameHint -> m n (Abs (NameBinder c) (Name c) n)
freshNameM hint = do
  scope    <- toScope <$> unsafeGetEnv
  Distinct <- getDistinct
  return $ withFresh hint scope \b -> Abs b (binderName b)
{-# INLINE freshNameM #-}
