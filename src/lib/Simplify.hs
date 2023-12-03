-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module Simplify
  ( simplifyTopBlock, simplifyTopFunction, ReconstructAtom (..), applyReconTop,
    linearizeTopFun, SimplifiedTopLam (..)) where

import Control.Category ((>>>))
import Control.Monad
import Control.Monad.Reader
import Data.Maybe

import Builder
import CheapReduction
import CheckType
import Core
import Err
import Generalize
import IRVariants
import Linearize
import Name
import Subst
import PPrint
import QueryType
import RuntimePrint
import Transpose
import Types.Core
import Types.Source
import Types.Top
import Types.Primitives
import Util (enumerate)

-- === Simplification ===

-- The purpose of simplification is that we want first-class functions
-- in the surface language, but we don't want to deal with them when
-- generating code.  To that end, simplification inlines almost all
-- functions everywhere they appear.

-- In particular, simplification also carries out AD by discharging
-- the `Linearize` and `Transpose` constructors of `PrimHof`.

-- The exception is functions explicitly tagged @noinline by the
-- programmer.  Those, however, are second-class: they are all
-- toplevel, and get specialized until they are first order.

-- Currently, simplification also discharges `CatchException` by
-- elaborating the expression into a Maybe-style monad.  Note: the
-- plan is for `CatchException` to become a user-defined effect, and
-- for simplification to discharge all of them.

-- Simplification also opportunistically does peep-hole optimizations:
-- some constant folding, case-of-known-constructor, projecting known
-- elements from products, etc; but is not guaranteed to find all such
-- opportunities.

-- === Conversions between CoreIR, CoreToSimpIR, SimpIR ===

tryAsDataAtom :: Emits n => CAtom n -> SimplifyM i n (Maybe (SAtom n, Type CoreIR n))
tryAsDataAtom atom = do
  let ty = getType atom
  isData ty >>= \case
    False -> return Nothing
    True -> Just <$> do
      repAtom <- dropSubst $ toDataAtom atom
      return (repAtom, ty)

data WithSubst (e::E) (o::S) where
  WithSubst :: Subst AtomSubstVal i o -> e i -> WithSubst e o

type ACase = SStuck `PairE` ListE (Abs SBinder CAtom) `PairE` CType

data ConcreteCAtom (n::S) =
   CCCon (WithSubst (Con CoreIR) n)
 | CCLiftSimp (CType n) (Stuck SimpIR n)
 | CCFun   (ConcreteCFun n)
 | CCTabLam (WithSubst TabLamExpr n)
 | CCACase (WithSubst ACase n)

data ConcreteCFun (n::S) =
   CCLiftSimpFun (CorePiType n) (LamExpr SimpIR n)
 | CCNoInlineFun (CAtomVar n) (CType n) (CAtom n)
 | CCFFIFun      (CorePiType n) (TopFunName n)

forceConstructor :: CAtom i -> SimplifyM i o (ConcreteCAtom o)
forceConstructor atom = withDistinct case atom of
  Stuck _ stuck -> forceStuck stuck
  Con con -> do
    subst <- getSubst
    return $ CCCon $ WithSubst subst con

forceStuck :: forall i o . CStuck i -> SimplifyM i o (ConcreteCAtom o)
forceStuck stuck = withDistinct case stuck of
  Var v -> lookupSubstM (atomVarName v) >>= \case
    SubstVal x -> dropSubst $ forceConstructor x
    Rename v' -> lookupAtomName v' >>= \case
      LetBound (DeclBinding _ (Atom x)) -> dropSubst $ forceConstructor x
      NoinlineFun t f -> do
        v'' <- toAtomVar v'
        return $ CCFun $ CCNoInlineFun v'' t f
      FFIFunBound t f -> return $ CCFun $ CCFFIFun t f
      _ -> error "shouldn't have other CVars left"
  LiftSimp _ x -> do
    -- the subst should be rename-only for `x`. We should make subst IR-specific
    s <- getSubst
    let s' = newSubst \v -> case s ! v of
          SubstVal _ -> error "subst should be rename-only for SimpIR vars" -- TODO: make subst IR-specific
          Rename v' -> v'
    x' <- runSubstReaderT s' $ renameM x
    returnLifted x'
  -- We "thunk" ACase rather than forcing it because different use-cases require different ways to force it
  ACase e alts resultTy -> do
    subst <- getSubst
    return $ CCACase $ WithSubst subst $ e `PairE` ListE alts `PairE` resultTy
  TabLam e -> do
    subst <- getSubst
    return $ CCTabLam $ WithSubst subst e
  StuckProject i x -> forceStuck x >>= \case
    CCLiftSimp _ x' -> returnLifted $ StuckProject i x'
    CCCon (WithSubst s con) -> withSubst s case con of
      ProdCon xs    -> forceConstructor (xs!!i)
      DepPair l r _ -> forceConstructor ([l, r]!!i)
      _ -> error "not a product"
    CCACase x' -> pushUnderACase x' \x'' -> reduceProj i x''
    CCFun _    -> error "not a product"
    CCTabLam _ -> error "not a product"
  StuckTabApp f x -> forceStuck f >>= \case
    CCLiftSimp _ f' -> do
      x' <- toDataAtom x
      returnLifted $ StuckTabApp f' x'
    CCTabLam (WithSubst s (PairE _ (Abs b body))) -> do
      x' <- toDataAtom x
      result <- withSubst s $ extendSubst (b@>SubstVal x') $ substM body
      dropSubst $ forceConstructor result
    CCACase f' -> pushUnderACase f' \f'' -> reduceTabApp f'' =<< substM x
    CCCon _ -> error "not a table"
    CCFun _ -> error "not a table"
  StuckUnwrap x -> forceStuck x >>= \case
    CCCon (WithSubst s con) -> case con of
      NewtypeCon _ x' -> withSubst s $ forceConstructor x'
      _ -> error "not a newtype"
    CCLiftSimp _ x' -> returnLifted x'
    CCACase x' -> pushUnderACase x' \x'' -> reduceUnwrap x''
    CCFun    _ -> error "not a newtype"
    CCTabLam _ -> error "not a newtype"
  InstantiatedGiven _ _ -> error "shouldn't have this left"
  SuperclassProj _ _    -> error "shouldn't have this left"
  PtrVar ty p -> do
    p' <- substM p
    returnLifted $ PtrVar ty p'
  LiftSimpFun t f -> CCFun <$> (CCLiftSimpFun <$> substM t <*> substM f)
  where
    returnLifted :: SStuck o -> SimplifyM i o (ConcreteCAtom o)
    returnLifted s = do
      resultTy <- getType <$> substMStuck stuck
      return $ CCLiftSimp resultTy s

pushUnderACase
  :: WithSubst ACase o
  -> (forall o'. DExt o o' => CAtom o' -> SimplifyM i o' (CAtom o'))
  -> SimplifyM i o (ConcreteCAtom o)
pushUnderACase _ _ = undefined
-- pushUnderACase (WithSubst s (scrut `PairE` ListE alts `PairE` resultTy)) cont = undefined
-- TODO: make a buildACase to use here and elsewhere in Simplify. Maybe in CheapReduce too?


forceACase
  :: Emits o => WithSubst ACase o
  -> (forall o'. (Emits o', DExt o o') => ConcreteCAtom o' -> SimplifyM i o' (CAtom o'))
  -> SimplifyM i o (CAtom o)
forceACase (WithSubst subst (scrut `PairE` ListE alts `PairE` resultTy)) cont = do
    resultTy' <- withSubst subst $ substM resultTy
    scrut'    <- withSubst subst $ substMStuck scrut
    defuncCase scrut' resultTy' \i x -> do
      Abs b body <- return $ alts !! i
      body' <- withSubst (sink subst) $ extendSubst (b@>SubstVal x) $ forceConstructor body
      cont body'

tryGetRepType :: Type CoreIR n -> SimplifyM i n (Maybe (SType n))
tryGetRepType t = isData t >>= \case
  False -> return Nothing
  True  -> Just <$> dropSubst (getRepType t)

getRepType :: Type CoreIR i -> SimplifyM i o (SType o)
getRepType (StuckTy _ stuck) =
  substMStuck stuck >>= \case
    Stuck _ _ -> error "shouldn't have stuck CType after substitution"
    Con (TyConAtom tyCon) -> dropSubst $ getRepType (TyCon tyCon)
    Con _ -> error "not a type"
getRepType (TyCon con) = case con of
  BaseType b  -> return $ toType $ BaseType b
  ProdType ts -> toType . ProdType <$> mapM getRepType ts
  SumType  ts -> toType . SumType  <$> mapM getRepType ts
  RefType h a -> toType <$> (RefType <$> toDataAtomAssumeNoDecls h <*> getRepType a)
  HeapType    -> return $ toType HeapType
  DepPairTy (DepPairType expl b r) -> do
    withSimplifiedBinder b \b' -> do
      r' <- getRepType r
      return $ toType $ DepPairType expl b' r'
  TabPi (TabPiType ixDict b r) -> do
    ixDict' <- simplifyIxDict ixDict
    withSimplifiedBinder b \b' -> do
      r' <- getRepType r
      return $ toType $ TabPi $ TabPiType ixDict' b' r'
  NewtypeTyCon con' -> do
    (_, ty') <- unwrapNewtypeType =<< substM con'
    dropSubst $ getRepType ty'
  Pi _     -> error notDataType
  DictTy _ -> error notDataType
  TypeKind -> error notDataType
  where notDataType = "Not a type of runtime-representable data"

toDataAtom :: CAtom i -> SimplifyM i o (SAtom o)
toDataAtom (Con con) = case con of
  Lit v -> return $ toAtom $ Lit v
  ProdCon xs -> toAtom . ProdCon <$> mapM rec xs
  SumCon  tys tag x -> toAtom <$> (SumCon <$> mapM getRepType tys <*> pure tag <*> rec x)
  HeapVal           -> return $ toAtom HeapVal
  DepPair x y ty -> do
    TyCon (DepPairTy ty') <- getRepType $ TyCon $ DepPairTy ty
    toAtom <$> (DepPair <$> rec x <*> rec y <*> pure ty')
  NewtypeCon _ x  -> rec x
  Lam _         -> notData
  DictConAtom _ -> notData
  Eff _         -> notData
  TyConAtom _   -> notData
  where
    rec = toDataAtom
    notData = error $ "Not runtime-representable data"
toDataAtom (Stuck _ stuck) = forceStuck stuck >>= \case
  CCCon (WithSubst s con) -> withSubst s $ toDataAtom (Con con)
  CCLiftSimp _ e -> mkStuck e
  CCFun    _   -> notData
  CCACase  _   -> notData -- TODO: make sure we observe this invariant"
  CCTabLam _   -> notData -- TODO: make sure we observe this invariant"
  where notData = error $ "Not runtime-representable data"

toDataAtomAssumeNoDecls :: CAtom i -> SimplifyM i o (SAtom o)
toDataAtomAssumeNoDecls x = do
  Abs decls result <- buildScoped $ toDataAtom x
  case decls of
    Empty -> return result
    _ -> error "unexpected decls"

withSimplifiedBinder
 :: CBinder i i'
 -> (forall o'. DExt o o' => Binder SimpIR o o' -> SimplifyM i' o' a)
 -> SimplifyM i o a
withSimplifiedBinder (b:>ty) cont = do
  tySimp <- getRepType ty
  tyCore <- substM ty
  withFreshBinder (getNameHint b) tySimp \b' -> do
    x <- liftSimpAtom (sink tyCore) (toAtom $ binderVar b')
    extendSubst (b@>SubstVal x) $ cont b'

withSimplifiedBinders
 :: Nest (Binder CoreIR) o any
 -> (forall o'. DExt o o' => Nest (Binder SimpIR) o o' -> [CAtom o'] -> SimplifyM i o' a)
 -> SimplifyM i o a
withSimplifiedBinders Empty cont = getDistinct >>= \Distinct -> cont Empty []
withSimplifiedBinders (Nest (bCore:>ty) bsCore) cont = do
  simpTy <- dropSubst $ getRepType ty
  withFreshBinder (getNameHint bCore) simpTy \bSimp -> do
    x <- liftSimpAtom (sink ty) (toAtom $ binderVar bSimp)
    -- TODO: carry a substitution instead of doing N^2 work like this
    Abs bsCore' UnitE <- applySubst (bCore@>SubstVal x) (EmptyAbs bsCore)
    withSimplifiedBinders bsCore' \bsSimp xs ->
      cont (Nest bSimp bsSimp) (sink x:xs)

-- === Reconstructions ===

data ReconstructAtom (n::S) =
   CoerceRecon (Type CoreIR n)
 | LamRecon (ReconAbs SimpIR CAtom n)

applyRecon :: (EnvReader m, Fallible1 m) => ReconstructAtom n -> SAtom n -> m n (CAtom n)
applyRecon (CoerceRecon ty) x = liftSimpAtom ty x
applyRecon (LamRecon ab) x = applyReconAbs ab x

-- === Simplification monad ===

class (ScopableBuilder2 SimpIR m, SubstReader AtomSubstVal m) => Simplifier m

newtype SimplifyM (i::S) (o::S) (a:: *) = SimplifyM
  { runSimplifyM'
    :: SubstReaderT AtomSubstVal (DoubleBuilderT SimpIR TopEnvFrag  HardFailM) i o a }
  deriving ( Functor, Applicative, Monad, ScopeReader, EnvExtender, Fallible
           , EnvReader, SubstReader AtomSubstVal, MonadFail
           , Builder SimpIR, HoistingTopBuilder TopEnvFrag)

liftSimplifyM
  :: (SinkableE e, RenameE e, TopBuilder m, Mut n)
  => (forall l. DExt n l => SimplifyM n l (e l))
  -> m n (e n)
liftSimplifyM cont = do
  Abs envFrag e <- liftM runHardFail $
    liftDoubleBuilderT $ runSubstReaderT (sink idSubst) $ runSimplifyM' cont
  emitEnv $ Abs envFrag e
{-# INLINE liftSimplifyM #-}

liftDoubleBuilderToSimplifyM :: DoubleBuilder SimpIR o a -> SimplifyM i o a
liftDoubleBuilderToSimplifyM cont = SimplifyM $ liftSubstReaderT cont

instance Simplifier SimplifyM
deriving instance ScopableBuilder SimpIR (SimplifyM i)

-- === Top-level API ===

data SimplifiedTopLam n = SimplifiedTopLam (STopLam n) (ReconstructAtom n)
data SimplifiedBlock n = SimplifiedBlock (SExpr n) (ReconstructAtom n)

simplifyTopBlock
  :: (TopBuilder m, Mut n) => TopBlock CoreIR n -> m n (SimplifiedTopLam n)
simplifyTopBlock (TopLam _ _ (LamExpr Empty body)) = do
  SimplifiedBlock block recon <- liftSimplifyM do
    {-# SCC "Simplify" #-} buildSimplifiedBlock $ simplifyExpr body
  topLam <- asTopLam $ LamExpr Empty block
  return $ SimplifiedTopLam topLam recon
simplifyTopBlock _ = error "not a block (nullary lambda)"

simplifyTopFunction :: (TopBuilder m, Mut n) => CTopLam n -> m n (STopLam n)
simplifyTopFunction (TopLam False _ f) = do
  asTopLam =<< liftSimplifyM do
    (lam, CoerceReconAbs) <- {-# SCC "Simplify" #-} simplifyLam f
    return lam
simplifyTopFunction _ = error "shouldn't be in destination-passing style already"

applyReconTop :: (EnvReader m, Fallible1 m) => ReconstructAtom n -> SAtom n -> m n (CAtom n)
applyReconTop = applyRecon

instance GenericE SimplifiedBlock where
  type RepE SimplifiedBlock = PairE SExpr ReconstructAtom
  fromE (SimplifiedBlock block recon) = PairE block recon
  {-# INLINE fromE #-}
  toE   (PairE block recon) = SimplifiedBlock block recon
  {-# INLINE toE #-}

instance SinkableE SimplifiedBlock
instance RenameE SimplifiedBlock
instance HoistableE SimplifiedBlock

instance Pretty (SimplifiedBlock n) where
  pretty (SimplifiedBlock block recon) =
    pretty block <> hardline <> pretty recon

instance SinkableE SimplifiedTopLam where
  sinkingProofE = todoSinkableProof

instance CheckableE SimpIR SimplifiedTopLam where
  checkE (SimplifiedTopLam lam recon) =
    -- TODO: CheckableE instance for the recon too
    SimplifiedTopLam <$> checkE lam <*> renameM recon

instance Pretty (SimplifiedTopLam n) where
  pretty (SimplifiedTopLam lam recon) = pretty lam <> hardline <> pretty recon

-- === All the bits of IR  ===

simplifyDecls :: Emits o => Nest (Decl CoreIR) i i' -> SimplifyM i' o a -> SimplifyM i o a
simplifyDecls topDecls cont = do
  s  <- getSubst
  s' <- simpDeclsSubst s topDecls
  withSubst s' cont
{-# INLINE simplifyDecls #-}

simpDeclsSubst
  :: Emits o => Subst AtomSubstVal l o -> Nest (Decl CoreIR) l i'
  -> SimplifyM i o (Subst AtomSubstVal i' o)
simpDeclsSubst !s = \case
  Empty -> return s
  Nest (Let b (DeclBinding _ expr)) rest -> do
    x <- withSubst s $ simplifyExpr expr
    simpDeclsSubst (s <>> (b@>SubstVal x)) rest

simplifyExpr :: Emits o => Expr CoreIR i -> SimplifyM i o (CAtom o)
simplifyExpr expr = confuseGHC >>= \_ -> case expr of
  Block _ (Abs decls body) -> simplifyDecls decls $ simplifyExpr body
  App (EffTy _ ty) f xs -> do
    ty' <- substM ty
    f' <- forceConstructor f
    xs' <- mapM simplifyAtom xs
    simplifyApp ty' f' xs'
  TabApp _ f x -> withDistinct do
    x' <- simplifyAtom x
    f' <- forceConstructor f
    simplifyTabApp f' x'
  Atom x -> simplifyAtom x
  PrimOp  op  -> simplifyOp op
  ApplyMethod (EffTy _ ty) dict i xs -> do
    ty' <- substM ty
    xs' <- mapM simplifyAtom xs
    Just dict' <- toMaybeDict <$> simplifyAtom dict
    applyDictMethod ty' dict' i xs'
  TabCon _ ty xs -> do
    ty' <- substM ty
    tySimp <- getRepType ty
    xs' <- forM xs \x -> toDataAtom x
    liftSimpAtom ty' =<< emit (TabCon Nothing tySimp xs')
  Case scrut alts (EffTy _ resultTy) -> do
    scrut' <- simplifyAtom scrut
    resultTy' <- substM resultTy
    defuncCaseCore scrut' resultTy' \i x -> do
      Abs b body <- return $ alts !! i
      extendSubst (b@>SubstVal x) $ simplifyExpr body
  Project ty i x -> do
    ty' <- substM ty
    x'  <- substM x
    tryAsDataAtom x' >>= \case
      Just (x'', _) -> liftSimpAtom ty' =<< proj i x''
      Nothing -> requireReduced $ Project ty' i x'
  Unwrap _ _ -> requireReduced =<< substM expr

requireReduced :: CExpr o -> SimplifyM i o (CAtom o)
requireReduced expr = reduceExpr expr >>= \case
  Just x -> return x
  Nothing -> error "couldn't reduce expression"

simplifyRefOp :: Emits o => RefOp CoreIR i -> SAtom o -> SimplifyM i o (SAtom o)
simplifyRefOp op ref = case op of
  MExtend (BaseMonoid em cb) x -> do
    em'  <- toDataAtom em
    x'   <- toDataAtom x
    (cb', CoerceReconAbs) <- simplifyLam cb
    emitRefOp $ MExtend (BaseMonoid em' cb') x'
  MGet   -> emit $ RefOp ref MGet
  MPut x -> do
    x' <- toDataAtom x
    emitRefOp $ MPut x'
  MAsk   -> emitRefOp MAsk
  IndexRef _ x -> do
    x' <- toDataAtom x
    emit =<< mkIndexRef ref x'
  ProjRef _ (ProjectProduct i) -> emit =<< mkProjRef ref (ProjectProduct i)
  ProjRef _ UnwrapNewtype -> return ref
  where emitRefOp op' = emit $ RefOp ref op'

defuncCaseCore :: Emits o
  => Atom CoreIR o -> Type CoreIR o
  -> (forall o'. (Emits o', DExt o o') => Int -> CAtom o' -> SimplifyM i o' (CAtom o'))
  -> SimplifyM i o (CAtom o)
defuncCaseCore scrut resultTy cont = do
  tryAsDataAtom scrut >>= \case
    Just (scrutSimp, _) -> do
      altBinderTys <- caseAltsBinderTys $ getType scrut
      defuncCase scrutSimp resultTy \i x -> do
        let xCoreTy = altBinderTys !! i
        x' <- liftSimpAtom (sink xCoreTy) x
        cont i x'
    Nothing -> case scrut of
      Con (SumCon _ i arg) -> getDistinct >>= \Distinct -> cont i arg
      _ -> error $ "Don't know how to scrutinize non-data " ++ pprint scrut

defuncCase :: Emits o
  => Atom SimpIR o -> Type CoreIR o
  -> (forall o'. (Emits o', DExt o o') => Int -> SAtom o' -> SimplifyM i o' (CAtom o'))
  -> SimplifyM i o (CAtom o)
defuncCase scrut resultTy cont = do
  case scrut of
    Con (SumCon _ i arg) -> getDistinct >>= \Distinct -> cont i arg
    Con _ -> error "scrutinee must be a sum type"
    Stuck _ _ -> do
      altBinderTys <- caseAltsBinderTys (getType scrut)
      tryGetRepType resultTy >>= \case
        Just resultTyData -> do
          alts' <- forM (enumerate altBinderTys) \(i, bTy) -> do
            buildAbs noHint bTy \x -> buildBlock do
              ans <- cont i (toAtom $ sink x)
              dropSubst $ toDataAtom ans
          caseExpr <- mkCase scrut resultTyData alts'
          emit caseExpr >>= liftSimpAtom resultTy
        Nothing -> do
          split <- splitDataComponents resultTy
          (alts', closureTys, recons) <- unzip3 <$> forM (enumerate altBinderTys) \(i, bTy) -> do
             simplifyAlt split bTy $ cont i
          let closureSumTy = TyCon $ SumType closureTys
          let newNonDataTy = nonDataTy split
          alts'' <- forM (enumerate alts') \(i, alt) -> injectAltResult closureTys i alt
          caseExpr <- mkCase scrut  (PairTy (dataTy split) closureSumTy) alts''
          caseResult <- emit $ caseExpr
          (dataVal, sumVal) <- fromPair caseResult
          reconAlts <- forM (zip closureTys recons) \(ty, recon) ->
            buildAbs noHint ty \v -> applyRecon (sink recon) (toAtom v)
          nonDataVal <- reduceACase sumVal reconAlts newNonDataTy
          Distinct <- getDistinct
          fromSplit split dataVal nonDataVal

simplifyAlt
  :: SplitDataNonData n
  -> SType o
  -> (forall o'. (Emits o', DExt o o') => SAtom o' -> SimplifyM i o' (CAtom o'))
  -> SimplifyM i o (Alt SimpIR o, SType o, ReconstructAtom o)
simplifyAlt split ty cont = do
  withFreshBinder noHint ty \b -> do
    ab <- buildScoped $ cont $ sink $ toAtom $ binderVar b
    (body, recon) <- refreshAbs ab \decls result -> do
      let locals = toScopeFrag b >>> toScopeFrag decls
      -- TODO: this might be too cautious. The type only needs to
      -- be hoistable above the decls. In principle it can still
      -- mention vars from the lambda binders.
      Distinct <- getDistinct
      (resultData, resultNonData) <- toSplit split result
      (newResult, reconAbs) <- telescopicCapture locals resultNonData
      return (Abs decls (PairVal resultData newResult), LamRecon reconAbs)
    body' <- mkBlock body
    PairTy _ nonDataType <- return $ getType body'
    let nonDataType' = ignoreHoistFailure $ hoist b nonDataType
    return (Abs b body', nonDataType', recon)

simplifyApp :: Emits o => CType o -> ConcreteCAtom o -> [CAtom o] -> SimplifyM i o (CAtom o)
simplifyApp resultTy f xs = case f of
  CCCon (WithSubst s con) -> case con of
    Lam (CoreLamExpr _ lam) -> withSubst s $ withInstantiated lam xs \body -> simplifyExpr body
    _ -> error "not a function"
  CCFun ccFun -> case ccFun of
    CCLiftSimpFun _ lam -> do
      xs' <- dropSubst $ mapM toDataAtom xs
      result <- instantiate lam xs' >>= emit
      liftSimpAtom resultTy result
    CCNoInlineFun v _ _ -> simplifyTopFunApp v xs
    CCFFIFun _ f' -> do
      xs' <- dropSubst $ mapM toDataAtom xs
      liftSimpAtom resultTy =<< naryTopApp f' xs'
  CCACase aCase -> forceACase aCase \f' -> simplifyApp (sink resultTy) f' (sink <$> xs)
  CCTabLam _     -> error "not a function"
  CCLiftSimp _ _ -> error "not a function"

simplifyTopFunApp :: Emits n => CAtomVar n -> [CAtom n] -> SimplifyM i n (CAtom n)
simplifyTopFunApp fName xs = do
  fTy@(TyCon (Pi piTy)) <- return $ getType fName
  resultTy <- typeOfApp fTy xs
  isData resultTy >>= \case
    True -> do
      (xsGeneralized, runtimeArgs) <- generalizeArgs piTy xs
      let spec = AppSpecialization fName xsGeneralized
      Just specializedFunction <- getSpecializedFunction spec >>= emitHoistedEnv
      runtimeArgs' <- dropSubst $ mapM toDataAtom runtimeArgs
      liftSimpAtom resultTy =<< naryTopApp specializedFunction runtimeArgs'
    False ->
      -- TODO: we should probably just fall back to inlining in this case,
      -- especially if we want make everything @noinline by default.
      error $ "can't specialize " ++ pprint fName ++ " " ++ pprint xs

getSpecializedFunction :: EnvReader m => SpecializationSpec n -> m n (Abs TopEnvFrag TopFunName n)
getSpecializedFunction s = do
  querySpecializationCache s >>= \case
    Just name -> return $ Abs emptyOutFrag name
    Nothing -> liftTopBuilderHoisted $ emitSpecialization (sink s)

emitSpecialization :: (Mut n, TopBuilder m) => SpecializationSpec n -> m n (TopFunName n)
emitSpecialization s = do
  let hint = getNameHint s
  fCore <- specializedFunCoreDefinition s
  fSimp <- simplifyTopFunction fCore
  name <- emitTopFunBinding hint (Specialization s) fSimp
  extendSpecializationCache s name
  return name

specializedFunCoreDefinition :: (Mut n, TopBuilder m) => SpecializationSpec n -> m n (TopLam CoreIR n)
specializedFunCoreDefinition (AppSpecialization f (Abs bs staticArgs)) = do
  (asTopLam =<<) $ liftBuilder $ buildLamExpr (EmptyAbs bs) \runtimeArgs -> do
    -- This avoids an infinite loop. Otherwise, in simplifyTopFunction,
    -- where we eta-expand and try to simplify `App f args`, we would see `f` as a
    -- "noinline" function and defer its simplification.
    NoinlineFun _ f' <- lookupAtomName (atomVarName (sink f))
    ListE staticArgs' <- applyRename (bs@@>(atomVarName <$> runtimeArgs)) staticArgs
    naryApp f' staticArgs'

simplifyTabApp ::Emits o => ConcreteCAtom o -> CAtom o -> SimplifyM i o (CAtom o)
simplifyTabApp f x = case f of
  CCLiftSimp fTy f' -> do
    f'' <- mkStuck f'
    resultTy <- typeOfTabApp fTy x
    x' <- dropSubst $ toDataAtom x
    liftSimpAtom resultTy =<< tabApp f'' x'
  CCACase aCase -> forceACase aCase \f' -> simplifyTabApp f' (sink x)
  CCTabLam (WithSubst s (PairE _ (Abs b ab))) -> do
    x' <- dropSubst $ toDataAtom x
    withSubst s $ extendSubst (b@>(SubstVal x')) $ substM ab
  _ -> error "not a table"

simplifyIxDict :: Dict CoreIR i -> SimplifyM i o (SDict o)
simplifyIxDict (StuckDict _ stuck) = forceStuck stuck >>= \case
  CCCon (WithSubst s con) -> case con of
    DictConAtom con' -> withSubst s $ simplifyIxDict (DictCon con')
    _ -> error "not a dict"
  CCLiftSimp _ _   -> error "not a dict"
  CCFun      _     -> error "not a dict"
  CCTabLam   _     -> error "not a dict"
  CCACase    _     -> error "not implemented" -- TODO: consider what to do about this
simplifyIxDict (DictCon con) = case con of
  IxFin n -> DictCon <$> IxRawFin <$> toDataAtomAssumeNoDecls n
  IxRawFin n -> DictCon <$> IxRawFin <$> toDataAtomAssumeNoDecls n
  InstanceDict _ _ _ -> do
    d <- DictCon <$> substM con
    (dictAbs, params) <- generalizeIxDict d
    params' <- dropSubst $ mapM toDataAtomAssumeNoDecls params
    sdName <- requireIxDictCache dictAbs
    return $ DictCon $ IxSpecialized sdName params'
  DataData _ -> error "not an Ix dict"

requireIxDictCache
  :: (HoistingTopBuilder TopEnvFrag m) => AbsDict n -> m n (Name SpecializedDictNameC n)
requireIxDictCache dictAbs = do
  queryIxDictCache dictAbs >>= \case
    Just name -> return name
    Nothing -> do
      ab <- liftTopBuilderHoisted do
        dName <- emitBinding "d" $ sink $ SpecializedDictBinding $ SpecializedDict dictAbs Nothing
        updateTopEnv $ ExtendCache $ mempty { ixDictCache = eMapSingleton (sink dictAbs) dName }
        methods <- forM [minBound..maxBound] \method -> simplifyDictMethod (sink dictAbs) method
        updateTopEnv $ FinishDictSpecialization dName methods
        return dName
      maybeD <- emitHoistedEnv ab
      case maybeD of
        Just name -> return name
        Nothing -> error "Couldn't hoist specialized dictionary"
{-# INLINE requireIxDictCache #-}

simplifyDictMethod :: Mut n => AbsDict n -> IxMethod -> TopBuilderM n (TopLam SimpIR n)
simplifyDictMethod absDict@(Abs bs dict) method = do
  ty <- liftEnvReaderM $ ixMethodType method absDict
  lamExpr <- liftBuilder $ buildTopLamFromPi ty \allArgs -> do
    let (extraArgs, methodArgs) = splitAt (nestLength bs) allArgs
    dict' <- applyRename (bs @@> (atomVarName <$> extraArgs)) dict
    emit =<< mkApplyMethod dict' (fromEnum method) (toAtom <$> methodArgs)
  simplifyTopFunction lamExpr

ixMethodType :: IxMethod -> AbsDict n -> EnvReaderM n (PiType CoreIR n)
ixMethodType method absDict = do
  refreshAbs absDict \extraArgBs dict -> do
    CorePiType _ _ methodArgs (EffTy _ resultTy) <- getMethodType dict (fromEnum method)
    let allBs = extraArgBs >>> methodArgs
    return $ PiType allBs (EffTy Pure resultTy)

simplifyAtom :: CAtom i -> SimplifyM i o (CAtom o)
simplifyAtom = substM

-- Assumes first order (args/results are "data", allowing newtypes), monormophic
simplifyLam
  :: LamExpr CoreIR i
  -> SimplifyM i o (LamExpr SimpIR o, Abs (Nest (AtomNameBinder SimpIR)) ReconstructAtom o)
simplifyLam (LamExpr bsTop body) = case bsTop of
  Nest b bs -> withSimplifiedBinder b \b'@(b'':>_) -> do
    (LamExpr bs' body', Abs bsRecon recon) <- simplifyLam $ LamExpr bs body
    return (LamExpr (Nest b' bs') body', Abs (Nest b'' bsRecon) recon)
  Empty -> do
    SimplifiedBlock body' recon <- buildSimplifiedBlock $ simplifyExpr body
    return (LamExpr Empty body', Abs Empty recon)

data SplitDataNonData n = SplitDataNonData
  { dataTy    :: Type SimpIR n
  , nonDataTy :: Type CoreIR n
  , toSplit   :: forall i l . CAtom l -> SimplifyM i l (SAtom l, CAtom l)
  , fromSplit :: forall i l . DExt n l => SAtom l -> CAtom l -> SimplifyM i l (CAtom l) }

-- bijection between that type and a (data, non-data) pair type.
splitDataComponents :: Type CoreIR n -> SimplifyM i n (SplitDataNonData n)
splitDataComponents = \case
  TyCon (ProdType tys) -> do
    splits <- mapM splitDataComponents tys
    return $ SplitDataNonData
      { dataTy    = TyCon $ ProdType $ map dataTy    splits
      , nonDataTy = TyCon $ ProdType $ map nonDataTy splits
      , toSplit = \xProd -> do
          xs <- getUnpackedReduced xProd
          (ys, zs) <- unzip <$> forM (zip xs splits) \(x, split) -> toSplit split x
          return (Con $ ProdCon ys, Con $ ProdCon zs)
      , fromSplit = \xsProd ysProd -> do
          xs <- getUnpackedReduced xsProd
          ys <- getUnpackedReduced ysProd
          zs <- forM (zip (zip xs ys) splits) \((x, y), split) -> fromSplit split x y
          return $ Con $ ProdCon zs }
  ty -> tryGetRepType ty >>= \case
    Just repTy -> return $ SplitDataNonData
      { dataTy = repTy
      , nonDataTy = UnitTy
      , toSplit = \x -> (,UnitVal) <$> (dropSubst $ toDataAtomAssumeNoDecls x)
      , fromSplit = \x _ -> liftSimpAtom (sink ty) x }
    Nothing -> return $ SplitDataNonData
      { dataTy = UnitTy
      , nonDataTy = ty
      , toSplit = \x -> return (UnitVal, x)
      , fromSplit = \_ x -> return x }

buildSimplifiedBlock
  :: (forall o'. (Emits o', DExt o o') => SimplifyM i o' (CAtom o'))
  -> SimplifyM i o (SimplifiedBlock o)
buildSimplifiedBlock cont = do
  Abs decls eitherResult <- buildScoped do
    ans <- cont
    tryAsDataAtom ans >>= \case
      Nothing -> return $ LeftE ans
      Just (dataResult, _) -> do
        ansTy <- return $ getType ans
        return $ RightE (dataResult `PairE` ansTy)
  case eitherResult of
    LeftE ans -> do
      (blockAbs, recon) <- refreshAbs (Abs decls ans) \decls' ans' -> do
        (newResult, reconAbs) <- telescopicCapture (toScopeFrag decls') ans'
        return (Abs decls' newResult, LamRecon reconAbs)
      block' <- mkBlock blockAbs
      return $ SimplifiedBlock block' recon
    RightE (ans `PairE` ty) -> do
      let ty' = ignoreHoistFailure $ hoist (toScopeFrag decls) ty
      block <- mkBlock $ Abs decls ans
      return $ SimplifiedBlock block (CoerceRecon ty')

simplifyOp :: Emits o => PrimOp CoreIR i -> SimplifyM i o (CAtom o)
simplifyOp op = case op of
  Hof (TypedHof (EffTy _ ty) hof) -> do
    ty' <- substM ty
    simplifyHof ty' hof
  MemOp    op' -> simplifyGenericOp op'
  VectorOp op' -> simplifyGenericOp op'
  RefOp ref eff -> do
    ref' <- toDataAtom ref
    liftResult =<< simplifyRefOp eff ref'
  BinOp binop x y -> do
    x' <- toDataAtom x
    y' <- toDataAtom y
    liftResult =<< emit (BinOp binop x' y')
  UnOp unOp x -> do
    x' <- toDataAtom x
    liftResult =<< emit (UnOp unOp x')
  MiscOp op' -> case op' of
    ShowAny x -> do
      x' <- simplifyAtom x
      dropSubst $ showAny x' >>= simplifyExpr
    _ -> simplifyGenericOp op'
  where
    liftResult x = do
      ty <- substM $ getType op
      liftSimpAtom ty x

simplifyGenericOp
  :: (GenericOp op, ToExpr (op SimpIR) SimpIR, HasType CoreIR (op CoreIR), Emits o,
      OpConst op CoreIR ~ OpConst op SimpIR)
  => op CoreIR i
  -> SimplifyM i o (CAtom o)
simplifyGenericOp op = do
  ty <- substM $ getType op
  op' <- traverseOp op getRepType toDataAtom (error "shouldn't have lambda left")
  liftSimpAtom ty =<< emit op'
{-# INLINE simplifyGenericOp #-}

pattern CoerceReconAbs :: Abs (Nest b) ReconstructAtom n
pattern CoerceReconAbs <- Abs _ (CoerceRecon _)

applyDictMethod :: Emits o => CType o -> CDict o -> Int -> [CAtom o] -> SimplifyM i o (CAtom o)
applyDictMethod resultTy d i methodArgs = case d of
  DictCon (InstanceDict _ instanceName instanceArgs) -> dropSubst do
    instanceArgs' <- mapM simplifyAtom instanceArgs
    instanceDef <- lookupInstanceDef instanceName
    withInstantiated instanceDef instanceArgs' \(PairE _ body) -> do
      let InstanceBody _ methods = body
      let method = methods !! i
      method' <- forceConstructor method
      simplifyApp resultTy method' methodArgs
  DictCon (IxFin n) -> applyIxFinMethod (toEnum i) n methodArgs
  d' -> error $ "Not a simplified dict: " ++ pprint d'
  where
    applyIxFinMethod :: EnvReader m => IxMethod -> CAtom n -> [CAtom n] -> m n (CAtom n)
    applyIxFinMethod method n args = do
      case (method, args) of
        (Size, []) -> return n  -- result : Nat
        (Ordinal, [ix]) -> reduceUnwrap ix -- result : Nat
        (UnsafeFromOrdinal, [ix]) -> return $ toAtom $ NewtypeCon (FinCon n) ix
        _ -> error "bad ix args"

simplifyHof :: Emits o => CType o -> Hof CoreIR i -> SimplifyM i o (CAtom o)
simplifyHof resultTy = \case
  For d (IxType ixTy ixDict) lam -> do
    (lam', Abs (UnaryNest bIx) recon) <- simplifyLam lam
    ixTy' <- getRepType ixTy
    ixDict' <- simplifyIxDict ixDict
    ans <- emitHof $ For d (IxType ixTy' ixDict') lam'
    case recon of
      CoerceRecon _ -> liftSimpAtom resultTy ans
      LamRecon (Abs bsClosure reconResult) -> do
        ab <- buildAbs noHint ixTy' \i -> do
          xs <- unpackTelescope bsClosure =<< reduceTabApp (sink ans) (toAtom i)
          applySubst (bIx@>Rename (atomVarName i) <.> bsClosure @@> map SubstVal xs) reconResult
        TyCon (TabPi resultTy') <- return resultTy
        mkStuck $ TabLam $ resultTy' `PairE` ab
  While body -> do
    SimplifiedBlock body' (CoerceRecon _) <- buildSimplifiedBlock $ simplifyExpr body
    result <- emitHof $ While body'
    liftSimpAtom resultTy result
  RunReader r lam -> do
    r' <- toDataAtom r
    (lam', Abs b recon) <- simplifyLam lam
    ans <- emitHof $ RunReader r' lam'
    let recon' = ignoreHoistFailure $ hoist b recon
    applyRecon recon' ans
  RunWriter Nothing (BaseMonoid e combine) lam -> do
    LamExpr (BinaryNest h (_:>RefTy _ wTy)) _ <- return lam
    wTy' <- substM $ ignoreHoistFailure $ hoist h wTy
    e' <- toDataAtom e
    (combine', CoerceReconAbs) <- simplifyLam combine
    (lam', Abs b recon) <- simplifyLam lam
    (ans, w) <- fromPair =<< emitHof (RunWriter Nothing (BaseMonoid e' combine') lam')
    let recon' = ignoreHoistFailure $ hoist b recon
    ans' <- applyRecon recon' ans
    w' <- liftSimpAtom wTy' w
    return $ PairVal ans' w'
  RunWriter _ _ _ -> error "Shouldn't see a RunWriter with a dest in Simplify"
  RunState Nothing s lam -> do
    s' <- toDataAtom s
    sTy <- substM $ getType s
    (lam', Abs b recon) <- simplifyLam lam
    resultPair <- emitHof $ RunState Nothing s' lam'
    (ans, sOut) <- fromPair resultPair
    let recon' = ignoreHoistFailure $ hoist b recon
    ans' <- applyRecon recon' ans
    sOut' <- liftSimpAtom sTy sOut
    return $ PairVal ans' sOut'
  RunState _ _ _ -> error "Shouldn't see a RunState with a dest in Simplify"
  RunIO body -> do
    SimplifiedBlock body' recon <- buildSimplifiedBlock $ simplifyExpr body
    ans <- emitHof $ RunIO body'
    applyRecon recon ans
  RunInit body -> do
    SimplifiedBlock body' recon <- buildSimplifiedBlock $ simplifyExpr body
    ans <- emitHof $ RunInit body'
    applyRecon recon ans
  Linearize lam x -> do
    x' <- toDataAtom x
    -- XXX: we're ignoring the result type here, which only makes sense if we're
    -- dealing with functions on simple types.
    (lam', recon) <- simplifyLam lam
    CoerceReconAbs <- return recon
    (result, linFun) <- liftDoubleBuilderToSimplifyM $ linearize lam' x'
    PairTy lamResultTy linFunTy <- return resultTy
    result' <- liftSimpAtom lamResultTy result
    linFun' <- liftSimpFun linFunTy linFun
    return $ PairVal result' linFun'
  Transpose lam x -> do
    (lam', CoerceReconAbs) <- simplifyLam lam
    x' <- toDataAtom x
    result <- transpose lam' x'
    liftSimpAtom resultTy result
  CatchException _ body-> do
    SimplifiedBlock body' recon <- buildSimplifiedBlock $ simplifyExpr body
    block <- liftBuilder $ runSubstReaderT idSubst $ buildBlock $
      exceptToMaybeExpr body'
    result <- emit block
    case recon of
      CoerceRecon ty -> do
        maybeTy <- makePreludeMaybeTy ty
        liftSimpAtom maybeTy result
      LamRecon reconAbs -> fmapMaybe result (applyReconAbs $ sink reconAbs)

-- takes an internal SimpIR Maybe to a CoreIR "prelude Maybe"
fmapMaybe
  :: SAtom n -> (forall l. DExt n l => SAtom l -> SimplifyM i l (CAtom l))
  -> SimplifyM i n (CAtom n)
fmapMaybe scrut f = do
  ~(MaybeTy justTy) <- return $ getType scrut
  (justAlt, resultJustTy) <- withFreshBinder noHint justTy \b -> do
    result <- f (toAtom $ binderVar b)
    resultTy <- return $ ignoreHoistFailure $ hoist b (getType result)
    result' <- preludeJustVal result
    return (Abs b result', resultTy)
  nothingAlt <- buildAbs noHint UnitTy \_ -> preludeNothingVal $ sink resultJustTy
  resultMaybeTy <- makePreludeMaybeTy resultJustTy
  reduceACase scrut [nothingAlt, justAlt] resultMaybeTy

-- This is wrong! The correct implementation is below. And yet there's some
-- compensatory bug somewhere that means that the wrong answer works and the
-- right answer doesn't. Need to investigate.
preludeJustVal :: EnvReader m => CAtom n -> m n (CAtom n)
preludeJustVal x = return x
  -- xTy <- getType x
  -- con <- preludeMaybeNewtypeCon xTy
  -- return $ NewtypeCon con (JustAtom xTy x)

preludeNothingVal :: EnvReader m => CType n -> m n (CAtom n)
preludeNothingVal ty = do
  con <- preludeMaybeNewtypeCon ty
  return $ Con $ NewtypeCon con (NothingAtom ty)

preludeMaybeNewtypeCon :: EnvReader m => CType n -> m n (NewtypeCon n)
preludeMaybeNewtypeCon ty = do
  ~(Just (UTyConVar tyConName)) <- lookupSourceMap "Maybe"
  TyConDef sn _ _ _ <- lookupTyCon tyConName
  let params = TyConParams [Explicit] [toAtom ty]
  return $ UserADTData sn tyConName params

liftSimpFun :: EnvReader m => Type CoreIR n -> LamExpr SimpIR n -> m n (CAtom n)
liftSimpFun (TyCon (Pi piTy)) f = mkStuck $ LiftSimpFun piTy f
liftSimpFun _ _ = error "not a pi type"

-- === simplifying custom linearizations ===

linearizeTopFun :: (Mut n, Fallible1 m, TopBuilder m) => LinearizationSpec n -> m n (TopFunName n, TopFunName n)
linearizeTopFun spec = do
  -- TODO: package up this caching pattern so we don't keep reimplementing it
  queryLinearizationCache spec >>= \case
    Just (primal, tangent) -> return (primal, tangent)
    Nothing -> do
      (primal, tangent) <- linearizeTopFunNoCache spec
      extendLinearizationCache spec (primal, tangent)
      return (primal, tangent)

linearizeTopFunNoCache :: (Mut n, TopBuilder m) => LinearizationSpec n -> m n (TopFunName n, TopFunName n)
linearizeTopFunNoCache spec@(LinearizationSpec f actives) = do
  TopFunBinding ~(DexTopFun _ lam _) <- lookupEnv f
  PairE fPrimal fTangent <- liftSimplifyM $ tryGetCustomRule (sink f) >>= \case
    Just (absParams, rule) -> simplifyCustomLinearization (sink absParams) actives (sink rule)
    Nothing -> liftM toPairE $ liftDoubleBuilderToSimplifyM $ linearizeTopLam (sink lam) actives
  fTangentT <- transposeTopFun fTangent
  fPrimal'   <- emitTopFunBinding "primal"   (LinearizationPrimal  spec) fPrimal
  fTangent'  <- emitTopFunBinding "tangent"  (LinearizationTangent spec) fTangent
  fTangentT' <- emitTopFunBinding "tangent"  (LinearizationTangent spec) fTangentT
  updateTransposeRelation fTangent' fTangentT'
  return (fPrimal', fTangent')

tryGetCustomRule :: EnvReader m => TopFunName n -> m n (Maybe (Abstracted CoreIR (ListE CAtom) n, AtomRules n))
tryGetCustomRule f' = do
  ~(TopFunBinding f) <- lookupEnv f'
  case f of
    DexTopFun def _ _ -> case def of
      Specialization (AppSpecialization fCore absParams) ->
        fmap (absParams,) <$> lookupCustomRules (atomVarName fCore)
      _ -> return Nothing
    _ -> return Nothing

type Linearized = Abs (Nest SBinder)    -- primal args
                      (Abs (Nest SDecl) -- primal decls
                      (PairE SAtom      -- primal result
                             SLam))     -- tangent function

simplifyCustomLinearization
  :: Abstracted CoreIR (ListE CAtom) n -> [Active] -> AtomRules n
  -> SimplifyM i n (PairE STopLam STopLam n)
simplifyCustomLinearization (Abs runtimeBs staticArgs) actives rule = do
  CustomLinearize nImplicit nExplicit zeros fCustom <- return rule
  linearized <- withSimplifiedBinders runtimeBs \runtimeBs' runtimeArgs -> do
      Abs runtimeBs' <$> buildScoped do
        ListE staticArgs' <- instantiate (sink $ Abs runtimeBs staticArgs) (sink <$> runtimeArgs)
        fCustom' <- sinkM fCustom
        -- TODO: give a HasType instance to ConcreteCAtom
        resultTy <- typeOfApp (getType fCustom') staticArgs'
        fCustom'' <- dropSubst $ forceConstructor fCustom'
        pairResult <- dropSubst $ simplifyApp resultTy fCustom'' staticArgs'
        (primalResult, fLin) <- fromPairReduced pairResult
        primalResult' <- dropSubst $ toDataAtom primalResult
        let explicitPrimalArgs = drop nImplicit staticArgs'
        allTangentTys <- forM explicitPrimalArgs \primalArg -> do
          tangentType =<< dropSubst (getRepType (getType primalArg))
        let actives' = drop (length actives - nExplicit) actives
        activeTangentTys <- catMaybes <$> forM (zip allTangentTys actives')
          \(t, active) -> return case active of True  -> Just t; False -> Nothing
        fLin' <- buildUnaryLamExpr "t" (toType $ ProdType activeTangentTys) \activeTangentArg -> do
          activeTangentArgs <- getUnpacked $ toAtom activeTangentArg
          ListE allTangentTys' <- sinkM $ ListE allTangentTys
          tangentArgs <- buildTangentArgs zeros (zip allTangentTys' actives') activeTangentArgs
          -- TODO: we're throwing away core type information here. Once we
          -- support core-level tangent types we should make an effort to
          -- correctly restore the core types before applying `fLin`. Right now,
          -- a custom linearization defined for a function on ADTs will
          -- not work.
          fLin' <- sinkM fLin
          TyCon (Pi (CorePiType _ _ bs _)) <- return $ getType fLin'
          let tangentCoreTys = fromNonDepNest bs
          tangentArgs' <- zipWithM liftSimpAtom tangentCoreTys tangentArgs
          resultTyTangent <- typeOfApp (getType fLin') tangentArgs'
          fLin'' <- dropSubst $ forceConstructor fLin'
          tangentResult <- dropSubst $ simplifyApp resultTyTangent fLin'' tangentArgs'
          dropSubst $ toDataAtom tangentResult
        return $ PairE primalResult' fLin'
  PairE primalFun tangentFun <- defuncLinearized linearized
  primalFun' <- asTopLam primalFun
  tangentFun' <- asTopLam tangentFun
  return $ PairE primalFun' tangentFun'
 where
    buildTangentArgs :: Emits n => SymbolicZeros -> [(SType n, Active)] -> [SAtom n] -> SimplifyM i n [SAtom n]
    buildTangentArgs _ [] [] = return []
    buildTangentArgs zeros ((t, False):tys) activeArgs = do
      inactiveArg <- case zeros of
        SymbolicZeros -> symbolicTangentZero t
        InstantiateZeros -> zeroAt t
      rest <- buildTangentArgs zeros tys activeArgs
      return $ inactiveArg:rest
    buildTangentArgs zeros ((_, True):tys) (activeArg:activeArgs) = do
      activeArg' <- case zeros of
        SymbolicZeros -> symbolicTangentNonZero activeArg
        InstantiateZeros -> return activeArg
      rest <- buildTangentArgs zeros tys activeArgs
      return $ activeArg':rest
    buildTangentArgs _ _ _ = error "zip error"

    fromNonDepNest :: Nest CBinder n l -> [CType n]
    fromNonDepNest Empty = []
    fromNonDepNest (Nest b bs) =
      case ignoreHoistFailure $ hoist b (Abs bs UnitE) of
        Abs bs' UnitE -> binderType b : fromNonDepNest bs'

defuncLinearized :: EnvReader m => Linearized n -> m n (PairE SLam SLam n)
defuncLinearized ab = liftBuilder $ refreshAbs ab \bs ab' -> do
  (declsAndResult, reconAbs, residualsTangentsBs) <-
    refreshAbs ab' \decls (PairE primalResult fLin) -> do
      (residuals, reconAbs) <- telescopicCapture (toScopeFrag decls) fLin
      let rTy = getType residuals
      LamExpr tBs _ <- return fLin
      residualsTangentsBs <- withFreshBinder "residual" rTy \rB -> do
        Abs tBs' UnitE <- sinkM $ Abs tBs UnitE
        return $ Abs (Nest rB tBs') UnitE
      residualsTangentsBs' <- return $ ignoreHoistFailure $ hoist decls residualsTangentsBs
      return (Abs decls (PairVal primalResult residuals), reconAbs, residualsTangentsBs')
  primalFun <- LamExpr bs <$> mkBlock declsAndResult
  LamExpr residualAndTangentBs tangentBody <- buildLamExpr residualsTangentsBs \(residuals:tangents) -> do
    LamExpr tangentBs' body <- applyReconAbs (sink reconAbs) (toAtom residuals)
    applyRename (tangentBs' @@> (atomVarName <$> tangents)) body >>= emit
  let tangentFun = LamExpr (bs >>> residualAndTangentBs) tangentBody
  return $ PairE primalFun tangentFun

-- === exception-handling pass ===

type HandlerM = SubstReaderT AtomSubstVal (BuilderM SimpIR)

exceptToMaybeBlock :: Emits o => SType o -> SBlock i -> HandlerM i o (SAtom o)
exceptToMaybeBlock ty (Abs Empty result) = do
  result' <- exceptToMaybeExpr result
  return $ JustAtom ty result'
exceptToMaybeBlock resultTy (Abs (Nest (Let b (DeclBinding _ rhs)) decls) finalResult) = do
  maybeResult <- exceptToMaybeExpr rhs
  case maybeResult of
    -- This case is just an optimization (but an important one!)
    JustAtom _ x  ->
      extendSubst (b@> SubstVal x) $ exceptToMaybeBlock resultTy (Abs decls finalResult)
    _ -> emitMaybeCase maybeResult (MaybeTy resultTy)
          (return $ NothingAtom $ sink resultTy)
          (\v -> extendSubst (b@> SubstVal v) $
                   exceptToMaybeBlock (sink resultTy) (Abs decls finalResult))

exceptToMaybeExpr :: Emits o => SExpr i -> HandlerM i o (SAtom o)
exceptToMaybeExpr expr = case expr of
  Block (EffTy _ ty) body -> do
    ty' <- substM ty
    exceptToMaybeBlock ty' body
  Case e alts (EffTy _ resultTy) -> do
    e' <- substM e
    resultTy' <- substM $ MaybeTy resultTy
    buildCase e' resultTy' \i v -> do
      Abs b body <- return $ alts !! i
      extendSubst (b @> SubstVal v) do
        exceptToMaybeExpr body
  Atom x -> do
    x' <- substM x
    let ty = getType x'
    return $ JustAtom ty x'
  PrimOp (Hof (TypedHof _ (For ann ixTy' (UnaryLamExpr b body)))) -> do
    ixTy <- substM ixTy'
    maybes <- buildFor (getNameHint b) ann ixTy \i -> do
      extendSubst (b@>Rename (atomVarName i)) $ exceptToMaybeExpr body
    catMaybesE maybes
  PrimOp (MiscOp (ThrowException _)) -> do
    ty <- substM $ getType expr
    return $ NothingAtom ty
  PrimOp (Hof (TypedHof _ (RunState Nothing s lam))) -> do
    s' <- substM s
    BinaryLamExpr h ref body <- return lam
    result  <- emitRunState noHint s' \h' ref' ->
      extendSubst (h @> Rename (atomVarName h') <.> ref @> Rename (atomVarName ref')) do
        exceptToMaybeExpr body
    (maybeAns, newState) <- fromPair result
    a <- substM $ getType expr
    emitMaybeCase maybeAns (MaybeTy a)
       (return $ NothingAtom $ sink a)
       (\ans -> return $ JustAtom (sink a) $ PairVal ans (sink newState))
  PrimOp (Hof (TypedHof (EffTy _ resultTy) (RunWriter Nothing monoid (BinaryLamExpr h ref body)))) -> do
    monoid' <- substM monoid
    PairTy _ accumTy <- substM resultTy
    result <- emitRunWriter noHint accumTy monoid' \h' ref' ->
      extendSubst (h @> Rename (atomVarName h') <.> ref @> Rename (atomVarName ref')) do
        exceptToMaybeExpr body
    (maybeAns, accumResult) <- fromPair result
    a <- substM $ getType expr
    emitMaybeCase maybeAns (MaybeTy a)
      (return $ NothingAtom $ sink a)
      (\ans -> return $ JustAtom (sink a) $ PairVal ans (sink accumResult))
  PrimOp (Hof (TypedHof _ (While body))) -> runMaybeWhile $ exceptToMaybeExpr body
  _ -> do
    expr' <- substM expr
    case hasExceptions expr' of
      True -> error $ "Unexpected exception-throwing expression: " ++ pprint expr
      False -> do
        v <- emit expr'
        let ty = getType v
        return $ JustAtom ty v

hasExceptions :: SExpr n -> Bool
hasExceptions expr = case getEffects expr of
  EffectRow effs NoTail -> ExceptionEffect `eSetMember` effs

-- === instances ===

instance GenericE ReconstructAtom where
  type RepE ReconstructAtom = EitherE2 (Type CoreIR) (ReconAbs SimpIR CAtom)

  fromE = \case
    CoerceRecon ty -> Case0 ty
    LamRecon ab    -> Case1 ab
  {-# INLINE fromE #-}
  toE = \case
    Case0 ty -> CoerceRecon ty
    Case1 ab -> LamRecon ab
    _ -> error "impossible"
  {-# INLINE toE #-}

instance SinkableE  ReconstructAtom
instance HoistableE ReconstructAtom
instance RenameE    ReconstructAtom

instance Pretty (ReconstructAtom n) where
  pretty (CoerceRecon ty) = "Coercion reconstruction: " <> pretty ty
  pretty (LamRecon ab) = "Reconstruction abs: " <> pretty ab

-- === GHC performance hacks ===

-- Note [Confuse GHC]
-- I can't explain this, but for some reason using this function in strategic
-- places makes GHC produce significantly better code. If we define
--
-- simplifyAtom = \case
--   ...
--   Con con -> traverse simplifyAtom con
--   ...
--
-- then GHC is reluctant to generate a fast-path worker function for simplifyAtom
-- that would return unboxed tuples, because (at least that's my guess) it's afraid
-- that it will have to allocate a reader closure for the traverse, which does not
-- get inlined. For some reason writing the `confuseGHC >>= \_ -> case atom of ...`
-- makes GHC do the right thing, i.e. generate unboxed worker + a tiny wrapper that
-- allocates -- a closure to be passed into traverse.
--
-- What's so special about this, I don't know. `return ()` is insufficient and doesn't
-- make the optimization go through. I'll just take the win for now...
--
-- NB: We should revise this whenever we upgrade to a newer GHC version.
confuseGHC :: SimplifyM i o (DistinctEvidence o)
confuseGHC = getDistinct
{-# INLINE confuseGHC #-}
