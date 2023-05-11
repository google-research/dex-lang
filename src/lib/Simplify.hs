-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module Simplify
  ( simplifyTopBlock, simplifyTopFunction, SimplifiedBlock (..), ReconstructAtom (..), applyReconTop,
    linearizeTopFun) where

import Control.Category ((>>>))
import Control.Monad
import Control.Monad.Reader
import Data.Maybe
import Data.Text.Prettyprint.Doc (Pretty (..), hardline)

import Builder
import CheapReduction
import CheckType (CheckableE (..), isData)
import Core
import Err
import Generalize
import IRVariants
import Linearize
import Name
import Subst
import Optimize (peepholeOp)
import QueryType
import RuntimePrint
import Transpose
import Types.Core
import Types.Source
import Types.Primitives
import Util (enumerate, foldMapM)

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
  ty <- getType atom
  isData ty >>= \case
    False -> return Nothing
    True -> Just <$> do
      repAtom <- go atom
      return (repAtom, ty)
 where
  go :: Emits n => CAtom n -> SimplifyM i n (SAtom n)
  go = \case
    Var v -> lookupAtomName v >>= \case
      LetBound (DeclBinding _ _ (Atom x)) -> go x
      _ -> error "Shouldn't have irreducible top names left"
    Con con -> Con <$> case con of
      Lit v -> return $ Lit v
      ProdCon xs -> ProdCon <$> mapM go xs
      SumCon  tys tag x -> SumCon <$> mapM getRepType tys <*> pure tag <*> go x
      HeapVal       -> return HeapVal
    PtrVar v        -> return $ PtrVar v
    DepPair x y ty -> do
      DepPairTy ty' <- getRepType $ DepPairTy ty
      DepPair <$> go x <*> go y <*> pure ty'
    ProjectElt UnwrapNewtype x -> go x
    -- TODO: do we need to think about a case like `fst (1, \x.x)`, where
    -- the projection is data but the argument isn't?
    ProjectElt (ProjectProduct i) x -> normalizeProj (ProjectProduct i) =<< go x
    NewtypeCon _ x  -> go x
    SimpInCore x    -> case x of
      LiftSimp _ x' -> return x'
      LiftSimpFun _ _ -> notData
      TabLam _ tabLam -> forceTabLam tabLam
      ACase scrut alts resultTy -> forceACase scrut alts resultTy
    Lam _           -> notData
    DictCon _       -> notData
    Eff _           -> notData
    DictHole _ _ _  -> notData
    TypeAsAtom _    -> notData
    where
      notData = error $ "Not runtime-representable data: " ++ pprint atom

forceTabLam :: Emits n => TabLamExpr n -> SimplifyM i n (SAtom n)
forceTabLam (Abs (b:>ixTy) ab) =
  buildFor (getNameHint b) Fwd ixTy \v -> do
    Abs decls result <- applyRename (b@>v) ab
    result' <- emitDecls decls result
    toDataAtomIgnoreRecon result'

forceACase :: Emits n => SAtom n -> [Abs SBinder CAtom n] -> CType n -> SimplifyM i n (SAtom n)
forceACase scrut alts resultTy = do
  resultTy' <- getRepType  resultTy
  buildCase scrut resultTy' \i arg -> do
    Abs b result <- return $ alts !! i
    applySubst (b@>SubstVal arg) result >>= toDataAtomIgnoreRecon

tryGetRepType :: Type CoreIR n -> SimplifyM i n (Maybe (SType n))
tryGetRepType t = isData t >>= \case
  False -> return Nothing
  True  -> Just <$> getRepType t

getRepType :: Type CoreIR n -> SimplifyM i n (SType n)
getRepType ty = go ty where
  go :: Type CoreIR n -> SimplifyM i n (SType n)
  go = \case
    TC con -> TC <$> case con of
      BaseType b  -> return $ BaseType b
      ProdType ts -> ProdType <$> mapM go ts
      SumType  ts -> SumType  <$> mapM go ts
      RefType h a -> RefType  <$> toDataAtomIgnoreReconAssumeNoDecls h <*> go a
      TypeKind    -> error $ notDataType
      HeapType    -> return $ HeapType
    DepPairTy (DepPairType expl b@(_:>l) r) -> do
      l' <- go l
      withFreshBinder (getNameHint b) l' \b' -> do
        x <- liftSimpAtom (sink l) (Var $ binderName b')
        r' <- go =<< applySubst (b@>SubstVal x) r
        return $ DepPairTy $ DepPairType expl b' r'
    TabPi (TabPiType (b:>ixTy) bodyTy) -> do
      ixTy' <- simplifyIxType ixTy
      withFreshBinder (getNameHint b) ixTy' \b' -> do
        x <- liftSimpAtom (sink $ ixTypeType ixTy) (Var $ binderName b')
        bodyTy' <- go =<< applySubst (b@>SubstVal x) bodyTy
        return $ TabPi $ TabPiType b' bodyTy'
    NewtypeTyCon con -> do
      (_, ty') <- unwrapNewtypeType con
      go ty'
    Pi _           -> error notDataType
    DictTy _       -> error notDataType
    TyVar _ -> error "Shouldn't have type variables in CoreIR IR with SimpIR builder names"
    ProjectEltTy _ _ -> error "Shouldn't have this left"
    where notDataType = "Not a type of runtime-representable data: " ++ pprint ty

toDataAtom :: Emits n => CAtom n -> SimplifyM i n (SAtom n, Type CoreIR n)
toDataAtom x = tryAsDataAtom x >>= \case
  Just x' -> return x'
  Nothing -> error $ "Not a data atom: " ++ pprint x

simplifyDataAtom :: Emits o => CAtom i -> SimplifyM i o (SAtom o)
simplifyDataAtom x = toDataAtomIgnoreRecon =<< simplifyAtom x

toDataAtomIgnoreRecon :: Emits n => CAtom n -> SimplifyM i n (SAtom n)
toDataAtomIgnoreRecon x = fst <$> toDataAtom x

toDataAtomIgnoreReconAssumeNoDecls :: CAtom n -> SimplifyM i n (SAtom n)
toDataAtomIgnoreReconAssumeNoDecls x = do
  Abs decls result <- buildScoped $ fst <$> toDataAtom (sink x)
  case decls of
    Empty -> return result
    _ -> error "unexpected decls"

withSimplifiedBinders
 :: Nest (Binder CoreIR) o any
 -> (forall o'. DExt o o' => Nest (Binder SimpIR) o o' -> [CAtom o'] -> SimplifyM i o' a)
 -> SimplifyM i o a
withSimplifiedBinders Empty cont = getDistinct >>= \Distinct -> cont Empty []
withSimplifiedBinders (Nest (bCore:>ty) bsCore) cont = do
  simpTy <- getRepType ty
  withFreshBinder (getNameHint bCore) simpTy \bSimp -> do
    x <- liftSimpAtom (sink ty) (Var $ binderName bSimp)
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

-- TODO: figure out why we can't derive this one (here and elsewhere)
instance ScopableBuilder SimpIR (SimplifyM i) where
  buildScoped cont = SimplifyM $ SubstReaderT $ ReaderT \env ->
    buildScoped $ runSubstReaderT (sink env) (runSimplifyM' cont)
  {-# INLINE buildScoped #-}

-- === Top-level API ===

data SimplifiedBlock n = SimplifiedBlock (SBlock n) (ReconstructAtom n)

-- TODO: extend this to work on functions instead of blocks (with blocks still
-- accessible as nullary functions)
simplifyTopBlock :: (TopBuilder m, Mut n) => Block CoreIR n -> m n (SimplifiedBlock n)
simplifyTopBlock block = liftSimplifyM $ buildSimplifiedBlock $ simplifyBlock block
{-# SCC simplifyTopBlock #-}

simplifyTopFunction :: (TopBuilder m, Mut n) => LamExpr CoreIR n -> m n (LamExpr SimpIR n)
simplifyTopFunction f = liftSimplifyM do
  (lam, CoerceReconAbs) <- simplifyLam f
  return lam
{-# SCC simplifyTopFunction #-}

applyReconTop :: (EnvReader m, Fallible1 m) => ReconstructAtom n -> SAtom n -> m n (CAtom n)
applyReconTop = applyRecon

instance GenericE SimplifiedBlock where
  type RepE SimplifiedBlock = PairE SBlock ReconstructAtom
  fromE (SimplifiedBlock block recon) = PairE block recon
  {-# INLINE fromE #-}
  toE   (PairE block recon) = SimplifiedBlock block recon
  {-# INLINE toE #-}

instance SinkableE SimplifiedBlock
instance RenameE SimplifiedBlock
instance HoistableE SimplifiedBlock
instance CheckableE SimpIR SimplifiedBlock where
  checkE (SimplifiedBlock block _) =
    -- TODO: CheckableE instance for the recon too
    checkE block

instance Pretty (SimplifiedBlock n) where
  pretty (SimplifiedBlock block recon) =
    pretty block <> hardline <> pretty recon

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
  Nest (Let b (DeclBinding _ _ expr)) rest -> do
    let hint = (getNameHint b)
    x <- withSubst s $ simplifyExpr hint expr
    simpDeclsSubst (s <>> (b@>SubstVal x)) rest

simplifyExpr :: Emits o => NameHint -> Expr CoreIR i -> SimplifyM i o (CAtom o)
simplifyExpr hint expr = confuseGHC >>= \_ -> case expr of
  App f xs -> do
    xs' <- mapM simplifyAtom xs
    simplifyApp hint f xs'
  TabApp f xs -> do
    xs' <- mapM simplifyAtom xs
    f'  <- simplifyAtom f
    simplifyTabApp f' xs'
  Atom x -> simplifyAtom x
  PrimOp  op  -> simplifyOp hint op
  ApplyMethod dict i xs -> do
    xs' <- mapM simplifyAtom xs
    dict' <- simplifyAtom dict
    applyDictMethod dict' i xs'
  TabCon _ ty xs -> do
    ty' <- substM ty
    tySimp <- getRepType ty'
    xs' <- forM xs \x -> simplifyDataAtom x
    liftSimpAtom ty' =<< emitExpr (TabCon Nothing tySimp xs')
  Case scrut alts resultTy _ -> do
    scrut' <- simplifyAtom scrut
    resultTy' <- substM resultTy
    defuncCaseCore scrut' resultTy' \i x -> do
      Abs b body <- return $ alts !! i
      extendSubst (b@>SubstVal x) $ simplifyBlock body

simplifyRefOp :: Emits o => RefOp CoreIR i -> SAtom o -> SimplifyM i o (SAtom o)
simplifyRefOp op ref = case op of
  MExtend (BaseMonoid em cb) x -> do
    em'  <- simplifyDataAtom em
    x'   <- simplifyDataAtom x
    (cb', CoerceReconAbs) <- simplifyLam cb
    emitRefOp $ MExtend (BaseMonoid em' cb') x'
  MGet   -> emitOp $ RefOp ref MGet
  MPut x -> do
    x' <- simplifyDataAtom x
    emitRefOp $ MPut x'
  MAsk   -> emitRefOp MAsk
  IndexRef x -> do
    x' <- simplifyDataAtom x
    emitRefOp $ IndexRef x'
  ProjRef (ProjectProduct i) -> emitRefOp $ ProjRef (ProjectProduct i)
  ProjRef UnwrapNewtype -> return ref
  where emitRefOp op' = emitOp $ RefOp ref op'

caseComputingEffs
  :: forall m n r. (MonadFail1 m, EnvReader m, IRRep r)
  => Atom r n -> [Alt r n] -> Type r n -> m n (Expr r n)
caseComputingEffs scrut alts resultTy = do
  Case scrut alts resultTy <$> foldMapM getEffects alts
{-# INLINE caseComputingEffs #-}

defuncCaseCore :: Emits o
  => Atom CoreIR o -> Type CoreIR o
  -> (forall o'. (Emits o', DExt o o') => Int -> CAtom o' -> SimplifyM i o' (CAtom o'))
  -> SimplifyM i o (CAtom o)
defuncCaseCore scrut resultTy cont = do
  tryAsDataAtom scrut >>= \case
    Just (scrutSimp, _) -> do
      altBinderTys <- caseAltsBinderTys =<< getType scrut
      defuncCase scrutSimp resultTy \i x -> do
        let xCoreTy = altBinderTys !! i
        x' <- liftSimpAtom (sink xCoreTy) x
        cont i x'
    Nothing -> case trySelectBranch scrut of
      Just (i, arg) -> getDistinct >>= \Distinct -> cont i arg
      Nothing -> go scrut where
        go = \case
          SimpInCore (ACase scrutSimp alts _) -> do
            defuncCase scrutSimp resultTy \i x -> do
              Abs altb altAtom <- return $ alts !! i
              altAtom' <- applySubst (altb @> SubstVal x) altAtom
              cont i altAtom'
          NewtypeCon con scrut' | isSumCon con -> go scrut'
          _ -> nope
        nope = error $ "Don't know how to scrutinize non-data " ++ pprint scrut

defuncCase :: Emits o
  => Atom SimpIR o -> Type CoreIR o
  -> (forall o'. (Emits o', DExt o o') => Int -> SAtom o' -> SimplifyM i o' (CAtom o'))
  -> SimplifyM i o (CAtom o)
defuncCase scrut resultTy cont = do
  case trySelectBranch scrut of
    Just (i, arg) -> getDistinct >>= \Distinct -> cont i arg
    Nothing -> do
      scrutTy <- getType scrut
      altBinderTys <- caseAltsBinderTys scrutTy
      tryGetRepType resultTy >>= \case
        Just resultTyData -> do
          alts' <- forM (enumerate altBinderTys) \(i, bTy) -> do
            buildAbs noHint bTy \x -> do
              buildBlock $ cont i (sink $ Var x) >>= toDataAtomIgnoreRecon
          caseExpr <- caseComputingEffs scrut alts' resultTyData
          emitExpr caseExpr >>= liftSimpAtom resultTy
        Nothing -> do
          split <- splitDataComponents resultTy
          (alts', recons) <- unzip <$> forM (enumerate altBinderTys) \(i, bTy) -> do
             simplifyAlt split bTy $ cont i
          closureTys <- mapM getAltNonDataTy alts'
          let closureSumTy = SumTy closureTys
          let newNonDataTy = nonDataTy split
          alts'' <- forM (enumerate alts') \(i, alt) -> injectAltResult closureTys i alt
          caseExpr <- caseComputingEffs scrut alts'' (PairTy (dataTy split) closureSumTy)
          caseResult <- emitExpr $ caseExpr
          (dataVal, sumVal) <- fromPair caseResult
          reconAlts <- forM (zip closureTys recons) \(ty, recon) ->
            buildAbs noHint ty \v -> applyRecon (sink recon) (Var v)
          let nonDataVal = SimpInCore $ ACase sumVal reconAlts newNonDataTy
          Distinct <- getDistinct
          fromSplit split dataVal nonDataVal

simplifyAlt
  :: SplitDataNonData n
  -> SType o
  -> (forall o'. (Emits o', DExt o o') => SAtom o' -> SimplifyM i o' (CAtom o'))
  -> SimplifyM i o (Alt SimpIR o, ReconstructAtom o)
simplifyAlt split ty cont = fromPairE <$> do
  withFreshBinder noHint ty \b -> do
    ab <- buildScoped $ cont $ sink $ Var $ binderName b
    (resultWithDecls, recon) <- refreshAbs ab \decls result -> do
      let locals = toScopeFrag b >>> toScopeFrag decls
      -- TODO: this might be too cautious. The type only needs to
      -- be hoistable above the decls. In principle it can still
      -- mention vars from the lambda binders.
      Distinct <- getDistinct
      (resultData, resultNonData) <- toSplit split result
      (newResult, reconAbs) <- telescopicCapture locals resultNonData
      return (Abs decls (PairVal resultData newResult), LamRecon reconAbs)
    block <- makeBlockFromDecls resultWithDecls
    return $ PairE (Abs b block) recon

getAltNonDataTy :: EnvReader m => Alt SimpIR n -> m n (SType n)
getAltNonDataTy (Abs bs body) = liftSubstEnvReaderM do
  substBinders bs \bs' -> do
    ~(PairTy _ ty) <- getTypeSubst body
    -- Result types of simplified abs should be hoistable past binder
    return $ ignoreHoistFailure $ hoist bs' ty

simplifyApp :: forall i o. Emits o
  => NameHint -> CAtom i -> [CAtom o] -> SimplifyM i o (CAtom o)
simplifyApp hint f xs =  case f of
  Lam (CoreLamExpr _ lam) -> fast lam
  _ -> slow =<< simplifyAtomAndInline f
  where
    fast :: LamExpr CoreIR i' -> SimplifyM i' o (CAtom o)
    fast (LamExpr bs body) = extendSubst (bs@@>(SubstVal<$>xs)) $ simplifyBlock body

    slow :: CAtom o -> SimplifyM i o (CAtom o)
    slow = \case
      Lam (CoreLamExpr _ lam) -> dropSubst $ fast lam
      SimpInCore (ACase e alts ty) -> dropSubst do
        resultTy <- getAppType ty xs
        defuncCase e resultTy \i x -> do
          Abs b body <- return $ alts !! i
          extendSubst (b@>SubstVal x) do
            xs' <- mapM sinkM xs
            simplifyApp hint body xs'
      SimpInCore (LiftSimpFun (CorePiType _ bs _ resultTy) (LamExpr bs' body)) -> do
        let resultTy' = ignoreHoistFailure $ hoist bs resultTy
        xs' <- mapM toDataAtomIgnoreRecon xs
        body' <- applySubst (bs'@@>map SubstVal xs') body
        liftSimpAtom resultTy' =<< emitBlock body'
      Var v -> do
        lookupAtomName v >>= \case
          NoinlineFun _ _ -> simplifyTopFunApp v xs
          FFIFunBound _ f' -> do
            fTy <- getType $ Var v
            resultTy <- getAppType fTy xs
            xs' <- mapM toDataAtomIgnoreRecon xs
            liftSimpAtom resultTy =<< naryTopApp f' xs'
          b -> error $ "Should only have noinline functions left " ++ pprint b
      atom -> error $ "Unexpected function: " ++ pprint atom

-- | Like `simplifyAtom`, but will try to inline function definitions found
-- in the environment. The only exception is when we're going to differentiate
-- and the function has a custom derivative rule defined.
-- TODO(dougalm): do we still need this?
simplifyAtomAndInline :: CAtom i -> SimplifyM i o (CAtom o)
simplifyAtomAndInline atom = confuseGHC >>= \_ -> case atom of
  Var v -> do
    env <- getSubst
    case env ! v of
      Rename v' -> doInline v'
      SubstVal (Var v') -> doInline v'
      SubstVal x -> return x
  -- This is a hack because we weren't normalize the unwrapping of
  -- `unit_type_scale` in `plot.dx`. We need a better system for deciding how to
  -- normalize and inline.
  ProjectElt i x -> do
    x' <- simplifyAtom x >>= normalizeProj i
    dropSubst $ simplifyAtomAndInline x'
  _ -> simplifyAtom atom >>= \case
    Var v -> doInline v
    ans -> return ans
  where
    doInline v = do
      lookupAtomName v >>= \case
        LetBound (DeclBinding _ _ (Atom x)) -> dropSubst $ simplifyAtomAndInline x
        _ -> return $ Var v

simplifyTopFunApp :: Emits n => CAtomName n -> [CAtom n] -> SimplifyM i n (CAtom n)
simplifyTopFunApp fName xs = do
  fTy@(Pi piTy) <- getType $ Var fName
  resultTy <- getAppType fTy xs
  isData resultTy >>= \case
    True -> do
      (xsGeneralized, runtimeArgs) <- generalizeArgs piTy xs
      let spec = AppSpecialization fName xsGeneralized
      Just specializedFunction <- getSpecializedFunction spec >>= emitHoistedEnv
      runtimeArgs' <- mapM toDataAtomIgnoreRecon runtimeArgs
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

specializedFunCoreDefinition :: (Mut n, TopBuilder m) => SpecializationSpec n -> m n (LamExpr CoreIR n)
specializedFunCoreDefinition (AppSpecialization f (Abs bs staticArgs)) = do
  liftBuilder $ buildLamExpr (EmptyAbs bs) \runtimeArgs -> do
    -- This avoids an infinite loop. Otherwise, in simplifyTopFunction,
    -- where we eta-expand and try to simplify `App f args`, we would see `f` as a
    -- "noinline" function and defer its simplification.
    NoinlineFun _ f' <- lookupAtomName (sink f)
    ListE staticArgs' <- applyRename (bs@@>runtimeArgs) staticArgs
    naryApp f' staticArgs'

simplifyTabApp :: forall i o. Emits o
  => CAtom o -> [CAtom o] -> SimplifyM i o (CAtom o)
simplifyTabApp f [] = return f
simplifyTabApp f@(SimpInCore sic) xs = case sic of
  TabLam _ _ -> do
    case fromNaryTabLam (length xs) f of
      Just (bsCount, Abs bs declsAtom) -> do
        let (xsPref, xsRest) = splitAt bsCount xs
        xsPref' <- mapM toDataAtomIgnoreRecon xsPref
        Abs decls atom <- applySubst (bs@@>(SubstVal <$> xsPref')) declsAtom
        atom' <- emitDecls decls atom
        simplifyTabApp atom' xsRest
      Nothing -> error "should never happen"
  ACase e alts ty -> dropSubst do
    resultTy <- getTabAppType ty xs
    defuncCase e resultTy \i x -> do
      Abs b body <- return $ alts !! i
      extendSubst (b@>SubstVal x) do
        xs' <- mapM sinkM xs
        body' <- substM body
        simplifyTabApp body' xs'
  LiftSimp _ f' -> do
    fTy <- getType f
    resultTy <- getTabAppType fTy xs
    xs' <- mapM toDataAtomIgnoreRecon xs
    liftSimpAtom resultTy =<< naryTabApp f' xs'
  LiftSimpFun _ _ -> error "not implemented"
simplifyTabApp f _ = error $ "Unexpected table: " ++ pprint f

simplifyIxType :: IxType CoreIR o -> SimplifyM i o (IxType SimpIR o)
simplifyIxType (IxType t ixDict) = do
  t' <- getRepType t
  IxType t' <$> case ixDict of
    IxDictAtom (DictCon (IxFin n)) -> do
      n' <- toDataAtomIgnoreReconAssumeNoDecls n
      return $ IxDictRawFin n'
    IxDictAtom d -> do
      (dictAbs, params) <- generalizeIxDict =<< cheapNormalize d
      params' <- mapM toDataAtomIgnoreReconAssumeNoDecls params
      sdName <- requireIxDictCache dictAbs
      return $ IxDictSpecialized t' sdName params'
    IxDictRawFin n            -> do
      n' <- toDataAtomIgnoreReconAssumeNoDecls n
      return $ IxDictRawFin n'

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

simplifyDictMethod :: Mut n => AbsDict n -> IxMethod -> TopBuilderM n (SLam n)
simplifyDictMethod absDict@(Abs bs dict) method = do
  ty <- liftEnvReaderM $ ixMethodType method absDict
  lamExpr <- liftBuilder $ buildLamExprFromPi ty \allArgs -> do
    let (extraArgs, methodArgs) = splitAt (nestLength bs) allArgs
    dict' <- applyRename (bs @@> extraArgs) dict
    emitExpr $ ApplyMethod dict' (fromEnum method) (Var <$> methodArgs)
  simplifyTopFunction lamExpr

ixMethodType :: IxMethod -> AbsDict n -> EnvReaderM n (PiType CoreIR n)
ixMethodType method absDict = do
  refreshAbs absDict \extraArgBs dict -> do
    CorePiType _ methodArgs _ resultTy <- getMethodType dict (fromEnum method)
    let allBs = extraArgBs >>> fmapNest withoutExpl methodArgs
    return $ PiType allBs Pure resultTy

-- TODO: do we even need this, or is it just a glorified `SubstM`?
simplifyAtom :: CAtom i -> SimplifyM i o (CAtom o)
simplifyAtom atom = confuseGHC >>= \_ -> case atom of
  Var v -> simplifyVar v
  Lam _ -> substM atom
  DepPair x y ty -> DepPair <$> simplifyAtom x <*> simplifyAtom y <*> substM ty
  Con con -> Con <$> traverseOp con substM simplifyAtom (error "unexpected lambda")
  Eff eff -> Eff <$> substM eff
  PtrVar v -> PtrVar <$> substM v
  DictCon d -> (DictCon <$> substM d) >>= cheapNormalize
  DictHole _ _ _ -> error "shouldn't have dict holes past inference"
  NewtypeCon _ _ -> substM atom
  ProjectElt i x -> normalizeProj i =<< simplifyAtom x
  SimpInCore _ -> substM atom
  TypeAsAtom _ -> substM atom

simplifyVar :: AtomName CoreIR i -> SimplifyM i o (CAtom o)
simplifyVar v = do
  env <- getSubst
  case env ! v of
    SubstVal x -> return x
    Rename v' -> do
      AtomNameBinding bindingInfo <- lookupEnv v'
      case bindingInfo of
        -- Functions get inlined only at application sites
        LetBound (DeclBinding _ (Pi _) _) -> return $ Var v'
        LetBound (DeclBinding _ _ (Atom x)) -> dropSubst $ simplifyAtom x
        _ -> return $ Var v'

-- Assumes first order (args/results are "data", allowing newtypes), monormophic
simplifyLam
  :: LamExpr CoreIR i
  -> SimplifyM i o (LamExpr SimpIR o, Abs (Nest (AtomNameBinder SimpIR)) ReconstructAtom o)
simplifyLam (LamExpr bsTop body) = case bsTop of
  Nest (b:>ty) bs -> do
    ty' <- substM ty
    tySimp <- getRepType ty'
    withFreshBinder (getNameHint b) tySimp \(b':>_) -> do
      x <- liftSimpAtom (sink ty') (Var $ binderName b')
      extendSubst (b@>SubstVal x) do
        (LamExpr bs' body', Abs bsRecon recon) <- simplifyLam $ LamExpr bs body
        return (LamExpr (Nest (b':>tySimp) bs') body', Abs (Nest b' bsRecon) recon)
  Empty -> do
    SimplifiedBlock body' recon <- buildSimplifiedBlock $ simplifyBlock body
    return (LamExpr Empty body', Abs Empty recon)

data SplitDataNonData n = SplitDataNonData
  { dataTy    :: Type SimpIR n
  , nonDataTy :: Type CoreIR n
  , toSplit   :: forall i l . CAtom l -> SimplifyM i l (SAtom l, CAtom l)
  , fromSplit :: forall i l . DExt n l => SAtom l -> CAtom l -> SimplifyM i l (CAtom l) }

-- bijection between that type and a (data, non-data) pair type.
splitDataComponents :: Type CoreIR n -> SimplifyM i n (SplitDataNonData n)
splitDataComponents = \case
  ProdTy tys -> do
    splits <- mapM splitDataComponents tys
    return $ SplitDataNonData
      { dataTy    = ProdTy $ map dataTy    splits
      , nonDataTy = ProdTy $ map nonDataTy splits
      , toSplit = \xProd -> do
          xs <- getUnpacked xProd
          (ys, zs) <- unzip <$> forM (zip xs splits) \(x, split) -> toSplit split x
          return (ProdVal ys, ProdVal zs)
      , fromSplit = \xsProd ysProd -> do
          xs <- getUnpacked xsProd
          ys <- getUnpacked ysProd
          zs <- forM (zip (zip xs ys) splits) \((x, y), split) -> fromSplit split x y
          return $ ProdVal zs }
  ty -> tryGetRepType ty >>= \case
    Just repTy -> return $ SplitDataNonData
      { dataTy = repTy
      , nonDataTy = UnitTy
      , toSplit = \x -> (,UnitVal) <$> toDataAtomIgnoreReconAssumeNoDecls x
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
        ansTy <- getType ans
        return $ RightE (dataResult `PairE` ansTy)
  case eitherResult of
    LeftE ans -> do
      (declsResult, recon) <- refreshAbs (Abs decls ans) \decls' ans' -> do
        (newResult, reconAbs) <- telescopicCapture (toScopeFrag decls') ans'
        return (Abs decls' newResult, LamRecon reconAbs)
      block <- makeBlockFromDecls declsResult
      return $ SimplifiedBlock block recon
    RightE (ans `PairE` ty) -> do
      block <- makeBlockFromDecls $ Abs decls ans
      let ty' = ignoreHoistFailure $ hoist (toScopeFrag decls) ty
      return $ SimplifiedBlock block (CoerceRecon ty')

simplifyOp :: Emits o => NameHint -> PrimOp CoreIR i -> SimplifyM i o (CAtom o)
simplifyOp hint op = case op of
  UserEffectOp _ -> error "not implemented"
  Hof hof -> simplifyHof hint hof
  MemOp    op' -> simplifyGenericOp op'
  VectorOp op' -> simplifyGenericOp op'
  RefOp ref eff -> do
    ref' <- simplifyDataAtom ref
    liftResult =<< simplifyRefOp eff ref'
  BinOp binop x' y' -> do
    x <- simplifyDataAtom x'
    y <- simplifyDataAtom y'
    liftResult =<< case binop of
      ISub -> isub x y
      IAdd -> iadd x y
      IMul -> imul x y
      IDiv -> idiv x y
      ICmp Less  -> ilt x y
      ICmp Equal -> ieq x y
      _ -> emitOp $ BinOp binop x y
  UnOp unOp x' -> do
    x <- simplifyDataAtom x'
    liftResult =<< emitOp (UnOp unOp x)
  MiscOp op' -> case op' of
    Select c' x' y' -> do
      c <- simplifyDataAtom c'
      x <- simplifyDataAtom x'
      y <- simplifyDataAtom y'
      liftResult =<< select c x y
    ShowAny x' -> do
      x <- simplifyAtom x'
      dropSubst $ showAny x >>= simplifyBlock
    _ -> simplifyGenericOp op'
  where
    liftResult x = do
      ty <- getTypeSubst op
      liftSimpAtom ty x

simplifyGenericOp
  :: (GenericOp op, IsPrimOp op, HasType CoreIR (op CoreIR), Emits o,
      OpConst op CoreIR ~ OpConst op SimpIR)
  => op CoreIR i
  -> SimplifyM i o (CAtom o)
simplifyGenericOp op = do
  ty <- getTypeSubst op
  op' <- traverseOp op
           (substM >=> getRepType)
           (simplifyAtom >=> toDataAtomIgnoreRecon)
           (error "shouldn't have lambda left")
  result <- liftEnvReaderM (peepholeOp $ toPrimOp op') >>= \case
    Left  a   -> return a
    Right op'' -> emitOp op''
  liftSimpAtom ty result
{-# INLINE simplifyGenericOp #-}

pattern CoerceReconAbs :: Abs (Nest b) ReconstructAtom n
pattern CoerceReconAbs <- Abs _ (CoerceRecon _)

applyDictMethod :: Emits o => CAtom o -> Int -> [CAtom o] -> SimplifyM i o (CAtom o)
applyDictMethod d i methodArgs = do
  cheapNormalize d >>= \case
    DictCon (InstanceDict instanceName instanceArgs) -> dropSubst do
      instanceArgs' <- mapM simplifyAtom instanceArgs
      InstanceDef _ bsInstance _ body <- lookupInstanceDef instanceName
      let InstanceBody _ methods = body
      let method = methods !! i
      extendSubst (bsInstance @@> (SubstVal <$> instanceArgs')) do
        simplifyApp noHint method methodArgs
    DictCon (IxFin n) -> applyIxFinMethod (toEnum i) n methodArgs
    d' -> error $ "Not a simplified dict: " ++ pprint d'
  where
    applyIxFinMethod :: EnvReader m => IxMethod -> CAtom n -> [CAtom n] -> m n (CAtom n)
    applyIxFinMethod method n args = do
      case (method, args) of
        (Size, []) -> return n  -- result : Nat
        (Ordinal, [ix]) -> return $ unwrapNewtype ix -- result : Nat
        (UnsafeFromOrdinal, [ix]) -> return $ NewtypeCon (FinCon n) ix
        _ -> error "bad ix args"

simplifyHof :: Emits o => NameHint -> Hof CoreIR i -> SimplifyM i o (CAtom o)
simplifyHof _hint hof = case hof of
  For d ixDict lam -> do
    (lam', Abs (UnaryNest bIx) recon) <- simplifyLam lam
    ixTypeCore <- ixTyFromDict =<< substM ixDict
    ixTypeSimp@(IxType _ ixDict') <- simplifyIxType ixTypeCore
    ans <- emitExpr $ PrimOp $ Hof $ For d ixDict' lam'
    case recon of
      CoerceRecon _ -> do
        resultTy <- getTypeSubst $ Hof hof
        liftSimpAtom resultTy ans
      LamRecon (Abs bsClosure reconResult) -> do
        TabPi resultTy <- getTypeSubst $ Hof hof
        liftM (SimpInCore . TabLam resultTy) $
          buildAbs noHint ixTypeSimp \i -> buildScoped do
            i' <- sinkM i
            xs <- unpackTelescope bsClosure =<< tabApp (sink ans) (Var i')
            applySubst (bIx@>Rename i' <.> bsClosure @@> map SubstVal xs) reconResult
  While body -> do
    SimplifiedBlock body' (CoerceRecon resultTy) <- buildSimplifiedBlock $ simplifyBlock body
    result <- emitOp (Hof $ While body')
    liftSimpAtom resultTy result
  RunReader r lam -> do
    r' <- simplifyDataAtom r
    (lam', Abs b recon) <- simplifyLam lam
    ans <- emitOp $ Hof $ RunReader r' lam'
    let recon' = ignoreHoistFailure $ hoist b recon
    applyRecon recon' ans
  RunWriter Nothing (BaseMonoid e combine) lam -> do
    LamExpr (BinaryNest h (_:>RefTy _ wTy)) _ <- return lam
    wTy' <- substM $ ignoreHoistFailure $ hoist h wTy
    e' <- simplifyDataAtom e
    (combine', CoerceReconAbs) <- simplifyLam combine
    (lam', Abs b recon) <- simplifyLam lam
    let hof' = Hof $ RunWriter Nothing (BaseMonoid e' combine') lam'
    (ans, w) <- fromPair =<< emitOp hof'
    let recon' = ignoreHoistFailure $ hoist b recon
    ans' <- applyRecon recon' ans
    w' <- liftSimpAtom wTy' w
    return $ PairVal ans' w'
  RunWriter _ _ _ -> error "Shouldn't see a RunWriter with a dest in Simplify"
  RunState Nothing s lam -> do
    (s', sTy) <- toDataAtom =<< simplifyAtom s
    (lam', Abs b recon) <- simplifyLam lam
    resultPair <- emitOp $ Hof $ RunState Nothing s' lam'
    (ans, sOut) <- fromPair resultPair
    let recon' = ignoreHoistFailure $ hoist b recon
    ans' <- applyRecon recon' ans
    sOut' <- liftSimpAtom sTy sOut
    return $ PairVal ans' sOut'
  RunState _ _ _ -> error "Shouldn't see a RunState with a dest in Simplify"
  RunIO body -> do
    SimplifiedBlock body' recon <- buildSimplifiedBlock $ simplifyBlock body
    ans <- emitOp $ Hof $ RunIO body'
    applyRecon recon ans
  RunInit body -> do
    SimplifiedBlock body' recon <- buildSimplifiedBlock $ simplifyBlock body
    ans <- emitOp $ Hof $ RunInit body'
    applyRecon recon ans
  Linearize lam x -> do
    x' <- simplifyDataAtom x
    -- XXX: we're ignoring the result type here, which only makes sense if we're
    -- dealing with functions on simple types.
    (lam', recon) <- simplifyLam lam
    CoerceReconAbs <- return recon
    (result, linFun) <- liftDoubleBuilderToSimplifyM $ linearize lam' x'
    PairTy resultTy linFunTy <- getTypeSubst $ Hof hof
    result' <- liftSimpAtom resultTy result
    linFun' <- liftSimpFun linFunTy linFun
    return $ PairVal result' linFun'
  Transpose lam x -> do
    (lam', CoerceReconAbs) <- simplifyLam lam
    x' <- simplifyDataAtom x
    result <- transpose lam' x'
    resultTy <- getTypeSubst $ Hof hof
    liftSimpAtom resultTy result
  CatchException body-> do
    SimplifiedBlock body' recon <- buildSimplifiedBlock $ simplifyBlock body
    block <- liftBuilder $ runSubstReaderT idSubst $ buildBlock $ exceptToMaybeBlock body'
    result <- emitBlock block
    case recon of
      CoerceRecon ty -> do
        maybeTy <- makePreludeMaybeTy ty
        liftSimpAtom maybeTy result
      LamRecon reconAbs -> fmapMaybe result (applyReconAbs $ sink reconAbs)

-- takes an internal SimpIR Maybe to a CoreIR "prelude Maybe"
fmapMaybe
  :: (EnvReader m, EnvExtender m)
  => SAtom n -> (forall l. DExt n l => SAtom l -> m l (CAtom l))
  -> m n (CAtom n)
fmapMaybe scrut f = do
  ~(MaybeTy justTy) <- getType scrut
  (justAlt, resultJustTy) <- withFreshBinder noHint justTy \b -> do
    result <- f (Var $ binderName b)
    resultTy <- ignoreHoistFailure . hoist b <$> getType result
    result' <- preludeJustVal result
    return (Abs b result', resultTy)
  nothingAlt <- buildAbs noHint UnitTy \_ -> preludeNothingVal $ sink resultJustTy
  resultMaybeTy <- makePreludeMaybeTy resultJustTy
  return $ SimpInCore $ ACase scrut [nothingAlt, justAlt] resultMaybeTy

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
  return $ NewtypeCon con (NothingAtom ty)

preludeMaybeNewtypeCon :: EnvReader m => CType n -> m n (NewtypeCon n)
preludeMaybeNewtypeCon ty = do
  ~(Just (UTyConVar tyConName)) <- lookupSourceMap "Maybe"
  let params = TyConParams [Explicit] [Type ty]
  return $ UserADTData tyConName params

simplifyBlock :: Emits o => Block CoreIR i -> SimplifyM i o (CAtom o)
simplifyBlock (Block _ decls result) = simplifyDecls decls $ simplifyAtom result

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
  TopFunBinding ~(DexTopFun _ _ lam _) <- lookupEnv f
  PairE fPrimal fTangent <- liftSimplifyM $ tryGetCustomRule (sink f) >>= \case
    Just (absParams, rule) -> simplifyCustomLinearization (sink absParams) actives (sink rule)
    Nothing -> liftM toPairE $ liftDoubleBuilderToSimplifyM $ linearizeLam (sink lam) actives
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
    DexTopFun def _ _ _ -> case def of
      Specialization (AppSpecialization fCore absParams) ->
        fmap (absParams,) <$> lookupCustomRules fCore
      _ -> return Nothing
    _ -> return Nothing

type Linearized = Abs (Nest SBinder)    -- primal args
                      (Abs (Nest SDecl) -- primal decls
                      (PairE SAtom      -- primal result
                             SLam))     -- tangent function

simplifyCustomLinearization
  :: Abstracted CoreIR (ListE CAtom) n -> [Active] -> AtomRules n
  -> SimplifyM i n (PairE SLam SLam n)
simplifyCustomLinearization (Abs runtimeBs staticArgs) actives rule = do
  CustomLinearize nImplicit nExplicit zeros fCustom <- return rule
  defuncLinearized =<< withSimplifiedBinders runtimeBs \runtimeBs' runtimeArgs -> do
      Abs runtimeBs' <$> buildScoped do
        ListE staticArgs' <- applySubst (runtimeBs @@> (SubstVal . sink <$> runtimeArgs)) staticArgs
        fCustom' <- sinkM fCustom
        pairResult <- dropSubst $ simplifyApp noHint fCustom' staticArgs'
        (primalResult, fLin) <- fromPair pairResult
        primalResult' <- toDataAtomIgnoreRecon primalResult
        let explicitPrimalArgs = drop nImplicit staticArgs'
        allTangentTys <- forM explicitPrimalArgs \primalArg -> do
          tangentType =<< getRepType =<< getType primalArg
        let actives' = drop (length actives - nExplicit) actives
        activeTangentTys <- catMaybes <$> forM (zip allTangentTys actives')
          \(t, active) -> return case active of True  -> Just t; False -> Nothing
        fLin' <- buildUnaryLamExpr "t" (ProdTy activeTangentTys) \activeTangentArg -> do
          activeTangentArgs <- getUnpacked $ Var activeTangentArg
          ListE allTangentTys' <- sinkM $ ListE allTangentTys
          tangentArgs <- buildTangentArgs zeros (zip allTangentTys' actives') activeTangentArgs
          -- TODO: we're throwing away core type information here. Once we
          -- support core-level tangent types we should make an effort to
          -- correctly restore the core types before applying `fLin`. Right now,
          -- a custom linearization defined for a function on ADTs will
          -- not work.
          fLin' <- sinkM fLin
          Pi (CorePiType _ bs _ _) <- getType fLin'
          let tangentCoreTys = fromNonDepNest bs
          tangentArgs' <- zipWithM liftSimpAtom tangentCoreTys tangentArgs
          tangentResult <- dropSubst $ simplifyApp noHint fLin' tangentArgs'
          toDataAtomIgnoreRecon tangentResult
        return $ PairE primalResult' fLin'
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

    fromNonDepNest :: (HoistableB b, BindsOneAtomName CoreIR b) => Nest b n l -> [CType n]
    fromNonDepNest Empty = []
    fromNonDepNest (Nest b bs) =
      case ignoreHoistFailure $ hoist b (Abs bs UnitE) of
        Abs bs' UnitE -> binderType b : fromNonDepNest bs'

defuncLinearized :: EnvReader m => Linearized n -> m n (PairE SLam SLam n)
defuncLinearized ab = liftBuilder $ refreshAbs ab \bs ab' -> do
  (declsAndResult, reconAbs, residualsTangentsBs) <-
    refreshAbs ab' \decls (PairE primalResult fLin) -> do
      (residuals, reconAbs) <- telescopicCapture (toScopeFrag decls) fLin
      rTy <- getType residuals
      LamExpr tBs _ <- return fLin
      residualsTangentsBs <- withFreshBinder "residual" rTy \rB -> do
        Abs tBs' UnitE <- sinkM $ Abs tBs UnitE
        return $ Abs (Nest rB tBs') UnitE
      residualsTangentsBs' <- return $ ignoreHoistFailure $ hoist decls residualsTangentsBs
      return (Abs decls (PairVal primalResult residuals), reconAbs, residualsTangentsBs')
  primalFun <- LamExpr bs <$> makeBlockFromDecls declsAndResult
  LamExpr residualAndTangentBs tangentBody <- buildLamExpr residualsTangentsBs \(residuals:tangents) -> do
    LamExpr tangentBs' body <- applyReconAbs (sink reconAbs) (Var residuals)
    applyRename (tangentBs' @@> tangents) body >>= emitBlock
  let tangentFun = LamExpr (bs >>> residualAndTangentBs) tangentBody
  return $ PairE primalFun tangentFun

-- === exception-handling pass ===

type HandlerM = SubstReaderT AtomSubstVal (BuilderM SimpIR)

exceptToMaybeBlock :: Emits o => SBlock i -> HandlerM i o (SAtom o)
exceptToMaybeBlock (Block (BlockAnn ty _) decls result) = do
  ty' <- substM ty
  exceptToMaybeDecls ty' decls $ Atom result
exceptToMaybeBlock (Block NoBlockAnn Empty result) = exceptToMaybeExpr $ Atom result
exceptToMaybeBlock _ = error "impossible"

exceptToMaybeDecls :: Emits o => SType o -> Nest SDecl i i' -> SExpr i' -> HandlerM i o (SAtom o)
exceptToMaybeDecls _ Empty result = exceptToMaybeExpr result
exceptToMaybeDecls resultTy (Nest (Let b (DeclBinding _ _ rhs)) decls) finalResult = do
  maybeResult <- exceptToMaybeExpr rhs
  case maybeResult of
    -- This case is just an optimization (but an important one!)
    JustAtom _ x  ->
      extendSubst (b@> SubstVal x) $ exceptToMaybeDecls resultTy decls finalResult
    _ -> emitMaybeCase maybeResult (MaybeTy resultTy)
          (return $ NothingAtom $ sink resultTy)
          (\v -> extendSubst (b@> SubstVal v) $
                   exceptToMaybeDecls (sink resultTy) decls finalResult)

exceptToMaybeExpr :: Emits o => SExpr i -> HandlerM i o (SAtom o)
exceptToMaybeExpr expr = case expr of
  Case e alts resultTy _ -> do
    e' <- substM e
    resultTy' <- substM $ MaybeTy resultTy
    buildCase e' resultTy' \i v -> do
      Abs b body <- return $ alts !! i
      extendSubst (b @> SubstVal v) $ exceptToMaybeBlock body
  Atom x -> do
    x' <- substM x
    ty <- getType x'
    return $ JustAtom ty x'
  PrimOp (Hof (For ann d (UnaryLamExpr b body))) -> do
    ixTy <- ixTyFromDict =<< substM d
    maybes <- buildForAnn (getNameHint b) ann ixTy \i ->
      extendSubst (b@>Rename i) $ exceptToMaybeBlock body
    catMaybesE maybes
  PrimOp (MiscOp (ThrowException _)) -> do
    ty <- getTypeSubst expr
    return $ NothingAtom ty
  PrimOp (Hof (RunState Nothing s lam)) -> do
    s' <- substM s
    BinaryLamExpr h ref body <- return lam
    result  <- emitRunState noHint s' \h' ref' ->
      extendSubst (h @> Rename h' <.> ref @> Rename ref') do
        exceptToMaybeBlock body
    (maybeAns, newState) <- fromPair result
    a <- getTypeSubst expr
    emitMaybeCase maybeAns (MaybeTy a)
       (return $ NothingAtom $ sink a)
       (\ans -> return $ JustAtom (sink a) $ PairVal ans (sink newState))
  PrimOp (Hof (RunWriter Nothing monoid (BinaryLamExpr h ref body))) -> do
    monoid' <- substM monoid
    accumTy <- substM =<< (getReferentTy $ EmptyAbs $ PairB h ref)
    result <- emitRunWriter noHint accumTy monoid' \h' ref' ->
      extendSubst (h @> Rename h' <.> ref @> Rename ref') $
        exceptToMaybeBlock body
    (maybeAns, accumResult) <- fromPair result
    a <- getTypeSubst expr
    emitMaybeCase maybeAns (MaybeTy a)
      (return $ NothingAtom $ sink a)
      (\ans -> return $ JustAtom (sink a) $ PairVal ans (sink accumResult))
  PrimOp (Hof (While body)) -> runMaybeWhile $ exceptToMaybeBlock body
  _ -> do
    expr' <- substM expr
    hasExceptions expr' >>= \case
      True -> error $ "Unexpected exception-throwing expression: " ++ pprint expr
      False -> do
        v <- emit expr'
        ty <- getType v
        return $ JustAtom ty (Var v)

hasExceptions :: EnvReader m => SExpr n -> m n Bool
hasExceptions expr = getEffects expr >>= \case
  EffectRow effs NoTail -> return $ ExceptionEffect `eSetMember` effs

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
