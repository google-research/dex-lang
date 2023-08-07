-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module Simplify
  ( simplifyTopBlock, simplifyTopFunction, ReconstructAtom (..), applyReconTop,
    linearizeTopFun, SimplifiedTopLam (..)) where

import Control.Applicative
import Control.Category ((>>>))
import Control.Monad
import Control.Monad.Reader
import Data.Maybe
import Data.Text.Prettyprint.Doc (Pretty (..), hardline)

import Builder
import CheckType
import Core
import Err
import Generalize
import IRVariants
import Linearize
import Name
import Subst
import Optimize (peepholeOp)
import QueryTypePure
import RuntimePrint
import Transpose
import Types.Core
import Types.Source
import Types.Primitives
import Util (enumerate)
import Visit

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
      repAtom <- go atom
      return (repAtom, ty)
 where
  go :: Emits n => CAtom n -> SimplifyM i n (SAtom n)
  go = \case
    Var v -> lookupAtomName (atomVarName v) >>= \case
      LetBound (DeclBinding _ (Atom x)) -> go x
      _ -> error "Shouldn't have irreducible top names left"
    Con con -> Con <$> case con of
      Lit v -> return $ Lit v
      ProdCon xs -> ProdCon <$> mapM go xs
      SumCon  tys tag x -> SumCon <$> mapM getRepType tys <*> pure tag <*> go x
      HeapVal       -> return HeapVal
    PtrVar t v      -> return $ PtrVar t v
    DepPair x y ty -> do
      DepPairTy ty' <- getRepType $ DepPairTy ty
      DepPair <$> go x <*> go y <*> pure ty'
    NewtypeCon _ x  -> go x
    SimpInCore x    -> case x of
      LiftSimp _ x' -> return x'
      LiftSimpFun _ _ -> notData
      TabLam _ tabLam -> forceTabLam tabLam
      ACase scrut alts resultTy -> forceACase scrut alts resultTy
    Lam _           -> notData
    DictCon _ _     -> notData
    Eff _           -> notData
    TypeAsAtom _    -> notData
    where
      notData = error $ "Not runtime-representable data: " ++ pprint atom

forceTabLam :: Emits n => TabLamExpr n -> SimplifyM i n (SAtom n)
forceTabLam (PairE ixTy (Abs b ab)) =
  buildFor (getNameHint b) Fwd ixTy \v -> do
    result <- applyRename (b@>(atomVarName v)) ab >>= emitDecls
    toDataAtomIgnoreRecon result

type NaryTabLamExpr = Abs SBinders (Abs (Nest SDecl) CAtom)

fromNaryTabLam :: Int -> CAtom n -> Maybe (Int, NaryTabLamExpr n)
fromNaryTabLam maxDepth | maxDepth <= 0 = error "expected positive number of args"
fromNaryTabLam maxDepth = \case
  SimpInCore (TabLam _ (PairE _ (Abs b body))) ->
    extend <|> (Just $ (1, Abs (Nest (PlainBD b) Empty) body))
    where
      extend = case body of
        Abs Empty lam | maxDepth > 1 -> do
          (d, Abs (Nest b2 bs2) body2) <- fromNaryTabLam (maxDepth - 1) lam
          return $ (d + 1, Abs (Nest (PlainBD b) (Nest b2 bs2)) body2)
        _ -> Nothing
  _ -> Nothing

forceACase
  :: Emits n => SAtom n -> [Abs SBinder (WithDecls SimpIR CAtom) n]
  -> CType n -> SimplifyM i n (SAtom n)
forceACase scrut alts resultTy = do
  resultTy' <- getRepType  resultTy
  dropSubst $ buildCase scrut resultTy' \i arg -> do
    Abs b (Abs decls result) <- return $ alts !! i
    extendSubst (b@>SubstVal arg) $ emitDeclsSubst decls $
      substM result >>= toDataAtomIgnoreRecon

tryGetRepType :: Type CoreIR n -> SimplifyM i n (Maybe (SType n))
tryGetRepType t = isData t >>= \case
  False -> return Nothing
  True  -> Just <$> getRepType t

getRepType :: Type CoreIR o -> SimplifyM i o (SType o)
getRepType ty = dropSubst $ go ty where
  go :: Type CoreIR i -> SimplifyM i o (SType o)
  go = \case
    TC con -> TC <$> case con of
      BaseType b  -> return $ BaseType b
      ProdType ts -> ProdType <$> mapM go ts
      SumType  ts -> SumType  <$> mapM go ts
      RefType h a -> do
        h' <- toDataAtomIgnoreReconAssumeNoDecls =<< substM h
        a' <- go a
        return $ RefType h' a'
      TypeKind    -> error $ notDataType
      HeapType    -> return $ HeapType
    DepPairTy (DepPairType expl b (Abs decls rhsTy)) -> do
      withSimpBinder b go \b' ->
        withSimpDecls decls \decls' -> do
          rhsTy' <- go rhsTy
          return $ DepPairTy $ DepPairType expl b' $ Abs decls' rhsTy'
    TabPi (TabPiType d b (Abs decls eltTy)) -> do
      d' <- simplifyIxDict =<< substM d
      withSimpBinder b go \b' ->
        withSimpDecls decls \decls' -> do
          eltTy' <- go eltTy
          return $ TabPi $ TabPiType d' b' $ Abs decls' eltTy'
    NewtypeTyCon con -> do
      con' <- substM con
      (_, ty') <- unwrapNewtypeType con'
      dropSubst $ go ty'
    Pi _           -> error notDataType
    DictTy _       -> error notDataType
    TyVar _ -> error "Shouldn't have type variables in CoreIR IR with SimpIR builder names"
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
 :: Binders CoreIR o any
 -> (forall o'. DExt o o' => Binders SimpIR o o' -> [CAtom o'] -> SimplifyM i o' a)
 -> SimplifyM i o a
withSimplifiedBinders Empty cont = getDistinct >>= \Distinct -> cont Empty []
-- withSimplifiedBinders (Nest (BD (bCore:>ty)) bsCore) cont = do
--   simpTy <- getRepType ty
--   withFreshBinder (getNameHint bCore) simpTy \bSimp -> do
--     x <- liftSimpAtom (sink ty) (Var $ binderVar bSimp)
--     -- TODO: carry a substitution instead of doing N^2 work like this
--     Abs bsCore' UnitE <- applySubst (bCore@>SubstVal x) (EmptyAbs bsCore)
--     withSimplifiedBinders bsCore' \bsSimp xs ->
--       cont (Nest (BD bSimp) bsSimp) (sink x:xs)

-- === Reconstructions ===

data ReconstructAtom (n::S) =
   CoerceRecon (Type CoreIR n)
 | LamRecon (ReconAbs SimpIR CAtom n)

applyRecon :: SBuilderEmits m n => ReconstructAtom n -> SAtom n -> m n (CAtom n)
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
data SimplifiedBlock n = SimplifiedBlock (SBlock n) (ReconstructAtom n)

simplifyTopBlock
  :: (TopBuilder m, Mut n) => TopBlock CoreIR n -> m n (SimplifiedTopLam n)
simplifyTopBlock (TopLam _ _ (LamExpr Empty body)) = do
  SimplifiedBlock block recon <- liftSimplifyM $ buildSimplifiedBlock $ simplifyBlock body
  topLam <- asTopLam $ LamExpr Empty block
  return $ SimplifiedTopLam topLam recon
simplifyTopBlock _ = error "not a block (nullary lambda)"
{-# SCC simplifyTopBlock #-}

simplifyTopFunction :: (TopBuilder m, Mut n) => CTopLam n -> m n (STopLam n)
simplifyTopFunction (TopLam False _ f) = do
  asTopLam =<< liftSimplifyM do
    (lam, CoerceReconAbs) <- simplifyLam f
    return lam
simplifyTopFunction _ = error "shouldn't be in destination-passing style already"
{-# SCC simplifyTopFunction #-}

applyReconTop :: (EnvReader m, Fallible1 m) => ReconstructAtom n -> SAtom n -> m n (CAtom n)
applyReconTop recon x = do
  Abs decls ans <- liftBuilder $ buildScoped $ applyRecon (sink recon) (sink x)
  case decls of
    Empty -> return ans
    _ -> error "unexpected decls at top level"

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
  checkE = renameM -- TODO
    -- block' <- renameM block
    -- effTy <- blockEffTy block' -- TODO: store this in the simplified block instead
    -- block'' <- dropSubst $ checkBlock effTy block'
    -- recon' <- renameM recon -- TODO: CheckableE instance for the recon too
    -- return $ SimplifiedBlock block'' recon'

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
    let hint = (getNameHint b)
    x <- withSubst s $ simplifyExpr hint expr
    simpDeclsSubst (s <>> (b@>SubstVal x)) rest

simplifyExpr :: Emits o => NameHint -> Expr CoreIR i -> SimplifyM i o (CAtom o)
simplifyExpr hint expr = confuseGHC >>= \_ -> case expr of
  App (EffTy _ ty) f xs -> do
    ty' <- substM ty
    xs' <- mapM simplifyAtom xs
    simplifyApp hint ty' f xs'
  TabApp _ f xs -> do
    xs' <- mapM simplifyAtom xs
    f'  <- simplifyAtom f
    simplifyTabApp f' xs'
  Atom x -> simplifyAtom x
  PrimOp  op  -> simplifyOp hint op
  ApplyMethod (EffTy _ ty) dict i xs -> do
    ty' <- substM ty
    xs' <- mapM simplifyAtom xs
    dict' <- simplifyAtom dict
    applyDictMethod ty' dict' i xs'
  TabCon _ ty xs -> do
    ty' <- substM ty
    tySimp <- getRepType ty'
    xs' <- forM xs \x -> simplifyDataAtom x
    liftSimpAtom ty' =<< emitExpr (TabCon Nothing tySimp xs')
  -- Case scrut alts (EffTy _ resultTy) -> do
  --   scrut' <- simplifyAtom scrut
  --   resultTy' <- substM resultTy
  --   defuncCaseCore scrut' resultTy' \i x -> do
  --     LamExpr b body <- return $ alts !! i
  --     extendSubst (b@>SubstVal x) $ simplifyBlock body

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
  IndexRef _ x -> do
    x' <- simplifyDataAtom x
    emitOp =<< mkIndexRef ref x'
  ProjRef _ (ProjectProduct i) -> emitOp =<< mkProjRef ref (ProjectProduct i)
  ProjRef _ UnwrapNewtype -> return ref
  where emitRefOp op' = emitOp $ RefOp ref op'

defuncCaseCore :: Emits o
  => Atom CoreIR o -> Type CoreIR o
  -> (forall o'. (Emits o', DExt o o') => Int -> CAtom o' -> SimplifyM i o' (CAtom o'))
  -> SimplifyM i o (CAtom o)
defuncCaseCore scrut resultTy cont = undefined
-- defuncCaseCore scrut resultTy cont = do
--   tryAsDataAtom scrut >>= \case
--     Just (scrutSimp, _) -> do
--       altBinderTys <- caseAltsBinderTys $ getType scrut
--       defuncCase scrutSimp resultTy \i x -> do
--         let xCoreTy = altBinderTys !! i
--         x' <- liftSimpAtom (sink xCoreTy) x
--         cont i x'
--     Nothing -> case trySelectBranch scrut of
--       Just (i, arg) -> getDistinct >>= \Distinct -> cont i arg
--       Nothing -> go scrut where
--         go = \case
--           SimpInCore (ACase scrutSimp alts _) -> do
--             defuncCase scrutSimp resultTy \i x -> do
--               Abs altb altAtom <- return $ alts !! i
--               altAtom' <- applySubst (altb @> SubstVal x) altAtom
--               cont i altAtom'
--           NewtypeCon con scrut' | isSumCon con -> go scrut'
--           _ -> nope
--         nope = error $ "Don't know how to scrutinize non-data " ++ pprint scrut

defuncCase :: Emits o
  => Atom SimpIR o -> Type CoreIR o
  -> (forall o'. (Emits o', DExt o o') => Int -> SAtom o' -> SimplifyM i o' (CAtom o'))
  -> SimplifyM i o (CAtom o)
defuncCase scrut resultTy cont = undefined
-- defuncCase scrut resultTy cont = do
--   case trySelectBranch scrut of
--     Just (i, arg) -> getDistinct >>= \Distinct -> cont i arg
--     Nothing -> do
--       scrutTy <- return $ getType scrut
--       altBinderTys <- caseAltsBinderTys scrutTy
--       tryGetRepType resultTy >>= \case
--         Just resultTyData -> do
--           alts' <- forM (enumerate altBinderTys) \(i, bTy) -> do
--             buildAbs noHint bTy \x -> do
--               buildBlock $ cont i (sink $ Var x) >>= toDataAtomIgnoreRecon
--           caseExpr <- mkCase scrut resultTyData alts'
--           emitExpr caseExpr >>= liftSimpAtom resultTy
--         Nothing -> do
--           split <- splitDataComponents resultTy
--           (alts', closureTys, recons) <- unzip3 <$> forM (enumerate altBinderTys) \(i, bTy) -> do
--              simplifyAlt split bTy $ cont i
--           let closureSumTy = SumTy closureTys
--           let newNonDataTy = nonDataTy split
--           alts'' <- forM (enumerate alts') \(i, alt) -> injectAltResult closureTys i alt
--           caseExpr <- mkCase scrut  (PairTy (dataTy split) closureSumTy) alts''
--           caseResult <- emitExpr $ caseExpr
--           (dataVal, sumVal) <- fromPair caseResult
--           reconAlts <- forM (zip closureTys recons) \(ty, recon) ->
--             buildAbs noHint ty \v -> applyRecon (sink recon) (Var v)
--           let nonDataVal = SimpInCore $ ACase sumVal reconAlts newNonDataTy
--           Distinct <- getDistinct
--           fromSplit split dataVal nonDataVal

simplifyAlt
  :: SplitDataNonData n
  -> SType o
  -> (forall o'. (Emits o', DExt o o') => SAtom o' -> SimplifyM i o' (CAtom o'))
  -> SimplifyM i o (Alt SimpIR o, SType o, ReconstructAtom o)
simplifyAlt split ty cont = undefined
-- simplifyAlt split ty cont = do
--   withFreshBinder noHint ty \b -> do
--     ab <- buildScoped $ cont $ sink $ Var $ binderVar b
--     (body, recon) <- refreshAbs ab \decls result -> do
--       let locals = toScopeFrag b >>> toScopeFrag decls
--       -- TODO: this might be too cautious. The type only needs to
--       -- be hoistable above the decls. In principle it can still
--       -- mention vars from the lambda binders.
--       Distinct <- getDistinct
--       (resultData, resultNonData) <- toSplit split result
--       (newResult, reconAbs) <- telescopicCapture locals resultNonData
--       return (Abs decls (PairVal resultData newResult), LamRecon reconAbs)
--     EffTy _ (PairTy _ nonDataType) <- blockEffTy body
--     let nonDataType' = ignoreHoistFailure $ hoist b nonDataType
--     return (Abs b body, nonDataType', recon)

simplifyApp :: forall i o. Emits o
  => NameHint -> CType o -> CAtom i -> [CAtom o] -> SimplifyM i o (CAtom o)
simplifyApp hint resultTy f xs =  case f of
  Lam (CoreLamExpr _ lam) -> fast lam
  _ -> slow =<< substM f
  where
    fast :: LamExpr CoreIR i' -> SimplifyM i' o (CAtom o)
    fast (LamExpr bs body) = instantiateSimp bs xs $ simplifyBlock body

    slow :: CAtom o -> SimplifyM i o (CAtom o)
    slow = \case
      Lam (CoreLamExpr _ lam) -> dropSubst $ fast lam
      SimpInCore (ACase e alts _) -> dropSubst do
        defuncCase e resultTy \i x -> do
          Abs b (Abs decls fResult) <- return $ alts !! i
          extendSubst (b@>SubstVal x) do
            emitDeclsSubst decls do
              xs' <- mapM sinkM xs
              simplifyApp hint (sink resultTy) fResult xs'
      SimpInCore (LiftSimpFun _ lam) -> do
        xs' <- mapM toDataAtomIgnoreRecon xs
        result <- instantiate lam xs'
        liftSimpAtom resultTy result
      Var v -> do
        lookupAtomName (atomVarName v) >>= \case
          NoinlineFun _ _ -> simplifyTopFunApp v xs
          FFIFunBound _ f' -> do
            xs' <- mapM toDataAtomIgnoreRecon xs
            liftSimpAtom resultTy =<< naryTopApp f' xs'
          b -> error $ "Should only have noinline functions left " ++ pprint b
      atom -> error $ "Unexpected function: " ++ pprint atom

simplifyTopFunApp :: Emits n => CAtomVar n -> [CAtom n] -> SimplifyM i n (CAtom n)
simplifyTopFunApp fName xs = do
  fTy@(Pi piTy) <- return $ getType fName
  resultTy <- liftBuilderSimp $ typeOfApp fTy xs
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

specializedFunCoreDefinition :: (Mut n, TopBuilder m) => SpecializationSpec n -> m n (TopLam CoreIR n)
specializedFunCoreDefinition (AppSpecialization f ab) = do
  (asTopLam =<<) $ liftBuilder $ buildLamExpr ab \runtimeArgs -> do
    -- This avoids an infinite loop. Otherwise, in simplifyTopFunction,
    -- where we eta-expand and try to simplify `App f args`, we would see `f` as a
    -- "noinline" function and defer its simplification.
    NoinlineFun _ f' <- lookupAtomName (atomVarName (sink f))
    ListE staticArgs' <- instantiate ab (Var <$> runtimeArgs)
    naryApp f' staticArgs'

simplifyTabApp :: forall i o. Emits o
  => CAtom o -> [CAtom o] -> SimplifyM i o (CAtom o)
simplifyTabApp f [] = return f
-- simplifyTabApp f@(SimpInCore sic) xs = case sic of
--   TabLam _ _ -> do
--     case fromNaryTabLam (length xs) f of
--       Just (bsCount, ab) -> do
--         let (xsPref, xsRest) = splitAt bsCount xs
--         xsPref' <- mapM toDataAtomIgnoreRecon xsPref
--         block' <- instantiate ab xsPref'
--         atom <- emitDecls block'
--         simplifyTabApp atom xsRest
--       Nothing -> error "should never happen"
--   ACase e alts ty -> dropSubst do
--     resultTy <- typeOfTabApp ty xs
--     defuncCase e resultTy \i x -> do
--       Abs b body <- return $ alts !! i
--       extendSubst (b@>SubstVal x) do
--         xs' <- mapM sinkM xs
--         body' <- substM body
--         simplifyTabApp body' xs'
--   LiftSimp _ f' -> do
--     fTy <- return $ getType f
--     resultTy <- typeOfTabApp fTy xs
--     xs' <- mapM toDataAtomIgnoreRecon xs
--     liftSimpAtom resultTy =<< naryTabApp f' xs'
--   LiftSimpFun _ _ -> error "not implemented"
-- simplifyTabApp f _ = error $ "Unexpected table: " ++ pprint f

simplifyIxType :: IxType CoreIR o -> SimplifyM i o (IxType SimpIR o)
simplifyIxType (IxType t d) = IxType <$> getRepType t <*> simplifyIxDict d

simplifyIxDict :: IxDict CoreIR o -> SimplifyM i o (IxDict SimpIR o)
simplifyIxDict = \case
  IxDictAtom (DictCon _ (IxFin n)) -> do
    n' <- toDataAtomIgnoreReconAssumeNoDecls n
    return $ IxDictRawFin n'
  IxDictAtom d -> do
    IxType t _ <- return $ ixTyFromDict $ IxDictAtom d
    t' <- getRepType t
    (dictAbs, params) <- generalizeIxDict d
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

simplifyDictMethod :: Mut n => AbsDict n -> IxMethod -> TopBuilderM n (TopLam SimpIR n)
simplifyDictMethod absDict method = undefined
-- simplifyDictMethod absDict method = do
--   ty <- liftEnvReaderM $ ixMethodType method absDict
--   lamExpr <- liftBuilder $ buildTopLamFromPi ty \allArgs -> do
--     let (extraArgs, methodArgs) = splitAt (arity absDict) allArgs
--     dict' <- instantiate absDict (Var <$> extraArgs)
--     emitExpr =<< mkApplyMethod dict' (fromEnum method) (Var <$> methodArgs)
--   simplifyTopFunction lamExpr

ixMethodType :: IxMethod -> AbsDict n -> EnvReaderM n (PiType CoreIR n)
ixMethodType method absDict = undefined  -- DECLS: need to be able to emit. We're under binders so it should be ok
-- ixMethodType method absDict = do
--   refreshAbs absDict \extraArgBs dict -> do
--     CorePiType _ _ methodArgs (EffTy _ resultTy) <- getMethodType dict (fromEnum method)
--     let allBs = extraArgBs >>> methodArgs
--     return $ PiType allBs (EffTy Pure resultTy)

simplifyAtom :: CAtom i -> SimplifyM i o (CAtom o)
simplifyAtom = substM

simplifyVar :: AtomVar CoreIR i -> SimplifyM i o (CAtom o)
simplifyVar v = do
  env <- getSubst
  case env ! atomVarName v of
    SubstVal x -> return x
    Rename v' -> do
      AtomNameBinding bindingInfo <- lookupEnv v'
      let ty = getType bindingInfo
      case bindingInfo of
        -- Functions get inlined only at application sites
        LetBound (DeclBinding _  _) | isFun -> return $ Var $ AtomVar v' ty
          where isFun = case ty of Pi _ -> True; _ -> False
        LetBound (DeclBinding _ (Atom x)) -> dropSubst $ simplifyAtom x
        _ -> return $ Var $ AtomVar v' ty

-- Assumes first order (args/results are "data", allowing newtypes), monormophic
simplifyLam :: LamExpr CoreIR i -> SimplifyM i o (LamExpr SimpIR o, Abs SBinders ReconstructAtom o)
simplifyLam (LamExpr bs body) =
  withSimpBinders bs (\t -> substM t >>= getRepType) \bs' -> do
    SimplifiedBlock body' recon <- buildSimplifiedBlock $ simplifyBlock body
    return (LamExpr bs' body', Abs bs' recon)

data SplitDataNonData n = SplitDataNonData
  { dataTy    :: Type SimpIR n
  , nonDataTy :: Type CoreIR n
  , toSplit   :: forall i l . CAtom l -> SimplifyM i l (SAtom l, CAtom l)
  , fromSplit :: forall i l . DExt n l => SAtom l -> CAtom l -> SimplifyM i l (CAtom l) }

-- bijection between that type and a (data, non-data) pair type.
splitDataComponents :: Type CoreIR n -> SimplifyM i n (SplitDataNonData n)
splitDataComponents = undefined
-- splitDataComponents = \case
--   ProdTy tys -> do
--     splits <- mapM splitDataComponents tys
--     return $ SplitDataNonData
--       { dataTy    = ProdTy $ map dataTy    splits
--       , nonDataTy = ProdTy $ map nonDataTy splits
--       , toSplit = \xProd -> do
--           xs <- getUnpacked xProd
--           (ys, zs) <- unzip <$> forM (zip xs splits) \(x, split) -> toSplit split x
--           return (ProdVal ys, ProdVal zs)
--       , fromSplit = \xsProd ysProd -> do
--           xs <- getUnpacked xsProd
--           ys <- getUnpacked ysProd
--           zs <- forM (zip (zip xs ys) splits) \((x, y), split) -> fromSplit split x y
--           return $ ProdVal zs }
--   ty -> tryGetRepType ty >>= \case
--     Just repTy -> return $ SplitDataNonData
--       { dataTy = repTy
--       , nonDataTy = UnitTy
--       , toSplit = \x -> (,UnitVal) <$> toDataAtomIgnoreReconAssumeNoDecls x
--       , fromSplit = \x _ -> liftSimpAtom (sink ty) x }
--     Nothing -> return $ SplitDataNonData
--       { dataTy = UnitTy
--       , nonDataTy = ty
--       , toSplit = \x -> return (UnitVal, x)
--       , fromSplit = \_ x -> return x }

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
      (block, recon) <- refreshAbs (Abs decls ans) \decls' ans' -> do
        (Abs decls'' newResult, reconAbs) <- telescopicCapture (toScopeFrag decls') ans'
        return (Abs (decls' >>> decls'') newResult, LamRecon reconAbs)
      return $ SimplifiedBlock block recon
    RightE (ans `PairE` ty) -> do
      let ty' = ignoreHoistFailure $ hoist (toScopeFrag decls) ty
      return $ SimplifiedBlock (Abs decls ans) (CoerceRecon ty')

simplifyOp :: Emits o => NameHint -> PrimOp CoreIR i -> SimplifyM i o (CAtom o)
simplifyOp hint op = case op of
  Hof (TypedHof (EffTy _ ty) hof) -> do
    ty' <- substM ty
    simplifyHof hint ty' hof
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
      ty <- substM $ getType op
      liftSimpAtom ty x

simplifyGenericOp
  :: (GenericOp op, IsPrimOp op, HasType CoreIR (op CoreIR), Emits o,
      OpConst op CoreIR ~ OpConst op SimpIR)
  => op CoreIR i
  -> SimplifyM i o (CAtom o)
simplifyGenericOp op = do
  ty <- substM $ getType op
  op' <- traverseOp op
           (substM >=> getRepType)
           (simplifyAtom >=> toDataAtomIgnoreRecon)
           (error "shouldn't have lambda left")
  result <- liftEnvReaderM (peepholeOp $ toPrimOp op') >>= emitExprToAtom
  liftSimpAtom ty result
{-# INLINE simplifyGenericOp #-}

pattern CoerceReconAbs :: Abs (Nest b) ReconstructAtom n
pattern CoerceReconAbs <- Abs _ (CoerceRecon _)

applyDictMethod :: Emits o => CType o -> CAtom o -> Int -> [CAtom o] -> SimplifyM i o (CAtom o)
applyDictMethod resultTy d i methodArgs = case d of
  DictCon _ (InstanceDict instanceName instanceArgs) -> undefined
  -- DictCon _ (InstanceDict instanceName instanceArgs) -> dropSubst do
  --   instanceArgs' <- mapM simplifyAtom instanceArgs
  --   InstanceDef _ _ paramBs _ decls body <- lookupInstanceDef instanceName
  --   instantiateSimp paramBs instanceArgs' do
  --     let InstanceBody _ methods = body
  --     let method = methods !! i
  --     simplifyApp noHint resultTy method methodArgs
  DictCon _ (IxFin n) -> applyIxFinMethod (toEnum i) n methodArgs
  d' -> error $ "Not a simplified dict: " ++ pprint d'
  where
    applyIxFinMethod :: EnvReader m => IxMethod -> CAtom n -> [CAtom n] -> m n (CAtom n)
    applyIxFinMethod method n args = do
      case (method, args) of
        (Size, []) -> return n  -- result : Nat
        (Ordinal, [NewtypeCon _ ix]) -> return ix
        (UnsafeFromOrdinal, [ix]) -> return $ NewtypeCon (FinCon n) ix
        _ -> error "bad ix args"

simplifyHof :: Emits o => NameHint -> CType o -> Hof CoreIR i -> SimplifyM i o (CAtom o)
simplifyHof _hint resultTy = \case
  For d ixTypeCore lam -> do
    (lam', Abs (UnaryNest bIx) recon) <- simplifyLam lam
    ixTypeSimp <- simplifyIxType =<< substM ixTypeCore
    ans <- emitHof $ For d ixTypeSimp lam'
    dropSubst $ case recon of
      CoerceRecon _ -> liftSimpAtom resultTy ans
      LamRecon (Abs bsClosure reconResult) -> do
        TabPi resultTabTy <- return resultTy
        liftM (SimpInCore . TabLam resultTabTy) $
          PairE ixTypeSimp <$> buildAbs noHint (ixTypeType ixTypeSimp) \i -> buildScoped do
            i' <- sinkM i
            xs <- unpackTelescope bsClosure =<< tabApp (sink ans) (Var i')
            extendSubstBD (UnaryNest bIx) [SubstVal $ Var i'] do
              extendSubst (bsClosure @@> map SubstVal xs) do
                substM reconResult
  While body -> do
    SimplifiedBlock body' (CoerceRecon _) <- buildSimplifiedBlock $ simplifyBlock body
    result <- emitHof $ While body'
    liftSimpAtom resultTy result
  RunReader r lam -> do
    r' <- simplifyDataAtom r
    (lam', Abs b recon) <- simplifyLam lam
    ans <- emitHof $ RunReader r' lam'
    let recon' = ignoreHoistFailure $ hoist b recon
    applyRecon recon' ans
  RunWriter Nothing (BaseMonoid e combine) lam -> do
    LamExpr (BinaryNest h (BD decls refB)) _ <- return lam
    RefTy _ wTy <- return $ binderType refB
    wTy' <- substM $ ignoreHoistFailure $ hoist (PairB h decls) wTy
    e' <- simplifyDataAtom e
    (combine', CoerceReconAbs) <- simplifyLam combine
    (lam', Abs b recon) <- simplifyLam lam
    (ans, w) <- fromPair =<< emitHof (RunWriter Nothing (BaseMonoid e' combine') lam')
    let recon' = ignoreHoistFailure $ hoist b recon
    ans' <- applyRecon recon' ans
    w' <- liftSimpAtom wTy' w
    return $ PairVal ans' w'
  RunWriter _ _ _ -> error "Shouldn't see a RunWriter with a dest in Simplify"
  RunState Nothing s lam -> do
    (s', sTy) <- toDataAtom =<< simplifyAtom s
    (lam', Abs b recon) <- simplifyLam lam
    resultPair <- emitHof $ RunState Nothing s' lam'
    (ans, sOut) <- fromPair resultPair
    let recon' = ignoreHoistFailure $ hoist b recon
    ans' <- applyRecon recon' ans
    sOut' <- liftSimpAtom sTy sOut
    return $ PairVal ans' sOut'
  RunState _ _ _ -> error "Shouldn't see a RunState with a dest in Simplify"
  RunIO body -> do
    SimplifiedBlock body' recon <- buildSimplifiedBlock $ simplifyBlock body
    ans <- emitHof $ RunIO body'
    applyRecon recon ans
  RunInit body -> do
    SimplifiedBlock body' recon <- buildSimplifiedBlock $ simplifyBlock body
    ans <- emitHof $ RunInit body'
    applyRecon recon ans
  Linearize lam x -> do
    x' <- simplifyDataAtom x
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
    x' <- simplifyDataAtom x
    result <- transpose lam' x'
    liftSimpAtom resultTy result
  CatchException _ body-> do
    SimplifiedBlock body' recon <- buildSimplifiedBlock $ simplifyBlock body
    simplifiedResultTy <- blockTy body'
    block <- liftBuilder $ runSubstReaderT idSubst $ buildBlock $
      exceptToMaybeBlock (sink simplifiedResultTy) body'
    result <- emitBlock block
    case recon of
      CoerceRecon ty -> do
        maybeTy <- makePreludeMaybeTy ty
        liftSimpAtom maybeTy result
      LamRecon reconAbs -> fmapMaybe result (applyReconAbs $ sink reconAbs)

-- takes an internal SimpIR Maybe to a CoreIR "prelude Maybe"
fmapMaybe
  :: (EnvReader m, EnvExtender m)
  => SAtom n -> (forall l. (Emits l, DExt n l) => SAtom l -> m l (CAtom l))
  -> m n (CAtom n)
fmapMaybe scrut f = undefined
-- fmapMaybe scrut f = do
--   ~(MaybeTy justTy) <- return $ getType scrut
--   (justAlt, resultJustTy) <- withFreshBinder noHint justTy \b -> do
--     result <- f (Var $ binderVar b)
--     resultTy <- return $ ignoreHoistFailure $ hoist b (getType result)
--     result' <- preludeJustVal result
--     return (Abs b result', resultTy)
--   nothingAlt <- buildAbs noHint UnitTy \_ ->
--     liftM WithoutDecls $ preludeNothingVal $ sink resultJustTy
--   resultMaybeTy <- makePreludeMaybeTy resultJustTy
--   return $ SimpInCore $ ACase scrut [nothingAlt, justAlt] resultMaybeTy

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
  TyConDef sn _ _ _ <- lookupTyCon tyConName
  let params = TyConParams [Explicit] [Type ty]
  return $ UserADTData sn tyConName params

simplifyBlock :: Emits o => Block CoreIR i -> SimplifyM i o (CAtom o)
simplifyBlock (Abs decls result) = simplifyDecls decls $ simplifyAtom result

liftSimpAtom :: SBuilderEmits m n => Type CoreIR n -> SAtom n -> m n (CAtom n)
liftSimpAtom ty simpAtom = case simpAtom of
  Var _          -> justLift
  RepValAtom _   -> justLift -- TODO(dougalm): should we make more effort to pull out products etc?
  _ -> case (ty, simpAtom) of
    (NewtypeTyCon tc, x) -> do
      (dc, ty') <- unwrapNewtypeType tc
      NewtypeCon dc <$> rec ty' x
    (BaseTy _  , Con (Lit v))      -> return $ Con $ Lit v
    (ProdTy tys, Con (ProdCon xs))   -> Con . ProdCon <$> zipWithM rec tys xs
    (SumTy  tys, Con (SumCon _ i x)) -> Con . SumCon tys i <$> rec (tys!!i) x
    (DepPairTy dpt, DepPair x1 x2 _) -> do
      x1' <- do
        t1 <- liftBuilderSimp $ depPairLeftTy dpt
        rec t1 x1
      t2' <- liftBuilderSimp $ instantiate dpt [x1']
      x2' <- rec t2' x2
      return $ DepPair x1' x2' dpt
    _ -> error $ "can't lift " <> pprint simpAtom <> " to " <> pprint ty
  where
    rec = liftSimpAtom
    justLift = return $ SimpInCore $ LiftSimp ty simpAtom
{-# INLINE liftSimpAtom #-}

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

type Linearized = Abs SBinders          -- primal args
                      (Abs (Nest SDecl) -- primal decls
                      (PairE SAtom      -- primal result
                             SLam))     -- tangent function

simplifyCustomLinearization
  :: Abstracted CoreIR (ListE CAtom) n -> [Active] -> AtomRules n
  -> SimplifyM i n (PairE STopLam STopLam n)
simplifyCustomLinearization (Abs runtimeBs staticArgs) actives rule = undefined
-- simplifyCustomLinearization (Abs runtimeBs staticArgs) actives rule = do
--   CustomLinearize nImplicit nExplicit zeros fCustom <- return rule
--   linearized <- withSimplifiedBinders runtimeBs \runtimeBs' runtimeArgs -> do
--       Abs runtimeBs' <$> buildScoped do
--         ListE staticArgs' <- instantiate (Abs runtimeBs staticArgs) (sink <$> runtimeArgs)
--         fCustom' <- sinkM fCustom
--         resultTy <- typeOfApp (getType fCustom') staticArgs'
--         pairResult <- dropSubst $ simplifyApp noHint resultTy fCustom' staticArgs'
--         (primalResult, fLin) <- fromPair pairResult
--         primalResult' <- toDataAtomIgnoreRecon primalResult
--         let explicitPrimalArgs = drop nImplicit staticArgs'
--         allTangentTys <- forM explicitPrimalArgs \primalArg -> do
--           tangentType =<< getRepType (getType primalArg)
--         let actives' = drop (length actives - nExplicit) actives
--         activeTangentTys <- catMaybes <$> forM (zip allTangentTys actives')
--           \(t, active) -> return case active of True  -> Just t; False -> Nothing
--         fLin' <- buildUnaryLamExpr "t" (ProdTy activeTangentTys) \activeTangentArg -> do
--           activeTangentArgs <- getUnpacked $ Var activeTangentArg
--           ListE allTangentTys' <- sinkM $ ListE allTangentTys
--           tangentArgs <- buildTangentArgs zeros (zip allTangentTys' actives') activeTangentArgs
--           -- TODO: we're throwing away core type information here. Once we
--           -- support core-level tangent types we should make an effort to
--           -- correctly restore the core types before applying `fLin`. Right now,
--           -- a custom linearization defined for a function on ADTs will
--           -- not work.
--           fLin' <- sinkM fLin
--           Pi (CorePiType _ _ bs _) <- return $ getType fLin'
--           let tangentCoreTys = fromNonDepNest bs
--           tangentArgs' <- zipWithM liftSimpAtom tangentCoreTys tangentArgs
--           resultTyTangent <- typeOfApp (getType fLin') tangentArgs'
--           tangentResult <- dropSubst $ simplifyApp noHint resultTyTangent fLin' tangentArgs'
--           toDataAtomIgnoreRecon tangentResult
--         return $ PairE primalResult' fLin'
--   PairE primalFun tangentFun <- defuncLinearized linearized
--   primalFun' <- asTopLam primalFun
--   tangentFun' <- asTopLam tangentFun
--   return $ PairE primalFun' tangentFun'
--  where
--     buildTangentArgs :: Emits n => SymbolicZeros -> [(SType n, Active)] -> [SAtom n] -> SimplifyM i n [SAtom n]
--     buildTangentArgs _ [] [] = return []
--     buildTangentArgs zeros ((t, False):tys) activeArgs = do
--       inactiveArg <- case zeros of
--         SymbolicZeros -> symbolicTangentZero t
--         InstantiateZeros -> zeroAt t
--       rest <- buildTangentArgs zeros tys activeArgs
--       return $ inactiveArg:rest
--     buildTangentArgs zeros ((_, True):tys) (activeArg:activeArgs) = do
--       activeArg' <- case zeros of
--         SymbolicZeros -> symbolicTangentNonZero activeArg
--         InstantiateZeros -> return activeArg
--       rest <- buildTangentArgs zeros tys activeArgs
--       return $ activeArg':rest
--     buildTangentArgs _ _ _ = error "zip error"

--     fromNonDepNest :: Nest CBinderAndDecls n l -> [CType n]
--     fromNonDepNest Empty = []
--     -- fromNonDepNest (Nest b bs) =
--     --   case ignoreHoistFailure $ hoist b (Abs bs UnitE) of
--     --     Abs bs' UnitE -> binderType b : fromNonDepNest bs'

defuncLinearized :: EnvReader m => Linearized n -> m n (PairE SLam SLam n)
defuncLinearized ab = undefined
-- defuncLinearized ab = liftBuilder $ refreshAbs ab \bs ab' -> do
--   (declsAndResult, reconAbs, residualsTangentsBs) <-
--     refreshAbs ab' \decls (PairE primalResult fLin) -> do
--       (residuals, reconAbs) <- telescopicCapture (toScopeFrag decls) fLin
--       let rTy = getType residuals
--       LamExpr tBs _ <- return fLin
--       residualsTangentsBs <- withFreshBinder "residual" rTy \rB -> do
--         Abs tBs' UnitE <- sinkM $ Abs tBs UnitE
--         return $ Abs (Nest (BD rB) tBs') UnitE
--       residualsTangentsBs' <- return $ ignoreHoistFailure $ hoist decls residualsTangentsBs
--       return (Abs decls (PairVal primalResult residuals), reconAbs, residualsTangentsBs')
--   let primalFun = LamExpr bs declsAndResult
--   LamExpr residualAndTangentBs tangentBody <- buildLamExpr residualsTangentsBs \(residuals:tangents) -> do
--     lam <- applyReconAbs (sink reconAbs) (Var residuals)
--     instantiate lam (Var <$> tangents)
--   let tangentFun = LamExpr (bs >>> residualAndTangentBs) tangentBody
--   return $ PairE primalFun tangentFun

-- === exception-handling pass ===

type HandlerM = SubstReaderT AtomSubstVal (BuilderM SimpIR)

exceptToMaybeBlock :: Emits o => SType o -> SBlock i -> HandlerM i o (SAtom o)
exceptToMaybeBlock ty (Abs Empty result) = do
  result' <- substM result
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
  -- Case e alts (EffTy _ resultTy) -> do
  --   e' <- substM e
  --   resultTy' <- substM $ MaybeTy resultTy
  --   buildCase e' resultTy' \i v -> do
  --     LamExpr b body <- return $ alts !! i
  --     extendSubst (b @> SubstVal v) do
  --       blockResultTy <- blockTy =<< substM body -- TODO: avoid this by caching the type
  --       exceptToMaybeBlock blockResultTy body
  Atom x -> do
    x' <- substM x
    let ty = getType x'
    return $ JustAtom ty x'
  -- PrimOp (Hof (TypedHof _ (For ann ixTy' (UnaryLamExpr b body)))) -> do
  --   ixTy <- substM ixTy'
  --   maybes <- buildForAnn (getNameHint b) ann ixTy \i -> do
  --     extendSubst (b@>Rename (atomVarName i)) do
  --       blockResultTy <- blockTy =<< substM body -- TODO: avoid this by caching the type
  --       exceptToMaybeBlock blockResultTy body
  --   catMaybesE maybes
  PrimOp (MiscOp (ThrowException _)) -> do
    ty <- substM $ getType expr
    return $ NothingAtom ty
  PrimOp (Hof (TypedHof _ (RunState Nothing s lam))) -> do
    s' <- substM s
    BinaryLamExpr h ref body <- return lam
    result  <- emitRunState noHint s' \h' ref' ->
      extendSubstBD (BinaryNest h ref) [Rename (atomVarName h'), Rename (atomVarName ref')] do
        blockResultTy <- blockTy =<< substM body -- TODO: avoid this by caching the type
        exceptToMaybeBlock blockResultTy body
    (maybeAns, newState) <- fromPair result
    a <- substM $ getType expr
    emitMaybeCase maybeAns (MaybeTy a)
       (return $ NothingAtom $ sink a)
       (\ans -> return $ JustAtom (sink a) $ PairVal ans (sink newState))
  PrimOp (Hof (TypedHof (EffTy _ resultTy) (RunWriter Nothing monoid (BinaryLamExpr h ref body)))) -> do
    monoid' <- substM monoid
    PairTy _ accumTy <- substM resultTy
    result <- emitRunWriter noHint accumTy monoid' \h' ref' ->
      extendSubstBD (BinaryNest h ref) [Rename (atomVarName h'), Rename (atomVarName ref')] do
        blockResultTy <- blockTy =<< substM body -- TODO: avoid this by caching the type
        exceptToMaybeBlock blockResultTy body
    (maybeAns, accumResult) <- fromPair result
    a <- substM $ getType expr
    emitMaybeCase maybeAns (MaybeTy a)
      (return $ NothingAtom $ sink a)
      (\ans -> return $ JustAtom (sink a) $ PairVal ans (sink accumResult))
  PrimOp (Hof (TypedHof _ (While body))) -> do
    blockResultTy <- blockTy =<< substM body -- TODO: avoid this by caching the type
    runMaybeWhile $ exceptToMaybeBlock (sink blockResultTy) body
  -- _ -> do
  --   expr' <- substM expr
  --   case hasExceptions expr' of
  --     True -> error $ "Unexpected exception-throwing expression: " ++ pprint expr
  --     False -> do
  --       v <- emit expr'
  --       let ty = getType v
  --       return $ JustAtom ty (Var v)

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




-- === Combinators we need ===

-- XXX: should we allow `Emits` (or equivalent) in the continuations? Seems we
-- could go either way, but it would mean we couldn't give direct access to the
-- decls. Interestingly, we only care about it for the result decls not the ones
-- before the binder's type.

withSimpBinder
  :: BinderAndDecls CoreIR i i'
  -> (forall i'' o'. DExt o o' => CType i'' -> SimplifyM i'' o' (SType o'))
  -> (forall o' . DExt o o' => BinderAndDecls SimpIR o o' -> SimplifyM i' o' a)
  -> SimplifyM i o a
withSimpBinder _ _ _ = undefined

withSimpBinders
  :: Binders CoreIR i i'
  -> (forall i'' o'. DExt o o' => CType i'' -> SimplifyM i'' o' (SType o'))
  -> (forall o' . DExt o o' => Binders SimpIR o o' -> SimplifyM i' o' a)
  -> SimplifyM i o a
withSimpBinders _ _ _ = undefined

withSimpDecls
  :: Decls CoreIR i i'
  -> (forall o'. DExt o o' => Decls SimpIR o o' -> SimplifyM i' o' a)
  -> SimplifyM i o a
withSimpDecls _ _ = undefined

instantiateSimp
  :: Emits o
  => Binders CoreIR i i'
  -> [CAtom o]
  -> SimplifyM i' o a
  -> SimplifyM i  o a
instantiateSimp _ _ = undefined

liftBuilderSimp :: SBuilderEmits m o => BuilderM CoreIR o a -> m o a
liftBuilderSimp = undefined

-- TODO: this should go in Builder
emitDeclsSubst :: (Builder2 r m, Emits o, SubstReader AtomSubstVal m)
               => Nest (Decl r) i i' -> m i' o a -> m i o a
emitDeclsSubst = undefined
