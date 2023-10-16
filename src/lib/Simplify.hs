-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module Simplify
  ( simplifyTopBlock, simplifyTopFunction, ReconstructAtom (..),
    linearizeTopFun, SimplifiedTopLam (..)) where

import Control.Applicative
import Control.Category ((>>>))
import Control.Monad
import Control.Monad.Trans.Maybe
import Control.Monad.Reader
import Data.Maybe
import Data.Text.Prettyprint.Doc (Pretty (..), hardline)

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
import Optimize (peepholeOp)
import QueryType
import RuntimePrint
import Transpose
import Types.Core
import Types.Source
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

type SimpSubstVal = SubstVal SimpAtom' :: C -> S -> *

liftSimpFun :: LamExpr SimpIR o -> SimplifyM i o (SimpAtom o)
liftSimpFun = undefined -- (Pi piTy) f = return $ SimpInCore $ LiftSimpFun piTy f
-- liftSimpFun _ _ = error "not a pi type"

prodSimpAtom :: [SimpAtom n] -> SimplifyM i n (SimpAtom n)
prodSimpAtom = undefined  -- TODO: make some fresh CoreIR binders and put them in a pair and with a two-component Subst

pairSimpAtom :: SimpAtom n -> SimpAtom n -> SimplifyM i n (SimpAtom n)
pairSimpAtom = undefined  -- TODO: make some fresh CoreIR binders and put them in a pair and with a two-component Subst

getUnpackedSimpAtom :: SimpAtom n -> SimplifyM i n [SimpAtom n]
getUnpackedSimpAtom = undefined

withSusp :: SuspendedCAtom o -> (forall i'. CAtom i' -> SimplifyM i' o a) -> SimplifyM i o a
withSusp (SuspendedSubst (Abs bs e) xs) cont = dropSubst $ extendSubst (bs@@>(SubstVal<$>xs)) $ cont e

simpAtomToDataAtom :: SimpAtom o -> SimplifyM i o (Maybe (SAtom o))
simpAtomToDataAtom = \case
  SimpLift x -> return $ Just x
  SimpSuspend _ -> return Nothing

toDataAtom :: CAtom i -> SimplifyM i o (Maybe (SAtom o))
toDataAtom x = getRepType (getType x) >>= \case
  Nothing -> return Nothing
  Just _ -> Just <$> toDataAtom' x

toDataSimpAtom :: SimpAtom o -> SimplifyM i o (SAtom o)
toDataSimpAtom = \case
  SimpLift x' -> return x'
  SimpSuspend _ -> error "not runtime-representable data"

data SimplifiedVar (n::S) =
   SVSimpAtom (SimpAtom n)
 | SVNoinlineFun (CAtomVar n) (CType n) (CAtom n)
 | SVFFIFun (CorePiType n) (TopFunName n)

simplifyVar :: CAtomVar i -> SimplifyM i o (SimplifiedVar o)
simplifyVar v = lookupSubstM (atomVarName v) >>= \case
  SubstVal simpAtom -> return $ SVSimpAtom simpAtom
  Rename v' -> lookupAtomName v' >>= \case
    TopAtomBinding b -> return case b of
      TopCAtom f'     -> SVSimpAtom $ SimpSuspend $ SuspendedSubst (Abs Empty f') []
      TopSimpAtom _ x -> SVSimpAtom x
      NoinlineFun t x -> SVNoinlineFun (AtomVar v' t) t x
      FFIFun  t x     -> SVFFIFun t x
    LetBound    _ -> notLocal
    MiscBound   _ -> notLocal
    SolverBound _ -> notLocal
    where notLocal = error "shouldn't have local CAtomNames left"

toDataAtom' :: CAtom i -> SimplifyM i o (SAtom o)
toDataAtom' x = go x where
 go :: CAtom i -> SimplifyM i o (SAtom o)
 go = \case
   Var v -> simplifyVar v >>= \case
     SVSimpAtom simpAtom -> case simpAtom of
       SimpLift x' -> return x'
       SimpSuspend _     -> notData
       TabLam _          -> notData
     SVNoinlineFun _ _ _ -> notData
     SVFFIFun _ _        -> notData
   Con con -> Con <$> case con of
     Lit v -> return $ Lit v
     ProdCon xs -> ProdCon <$> mapM go xs
     SumCon tys tag x -> do
       tys' <- forM tys \ty -> fromJust <$> getRepType ty
       SumCon tys' tag <$> go x
     HeapVal       -> return HeapVal
   PtrVar t v -> PtrVar t <$> substM v
   DepPair x y ty -> do
     Just (DepPairTy ty') <- getRepType $ DepPairTy ty
     DepPair <$> go x <*> go y <*> pure ty'
   ProjectElt _ UnwrapNewtype x -> go x
   -- TODO: do we need to think about a case like `fst (1, \x.x)`, where
   -- the projection is data but the argument isn't?
   ProjectElt _ (ProjectProduct i) x -> undefined -- normalizeProj (ProjectProduct i) =<< go x
   NewtypeCon _ x  -> go x
   Lam _           -> notData
   DictCon _ _     -> notData
   Eff _           -> notData
   TypeAsAtom _    -> notData
   where notData = error "not a runtime-representable type"
         notLocal = error "shouldn't have local CAtomNames left"

getRepType :: CType i -> SimplifyM i o (Maybe (SType o))
getRepType tyTop = runMaybeT $ go tyTop where
 go :: CType i -> MaybeT (SimplifyM i o) (SType o)
 go = \case
   TC con -> TC <$> case con of
     BaseType b  -> return $ BaseType b
     ProdType ts -> ProdType <$> mapM go ts
     SumType  ts -> SumType  <$> mapM go ts
     RefType h a -> do
       h' <- lift $ fromJust <$> toDataAtom h
       RefType h' <$> go a
     TypeKind    -> empty
     HeapType    -> return $ HeapType
   -- DepPairTy (DepPairType expl b@(_:>l) r) -> do
   --   l' <- go l
   --   withFreshBinder (getNameHint b) l' \b' -> do
   --     x <- SimpLift (sink l) (Var $ binderVar b')
   --     r' <- go =<< applySubst (b@>SubstVal x) r
   --     return $ DepPairTy $ DepPairType expl b' r'
   -- TabPi tabTy -> do
   --   let ixTy = tabIxType tabTy
   --   IxType t' d' <- simplifyIxType ixTy
   --   withFreshBinder (getNameHint tabTy) t' \b' -> do
   --     x <- SimpLift (sink $ ixTypeType ixTy) (Var $ binderVar b')
   --     bodyTy' <- go =<< instantiate (sink tabTy) [x]
   --     return $ TabPi $ TabPiType d' b' bodyTy'
   NewtypeTyCon con -> go $ snd $ unwrapNewtypeType con
   Pi _           -> empty
   DictTy _       -> empty
   TyVar _ -> undefined

-- type NaryTabLamExpr = Abs (Nest SBinder) (Abs (Nest SDecl) CAtom)

-- fromNaryTabLam :: Int -> CAtom n -> Maybe (Int, NaryTabLamExpr n)
-- fromNaryTabLam maxDepth | maxDepth <= 0 = error "expected positive number of args"
-- fromNaryTabLam maxDepth = \case
--   SimpInCore (TabLam _ (PairE _ (Abs b body))) ->
--     extend <|> (Just $ (1, Abs (Nest b Empty) body))
--     where
--       extend = case body of
--         Abs Empty lam | maxDepth > 1 -> do
--           (d, Abs (Nest b2 bs2) body2) <- fromNaryTabLam (maxDepth - 1) lam
--           return $ (d + 1, Abs (Nest b (Nest b2 bs2)) body2)
--         _ -> Nothing
--   _ -> Nothing

-- forceACase :: Emits n => SAtom n -> [Abs SBinder CAtom n] -> CType i -> SimplifyM i n (SAtom n)
-- forceACase scrut alts resultTy = do
--   resultTy' <- getRepType  resultTy
--   buildCase scrut resultTy' \i arg -> do
--     Abs b result <- return $ alts !! i
--     applySubst (b@>SubstVal (SimpAtom arg)) result >>= toDataAtom

-- === Reconstructions ===

data ReconstructAtom (n::S) =
   CoerceRecon
 | LamRecon (ReconAbs SimpIR SuspendedCAtom n)

applyRecon :: Emits o => ReconstructAtom o -> SAtom o -> SimplifyM i o (SimpAtom o)
applyRecon CoerceRecon x = return $ SimpLift x
applyRecon (LamRecon ab) x = SimpSuspend <$> applyReconAbs ab x

-- === Simplification monad ===

newtype SimplifyM (i::S) (o::S) (a:: *) = SimplifyM
  { runSimplifyM'
    :: SubstReaderT SimpSubstVal (DoubleBuilderT SimpIR TopEnvFrag  HardFailM) i o a }
  deriving ( Functor, Applicative, Monad, ScopeReader, EnvExtender, Fallible
           , EnvReader, SubstReader SimpSubstVal, MonadFail
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

deriving instance ScopableBuilder SimpIR (SimplifyM i)

-- === Top-level API ===

data SimplifiedTopLam n = SimplifiedTopLam (STopLam n) (ReconstructAtom n)
data SimplifiedBlock n = SimplifiedBlock (SBlock n) (ReconstructAtom n)

simplifyTopBlock
  :: (TopBuilder m, Mut n) => TopBlock CoreIR n -> m n (SimplifiedTopLam n)
simplifyTopBlock (TopLam _ _ (LamExpr Empty body)) = do
  SimplifiedBlock block recon <- liftSimplifyM do
    {-# SCC "Simplify" #-} buildSimplifiedBlock $ simplifyBlock body
  topLam <- asTopLam $ LamExpr Empty block
  return $ SimplifiedTopLam topLam recon
simplifyTopBlock _ = error "not a block (nullary lambda)"

simplifyTopFunction :: (TopBuilder m, Mut n) => CTopLam n -> m n (STopLam n)
simplifyTopFunction (TopLam False _ f) = do
  asTopLam =<< liftSimplifyM do
    (lam, CoerceReconAbs) <- {-# SCC "Simplify" #-} simplifyLam f
    return lam
simplifyTopFunction _ = error "shouldn't be in destination-passing style already"

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
  checkE (SimplifiedBlock block recon) = do
    block' <- renameM block
    effTy <- blockEffTy block' -- TODO: store this in the simplified block instead
    block'' <- dropSubst $ checkBlock effTy block'
    recon' <- renameM recon -- TODO: CheckableE instance for the recon too
    return $ SimplifiedBlock block'' recon'

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
  :: Emits o => Subst SimpSubstVal l o -> Nest (Decl CoreIR) l i'
  -> SimplifyM i o (Subst SimpSubstVal i' o)
simpDeclsSubst !s = \case
  Empty -> return s
  Nest (Let b (DeclBinding _ expr)) rest -> do
    let hint = (getNameHint b)
    x <- withSubst s $ simplifyExpr hint expr
    simpDeclsSubst (s <>> (b@>SubstVal x)) rest

simplifyAtom :: Atom CoreIR i -> SimplifyM i o (SimpAtom o)
simplifyAtom x = do
  toDataAtom x >>= \case
    Nothing -> SimpSuspend <$> suspendSubst x
    Just x' -> return $ SimpLift x'

simplifyExpr :: Emits o => NameHint -> Expr CoreIR i -> SimplifyM i o (SimpAtom o)
simplifyExpr hint expr = confuseGHC >>= \_ -> case expr of
  App (EffTy _ ty) f xs -> do
    xs' <- mapM simplifyAtom xs
    simplifyApp f xs'
  TabApp _ f xs -> do
    xs' <- mapM simplifyAtom xs
    f'  <- simplifyAtom f
    simplifyTabApp f' xs'
  Atom x -> simplifyAtom x
  PrimOp  op  -> simplifyOp hint op
  ApplyMethod (EffTy _ ty) dict i xs -> do
    xs' <- mapM simplifyAtom xs
    applyDictMethod ty dict i xs'
  TabCon _ ty xs -> do
    Just tySimp <- getRepType ty
    xs' <- forM xs \x -> fromJust <$> toDataAtom x
    SimpLift <$> emitExpr (TabCon Nothing tySimp xs')
  Case scrut alts (EffTy _ resultTy) -> do
    defuncCaseCore scrut resultTy \i x -> do
      Abs b body <- return $ alts !! i
      extendSubst (b@>SubstVal x) $ simplifyBlock body

simplifyRefOp :: Emits o => RefOp CoreIR i -> SAtom o -> SimplifyM i o (SAtom o)
simplifyRefOp op ref = case op of
  MExtend (BaseMonoid em cb) x -> do
    Just em'  <- toDataAtom em
    Just x'   <- toDataAtom x
    (cb', CoerceReconAbs) <- simplifyLam cb
    emitRefOp $ MExtend (BaseMonoid em' cb') x'
  MGet   -> emitOp $ RefOp ref MGet
  MPut x -> do
    Just x' <- toDataAtom x
    emitRefOp $ MPut x'
  MAsk   -> emitRefOp MAsk
  IndexRef _ x -> do
    Just x' <- toDataAtom x
    emitOp =<< mkIndexRef ref x'
  ProjRef _ (ProjectProduct i) -> emitOp =<< mkProjRef ref (ProjectProduct i)
  ProjRef _ UnwrapNewtype -> return ref
  where emitRefOp op' = emitOp $ RefOp ref op'

defuncCaseCore :: Emits o
  => CAtom i -> CType i
  -> (forall o'. (Emits o', DExt o o') => Int -> SimpAtom o' -> SimplifyM i o' (SimpAtom o'))
  -> SimplifyM i o (SimpAtom o)
defuncCaseCore scrut resultTy cont = do
  toDataAtom scrut >>= \case
    Just scrutSimp -> defuncCase scrutSimp resultTy \i x -> cont i (SimpLift x)
    Nothing -> case trySelectBranch scrut of
      Just (i, arg) -> getDistinct >>= \Distinct -> cont i =<< simplifyAtom arg
      -- Nothing -> go scrut where
      --   go = \case
      --     SimpInCore (ACase scrutSimp alts _) -> do
      --       defuncCase scrutSimp resultTy \i x -> do
      --         Abs altb altAtom <- return $ alts !! i
      --         altAtom' <- applySubst (altb @> SubstVal x) altAtom
      --         cont i altAtom'
      --     NewtypeCon con scrut' | isSumCon con -> go scrut'
      --     _ -> nope
      --   nope = error $ "Don't know how to scrutinize non-data " ++ pprint scrut

defuncCase :: Emits o
  => Atom SimpIR o -> CType i
  -> (forall o'. (Emits o', DExt o o') => Int -> SAtom o' -> SimplifyM i o' (SimpAtom o'))
  -> SimplifyM i o (SimpAtom o)
defuncCase scrut resultTy cont = do
  case trySelectBranch scrut of
    Just (i, arg) -> getDistinct >>= \Distinct -> cont i arg
    Nothing -> do
      altBinderTys <- caseAltsBinderTys (getType scrut)
      getRepType resultTy >>= \case
        Just resultTyData -> do
          alts' <- forM (enumerate altBinderTys) \(i, bTy) -> do
            buildAbs noHint bTy \x -> do
              buildBlock do
                ans <- cont i (sink $ Var x)
                undefined -- toDataAtom
          caseExpr <- mkCase scrut resultTyData alts'
          SimpLift <$> emitExpr caseExpr
        -- Nothing -> do
        --   split <- splitDataComponents resultTy
        --   (alts', closureTys, recons) <- unzip3 <$> forM (enumerate altBinderTys) \(i, bTy) -> do
        --      simplifyAlt split bTy $ cont i
        --   let closureSumTy = SumTy closureTys
        --   alts'' <- forM (enumerate alts') \(i, alt) -> injectAltResult closureTys i alt
        --   caseExpr <- mkCase scrut  (PairTy (dataTy split) closureSumTy) alts''
        --   caseResult <- emitExpr $ caseExpr
        --   (dataVal, sumVal) <- fromPair caseResult
        --   reconAlts <- forM (zip closureTys recons) \(ty, recon) ->
        --     buildAbs noHint ty \v -> applyRecon (sink recon) v
        --   let nonDataVal = undefined -- SimpInCore $ ACase sumVal reconAlts newNonDataTy
        --   Distinct <- getDistinct
        --   fromSplit split dataVal nonDataVal

simplifyAlt
  :: SplitDataNonData n
  -> SType o
  -> (forall o'. (Emits o', DExt o o') => SAtom o' -> SimplifyM i o' (SimpAtom o'))
  -> SimplifyM i o (Alt SimpIR o, SType o, ReconstructAtom o)
simplifyAlt split ty cont = do
  withFreshBinder noHint ty \b -> do
    ab <- buildScoped $ cont $ sink $ Var $ binderVar b
    (body, recon) <- refreshAbs ab \decls result -> do
      let locals = toScopeFrag b >>> toScopeFrag decls
      -- TODO: this might be too cautious. The type only needs to
      -- be hoistable above the decls. In principle it can still
      -- mention vars from the lambda binders.
      Distinct <- getDistinct
      (resultData, SimpSuspend resultNonData) <- toSplit split result
      (newResult, reconAbs) <- telescopicCapture locals resultNonData
      return (Abs decls (PairVal resultData newResult), LamRecon reconAbs)
    EffTy _ (PairTy _ nonDataType) <- blockEffTy body
    let nonDataType' = ignoreHoistFailure $ hoist b nonDataType
    return (Abs b body, nonDataType', recon)

simplifyApp
  :: forall i o. Emits o
  => CAtom i -> [SimpAtom o] -> SimplifyM i o (SimpAtom o)
simplifyApp f xs = case f of
  Lam (CoreLamExpr _ (LamExpr bs body)) ->
    extendSubst (bs@@>(SubstVal<$>xs)) (simplifyBlock body)
  Var v -> simplifyVar v >>= \case
    SVSimpAtom simpAtom -> case simpAtom of
      SimpSuspend susp -> withSusp susp \f' -> simplifyApp f' xs
      SimpLift    _ -> error "not a function"
      TabLam      _ -> error "not a function"
    SVNoinlineFun v'' _ _ -> simplifyTopFunApp v'' xs
    SVFFIFun _ f' -> do
      xs' <- forM xs \(SimpLift x) -> return x
      SimpLift <$> naryTopApp f' xs'

simplifyTopFunApp :: Emits o => CAtomVar o -> [SimpAtom o] -> SimplifyM i o (SimpAtom o)
simplifyTopFunApp fName xs = undefined
  -- Pi piTy <- return $ getType fName
  -- (xsGeneralized, runtimeArgs) <- generalizeArgs piTy xs
  -- let spec = AppSpecialization fName xsGeneralized
  -- Just specializedFunction <- getSpecializedFunction spec >>= emitHoistedEnv
  -- runtimeArgs' <- mapM toDataAtom runtimeArgs
  -- SimpLift <$> naryTopApp specializedFunction runtimeArgs'

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
    TopAtomBinding (NoinlineFun _ f') <- lookupAtomName (atomVarName (sink f))
    ListE staticArgs' <- applyRename (bs@@>(atomVarName <$> runtimeArgs)) staticArgs
    naryApp f' staticArgs'

simplifyTabApp :: forall i o. Emits o
  => SimpAtom o -> [SimpAtom o] -> SimplifyM i o (SimpAtom o)
simplifyTabApp f [] = return f
-- simplifyTabApp f@(SimpInCore sic) xs = case sic of
--   TabLam _ _ -> do
--     case fromNaryTabLam (length xs) f of
--       Just (bsCount, ab) -> do
--         let (xsPref, xsRest) = splitAt bsCount xs
--         xsPref' <- mapM toDataAtom xsPref
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
--     xs' <- mapM toDataAtom xs
--     SimpLift resultTy =<< naryTabApp f' xs'
--   LiftSimpFun _ _ -> error "not implemented"
-- simplifyTabApp f _ = error $ "Unexpected table: " ++ pprint f

simplifyIxType :: IxType CoreIR i -> SimplifyM i o (IxType SimpIR o)
simplifyIxType (IxType t ixDict) = do
  Just t' <- getRepType t
  IxType t' <$> case ixDict of
    IxDictAtom (DictCon _ (IxFin n)) -> do
      Just n' <- toDataAtom n
      return $ IxDictRawFin n'
    IxDictAtom d -> undefined
    -- IxDictAtom d -> do
    --   (dictAbs, params) <- generalizeIxDict =<< cheapNormalize d
    --   params' <- forM params \p -> fromJust <$> toDataAtom p
    --   sdName <- requireIxDictCache dictAbs
    --   return $ IxDictSpecialized t' sdName params'
    IxDictRawFin n            -> do
      Just n' <- toDataAtom n
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
simplifyDictMethod absDict@(Abs bs dict) method = do
  ty <- liftEnvReaderM $ ixMethodType method absDict
  lamExpr <- liftBuilder $ buildTopLamFromPi ty \allArgs -> do
    let (extraArgs, methodArgs) = splitAt (nestLength bs) allArgs
    dict' <- applyRename (bs @@> (atomVarName <$> extraArgs)) dict
    emitExpr =<< mkApplyMethod dict' (fromEnum method) (Var <$> methodArgs)
  simplifyTopFunction lamExpr

ixMethodType :: IxMethod -> AbsDict n -> EnvReaderM n (PiType CoreIR n)
ixMethodType method absDict = do
  refreshAbs absDict \extraArgBs dict -> do
    CorePiType _ _ methodArgs (EffTy _ resultTy) <- getMethodType dict (fromEnum method)
    let allBs = extraArgBs >>> methodArgs
    return $ PiType allBs (EffTy Pure resultTy)

-- Assumes first order (args/results are "data", allowing newtypes), monormophic
simplifyLam
  :: LamExpr CoreIR i
  -> SimplifyM i o (LamExpr SimpIR o, Abs (Nest (AtomNameBinder SimpIR)) ReconstructAtom o)
simplifyLam (LamExpr bsTop body) = case bsTop of
  Nest (b:>ty) bs -> do
    Just tySimp <- getRepType ty
    withFreshBinder (getNameHint b) tySimp \b''@(b':>_) -> do
      let x = SimpLift $ Var $ binderVar b''
      extendSubst (b@>SubstVal x) do
        (LamExpr bs' body', Abs bsRecon recon) <- simplifyLam $ LamExpr bs body
        return (LamExpr (Nest (b':>tySimp) bs') body', Abs (Nest b' bsRecon) recon)
  Empty -> do
    SimplifiedBlock body' recon <- buildSimplifiedBlock $ simplifyBlock body
    return (LamExpr Empty body', Abs Empty recon)

data SplitDataNonData n = SplitDataNonData
  { dataTy    :: Type SimpIR n
  , toSplit   :: forall i l . SimpAtom l -> SimplifyM i l (SAtom l, SimpAtom l)
  , fromSplit :: forall i l . DExt n l => SAtom l -> SimpAtom l -> SimplifyM i l (SimpAtom l) }

-- bijection between that type and a (data, non-data) pair type.
splitDataComponents :: CType i -> SimplifyM i n (SplitDataNonData n)
splitDataComponents = \case
  ProdTy tys -> do
    splits <- mapM splitDataComponents tys
    return $ SplitDataNonData
      { dataTy    = ProdTy $ map dataTy    splits
      , toSplit = \xProd -> do
          xs <- getUnpackedSimpAtom xProd
          (ys, zs) <- unzip <$> forM (zip xs splits) \(x, split) -> toSplit split x
          ys' <- return $ ProdVal ys
          zs' <- prodSimpAtom zs
          return (ys', zs')
      , fromSplit = \xsProd ysProd -> do
          xs <- getUnpacked xsProd
          ys <- getUnpackedSimpAtom ysProd
          zs <- forM (zip (zip xs ys) splits) \((x, y), split) -> fromSplit split x y
          prodSimpAtom zs }
  -- ty -> tryGetRepType ty >>= \case
  --   Just repTy -> return $ SplitDataNonData
  --     { dataTy = repTy
  --     , nonDataTy = UnitTy
  --     , toSplit = \x -> (,UnitVal) <$> toDataAtomAssumeNoDecls x
  --     , fromSplit = \x _ -> SimpLift (sink ty) x }
  --   Nothing -> return $ SplitDataNonData
  --     { dataTy = UnitTy
  --     , nonDataTy = ty
  --     , toSplit = \x -> return (UnitVal, x)
  --     , fromSplit = \_ x -> return x }

buildSimplifiedBlock
  :: (forall o'. (Emits o', DExt o o') => SimplifyM i o' (SimpAtom o'))
  -> SimplifyM i o (SimplifiedBlock o)
buildSimplifiedBlock cont = do
  Abs decls result <- buildScoped cont
  case result of
    SimpSuspend ans -> do
      (block, recon) <- refreshAbs (Abs decls ans) \decls' ans' -> do
        (newResult, reconAbs) <- telescopicCapture (toScopeFrag decls') ans'
        return (Abs decls' newResult, LamRecon reconAbs)
      return $ SimplifiedBlock block recon
    SimpLift ans ->
      return $ SimplifiedBlock (Abs decls ans) CoerceRecon

simplifyOp :: Emits o => NameHint -> PrimOp CoreIR i -> SimplifyM i o (SimpAtom o)
simplifyOp hint op = case op of
  Hof (TypedHof _ hof) -> simplifyHof hof
  MemOp    op' -> simplifyGenericOp op'
  VectorOp op' -> simplifyGenericOp op'
  RefOp ref eff -> do
    Just ref' <- toDataAtom ref
    SimpLift <$> simplifyRefOp eff ref'
  BinOp binop x' y' -> do
    Just x <- toDataAtom x'
    Just y <- toDataAtom y'
    SimpLift <$> case binop of
      ISub -> isub x y
      IAdd -> iadd x y
      IMul -> imul x y
      IDiv -> idiv x y
      ICmp Less  -> ilt x y
      ICmp Equal -> ieq x y
      _ -> emitOp $ BinOp binop x y
  UnOp unOp x' -> do
    Just x <- toDataAtom x'
    SimpLift <$> emitOp (UnOp unOp x)
  MiscOp op' -> case op' of
    Select c' x' y' -> do
      Just c <- toDataAtom c'
      Just x <- toDataAtom x'
      Just y <- toDataAtom y'
      SimpLift <$> select c x y
    ShowAny x' -> undefined -- do
      -- x <- simplifyAtom x'
      -- dropSubst $ showAny x >>= simplifyBlock
    _ -> simplifyGenericOp op'

simplifyGenericOp
  :: (GenericOp op, IsPrimOp op, HasType CoreIR (op CoreIR), Emits o,
      OpConst op CoreIR ~ OpConst op SimpIR)
  => op CoreIR i
  -> SimplifyM i o (SimpAtom o)
simplifyGenericOp op = do
  op' <- traverseOp op
           (\x -> fromJust <$> getRepType x)
           (\x -> fromJust <$> toDataAtom x)
           (error "shouldn't have lambda left")
  liftM SimpLift $ liftEnvReaderM (peepholeOp $ toPrimOp op') >>= emitExprToAtom
{-# INLINE simplifyGenericOp #-}

pattern CoerceReconAbs :: Abs (Nest b) ReconstructAtom n
pattern CoerceReconAbs <- Abs _ CoerceRecon

applyDictMethod :: Emits o => CType i -> CAtom i -> Int -> [SimpAtom o] -> SimplifyM i o (SimpAtom o)
applyDictMethod resultTy d i methodArgs = do
  cheapNormalize d >>= \case
    DictCon _ (InstanceDict instanceName instanceArgs) -> dropSubst do
      instanceArgs' <- mapM simplifyAtom instanceArgs
      instanceDef <- lookupInstanceDef instanceName
      withInstantiated instanceDef instanceArgs' \(PairE _ body) -> do
        let InstanceBody _ methods = body
        let method = methods !! i
        simplifyApp noHint resultTy method methodArgs
  --   DictCon _ (IxFin n) -> applyIxFinMethod (toEnum i) n methodArgs
  --   d' -> error $ "Not a simplified dict: " ++ pprint d'
  -- where
  --   applyIxFinMethod :: EnvReader m => IxMethod -> CAtom n -> [CAtom n] -> m n (CAtom n)
  --   applyIxFinMethod method n args = do
  --     case (method, args) of
  --       (Size, []) -> return n  -- result : Nat
  --       (Ordinal, [ix]) -> unwrapNewtype ix -- result : Nat
  --       (UnsafeFromOrdinal, [ix]) -> return $ NewtypeCon (FinCon n) ix
  --       _ -> error "bad ix args"

simplifyHof :: Emits o => Hof CoreIR i -> SimplifyM i o (SimpAtom o)
simplifyHof = \case
  For d ixTypeCore lam -> do
    (lam', Abs (UnaryNest bIx) recon) <- simplifyLam lam
    ixTypeSimp <- simplifyIxType ixTypeCore
    ans <- emitHof $ For d ixTypeSimp lam'
    case recon of
      CoerceRecon -> return $ SimpLift ans
      LamRecon (Abs bsClosure reconResult) -> liftM TabLam do
        PairE ixTypeSimp <$> buildAbs noHint (ixTypeType ixTypeSimp) \i -> buildScoped do
          i' <- sinkM i
          xs <- unpackTelescope bsClosure =<< tabApp (sink ans) (Var i')
          vs <- mapM emitAtom xs
          let substFrag = bIx@>(atomVarName i') <.> bsClosure @@> (atomVarName <$> vs)
          SimpSuspend <$> applyRename substFrag reconResult
  While body -> do
    SimplifiedBlock body' CoerceRecon <- buildSimplifiedBlock $ simplifyBlock body
    liftM SimpLift $ emitHof $ While body'
  RunReader r lam -> do
    Just r' <- toDataAtom r
    (lam', Abs b recon) <- simplifyLam lam
    ans <- emitHof $ RunReader r' lam'
    let recon' = ignoreHoistFailure $ hoist b recon
    applyRecon recon' ans
  RunWriter Nothing (BaseMonoid e combine) lam -> do
    LamExpr (BinaryNest h (_:>RefTy _ wTy)) _ <- return lam
    Just e' <- toDataAtom e
    (combine', CoerceReconAbs) <- simplifyLam combine
    (lam', Abs b recon) <- simplifyLam lam
    (ans, w) <- fromPair =<< emitHof (RunWriter Nothing (BaseMonoid e' combine') lam')
    let recon' = ignoreHoistFailure $ hoist b recon
    ans' <- applyRecon recon' ans
    pairSimpAtom ans' (SimpLift w)
  RunWriter _ _ _ -> error "Shouldn't see a RunWriter with a dest in Simplify"
  RunState Nothing s lam -> do
    Just s' <- toDataAtom s
    (lam', Abs b recon) <- simplifyLam lam
    resultPair <- emitHof $ RunState Nothing s' lam'
    (ans, sOut) <- fromPair resultPair
    let recon' = ignoreHoistFailure $ hoist b recon
    ans' <- applyRecon recon' ans
    pairSimpAtom ans' (SimpLift sOut)
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
    Just x' <- toDataAtom x
    -- XXX: we're ignoring the result type here, which only makes sense if we're
    -- dealing with functions on simple types.
    (lam', recon) <- simplifyLam lam
    CoerceReconAbs <- return recon
    (result, linFun) <- liftDoubleBuilderToSimplifyM $ linearize lam' x'
    let result' = SimpLift result
    linFun' <- liftSimpFun linFun
    pairSimpAtom result' linFun'
  Transpose lam x -> do
    (lam', CoerceReconAbs) <- simplifyLam lam
    Just x' <- toDataAtom x
    SimpLift <$> transpose lam' x'
  -- CatchException _ body-> do
  --   SimplifiedBlock body' recon <- buildSimplifiedBlock $ simplifyBlock body
  --   simplifiedResultTy <- blockTy body'
  --   block <- liftBuilder $ runSubstReaderT idSubst $ buildBlock $
  --     exceptToMaybeBlock (sink simplifiedResultTy) body'
  --   result <- emitBlock block
  --   case recon of
  --     CoerceRecon ty -> do
  --       maybeTy <- makePreludeMaybeTy ty
  --       liftSimpAtom maybeTy result
  --     LamRecon reconAbs -> fmapMaybe result (applyReconAbs $ sink reconAbs)

-- -- takes an internal SimpIR Maybe to a CoreIR "prelude Maybe"
-- fmapMaybe
--   :: (EnvReader m, EnvExtender m)
--   => SAtom n -> (forall l. DExt n l => SAtom l -> m l (CAtom l))
--   -> m n (CAtom n)
-- fmapMaybe scrut f = do
--   ~(MaybeTy justTy) <- return $ getType scrut
--   (justAlt, resultJustTy) <- withFreshBinder noHint justTy \b -> do
--     result <- f (Var $ binderVar b)
--     resultTy <- return $ ignoreHoistFailure $ hoist b (getType result)
--     result' <- preludeJustVal result
--     return (Abs b result', resultTy)
--   nothingAlt <- buildAbs noHint UnitTy \_ -> preludeNothingVal $ sink resultJustTy
--   resultMaybeTy <- makePreludeMaybeTy resultJustTy
--   return $ SimpInCore $ ACase scrut [nothingAlt, justAlt] resultMaybeTy

-- -- This is wrong! The correct implementation is below. And yet there's some
-- -- compensatory bug somewhere that means that the wrong answer works and the
-- -- right answer doesn't. Need to investigate.
-- preludeJustVal :: EnvReader m => CAtom n -> m n (SimpAtom n)
-- preludeJustVal x = return x
--   -- xTy <- getType x
--   -- con <- preludeMaybeNewtypeCon xTy
--   -- return $ NewtypeCon con (JustAtom xTy x)

-- preludeNothingVal :: EnvReader m => CType n -> m n (SimpAtom n)
-- preludeNothingVal ty = do
--   con <- preludeMaybeNewtypeCon ty
--   return $ NewtypeCon con (NothingAtom ty)

-- preludeMaybeNewtypeCon :: EnvReader m => CType n -> m n (NewtypeCon n)
-- preludeMaybeNewtypeCon ty = do
--   ~(Just (UTyConVar tyConName)) <- lookupSourceMap "Maybe"
--   TyConDef sn _ _ _ <- lookupTyCon tyConName
--   let params = TyConParams [Explicit] [Type ty]
--   return $ UserADTData sn tyConName params

simplifyBlock :: Emits o => Block CoreIR i -> SimplifyM i o (SimpAtom o)
simplifyBlock (Abs decls result) = simplifyDecls decls $ simplifyAtom result

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

-- withSimplifiedBinders
--  :: Nest (Binder CoreIR) o any
--  -> (forall o'. DExt o o' => Nest (Binder SimpIR) o o' -> [SimpAtom o'] -> SimplifyM i o' a)
--  -> SimplifyM i o a
-- withSimplifiedBinders Empty cont = getDistinct >>= \Distinct -> cont Empty []
-- withSimplifiedBinders (Nest (bCore:>ty) bsCore) cont = do
--   simpTy <- getRepType ty
--   withFreshBinder (getNameHint bCore) simpTy \bSimp -> do
--     x <- liftSimpAtom (Var $ binderVar bSimp)
--     -- TODO: carry a substitution instead of doing N^2 work like this
--     Abs bsCore' UnitE <- applySubst (bCore@>SubstVal x) (EmptyAbs bsCore)
--     withSimplifiedBinders bsCore' \bsSimp xs ->
--       cont (Nest bSimp bsSimp) (sink x:xs)

simplifyCustomLinearization
  :: Abstracted CoreIR (ListE CAtom) n -> [Active] -> AtomRules n
  -> SimplifyM i n (PairE STopLam STopLam n)
simplifyCustomLinearization (Abs runtimeBs staticArgs) actives rule = undefined
-- simplifyCustomLinearization (Abs runtimeBs staticArgs) actives rule = do
--   CustomLinearize nImplicit nExplicit zeros fCustom <- return rule
--   linearized <- withSimplifiedBinders runtimeBs \runtimeBs' runtimeArgs -> do
--       Abs runtimeBs' <$> buildScoped do
--         ListE staticArgs' <- instantiate (sink $ Abs runtimeBs staticArgs) (sink <$> runtimeArgs)
--         fCustom' <- sinkM fCustom
--         resultTy <- typeOfApp (getType fCustom') staticArgs'
--         pairResult <- dropSubst $ simplifyApp noHint resultTy fCustom' staticArgs'
--         (primalResult, fLin) <- fromPair pairResult
--         primalResult' <- toDataAtom primalResult
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
--           toDataAtom tangentResult
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

--     fromNonDepNest :: Nest CBinder n l -> [CType n]
--     fromNonDepNest Empty = []
--     fromNonDepNest (Nest b bs) =
--       case ignoreHoistFailure $ hoist b (Abs bs UnitE) of
--         Abs bs' UnitE -> binderType b : fromNonDepNest bs'

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
  let primalFun = LamExpr bs declsAndResult
  LamExpr residualAndTangentBs tangentBody <- buildLamExpr residualsTangentsBs \(residuals:tangents) -> do
    LamExpr tangentBs' body <- applyReconAbs (sink reconAbs) (Var residuals)
    applyRename (tangentBs' @@> (atomVarName <$> tangents)) body >>= emitBlock
  let tangentFun = LamExpr (bs >>> residualAndTangentBs) tangentBody
  return $ PairE primalFun tangentFun

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
  Case e alts (EffTy _ resultTy) -> do
    e' <- substM e
    resultTy' <- substM $ MaybeTy resultTy
    buildCase e' resultTy' \i v -> do
      Abs b body <- return $ alts !! i
      extendSubst (b @> SubstVal v) do
        blockResultTy <- blockTy =<< substM body -- TODO: avoid this by caching the type
        exceptToMaybeBlock blockResultTy body
  Atom x -> do
    x' <- substM x
    let ty = getType x'
    return $ JustAtom ty x'
  PrimOp (Hof (TypedHof _ (For ann ixTy' (UnaryLamExpr b body)))) -> do
    ixTy <- substM ixTy'
    maybes <- buildForAnn (getNameHint b) ann ixTy \i -> do
      extendSubst (b@>Rename (atomVarName i)) do
        blockResultTy <- blockTy =<< substM body -- TODO: avoid this by caching the type
        exceptToMaybeBlock blockResultTy body
    catMaybesE maybes
  PrimOp (MiscOp (ThrowException _)) -> do
    ty <- substM $ getType expr
    return $ NothingAtom ty
  PrimOp (Hof (TypedHof _ (RunState Nothing s lam))) -> do
    s' <- substM s
    BinaryLamExpr h ref body <- return lam
    result  <- emitRunState noHint s' \h' ref' ->
      extendSubst (h @> Rename (atomVarName h') <.> ref @> Rename (atomVarName ref')) do
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
      extendSubst (h @> Rename (atomVarName h') <.> ref @> Rename (atomVarName ref')) do
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
  _ -> do
    expr' <- substM expr
    case hasExceptions expr' of
      True -> error $ "Unexpected exception-throwing expression: " ++ pprint expr
      False -> do
        v <- emit expr'
        let ty = getType v
        return $ JustAtom ty (Var v)

hasExceptions :: SExpr n -> Bool
hasExceptions expr = case getEffects expr of
  EffectRow effs NoTail -> ExceptionEffect `eSetMember` effs

-- === instances ===

instance GenericE ReconstructAtom where
  type RepE ReconstructAtom = EitherE2 UnitE (ReconAbs SimpIR SuspendedCAtom)

  fromE = \case
    CoerceRecon -> Case0 UnitE
    LamRecon ab -> Case1 ab
  {-# INLINE fromE #-}
  toE = \case
    Case0 UnitE -> CoerceRecon
    Case1 ab    -> LamRecon ab
    _ -> error "impossible"
  {-# INLINE toE #-}

instance SinkableE  ReconstructAtom
instance HoistableE ReconstructAtom
instance RenameE    ReconstructAtom

instance Pretty (ReconstructAtom n) where
  pretty CoerceRecon   = "Coercion reconstruction"
  pretty (LamRecon ab) = undefined -- "Reconstruction abs: " <> pretty ab

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
