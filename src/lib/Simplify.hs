-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module Simplify (simplifyTopBlock, simplifyTopFunction, linearizeTopFun) where

import Control.Category ((>>>))
import Control.Monad
import Control.Monad.Reader
import Data.Maybe

import Builder
import CheapReduction
import Core
import Err
import Generalize
import IRVariants
-- import Linearize
import Name
import Subst
import PPrint
import QueryType
import RuntimePrint
-- import Transpose
import Types.Core
import Types.Top
import Types.Primitives
import Util (enumerate)

-- === Top-level API ===

simplifyTopBlock
  :: (TopBuilder m, Mut n) => TopBlock CoreIR n -> m n (STopLam n)
simplifyTopBlock (TopLam _ _ (LamExpr Empty body)) = do
  block <- liftSimplifyM do
    buildBlock $ fromSimpAtom <$> simplifyExpr body
  asTopLam $ LamExpr Empty block
simplifyTopBlock _ = error "not a block (nullary lambda)"

simplifyTopFunction :: (TopBuilder m, Mut n) => CTopLam n -> m n (STopLam n)
simplifyTopFunction (TopLam False _ f) = do
  asTopLam =<< liftSimplifyM (simplifyLam f)
simplifyTopFunction _ = error "shouldn't be in destination-passing style already"

-- === Simplification monad ===

class (ScopableBuilder2 SimpIR m, SubstReader SimpSubstVal m) => Simplifier m

newtype SimplifyM (i::S) (o::S) (a:: *) = SimplifyM
  { runSimplifyM'
    :: SubstReaderT SimpSubstVal (DoubleBuilderT SimpIR TopEnvFrag  HardFailM) i o a }
  deriving ( Functor, Applicative, Monad, ScopeReader, EnvExtender, Fallible
           , EnvReader, SubstReader SimpSubstVal, MonadFail
           , Builder SimpIR, HoistingTopBuilder TopEnvFrag)

data SimpValR (r::IR) (n::S) where
  SimpAtom  :: SAtom n                  -> SimpValR CoreIR n
  SimpCCon  :: WithSubst (Con CoreIR) n -> SimpValR CoreIR n
  TopFunVal :: CAtomVar n               -> SimpValR CoreIR n
  FFIFunVal :: TopFunName n             -> SimpValR CoreIR n

type SimpVal = SimpValR CoreIR

data WithSubst (e::E) (o::S) where
  WithSubst :: Subst SimpSubstVal i o -> e i -> WithSubst e o

type SimpSubstVal = SubstVal SimpValR

instance SinkableE (SimpValR r) where
  sinkingProofE _ = undefined

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

-- === simplifying Atoms ===

simplifyAtom :: forall i o . CAtom i -> SimplifyM i o (SimpVal o)
simplifyAtom (Con con) = case con of
  Lit v -> return $ SimpAtom $ toAtom $ Lit v
  ProdCon xs -> SimpAtom . toAtom . ProdCon <$> mapM toDataAtom xs
  SumCon  tys tag x -> SimpAtom . toAtom <$> (SumCon <$> mapM getRepType tys <*> pure tag <*> toDataAtom x)
  DepPair x y ty -> do
    TyCon (DepPairTy ty') <- getRepType $ TyCon $ DepPairTy ty
    SimpAtom . toAtom <$> (DepPair <$> toDataAtom x <*> toDataAtom y <*> pure ty')
  NewtypeCon _ x  -> simplifyAtom x
  Lam _         -> returnCon
  DictConAtom _ -> returnCon
  TyConAtom _   -> returnCon
  where
    returnCon :: SimplifyM i o (SimpVal o)
    returnCon = do
      s <- getSubst
      return $ SimpCCon $ WithSubst s con
simplifyAtom (Stuck _ stuck) = case stuck of
  Var v -> lookupSubstM (atomVarName v) >>= \case
    SubstVal x -> return x
    Rename v' -> lookupAtomName v' >>= \case
      -- This should only be top-level atoms. TODO: consider making that
      -- explicit in the AtomBinding data definition.
      LetBound (DeclBinding _ (Atom (Con con))) ->
        return $ SimpCCon $ WithSubst idSubst con
      NoinlineFun _ _ -> do
        v'' <- toAtomVar v'
        return $ TopFunVal v''
      FFIFunBound _ f -> return $ FFIFunVal f
      _ -> error "shouldn't have other CVars left"
  -- StuckProject i x -> forceStuck x >>= \case
  --   CCLiftSimp _ x' -> returnLifted $ StuckProject i x'
  --   CCCon (WithSubst s con) -> withSubst s case con of
  --     ProdCon xs    -> forceConstructor (xs!!i)
  --     DepPair l r _ -> forceConstructor ([l, r]!!i)
  --     _ -> error "not a product"
  --   CCFun _    -> error "not a product"
  -- StuckTabApp f x -> forceStuck f >>= \case
  --   CCLiftSimp _ f' -> do
  --     x' <- toDataAtom x
  --     returnLifted $ StuckTabApp f' x'
  --   CCCon _ -> error "not a table"
  --   CCFun _ -> error "not a table"
  -- StuckUnwrap x -> forceStuck x >>= \case
  --   CCCon (WithSubst s con) -> case con of
  --     NewtypeCon _ x' -> withSubst s $ forceConstructor x'
  --     _ -> error "not a newtype"
  --   CCLiftSimp _ x' -> returnLifted x'
  --   CCFun    _ -> error "not a newtype"
  InstantiatedGiven _ _ -> error "shouldn't have this left"
  SuperclassProj _ _    -> error "shouldn't have this left"
  PtrVar ty p -> do
    p' <- substM p
    SimpAtom <$> mkStuck (PtrVar ty p')

fromSimpAtom :: SimpVal o -> SAtom o
fromSimpAtom = \case
  SimpAtom x -> x
  x -> error $ "Not a SimpAtom"

toDataAtom :: CAtom i -> SimplifyM i o (SAtom o)
toDataAtom x = fromSimpAtom <$> simplifyAtom x

-- === simplifying types ===

getRepType :: Type CoreIR i -> SimplifyM i o (SType o)
getRepType (StuckTy _ stuck) = undefined
  -- substMStuck stuck >>= \case
  --   Stuck _ _ -> error "shouldn't have stuck CType after substitution"
  --   Con (TyConAtom tyCon) -> dropSubst $ getRepType (TyCon tyCon)
  --   Con _ -> error "not a type"
getRepType (TyCon con) = case con of
  BaseType b  -> return $ toType $ BaseType b
  ProdType ts -> toType . ProdType <$> mapM getRepType ts
  SumType  ts -> toType . SumType  <$> mapM getRepType ts
  RefType a -> toType <$> (RefType <$> getRepType a)
  DepPairTy (DepPairType expl b r) -> do
    withSimplifiedBinder b \b' -> do
      r' <- getRepType r
      return $ toType $ DepPairType expl b' r'
  TabPi (TabPiType ixDict b r) -> do
    ixDict' <- simplifyIxDict ixDict
    withSimplifiedBinder b \b' -> do
      r' <- getRepType r
      return $ toType $ TabPi $ TabPiType ixDict' b' r'
  NewtypeTyCon con' -> undefined
    -- (_, ty') <- unwrapNewtypeType =<< substM con'
    -- dropSubst $ getRepType ty'
  Pi _     -> error notDataType
  DictTy _ -> error notDataType
  Kind _ -> error notDataType
  where notDataType = "Not a type of runtime-representable data"

toDataAtomAssumeNoDecls :: CAtom i -> SimplifyM i o (SAtom o)
toDataAtomAssumeNoDecls x = do
  Abs decls result <- buildScoped $ toDataAtom x
  case decls of
    Empty -> return result
    _ -> error "unexpected decls"

-- === all the bits of IR ===

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
    x <- withSubst s $ simplifyExpr expr
    simpDeclsSubst (s <>> (b@>SubstVal x)) rest

simplifyExpr :: Emits o => Expr CoreIR i -> SimplifyM i o (SimpVal o)
simplifyExpr = \case
  Block _ (Abs decls body) -> simplifyDecls decls $ simplifyExpr body
  App _ f xs -> do
    f' <- simplifyAtom f
    xs' <- mapM simplifyAtom xs
    simplifyApp f' xs'
  TabApp _ f x -> withDistinct do
    x' <- toDataAtom x
    f' <- toDataAtom f
    simplifyTabApp f' x'
  Atom x -> simplifyAtom x
  PrimOp  op  -> simplifyOp op
  Hof (TypedHof (EffTy _ ty) hof) -> simplifyHof hof
  ApplyMethod (EffTy _ ty) dict i xs -> do
    xs' <- mapM simplifyAtom xs
    SimpCCon (WithSubst s (DictConAtom d)) <- simplifyAtom dict
    withSubst s $ applyDictMethod d i xs'
  TabCon ty xs -> do
    tySimp <- getRepType ty
    xs' <- forM xs \x -> toDataAtom x
    SimpAtom <$> emit (TabCon tySimp xs')
  Case scrut alts (EffTy _ resultTy) -> do
    scrut' <- fromSimpAtom <$> simplifyAtom scrut
    resultTy' <- getRepType resultTy
    altBinderTys <- caseAltsBinderTys $ getType scrut'
    alts' <- forM (enumerate altBinderTys) \(i, bTy) -> do
      buildAbs noHint bTy \x -> buildBlock do
        let x' = SimpAtom $ toAtom $ sink x
        Abs b body <- return $ alts !! i
        extendSubst (b@>SubstVal x') do
          fromSimpAtom <$> simplifyExpr body
    result <- emit =<< mkCase scrut' resultTy' alts'
    return $ SimpAtom result
  Project ty i x -> do
    x'  <- toDataAtom x
    SimpAtom <$> proj i x'
  Unwrap _ x -> SimpAtom <$> toDataAtom x

requireReduced :: CExpr o -> SimplifyM i o (CAtom o)
requireReduced expr = reduceExpr expr >>= \case
  Just x -> return x
  Nothing -> error "couldn't reduce expression"

simplifyRefOp :: Emits o => RefOp CoreIR i -> SAtom o -> SimplifyM i o (SAtom o)
simplifyRefOp op ref = case op of
  MGet   -> emit $ RefOp ref MGet
  MPut x -> do
    x' <- toDataAtom x
    emitRefOp $ MPut x'
  IndexRef _ x -> do
    x' <- toDataAtom x
    emit =<< mkIndexRef ref x'
  ProjRef _ (ProjectProduct i) -> emit =<< mkProjRef ref (ProjectProduct i)
  ProjRef _ UnwrapNewtype -> return ref
  where emitRefOp op' = emit $ RefOp ref op'

simplifyApp :: Emits o => SimpVal o -> [SimpVal o] -> SimplifyM i o (SimpVal o)
simplifyApp f xs = case f of
  SimpCCon (WithSubst s con) -> case con of
    Lam (CoreLamExpr _ lam) -> withSubst s $ withInstantiated lam xs \body -> simplifyExpr body
    _ -> error "not a function"
  -- CCFun ccFun -> case ccFun of
  --   CCLiftSimpFun _ lam -> do
  --     xs' <- dropSubst $ mapM toDataAtom xs
  --     result <- instantiate lam xs' >>= emit
  --     liftSimpAtom resultTy result
  --   CCNoInlineFun v _ _ -> simplifyTopFunApp v xs
  --   CCFFIFun _ f' -> do
  --     xs' <- dropSubst $ mapM toDataAtom xs
  --     liftSimpAtom resultTy =<< topApp f' xs'
  -- CCLiftSimp _ _ -> error "not a function"

simplifyTopFunApp :: Emits n => CAtomVar n -> [CAtom n] -> SimplifyM i n (SimpVal n)
simplifyTopFunApp fName xs = undefined
-- simplifyTopFunApp fName xs = do
--   fTy@(TyCon (Pi piTy)) <- return $ getType fName
--   resultTy <- typeOfApp fTy xs
--   isData resultTy >>= \case
--     True -> do
--       (xsGeneralized, runtimeArgs) <- generalizeArgs piTy xs
--       let spec = AppSpecialization fName xsGeneralized
--       Just specializedFunction <- getSpecializedFunction spec >>= emitHoistedEnv
--       runtimeArgs' <- dropSubst $ mapM toDataAtom runtimeArgs
--       SimpAtom <$> topApp specializedFunction runtimeArgs'
--     False ->
--       -- TODO: we should probably just fall back to inlining in this case,
--       -- especially if we want make everything @noinline by default.
--       error $ "can't specialize " ++ pprint fName ++ " " ++ pprint xs

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

simplifyTabApp ::Emits o => SAtom o -> SAtom o -> SimplifyM i o (SimpVal o)
simplifyTabApp f x = undefined
-- simplifyTabApp f x = case f of
--   CCLiftSimp fTy f' -> do
--     f'' <- mkStuck f'
--     SimpAtom <$> tabApp f'' x
--   _ -> error "not a table"

simplifyIxDict :: Dict CoreIR i -> SimplifyM i o (SDict o)
simplifyIxDict (StuckDict _ stuck) = undefined
-- simplifyIxDict (StuckDict _ stuck) = forceStuck stuck >>= \case
--   CCCon (WithSubst s con) -> case con of
--     DictConAtom con' -> withSubst s $ simplifyIxDict (DictCon con')
--     _ -> error "not a dict"
--   CCLiftSimp _ _   -> error "not a dict"
--   CCFun      _     -> error "not a dict"
-- simplifyIxDict (DictCon con) = case con of
--   IxFin n -> DictCon <$> IxRawFin <$> toDataAtomAssumeNoDecls n
--   IxRawFin n -> DictCon <$> IxRawFin <$> toDataAtomAssumeNoDecls n
--   InstanceDict _ _ _ -> undefined
--     -- d <- DictCon <$> substM con
--     -- (dictAbs, params) <- generalizeIxDict d
--     -- params' <- dropSubst $ mapM toDataAtomAssumeNoDecls params
--     -- sdName <- requireIxDictCache dictAbs
--     -- return $ DictCon $ IxSpecialized sdName params'

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
    CorePiType _ _ methodArgs resultTy <- getMethodType dict (fromEnum method)
    let allBs = extraArgBs >>> methodArgs
    return $ PiType allBs resultTy


withSimplifiedBinder
 :: CBinder i i'
 -> (forall o'. DExt o o' => Binder SimpIR o o' -> SimplifyM i' o' a)
 -> SimplifyM i o a
withSimplifiedBinder (b:>ty) cont = do
  tySimp <- getRepType ty
  withFreshBinder (getNameHint b) tySimp \b' -> do
    let x = SimpAtom (toAtom $ binderVar b')
    extendSubst (b@>SubstVal x) $ cont b'

-- Assumes first order (args/results are "data", allowing newtypes), monormophic
simplifyLam
  :: LamExpr CoreIR i
  -> SimplifyM i o (LamExpr SimpIR o)
simplifyLam (LamExpr bsTop body) = case bsTop of
  Nest b bs -> withSimplifiedBinder b \b' -> do
    LamExpr bs' body' <- simplifyLam $ LamExpr bs body
    return $ LamExpr (Nest b' bs') body'
  Empty -> do
    body' <- buildBlock $ fromSimpAtom <$> simplifyExpr body
    return $ LamExpr Empty body'

simplifyOp :: Emits o => PrimOp CoreIR i -> SimplifyM i o (SimpVal o)
simplifyOp op = case op of
  MemOp    op' -> simplifyGenericOp op'
  VectorOp op' -> simplifyGenericOp op'
  RefOp ref eff -> do
    ref' <- toDataAtom ref
    SimpAtom <$> simplifyRefOp eff ref'
  BinOp binop x y -> do
    x' <- toDataAtom x
    y' <- toDataAtom y
    SimpAtom <$> emit (BinOp binop x' y')
  UnOp unOp x -> do
    x' <- toDataAtom x
    SimpAtom <$> emit (UnOp unOp x')
  MiscOp op' -> case op' of
    ShowAny x -> do
      x' <- toDataAtom x
      dropSubst $ showAny x' >>= simplifyExpr
    _ -> simplifyGenericOp op'

simplifyGenericOp
  :: (GenericOp op, ToExpr (op SimpIR) SimpIR, HasType CoreIR (op CoreIR), Emits o,
      OpConst op CoreIR ~ OpConst op SimpIR)
  => op CoreIR i
  -> SimplifyM i o (SimpVal o)
simplifyGenericOp op = do
  op' <- traverseOp op getRepType toDataAtom
  SimpAtom <$> emit op'
{-# INLINE simplifyGenericOp #-}

applyDictMethod :: Emits o => DictCon CoreIR i -> Int -> [SimpVal o] -> SimplifyM i o (SimpVal o)
applyDictMethod d i methodArgs = case d of
  InstanceDict _ instanceName instanceArgs -> do
    instanceName' <- substM instanceName
    instanceArgs' <- mapM simplifyAtom instanceArgs
    instanceDef <- lookupInstanceDef instanceName'
    dropSubst $ withInstantiated instanceDef instanceArgs' \(PairE _ body) -> do
      let InstanceBody _ methods = body
      let method = methods !! i
      method' <- simplifyAtom method
      simplifyApp method' methodArgs
  IxFin n -> do
    n' <- toDataAtom n
    case (toEnum i, methodArgs) of
      (Size             , []  ) -> return $ SimpAtom n' -- result : Nat
      (Ordinal          , [ix]) -> return ix            -- result : Nat
      (UnsafeFromOrdinal, [ix]) -> return ix
      _ -> error "bad ix args"
  d' -> error $ "Not a simplified dict: " ++ pprint d'

simplifyHof :: Emits o => Hof CoreIR i -> SimplifyM i o (SimpVal o)
simplifyHof = \case
  For d (IxType ixTy ixDict) lam -> do
    lam' <- simplifyLam lam
    ixTy' <- getRepType ixTy
    ixDict' <- simplifyIxDict ixDict
    SimpAtom <$> emitHof (For d (IxType ixTy' ixDict') lam')
  While body -> do
    body' <- buildBlock $ fromSimpAtom <$> simplifyExpr body
    SimpAtom <$> emitHof (While body')
  -- Linearize lam x -> do
  --   x' <- toDataAtom x
  --   lam' <- simplifyLam lam
  --   (result, linFun) <- liftDoubleBuilderToSimplifyM $ linearize lam' x'
  --   PairTy lamResultTy linFunTy <- return resultTy
  --   result' <- liftSimpAtom lamResultTy result
  --   linFun' <- liftSimpFun linFunTy linFun
  --   return $ PairVal result' linFun'
  -- Transpose lam x -> do
  --   lam' <- simplifyLam lam
  --   x' <- toDataAtom x
  --   SimpAtom <$> transpose lam' x'

liftSimpFun :: EnvReader m => Type CoreIR n -> LamExpr SimpIR n -> m n (SimpVal n)
liftSimpFun = undefined -- (TyCon (Pi piTy)) f = mkStuck $ LiftSimpFun piTy f
-- liftSimpFun _ _ = error "not a pi type"

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
linearizeTopFunNoCache spec@(LinearizationSpec f actives) = undefined
-- linearizeTopFunNoCache spec@(LinearizationSpec f actives) = do
--   TopFunBinding ~(DexTopFun _ lam _) <- lookupEnv f
--   PairE fPrimal fTangent <- liftM toPairE $ liftDoubleBuilderToSimplifyM $ linearizeTopLam (sink lam) actives
--   fTangentT <- transposeTopFun fTangent
--   fPrimal'   <- emitTopFunBinding "primal"   (LinearizationPrimal  spec) fPrimal
--   fTangent'  <- emitTopFunBinding "tangent"  (LinearizationTangent spec) fTangent
--   fTangentT' <- emitTopFunBinding "tangent"  (LinearizationTangent spec) fTangentT
--   updateTransposeRelation fTangent' fTangentT'
--   return (fPrimal', fTangent')

type Linearized = Abs (Nest SBinder)    -- primal args
                      (Abs (Nest SDecl) -- primal decls
                      (PairE SAtom      -- primal result
                             SLam))     -- tangent function

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
