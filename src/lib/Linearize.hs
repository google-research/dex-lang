-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Linearize (linearize, linearizeTopLam) where

import Control.Category ((>>>))
import Control.Monad.Reader
import Data.Foldable (toList)
import Data.Functor
import Data.List (elemIndex)
import Data.Maybe (catMaybes, isJust)
import qualified Data.Set as S
import GHC.Stack

import Builder
import Core
import Imp
import IRVariants
import MTL1
import Name
import Subst
import {-# SOURCE #-} Simplify (linearizeTopFun)
import PPrint
import QueryType
import Types.Core
import Types.Primitives
import Util (bindM2, enumerate)

-- === linearization monad ===

data ActivePrimals (n::S) = ActivePrimals
  { activeVars    :: [AtomVar SimpIR n]  -- includes refs and regions
  , activeEffs    :: EffectRow SimpIR n }

emptyActivePrimals :: ActivePrimals n
emptyActivePrimals = ActivePrimals [] Pure

data TangentArgs (n::S) = TangentArgs [SAtomVar n]

type PrimalM  = SubstReaderT Name (ReaderT1 ActivePrimals (DoubleBuilder SimpIR)) :: MonadKind2
type TangentM = ReaderT1 TangentArgs (DoubleBuilder SimpIR) :: MonadKind1

data WithTangent (n::S) (e1::E) (e2::E) =
  WithTangent (e1 n) (forall l. (Emits l, DExt n l) => TangentM l (e2 l))

type LinM i o e1 e2 = PrimalM i o (WithTangent o e1 e2)

-- TODO: maybe we shouldn't roll subst into this
pureLin :: (RenameE e, SinkableE e) => e i -> LinM i o e e
pureLin x = do
  x' <- renameM x
  return $ WithTangent x' (sinkM x')

pureLin2 :: SExpr i -> LinM i o SAtom SAtom
pureLin2 x = undefined
  -- x' <- renameM x
  -- return $ WithTangent x' (sinkM x')

runPrimalMInit :: PrimalM o o a -> DoubleBuilder SimpIR o a
runPrimalMInit cont = runPrimalM idSubst emptyActivePrimals cont

runPrimalM :: Subst Name i o -> ActivePrimals o -> PrimalM i o a -> DoubleBuilder SimpIR o a
runPrimalM subst args cont = runReaderT1 args $ runSubstReaderT subst cont

activePrimalIdx :: SAtomVar o -> PrimalM i o (Maybe Int)
activePrimalIdx v = asks \primals -> elemIndex v (activeVars primals)

getActivePrimals :: PrimalM i o (ActivePrimals o)
getActivePrimals = ask

extendActiveSubst
  :: BindsAtMostOneName b (AtomNameC SimpIR)
  => b i i' -> SAtomVar o -> PrimalM i' o a -> PrimalM i o a
extendActiveSubst b v cont = extendSubst (b@>atomVarName v) $ extendActivePrimals v cont

extendActiveEffs :: Effect SimpIR o -> PrimalM i o a -> PrimalM i o a
extendActiveEffs eff = local \primals ->
  primals { activeEffs = extendEffRow (eSetSingleton eff) (activeEffs primals)}

extendActivePrimals :: SAtomVar o -> PrimalM i o a -> PrimalM i o a
extendActivePrimals v = extendActivePrimalss [v]

extendActivePrimalss :: [SAtomVar o] -> PrimalM i o a -> PrimalM i o a
extendActivePrimalss vs =
  local \primals -> primals { activeVars = activeVars primals ++ vs }

getTangentArg :: Int -> TangentM o (Atom SimpIR o)
getTangentArg idx = asks \(TangentArgs vs) -> AVar $ vs !! idx

extendTangentArgs :: SAtomVar n -> TangentM n a -> TangentM n a
extendTangentArgs v m = local (\(TangentArgs vs) -> TangentArgs $ vs ++ [v]) m

extendTangentArgss :: [SAtomVar n] -> TangentM n a -> TangentM n a
extendTangentArgss vs' m = local (\(TangentArgs vs) -> TangentArgs $ vs ++ vs') m

getTangentArgs :: TangentM o (TangentArgs o)
getTangentArgs = ask

bindLin
  :: Emits o
  => LinM i o e  e
  -> (forall o' m. (Emits o', DExt o o', Builder SimpIR m) => e o' -> m o' (e' o'))
  -> LinM i o e' e'
bindLin m f = do
  result <- m
  withBoth result f

withBoth
  :: Emits o
  => WithTangent o e e
  -> (forall o' m. (Emits o', DExt o o', Builder SimpIR m) => e o' -> m o' (e' o'))
  -> PrimalM i o (WithTangent o e' e')
withBoth (WithTangent x tx) f = do
  Distinct <- getDistinct
  y <- f x
  return $ WithTangent y do
    tx >>= f

_withTangentComputation
  :: Emits o
  => WithTangent o e1 e2
  -> (forall o' m. (Emits o', DExt o o', Builder SimpIR m) => e2 o' -> m o' (e2' o'))
  -> PrimalM i o (WithTangent o e1 e2')
_withTangentComputation (WithTangent x tx) f = do
  Distinct <- getDistinct
  return $ WithTangent x do
    tx >>= f

fmapLin
  :: Emits o
  => (forall o'. e o' -> e' o')
  -> LinM i o e  e
  -> LinM i o e' e'
fmapLin f m = m `bindLin` (pure . f)

zipLin :: LinM i o e1 e1 -> LinM i o e2 e2 -> LinM i o (PairE e1 e2) (PairE e1 e2)
zipLin m1 m2 = do
  WithTangent x1 t1 <- m1
  WithTangent x2 t2 <- m2
  return $ WithTangent (PairE x1 x2) do PairE <$> t1 <*> t2

seqLin
  :: Traversable f
  => f (LinM i o e e)
  -> LinM i o (ComposeE f e) (ComposeE f e)
seqLin ms = do
  ms' <- sequence ms
  let xs = ms' <&> \(WithTangent x _) -> x
  return $ WithTangent (ComposeE xs) do
    ComposeE <$> forM ms' \(WithTangent _ t) -> t

liftTangentM :: TangentArgs o -> TangentM o a -> PrimalM i o a
liftTangentM args m = liftSubstReaderT $ lift11 $ runReaderT1 args m

isTrivialForAD :: SExpr o -> PrimalM i o Bool
isTrivialForAD expr = do
  trivialTy  <- presentAnd isSingletonType <$> (maybeTangentType $ getType expr)
  hasActiveEffs <- case getEffects expr of
                     Pure -> return False
                     -- TODO: Be more precise here, such as checking
                     -- whether the effects are themselves active.
                     _ -> return True
  hasActiveVars <- isActive expr
  return $ not hasActiveEffs && (trivialTy || not hasActiveVars)
    where presentAnd :: (a -> Bool) -> Maybe a -> Bool
          presentAnd = any

isActive :: HoistableE e => e o -> PrimalM i o Bool
isActive e = do
  vs <- (S.fromList . map atomVarName . activeVars) <$> getActivePrimals
  return $ any (`S.member` vs) (freeAtomVarsList e)

-- === converision between monadic and reified version of functions ===

tangentFunAsLambda
  :: Emits o
  => (forall o'. (DExt o o', Emits o') => TangentM o' (Atom SimpIR o'))
  -> PrimalM i o (SLam o)
tangentFunAsLambda cont = do
  ActivePrimals primalVars _ <- getActivePrimals
  tangentTys <- getTangentArgTys primalVars
  buildLamExpr tangentTys \tangentVars -> do
    liftTangentM (TangentArgs $ map sink tangentVars) cont

getTangentArgTys :: (Fallible1 m, EnvExtender m) => [SAtomVar n] -> m n (EmptyAbs (Nest SBinder) n)
getTangentArgTys topVs = go mempty topVs where
  go :: (Fallible1 m, EnvExtender m)
     => EMap SAtomName SAtomVar n -> [SAtomVar n] -> m n (EmptyAbs (Nest SBinder) n)
  go _ [] = return $ EmptyAbs Empty
  go heapMap (v:vs) = case getType v of
    -- This is a hack to handle heaps/references. They normally come in pairs
    -- like this, but there's nothing to prevent users writing programs that
    -- sling around heap variables by themselves. We should try to do something
    -- better...
    TC HeapType -> do
      withFreshBinder (getNameHint v) (TC HeapType) \hb -> do
        let newHeapMap = sink heapMap <> eMapSingleton (sink (atomVarName v)) (binderVar hb)
        Abs bs UnitE <- go newHeapMap $ sinkList vs
        return $ EmptyAbs $ Nest hb bs
    RefTy (Var h) referentTy -> do
      case lookupEMap heapMap (atomVarName h) of
        Nothing -> error "shouldn't happen?"
        Just h' -> do
          tt <- tangentType referentTy
          let refTy = RefTy (Var h') tt
          withFreshBinder (getNameHint v) refTy \refb -> do
            Abs bs UnitE <- go (sink heapMap) $ sinkList vs
            return $ EmptyAbs $ Nest refb bs
    ty -> do
      tt <- tangentType ty
      withFreshBinder (getNameHint v) tt \b -> do
        Abs bs UnitE <- go (sink heapMap) $ sinkList vs
        return $ EmptyAbs $ Nest b bs

class ReconFunctor (f :: E -> E) where
  capture
    :: (EnvReader m, HoistableE e, HoistableB b)
    => b n l -> SAtom l -> e l ->  m l (SAtom l, f e n)
  reconstruct
    :: (SinkableE e, Emits n)
    => SAtom n -> f e n -> PrimalM i n (SAtom n, e n)

-- tangent lambda
type LinLam = SLam
-- tangent lambda prefixed by residual args
type LinLamAbs = MaybeReconAbs LinLam

data MaybeReconAbs (e::E) (n::S) =
   ReconWithData (ReconAbs SimpIR e n)
 | TrivialRecon (e n)

data ObligateReconAbs (e::E) (n::S) =
   ObligateRecon (SType n) (ReconAbs SimpIR e n)

instance ReconFunctor MaybeReconAbs where
  capture locals original toCapture = do
    (reconVal, recon) <- telescopicCapture locals toCapture
    case recon of
      Abs (ReconBinders _ Empty) toCapture' -> return (original, TrivialRecon toCapture')
      _ -> return (PairVal original reconVal, ReconWithData recon)

  reconstruct primalAux recon = undefined
  -- reconstruct primalAux recon = case recon of
  --   TrivialRecon linLam -> return (primalAux, linLam)
  --   ReconWithData reconAbs -> do
  --     (primal, residuals) <- fromPair primalAux
  --     linLam' <- applyReconAbs reconAbs residuals
  --     return (primal, linLam')

instance ReconFunctor ObligateReconAbs where
  capture locals original toCapture = do
    (reconVal, recon) <- telescopicCapture locals toCapture
    -- TODO: telescopicCapture should probably return the hoisted type
    reconValTy <- return $ ignoreHoistFailure $ hoist locals $ getType reconVal
    return (PairVal original reconVal, ObligateRecon reconValTy recon)

  reconstruct primalAux recon = undefined
  -- reconstruct primalAux recon = case recon of
  --   ObligateRecon _ reconAbs -> do
  --     (primal, residuals) <- fromPair primalAux
  --     linLam' <- applyReconAbs reconAbs residuals
  --     return (primal, linLam')

linearizeBlockDefunc :: SExpr i -> PrimalM i o (SExpr o, LinLamAbs o)
linearizeBlockDefunc = linearizeBlockDefuncGeneral emptyOutFrag

linearizeBlockDefuncGeneral
  :: ReconFunctor f
  => ScopeFrag o' o -> SExpr i -> PrimalM i o (SExpr o, f SLam o')
linearizeBlockDefuncGeneral locals block = undefined
-- linearizeBlockDefuncGeneral locals block = do
--   Abs decls result <- buildScoped do
--     WithTangent primalResult tangentFun <- linearizeExpr block
--     lam <- tangentFunAsLambda tangentFun
--     return $ PairE primalResult lam
--   (block', recon) <- refreshAbs (Abs decls result) \decls' (PairE primal lam) -> do
--     (primal', recon) <- capture (locals >>> toScopeFrag decls') primal lam
--     return (Abs decls' primal', recon)
--   return (block', recon)

-- Inverse of tangentFunAsLambda. Should be used inside a returned tangent action.
applyLinLam :: Emits o => SLam i -> SubstReaderT (SubstVal Atom) TangentM i o (Atom SimpIR o)
applyLinLam (LamExpr bs body) = undefined
-- applyLinLam (LamExpr bs body) = do
--   TangentArgs args <- liftSubstReaderT $ getTangentArgs
--   extendSubst (bs @@> ((Rename . atomVarName) <$> args)) do
--     substM body >>= emitBlock

-- === actual linearization passs ===

-- main API entrypoint
linearize :: Emits n => SLam n -> SAtom n -> DoubleBuilder SimpIR n (SAtom n, SLam n)
linearize f x = runPrimalMInit $ linearizeLambdaApp f x
{-# SCC linearize #-}

linearizeTopLam :: STopLam n -> [Active] -> DoubleBuilder SimpIR n (STopLam n, STopLam n)
linearizeTopLam (TopLam False _ (LamExpr bs body)) actives = undefined
-- linearizeTopLam (TopLam False _ (LamExpr bs body)) actives = do
--   (primalFun, tangentFun) <- runPrimalMInit $ refreshBinders bs \bs' frag -> extendSubst frag do
--     let allPrimals = bindersVars bs'
--     activeVs <- catMaybes <$> forM (zip actives allPrimals) \(active, v) -> case active of
--       True  -> return $ Just v
--       False -> return $ Nothing
--     (body', linLamAbs) <- extendActivePrimalss activeVs do
--       linearizeBlockDefuncGeneral emptyOutFrag body
--     let primalFun = LamExpr bs' body'
--     ObligateRecon ty (Abs bsRecon (LamExpr bsTangent tangentBody)) <- return linLamAbs
--     tangentFun <- withFreshBinder "residuals" ty \bResidual -> do
--       xs <- unpackTelescope bsRecon $ Var $ binderVar bResidual
--       Abs bsTangent' UnitE <- applySubst (bsRecon @@> map SubstVal xs) (Abs bsTangent UnitE)
--       tangentTy <- ProdTy <$> typesFromNonDepBinderNest bsTangent'
--       withFreshBinder "t" tangentTy \bTangent -> do
--         tangentBody' <- buildBlock do
--           ts <- getUnpacked $ Var $ sink $ binderVar bTangent
--           let substFrag =   bsRecon   @@> map (SubstVal . sink) xs
--                         <.> bsTangent @@> map (SubstVal . sink) ts
--           emitBlock =<< applySubst substFrag tangentBody
--         return $ LamExpr (bs' >>> BinaryNest bResidual bTangent) tangentBody'
--     return (primalFun, tangentFun)
--   (,) <$> asTopLam primalFun <*> asTopLam tangentFun
-- linearizeTopLam (TopLam True _ _) _ = error "expected a non-destination-passing function"

-- reify the tangent builder as a lambda
linearizeLambdaApp :: Emits o => SLam i -> SAtom o -> PrimalM i o (SAtom o, SLam o)
linearizeLambdaApp (UnaryLamExpr b body) x = do
  vp <- emit $ toExpr x
  extendActiveSubst b vp do
    WithTangent primalResult tangentAction <- linearizeExpr body
    tanFun <- tangentFunAsLambda tangentAction
    return (primalResult, tanFun)
linearizeLambdaApp _ _ = error "not implemented"

linearizeDecls :: Emits o => Nest SDecl i i' -> LinM i' o e1 e2 -> LinM i  o e1 e2
linearizeDecls Empty cont = cont
-- TODO: as an optimization, don't bother extending the tangent args if the
-- tangent is trivial, either because its type is a singleton or because there
-- are no active vars.
linearizeDecls (Nest (Let b (DeclBinding ann expr)) rest) cont = do
  expr' <- renameM expr
  isTrivialForAD expr' >>= \case
    True -> do
      v <- emit expr'
      extendSubst (b@>atomVarName v) $ linearizeDecls rest cont
    False -> undefined
    -- False -> do
    --   WithTangent p tf <- linearizeExpr expr
    --   v <- emitDecl (getNameHint b) ann (Atom p)
    --   extendActiveSubst b v do
    --     WithTangent pRest tfRest <- linearizeDecls rest cont
    --     return $ WithTangent pRest do
    --       t <- tf
    --       vt <- emitDecl (getNameHint b) ann (Atom t)
    --       extendTangentArgs vt $
    --         tfRest

linearizeExpr :: Emits o => SExpr i -> LinM i o SAtom SAtom
linearizeExpr expr = case expr of
-- linearizeAtom :: Emits o => Atom SimpIR i -> LinM i o SAtom SAtom
-- linearizeAtom atom = case atom of
--   Var v -> do
--     v' <- renameM v
--     activePrimalIdx v' >>= \case
--       Nothing -> withZeroT $ return (Var v')
--       Just idx -> return $ WithTangent (Var v') $ getTangentArg idx
--   Con con -> linearizePrimCon con
--   DepPair _ _ _     -> notImplemented
--   PtrVar _ _      -> emitZeroT
--   RepValAtom _ -> emitZeroT
--   where emitZeroT = withZeroT $ renameM atom
  -- Atom x -> linearizeExpr x
-- linearizeBlock :: Emits o => SBlock i -> LinM i o SAtom SAtom
-- linearizeBlock (Abs decls result) =
--   linearizeDecls decls $ linearizeExpr result
  TopApp _ f xs -> do
    (xs', ts) <- unzip <$> forM xs \x -> do
      x' <- renameM x
      isActive x' >>= \case
        True  -> do
          WithTangent x'' t <- dropSubst $ linearizeExpr x'
          return (x'', Just (WithTangent (unitLike x'') t))
        False -> do
          x'' <- emitExpr x'
          return (x'', Nothing)
    f' <- renameM f
    -- TODO(dougalm): this works, but I think that what we really want here is
    -- to hoist the argument to `linearizeTopFun`, rather than the result. We
    -- want to pop all the way up to the top level, hoisting the E-kinded
    -- `LinearizationSpec` with us, rather than working underneath all the local
    -- bindings and then only hoisting the final result.
    Just (PairE fPrimal fTan) <- liftTopBuilderAndEmit $
       liftM toPairE $ linearizeTopFun (sink $ LinearizationSpec f' (map isJust ts))
    (ans, residuals) <- fromPair =<< naryTopApp fPrimal xs'
    return $ WithTangent ans do
      ts' <- forM (catMaybes ts) \(WithTangent UnitE t) -> t
      naryTopApp (sink fTan) (sinkList xs' ++ [sink residuals, ProdVal ts'])
    where
      unitLike :: e n -> UnitE n
      unitLike _ = UnitE
  -- TabApp _ x idxs -> undefined  -- pureLin2 not what we need here
  --   zipLin (linearizeExpr x) (pureLin2 $ ListE $ toList idxs) `bindLin`
  --     \(PairE x' (ListE idxs')) -> naryTabApp x' idxs'
  PrimOp op      -> linearizeOp op
  -- Case e alts (EffTy effs resultTy) -> do
  --   e' <- renameM e
  --   effs' <- renameM effs
  --   resultTy' <- renameM resultTy
  --   isActive e' >>= \case
  --     True -> notImplemented
  --     False -> do
  --       (alts', recons) <- unzip <$> buildCaseAlts e' \i b' -> do
  --         Abs b body <- return $ alts !! i
  --         extendSubst (b@>binderName b') do
  --           (block, recon) <- linearizeBlockDefuncGeneral (toScopeFrag b') body
  --           return (Abs b' block, recon)
  --       let tys = recons <&> \(ObligateRecon t _) -> t
  --       alts'' <- forM (enumerate alts') \(i, alt) -> do
  --         injectAltResult tys i alt
  --       let fullResultTy = PairTy resultTy' $ SumTy tys
  --       result <- emitExpr $ Case e' alts'' (EffTy effs' fullResultTy)
  --       (primal, residualss) <- fromPair result
  --       resultTangentType <- tangentType resultTy'
  --       return $ WithTangent primal do
  --         buildCase (sink residualss) (sink resultTangentType) \i residuals -> do
  --           ObligateRecon _ (Abs bs linLam) <- return $ sinkList recons !! i
  --           residuals' <- unpackTelescope bs residuals
  --           withSubstReaderT $ extendSubst (bs @@> (SubstVal <$> residuals')) do
  --             applyLinLam linLam
  TabCon _ ty xs -> do
    ty' <- renameM ty
    seqLin (map linearizeExpr xs) `bindLin` \(ComposeE xs') ->
      emitExpr $ TabCon Nothing (sink ty') (toExpr <$> xs')

linearizeOp :: Emits o => PrimOp SimpIR i -> LinM i o SAtom SAtom
linearizeOp op = case op of
  Hof (TypedHof _ e) -> linearizeHof e
  DAMOp _        -> error "shouldn't occur here"
  RefOp ref m -> case m of
    MAsk -> linearizeExpr ref `bindLin` \ref' -> liftM AVar $ emit $ PrimOp $ RefOp (toExpr ref') MAsk
    MExtend monoid x -> do
      -- TODO: check that we're dealing with a +/0 monoid
      monoid' <- renameM monoid
      zipLin (linearizeExpr ref) (linearizeExpr x) `bindLin` \(PairE ref' x') ->
        liftM AVar $ emit $ PrimOp $ RefOp (toExpr ref') $ MExtend (sink monoid') (toExpr x')
    MGet   -> linearizeExpr ref `bindLin` \ref' -> liftM AVar $ emit $ PrimOp $ RefOp (toExpr ref') MGet
    MPut x -> zipLin (linearizeExpr ref) (linearizeExpr x) `bindLin` \(PairE ref' x') ->
                liftM AVar $ emit $ PrimOp $ RefOp (toExpr ref') $ MPut (toExpr x')
    IndexRef _ i -> do
      zipLin (le ref) (pureLin2 i) `bindLin` \(PairE ref' i') ->
        emitOp =<< mkIndexRef (toExpr ref') (toExpr i')
    ProjRef _ i -> le ref `bindLin` \ref' -> emitOp =<< mkProjRef (toExpr ref') i
  UnOp  uop x       -> linearizeUnOp  uop x
  BinOp bop x y     -> linearizeBinOp bop x y
  -- XXX: This assumes that pointers are always constants
  MemOp _      -> emitZeroT
  MiscOp miscOp -> linearizeMiscOp miscOp
  VectorOp _ -> error "not implemented"
  where
    emitZeroT = withZeroT $ liftM AVar $ emit =<< renameM (PrimOp op)
    le = linearizeExpr

linearizeMiscOp :: Emits o => MiscOp SimpIR i -> LinM i o SAtom SAtom
linearizeMiscOp op = case op of
  SumTag _     -> emitZeroT
  ToEnum _ _   -> emitZeroT
  Select p t f -> (pureLin2 p `zipLin` le t `zipLin` le f) `bindLin`
                     \(p' `PairE` t' `PairE` f') -> emitOp $ MiscOp $ Select (toExpr p') (toExpr t') (toExpr f')
  CastOp t v -> do
    vt <- getType <$> renameM v
    t' <- renameM t
    vtTangentType <- tangentType vt
    tTangentType  <- tangentType t'
    ((&&) <$> (vtTangentType `alphaEq` vt)
          <*> (tTangentType  `alphaEq` t')) >>= \case
      True -> do
        linearizeExpr v `bindLin` \v' -> emitOp $ MiscOp $ CastOp (sink t') (toExpr v')
      False -> do
        WithTangent x xt <- linearizeExpr v
        yt <- case (vtTangentType, tTangentType) of
          (_     , UnitTy) -> return $ UnitVal
          (UnitTy, tt    ) -> zeroAt tt
          _                -> error "Expected at least one side of the CastOp to have a trivial tangent type"
        y <- emitOp $ MiscOp $ CastOp t' (toExpr x)
        return $ WithTangent y do xt >> return (sink yt)
  BitcastOp _ _    -> notImplemented
  UnsafeCoerce _ _ -> notImplemented
  GarbageVal _     -> notImplemented
  ThrowException _ -> notImplemented
  ThrowError _     -> emitZeroT
  OutputStream     -> emitZeroT
  ShowAny _ -> error "Shouldn't have ShowAny in simplified IR"
  ShowScalar _ -> error "Shouldn't have ShowScalar in simplified IR"
  where
    emitZeroT = withZeroT $ liftM AVar $ emit =<< renameM (PrimOp $ MiscOp op)
    le = linearizeExpr

linearizeUnOp :: Emits o => UnOp -> Expr SimpIR i -> LinM i o SAtom SAtom
linearizeUnOp op x' = do
  WithTangent x tx <- linearizeExpr x'
  let emitZeroT = withZeroT $ emitOp $ UnOp op (toExpr x)
  case op of
    Exp    -> do
      y <- emitUnOp Exp x
      return $ WithTangent y (bindM2 mul tx (sinkM y))
    Exp2   -> notImplemented
    Log    -> withT (emitUnOp Log x) $ (tx >>= (`div'` sink x))
    Log2   -> notImplemented
    Log10  -> notImplemented
    Log1p  -> notImplemented
    Sin    -> withT (emitUnOp Sin x) $ bindM2 mul tx (emitUnOp Cos (sink x))
    Cos    -> withT (emitUnOp Cos x) $ bindM2 mul tx (neg =<< emitUnOp Sin (sink x))
    Tan    -> notImplemented
    Sqrt   -> do
      y <- emitUnOp Sqrt x
      return $ WithTangent y do
        denominator <- bindM2 mul (2 `fLitLike` sink y) (sinkM y)
        bindM2 div' tx (pure denominator)
    Floor  -> emitZeroT
    Ceil   -> emitZeroT
    Round  -> emitZeroT
    LGamma -> notImplemented
    Erf    -> notImplemented
    Erfc   -> notImplemented
    FNeg   -> withT (neg x) (neg =<< tx)
    BNot   -> emitZeroT

linearizeBinOp :: Emits o => BinOp -> SExpr i -> SExpr i -> LinM i o SAtom SAtom
linearizeBinOp op x' y' = do
  WithTangent x tx <- linearizeExpr x'
  WithTangent y ty <- linearizeExpr y'
  let emitZeroT = withZeroT $ emitOp $ BinOp op (toExpr x) (toExpr y)
  case op of
    IAdd   -> emitZeroT
    ISub   -> emitZeroT
    IMul   -> emitZeroT
    IDiv   -> emitZeroT
    IRem   -> emitZeroT
    ICmp _ -> emitZeroT
    FAdd -> withT (add x y) (bindM2 add tx ty)
    FSub -> withT (sub x y) (bindM2 sub tx ty)
    FMul -> withT (mul x y)
                  (bindM2 add (bindM2 mul (referToPrimal x) ty)
                              (bindM2 mul tx (referToPrimal y)))
    FDiv -> withT (div' x y) do
      tx' <- bindM2 div' tx (referToPrimal y)
      ty' <- bindM2 div' (bindM2 mul (referToPrimal x) ty)
                      (bindM2 mul (referToPrimal y) (referToPrimal y))
      sub tx' ty'
    FPow -> withT (emitOp $ BinOp FPow (toExpr x) (toExpr y)) do
      px <- referToPrimal x
      py <- referToPrimal y
      c <- (1.0 `fLitLike` py) >>= (sub py) >>= fpow px
      tx' <- bindM2 mul tx (return py)
      ty' <- bindM2 mul (bindM2 mul (return px) ty) (flog px)
      mul c =<< add tx' ty'
    FCmp _ -> emitZeroT
    BAnd   -> emitZeroT
    BOr    -> emitZeroT
    BXor   -> emitZeroT
    BShL   -> emitZeroT
    BShR   -> emitZeroT

-- This has the same type as `sinkM` and falls back thereto, but recomputes
-- indexing a primal array in the tangent to avoid materializing intermediate
-- results thereof.  We should probably have a more cogent story for
-- rematerialization, but this suffices to remove embarrassing intermediates in
-- matrix multiplication.
referToPrimal :: (Builder SimpIR m, Emits l, DExt n l) => SAtom n -> m l (SAtom l)
referToPrimal x = undefined
-- referToPrimal x = do
--   case x of
--     Var v -> lookupEnv (atomVarName $ sink v) >>= \case
--       AtomNameBinding (LetBound (DeclBinding PlainLet (Atom atom))) ->
--         referToPrimal atom
--       AtomNameBinding (LetBound (DeclBinding PlainLet (TabApp _ tab is))) -> do
--         tab' <- referToPrimal tab
--         is' <- mapM referToPrimal is
--         emitExpr =<< mkTabApp tab' is'
--       _ -> sinkM x
--     _ -> sinkM x

linearizePrimCon :: Emits o => Con Expr SimpIR i -> LinM i o SAtom SAtom
linearizePrimCon con = undefined
-- linearizePrimCon con = case con of
--   Lit _ -> emitZeroT
--   ProdCon xs -> fmapLin (ProdVal . fromComposeE) $ seqLin (fmap linearizeExpr xs)
--   SumCon  _ _ _ -> notImplemented
--   HeapVal -> emitZeroT
--   where emitZeroT = withZeroT $ renameM $ Con con

linearizeHof :: Emits o => Hof SimpIR i -> LinM i o SAtom SAtom
linearizeHof hof = case hof of
  For d ixTy' lam -> do
    UnaryLamExpr ib body <- return lam
    ixTy <- renameM ixTy'
    (lam', Abs ib' linLam) <- withFreshBinder noHint (ixTypeType ixTy) \ib' -> do
      (block', linLam) <- extendSubst (ib@>binderName ib') $ linearizeBlockDefunc body
      return (UnaryLamExpr ib' block', Abs ib' linLam)
    primalsAux <- emitHof $ For d ixTy lam'
    case linLam of
      TrivialRecon linLam' ->
        return $ WithTangent primalsAux do
          Abs ib'' linLam'' <- sinkM (Abs ib' linLam')
          withSubstReaderT $ buildFor noHint d (sink ixTy) \i' -> do
            extendSubst (ib''@>Rename (atomVarName i')) $ applyLinLam linLam''
      -- ReconWithData reconAbs -> do
      --   primals <- buildMap primalsAux getFst
      --   return $ WithTangent primals do
      --     Abs ib'' (Abs bs linLam') <- sinkM (Abs ib' reconAbs)
      --     withSubstReaderT $ buildFor noHint d (sink ixTy) \i' -> do
      --       extendSubst (ib''@> Rename (atomVarName i')) do
      --         residuals' <- tabApp (sink primalsAux) (Var i') >>= getSnd >>= unpackTelescope bs
      --         extendSubst (bs @@> (SubstVal <$> residuals')) $
      --           applyLinLam linLam'
  RunReader r lam -> do
    WithTangent r' rLin <- linearizeExpr r
    (lam', recon) <- linearizeEffectFun Reader lam
    primalAux <- emitHof $ RunReader (toExpr r') lam'
    referentTy <- renameM $ getType r
    (primal, linLam) <- reconstruct primalAux recon
    return $ WithTangent primal do
      rLin' <- rLin
      tt <- tangentType $ sink referentTy
      tanEffLam <- buildEffLam noHint tt \h ref ->
        extendTangentArgss [h, ref] do
          withSubstReaderT $ applyLinLam $ sink linLam
      emitHof $ RunReader (toExpr rLin') tanEffLam
  RunState Nothing sInit lam -> do
    WithTangent sInit' sLin <- linearizeExpr sInit
    (lam', recon) <- linearizeEffectFun State lam
    (primalAux, sFinal) <- fromPair =<< emitHof (RunState Nothing (toExpr sInit') lam')
    referentTy <- snd <$> getTypeRWSAction lam'
    (primal, linLam) <- reconstruct primalAux recon
    return $ WithTangent (PairVal primal sFinal) do
      sLin' <- sLin
      tt <- tangentType $ sink referentTy
      tanEffLam <- buildEffLam noHint tt \h ref ->
        extendTangentArgss [h, ref] do
          withSubstReaderT $ applyLinLam $ sink linLam
      emitHof $ RunState Nothing (toExpr sLin') tanEffLam
  RunWriter Nothing bm lam -> do
    -- TODO: check it's actually the 0/+ monoid (or should we just build that in?)
    bm' <- renameM bm
    (lam', recon) <- linearizeEffectFun Writer lam
    (primalAux, wFinal) <- fromPair =<< emitHof (RunWriter Nothing bm' lam')
    (primal, linLam) <- reconstruct primalAux recon
    referentTy <- snd <$> getTypeRWSAction lam'
    return $ WithTangent (PairVal primal wFinal) do
      bm'' <- sinkM bm'
      tt <- tangentType $ sink referentTy
      tanEffLam <- buildEffLam noHint tt \h ref ->
        extendTangentArgss [h, ref] do
          withSubstReaderT $ applyLinLam $ sink linLam
      emitHof $ RunWriter Nothing bm'' tanEffLam
  RunIO body -> do
    (body', recon) <- linearizeBlockDefunc body
    primalAux <- emitHof $ RunIO body'
    (primal, linLam) <- reconstruct primalAux recon
    return $ WithTangent primal do
      withSubstReaderT $ applyLinLam $ sink linLam
  _ -> error $ "not implemented: " ++ pprint hof

linearizeEffectFun :: RWS -> SLam i -> PrimalM i o (SLam o, LinLamAbs o)
linearizeEffectFun rws (BinaryLamExpr hB refB body) = do
  withFreshBinder noHint (TC HeapType) \h -> do
    bTy <- extendSubst (hB@>binderName h) $ renameM $ binderType refB
    withFreshBinder noHint bTy \b -> do
      let ref = binderVar b
      hVar <- sinkM $ binderVar h
      (body', linLam) <- extendActiveSubst hB hVar $ extendActiveSubst refB ref $
        -- TODO: maybe we should check whether we need to extend the active effects
        extendActiveEffs (RWSEffect rws (Var hVar)) do
          linearizeBlockDefunc body
      -- TODO: this assumes that references aren't returned. Our type system
      -- ensures that such references can never be *used* once the effect runner
      -- returns, but technically it's legal to return them.
      let linLam' = ignoreHoistFailure $ hoist (PairB h b) linLam
      return (BinaryLamExpr h b body', linLam')
linearizeEffectFun _ _ = error "expect effect function to be a binary lambda"

withT :: PrimalM i o (e1 o)
      -> (forall o'. (Emits o', DExt o o') => TangentM o' (e2 o'))
      -> PrimalM i o (WithTangent o e1 e2)
withT p t = do
  p' <- p
  return $ WithTangent p' t

withZeroT :: PrimalM i o (Atom SimpIR o)
          -> PrimalM i o (WithTangent o SAtom SAtom)
withZeroT p = do
  p' <- p
  return $ WithTangent p' do
    pTy <- return $ getType $ sink p'
    zeroAt =<< tangentType pTy

notImplemented :: HasCallStack => a
notImplemented = error "Not implemented"

-- === boring instances ===

instance GenericE ActivePrimals where
  type RepE ActivePrimals = PairE (ListE SAtomVar) (EffectRow SimpIR)
  fromE (ActivePrimals vs effs) = ListE vs `PairE` effs
  {-# INLINE fromE #-}
  toE   (ListE vs `PairE` effs) = ActivePrimals vs effs
  {-# INLINE toE #-}

instance SinkableE   ActivePrimals
instance HoistableE  ActivePrimals
instance AlphaEqE    ActivePrimals
instance RenameE     ActivePrimals

instance GenericE TangentArgs where
  type RepE TangentArgs = ListE SAtomVar
  fromE (TangentArgs vs) = ListE vs
  {-# INLINE fromE #-}
  toE   (ListE vs) = TangentArgs vs
  {-# INLINE toE #-}

instance SinkableE   TangentArgs
instance HoistableE  TangentArgs
instance AlphaEqE    TangentArgs
instance RenameE     TangentArgs

instance GenericE (MaybeReconAbs e) where
  type RepE (MaybeReconAbs e) = EitherE (ReconAbs SimpIR e) e
  fromE = \case
    ReconWithData ab -> LeftE ab
    TrivialRecon e   -> RightE e
  {-# INLINE fromE #-}

  toE = \case
    LeftE ab -> ReconWithData ab
    RightE e -> TrivialRecon e
  {-# INLINE toE #-}

instance SinkableE  e => SinkableE  (MaybeReconAbs e)
instance HoistableE e => HoistableE (MaybeReconAbs e)
instance RenameE    e => RenameE    (MaybeReconAbs e)

instance SinkableE  e => SinkableE  (ObligateReconAbs e) where
  sinkingProofE = undefined
