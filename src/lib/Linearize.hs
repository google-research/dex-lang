-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Linearize (linearize, linearizeLam) where

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
import CheapReduction
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
  { activeVars    :: [AtomName SimpIR n]  -- includes refs and regions
  , activeEffs    :: EffectRow SimpIR n }

emptyActivePrimals :: ActivePrimals n
emptyActivePrimals = ActivePrimals [] Pure

data TangentArgs (n::S) = TangentArgs [SAtomName n]

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

runPrimalMInit :: PrimalM o o a -> DoubleBuilder SimpIR o a
runPrimalMInit cont = runPrimalM idSubst emptyActivePrimals cont

runPrimalM :: Subst Name i o -> ActivePrimals o -> PrimalM i o a -> DoubleBuilder SimpIR o a
runPrimalM subst args cont = runReaderT1 args $ runSubstReaderT subst cont

activePrimalIdx :: AtomName SimpIR o -> PrimalM i o (Maybe Int)
activePrimalIdx v = asks \primals -> elemIndex v (activeVars primals)

getActivePrimals :: PrimalM i o (ActivePrimals o)
getActivePrimals = ask

extendActiveSubst
  :: BindsAtMostOneName b (AtomNameC SimpIR)
  => b i i' -> AtomName SimpIR o -> PrimalM i' o a -> PrimalM i o a
extendActiveSubst b v cont = extendSubst (b@>v) $ extendActivePrimals v cont

extendActiveEffs :: Effect SimpIR o -> PrimalM i o a -> PrimalM i o a
extendActiveEffs eff = local \primals ->
  primals { activeEffs = extendEffRow (eSetSingleton eff) (activeEffs primals)}

extendActivePrimals :: AtomName SimpIR o -> PrimalM i o a -> PrimalM i o a
extendActivePrimals v = extendActivePrimalss [v]

extendActivePrimalss :: [AtomName SimpIR o] -> PrimalM i o a -> PrimalM i o a
extendActivePrimalss vs =
  local \primals -> primals { activeVars = activeVars primals ++ vs }

getTangentArg :: Int -> TangentM o (Atom SimpIR o)
getTangentArg idx = asks \(TangentArgs vs) -> Var $ vs !! idx

extendTangentArgs :: SAtomName n -> TangentM n a -> TangentM n a
extendTangentArgs v m = local (\(TangentArgs vs) -> TangentArgs $ vs ++ [v]) m

extendTangentArgss :: [SAtomName n] -> TangentM n a -> TangentM n a
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
  trivialTy  <- presentAnd isSingletonType <$> (maybeTangentType =<< getType expr)
  hasActiveEffs <- getEffects expr >>= \case
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
  vs <- (S.fromList . activeVars) <$> getActivePrimals
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

getTangentArgTys :: (Fallible1 m, EnvExtender m) => [SAtomName n] -> m n (EmptyAbs (Nest SBinder) n)
getTangentArgTys topVs = go mempty topVs where
  go :: (Fallible1 m, EnvExtender m)
     => EMap SAtomName SAtomName n -> [SAtomName n] -> m n (EmptyAbs (Nest SBinder) n)
  go _ [] = return $ EmptyAbs Empty
  go heapMap (v:vs) = getType v >>= \case
    -- This is a hack to handle heaps/references. They normally come in pairs
    -- like this, but there's nothing to prevent users writing programs that
    -- sling around heap variables by themselves. We should try to do something
    -- better...
    TC HeapType -> do
      withFreshBinder (getNameHint v) (TC HeapType) \hb -> do
        let newHeapMap = sink heapMap <> eMapSingleton (sink v) (binderName hb)
        Abs bs UnitE <- go newHeapMap $ sinkList vs
        return $ EmptyAbs $ Nest hb bs
    RefTy (Var h) referentTy -> do
      case lookupEMap heapMap h of
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
    :: (SubstE AtomSubstVal e, SinkableE e, Emits n)
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

  reconstruct primalAux recon = case recon of
    TrivialRecon linLam -> return (primalAux, linLam)
    ReconWithData reconAbs -> do
      (primal, residuals) <- fromPair primalAux
      linLam' <- applyReconAbs reconAbs residuals
      return (primal, linLam')

instance ReconFunctor ObligateReconAbs where
  capture locals original toCapture = do
    (reconVal, recon) <- telescopicCapture locals toCapture
    -- TODO: telescopicCapture should probably return the hoisted type
    reconValTy <- ignoreHoistFailure <$> hoist locals <$> getType reconVal
    return (PairVal original reconVal, ObligateRecon reconValTy recon)

  reconstruct primalAux recon = case recon of
    ObligateRecon _ reconAbs -> do
      (primal, residuals) <- fromPair primalAux
      linLam' <- applyReconAbs reconAbs residuals
      return (primal, linLam')

linearizeBlockDefunc :: SBlock i -> PrimalM i o (SBlock o, LinLamAbs o)
linearizeBlockDefunc = linearizeBlockDefuncGeneral emptyOutFrag

linearizeBlockDefuncGeneral
  :: ReconFunctor f
  => ScopeFrag o' o -> SBlock i -> PrimalM i o (SBlock o, f SLam o')
linearizeBlockDefuncGeneral locals block = do
  Abs decls result <- buildScoped do
    WithTangent primalResult tangentFun <- linearizeBlock block
    lam <- tangentFunAsLambda tangentFun
    return $ PairE primalResult lam
  (blockAbs, recon) <- refreshAbs (Abs decls result) \decls' (PairE primal lam) -> do
    (primal', recon) <- capture (locals >>> toScopeFrag decls') primal lam
    return (Abs decls' primal', recon)
  block' <- makeBlockFromDecls blockAbs
  return (block', recon)

-- Inverse of tangentFunAsLambda. Should be used inside a returned tangent action.
applyLinLam :: Emits o => SLam i -> SubstReaderT AtomSubstVal TangentM i o (Atom SimpIR o)
applyLinLam (LamExpr bs body) = do
  TangentArgs args <- liftSubstReaderT $ getTangentArgs
  extendSubst (bs @@> (Rename <$> args)) do
    substM body >>= emitBlock

-- === actual linearization passs ===

-- main API entrypoint
linearize :: Emits n => SLam n -> SAtom n -> DoubleBuilder SimpIR n (SAtom n, SLam n)
linearize f x = runPrimalMInit $ linearizeLambdaApp f x
{-# SCC linearize #-}

linearizeLam :: SLam n -> [Active] -> DoubleBuilder SimpIR n (SLam n, SLam n)
linearizeLam (LamExpr bs body) actives = runPrimalMInit do
  refreshBinders bs \bs' frag -> extendSubst frag do
    let allPrimals = nestToNames bs'
    activeVs <- catMaybes <$> forM (zip actives allPrimals) \(active, v) -> case active of
      True  -> return $ Just v
      False -> return $ Nothing
    (body', linLamAbs) <-extendActivePrimalss activeVs do
      linearizeBlockDefuncGeneral emptyOutFrag body
    let primalFun = LamExpr bs' body'
    ObligateRecon ty (Abs bsRecon (LamExpr bsTangent tangentBody)) <- return linLamAbs
    tangentFun <- withFreshBinder "residuals" ty \bResidual -> do
      xs <- unpackTelescope bsRecon $ Var $ binderName bResidual
      Abs bsTangent' UnitE <- applySubst (bsRecon @@> map SubstVal xs) (Abs bsTangent UnitE)
      tangentTy <- ProdTy <$> typesFromNonDepBinderNest bsTangent'
      withFreshBinder "t" tangentTy \bTangent -> do
        tangentBody' <- buildBlock do
          ts <- getUnpacked $ Var $ sink $ binderName bTangent
          let substFrag =   bsRecon   @@> map (SubstVal . sink) xs
                        <.> bsTangent @@> map (SubstVal . sink) ts
          emitBlock =<< applySubst substFrag tangentBody
        return $ LamExpr (bs' >>> BinaryNest bResidual bTangent) tangentBody'
    return (primalFun, tangentFun)

-- reify the tangent builder as a lambda
linearizeLambdaApp :: Emits o => SLam i -> SAtom o -> PrimalM i o (SAtom o, SLam o)
linearizeLambdaApp (UnaryLamExpr b body) x = do
  vp <- emit $ Atom x
  extendActiveSubst b vp do
    WithTangent primalResult tangentAction <- linearizeBlock body
    tanFun <- tangentFunAsLambda tangentAction
    return (primalResult, tanFun)
linearizeLambdaApp _ _ = error "not implemented"

linearizeAtom :: Emits o => Atom SimpIR i -> LinM i o SAtom SAtom
linearizeAtom atom = case atom of
  Var v -> do
    v' <- renameM v
    activePrimalIdx v' >>= \case
      Nothing -> withZeroT $ return (Var v')
      Just idx -> return $ WithTangent (Var v') $ getTangentArg idx
  Con con -> linearizePrimCon con
  DepPair _ _ _     -> notImplemented
  PtrVar _        -> emitZeroT
  ProjectElt i x -> do
    WithTangent x' tx <- linearizeAtom x
    xi <- normalizeProj i x'
    return $ WithTangent xi do
      t <- tx
      normalizeProj i t
  RepValAtom _ -> emitZeroT
  where emitZeroT = withZeroT $ renameM atom

linearizeBlock :: Emits o => SBlock i -> LinM i o SAtom SAtom
linearizeBlock (Block _ decls result) =
  linearizeDecls decls $ linearizeAtom result

linearizeDecls :: Emits o => Nest SDecl i i' -> LinM i' o e1 e2 -> LinM i  o e1 e2
linearizeDecls Empty cont = cont
-- TODO: as an optimization, don't bother extending the tangent args if the
-- tangent is trivial, either because its type is a singleton or because there
-- are no active vars.
linearizeDecls (Nest (Let b (DeclBinding ann _ expr)) rest) cont = do
  expr' <- renameM expr
  isTrivialForAD expr' >>= \case
    True -> do
      v <- emit expr'
      extendSubst (b@>v) $ linearizeDecls rest cont
    False -> do
      WithTangent p tf <- linearizeExpr expr
      v <- emitDecl (getNameHint b) ann (Atom p)
      extendActiveSubst b v do
        WithTangent pRest tfRest <- linearizeDecls rest cont
        return $ WithTangent pRest do
          t <- tf
          vt <- emitDecl (getNameHint b) ann (Atom t)
          extendTangentArgs vt $
            tfRest

linearizeExpr :: Emits o => SExpr i -> LinM i o SAtom SAtom
linearizeExpr expr = case expr of
  Atom x -> linearizeAtom x
  TopApp f xs -> do
    (xs', ts) <- unzip <$> forM xs \x -> do
      x' <- renameM x
      isActive x' >>= \case
        True  -> do
          WithTangent x'' t <- dropSubst $ linearizeAtom x'
          return (x'', Just (WithTangent (unitLike x'') t))
        False -> return (x', Nothing)
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
  TabApp x idxs -> do
    zipLin (linearizeAtom x) (pureLin $ ListE $ toList idxs) `bindLin`
      \(PairE x' (ListE idxs')) -> naryTabApp x' idxs'
  PrimOp op      -> linearizeOp op
  Case e alts resultTy effs -> do
    e' <- renameM e
    effs' <- renameM effs
    resultTy' <- renameM resultTy
    isActive e' >>= \case
      True -> notImplemented
      False -> do
        (alts', recons) <- unzip <$> buildCaseAlts e' \i b' -> do
          Abs b body <- return $ alts !! i
          extendSubst (b@>binderName b') do
            (block, recon) <- linearizeBlockDefuncGeneral (toScopeFrag b') body
            return (Abs b' block, recon)
        let tys = recons <&> \(ObligateRecon t _) -> t
        alts'' <- forM (enumerate alts') \(i, alt) -> do
          injectAltResult tys i alt
        let fullResultTy = PairTy resultTy' $ SumTy tys
        result <- emitExpr $ Case e' alts'' fullResultTy effs'
        (primal, residualss) <- fromPair result
        resultTangentType <- tangentType resultTy'
        return $ WithTangent primal do
          buildCase (sink residualss) (sink resultTangentType) \i residuals -> do
            ObligateRecon _ (Abs bs linLam) <- return $ sinkList recons !! i
            residuals' <- unpackTelescope bs residuals
            withSubstReaderT $ extendSubst (bs @@> (SubstVal <$> residuals')) do
              applyLinLam linLam
  TabCon _ ty xs -> do
    ty' <- renameM ty
    seqLin (map linearizeAtom xs) `bindLin` \(ComposeE xs') ->
      emitExpr $ TabCon Nothing (sink ty') xs'

linearizeOp :: Emits o => PrimOp SimpIR i -> LinM i o SAtom SAtom
linearizeOp op = case op of
  Hof e      -> linearizeHof e
  DAMOp _        -> error "shouldn't occur here"
  RefOp ref m -> case m of
    MAsk -> linearizeAtom ref `bindLin` \ref' -> liftM Var $ emit $ PrimOp $ RefOp ref' MAsk
    MExtend monoid x -> do
      -- TODO: check that we're dealing with a +/0 monoid
      monoid' <- renameM monoid
      zipLin (linearizeAtom ref) (linearizeAtom x) `bindLin` \(PairE ref' x') ->
        liftM Var $ emit $ PrimOp $ RefOp ref' $ MExtend (sink monoid') x'
    MGet   -> linearizeAtom ref `bindLin` \ref' -> liftM Var $ emit $ PrimOp $ RefOp ref' MGet
    MPut x -> zipLin (linearizeAtom ref) (linearizeAtom x) `bindLin` \(PairE ref' x') ->
                liftM Var $ emit $ PrimOp $ RefOp ref' $ MPut x'
    IndexRef i -> zipLin (la ref) (pureLin i) `bindLin`
                    \(PairE ref' i') -> emitOp $ RefOp ref' $ IndexRef i'
    ProjRef i -> la ref `bindLin` \ref' -> emitOp $ RefOp ref' $ ProjRef i
  UnOp  uop x       -> linearizeUnOp  uop x
  BinOp bop x y     -> linearizeBinOp bop x y
  -- XXX: This assumes that pointers are always constants
  MemOp _      -> emitZeroT
  MiscOp miscOp -> linearizeMiscOp miscOp
  VectorOp _ -> error "not implemented"
  where
    emitZeroT = withZeroT $ liftM Var $ emit =<< renameM (PrimOp op)
    la = linearizeAtom

linearizeMiscOp :: Emits o => MiscOp SimpIR i -> LinM i o SAtom SAtom
linearizeMiscOp op = case op of
  SumTag _     -> emitZeroT
  ToEnum _ _   -> emitZeroT
  Select p t f -> (pureLin p `zipLin` la t `zipLin` la f) `bindLin`
                     \(p' `PairE` t' `PairE` f') -> emitOp $ MiscOp $ Select p' t' f'
  CastOp t v -> do
    vt <- getType =<< renameM v
    t' <- renameM t
    vtTangentType <- tangentType vt
    tTangentType  <- tangentType t'
    ((&&) <$> (vtTangentType `alphaEq` vt)
          <*> (tTangentType  `alphaEq` t')) >>= \case
      True -> do
        linearizeAtom v `bindLin` \v' -> emitOp $ MiscOp $ CastOp (sink t') v'
      False -> do
        WithTangent x xt <- linearizeAtom v
        yt <- case (vtTangentType, tTangentType) of
          (_     , UnitTy) -> return $ UnitVal
          (UnitTy, tt    ) -> zeroAt tt
          _                -> error "Expected at least one side of the CastOp to have a trivial tangent type"
        y <- emitOp $ MiscOp $ CastOp t' x
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
    emitZeroT = withZeroT $ liftM Var $ emit =<< renameM (PrimOp $ MiscOp op)
    la = linearizeAtom

linearizeUnOp :: Emits o => UnOp -> Atom SimpIR i -> LinM i o SAtom SAtom
linearizeUnOp op x' = do
  WithTangent x tx <- linearizeAtom x'
  let emitZeroT = withZeroT $ emitOp $ UnOp op x
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

linearizeBinOp :: Emits o => BinOp -> SAtom i -> SAtom i -> LinM i o SAtom SAtom
linearizeBinOp op x' y' = do
  WithTangent x tx <- linearizeAtom x'
  WithTangent y ty <- linearizeAtom y'
  let emitZeroT = withZeroT $ emitOp $ BinOp op x y
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
    FPow -> withT (emitOp $ BinOp FPow x y) do
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
referToPrimal x = do
  case x of
    Var v -> lookupEnv (sink v) >>= \case
      AtomNameBinding (LetBound (DeclBinding PlainLet _ (Atom atom))) ->
        referToPrimal atom
      AtomNameBinding (LetBound (DeclBinding PlainLet _ (TabApp tab is))) -> do
        tab' <- referToPrimal tab
        is' <- mapM referToPrimal is
        Var <$> emit (TabApp tab' is')
      _ -> sinkM x
    _ -> sinkM x

linearizePrimCon :: Emits o => Con SimpIR i -> LinM i o SAtom SAtom
linearizePrimCon con = case con of
  Lit _ -> emitZeroT
  ProdCon xs -> fmapLin (ProdVal . fromComposeE) $ seqLin (fmap linearizeAtom xs)
  SumCon  _ _ _ -> notImplemented
  HeapVal -> emitZeroT
  where emitZeroT = withZeroT $ renameM $ Con con

linearizeHof :: Emits o => Hof SimpIR i -> LinM i o SAtom SAtom
linearizeHof hof = case hof of
  For d ixDict lam -> do
    UnaryLamExpr (ib:>ixTy) body <- return lam
    ixDict' <- renameM ixDict
    ixTy'   <- renameM ixTy
    let ixTyDict = IxType ixTy' ixDict'
    (lam', Abs ib' linLam) <- withFreshBinder noHint ixTy' \ib' -> do
      (block', linLam) <- extendSubst (ib@>binderName ib') $ linearizeBlockDefunc body
      return (UnaryLamExpr ib' block', Abs ib' linLam)
    primalsAux <- emitExpr $ PrimOp $ Hof $ For d ixDict' lam'
    case linLam of
      TrivialRecon linLam' ->
        return $ WithTangent primalsAux do
          Abs ib'' linLam'' <- sinkM (Abs ib' linLam')
          withSubstReaderT $ buildFor noHint d (sink ixTyDict) \i' -> do
            extendSubst (ib''@>Rename i') $ applyLinLam linLam''
      ReconWithData reconAbs -> do
        primals <- buildMap primalsAux getFst
        return $ WithTangent primals do
          Abs ib'' (Abs bs linLam') <- sinkM (Abs ib' reconAbs)
          withSubstReaderT $ buildFor noHint d (sink ixTyDict) \i' -> do
            extendSubst (ib''@> Rename i') do
              residuals' <- tabApp (sink primalsAux) (Var i') >>= getSnd >>= unpackTelescope bs
              extendSubst (bs @@> (SubstVal <$> residuals')) $
                applyLinLam linLam'
  RunReader r lam -> do
    WithTangent r' rLin <- linearizeAtom r
    (lam', recon) <- linearizeEffectFun Reader lam
    primalAux <- liftM Var (emit $ PrimOp $ Hof $ RunReader r' lam')
    referentTy <- getReferentTypeRWSAction lam'
    (primal, linLam) <- reconstruct primalAux recon
    return $ WithTangent primal do
      rLin' <- rLin
      tt <- tangentType $ sink referentTy
      tanEffLam <- buildEffLam noHint tt \h ref ->
        extendTangentArgss [h, ref] do
          withSubstReaderT $ applyLinLam $ sink linLam
      emitOp $ Hof $ RunReader rLin' tanEffLam
  RunState Nothing sInit lam -> do
    WithTangent sInit' sLin <- linearizeAtom sInit
    (lam', recon) <- linearizeEffectFun State lam
    (primalAux, sFinal) <- fromPair =<< liftM Var (emit $ PrimOp $ Hof $ RunState Nothing sInit' lam')
    referentTy <- getReferentTypeRWSAction lam'
    (primal, linLam) <- reconstruct primalAux recon
    return $ WithTangent (PairVal primal sFinal) do
      sLin' <- sLin
      tt <- tangentType $ sink referentTy
      tanEffLam <- buildEffLam noHint tt \h ref ->
        extendTangentArgss [h, ref] do
          withSubstReaderT $ applyLinLam $ sink linLam
      emitOp $ Hof $ RunState Nothing sLin' tanEffLam
  RunWriter Nothing bm lam -> do
    -- TODO: check it's actually the 0/+ monoid (or should we just build that in?)
    bm' <- renameM bm
    (lam', recon) <- linearizeEffectFun Writer lam
    (primalAux, wFinal) <- fromPair =<< liftM Var (emit $ PrimOp $ Hof $ RunWriter Nothing bm' lam')
    (primal, linLam) <- reconstruct primalAux recon
    referentTy <- getReferentTypeRWSAction lam'
    return $ WithTangent (PairVal primal wFinal) do
      bm'' <- sinkM bm'
      tt <- tangentType $ sink referentTy
      tanEffLam <- buildEffLam noHint tt \h ref ->
        extendTangentArgss [h, ref] do
          withSubstReaderT $ applyLinLam $ sink linLam
      emitOp $ Hof $ RunWriter Nothing bm'' tanEffLam
  RunIO body -> do
    (body', recon) <- linearizeBlockDefunc body
    primalAux <- liftM Var $ emit $ PrimOp $ Hof $ RunIO body'
    (primal, linLam) <- reconstruct primalAux recon
    return $ WithTangent primal do
      withSubstReaderT $ applyLinLam $ sink linLam
  _ -> error $ "not implemented: " ++ pprint hof

linearizeEffectFun :: RWS -> SLam i -> PrimalM i o (SLam o, LinLamAbs o)
linearizeEffectFun rws (BinaryLamExpr hB refB body) = do
  withFreshBinder noHint (TC HeapType) \h -> do
    bTy <- extendSubst (hB@>binderName h) $ renameM $ binderType refB
    withFreshBinder noHint bTy \b -> do
      let ref = binderName b
      hVar <- sinkM $ binderName h
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
    pTy <- getType $ sink p'
    zeroAt =<< tangentType pTy

notImplemented :: HasCallStack => a
notImplemented = error "Not implemented"

-- === boring instances ===

instance GenericE ActivePrimals where
  type RepE ActivePrimals = PairE (ListE SAtomName) (EffectRow SimpIR)
  fromE (ActivePrimals vs effs) = ListE vs `PairE` effs
  {-# INLINE fromE #-}
  toE   (ListE vs `PairE` effs) = ActivePrimals vs effs
  {-# INLINE toE #-}

instance SinkableE   ActivePrimals
instance HoistableE  ActivePrimals
instance AlphaEqE    ActivePrimals
instance RenameE     ActivePrimals

instance GenericE TangentArgs where
  type RepE TangentArgs = ListE SAtomName
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
