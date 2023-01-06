-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Linearize (linearize) where

import Control.Monad.Reader
import Data.Foldable (toList)
import Data.Functor
import Data.List (elemIndex)
import qualified Data.Set as S
import GHC.Stack

import Builder
import Core
import CheapReduction
import IRVariants
import MTL1
import Name
import Subst
import PPrint
import QueryType
import Types.Core
import Types.Source
import Types.Primitives
import Util (bindM2)

type CS = CoreToSimpIR

-- === linearization monad ===

data ActivePrimals (n::S) = ActivePrimals
  { activeVars    :: [AtomName CS n]  -- includes refs and regions
  , activeEffs    :: EffectRow n }

emptyActivePrimals :: ActivePrimals n
emptyActivePrimals = ActivePrimals [] Pure

data TangentArgs (n::S) = TangentArgs [CAtomName n]

type PrimalM  = SubstReaderT Name (ReaderT1 ActivePrimals (BuilderM CS)) :: MonadKind2
type TangentM = ReaderT1 TangentArgs (BuilderM CS) :: MonadKind1

data WithTangent (n::S) (e1::E) (e2::E) =
  WithTangent (e1 n) (forall l. (Emits l, DExt n l) => TangentM l (e2 l))

type LinM i o e1 e2 = PrimalM i o (WithTangent o e1 e2)

-- TODO: maybe we shouldn't roll subst into this
pureLin :: (RenameE e, SinkableE e) => e i -> LinM i o e e
pureLin x = do
  x' <- renameM x
  return $ WithTangent x' (sinkM x')

runPrimalM :: Subst Name i o -> ActivePrimals o -> PrimalM i o a -> BuilderM CS o a
runPrimalM subst args cont = runReaderT1 args $ runSubstReaderT subst cont

activePrimalIdx :: AtomName CS o -> PrimalM i o (Maybe Int)
activePrimalIdx v = asks \primals -> elemIndex v (activeVars primals)

getActivePrimals :: PrimalM i o (ActivePrimals o)
getActivePrimals = ask

extendActiveSubst
  :: BindsAtMostOneName b AtomNameC
  => b i i' -> AtomName CS o -> PrimalM i' o a -> PrimalM i o a
extendActiveSubst b v cont = do
  extendSubst (b@>v) $ extendActivePrimals v cont

extendActiveEffs :: Effect o -> PrimalM i o a -> PrimalM i o a
extendActiveEffs eff = local \primals ->
  primals { activeEffs = extendEffRow (S.singleton eff) (activeEffs primals)}

extendActivePrimals :: AtomName CS o -> PrimalM i o a -> PrimalM i o a
extendActivePrimals v =
  local \primals -> primals { activeVars = activeVars primals ++ [v] }

getTangentArg :: Int -> TangentM o (Atom CS o)
getTangentArg idx = asks \(TangentArgs vs) -> Var $ vs !! idx

extendTangentArgs :: CAtomName n -> TangentM n a -> TangentM n a
extendTangentArgs v m = local (\(TangentArgs vs) -> TangentArgs $ vs ++ [v]) m

getTangentArgs :: TangentM o (TangentArgs o)
getTangentArgs = ask

bindLin
  :: Emits o
  => LinM i o e  e
  -> (forall o' m. (Emits o', DExt o o', Builder CS m) => e o' -> m o' (e' o'))
  -> LinM i o e' e'
bindLin m f = do
  result <- m
  withBoth result f

withBoth
  :: Emits o
  => WithTangent o e e
  -> (forall o' m. (Emits o', DExt o o', Builder CS m) => e o' -> m o' (e' o'))
  -> PrimalM i o (WithTangent o e' e')
withBoth (WithTangent x tx) f = do
  Distinct <- getDistinct
  y <- f x
  return $ WithTangent y do
    tx >>= f

_withTangentComputation
  :: Emits o
  => WithTangent o e1 e2
  -> (forall o' m. (Emits o', DExt o o', Builder CS m) => e2 o' -> m o' (e2' o'))
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

injSubstM
  :: (SubstReader Name m, ScopeReader2 m
     , CovariantInIR e, SinkableE (e SimpIR), RenameE (e SimpIR))
  => e SimpIR i -> m i o (e CS o)
injSubstM e = injectIRE <$> renameM e
{-# INLINE injSubstM #-}

-- === converision between monadic and reified version of functions ===

withTangentFunAsLambda :: Emits o => LinM i o (Atom CS) (Atom CS) -> PrimalM i o (Atom CS o)
withTangentFunAsLambda cont = do
  WithTangent primalResult tf <- cont
  lam <- tangentFunAsLambda tf
  return $ PairVal primalResult lam

tangentFunType :: Type CS o -> PrimalM i o (Type CS o)
tangentFunType ty = do
  ActivePrimals primalVars effs <- getActivePrimals
  tangentTys <- varsAsBinderNest primalVars
  Abs bs effs' <- return $ abstractFreeVarsNoAnn primalVars effs
  buildNaryPi tangentTys \tangentVars -> do
    effs'' <- applyRename (bs @@> tangentVars) effs'
    buildNullaryPi effs'' $
      return $ sink ty

-- TODO: this sort of thing would make much more sense if we had proper n-ary
-- lambda atoms
tangentFunAsLambda
  :: Emits o
  => (forall o'. (DExt o o', Emits o') => TangentM o' (Atom CS o'))
  -> PrimalM i o (Atom CS o)
tangentFunAsLambda cont = do
  ActivePrimals primalVars _ <- getActivePrimals
  Abs tangentTys UnitE <- varsAsBinderNest primalVars
  lamExpr <- buildNaryLamExpr (EmptyAbs tangentTys) \tangentVars -> do
    buildPureLam noHint PlainArrow UnitTy \_ ->
      liftTangentM (TangentArgs $ map sink tangentVars) cont
  return $ naryLamExprToAtom lamExpr (map (const PlainArrow) primalVars)

-- Inverse of tangentFunAsLambda. Should be used inside a returned tangent action.
applyLinToTangents :: Emits n => Atom CS n -> TangentM n (Atom CS n)
applyLinToTangents f = do
  TangentArgs args <- getTangentArgs
  f'  <- naryApp f  $ map Var args
  app f' UnitVal

atomAsBinaryLamExpr :: (MonadFail1 m, EnvReader m) => Atom CS n -> m n (LamExpr CS n)
atomAsBinaryLamExpr f = do
  Pi (PiType (PiBinder b1 t1 _) _ (Pi (PiType (PiBinder b2 t2 _) _ _))) <- getType f
  liftBuilder $ buildNaryLamExpr (EmptyAbs (BinaryNest (b1:>t1) (b2:>t2))) \[x, y] ->
    naryApp (sink f) [Var x, Var y]

-- repeat the primal computation in the tangent part (this is ok if the
-- computation is cheap, e.g. the body of a table lambda)
_rematPrimal :: Emits o
            => Subst Name i o -> ActivePrimals o
            -> LinM i o e1 e2  -> TangentM o (e2 o)
_rematPrimal subst wrt m = do
  WithTangent _ lin <- lift11 $ runPrimalM subst wrt m
  Distinct <- getDistinct
  lin

fromPureUnaryTanFunLam :: EnvReader m => Atom r n -> m n (Atom r n)
fromPureUnaryTanFunLam atom = liftSubstEnvReaderM $ go atom
  where
    go :: Atom r i -> SubstEnvReaderM (AtomSubstVal r) i o (Atom r o)
    go = \case
      Lam (UnaryLamExpr b (AtomicBlock nullaryLam)) _ _ ->
        substBinders b \(b':>ty) -> do
          case nullaryLam of
            Lam (UnaryLamExpr unitBinder body) _ _ -> do
              body' <- extendSubst (unitBinder @> SubstVal UnitVal) $ substM body
              return $ lamExprToAtom (UnaryLamExpr (b':>ty) body') LinArrow (Just (Abs (b':>ty) Pure))
            _ -> error notValidStr
      _ -> error notValidStr
      where notValidStr = "not a pure unary tangent function: " ++ pprint atom

-- === actual linearization passs ===

-- main API entrypoint
linearize :: EnvReader m => LamExpr SimpIR n -> m n (Atom CoreToSimpIR n)
linearize x = liftBuilder $
  runPrimalM idSubst emptyActivePrimals $
    linearizeLambda' x
{-# SCC linearize #-}

-- reify the tangent builder as a lambda
linearizeLambda' :: LamExpr SimpIR i -> PrimalM i o (Atom CS o)
linearizeLambda' (UnaryLamExpr (b:>ty) body) = do
  ty' <- injSubstM ty
  buildLam (getNameHint b) PlainArrow ty' Pure \vp -> do
    extendActiveSubst b vp do
      WithTangent primalResult tangentAction <- linearizeBlock body
      tanFun <- tangentFunAsLambda tangentAction
      lam <- fromPureUnaryTanFunLam tanFun
      return $ PairVal primalResult lam
linearizeLambda' _ = error "not implemented"

linearizeAtom :: Emits o => Atom SimpIR i -> LinM i o (Atom CS) (Atom CS)
linearizeAtom atom = case atom of
  Var v -> do
    v' <- renameM v
    activePrimalIdx v' >>= \case
      Nothing -> withZeroT $ return (Var v')
      Just idx -> return $ WithTangent (Var v') $ getTangentArg idx
  Con con -> linearizePrimCon con
  DepPair _ _ _     -> notImplemented
  TabPi _         -> emitZeroT
  DepPairTy _     -> emitZeroT
  TC _            -> emitZeroT
  PtrVar _        -> emitZeroT
  ProjectElt i x -> do
    WithTangent x' tx <- linearizeAtom x
    xi <- normalizeProj i x'
    return $ WithTangent xi do
      t <- tx
      normalizeProj i t
  SimpInCore _ _ -> error "shouldn't occur in simplified IR"  -- TODO
  where emitZeroT = withZeroT $ injSubstM atom

linearizeBlock :: Emits o => SBlock i -> LinM i o (Atom CS) (Atom CS)
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
      v <- emit $ injectCS expr'
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

linearizeExpr :: Emits o => SExpr i -> LinM i o (Atom CS) (Atom CS)
linearizeExpr expr = case expr of
  Atom x -> linearizeAtom x
  App (Var f) xs -> do
    f' <- renameM f
    lookupCustomRules f' >>= \case
      Nothing -> error "not implemented"
      Just rule -> applyCustomLinearization rule (toList xs)
  App _ _ -> error "not implemented"
  TabApp x idxs -> do
    zipLin (linearizeAtom x) (pureLin $ ListE $ map injectCS $ toList idxs) `bindLin`
      \(PairE x' (ListE idxs')) -> naryTabApp x' idxs'
  PrimOp op      -> linearizeOp op
  RefOp ref m -> case m of
    MAsk -> linearizeAtom ref `bindLin` \ref' -> liftM Var $ emit $ RefOp ref' MAsk
    MExtend monoid x -> do
      -- TODO: check that we're dealing with a +/0 monoid
      monoid' <- injSubstM monoid
      zipLin (linearizeAtom ref) (linearizeAtom x) `bindLin` \(PairE ref' x') ->
        liftM Var $ emit $ RefOp ref' $ MExtend (sink monoid') x'
    MGet   -> linearizeAtom ref `bindLin` \ref' -> liftM Var $ emit $ RefOp ref' MGet
    MPut x -> zipLin (linearizeAtom ref) (linearizeAtom x) `bindLin` \(PairE ref' x') ->
                liftM Var $ emit $ RefOp ref' $ MPut x'

    IndexRef i -> zipLin (la ref) (pureLin (injectCS i)) `bindLin`
                    \(PairE ref' i') -> emitExpr $ RefOp ref' $ IndexRef i'
    ProjRef i -> la ref `bindLin` \ref' -> emitExpr $ RefOp ref' $ ProjRef i
  Hof e      -> linearizeHof e
  Case e alts resultTy _ -> do
    e' <- injSubstM e
    resultTy' <- injSubstM resultTy
    isActive e' >>= \case
      True -> notImplemented
      False -> do
        resultTangentType <- tangentTypeCS resultTy'
        resultTyWithTangent <- PairTy <$> injSubstM resultTy
                                      <*> tangentFunType resultTangentType
        (ans, linLam) <- fromPair =<< buildCase e' resultTyWithTangent \i x -> do
          x' <- emitAtomToName noHint x
          Abs b body <- return $ alts !! i
          extendSubst (b @> x') $ withTangentFunAsLambda $ linearizeBlock body
        return $ WithTangent ans do
          applyLinToTangents $ sink linLam
  TabCon ty xs -> do
    ty' <- injSubstM ty
    seqLin (map linearizeAtom xs) `bindLin` \(ComposeE xs') ->
      emitExpr $ TabCon (sink ty') xs'
  DAMOp _        -> error "shouldn't occur here"
  where
    la = linearizeAtom

linearizeOp :: Emits o => PrimOp (Atom SimpIR i) -> LinM i o (Atom CS) (Atom CS)
linearizeOp op = case op of
  UnOp  uop x       -> linearizeUnOp  uop x
  BinOp bop x y     -> linearizeBinOp bop x y
  -- XXX: This assumes that pointers are always constants
  MemOp _      -> emitZeroT
  MiscOp miscOp -> linearizeMiscOp miscOp
  VectorOp _ -> error "not implemented"
  where
    emitZeroT = withZeroT $ liftM Var $ emit =<< injSubstM (PrimOp op)

linearizeMiscOp :: Emits o => MiscOp (Atom SimpIR i) -> LinM i o (Atom CS) (Atom CS)
linearizeMiscOp op = case op of
  SumTag _     -> emitZeroT
  ToEnum _ _   -> emitZeroT
  Select p t f -> (pureLin (injectCS p) `zipLin` la t `zipLin` la f) `bindLin`
                     \(p' `PairE` t' `PairE` f') -> emitOp $ MiscOp $ Select p' t' f'
  CastOp t v -> do
    vt <- getType =<< injSubstM v
    t' <- injSubstM t
    vtTangentType <- tangentTypeCS vt
    tTangentType  <- tangentTypeCS t'
    ((&&) <$> (vtTangentType `alphaEq` vt)
          <*> (tTangentType  `alphaEq` t')) >>= \case
      True -> do
        linearizeAtom v `bindLin` \v' -> emitOp $ MiscOp $ CastOp (sink t') v'
      False -> do
        WithTangent x xt <- linearizeAtom v
        yt <- case (vtTangentType, tTangentType) of
          (_     , UnitTy) -> return $ UnitVal
          (UnitTy, tt    ) -> zeroAtCS tt
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
    emitZeroT = withZeroT $ liftM Var $ emit =<< injSubstM (PrimOp $ MiscOp op)
    la = linearizeAtom

linearizeUnOp :: Emits o => UnOp -> Atom SimpIR i -> LinM i o (Atom CS) (Atom CS)
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

linearizeBinOp :: Emits o => BinOp -> SAtom i -> SAtom i -> LinM i o (Atom CS) (Atom CS)
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
referToPrimal :: (Builder CoreIR m, Emits l, DExt n l) => CAtom n -> m l (CAtom l)
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

linearizePrimCon :: Emits o => Con SimpIR i -> LinM i o (Atom CS) (Atom CS)
linearizePrimCon con = case con of
  Lit _ -> emitZeroT
  ProdCon xs -> fmapLin (ProdVal . fromComposeE) $ seqLin (fmap linearizeAtom xs)
  SumCon  _ _ _ -> notImplemented
  SumAsProd tys tg elems -> do
    tys' <- forM tys \t -> injSubstM t
    tg' <- injSubstM tg
    -- There must be a way to do this with `seqLin` etc but it's too much for me
    elemsWithT <- traverse linearizeAtom elems
    let elemsP = fmap (\(WithTangent x _) -> x) elemsWithT
    return $ WithTangent (Con $ SumAsProd tys' tg' elemsP) do
      elemsT <- forM elemsWithT \(WithTangent _ t) -> t
      return $ Con $ SumAsProd (sinkList tys') (sink tg') elemsT
  DictHole _ _ -> error "impossible"  -- TODO: static constraint
  HeapVal -> emitZeroT
  where emitZeroT = withZeroT $ injSubstM $ Con con

linearizeHof :: Emits o => Hof SimpIR i -> LinM i o (Atom CS) (Atom CS)
linearizeHof hof = case hof of
  For d ixDict (UnaryLamExpr i body) -> do
    ixTy <- ixTyFromDict =<< injSubstM ixDict
    ansWithLinTab <- buildFor (getNameHint i) d ixTy \i' ->
      extendSubst (i@>i') $ withTangentFunAsLambda $ linearizeBlock body
    (ans, linTab) <- unzipTab ansWithLinTab
    return $ WithTangent ans do
      buildFor (getNameHint i) d (sink ixTy) \i' ->
        tabApp (sink linTab) (Var i') >>= applyLinToTangents
  RunReader r lam -> do
    WithTangent r' rLin <- linearizeAtom r
    lam' <- linearizeEffectFun Reader lam
    result <- liftM Var (emit $ Hof $ RunReader r' lam')
    (primalResult, tangentLam) <- fromPair result
    return $ WithTangent primalResult do
      rLin' <- rLin
      tanEffectLam <- atomAsBinaryLamExpr =<< applyLinToTangents (sink tangentLam)
      liftM Var $ emit $ Hof $ RunReader rLin' tanEffectLam
  RunState Nothing sInit lam -> do
    WithTangent sInit' sLin <- linearizeAtom sInit
    lam' <- linearizeEffectFun State lam
    (result, sFinal) <- fromPair =<< liftM Var (emit $ Hof $ RunState Nothing sInit' lam')
    (primalResult, tangentLam) <- fromPair result
    return $ WithTangent (PairVal primalResult sFinal) do
      sLin' <- sLin
      tanEffectLam <- atomAsBinaryLamExpr =<< applyLinToTangents (sink tangentLam)
      liftM Var $ emit $ Hof $ RunState Nothing sLin' tanEffectLam
  RunWriter Nothing bm lam -> do
    -- TODO: check it's actually the 0/+ monoid (or should we just build that in?)
    bm' <- injSubstM bm
    lam' <- linearizeEffectFun Writer lam
    (result, wFinal) <- fromPair =<< liftM Var (emit $ Hof $ RunWriter Nothing bm' lam')
    (primalResult, tangentLam) <- fromPair result
    return $ WithTangent (PairVal primalResult wFinal) do
      bm'' <- sinkM bm'
      tanEffectLam <- atomAsBinaryLamExpr =<< applyLinToTangents (sink tangentLam)
      liftM Var $ emit $ Hof $ RunWriter Nothing bm'' tanEffectLam
  RunIO body -> do
    ioLam <- buildBlock do
      WithTangent primalResult tangentFun <- linearizeBlock body
      lam <- tangentFunAsLambda tangentFun
      return $ PairVal primalResult lam
    result <- liftM Var $ emit $ Hof $ RunIO ioLam
    (ans, linLam) <- fromPair result
    return $ WithTangent ans $ applyLinToTangents (sink linLam)
  _ -> error $ "not implemented: " ++ pprint hof

applyCustomLinearization :: Emits o => AtomRules o -> [SAtom i] -> LinM i o CAtom CAtom
applyCustomLinearization = undefined
-- applyCustomLinearization (CustomLinearize n zeros cl) xs = do
--   let (polyXs, argXs) = splitAt n $ toList xs
--   polyXs' <- mapM (renameM . injectCore) polyXs
--   (any id <$> mapM isActive polyXs') >>= \case
--     True -> error $
--       "Polymorphic arguments of custom linearization rules are " ++
--       "expected to be inactive (i.e. independent of any differentiated " ++
--       "function argument)"
--     False -> return ()
--   wts <- case zeros of
--     InstantiateZeros -> forM (toList argXs) linearizeAtom
--     SymbolicZeros -> do
--       stDefName <- lookupSourceMap "ZeroTangent" >>= \case
--         Just (UDataConVar conName) -> do
--           DataConBinding dataDefName zeroConIx _ <- lookupEnv conName
--           unless (zeroConIx == 0) $ error "Ill-defined SymbolicTangent?"
--           return dataDefName
--         _ -> error "Ill-defined SymbolicTangent?"
--       forM (toList argXs) \arg -> do
--         arg' <- renameM arg
--         argTy' <- getType arg'
--         isActive arg' >>= \case
--           False -> -- Pass in ZeroTangent as the tangent
--             return $ WithTangent (injectCore arg') $
--               return $ sink $ Con $ Newtype
--                 (TypeCon "SymbolicTangent" stDefName
--                  (DataDefParams [(PlainArrow, injectCore argTy')]))
--                 (SumVal [UnitTy, injectCore argTy'] 0 UnitVal)
--           True -> do  -- Wrap tangent in SomeTangent
--             WithTangent arg'' argLin <- dropSubst $ linearizeAtom arg'
--             return $ WithTangent arg'' $ argLin <&> \argTan ->
--               Con $ Newtype
--                 (TypeCon "SymbolicTangent" (sink stDefName)
--                  (DataDefParams [(PlainArrow, sink (injectIRE argTy'))]))
--                 (SumVal [UnitTy, sink (injectIRE argTy')] 1 argTan)
--   (ans, flin) <- fromPair =<< naryApp cl (polyXs' ++ (wts <&> \(WithTangent p _) -> p))
--   return $ WithTangent ans $ naryApp (sink flin) =<< sequence (wts <&> \(WithTangent _ t) -> t)

-- takes an effect function, of type `(h:Type) -> Ref h s -> a``
-- and augments it with the tangent lambda, so instead of returning `a`, it returns:
-- `[tangent args] -> (a & ((h':Type) -> (ref':Ref h' (T s)) -> T a))`
linearizeEffectFun :: RWS -> LamExpr SimpIR i -> PrimalM i o (LamExpr CS o)
linearizeEffectFun rws (BinaryLamExpr hB refB body) = do
  RefTy _ referentTy <- injSubstM =<< getReferentTy (EmptyAbs $ PairB hB refB)
  buildEffLam rws (getNameHint refB) referentTy \h ref -> withTangentFunAsLambda do
    extendActiveSubst hB h $ extendActiveSubst refB ref $
      extendActiveEffs (RWSEffect rws (Just h)) do
        WithTangent p tangentFun <- linearizeBlock body
        return $ WithTangent p do
          tt <- tangentTypeCS $ sink referentTy
          lamExpr <- buildEffLam rws (getNameHint refB) tt \h' ref' ->
            extendTangentArgs h' $ extendTangentArgs ref' $
              tangentFun
          return $ naryLamExprToAtom lamExpr [PlainArrow, PlainArrow]
linearizeEffectFun _ _ = error "expected a binary lambda"

withT :: PrimalM i o (e1 o)
      -> (forall o'. (Emits o', DExt o o') => TangentM o' (e2 o'))
      -> PrimalM i o (WithTangent o e1 e2)
withT p t = do
  p' <- p
  return $ WithTangent p' t

withZeroT :: PrimalM i o (Atom CS o)
          -> PrimalM i o (WithTangent o (Atom CS) (Atom CS))
withZeroT p = do
  p' <- p
  return $ WithTangent p' do
    pTy <- getType $ sink p'
    zeroAtCS =<< tangentTypeCS pTy

zeroAtCS :: EnvReader m => Type CS n -> m n (Atom CS n)
zeroAtCS = undefined

tangentTypeCS :: EnvReader m => Type CS n -> m n (Type CS n)
tangentTypeCS = undefined

notImplemented :: HasCallStack => a
notImplemented = error "Not implemented"

injectCS :: CovariantInIR e => e SimpIR n -> e CS n
injectCS = injectIRE
{-# INLINE injectCS #-}

-- === instances ===

instance GenericE ActivePrimals where
  type RepE ActivePrimals = PairE (ListE (AtomName CS)) EffectRow
  fromE (ActivePrimals vs effs) = ListE vs `PairE` effs
  {-# INLINE fromE #-}
  toE   (ListE vs `PairE` effs) = ActivePrimals vs effs
  {-# INLINE toE #-}

instance SinkableE   ActivePrimals
instance HoistableE  ActivePrimals
instance AlphaEqE    ActivePrimals
instance RenameE     ActivePrimals

instance GenericE TangentArgs where
  type RepE TangentArgs = ListE (AtomName CS)
  fromE (TangentArgs vs) = ListE vs
  {-# INLINE fromE #-}
  toE   (ListE vs) = TangentArgs vs
  {-# INLINE toE #-}

instance SinkableE   TangentArgs
instance HoistableE  TangentArgs
instance AlphaEqE    TangentArgs
instance RenameE     TangentArgs
