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

import Name
import Builder
import Syntax
import MTL1
import QueryType
import Util (bindM2)
import PPrint
import Types.Core
import Core

-- === linearization monad ===

data ActivePrimals (n::S) = ActivePrimals
  { activeVars    :: [AtomName n]  -- includes refs and regions
  , activeEffs    :: EffectRow n }

emptyActivePrimals :: ActivePrimals n
emptyActivePrimals = ActivePrimals [] Pure

data TangentArgs (n::S) = TangentArgs [AtomName n]

type PrimalM  = SubstReaderT Name (ReaderT1 ActivePrimals BuilderM) :: MonadKind2
type TangentM = ReaderT1 TangentArgs BuilderM :: MonadKind1

data WithTangent (n::S) (e1::E) (e2::E) =
  WithTangent (e1 n) (forall l. (Emits l, DExt n l) => TangentM l (e2 l))

type LinM i o e1 e2 = PrimalM i o (WithTangent o e1 e2)

-- TODO: maybe we shouldn't roll subst into this
pureLin :: (SubstE Name e, SinkableE e) => e i -> LinM i o e e
pureLin x = do
  x' <- substM x
  return $ WithTangent x' (sinkM x')

runPrimalM :: Subst Name i o -> ActivePrimals o -> PrimalM i o a -> BuilderM o a
runPrimalM subst args cont = runReaderT1 args $ runSubstReaderT subst cont

activePrimalIdx :: AtomName o -> PrimalM i o (Maybe Int)
activePrimalIdx v = asks \primals -> elemIndex v (activeVars primals)

getActivePrimals :: PrimalM i o (ActivePrimals o)
getActivePrimals = ask

extendActiveSubst
  :: BindsAtMostOneName b AtomNameC
  => b i i' -> AtomName o -> PrimalM i' o a -> PrimalM i o a
extendActiveSubst b v cont = do
  extendSubst (b@>v) $ extendActivePrimals v cont

extendActiveEffs :: Effect o -> PrimalM i o a -> PrimalM i o a
extendActiveEffs eff = local \primals ->
  primals { activeEffs = extendEffRow (S.singleton eff) (activeEffs primals)}

extendActivePrimals :: AtomName o -> PrimalM i o a -> PrimalM i o a
extendActivePrimals v =
  local \primals -> primals { activeVars = activeVars primals ++ [v] }

getTangentArg :: Int -> TangentM o (Atom o)
getTangentArg idx = asks \(TangentArgs vs) -> Var $ vs !! idx

extendTangentArgs :: AtomName n -> TangentM n a -> TangentM n a
extendTangentArgs v m = local (\(TangentArgs vs) -> TangentArgs $ vs ++ [v]) m

getTangentArgs :: TangentM o (TangentArgs o)
getTangentArgs = ask

bindLin
  :: Emits o
  => LinM i o e  e
  -> (forall o' m. (Emits o', DExt o o', Builder m) => e o' -> m o' (e' o'))
  -> LinM i o e' e'
bindLin m f = do
  result <- m
  withBoth result f

withBoth
  :: Emits o
  => WithTangent o e e
  -> (forall o' m. (Emits o', DExt o o', Builder m) => e o' -> m o' (e' o'))
  -> PrimalM i o (WithTangent o e' e')
withBoth (WithTangent x tx) f = do
  Distinct <- getDistinct
  y <- f x
  return $ WithTangent y do
    tx >>= f

_withTangentComputation
  :: Emits o
  => WithTangent o e1 e2
  -> (forall o' m. (Emits o', DExt o o', Builder m) => e2 o' -> m o' (e2' o'))
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

traverseLin
  :: Traversable f
  => (a -> LinM i o e e)
  -> f a
  -> LinM i o (ComposeE f e) (ComposeE f e)
traverseLin f xs = seqLin $ fmap f xs

liftTangentM :: TangentArgs o -> TangentM o a -> PrimalM i o a
liftTangentM args m = liftSubstReaderT $ lift11 $ runReaderT1 args m

isTrivialForAD :: Expr o -> PrimalM i o Bool
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

withTangentFunAsLambda :: Emits o => LinM i o Atom Atom -> PrimalM i o (Atom o)
withTangentFunAsLambda cont = do
  WithTangent primalResult tf <- cont
  lam <- tangentFunAsLambda tf
  return $ PairVal primalResult lam

tangentFunType :: Type o -> PrimalM i o (Type o)
tangentFunType ty = do
  ActivePrimals primalVars effs <- getActivePrimals
  tangentTys <- varsAsBinderNest primalVars
  let effAbs = abstractFreeVarsNoAnn primalVars effs
  buildNaryPi tangentTys \tangentVars -> do
    effs' <- applyNaryAbs (sink effAbs) tangentVars
    buildNullaryPi effs' $
      return $ sink ty

tangentFunAsLambda
  :: Emits o
  => (forall o'. (DExt o o', Emits o') => TangentM o' (Atom o'))
  -> PrimalM i o (Atom o)
tangentFunAsLambda cont = do
  ActivePrimals primalVars effs <- getActivePrimals
  tangentTys <- varsAsBinderNest primalVars
  let effAbs = abstractFreeVarsNoAnn primalVars effs
  buildNaryLam tangentTys \tangentVars -> do
    effs' <- applyNaryAbs (sink effAbs) tangentVars
    buildNullaryLam effs' $
      liftTangentM (TangentArgs $ map sink tangentVars) cont

-- Inverse of tangentFunAsLambda. Should be used inside a returned tangent action.
applyLinToTangents :: Emits n => Atom n -> TangentM n (Atom n)
applyLinToTangents f = do
  TangentArgs args <- getTangentArgs
  f'  <- naryApp f  $ map Var args
  app f' UnitVal

-- repeat the primal computation in the tangent part (this is ok if the
-- computation is cheap, e.g. the body of a table lambda)
rematPrimal :: Emits o
            => Subst Name i o -> ActivePrimals o
            -> LinM i o e1 e2  -> TangentM o (e2 o)
rematPrimal subst wrt m = do
  WithTangent _ lin <- lift11 $ runPrimalM subst wrt m
  Distinct <- getDistinct
  lin

fromPureUnaryTanFunLam :: EnvReader m => Atom n -> m n (Atom n)
fromPureUnaryTanFunLam atom = liftSubstEnvReaderM $ go atom
  where
    go :: Atom i -> SubstEnvReaderM AtomSubstVal i o (Atom o)
    go = \case
      Lam (LamExpr b@(LamBinder _ _ _ Pure) (AtomicBlock nullaryLam)) ->
        substBinders b \(LamBinder b' ty _ _) -> do
          case nullaryLam of
            Lam (LamExpr unitBinder body) -> do
              body' <- extendSubst (unitBinder @> SubstVal UnitVal) $ substM body
              return $ Lam $ LamExpr (LamBinder b' ty LinArrow Pure) body'
            _ -> error notValidStr
      _ -> error notValidStr
      where notValidStr = "not a pure unary tangent function: " ++ pprint atom

-- === actual linearization passs ===

-- main API entrypoint
linearize :: EnvReader m => Atom n -> m n (Atom n)
linearize x = liftBuilder $
  runPrimalM idSubst emptyActivePrimals $
    linearizeLambda' x
{-# SCC linearize #-}

-- reify the tangent builder as a lambda
linearizeLambda' :: Atom i -> PrimalM i o (Atom o)
linearizeLambda' (Lam (LamExpr (LamBinder b ty PlainArrow Pure) body)) = do
  ty' <- substM ty
  buildLam (getNameHint b) PlainArrow ty' Pure \vp -> do
    extendActiveSubst b vp do
      WithTangent primalResult tangentAction <- linearizeBlock body
      tanFun <- tangentFunAsLambda tangentAction
      lam <- fromPureUnaryTanFunLam tanFun
      return $ PairVal primalResult lam
linearizeLambda' _ = error "not implemented"

linearizeAtom :: Emits o => Atom i -> LinM i o Atom Atom
linearizeAtom atom = case atom of
  Var v -> do
    v' <- substM v
    activePrimalIdx v' >>= \case
      Nothing -> withZeroT $ return (Var v')
      Just idx -> return $ WithTangent (Var v') $ getTangentArg idx
  Con con -> linearizePrimCon con
  TabLam (TabLamExpr b body) -> do
    ty <- substM $ binderAnn b
    wrt <- getActivePrimals
    subst <- getSubst
    atom' <- substM atom
    return $ WithTangent atom' do
      buildTabLam (getNameHint b) (sink ty) \i ->
        rematPrimal (sink subst) (sink wrt) $
          extendSubst (b@>i) $ linearizeBlock body
  DataCon _ _ _ _ _ -> notImplemented  -- Need to synthesize or look up a tangent ADT
  DictCon _ -> notImplemented
  DictTy _  -> notImplemented
  DepPair _ _ _     -> notImplemented
  Record elems ->
    fmapLin (Record . fromComposeE) $ seqLin (fmap linearizeAtom elems)
  Variant t l i e -> do
    t' <- substM $ ExtLabeledItemsE t
    linearizeAtom e `bindLin` \e' ->
      return $ Variant (fromExtLabeledItemsE $ sink t') l i e'
  TypeCon _ _ _   -> emitZeroT
  LabeledRow _    -> emitZeroT
  RecordTy _      -> emitZeroT
  VariantTy _     -> emitZeroT
  Pi _            -> emitZeroT
  TabPi _         -> emitZeroT
  DepPairTy _     -> emitZeroT
  TC _            -> emitZeroT
  Eff _           -> emitZeroT
  ProjectElt idxs v ->
    linearizeAtom (Var v) `bindLin` \x ->
      return $ getProjection (toList idxs) x
  -- Those should be gone after simplification
  Lam _            -> error "Unexpected non-table lambda"
  ACase _ _ _      -> error "Unexpected ACase"
  DataConRef _ _ _ -> error "Unexpected ref"
  BoxedRef _       -> error "Unexpected ref"
  DepPairRef _ _ _ -> error "Unexpected ref"
  where emitZeroT = withZeroT $ substM atom

linearizeBlock :: Emits o => Block i -> LinM i o Atom Atom
linearizeBlock (Block _ decls result) =
  linearizeDecls decls $ linearizeAtom result

linearizeDecls :: Emits o => Nest Decl i i' -> LinM i' o e1 e2 -> LinM i  o e1 e2
linearizeDecls Empty cont = cont
-- TODO: as an optimization, don't bother extending the tangent args if the
-- tangent is trivial, either because its type is a singleton or because there
-- are no active vars.
linearizeDecls (Nest (Let b (DeclBinding ann _ expr)) rest) cont = do
  expr' <- substM expr
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

linearizeExpr :: Emits o => Expr i -> LinM i o Atom Atom
linearizeExpr expr = case expr of
  Atom x -> linearizeAtom x
  App (Var f) xs -> do
    f' <- substM f
    lookupCustomRules f' >>= \case
      Nothing -> error "not implemented"
      Just (CustomLinearize n zeros cl) -> do
        let (polyXs, argXs) = splitAt n $ toList xs
        polyXs' <- mapM substM polyXs
        (any id <$> mapM isActive polyXs') >>= \case
          True -> error $
            "Polymorphic arguments of custom linearization rules are " ++
            "expected to be inactive (i.e. independent of any differentiated " ++
            "function argument)"
          False -> return ()
        wts <- case zeros of
          InstantiateZeros -> forM (toList argXs) linearizeAtom
          SymbolicZeros -> do
            stDefName <- lookupSourceMap "ZeroTangent" >>= \case
              Just (UDataConVar conName) -> do
                DataConBinding dataDefName zeroConIx _ <- lookupEnv conName
                unless (zeroConIx == 0) $ error "Ill-defined SymbolicTangent?"
                return dataDefName
              _ -> error "Ill-defined SymbolicTangent?"
            forM (toList argXs) \arg -> do
              arg' <- substM arg
              argTy' <- getType arg'
              isActive arg' >>= \case
                False -> -- Pass in ZeroTangent as the tangent
                  return $ WithTangent arg' $
                    return $ sink $ DataCon "SymbolicTangent" stDefName
                                    (DataDefParams [argTy'] []) 0 []
                True -> do  -- Wrap tangent in SomeTangent
                  WithTangent arg'' argLin <- dropSubst $ linearizeAtom arg'
                  return $ WithTangent arg'' $ argLin <&> \argTan ->
                    DataCon "SymbolicTangent" (sink stDefName)
                    (DataDefParams [sink argTy'] []) 1 [argTan]
        (ans, flin) <- fromPair =<< naryApp cl (polyXs' ++ (wts <&> \(WithTangent p _) -> p))
        return $ WithTangent ans $ naryApp (sink flin) =<< sequence (wts <&> \(WithTangent _ t) -> t)
  App _ _ -> error "not implemented"
  TabApp x idxs -> do
    zipLin (linearizeAtom x) (pureLin $ ListE $ toList idxs) `bindLin`
      \(PairE x' (ListE idxs')) -> naryTabApp x' idxs'
  Op op      -> linearizeOp op
  Hof e      -> linearizeHof e
  Case e alts resultTy _ -> do
    e' <- substM e
    resultTy' <- substM resultTy
    isActive e' >>= \case
      True -> notImplemented
      False -> do
        resultTangentType <- tangentType resultTy'
        resultTyWithTangent <- PairTy <$> substM resultTy
                                      <*> tangentFunType resultTangentType
        (ans, linLam) <- fromPair =<< buildCase e' resultTyWithTangent \i xs -> do
          xs' <- mapM emitAtomToName xs
          Abs bs body <- return $ alts !! i
          extendSubst (bs @@> xs') $ withTangentFunAsLambda $ linearizeBlock body
        return $ WithTangent ans do
          applyLinToTangents $ sink linLam

linearizeOp :: Emits o => Op i -> LinM i o Atom Atom
linearizeOp op = case op of
  UnOp  uop x       -> linearizeUnOp  uop x
  BinOp bop x y     -> linearizeBinOp bop x y
  PrimEffect ref m -> case m of
    MAsk -> linearizeAtom ref `bindLin` \ref' -> emitOp $ PrimEffect ref' MAsk
    MExtend monoid x -> do
      -- TODO: check that we're dealing with a +/0 monoid
      monoid' <- mapM substM monoid
      zipLin (linearizeAtom ref) (linearizeAtom x) `bindLin` \(PairE ref' x') ->
        emitOp $ PrimEffect ref' $ MExtend (fmap sink monoid') x'
    MGet   -> linearizeAtom ref `bindLin` \ref' -> emitOp $ PrimEffect ref' MGet
    MPut x -> zipLin (linearizeAtom ref) (linearizeAtom x) `bindLin` \(PairE ref' x') ->
                emitOp $ PrimEffect ref' $ MPut x'
  IndexRef ref i -> zipLin (la ref) (pureLin i) `bindLin`
                      \(PairE ref' i') -> emitOp $ IndexRef ref' i'
  ProjRef i ref -> la ref `bindLin` \ref' -> emitOp $ ProjRef i ref'
  Select p t f -> (pureLin p `zipLin` la t `zipLin` la f) `bindLin`
                     \(p' `PairE` t' `PairE` f') -> emitOp $ Select p' t' f'
  -- XXX: This assumes that pointers are always constants
  PtrLoad _              -> emitZeroT
  PtrStore _ _           -> emitZeroT
  PtrOffset _ _          -> emitZeroT
  IOAlloc _ _            -> emitZeroT
  IOFree _               -> emitZeroT
  ThrowError _           -> emitZeroT
  DataConTag _           -> emitZeroT
  ToEnum _ _             -> emitZeroT
  TabCon ty xs -> do
    ty' <- substM ty
    seqLin (map linearizeAtom xs) `bindLin` \(ComposeE xs') ->
      emitOp $ TabCon (sink ty') xs'
  CastOp t v             -> do
    vt <- getType =<< substM v
    t' <- substM t
    vtTangentType <- tangentType vt
    tTangentType  <- tangentType t'
    ((&&) <$> (vtTangentType `alphaEq` vt)
          <*> (tTangentType  `alphaEq` t')) >>= \case
      True -> do
        linearizeAtom v `bindLin` \v' -> emitOp $ CastOp (sink t') v'
      False -> do
        WithTangent x xt <- linearizeAtom v
        yt <- case (vtTangentType, tTangentType) of
          (_     , UnitTy) -> return $ UnitVal
          (UnitTy, tt    ) -> zeroAt tt
          _                -> error "Expected at least one side of the CastOp to have a trivial tangent type"
        y <- emitOp $ CastOp t' x
        return $ WithTangent y do xt >> return (sink yt)
  RecordCons l r ->
    zipLin (la l) (la r) `bindLin` \(PairE l' r') ->
      emitOp $ RecordCons l' r'
  RecordSplit f r ->
    zipLin (la f) (la r) `bindLin` \(PairE f' r') ->
      emitOp $ RecordSplit f' r'
  VariantLift ts v ->
    zipLin (traverseLin pureLin ts) (la v) `bindLin`
      \(PairE (ComposeE ts') v') -> emitOp $ VariantLift ts' v'
  VariantSplit ts v ->
    zipLin (traverseLin pureLin ts) (la v) `bindLin`
      \(PairE (ComposeE ts') v') -> emitOp $ VariantSplit ts' v'
  ThrowException _       -> notImplemented
  SumToVariant _         -> notImplemented
  OutputStreamPtr        -> emitZeroT
  _ -> notImplemented
  where
    emitZeroT = withZeroT $ liftM Var $ emit =<< substM (Op op)
    la = linearizeAtom

linearizeUnOp :: Emits o => UnOp -> Atom i -> LinM i o Atom Atom
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
    FNeg   -> withT (neg x) (neg =<< tx)
    BNot   -> emitZeroT

linearizeBinOp :: Emits o => BinOp -> Atom i -> Atom i -> LinM i o Atom Atom
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
                  (bindM2 add (bindM2 mul (sinkM x) ty)
                              (bindM2 mul tx (sinkM y)))
    FDiv -> withT (div' x y) do
      tx' <- bindM2 div' tx (sinkM y)
      ty' <- bindM2 div' (bindM2 mul (sinkM x) ty)
                      (bindM2 mul (sinkM y) (sinkM y))
      sub tx' ty'
    FPow -> withT (emitOp $ BinOp FPow x y) do
      c <- fpow (sink x) =<< bindM2 sub (sinkM y) (1.0 `fLitLike` sink y)
      tx' <- bindM2 mul tx (sinkM y)
      ty' <- bindM2 mul (bindM2 mul (sinkM x) ty) (flog $ sink x)
      mul c =<< add tx' ty'
    FCmp _ -> emitZeroT
    BAnd   -> emitZeroT
    BOr    -> emitZeroT
    BXor   -> emitZeroT
    BShL   -> emitZeroT
    BShR   -> emitZeroT

linearizePrimCon :: Emits o => Con i -> LinM i o Atom Atom
linearizePrimCon con = case con of
  Lit _ -> emitZeroT
  ProdCon xs -> fmapLin (ProdVal . fromComposeE) $ seqLin (fmap linearizeAtom xs)
  SumCon  _ _ _ -> notImplemented
  SumAsProd ty tg elems -> do
    ty' <- substM ty
    tg' <- substM tg
    -- There must be a way to do this with `seqLin` etc but it's too much for me
    elemsWithT <- traverse (traverse linearizeAtom) elems
    let elemsP = fmap (fmap (\(WithTangent x _) -> x)) elemsWithT
    return $ WithTangent (Con $ SumAsProd ty' tg' elemsP) do
      elemsT <- forM elemsWithT \elemsWithT' ->
                  forM elemsWithT' \(WithTangent _ t) -> t
      return $ Con $ SumAsProd (sink ty') (sink tg') elemsT
  FinVal _ _            -> emitZeroT
  LabelCon _     -> error "Unexpected label"
  BaseTypeRef _  -> error "Unexpected ref"
  TabRef _       -> error "Unexpected ref"
  ConRef _       -> error "Unexpected ref"
  RecordRef _    -> error "Unexpected ref"
  ExplicitDict  _ _ -> error "Unexpected ExplicitDict"
  DictHole _ _ -> error "Unexpected DictHole"
  where emitZeroT = withZeroT $ substM $ Con con

linearizeHof :: Emits o => Hof i -> LinM i o Atom Atom
linearizeHof hof = case hof of
  For d ixDict (Lam (LamExpr i body)) -> do
    ixTy <- ixTyFromDict =<< substM ixDict
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
      tanEffectLam <- applyLinToTangents $ sink tangentLam
      liftM Var $ emit $ Hof $ RunReader rLin' tanEffectLam
  RunState sInit lam -> do
    WithTangent sInit' sLin <- linearizeAtom sInit
    lam' <- linearizeEffectFun State lam
    (result, sFinal) <- fromPair =<< liftM Var (emit $ Hof $ RunState sInit' lam')
    (primalResult, tangentLam) <- fromPair result
    return $ WithTangent (PairVal primalResult sFinal) do
      sLin' <- sLin
      tanEffectLam <- applyLinToTangents $ sink tangentLam
      liftM Var $ emit $ Hof $ RunState sLin' tanEffectLam
  RunWriter bm lam -> do
    -- TODO: check it's actually the 0/+ monoid (or should we just build that in?)
    ComposeE bm' <- substM (ComposeE bm)
    lam' <- linearizeEffectFun Writer lam
    (result, wFinal) <- fromPair =<< liftM Var (emit $ Hof $ RunWriter bm' lam')
    (primalResult, tangentLam) <- fromPair result
    return $ WithTangent (PairVal primalResult wFinal) do
      ComposeE bm'' <- sinkM $ ComposeE bm'
      tanEffectLam <- applyLinToTangents $ sink tangentLam
      liftM Var $ emit $ Hof $ RunWriter bm'' tanEffectLam
  RunIO (Lam (LamExpr b@(LamBinder _ _ _ effs) body)) -> do
    effs' <- substM $ ignoreHoistFailure $ hoist b effs
    -- TODO: consider the possibility of other effects here besides IO
    ioLam <- buildLam noHint PlainArrow UnitTy effs' \v -> do
      WithTangent primalResult tangentFun <- extendSubst (b@>v) $ linearizeBlock body
      lam <- tangentFunAsLambda tangentFun
      return $ PairVal primalResult lam
    result <- liftM Var $ emit $ Hof $ RunIO ioLam
    (ans, linLam) <- fromPair result
    return $ WithTangent ans $ applyLinToTangents (sink linLam)
  _ -> error $ "not implemented: " ++ pprint hof

-- takes an effect function, of type `(h:Type) -> Ref h s -> a``
-- and augments it with the tangent lambda, so instead of returning `a`, it returns:
-- `[tangent args] -> (a & ((h':Type) -> (ref':Ref h' (T s)) -> T a))`
linearizeEffectFun :: RWS -> Atom i -> PrimalM i o (Atom o)
linearizeEffectFun rws ~(Lam lam) = do
  BinaryLamExpr hB refB body <- return lam
  referentTy <- getReferentTy =<< substM (EmptyAbs $ PairB hB refB)
  buildEffLam rws (getNameHint refB) referentTy \h ref -> withTangentFunAsLambda do
    extendActiveSubst hB h $ extendActiveSubst refB ref $
      extendActiveEffs (RWSEffect rws (Just h)) do
        WithTangent p tangentFun <- linearizeBlock body
        return $ WithTangent p do
          tt <- tangentType $ sink referentTy
          buildEffLam rws (getNameHint refB) tt \h' ref' ->
            extendTangentArgs h' $ extendTangentArgs ref' $
              tangentFun

withT :: PrimalM i o (e1 o)
      -> (forall o'. (Emits o', DExt o o') => TangentM o' (e2 o'))
      -> PrimalM i o (WithTangent o e1 e2)
withT p t = do
  p' <- p
  return $ WithTangent p' t

withZeroT :: PrimalM i o (Atom o)
          -> PrimalM i o (WithTangent o Atom Atom)
withZeroT p = do
  p' <- p
  return $ WithTangent p' do
    pTy <- getType $ sink p'
    zeroAt =<< tangentType pTy

notImplemented :: HasCallStack => a
notImplemented = error "Not implemented"

-- === instances ===

instance GenericE ActivePrimals where
  type RepE ActivePrimals = PairE (ListE AtomName) EffectRow
  fromE (ActivePrimals vs effs) = ListE vs `PairE` effs
  {-# INLINE fromE #-}
  toE   (ListE vs `PairE` effs) = ActivePrimals vs effs
  {-# INLINE toE #-}

instance SinkableE   ActivePrimals
instance HoistableE  ActivePrimals
instance AlphaEqE    ActivePrimals
instance SubstE Name ActivePrimals

instance GenericE TangentArgs where
  type RepE TangentArgs = ListE AtomName
  fromE (TangentArgs vs) = ListE vs
  {-# INLINE fromE #-}
  toE   (ListE vs) = TangentArgs vs
  {-# INLINE toE #-}

instance SinkableE   TangentArgs
instance HoistableE  TangentArgs
instance AlphaEqE    TangentArgs
instance SubstE Name TangentArgs
