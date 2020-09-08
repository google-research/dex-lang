-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}

module Autodiff (linearize, transposeMap) where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader

import Array
import Type
import Env
import Syntax
import Cat
import PPrint
import Embed
import Util (bindM2)
import GHC.Stack

-- === linearization ===

-- `DerivWrt` holds the (out-expr) variables that we're differentiating with
-- respect to (including refs but not regions).
data DerivWrt = DerivWrt { activeVars :: Env Type, _activeEffs :: [Effect] }
-- `Tangents` holds the tangent values and the region variables that are
-- arguments to the linearized function.
data TangentEnv = TangentEnv { tangentVals :: SubstEnv, activeRefs :: [Name] }

type PrimalM  = ReaderT DerivWrt   Embed
type TangentM = ReaderT TangentEnv Embed
newtype LinA a = LinA { runLinA :: PrimalM (a, TangentM a) }

linearize :: Scope -> Atom -> Atom
linearize scope ~(Lam (Abs b (_, block))) = fst $ flip runEmbed scope $ do
  buildLam b PureArrow $ \x@(Var v) -> do
    (y, yt) <- flip runReaderT (DerivWrt (varAsEnv v) []) $ runLinA $ linearizeBlock (b@>x) block
    -- TODO: check linearity
    fLin <- buildLam b LinArrow $ \xt -> runReaderT yt $ TangentEnv (v @> xt) []
    fLinChecked <- checkEmbed fLin
    return $ PairVal y fLinChecked

linearizeBlock :: SubstEnv -> Block -> LinA Atom
linearizeBlock env (Block decls result) = case decls of
  Empty -> linearizeExpr env result
  Nest (Let _ b bound) rest -> LinA $ do
    -- TODO: Handle the discrete and inactive case specially.
    (x, boundLin) <- runLinA $ linearizeExpr env bound
    ~x'@(Var v) <- emit $ Atom x
    (ans, bodyLin) <- extendWrt v [] $ runLinA $ linearizeBlock (env <> b@>x') body
    return (ans, do t <- boundLin; extendTangentEnv (v @> t) [] bodyLin)
    where body = Block rest result
  Nest (Unpack _ _) _ -> notImplemented

linearizeExpr :: SubstEnv -> Expr -> LinA Atom
linearizeExpr env expr = case expr of
  Hof  e -> linearizeHof env e
  _ -> LinA $ do
    expr' <- substEmbed env expr
    runLinA $ case expr' of
      App x i | isTabTy (getType x) -> liftA (flip App i) (linearizeAtom x) `bindLin` emit
      Op   e     -> linearizeOp   e
      Atom e     -> linearizeAtom e
      Case _ _ _ -> notImplemented
      App _ _    -> error "Unexpected non-table application"
      Hof _      -> error "Hofs should be handled above"

linearizeOp :: Op -> LinA Atom
linearizeOp op = case op of
  ScalarUnOp  uop x       -> linearizeUnOp  uop x
  ScalarBinOp bop x y     -> linearizeBinOp bop x y
  PrimEffect refArg m ->
    liftA2 PrimEffect (la refArg)
      (case m of
         MAsk    -> pure MAsk
         MTell x -> liftA MTell $ la x
         MGet    -> pure MGet
         MPut  x -> liftA MPut $ la x) `bindLin` emitOp
  Fst x                  -> (Fst <$> la x) `bindLin` emitOp
  Snd x                  -> (Snd <$> la x) `bindLin` emitOp
  IndexRef ref i         -> (IndexRef <$> la ref <*> pure i) `bindLin` emitOp
  FstRef   ref           -> (FstRef   <$> la ref           ) `bindLin` emitOp
  SndRef   ref           -> (SndRef   <$> la ref           ) `bindLin` emitOp
  Select p t f           -> (Select p <$> la t   <*> la f  ) `bindLin` emitOp
  ArrayLoad _            -> emitWithZero -- XXX: This assumes that arrays are always constants
  TabCon ty xs           -> liftA (TabCon ty) (traverse la xs) `bindLin` emitOp
  ArrayOffset _ _ _      -> emitDiscrete
  Inject _               -> emitDiscrete
  SliceOffset _ _        -> emitDiscrete
  SliceCurry  _ _        -> emitDiscrete
  VectorBinOp _ _ _      -> notImplemented
  VectorPack  vals       -> (VectorPack  <$> traverse la vals) `bindLin` emitOp
  VectorIndex v i        -> (VectorIndex <$> la v <*> pure i ) `bindLin` emitOp
  IntAsIndex _ _         -> emitDiscrete
  IndexAsInt _           -> emitDiscrete
  IdxSetSize _           -> emitDiscrete
  ThrowError _           -> emitWithZero
  CastOp t v             -> (CastOp t <$> la v) `bindLin` emitOp
  RecordCons   vs r      -> (RecordCons      <$> traverse la vs <*> la r) `bindLin` emitOp
  RecordSplit  vs r      -> (RecordSplit     <$> traverse la vs <*> la r) `bindLin` emitOp
  VariantLift  ts v      -> (VariantLift  ts <$> la v) `bindLin` emitOp
  VariantSplit ts v      -> (VariantSplit ts <$> la v) `bindLin` emitOp
  FFICall _ _ _          -> error $ "Can't differentiate through an FFI call"
  where
    emitDiscrete = if hasDiscreteType (Op op)
      then LinA $ withZeroTangent <$> emitOp op
      else error $ "Op expected to have a discrete result: " ++ pprint op
    la = linearizeAtom
    emitWithZero :: LinA Atom
    emitWithZero = LinA $ withZeroTangent <$> emitOp op

emitUnOp :: MonadEmbed m => UnOp -> Atom -> m Atom
emitUnOp op x = emitOp $ ScalarUnOp op x

linearizeUnOp :: UnOp -> Atom -> LinA Atom
linearizeUnOp op x' = LinA $ do
  (x, tx) <- runLinA $ linearizeAtom x'
  case op of
    Exp    -> notImplemented
    Exp2   -> notImplemented
    Log    -> notImplemented
    Log2   -> notImplemented
    Log10  -> notImplemented
    Log1p  -> notImplemented
    Sin    -> emitUnOp Sin x <$$> (,emitUnOp Cos =<< tx)
    Cos    -> emitUnOp Cos x <$$> (,neg =<< emitUnOp Sin =<< tx)
    Tan    -> notImplemented
    Sqrt   -> notImplemented
    Floor  -> withZeroTangent <$> emitUnOp Floor x
    Ceil   -> withZeroTangent <$> emitUnOp Ceil  x
    Round  -> withZeroTangent <$> emitUnOp Round x
    LGamma -> notImplemented
    FNeg   -> neg x <$$> (,neg =<< tx)
    BNot   -> emitDiscrete
  where
    (<$$>) = flip (<$>)
    emitDiscrete = if hasDiscreteType (Op $ ScalarUnOp op x')
      then withZeroTangent <$> emitOp (ScalarUnOp op x')
      else error $ "Op expected to have a discrete result: " ++ show op

linearizeBinOp :: BinOp -> Atom -> Atom -> LinA Atom
linearizeBinOp op x' y' = LinA $ do
  (x, tx) <- runLinA $ linearizeAtom x'
  (y, ty) <- runLinA $ linearizeAtom y'
  case op of
    IAdd   -> emitDiscrete
    ISub   -> emitDiscrete
    IMul   -> emitDiscrete
    IDiv   -> emitDiscrete
    IRem   -> emitDiscrete
    ICmp _ -> emitDiscrete
    FAdd   -> add x y  <$$> (,bindM2 add tx ty)
    FSub   -> sub x y  <$$> (,bindM2 sub tx ty)
    FMul   -> mul x y  <$$> (,bindM2 add (bindM2 mul (pure x) ty) (bindM2 mul tx (pure y)))
    FDiv   -> div' x y <$$>
        (,do
             tx' <- bindM2 div' tx (pure y)
             ty' <- bindM2 div' (bindM2 mul (pure x) ty) (mul y y)
             sub tx' ty')
    FPow   -> (emitOp $ ScalarBinOp FPow x y) <$$>
        (,do
             c <- fpow x =<< sub y (1.0 `fLitLike` y)
             tx' <- bindM2 mul tx (pure y)
             ty' <- bindM2 mul (bindM2 mul (pure x) ty) (flog x)
             mul c =<< add tx' ty')
    FCmp _ -> emitDiscrete
    BAnd   -> emitDiscrete
    BOr    -> emitDiscrete
  where
    (<$$>) = flip (<$>)
    emitDiscrete = if hasDiscreteType (Op $ ScalarBinOp op x' y')
      then withZeroTangent <$> emitOp (ScalarBinOp op x' y')
      else error $ "Op expected to have a discrete result: " ++ show op

-- Here, we want to take advantage of simplification's automatic desugaring of
-- Hofs that return functions into Hofs that return residual values, so the where
-- part implements functions that convert the TangentM actions into lambdas that
-- abstract over the whole tangent state.
linearizeHof :: SubstEnv -> Hof -> LinA Atom
linearizeHof env hof = case hof of
  For d ~(LamVal i body) -> LinA $ do
    i' <- mapM (substEmbed env) i
    (ans, linTab) <- (unzipTab =<<) $ buildFor d i' $ \i'' ->
       tangentFunAsLambda $ linearizeBlock (env <> i@>i'') body
    return (ans, buildFor d i' $ app linTab >=> applyLinToTangents)
  Tile _ _ _        -> notImplemented
  RunWriter     lam -> linearizeEff Nothing    lam True  (const RunWriter) (emitRunWriter "r") Writer
  RunReader val lam -> linearizeEff (Just val) lam False RunReader         (emitRunReader "r") Reader
  RunState  val lam -> linearizeEff (Just val) lam True  RunState          (emitRunState  "r") State
  -- TODO: Consider providing an upper bound for the number of while iterations as a hint.
  --       In the current form the best we can do is try to use some dynamically growing lists,
  --       but that won't work on the GPU.
  While _ _   -> notImplemented
  Linearize _ -> error "Unexpected linearization"
  Transpose _ -> error "Unexpected transposition"
  where
    linearizeEff maybeInit lam hasResult hofMaker emitter eff = LinA $ do
      (valHofMaker, maybeLinInit) <- case maybeInit of
          Just val -> do
            (val', linVal) <- runLinA <$> linearizeAtom =<< substEmbed env val
            return (hofMaker val', Just linVal)
          Nothing -> return (hofMaker undefined, Nothing)
      (lam', ref)    <- linearizeEffectFun eff lam
      (ans, linBody) <- case hasResult of
          True -> do
            (ansLin, w)    <- fromPair =<< emit (Hof $ valHofMaker lam')
            (ans, linBody) <- fromPair ansLin
            return (PairVal ans w, linBody)
          False -> fromPair =<< emit (Hof $ valHofMaker lam')
      let lin = do
                  valEmitter <- case maybeLinInit of
                    Just linVal -> emitter <$> linVal
                    Nothing     -> do
                      let (BinaryFunTy _ b _ _) = getType lam'
                      let RefTy _ wTy = binderType b
                      return $ emitter wTy
                  valEmitter $ \ref'@(Var (_:> RefTy (Var (h:>_)) _)) -> do
                      extendTangentEnv (ref @> ref') [h] $ applyLinToTangents linBody
      return (ans, lin)

    -- Abstract the tangent action as a lambda.
    -- TODO: curried linear functions somehow?
    tangentFunAsLambda :: LinA Atom -> PrimalM Atom
    tangentFunAsLambda m = do
      (ans, tanFun) <- runLinA m
      DerivWrt activeVars effs <- ask
      let hs = map (Bind . (:>TyKind) . snd) effs
      liftM (PairVal ans) $ lift $ do
        buildNestedLam hs $ \hVals -> do
          let hVarNames = map (\(Var (v:>_)) -> v) hVals
          let effs' = zipWith (\(effName, _) v -> (effName, v)) effs hVarNames
          -- want to use tangents here, not the original binders
          let regionMap = newEnv (map ((:>()) . snd) effs) hVals
          -- TODO: Only bind tangents for free variables?
          let activeVarBinders = map (Bind . fmap (tangentRefRegion regionMap)) $ envAsVars activeVars
          buildNestedLam activeVarBinders $ \activeVarArgs ->
            buildLam (Ignore UnitTy) (PlainArrow $ EffectRow effs' Nothing) $ \_ ->
              runReaderT tanFun $ TangentEnv (newEnv (envNames activeVars) activeVarArgs) hVarNames

    -- This doesn't work if we have references inside pairs, tables etc.
    -- TODO: something more general and cleaner.
    tangentRefRegion :: Env Atom -> Type -> Type
    tangentRefRegion regEnv ty = case ty of
      RefTy ~(Var h) a -> RefTy (regEnv ! h) $ tangentType a
      _ -> tangentType ty

    -- Inverse of tangentFunAsLambda. Should be used inside a returned tangent action.
    applyLinToTangents :: Atom -> TangentM Atom
    applyLinToTangents f = do
      TangentEnv{..} <- ask
      let hs' = map (Var . (:>TyKind)) activeRefs
      let tangents = fmap snd $ envPairs $ tangentVals
      let args = hs' ++ tangents ++ [UnitVal]
      naryApp f args

    linearizeEffectFun :: EffectName -> Atom -> PrimalM (Atom, Var)
    linearizeEffectFun effName ~(BinaryFunVal h ref eff body) = do
      h' <- mapM (substEmbed env) h
      buildLamAux h' (const $ return PureArrow) $ \h''@(Var hVar) -> do
        let env' = env <> h@>h''
        eff' <- substEmbed env' eff
        ref' <- mapM (substEmbed env') ref
        buildLamAux ref' (const $ return $ PlainArrow eff') $ \ref''@(Var refVar) ->
          extendWrt refVar [(effName, varName hVar)] $
            (,refVar) <$> (tangentFunAsLambda $ linearizeBlock (env' <> ref@>ref'') body)

linearizePrimCon :: Con -> LinA Atom
linearizePrimCon con = case con of
  Lit _                 -> emitWithZero
  CharCon _             -> emitWithZero
  ArrayLit _ _          -> emitWithZero
  AnyValue _            -> emitWithZero
  PairCon x y           -> PairVal <$> linearizeAtom x <*> linearizeAtom y
  UnitCon               -> emitWithZero
  Coerce _ _            -> emitWithZero -- XXX: This assumes that coercions are only used for discrete types
  SumAsProd ty tg elems -> Con . SumAsProd ty tg <$> traverse (traverse linearizeAtom) elems
  ClassDictHole _ _ -> error "Unexpected ClassDictHole"
  where emitWithZero = LinA $ return $ withZeroTangent $ Con con

linearizeAtom :: Atom -> LinA Atom
linearizeAtom atom = case atom of
  Var v -> LinA $ do
    isActive <- asks ((v `isin`) . activeVars)
    if isActive
      then return $ (atom, asks $ (!v) . tangentVals)
      else return $ withZeroTangent atom
  Con con -> linearizePrimCon con
  Lam (Abs i (TabArrow, body)) -> LinA $ do
    wrt <- ask
    return (atom, buildLam i TabArrow $ \i' ->
                    rematPrimal wrt $ linearizeBlock (i@>i') body)
  Lam _ -> error "Unexpected non-table lambda"
  DataCon ty params t elems -> DataCon ty params t <$> traverse linearizeAtom elems
  Record elems    -> Record <$> traverse linearizeAtom elems
  Variant t l i e -> Variant t l i <$> linearizeAtom e
  TypeCon _ _     -> emitWithZero
  LabeledRow _    -> emitWithZero
  RecordTy _      -> emitWithZero
  VariantTy _     -> emitWithZero
  Pi _            -> emitWithZero
  TC _            -> emitWithZero
  Eff _           -> emitWithZero
  where
    emitWithZero = LinA $ return $ withZeroTangent atom
    rematPrimal wrt m = do
      (_, lin) <- lift $ runReaderT (runLinA m) wrt
      lin

withZeroTangent :: Atom -> (Atom, TangentM Atom)
withZeroTangent x = (x, return $ zeroAt (tangentType (getType x)))

zeroAt :: Type -> Atom
zeroAt ty = case ty of
  BaseTy bt  -> Con $ Lit $ zeroLit bt
  TabTy i a  -> TabValA i $ zeroAt a
  UnitTy     -> UnitVal
  PairTy a b -> PairVal (zeroAt a) (zeroAt b)
  _          -> unreachable
  where
    unreachable = error $ "Missing zero case for a tangent type: " ++ pprint ty
    zeroLit bt = case bt of
      Scalar Float64Type -> Float64Lit 0.0
      Scalar Float32Type -> Float32Lit 0.0
      Vector st          -> VecLit $ replicate vectorWidth $ zeroLit $ Scalar st
      _                  -> unreachable

tangentType :: Type -> Type
tangentType ty = case ty of
  RecordTy _   -> notImplemented
  TypeCon  _ _ -> notImplemented
  TabTy n a -> TabTy n (tangentType a)
  TC con    -> case con of
    BaseType (Scalar Float64Type) -> TC con
    BaseType (Scalar Float32Type) -> TC con
    BaseType (Vector Float64Type) -> TC con
    BaseType (Vector Float32Type) -> TC con
    BaseType   _                  -> UnitTy
    CharType                      -> UnitTy
    IntRange   _ _                -> UnitTy
    IndexRange _ _ _              -> UnitTy
    IndexSlice _ _                -> UnitTy
    UnitType                      -> UnitTy
    PairType a b                  -> PairTy (tangentType a) (tangentType b)
    -- XXX: This assumes that arrays are always constants.
    ArrayType _                   -> UnitTy
    _ -> unsupported
  _ -> unsupported
  where unsupported = error $ "Can't differentiate wrt type " ++ pprint ty

-- TODO: consider effects!
hasDiscreteType :: HasType e => e -> Bool
hasDiscreteType expr = isSingletonType tangentTy
  where tangentTy = tangentType $ getType expr

bindLin :: LinA a -> (a -> Embed b) -> LinA b
bindLin (LinA m) f = LinA $ do
  (e, t) <- m
  x <- lift $ f e
  return (x, t >>= (lift . f))

instance Functor LinA where
  fmap = liftA

instance Applicative LinA where
  pure x = LinA $ return (x, return x)
  liftA2 f (LinA m1) (LinA m2) = LinA $ do
    (x1, t1) <- m1
    (x2, t2) <- m2
    return (f x1 x2, liftM2 f t1 t2)

extendWrt :: Var -> [Effect] -> PrimalM a -> PrimalM a
extendWrt v effs m = local update m
  where update (DerivWrt scope effs') = DerivWrt (scope <> varAsEnv v) (effs' <> effs)

extendTangentEnv :: SubstEnv -> [Name] -> TangentM a -> TangentM a
extendTangentEnv tv effs m = local update m
  where update (TangentEnv tv' effs') = TangentEnv (tv' <> tv) (effs' <> effs)

notImplemented :: HasCallStack => a
notImplemented = error "Not implemented"

-- -- === transposition ===

type LinVars = Env Atom
type TransposeM a = ReaderT (LinVars, SubstEnv) Embed a

transposeMap :: Scope -> Atom -> Atom
transposeMap scope ~(Lam (Abs b (_, expr))) = fst $ flip runEmbed scope $ do
  buildLam (Bind $ "ct" :> getType expr) LinArrow $ \ct -> do
    flip runReaderT mempty $ withLinVar b $ transposeBlock expr ct

transposeBlock :: Block -> Atom -> TransposeM ()
transposeBlock (Block decls result) ct = case decls of
  Empty -> transposeExpr result ct
  Nest (Let _ b bound) rest -> do
    -- let (eff, _) = getEffType bound
    -- linEff <- isLinEff eff
    let linEff = not $ isPure bound
    lin <- isLin bound
    if lin || linEff
      then do
        ct' <- withLinVar b $ transposeBlock body ct
        transposeExpr bound ct'
      else do
        bound' <- substTranspose bound
        x <- withNameHint b $ emit bound'
        extendR (asSnd (b@>x)) $ transposeBlock body ct
    where body = Block rest result
  Nest (Unpack _ _) _ -> notImplemented

transposeExpr :: Expr -> Atom -> TransposeM ()
transposeExpr expr ct = case expr of
  App x i -> case getType x of
    TabTy _ _ -> do
      i' <- substTranspose i
      ref <- linAtomRef x
      ref' <- emitOp $ IndexRef ref i'
      emitCTToRef ref' ct
    _ -> error $ "shouldn't have non-table app left"
  Hof hof    -> transposeHof hof ct
  Op op      -> transposeOp op ct
  Atom atom  -> transposeAtom atom ct
  Case _ _ _ -> notImplemented

transposeOp :: Op -> Atom -> TransposeM ()
transposeOp op ct = case op of
  Fst x -> do
    ref <- linAtomRef x
    ref' <- emitOp $ FstRef ref
    emitCTToRef ref' ct
  Snd x -> do
    ref <- linAtomRef x
    ref' <- emitOp $ SndRef ref
    emitCTToRef ref' ct
  ScalarUnOp FNeg x -> do
    ctNeg <- neg ct
    transposeAtom x ctNeg
  ScalarBinOp FAdd x y -> do
    transposeAtom x ct
    transposeAtom y ct
  ScalarBinOp FSub x y -> do
    ctNeg <- neg ct
    transposeAtom x ct
    transposeAtom y ctNeg
  ScalarBinOp FMul x y -> do
    xLin <- isLin x
    if xLin
      then do
        y' <- substTranspose y
        ct' <- mul ct y'
        transposeAtom x ct'
      else do
        x' <- substTranspose x
        ct' <- mul ct x'
        transposeAtom y ct'
  ScalarBinOp FDiv x y -> do
    y' <- substTranspose y
    ct' <- div' ct y'
    transposeAtom x ct'
  PrimEffect refArg m -> do
    refArg' <- substTranspose refArg
    case m of
      MAsk -> void $ emitOp $ PrimEffect refArg' (MTell ct)
      MTell x -> do
       ct' <- emitOp $ PrimEffect refArg' MAsk
       transposeAtom x ct'
      _ -> error "Not implemented"
  _ -> error $ "not implemented: transposition for: " ++ pprint op

linAtomRef :: Atom -> TransposeM Atom
linAtomRef (Var x) = do
  linVars <- asks fst
  case envLookup linVars x of
    Just ref -> return ref
    _ -> error "Not a linear var"
linAtomRef _ = error "Not a linear var"

transposeHof :: Hof -> Atom -> TransposeM ()
transposeHof hof ct = case hof of
  For d ~(Lam (Abs b (_, body))) ->
    void $ buildFor (flipDir d) b $ \i -> do
      ct' <- tabGet ct i
      extendR (asSnd (b@>i)) $ transposeBlock body ct'
      return UnitVal
  RunReader r ~(BinaryFunVal _ b _ body) -> do
    (_, ctr) <- (fromPair =<<) $ emitRunWriter "w" (getType r) $ \ref -> do
      extendR (asSnd (b@>ref)) $ transposeBlock body ct
      return UnitVal
    transposeAtom r ctr
  RunWriter ~(BinaryFunVal _ b _ body) -> do
    (ctBody, ctEff) <- fromPair ct
    void $ emitRunReader "r" ctEff $ \ref -> do
      extendR (asSnd (b@>ref)) $ transposeBlock body ctBody
      return UnitVal
  RunState _ _ -> notImplemented
  Tile   _ _ _ -> notImplemented
  While    _ _ -> notImplemented
  Linearize  _ -> error "Unexpected linearization"
  Transpose  _ -> error "Unexpected transposition"


transposeCon :: Con -> Atom -> TransposeM ()
transposeCon con _ | isSingletonType (getType (Con con)) = return ()
transposeCon con ct = case con of
  Lit _ -> return ()
  PairCon x y -> do
    getFst ct >>= transposeAtom x
    getSnd ct >>= transposeAtom y
  _ -> error $ "not implemented: transposition for: " ++ pprint con

transposeAtom :: Atom -> Atom -> TransposeM ()
transposeAtom atom ct = case atom of
  Var v -> emitCT v ct
  Con con -> transposeCon con ct
  _ -> error $ "Can't transpose: " ++ pprint atom

freeLinVars :: HasVars a => a -> TransposeM [Var]
freeLinVars x = do
  linVs <- asks fst
  return $ bindingsAsVars $ envIntersect linVs (freeVars x)

isLin :: HasVars a => a -> TransposeM Bool
isLin x = liftM (not . null) $ freeLinVars x

-- TODO: allow nonlinear effects
_isLinEff :: EffectRow -> TransposeM Bool
_isLinEff = undefined
-- isLinEff ~(Effect row _) = return $ not $ null $ toList row

emitCT :: Var -> Atom -> TransposeM ()
emitCT v ct = do
  linVars <- asks fst
  case envLookup linVars v of
    Just ref -> emitCTToRef ref ct
    _ -> return ()

emitCTToRef :: Atom -> Atom -> TransposeM ()
emitCTToRef ref ct = void $ emitOp $ PrimEffect ref (MTell ct)

substTranspose :: Subst a => a -> TransposeM a
substTranspose x = do
  env <- asks snd
  scope <- getScope
  return $ subst (env, scope) x

withLinVar :: Binder -> TransposeM () -> TransposeM Atom
withLinVar b body = case
  singletonTypeVal (binderType b) of
    Nothing -> do
      ans <- emitRunWriter "ref" (binderType b) $ \ref -> do
        extendR (asFst (b@>ref)) (body >> return UnitVal)
      getSnd ans
    Just x -> body >> return x  -- optimization to avoid accumulating into unit

flipDir :: Direction -> Direction
flipDir Fwd = Rev
flipDir Rev = Fwd
