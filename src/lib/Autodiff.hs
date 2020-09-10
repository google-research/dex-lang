-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}

module Autodiff (linearize, transpose) where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import qualified Data.Set as S

import Array
import Type
import Env
import Syntax
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
  Nest (Let _ b expr) rest -> LinA $ do
    -- Don't linearize expressions with no free active variables.
    -- Technically, we could do this and later run the code through a simplification
    -- pass that would eliminate a bunch of multiplications with zeros, but this seems
    -- simpler to do for now.
    freeAtoms <- traverse (substEmbed env . Var) $ bindingsAsVars $ freeVars expr
    varsAreActive <- traverse isActive $ bindingsAsVars $ freeVars freeAtoms
    if any id varsAreActive
      then do
        (x, boundLin) <- runLinA $ linearizeExpr env expr
        ~x'@(Var v) <- emit $ Atom x
        (ans, bodyLin) <- extendWrt v [] $ runLinA $ linearizeBlock (env <> b@>x') body
        return (ans, do t <- boundLin; extendTangentEnv (v @> t) [] bodyLin)
      else do
        x' <- emit =<< substEmbed env expr
        runLinA $ linearizeBlock (env <> b@>x') body
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
  TabCon ty xs           -> (TabCon ty <$> traverse la xs) `bindLin` emitOp
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
    emitDiscrete = if isTrivialForAD (Op op)
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
    emitDiscrete = if isTrivialForAD (Op $ ScalarUnOp op x')
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
    emitDiscrete = if isTrivialForAD (Op $ ScalarBinOp op x' y')
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
    active <- isActive v
    if active
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

isTrivialForAD :: Expr -> Bool
isTrivialForAD expr = isSingletonType tangentTy && exprEffs expr == mempty
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

isActive :: Var -> PrimalM Bool
isActive v = asks ((v `isin`) . activeVars)

extendWrt :: Var -> [Effect] -> PrimalM a -> PrimalM a
extendWrt v effs m = local update m
  where update (DerivWrt scope effs') = DerivWrt (scope <> varAsEnv v) (effs' <> effs)

extendTangentEnv :: SubstEnv -> [Name] -> TangentM a -> TangentM a
extendTangentEnv tv effs m = local update m
  where update (TangentEnv tv' effs') = TangentEnv (tv' <> tv) (effs' <> effs)

notImplemented :: HasCallStack => a
notImplemented = error "Not implemented"

-- -- === transposition ===

data TransposeEnv = TransposeEnv { linRefs        :: Env Atom
                                 , linRegions     :: Env ()
                                 , transposeSubst :: SubstEnv
                                 }

instance Semigroup TransposeEnv where
  (TransposeEnv x y z) <> (TransposeEnv x' y' z') = TransposeEnv (x <> x') (y <> y') (z <> z')

instance Monoid TransposeEnv where
  mempty = TransposeEnv mempty mempty mempty

type TransposeM a = ReaderT TransposeEnv Embed a

transpose :: Scope -> Atom -> Atom
transpose scope ~(Lam (Abs b (_, expr))) = fst $ flip runEmbed scope $ do
  buildLam (Bind $ "ct" :> getType expr) LinArrow $ \ct -> do
    flip runReaderT mempty $ withLinVar b $ transposeBlock expr ct

transposeBlock :: Block -> Atom -> TransposeM ()
transposeBlock (Block decls result) ct = case decls of
  Empty -> transposeExpr result ct
  Nest (Let _ b expr) rest -> do
    isLinearExpr <- (||) <$> isLinEff (exprEffs expr) <*> isLin expr
    if isLinearExpr
      then do
        ct' <- withLinVar b $ transposeBlock body ct
        transposeExpr expr ct'
      else do
        expr' <- substTranspose expr
        x <- withNameHint b $ emit expr'
        localSubst (b@>x) $ transposeBlock body ct
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
  Fst x                 -> flip emitCTToRef ct =<< emitOp . FstRef =<< linAtomRef x
  Snd x                 -> flip emitCTToRef ct =<< emitOp . SndRef =<< linAtomRef x
  ScalarUnOp  FNeg x    -> transposeAtom x =<< neg ct
  ScalarUnOp  _    _    -> notLinear
  ScalarBinOp FAdd x y  -> transposeAtom x ct >> transposeAtom y ct
  ScalarBinOp FSub x y  -> transposeAtom x ct >> (transposeAtom y =<< neg ct)
  ScalarBinOp FMul x y  -> do
    xLin <- isLin x
    if xLin
      then transposeAtom x =<< mul ct =<< substTranspose y
      else transposeAtom y =<< mul ct =<< substTranspose x
  ScalarBinOp FDiv x y  -> transposeAtom x =<< div' ct =<< substTranspose y
  ScalarBinOp _    _ _  -> notLinear
  PrimEffect refArg m   -> do
    refArg' <- substTranspose refArg
    case m of
      MAsk    -> void $ emitOp $ PrimEffect refArg' (MTell ct)
      MTell x -> do
       ct' <- emitOp $ PrimEffect refArg' MAsk
       transposeAtom x ct'
      MGet    -> notImplemented
      MPut  _ -> notImplemented
  IndexRef     _ _      -> notImplemented
  FstRef       _        -> notImplemented
  SndRef       _        -> notImplemented
  Select       _ _ _    -> notImplemented
  VectorBinOp  _ _ _    -> notImplemented
  VectorPack   _        -> notImplemented
  VectorIndex  _ _      -> notImplemented
  CastOp       _ _      -> notImplemented
  RecordCons   _ _      -> notImplemented
  RecordSplit  _ _      -> notImplemented
  VariantLift  _ _      -> notImplemented
  VariantSplit _ _      -> notImplemented
  TabCon       _ _      -> notImplemented
  ArrayLoad    _        -> notLinear
  ArrayOffset  _ _ _    -> notLinear
  Inject       _        -> notLinear
  SliceOffset  _ _      -> notLinear
  SliceCurry   _ _      -> notLinear
  IntAsIndex   _ _      -> notLinear
  IndexAsInt   _        -> notLinear
  IdxSetSize   _        -> notLinear
  ThrowError   _        -> notLinear
  FFICall      _ _ _    -> notLinear
  where
    -- Both nonlinear operations and operations on discrete types, where linearity doesn't make sense
    notLinear = error $ "Can't transpose a non-linear operation: " ++ pprint op

linAtomRef :: Atom -> TransposeM Atom
linAtomRef (Var x) = do
  refs <- asks linRefs
  case envLookup refs x of
    Just ref -> return ref
    _ -> error $ "Not a linear var" ++ pprint (Var x)
linAtomRef a = error $ "Not a linear var" ++ pprint a

transposeHof :: Hof -> Atom -> TransposeM ()
transposeHof hof ct = case hof of
  For d ~(Lam (Abs b (_, body))) ->
    void $ buildFor (flipDir d) b $ \i -> do
      ct' <- tabGet ct i
      localSubst (b@>i) $ transposeBlock body ct'
      return UnitVal
    where flipDir dir = case dir of Fwd -> Rev; Rev -> Fwd
  RunReader r ~(BinaryFunVal (Bind (h:>_)) b _ body) -> do
    (_, ctr) <- (fromPair =<<) $ emitRunWriter "w" (getType r) $ \ref -> do
      localLinRegion h $ localSubst (b@>ref) $ transposeBlock body ct
      return UnitVal
    transposeAtom r ctr
  RunWriter ~(BinaryFunVal (Bind (h:>_)) b _ body) -> do
    (ctBody, ctEff) <- fromPair ct
    void $ emitRunReader "r" ctEff $ \ref -> do
      localLinRegion h $ localSubst (b@>ref) $ transposeBlock body ctBody
      return UnitVal
  RunState _ _ -> notImplemented
  Tile   _ _ _ -> notImplemented
  While    _ _ -> notImplemented
  Linearize  _ -> error "Unexpected linearization"
  Transpose  _ -> error "Unexpected transposition"

transposeAtom :: Atom -> Atom -> TransposeM ()
transposeAtom atom ct = case atom of
  Var v -> do
    refs <- asks linRefs
    case envLookup refs v of
      Just ref -> emitCTToRef ref ct
      _ -> return ()
  Con con         -> transposeCon con ct
  TabVal _ _      -> notImplemented
  Lam _           -> notTangent
  DataCon _ _ _ _ -> notImplemented
  Record  _       -> notImplemented
  Variant _ _ _ _ -> notImplemented
  TypeCon _ _     -> notTangent
  LabeledRow _    -> notTangent
  RecordTy _      -> notTangent
  VariantTy _     -> notTangent
  Pi _            -> notTangent
  TC _            -> notTangent
  Eff _           -> notTangent
  where notTangent = error $ "Not a tangent atom: " ++ pprint atom

transposeCon :: Con -> Atom -> TransposeM ()
transposeCon con ct = case con of
  Lit _             -> return ()
  UnitCon           -> return ()
  PairCon x y       -> do
    getFst ct >>= transposeAtom x
    getSnd ct >>= transposeAtom y
  SumAsProd _ _ _   -> notImplemented
  CharCon _         -> notTangent
  ArrayLit _ _      -> notTangent
  AnyValue _        -> notTangent
  Coerce _ _        -> notTangent  -- Technically this depends on the legal coercions
  ClassDictHole _ _ -> notTangent
  where notTangent = error $ "Not a tangent atom: " ++ pprint (Con con)

freeLinVars :: HasVars a => a -> TransposeM [Var]
freeLinVars x = do
  refs <- asks linRefs
  return $ bindingsAsVars $ envIntersect refs (freeVars x)

isLin :: HasVars a => a -> TransposeM Bool
isLin x = not . null <$> freeLinVars x

isLinEff :: EffectSummary -> TransposeM Bool
isLinEff effs = do
  regions <- asks linRegions
  return $ not $ null $ effRegions `envIntersect` regions
  where effRegions = newEnv (S.map snd effs) (repeat ())

emitCTToRef :: Atom -> Atom -> TransposeM ()
emitCTToRef ref ct = void $ emitOp $ PrimEffect ref (MTell ct)

substTranspose :: Subst a => a -> TransposeM a
substTranspose x = do
  env <- asks transposeSubst
  scope <- getScope
  return $ subst (env, scope) x

withLinVar :: Binder -> TransposeM () -> TransposeM Atom
withLinVar b body = case
  singletonTypeVal (binderType b) of
    Nothing -> do
      ans <- emitRunWriter "ref" (binderType b) $ \ref -> do
        localLinRef (b@>ref) (body >> return UnitVal)
      getSnd ans
    Just x -> body >> return x  -- optimization to avoid accumulating into unit

localLinRef :: Env Atom -> TransposeM a -> TransposeM a
localLinRef refs = local (<> mempty { linRefs = refs })

localLinRegion :: Name -> TransposeM a -> TransposeM a
localLinRegion h = local (<> mempty { linRegions = h @> () })

localSubst :: SubstEnv -> TransposeM a -> TransposeM a
localSubst s = local (<> mempty { transposeSubst = s })
