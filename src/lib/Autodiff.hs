-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}

module Autodiff (linearize, transposeMap) where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Foldable

import Type
import Env
import Syntax
import Cat
import PPrint
import Subst
import Embed
import Record

-- -- === linearization ===

type EmbedSubM = ReaderT SubstEnv Embed
type PrimalM = WriterT Vars EmbedSubM
newtype LinA a = LinA { runLinA :: PrimalM (a, EmbedSubM a) }

linearize :: RuleEnv -> Scope -> LamExpr -> Atom
linearize env scope (LamExpr b expr) = fst $ flip runEmbed scope $ do
  buildLam NonLin b $ \x -> do
    ((y, yt), _) <- flip runReaderT (b @> L x) $ runWriterT $
                      runLinA (linearizeExpr env expr)
    -- TODO: check linearity
    fLin <- buildLam Lin b $ \xt ->do
              ans <- runReaderT yt (b @> L xt)
              return (ans, noEffect)
    return (PairVal y fLin, noEffect)

linearizeExpr :: RuleEnv -> Expr -> LinA Atom
linearizeExpr ruleEnv expr = case expr of
  Decl (Let b bound) body -> LinA $ do
    (env, tEnvM) <- runLinA $ liftA (\x -> b @> L x) $ linearizeCExpr ruleEnv bound
    (ans, fLin) <- extendR env $ runLinA $ linearizeExpr ruleEnv body
    return (ans, do tEnv <- tEnvM
                    extendR tEnv fLin)
  CExpr e -> linearizeCExpr ruleEnv e
  Atom x  -> linearizeAtom x

linearizeLamExpr :: RuleEnv -> LamExpr
                 -> EmbedSubM (LamExpr, [Type], Atom -> [Atom] -> EmbedSubM Atom)
linearizeLamExpr ruleEnv (LamExpr v body) = do
  (lam, (v', residualVs, tBuilder)) <- buildLamExprAux v $ \v'@(Var iVar) ->
    extendR (v @> L v') $ do
       (((ans, ansT), embedEnv), fvs) <- runWriterT $ scoped $ runLinA $
                                           linearizeExpr ruleEnv body
       let localScope = fst embedEnv
       extend embedEnv
       let residualVs = [rv :> ty | (rv, L ty) <- envPairs $ localScope `envIntersect` fvs]
       let ansWithResiduals = foldr PairVal ans $ map Var residualVs
       return (ansWithResiduals, (iVar, residualVs, ansT))
  extend $ asFst (foldMap (@>()) (v':residualVs))
  return (lam, map varAnn residualVs, \v'' residuals -> do
     scope <- looks fst
     (ansT', (_, decls)) <- extendR (v @> L (Var v')) $ scoped tBuilder
     let env = (v' @> L v'') <> newLEnv residualVs residuals
     emitExpr $ subst (env, scope) $ wrapDecls decls ansT')

unpackResiduals :: Monad m => (ty -> a -> m (a, a)) -> [ty] -> a -> m (a, [a])
unpackResiduals _ [] ans = return (ans, [])
unpackResiduals f (t:ts) packed = do
  (r, packed') <- f t packed
  (ans, rs) <- unpackResiduals f ts packed'
  return (ans, r:rs)

linearizeCExpr :: RuleEnv -> CExpr -> LinA Atom
linearizeCExpr ruleEnv (App _ (Var v) arg) | v `isin` ruleEnv = LinA $ do
  (x, t) <- runLinA $ linearizeAtom arg
  (y, f) <- emit (App NonLin (ruleEnv ! v) x) >>= fromPair
  saveVars f
  return ( y
         , liftM (App Lin f) t >>= emit )
linearizeCExpr _ expr | hasDiscreteType expr = LinA $ do
  expr' <- substEmbed expr
  ans <- emit expr'
  return $ withZeroTangent ans

linearizeCExpr ruleEnv expr = case expr' of
  ScalarUnOp  FNeg x     ->     liftA  (ScalarUnOp  FNeg) x     `bindLin` emit
  ScalarBinOp FAdd x1 x2 ->     liftA2 (ScalarBinOp FAdd) x1 x2 `bindLin` emit
  ScalarBinOp FSub x1 x2 ->     liftA2 (ScalarBinOp FSub) x1 x2 `bindLin` emit
  ScalarBinOp FMul x1 x2 -> tensLiftA2 (ScalarBinOp FMul) x1 x2
  ScalarBinOp FDiv x y -> LinA $ do
    (x', tx) <- runLinA x
    (y', ty) <- runLinA y
    ans <- div' x' y'
    saveVars (x', y')
    return (ans, do tx' <- tx
                    ty' <- ty
                    linearizedDiv x' y' tx' ty')
  TabGet x i -> LinA $ do
    (i', _)  <- runLinA i
    (x', tx) <- runLinA x
    ans <- emit $ TabGet x' i'
    return (ans, do tx' <- tx
                    emit $ TabGet tx' i')
  For d lam@(LamExpr i _) -> LinA $ do
    (lam', rTys, lin) <- lift $ linearizeLamExpr ruleEnv lam
    ansRes <- emit $ For d lam'
    (ans, residuals) <- unpackResiduals (const unzipTab) rTys ansRes
    mapM_ saveVars residuals
    return (ans, buildFor d i $ \i' -> do
                   residuals' <- forM residuals $ \r -> emit $ TabGet r i'
                   lin i' residuals')
  RunReader r lam@(LamExpr ref _) -> LinA $ do
    (r', rt) <- runLinA r
    (lam', rTys, lin) <- lift $ linearizeLamExpr ruleEnv lam
    ansRes <- emit $ RunReader r' lam'
    (ans, residuals) <- unpackResiduals (const fromPair) rTys ansRes
    mapM_ saveVars residuals
    return (ans , do rt' <- rt
                     lam'' <- buildLamExpr ref $ \ref' -> lin ref' residuals
                     emit $ RunReader rt' lam'')
  RunWriter lam@(LamExpr ref _) -> LinA $ do
    (lam', rTys, lin) <- lift $ linearizeLamExpr ruleEnv lam
    (ansRes, w) <- fromPair =<< emit (RunWriter lam')
    (ans, residuals) <- unpackResiduals (const fromPair) rTys ansRes
    mapM_ saveVars residuals
    return ( PairVal ans w
           , do lam'' <- buildLamExpr ref $ \ref' -> lin ref' residuals
                emit $ RunWriter lam'')
  PrimEffect refArg m ->
    liftA2 PrimEffect refArg
      (case m of
         MAsk    -> pure MAsk
         MTell x -> liftA MTell x
         _       -> error "Not implemented") `bindLin` emit
  RecGet x i -> liftA (flip RecGet i) x `bindLin` emit
  _ -> error $ "not implemented: " ++ pprint expr
  where expr' = fmapExpr expr id linearizeAtom id

linearizedDiv :: Atom -> Atom -> Atom -> Atom -> EmbedSubM Atom
linearizedDiv x y tx ty = do
  tx'  <- div' tx y
  ty'  <- mul ty x
  ySq  <- mul y y
  ty'' <- div' ty' ySq >>= neg
  add tx' ty''

linearizePrimCon :: Con -> LinA Atom
linearizePrimCon con = case con of
  Lit _    -> LinA $ return (withZeroTangent x)  where x = Con con
  AFor _ _ -> LinA $ return (withZeroTangent x)  where x = Con con
  RecCon r -> liftA RecVal $ sequenceA $ fmap linearizeAtom r
  _ -> error $ "not implemented: " ++ pprint con

linearizeAtom :: Atom -> LinA Atom
linearizeAtom atom | hasDiscreteType atom =
  LinA $ liftM withZeroTangent $ substEmbed atom
linearizeAtom atom = case atom of
  Var v -> linearizeVar v
  Con con -> linearizePrimCon con
  _ -> error "Not implemented"

linearizeVar :: Var -> LinA Atom
linearizeVar v = LinA $ do
  maybeVal <- asks $ flip envLookup v
  case maybeVal of
    Just (L x) -> return (x, do
      maybeTVal <- asks $ flip envLookup v
      -- TODO: consider having separate primal-subst and tangent envs
      case maybeTVal of
        Just ~(L t) -> return t
        Nothing    -> error "Tangent lookup failed")
    Nothing    -> return (withZeroTangent (Var v))
    _ -> error "unexpected lookup"

withZeroTangent :: Atom -> (Atom, EmbedSubM Atom)
withZeroTangent x = (x, zeroAt (tangentType (getType x)))

tangentType :: Type -> Type
tangentType (TabTy n a) = TabTy n (tangentType a)
tangentType (TC con) = case con of
  BaseType RealType  -> TC $ BaseType RealType
  BaseType   _       -> UnitTy
  IntRange   _ _     -> UnitTy
  IndexRange _ _ _   -> UnitTy
  RecType r          -> RecTy $ fmap tangentType r
  RefType a          -> RefTy $ tangentType a
  _           -> error $ "Can't differentiate wrt type " ++ pprint con
tangentType ty = error $ "Can't differentiate wrt type " ++ pprint ty

hasDiscreteType :: HasType e => e -> Bool
hasDiscreteType expr = case tailVar of
  Nothing | null eff -> isSingletonType tangentTy
  _ -> False
  where (Effect eff tailVar, ty) = getEffType expr
        tangentTy = tangentType ty

tensLiftA2 :: (HasVars a, HasVars b)
           => (a -> b -> CExpr) -> LinA a -> LinA b -> LinA Atom
tensLiftA2 f (LinA m1) (LinA m2) = LinA $ do
  (x1, mt1) <- m1
  (x2, mt2) <- m2
  ans <- emit $ f x1 x2
  saveVars (x1, x2)
  return ( ans
         , do t1 <- mt1
              t2 <- mt2
              tOut1 <- emit $ f x1 t2
              tOut2 <- emit $ f t1 x2
              add tOut1 tOut2)

bindLin :: LinA a -> (a -> EmbedSubM b) -> LinA b
bindLin (LinA m) f = LinA $ do
  (e, t) <- m
  x <- lift $ f e
  return (x, t >>= f)

saveVars :: HasVars a => a -> PrimalM ()
saveVars x = tell $ freeVars x

instance Functor LinA where
  fmap = liftA

instance Applicative LinA where
  pure x = LinA $ return (x, return x)
  liftA2 f (LinA m1) (LinA m2) = LinA $ do
    (x1, t1) <- m1
    (x2, t2) <- m2
    return (f x1 x2, liftM2 f t1 t2)

-- -- === transposition ===

type LinVars = Env Atom
type TransposeM a = ReaderT (LinVars, SubstEnv) Embed a

transposeMap :: Scope -> LamExpr -> Atom
transposeMap scope (LamExpr b expr) = fst $ flip runEmbed scope $ do
  buildLam Lin ("ct" :> getType expr) $ \ct -> do
    flip runReaderT mempty $ do
      ans <- withLinVar b $ transposeExpr expr ct
      return (ans, noEffect)

transposeExpr :: Expr -> Atom -> TransposeM ()
transposeExpr expr ct = case expr of
  Decl (Let b bound) body -> do
    let (eff, _) = getEffType bound
    linEff <- isLinEff eff
    lin <- isLin bound
    if lin || linEff
      then do
        ct' <- withLinVar b $ transposeExpr body ct
        transposeCExpr bound ct'
      else do
        x <- substTranspose bound >>= emitTo b
        extendR (asSnd (b @> L x)) $ transposeExpr body ct
  CExpr e -> transposeCExpr e ct
  Atom x  -> transposeAtom x ct

transposeCExpr :: CExpr -> Atom -> TransposeM ()
transposeCExpr expr ct = case expr of
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
  RecGet x i -> do
    ~(RecVal rZeros) <- zeroAt (getType x)
    let ct' = RecVal $ recUpdate i ct rZeros
    transposeAtom x ct'
  For d (LamExpr v body) -> do
    lam <- buildLamExpr v $ \i -> do
      ct' <- nTabGet ct i
      extendR (asSnd (v @> L i)) $ transposeExpr body ct'
      return UnitVal
    void $ emit $ For (flipDir d) lam
  TabGet ~(Var x) i -> do
    i' <- substTranspose i
    linVars <- asks fst
    ref <- case envLookup linVars x of
             Just ref -> return ref
             -- might be possible to reach here indexing into a literal zero array
             _ -> error "Not implemented"
    void $ withIndexed Writer ref i' $ \(Var ref') -> do
      emitCTToRef ref' ct
      return UnitVal
  RunReader r (LamExpr v body) -> do
    lam <- buildLamExpr v $ \x -> do
             extendR (asSnd (v @> L x)) $ transposeExpr body ct
             return UnitVal
    (_, ctr) <- emit (RunWriter lam) >>= fromPair
    transposeAtom r ctr
  RunWriter (LamExpr v body) -> do
    (ctBody, ctEff) <- fromPair ct
    lam <- buildLamExpr v $ \x -> do
             extendR (asSnd (v @> L x)) $ transposeExpr body ctBody
             return UnitVal
    void $ emit $ RunReader ctEff lam
  PrimEffect refArg m -> do
    refArg' <- substTranspose refArg
    case m of
      MAsk -> void $ emit $ PrimEffect refArg' (MTell ct)
      MTell x -> do
       ct' <- emit $ PrimEffect refArg' MAsk
       transposeAtom x ct'
      _ -> error "Not implemented"
  _ -> error $ "not implemented: transposition for: " ++ pprint expr

transposeCon :: Con -> Atom -> TransposeM ()
transposeCon con _ | isSingletonType (getType (Con con)) = return ()
transposeCon con ct = case con of
  Lit _ -> return ()
  RecCon r -> do
    rCT <- unpackRec ct
    sequence_ $ recZipWith transposeAtom r rCT
  _ -> error $ "not implemented: transposition for: " ++ pprint con

transposeAtom :: Atom -> Atom -> TransposeM ()
transposeAtom atom ct = case atom of
  Var v -> emitCT v ct
  Con con -> transposeCon con ct
  _ -> error $ "Can't transpose: " ++ pprint atom

freeLinVars :: HasVars a => a -> TransposeM [Var]
freeLinVars x = do
  linVs <- asks fst
  return [v:>ty | (v, L ty) <- envPairs $ envIntersect linVs (freeVars x)]

isLin :: HasVars a => a -> TransposeM Bool
isLin x = liftM (not . null) $ freeLinVars x

-- TODO: allow nonlinear effects
isLinEff :: Effect -> TransposeM Bool
isLinEff ~(Effect row _) = return $ not $ null $ toList row

emitCT :: Var -> Atom -> TransposeM ()
emitCT v ct = do
  linVars <- asks fst
  case envLookup linVars v of
    Just ~(Var ref) -> emitCTToRef ref ct
    _ -> return ()

emitCTToRef :: Var -> Atom -> TransposeM ()
emitCTToRef ref ct = void $ emit $ PrimEffect (Var ref) (MTell ct)

substTranspose :: Subst a => a -> TransposeM a
substTranspose x = do
  env <- asks snd
  scope <- looks fst
  return $ subst (env, scope) x

withLinVar :: Var -> TransposeM () -> TransposeM Atom
withLinVar v m = liftM fst $ extractCT v m

extractCT :: Var -> TransposeM a -> TransposeM (Atom, a)
extractCT v@(_:>ty) m = do
  (lam, ans) <- buildLamExprAux ("ctRef":> RefTy ty) $ \ctRef -> do
    extendR (asFst (v @> ctRef)) $ do
      ans <- m
      return (UnitVal, ans)
  (_, w) <- emit (RunWriter lam) >>= fromPair
  return (w, ans)

flipDir :: Direction -> Direction
flipDir Fwd = Rev
flipDir Rev = Fwd
