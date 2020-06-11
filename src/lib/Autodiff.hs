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

import Type
import Env
import Syntax
import Cat
import PPrint
import Embed

-- -- === linearization ===

type EmbedSubM = ReaderT SubstEnv Embed
type PrimalM = WriterT Vars EmbedSubM
newtype LinA a = LinA { runLinA :: PrimalM (a, EmbedSubM a) }

linearize :: RuleEnv -> Scope -> Atom -> Atom
linearize = undefined
-- linearize env scope (AbsBlock b block) = fst $ flip runEmbed scope $ do
--   buildLam PlainArrow b $ \x -> do
--     ((y, yt), _) <- flip runReaderT (b@>x) $ runWriterT $
--                       runLinA (linearizeBlock env block)
--     -- TODO: check linearity
--     fLin <- buildLam LinArrow b $ \xt -> runReaderT yt (b@>xt)
--     return $ PairVal y fLin

linearizeBlock :: RuleEnv -> Block -> LinA Atom
linearizeBlock ruleEnv (Block decls result) = case decls of
  [] -> linearizeExpr ruleEnv result
  Let b bound : rest -> LinA $ do
    (env, tEnvM) <- runLinA $ liftA (\x -> b@>x) $ linearizeExpr ruleEnv bound
    (ans, fLin) <- extendR env $ runLinA $ linearizeBlock ruleEnv body
    return (ans, do tEnv <- tEnvM
                    extendR tEnv fLin)
    where body = Block rest result

-- linearizeLam :: RuleEnv -> AbsBlock
--                  -> EmbedSubM (AbsBlock, [Type], Atom -> [Atom] -> EmbedSubM Atom)
-- linearizeabsblock = undefined
-- linearizeAbsBlock ruleEnv (AbsBlock v body) = do
--   (lam, (v', residualVs, tBuilder)) <- buildAbsBlockAux v $ \v'@(Var iVar) ->
--     extendR (v@>v') $ do
--        (((ans, ansT), (localScope, decls)), fvs) <-
--            runWriterT $ embedScoped $ runLinA $ linearizeBlock ruleEnv body
--        extendScope localScope
--        mapM_ emitDecl decls
--        let residualVs = [rv :> ty | (rv, ty) <- envPairs $ localScope `envIntersect` fvs]
--        let ansWithResiduals = foldr PairVal ans $ map Var residualVs
--        return (ansWithResiduals, (iVar, residualVs, ansT))
--   extendScope $ foldMap (@>Nothing) (v':residualVs)
--   return (lam, map varAnn residualVs, \v'' residuals -> do
--      scope <- getScope
--      (ansT', decls) <- extendR (v @> Var v') $ scopedDecls tBuilder
--      let env = (v'@>v'') <> newEnv residualVs residuals
--      emitBlock $ subst (env, scope) $ wrapDecls decls ansT')

unpackResiduals :: Monad m => (ty -> a -> m (a, a)) -> [ty] -> a -> m (a, [a])
unpackResiduals _ [] ans = return (ans, [])
unpackResiduals f (t:ts) packed = do
  (r, packed') <- f t packed
  (ans, rs) <- unpackResiduals f ts packed'
  return (ans, r:rs)

linearizeExpr :: RuleEnv -> Expr -> LinA Atom
linearizeExpr ruleEnv expr = case expr of
  _ | hasDiscreteType expr -> LinA $ do
    ans <- substEmbed expr >>= emit
    return $ withZeroTangent ans
  -- For d lam@(AbsBlock i _) -> LinA $ do
  --   (lam', rTys, lin) <- lift $ linearizeAbsBlock ruleEnv lam
  --   ansRes <- emit $ For d lam'
  --   (ans, residuals) <- unpackResiduals (const unzipTab) rTys ansRes
  --   mapM_ saveVars residuals
  --   return (ans, buildFor d i $ \i' -> do
  --                  residuals' <- forM residuals $ \r -> emit $ TabGet r i'
  --                  lin i' residuals')
  App x i | isTabTy (getType x) -> LinA $ do
    (i', _)  <- runLinA $ linearizeAtom i
    (x', tx) <- runLinA $ linearizeAtom x
    ans <- emit $ App x' i'
    return (ans, do tx' <- tx
                    emit $ App tx' i')
  App (Var v) arg | v `isin` ruleEnv -> LinA $ do
    (x, t) <- runLinA $ linearizeAtom arg
    (y, f) <- emit (App (ruleEnv ! v) x) >>= fromPair
    saveVars f
    return (y, liftM (App f) t >>= emit )

linearizeOp :: RuleEnv -> Op -> LinA Atom
linearizeOp ruleEnv op = case fmap linearizeAtom op of
  ScalarUnOp  FNeg x     ->     liftA  (ScalarUnOp  FNeg) x     `bindLin` emitOp
  ScalarBinOp FAdd x1 x2 ->     liftA2 (ScalarBinOp FAdd) x1 x2 `bindLin` emitOp
  ScalarBinOp FSub x1 x2 ->     liftA2 (ScalarBinOp FSub) x1 x2 `bindLin` emitOp
  ScalarBinOp FMul x1 x2 -> tensLiftA2 (ScalarBinOp FMul) x1 x2
  ScalarBinOp FDiv x y -> LinA $ do
    (x', tx) <- runLinA x
    (y', ty) <- runLinA y
    ans <- div' x' y'
    saveVars (x', y')
    return (ans, do tx' <- tx
                    ty' <- ty
                    linearizedDiv x' y' tx' ty')
  PrimEffect refArg m ->
    liftA2 PrimEffect refArg
      (case m of
         MAsk    -> pure MAsk
         MTell x -> liftA MTell x
         _       -> error "Not implemented") `bindLin` emitOp
  Fst x -> liftA Fst x `bindLin` emitOp
  Snd x -> liftA Snd x `bindLin` emitOp
  _ -> error $ "not implemented: " ++ pprint op

linearizeHof :: RuleEnv -> Hof -> LinA Atom
linearizeHof = undefined
-- linearizeHof ruleEnv hof = case bimap linearizeAtom id hof of
--   RunReader r lam@(AbsBlock ref _) -> LinA $ do
--     (r', rt) <- runLinA r
--     (lam', rTys, lin) <- lift $ linearizeAbsBlock ruleEnv lam
--     ansRes <- emit $ Hof $ RunReader r' lam'
--     (ans, residuals) <- unpackResiduals (const fromPair) rTys ansRes
--     mapM_ saveVars residuals
--     return (ans , do rt' <- rt
--                      lam'' <- buildAbsBlock ref $ \ref' -> lin ref' residuals
--                      emit $ Hof $ RunReader rt' lam'')
--   RunWriter lam@(AbsBlock ref _) -> LinA $ do
--     (lam', rTys, lin) <- lift $ linearizeAbsBlock ruleEnv lam
--     (ansRes, w) <- fromPair =<< emit (Hof $ RunWriter lam')
--     (ans, residuals) <- unpackResiduals (const fromPair) rTys ansRes
--     mapM_ saveVars residuals
--     return ( PairVal ans w
--            , do lam'' <- buildAbsBlock ref $ \ref' -> lin ref' residuals
--                 emit $ Hof $ RunWriter lam'')

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
  PairCon x y -> liftA2 PairVal (linearizeAtom x) (linearizeAtom y)
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
    Just x -> return (x, do
      maybeTVal <- asks $ flip envLookup v
      -- TODO: consider having separate primal-subst and tangent envs
      case maybeTVal of
        Just t -> return t
        Nothing    -> error "Tangent lookup failed")
    Nothing    -> return (withZeroTangent (Var v))

withZeroTangent :: Atom -> (Atom, EmbedSubM Atom)
withZeroTangent x = (x, zeroAt (tangentType (getType x)))

tangentType :: Type -> Type
tangentType (TabTy n a) = TabTy n (tangentType a)
tangentType (TC con) = case con of
  BaseType RealType  -> TC $ BaseType RealType
  BaseType   _       -> UnitTy
  IntRange   _ _     -> UnitTy
  IndexRange _ _ _   -> UnitTy
  PairType a b       -> PairTy (tangentType a) (tangentType b)
  -- RefType a          -> RefTy $ tangentType a
  _           -> error $ "Can't differentiate wrt type " ++ pprint con
tangentType ty = error $ "Can't differentiate wrt type " ++ pprint ty

hasDiscreteType :: HasType e => e -> Bool
hasDiscreteType = undefined
  -- Nothing | null eff -> isSingletonType tangentTy
  -- _ -> False
  -- where (Effects eff tailVar, ty) = getEffType expr
  --       tangentTy = tangentType ty

tensLiftA2 :: (HasVars a, HasVars b)
           => (a -> b -> Op) -> LinA a -> LinA b -> LinA Atom
tensLiftA2 f (LinA m1) (LinA m2) = LinA $ do
  (x1, mt1) <- m1
  (x2, mt2) <- m2
  ans <- emitOp $ f x1 x2
  saveVars (x1, x2)
  return ( ans
         , do t1 <- mt1
              t2 <- mt2
              tOut1 <- emitOp $ f x1 t2
              tOut2 <- emitOp $ f t1 x2
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

transposeMap :: Scope -> Atom -> Atom
transposeMap = undefined
-- transposeMap scope (AbsBlock b expr) = fst $ flip runEmbed scope $ do
--   buildLam LinArrow ("ct" :> getType expr) $ \ct -> do
--     flip runReaderT mempty $ withLinVar b $ transposeBlock expr ct

transposeBlock :: Block -> Atom -> TransposeM ()
transposeBlock = undefined
-- transposeBlock (Block decls result) ct = case decls of
--   [] -> transposeExpr result ct
--   Let b bound : rest -> do
--     let (eff, _) = getEffType bound
--     linEff <- isLinEff eff
--     lin <- isLin bound
--     if lin || linEff
--       then do
--         ct' <- withLinVar b $ transposeBlock body ct
--         transposeExpr bound ct'
--       else do
--         x <- substTranspose bound >>= emitTo b
--         extendR (asSnd (b@>x)) $ transposeBlock body ct
--     where body = Block rest result

transposeExpr :: Expr -> Atom -> TransposeM ()
transposeExpr = undefined
-- transposeExpr expr ct = case expr of
--   For d (AbsBlock v body) -> do
--     lam <- buildAbsBlock v $ \i -> do
--       ct' <- nTabGet ct i
--       extendR (asSnd (v@>i)) $ transposeBlock body ct'
--       return UnitVal
--     void $ emit $ For (flipDir d) lam
  -- TabGet ~(Var x) i -> do
  --   i' <- substTranspose i
  --   linVars <- asks fst
  --   ref <- case envLookup linVars x of
  --            Just ref -> return ref
  --            -- might be possible to reach here indexing into a literal zero array
  --            _ -> error "Not implemented"
  --   void $ withIndexed Writer ref i' $ \(Var ref') -> do
  --     emitCTToRef ref' ct
  --     return UnitVal

transposeOp :: Op -> Atom -> TransposeM ()
transposeOp op ct = case op of
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
  -- RecGet x i -> do
  --   ~(RecVal rZeros) <- zeroAt (getType x)
  --   let ct' = RecVal $ recUpdate i ct rZeros
  --   transposeAtom x ct'
  PrimEffect refArg m -> do
    refArg' <- substTranspose refArg
    case m of
      MAsk -> void $ emitOp $ PrimEffect refArg' (MTell ct)
      MTell x -> do
       ct' <- emitOp $ PrimEffect refArg' MAsk
       transposeAtom x ct'
      _ -> error "Not implemented"
  _ -> error $ "not implemented: transposition for: " ++ pprint op


transposeHof :: Hof -> Atom -> TransposeM ()
transposeHof = undefined
-- transposeHof hof ct = case hof of
--   RunReader r (AbsBlock v body) -> do
--     lam <- buildAbsBlock v $ \x -> do
--              extendR (asSnd (v@>x)) $ transposeBlock body ct
--              return UnitVal
--     (_, ctr) <- emit (Hof $ RunWriter lam) >>= fromPair
--     transposeAtom r ctr
--   RunWriter (AbsBlock v body) -> do
--     (ctBody, ctEff) <- fromPair ct
--     lam <- buildAbsBlock v $ \x -> do
--              extendR (asSnd (v@>x)) $ transposeBlock body ctBody
--              return UnitVal
--     void $ emit $ Hof $ RunReader ctEff lam


transposeCon :: Con -> Atom -> TransposeM ()
transposeCon con _ | isSingletonType (getType (Con con)) = return ()
transposeCon con ct = case con of
  Lit _ -> return ()
  -- RecCon r -> do
  --   rCT <- unpackRec ct
  --   sequence_ $ recZipWith transposeAtom r rCT
  _ -> error $ "not implemented: transposition for: " ++ pprint con

transposeAtom :: Atom -> Atom -> TransposeM ()
transposeAtom atom ct = case atom of
  Var v -> emitCT v ct
  Con con -> transposeCon con ct
  _ -> error $ "Can't transpose: " ++ pprint atom

freeLinVars :: HasVars a => a -> TransposeM [Var]
freeLinVars x = do
  linVs <- asks fst
  return $ map (uncurry (:>)) $ envPairs $ envIntersect linVs (freeVars x)

isLin :: HasVars a => a -> TransposeM Bool
isLin x = liftM (not . null) $ freeLinVars x

-- TODO: allow nonlinear effects
isLinEff :: EffectRow -> TransposeM Bool
isLinEff = undefined
-- isLinEff ~(Effect row _) = return $ not $ null $ toList row

emitCT :: Var -> Atom -> TransposeM ()
emitCT v ct = do
  linVars <- asks fst
  case envLookup linVars v of
    Just ~(Var ref) -> emitCTToRef ref ct
    _ -> return ()

emitCTToRef :: Var -> Atom -> TransposeM ()
emitCTToRef ref ct = void $ emitOp $ PrimEffect (Var ref) (MTell ct)

substTranspose :: HasVars a => a -> TransposeM a
substTranspose x = do
  env <- asks snd
  scope <- getScope
  return $ subst (env, scope) x

withLinVar :: Var -> TransposeM () -> TransposeM Atom
withLinVar v m = liftM fst $ extractCT v m

extractCT :: Var -> TransposeM a -> TransposeM (Atom, a)
extractCT = undefined
-- extractCT v@(_:>ty) m = do
--   (lam, ans) <- buildAbsBlockAux ("ctRef":> RefTy ty) $ \ctRef -> do
--     extendR (asFst (v @> ctRef)) $ do
--       ans <- m
--       return (UnitVal, ans)
--   (_, w) <- emit (Hof (RunWriter lam)) >>= fromPair
--   return (w, ans)

flipDir :: Direction -> Direction
flipDir Fwd = Rev
flipDir Rev = Fwd
