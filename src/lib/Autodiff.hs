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

linearize :: TopEnv -> Scope -> LamExpr -> Atom
linearize env scope (LamExpr b expr) = fst $ flip runEmbed scope $ do
  buildLam NonLin b $ \x -> do
    ((y, yt), _) <- flip runReaderT (b @> L x) $ runWriterT $
                      runLinA (linearizeExpr env expr)
    -- TODO: check linearity
    fLin <- buildLam Lin b $ \xt ->do
              ans <- runReaderT yt (b @> L xt)
              return (ans, noEffect)
    return (makePair y fLin, noEffect)

linearizeExpr :: TopEnv -> Expr -> LinA Atom
linearizeExpr topEnv expr = case expr of
  Decl (Let b bound) body -> LinA $ do
    (env, tEnvM) <- runLinA $ liftA (\x -> b @> L x) $ linearizeCExpr topEnv bound
    (ans, fLin) <- extendR env $ runLinA $ linearizeExpr topEnv body
    return (ans, do tEnv <- tEnvM
                    extendR tEnv fLin)
  CExpr e -> linearizeCExpr topEnv e
  Atom x  -> linearizeAtom x

linearizeLamExpr :: TopEnv -> LamExpr
                 -> EmbedSubM (LamExpr, Atom -> Atom -> EmbedSubM Atom)
linearizeLamExpr topEnv (LamExpr v body) = do
  (lam, (v', residualVs, tBuilder)) <- buildLamExprAux v $ \v'@(Var iVar) ->
    extendR (v @> L v') $ do
       (((ans, ansT), embedEnv), fvs) <- runWriterT $ scoped $ runLinA $
                                           linearizeExpr topEnv body
       let localScope = fst embedEnv
       extend embedEnv
       let residualVs = [rv :> ty | (rv, L ty) <- envPairs $ localScope `envIntersect` fvs]
       let ansWithResiduals = makePair ans (makeTup (map Var residualVs))
       return (ansWithResiduals, (iVar, residualVs, ansT))
  extend $ asFst (foldMap (@>()) (v':residualVs))
  return (lam, \v'' residuals -> do
     ~(Tup residuals') <- unpackRec residuals
     scope <- looks fst
     (ansT', (_, decls)) <- extendR (v @> L (Var v')) $ scoped tBuilder
     let env = (v' @> L v'') <> newLEnv residualVs residuals'
     emitExpr $ subst (env, scope) $ wrapDecls decls ansT')

linearizeCExpr :: TopEnv -> CExpr -> LinA Atom
linearizeCExpr topEnv (App _ _ (Var v) arg) | v `isin` linRules topEnv = LinA $ do
  (x, t) <- runLinA $ linearizeAtom arg
  ~(Tup [y, f]) <- emit (App NonLin NoDep (linRules topEnv ! v) x) >>= unpackRec
  saveVars f
  return ( y
         , liftM (App Lin NoAnn f) t >>= emit )
linearizeCExpr _ expr | hasDiscreteType expr = LinA $ do
  expr' <- substEmbed expr
  ans <- emit expr'
  return $ withZeroTangent ans

linearizeCExpr topEnv expr = case expr' of
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
  For lam@(LamExpr i _) -> LinA $ do
    (lam', lin) <- lift $ linearizeLamExpr topEnv lam
    (ans, residuals) <- emit (For lam') >>= unzipTab
    saveVars residuals
    return (ans, buildFor i $ \i' -> do residuals' <- emit $ TabGet residuals i'
                                        lin i' residuals')
  RunReader r lam@(LamExpr ref _) -> LinA $ do
    (r', rt) <- runLinA r
    (lam', lin) <- lift $ linearizeLamExpr topEnv lam
    (ans, residuals) <- fromPair =<< emit (RunReader r' lam')
    saveVars residuals
    return (ans , do rt' <- rt
                     lam'' <- buildLamExpr ref $ \ref' -> lin ref' residuals
                     emit $ RunReader rt' lam'')
  RunWriter lam@(LamExpr ref _) -> LinA $ do
    (lam', lin) <- lift $ linearizeLamExpr topEnv lam
    (ansRes, w) <- fromPair =<< emit (RunWriter lam')
    (ans, residuals) <- fromPair ansRes
    saveVars residuals
    return ( makePair ans w
           , do lam'' <- buildLamExpr ref $ \ref' -> lin ref' residuals
                emit $ RunWriter lam'')
  PrimEffect ~(Dep ref) refArg m ->
    liftA3 (\ref' refArg' m' -> PrimEffect (Dep ref') refArg' m')
      (liftA (\(Var v) -> v) $ linearizeVar ref) refArg
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
linearizePrimCon con = case con' of
  Lit _    -> LinA $ return (withZeroTangent x)  where x = Con con
  RecCon r -> liftA (Con . RecCon) $ sequenceA r
  _ -> error $ "not implemented: " ++ pprint con
  where con' = fmapExpr con id linearizeAtom id

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
tangentType ty = case ty of
  BaseType RealType -> BaseType RealType
  BaseType   _   -> unitTy
  IntRange   _ _ -> unitTy
  IndexRange _ _ -> unitTy
  TabType n a    -> TabType n (tangentType a)
  RecType r      -> RecType $ fmap tangentType r
  Ref a          -> Ref $ tangentType a
  _ -> error $ "Can't differentiate wrt type " ++ pprint ty

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
    ~(Con (RecCon rZeros)) <- zeroAt (getType x)
    let ct' = Con $ RecCon $ recUpdate i ct rZeros
    transposeAtom x ct'
  For (LamExpr v body) -> do
    -- TODO: flip index or iteration order!
    lam <- buildLamExpr v $ \i -> do
      ct' <- nTabGet ct i
      extendR (asSnd (v @> L i)) $ transposeExpr body ct'
      return unitCon
    void $ emit $ For lam
  TabGet ~(Var x) i -> do
    i' <- substTranspose i
    linVars <- asks fst
    ref <- case envLookup linVars x of
             Just ref -> return ref
             -- might be possible to reach here indexing into a literal zero array
             _ -> error "Not implemented"
    void $ withIndexed Writer ref i' $ \(Var ref') -> do
      emitCTToRef ref' ct
      return unitCon
  -- TODO: de-dup RunReader/RunWriter a bit
  RunReader r (LamExpr v body) -> do
    vs <- freeLinVars body
    body' <- buildLamExpr v $ \x ->
               extendR (asSnd (v @> L x)) $ do
                 vsCTs <- withLinVars vs $ transposeExpr body ct
                 return $ Con $ RecCon $ Tup vsCTs
    (vsCTs, ctr) <- emit (RunWriter body') >>= fromPair
    ~(Tup vsCTs') <- unpackRec vsCTs
    zipWithM_ emitCT vs vsCTs'
    transposeAtom r ctr
  RunWriter (LamExpr v body) -> do
    (ctBody, ctEff) <- fromPair ct
    vs <- freeLinVars body
    body' <- buildLamExpr v $ \x -> do
               extendR (asSnd (v @> L x)) $ do
                 vsCTs <- withLinVars vs $ transposeExpr body ctBody
                 return $ Con $ RecCon $ Tup vsCTs
    vsCTs <- emit (RunReader ctEff body')
    ~(Tup vsCTs') <- unpackRec vsCTs
    zipWithM_ emitCT vs vsCTs'
  PrimEffect ~(Dep ref) refArg m -> do
    ref' <- substVar ref
    refArg' <- substTranspose refArg
    case m of
      MAsk -> void $ emit $ PrimEffect (Dep ref') refArg' (MTell ct)
      MTell x -> do
       ct' <- emit $ PrimEffect (Dep ref') refArg' MAsk
       transposeAtom x ct'
      _ -> error "Not implemented"
  _ -> error $ "not implemented: transposition for: " ++ pprint expr

substVar :: Var -> TransposeM Var
substVar v = do
  ~(Var v') <- substTranspose (Var v)
  return v'

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
emitCTToRef ref ct = void $ emit $ PrimEffect (Dep ref) (Var ref) (MTell ct)

substTranspose :: Subst a => a -> TransposeM a
substTranspose x = do
  env <- asks snd
  scope <- looks fst
  return $ subst (env, scope) x

withLinVar :: Var -> TransposeM () -> TransposeM Atom
withLinVar v m = liftM fst $ extractCT v m

withLinVars :: [Var] -> TransposeM () -> TransposeM [Atom]
withLinVars [] m = m >> return []
withLinVars (v:vs) m = liftM (uncurry (:)) $ extractCT v $ withLinVars vs m

extractCT :: Var -> TransposeM a -> TransposeM (Atom, a)
extractCT v@(_:>ty) m = do
  (lam, ans) <- buildLamExprAux ("ctRef":> Ref ty) $ \ctRef -> do
    extendR (asFst (v @> ctRef)) $ do
      ans <- m
      return (unitCon, ans)
  (_, w) <- emit (RunWriter lam) >>= fromPair
  return (w, ans)
