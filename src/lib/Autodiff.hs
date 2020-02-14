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
import qualified Data.Map.Strict as M

import Type
import Env
import Syntax
import Cat
import PPrint
import Subst
import Embed

-- -- === linearization ===

type EmbedSubM a = ReaderT SubstEnv Embed a
newtype LinA a = LinA { runLinA :: EmbedSubM (a, EmbedSubM a) }

linearize :: Scope -> LamExpr -> Atom
linearize scope (LamExpr b expr) = fst $ flip runEmbed scope $ do
  buildLam NonLin b $ \x -> do
    (y, yt) <- runReaderT (runLinA (linearizeExpr expr)) (b @> L x)
    -- TODO: check linearity
    fLin <- buildLam Lin b $ \xt -> runReaderT yt (b @> L xt)
    return $ makePair y fLin

linearizeExpr :: Expr -> LinA Atom
linearizeExpr expr = case expr of
  Decl (Let b bound) body -> LinA $ do
    (env, tEnvM) <- runLinA $ liftA (\x -> b @> L x) $ linearizeCExpr bound
    (ans, fLin) <- extendR env $ runLinA $ linearizeExpr body
    return (ans, do tEnv <- tEnvM
                    extendR tEnv fLin)
  CExpr e -> linearizeCExpr e
  Atom x  -> linearizeAtom x

linearizeCExpr :: CExpr -> LinA Atom
linearizeCExpr expr = case expr' of
  ScalarUnOp  FNeg x     ->     liftA  (ScalarUnOp  FNeg) x     `bindLin` emit
  ScalarBinOp FAdd x1 x2 ->     liftA2 (ScalarBinOp FAdd) x1 x2 `bindLin` emit
  ScalarBinOp FSub x1 x2 ->     liftA2 (ScalarBinOp FSub) x1 x2 `bindLin` emit
  ScalarBinOp FMul x1 x2 -> tensLiftA2 (ScalarBinOp FMul) x1 x2
  _ -> error $ "not implemented: " ++ pprint expr
  where expr' = fmapExpr expr id linearizeAtom id

linearizePrimCon :: Con -> LinA Atom
linearizePrimCon con = case con' of
  Lit _    -> LinA $ return (x, zeroAt (getType x))  where x = Con con
  RecCon r -> liftA (Con . RecCon) $ sequenceA r
  _ -> error $ "not implemented: " ++ pprint con
  where con' = fmapExpr con id linearizeAtom id

linearizeAtom :: Atom -> LinA Atom
linearizeAtom atom = case atom of
  Var v -> LinA $ do
    maybeVal <- asks $ flip envLookup v
    case maybeVal of
      Just (L x) -> return (x, asks (fromL . (!v)))
      Nothing    -> return (atom, zeroAt (getType atom))
      _ -> error "unexpected lookup"
  Con con -> linearizePrimCon con

tensLiftA2 :: (a -> b -> CExpr) -> LinA a -> LinA b -> LinA Atom
tensLiftA2 f (LinA m1) (LinA m2) = LinA $ do
  (x1, mt1) <- m1
  (x2, mt2) <- m2
  ans <- emit $ f x1 x2
  return (ans, do t1 <- mt1
                  t2 <- mt2
                  tOut1 <- emit $ f x1 t2
                  tOut2 <- emit $ f t1 x2
                  add tOut1 tOut2)

bindLin :: LinA a -> (a -> EmbedSubM b) -> LinA b
bindLin (LinA m) f = LinA $ do
  (e, t) <- m
  x <- f e
  return (x, t >>= f)

instance Functor LinA where
  fmap = liftA

instance Applicative LinA where
  pure x = LinA $ return (x, return x)
  liftA2 f (LinA m1) (LinA m2) = LinA $ do
    (x1, t1) <- m1
    (x2, t2) <- m2
    return (f x1 x2, liftM2 f t1 t2)

-- -- === transposition ===

type LinVars = Env ()
type CotangentVals = MonMap Name [Atom]  -- TODO: consider folding as we go
type TransposeM a = WriterT CotangentVals (ReaderT (LinVars, SubstEnv) Embed) a

transposeMap :: Scope -> LamExpr -> Atom
transposeMap scope (LamExpr b expr) = fst $ flip runEmbed scope $ do
  buildLam Lin ("ct" :> getType expr) $ \ct -> do
    flip runReaderT mempty $ liftM fst $ runWriterT $
      withLinVar b $ transposeExpr expr ct

transposeExpr :: Expr -> Atom -> TransposeM ()
transposeExpr expr ct = case expr of
  Decl (Let b bound) body -> do
    lin <- isLin bound
    if lin
      then do
        ct' <- withLinVar b $ transposeExpr body ct
        transposeCExpr bound ct'
      else do
        x <- substTranspose bound >>= emitTo b
        extendR (asSnd (b @> L x)) $ transposeExpr body ct
  CExpr e -> transposeCExpr e ct
  Atom x  -> transposeAtom x ct
  _ -> error $ "Transpose not implemented for " ++ pprint expr

transposeCExpr :: CExpr -> Atom -> TransposeM ()
transposeCExpr expr ct = case expr of
  ScalarBinOp FAdd x y -> do
    transposeAtom x ct
    transposeAtom y ct
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

transposeAtom :: Atom -> Atom -> TransposeM ()
transposeAtom atom ct = case atom of
  Var (v:>_) -> emitCT v ct
  _ -> error $ "Can't transpose: " ++ pprint atom

isLin :: HasVars a => a -> TransposeM Bool
isLin x = do linVs <- asks fst
             return $ not $ null $ toList $ envIntersect (freeVars x) linVs

emitCT :: Name -> Atom -> TransposeM ()
emitCT v ct = tell $ MonMap $ M.singleton v [ct]

substTranspose :: Subst a => a -> TransposeM a
substTranspose x = do
  env <- asks snd
  scope <- looks fst
  return $ subst (env, scope) x

withLinVar :: Var -> TransposeM () -> TransposeM Atom
withLinVar v m = extractCT v $ extendR (asFst (v@>())) m

extractCT :: Var -> TransposeM () -> TransposeM Atom
extractCT b m = do
  ((), ctEnv) <- captureW m
  (ct, ctEnv') <- sepCotangent b ctEnv
  tell ctEnv'
  return ct

sepCotangent :: MonadCat EmbedEnv m =>
                  Var -> CotangentVals -> m (Atom, CotangentVals)
sepCotangent (v:>ty) (MonMap m) = do
  ans <- sumAt ty $ M.findWithDefault [] v m
  return (ans, MonMap (M.delete v m))
