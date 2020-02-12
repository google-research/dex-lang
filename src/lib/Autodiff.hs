-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}

module Autodiff (linearize, transposeMap) where

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

type LinearizeM a = ReaderT SubstEnv Embed a
type TangentM   a = ReaderT SubstEnv Embed a

-- -- === linearization ===

linearize :: Scope -> LamExpr -> Atom
linearize scope (LamExpr b expr) = fst $ flip runEmbed scope $ do
  buildLam NonLin b $ \x -> do
    (y, yt) <- runReaderT (linearizeExpr expr) (b @> L x)
    -- TODO: check linearity
    fLin <- buildLam Lin b $ \xt -> runReaderT yt (b @> L xt)
    return $ makePair y fLin

linearizeExpr :: Expr -> LinearizeM (Atom, TangentM Atom)
linearizeExpr expr = case expr of
  Decl decl body -> do
    (env, makeTangentEnv) <- linearizeDecl decl
    (ans, fLin) <- extendR env (linearizeExpr body)
    return (ans, do tEnv <- makeTangentEnv
                    extendR tEnv fLin)
  CExpr e -> linearizeCExpr e
  Atom x  -> linearizeAtom x

linearizeDecl :: Decl -> LinearizeM (SubstEnv, TangentM SubstEnv)
linearizeDecl decl = case decl of
  Let b bound -> do
    b' <- substEmbed b
    (x, fLin) <- linearizeCExpr bound
    return (b' @> L x, do t <- fLin
                          return (b'@> L t))
  _ -> error "Not implemented"

linearizeCExpr :: CExpr -> LinearizeM (Atom, TangentM Atom)
linearizeCExpr expr = case expr of
  ScalarBinOp FAdd x1 x2 -> do
    (x1', t1) <- linearizeAtom x1
    (x2', t2) <- linearizeAtom x2
    y <- add x1' x2'
    return (y, do t1' <- t1
                  t2' <- t2
                  add t1' t2')
  ScalarBinOp FMul x1 x2 -> do
    (x1', t1) <- linearizeAtom x1
    (x2', t2) <- linearizeAtom x2
    y <- mul x1' x2'
    return (y, do t1' <- t1
                  t2' <- t2
                  yt1 <- mul x1' t2'
                  yt2 <- mul t1' x2'
                  add yt1 yt2)

linearizeAtom :: Atom -> LinearizeM (Atom, TangentM Atom)
linearizeAtom atom = case atom of
  Var v -> do
    maybeVal <- asks $ flip envLookup v
    case maybeVal of
      Just (L x) -> return (x, asks (fromL . (!v)))
      Nothing -> return $ zeroDeriv atom
      _ -> error "unexpected lookup"
  Con con -> case con of
    Lit _ -> return $ zeroDeriv atom
    _ -> error $ "not implemented: " ++ pprint atom
  _ -> error $ "not implemented: " ++ pprint atom

zeroDeriv :: Atom -> (Atom, TangentM Atom)
zeroDeriv x = (x, zeroAt (getType x))

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
