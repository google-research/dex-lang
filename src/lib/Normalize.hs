-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Normalize (normalizeModule) where

import Control.Monad
import Control.Monad.Reader
import Data.Foldable

import Env
import Syntax
import Cat
import PPrint
import Type
import Embed
import Subst
import Record

type NormM a = ReaderT SubstEnv Embed a

normalizeModule :: FModule -> Module
normalizeModule (Module bid sig@(_, exports) decls) =
  Module bid sig $ wrapDecls decls' ans
  where
    outFVars = [FVar (v:>ty) | (v:>ty) <- exports]
    outTuple = FPrimExpr $ ConExpr $ RecCon $ Tup outFVars
    (ans, decls') = runNormM $ normalize $ wrapFDecls decls outTuple

runNormM :: NormM a -> (a, [Decl])
runNormM m = (ans, decls)
  where (ans, (_, decls)) = runEmbed (runReaderT m mempty) mempty

normalize :: FExpr -> NormM Atom
normalize expr = case expr of
  FDecl decl body -> do
    env <- normalizeDecl decl
    extendR env $ normalize body
  FVar v -> lookupVar v
  FPrimExpr (OpExpr op) ->
    traverseExpr op substNorm normalize normalizeLam >>= emit
  FPrimExpr (ConExpr con) ->
    liftM Con $ traverseExpr con substNorm normalize normalizeLam
  Annot    e _ -> normalize e
  SrcAnnot e _ -> normalize e

lookupVar :: Var -> NormM Atom
lookupVar v = do
  env <- ask
  case envLookup env v of
     Nothing -> Var <$> traverse substNorm v
     Just x  -> return x

normalizeLam :: FLamExpr -> NormM LamExpr
normalizeLam (FLamExpr p body) = do
  b <- normalizePat p
  buildLamExpr b $ \x -> do
    env <- bindPat p x
    extendR env $ normalize body

normalizePat :: Pat -> NormM Var
normalizePat p = do
  ty <- getType <$> traverse (traverse substNorm) p
  let v' = case toList p of (v:>_):_ -> v
                            []       -> NoName
  return $ v':>ty

bindPat :: Pat -> Atom -> NormM SubstEnv
bindPat (RecLeaf v) x = return $ v @> x
bindPat (RecTree r) xs =
  liftM fold $ flip traverse (recNameVals r) $ \(i, p) -> do
    x <- nRecGet xs i
    bindPat p x

normalizeDecl :: FDecl -> NormM SubstEnv
normalizeDecl decl = case decl of
  LetMono p bound -> do
    xs <- normalize bound  -- TODO: preserve names
    bindPat p xs
  LetPoly v tlam -> do
    x <- normalizeTLam tlam
    return $ v @> x
  _ -> error $ "Shouldn't this left: " ++ pprint decl

normalizeTLam ::FTLam -> NormM Atom
normalizeTLam (FTLam tvs qs body) =
  buildTLam tvs $ \tys -> do
    qs' <- mapM substNorm qs
    let env = fold $ zipWith (@>) tvs tys
    body' <- extendR env $ normalize body
    return (qs', body')

substNorm :: Subst a => a -> NormM a
substNorm x = do
  env <- ask
  scope <- embedScope
  return $ subst (env, scope) x
