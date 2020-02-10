-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Normalize (normalizeModule, normalizeVal) where

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
normalizeModule (Module ty (FModBody decls)) = Module ty (ModBody decls' results)
  where (results, decls') = runNormM (catFold normalizeDecl decls) mempty

runNormM :: NormM a -> SubstEnv -> (a, [Decl])
runNormM m env = (ans, decls)
  where (ans, (_, decls)) = runEmbed (runReaderT m env) mempty

normalizeVal :: FExpr -> Except Atom
normalizeVal expr = do
  let (ans, decls) = runNormM (normalize expr) mempty
  case decls of [] -> return ans
                _  -> throw MiscErr "leftover decls"

normalize :: FExpr -> NormM Atom
normalize expr = case expr of
  FDecl decl body -> do
    env <- normalizeDecl decl
    extendR env $ normalize body
  FVar v [] -> lookupVar v
  FVar v ts -> liftM2 TApp (lookupVar v) (mapM substTy ts) >>= emit
  FPrimExpr (PrimOpExpr op) ->
    traverseExpr op substTy normalize normalizeLam >>= emit
  FPrimExpr (ConExpr con) ->
    liftM Con $ traverseExpr con substTy normalize normalizeLam
  Annot    e _ -> normalize e
  SrcAnnot e _ -> normalize e

lookupVar :: Var -> NormM Atom
lookupVar v = do
  env <- ask
  return $ case envLookup env v of
     Nothing    -> Var v
     Just (L x) -> x
     Just (T _) -> error $ "Lookup failed: " ++ pprint v

normalizeLam :: FLamExpr -> NormM LamExpr
normalizeLam (FLamExpr p body) = do
  b <- normalizePat p
  buildLam b $ \x -> do
    env <- bindPat p x
    extendR env $ normalize body

normalizePat :: Pat -> NormM Var
normalizePat p = do
  ty <- liftM getType $ traverse (traverse substTy) p
  let v' = case toList p of (v:>_):_ -> v
                            []       -> "_"
  return $ v':>ty

bindPat :: Pat -> Atom -> NormM SubstEnv
bindPat (RecLeaf v) x = return $ v @> L x
bindPat (RecTree r) xs =
  liftM fold $ flip traverse (recNameVals r) $ \(i, p) -> do
    x <- nRecGet xs i
    bindPat p x

normalizeDecl :: FDecl -> NormM SubstEnv
normalizeDecl decl = case decl of
  LetMono p bound -> do
    xs <- normalize bound  -- TODO: preserve names
    bindPat p xs
  LetPoly v (FTLam tvs body) -> do
    tlam <- buildTLam tvs $ \tys -> do
      let env = fold [tv @> T ty | (tv, ty) <- zip tvs tys]
      extendR env $ normalize body
    return $ v @> L tlam
  TyDef v ty -> do
    ty' <- substTy ty
    return $ v @> T ty'
  FRuleDef _ _ _ -> return mempty  -- TODO

substTy :: Type -> NormM Type
substTy ty = do
  env <- ask
  return $ subst (env, mempty) ty
