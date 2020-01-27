-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Normalize (normalizePass, normalizeVal) where

import Control.Monad
import Control.Monad.Reader
import Data.Foldable

import Env
import Syntax
import Cat
import PPrint
import Type
import Pass
import Embed
import Subst
import Record

data TLamEnv = TLamContents NormEnv [TBinder] FExpr
type NormEnv = FullEnv (Either Atom TLamEnv) Type
type NormM a = ReaderT NormEnv (EmbedT (Either Err)) a

-- TODO: add top-level freshness scope to top-level env
normalizePass :: TopPass TopDecl NTopDecl
normalizePass = TopPass $ \topDecl -> case topDecl of
  TopDecl ann decl -> do
    (env, decls) <- asTopPassM (normalizeDecl decl)
    extend (asFst env)
    return $ map (NTopDecl ann) decls
  RuleDef ann (Forall [] ty) (TLam [] expr) -> do
    (expr', _) <- asTopPassM $ buildScoped $ normalize expr
    (ty'  , _) <- asTopPassM $ substTy ty
    return [NRuleDef ann ty' expr']
  RuleDef _ _ _ -> error "Not implemented"
  EvalCmd (Command cmd expr) -> do
    let ty = getType expr
    (expr', _) <- asTopPassM $ buildScoped $ normalize expr
    case cmd of
      ShowNormalized -> emitOutput $ TextOut $ pprint expr'
      _ -> return [NEvalCmd (Command cmd (ty, expr'))]

asTopPassM :: NormM a -> TopPassM (NormEnv, Scope) (a, [Decl])
asTopPassM m = do
  (env, scope) <- look
  (ans, (scope', decls)) <- liftExceptTop $ runEmbedT (runReaderT m env) scope
  extend (asSnd (scope'))
  return (ans, decls)

normalizeVal :: FExpr -> Except Atom
normalizeVal expr = do
  (ans, (_, decls)) <- runEmbedT (runReaderT (normalize expr) mempty) mempty
  case decls of [] -> return ans
                _  -> throw MiscErr "leftover decls"

normalize :: FExpr -> NormM Atom
normalize expr = case expr of
  FDecl decl body -> do
    env <- normalizeDecl decl
    extendR env $ normalize body
  FVar v _ ts -> do
    x <- asks $ fromL . (! v)
    case x of
      Left x' -> case ts of
        [] -> return x'
        _ -> error "Unexpected type application"
      Right (TLamContents env tbs body) -> do
        ts' <- mapM substTy ts
        let env' = foldMap tbind $ zipWith replaceAnnot tbs ts'
        local (const (env <> env')) $ normalize body
  -- TODO: expand typeclasses in a separate post-normalization pass
  FPrimExpr (PrimOpExpr (For (FLamExpr p body))) -> do
    b <- normalizePat p
    buildFor b $ \x -> do
      env <- bindPat p x
      extendR env (normalize body)
  FPrimExpr (PrimOpExpr op) -> do
    op' <- traverseExpr op substTy normalize normalizeLam
    case op' of
      Select ty p x y -> selectAt ty p x y
      NewtypeCast ty x | ty == getType x -> return x
                       | otherwise -> error $ "Can't cast " ++ pprint (getType x)
                                                  ++ " to " ++ pprint ty
      _ -> emit op'
  FPrimExpr (PrimConExpr con) ->
    liftM PrimCon $ traverseExpr con substTy normalize normalizeLam
  Annot    e _ -> normalize e
  SrcAnnot e _ -> normalize e

normalizeLam :: FLamExpr -> NormM LamExpr
normalizeLam (FLamExpr p body) = do
  b <- normalizePat p
  buildLam b $ \x -> do
    env <- bindPat p x
    extendR env $ normalize body

normalizePat :: Pat -> NormM Binder
normalizePat p = do
  ty <- liftM getType $ traverse (traverse substTy) p
  let v' = case toList p of (v:>_):_ -> v
                            []       -> "_"
  return $ v':>ty

bindPat :: Pat -> Atom -> NormM NormEnv
bindPat (RecLeaf (v:>_)) x = return $ v @> L (Left x)
bindPat (RecTree r) xs =
  liftM fold $ flip traverse (recNameVals r) $ \(i, p) -> do
    bindPat p $ nRecGet xs i

normalizeDecl :: FDecl -> NormM NormEnv
normalizeDecl decl = case decl of
  LetMono p bound -> do
    xs <- normalize bound  -- TODO: preserve names
    bindPat p xs
  LetPoly (v:>_) (TLam tbs body) -> do
    env <- ask
    return $ v @> L (Right (TLamContents env tbs body))
  FUnpack b tv bound -> do
    bound' <- normalize bound
    (ty, emitUnpackRest) <- emitUnpack tv bound'
    let tenv = tv @> T ty
    bs <- extendR tenv $ normalizePat (RecLeaf b)
    x <- emitUnpackRest bs
    lenv <- bindPat (RecLeaf b) x
    return (tenv <> lenv)
  TyDef NewType v _ ty -> do
    ty' <- substTy ty
    return $ v @> T ty'
  TyDef TyAlias _ _ _ -> error "Shouldn't have TAlias left"

substTy :: Type -> NormM Type
substTy ty = do
  env <- ask
  return $ subst (envMapMaybe f env, mempty) ty
  where
    f :: LorT (Either Atom TLamEnv) Type -> Maybe (LorT a Type)
    f (L _) = Nothing
    f (T t) = Just (T t)
