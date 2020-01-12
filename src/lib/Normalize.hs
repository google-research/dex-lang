-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Normalize (normalizePass) where

import Control.Monad
import Control.Monad.Reader
import Data.Foldable
import Data.List (transpose)

import Env
import Syntax
import Cat
import PPrint
import Type
import Pass
import Embed
import Subst

data TLamEnv = TLamContents NormEnv [TBinder] Expr
type NormEnv = FullEnv (Either [NAtom] TLamEnv) [NType]
type NormM a = ReaderT NormEnv (NEmbedT (Either Err)) a

-- TODO: add top-level freshness scope to top-level env
normalizePass :: TopPass TopDecl NTopDecl
normalizePass = TopPass $ \topDecl -> case topDecl of
  TopDecl ann decl -> do
    (env, decls) <- asTopPassM (normalizeDecl decl)
    extend (asFst env)
    return $ map (NTopDecl ann) decls
  RuleDef ann (Forall [] ty) (TLam [] expr) -> do
    (expr', _)  <- asTopPassM $ buildScoped $ normalize expr
    ~([ty'], _) <- asTopPassM $ normalizeTy ty
    return [NRuleDef ann ty' expr']
  RuleDef _ _ _ -> error "Not implemented"
  EvalCmd (Command cmd expr) -> do
    let ty = getType expr
    (expr', _) <- asTopPassM $ buildScoped $ normalize expr
    case cmd of
      ShowNormalized -> emitOutput $ TextOut $ pprint expr'
      _ -> return [NEvalCmd (Command cmd (ty, expr'))]

asTopPassM :: NormM a -> TopPassM (NormEnv, Scope) (a, [NDecl])
asTopPassM m = do
  (env, scope) <- look
  (ans, (scope', decls)) <- liftExceptTop $ runEmbedT (runReaderT m env) scope
  extend (asSnd (scope'))
  return (ans, decls)

normalize :: Expr -> NormM NExpr
normalize expr = case expr of
  Lit x -> return $ NAtoms [NLit x]
  Var v _ ts -> do
    x <- asks $ fromL . (! v)
    case x of
      Left xs -> case ts of
        [] -> return $ NAtoms xs
        _ -> error "Unexpected type application"
      Right (TLamContents env tbs body) -> do
        ts' <- mapM normalizeTy ts
        let env' = foldMap tbind $ zipWith replaceAnnot tbs ts'
        local (const (env <> env')) $ normalize body
  PrimOp Scan _ [x, For ip (Lam _ p body)] -> do
    xs <- atomize x
    (ibs, iToEnv) <- normalizePat ip
    (bs , toEnv ) <- normalizePat p
    buildNestedNScans ibs bs xs $ \idxs carry ->
      extendR (iToEnv idxs <> toEnv carry) (normalize body)
  PrimOp b ts xs -> do
    ts' <- mapM normalizeTy ts
    xs' <- mapM atomize xs
    normalizePrimOp b ts' xs'
  Decl decl body -> do
    env <- normalizeDecl decl
    extendR env $ normalize body
  Lam ~(Mult l) p body -> do
    (bs, toEnv) <- normalizePat p
    f <- buildNLam l bs $ \xs -> extendR (toEnv xs) (normalize body)
    return $ NAtoms [f]
  App f x -> do
    ~[f'] <- atomize f
    x'    <- atomize x
    return $ NApp f' x'
  For p body -> do
    (bs, toEnv) <- normalizePat p
    buildNestedNScans bs [] [] $ \idxs _ ->
      extendR (toEnv idxs) (normalize body)
  Get e i -> do
    e' <- atomize e
    i' <- atomize i
    return $ NAtoms $ map (\x -> foldl NGet x i') e'
  RecCon _ r -> do
    r' <- traverse atomize r
    return $ NAtoms $ concat r'
  TabCon (TabType (IdxSetLit n) ty) rows -> do
    ts' <- normalizeTy ty
    rows'  <- mapM (normalize >=> emit) rows
    let tabExprs = zipWith (NTabCon (NIdxSetLit n)) ts' (transpose rows')
    liftM NAtoms $ mapM emitOneAtom tabExprs
  IdxLit n i -> return $ NPrimOp IntAsIndex [[NIdxSetLit n]] [NLit (IntLit i)]
  _ -> error $ "Can't yet normalize: " ++ pprint expr

normalizePrimOp :: Builtin -> [[NType]] -> [[NAtom]] -> NormM NExpr
normalizePrimOp builtin tyArgs args = case builtin of
  NewtypeCast ->
    if a == b then return $ NAtoms [x]
              else error $ "Can't cast " ++ pprint a
                               ++ " to " ++ pprint b
    where [a, b] = tyArgs
          [[x]] = args
  Select -> liftM NAtoms $ sequence $ zipWith3 (selectAt p) tys xs ys
    where [tys] = tyArgs
          [[p], xs, ys] = args
  VAdd -> liftM NAtoms $ sequence $ zipWith3 addAt tys xs ys
    where [tys] = tyArgs
          [xs, ys] = args
  VZero -> liftM NAtoms $ mapM zeroAt tys
    where [tys] = tyArgs
  _ -> return $ NPrimOp builtin tyArgs (concat args)

atomize :: Expr -> NormM [NAtom]
atomize expr = normalize expr >>= emit

normalizePat :: Traversable f => f Binder -> NormM ([NBinder], [NAtom] -> NormEnv)
normalizePat p = do
  p' <- traverse (traverse normalizeTy) p
  let bs = fold (fmap flattenBinder p')
  return (bs, bindPat p')
  where
    flattenBinder :: BinderP [NType] -> [NBinder]
    flattenBinder (v:>ts) = map (v:>) ts

bindPat :: Traversable f => f (BinderP [a]) -> [NAtom] -> NormEnv
bindPat p xs = fst $ foldl addBinder (mempty, xs) p
  where
    addBinder :: (NormEnv, [NAtom]) -> BinderP [a] -> (NormEnv, [NAtom])
    addBinder (env, xs') (v:>ts) = (env <> (v @> L (Left cur)), rest)
      where (cur, rest) = splitAt (length ts) xs'

normalizeDecl :: Decl -> NormM NormEnv
normalizeDecl decl = case decl of
  LetMono p bound -> do
    (bs, toEnv) <- normalizePat p
    bound' <- buildScoped $ normalize bound
    xs <- emitTo bs bound'
    return $ toEnv xs
  LetPoly (v:>_) (TLam tbs body) -> do
    env <- ask
    return $ v @> L (Right (TLamContents env tbs body))
  Unpack b tv bound -> do
    bound' <- buildScoped $ normalize bound
    (ty, emitUnpackRest) <- emitUnpack tv bound'
    let tenv = tv @> T [ty]
    (bs, toEnv) <- extendR tenv $ normalizePat [b]
    xs <- emitUnpackRest bs
    return (tenv <> toEnv xs)
  TyDef NewType v _ ty -> do
    ty' <- normalizeTy ty
    return $ v @> T ty'
  TyDef TyAlias _ _ _ -> error "Shouldn't have TAlias left"

normalizeTy :: Type -> NormM [NType]
normalizeTy ty = case ty of
  BaseType b -> return [NBaseType b]
  TypeVar v -> asks $ fromT . (!v)
  ArrType ~(Mult l) a b -> do
    a' <- normalizeTy a
    b' <- normalizeTy b
    return [NArrType l (toList a') (toList b')]
  TabType a b -> do
    a' <- normalizeTy a
    b' <- normalizeTy b
    return $ fmap (\x -> foldr NTabType x a') b'
  RecType _ r -> liftM fold $ traverse normalizeTy r
  Exists body -> do
    body' <- normalizeTy body
    return [NExists (toList body')]
  IdxSetLit x -> return [NIdxSetLit x]
  BoundTVar n -> return [NBoundTVar n]
  TypeApp _ _ -> error "Shouldn't have type application left"
  Mult _      -> error "Shouldn't be normalizing multiplicity"
