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

import Env
import Syntax
import Cat
import PPrint
import Type
import Pass
import Embed

data TLamEnv = TLamContents NormEnv [TBinder] Expr
type NormSubEnv = FullEnv (Either [NAtom] TLamEnv) [NType]
type NormEnv = (TypeEnv, NormSubEnv)
type NormM a = ReaderT NormEnv (NEmbedT (Either Err)) a

-- TODO: add top-level freshness scope to top-level env
normalizePass :: TopPass TopDecl NTopDecl
normalizePass = TopPass $ \topDecl -> case topDecl of
  TopDecl ann decl -> do
    (env, decls) <- asTopPassM (normalizeDecl decl)
    extend (asFst env)
    case decls of
      [] -> emitOutput $ NoOutput
      [decl'] -> return $ NTopDecl ann decl'
      _ -> error "Multiple decls not implemented"
  RuleDef ann (Forall [] ty) (TLam [] expr) -> do
    (expr', _)  <- asTopPassM $ buildScoped $ normalize expr
    ~([ty'], _) <- asTopPassM $ normalizeTy ty
    return $ NRuleDef ann ty' expr'
  RuleDef _ _ _ -> error "Not implemented"
  EvalCmd (Command cmd expr) -> do
    tyEnv <- looks (fst . fst)
    let ty = getType tyEnv expr
    ((ntys, expr'), _) <- asTopPassM $ do
       expr' <- buildScoped $ normalize expr
       ntys <- askType expr'
       return (ntys, expr')
    case cmd of
      ShowNormalized -> emitOutput $ TextOut $ pprint expr'
      _ -> return $ NEvalCmd (Command cmd (ty, ntys, expr'))

asTopPassM :: NormM a -> TopPassM (NormEnv, NEmbedScope) (a, [NDecl])
asTopPassM m = do
  (env, scope) <- look
  (ans, (scope', decls)) <- liftExceptTop $ runEmbedT (runReaderT m env) scope
  extend (asSnd (scope'))
  return (ans, decls)

normalize :: Expr -> NormM NExpr
normalize expr = case expr of
  Lit x -> return $ NAtoms [NLit x]
  Var v ts -> do
    x <- asks $ fromL . (! v) . snd
    case x of
      Left xs -> case ts of
        [] -> return $ NAtoms xs
        _ -> error "Unexpected type application"
      Right (TLamContents env tbs body) -> do
        ts' <- mapM normalizeTy ts
        let env' = (foldMap tbind tbs,
                    foldMap tbind $ zipWith replaceAnnot tbs ts')
        local (const (env <> env')) $ normalize body
  PrimOp Scan _ [x, For ip (Lam _ p body)] -> do
    xs <- atomize x
    (ibs, iToEnv) <- normalizePat ip
    (bs , toEnv ) <- normalizePat p
    buildNestedNScans ibs bs xs $ \idxs carry ->
      extendR (iToEnv idxs <> toEnv carry) (normalize body)
  PrimOp NewtypeCast ~[a, b] ~[x] -> do
    a' <- normalizeTy a
    b' <- normalizeTy b
    if a' == b'
      then normalize x
      else error $ "Can't cast " ++ pprint a' ++ " to " ++ pprint b'
  -- TODO: expand functions like `==` over nonscalars
  PrimOp b ts xs -> do
    ts' <- mapM normalizeTy ts
    xs' <- liftM concat $ mapM atomize xs
    return $ NPrimOp b ts' xs'
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
    rows'  <- mapM normalize rows
    rows'' <- mapM deShadow rows'  -- Should we just make NTabCon an atom?
    return $ NTabCon (NIdxSetLit n) ts' rows''
  IdxLit n i -> return $ NPrimOp IntAsIndex [[NIdxSetLit n]] [NLit (IntLit i)]
  _ -> error $ "Can't yet normalize: " ++ pprint expr

atomize :: Expr -> NormM [NAtom]
atomize expr = normalize expr >>= emit

normalizePat :: Traversable f => f Binder -> NormM ([NBinder], [NAtom] -> NormEnv)
normalizePat p = do
  p' <- traverse (traverse normalizeTy) p
  let bs = fold (fmap flattenBinder p')
  let tyEnv = foldMap (\(v:>ty) -> v @> L (asSigma ty)) p
  return (bs, \xs -> (tyEnv, bindPat p' xs))
  where
    flattenBinder :: BinderP [NType] -> [NBinder]
    flattenBinder (v:>ts) = map (v:>) ts

bindPat :: Traversable f => f (BinderP [a]) -> [NAtom] -> NormSubEnv
bindPat p xs = fst $ foldl addBinder (mempty, xs) p
  where
    addBinder :: (NormSubEnv, [NAtom]) -> BinderP [a] -> (NormSubEnv, [NAtom])
    addBinder (env, xs') (v:>ts) = (env <> (v @> L (Left cur)), rest)
      where (cur, rest) = splitAt (length ts) xs'

normalizeDecl :: Decl -> NormM NormEnv
normalizeDecl decl = case decl of
  LetMono p bound -> do
    (bs, toEnv) <- normalizePat p
    bound' <- buildScoped $ normalize bound
    xs <- emitTo bs bound'
    return $ toEnv xs
  LetPoly (v:>ty) (TLam tbs body) -> do
    env <- ask
    return (v@>L ty, v@>L (Right (TLamContents env tbs body)))
  Unpack b tv bound -> do
    bound' <- buildScoped $ normalize bound
    (ty, emitUnpackRest) <- emitUnpack tv bound'
    let tenv = (tv @> T (Kind [IdxSet]), tv @> T [ty])
    (bs, toEnv) <- extendR tenv $ normalizePat [b]
    xs <- emitUnpackRest bs
    return (tenv <> toEnv xs)
  TyDef NewType v ty -> do
    ty' <- normalizeTy ty
    return (v @> T (Kind []), v @> T ty')
  TyDef TyAlias _ _ -> error "Shouldn't have TAlias left"

normalizeTy :: Type -> NormM [NType]
normalizeTy ty = case ty of
  BaseType b -> return [NBaseType b]
  TypeVar v -> asks $ fromT . (!v) . snd
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
  Mult _      -> error "Shouldn't be normalizing multiplicity"
