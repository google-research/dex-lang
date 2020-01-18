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
import Subst
import Record

data TLamEnv = TLamContents NormEnv [TBinder] Expr
type NormEnv = FullEnv (Either NAtom TLamEnv) Type
type NormM a = ReaderT NormEnv (NEmbedT (Either Err)) a

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

asTopPassM :: NormM a -> TopPassM (NormEnv, Scope) (a, [NDecl])
asTopPassM m = do
  (env, scope) <- look
  (ans, (scope', decls)) <- liftExceptTop $ runEmbedT (runReaderT m env) scope
  extend (asSnd (scope'))
  return (ans, decls)

normalize :: Expr -> NormM NExpr
normalize expr = case expr of
  Lit x -> return $ NAtom $ NLit x
  Var v _ ts -> do
    x <- asks $ fromL . (! v)
    case x of
      Left x' -> case ts of
        [] -> return $ NAtom x'
        _ -> error "Unexpected type application"
      Right (TLamContents env tbs body) -> do
        ts' <- mapM substTy ts
        let env' = foldMap tbind $ zipWith replaceAnnot tbs ts'
        local (const (env <> env')) $ normalize body
  PrimOp Scan _ [x, For ip (Lam _ p body)] -> do
    xs <- atomize x
    (i:>idxTy) <- normalizePat ip
    let ibs = map (i:>) $ flattenIdxType idxTy
    b  <- normalizePat p
    buildNestedNScans ibs b xs $ \idxs carry -> do
      let idxs' = restructureIdx idxTy idxs
      withBindPat ip idxs' $ withBindPat p carry $ normalize body
  PrimOp b ts xs -> do
    ts' <- mapM substTy ts
    xs' <- mapM atomize xs
    normalizePrimOp b ts' xs'
  Decl (DoBind p bound) body -> do
    b <- normalizePat p
    m <- atomize bound
    f <- buildNLam [b] $ \[x] -> withBindPat p x $ normalize body
    return $ NAtom (NDoBind m f)
  Decl decl body -> do
    env <- normalizeDecl decl
    extendR env $ normalize body
  Lam l p body -> do
    b <- normalizePat p
    f <- buildNLam [b] $ \[x] -> withBindPat p x $ normalize body
    return $ NAtom (NLam l f)
  App f x -> liftM2 NApp (atomize f) (atomize x)
  For p body -> do
    b <- normalizePat p
    buildNFor b $ \i -> withBindPat p i $ normalize body
  Get e i -> do
    e' <- atomize e
    i' <- atomize i
    return $ NAtom $ NGet e' i'
  RecCon k r -> liftM (NAtom . NRecCon k) $ traverse atomize r
  TabCon (TabType (IdxSetLit n) ty) rows -> do
    ty' <- substTy ty
    rows'  <- mapM (normalize >=> emit) rows
    liftM NAtom $ emit $ NTabCon (IdxSetLit n) ty' rows'
  IdxLit n i -> return $ NPrimOp IntAsIndex [IdxSetLit n] [NLit (IntLit i)]
  _ -> error $ "Can't yet normalize: " ++ pprint expr

normalizePrimOp :: Builtin -> [Type] -> [NAtom] -> NormM NExpr
normalizePrimOp builtin tyArgs args = case builtin of
  NewtypeCast ->
    if a == b then return $ NAtom x
              else error $ "Can't cast " ++ pprint a
                               ++ " to " ++ pprint b
    where [a, b] = tyArgs
          [x] = args
  Select -> liftM NAtom $ selectAt p ty x y
    where [ty] = tyArgs
          [p, x, y] = args
  VAdd -> liftM NAtom $ addAt ty x y
    where [ty] = tyArgs
          [x, y] = args
  VZero -> liftM NAtom $ zeroAt ty  where [ty] = tyArgs
  _ -> if isAtomicBuiltin builtin
        then return $ NAtom (NAtomicPrimOp builtin tyArgs args)
        else return $ NPrimOp builtin tyArgs args

atomize :: Expr -> NormM NAtom
atomize expr = normalize expr >>= emit

normalizePat :: Pat -> NormM NBinder
normalizePat p = do
  ty <- liftM patType $ traverse (traverse substTy) p
  let v' = case toList p of (v:>_):_ -> v
                            []       -> "_"
  return $ v':>ty

flattenIdxType :: Type -> [Type]
flattenIdxType (RecType _ r) = foldMap flattenIdxType r
flattenIdxType ty = [ty]

restructureIdx :: Type -> [NAtom] -> NAtom
restructureIdx (RecType m r) xs =
  NRecCon m $ fmap (uncurry restructureIdx) $ listIntoRecord r xs
restructureIdx _ [x] = x
restructureIdx ty _ = error $ "Unexpected type " ++ pprint ty

bindPat :: Pat -> NAtom -> NormM NormEnv
bindPat (RecLeaf (v:>_)) x = return $ v @> L (Left x)
bindPat (RecTree r) xs =
  liftM fold $ flip traverse (recNameVals r) $ \(i, p) -> do
    x <- nRecGet xs i
    bindPat p x

withBindPat :: Pat -> NAtom -> NormM a -> NormM a
withBindPat p x m = do
  env <- bindPat p x
  extendR env m

normalizeDecl :: Decl -> NormM NormEnv
normalizeDecl decl = case decl of
  LetMono p bound -> do
    bs <- normalizePat p
    bound' <- buildScoped $ normalize bound
    xs <- emitTo bs bound'
    bindPat p xs
  LetPoly (v:>_) (TLam tbs body) -> do
    env <- ask
    return $ v @> L (Right (TLamContents env tbs body))
  Unpack b tv bound -> do
    bound' <- buildScoped $ normalize bound
    (ty, emitUnpackRest) <- emitUnpack tv bound'
    let tenv = tv @> T ty
    bs <- extendR tenv $ normalizePat (RecLeaf b)
    xs <- emitUnpackRest bs
    lenv <- bindPat (RecLeaf b) xs
    return (tenv <> lenv)
  TyDef NewType v _ ty -> do
    ty' <- substTy ty
    return $ v @> T ty'
  TyDef TyAlias _ _ _ -> error "Shouldn't have TAlias left"
  DoBind _ _          -> error "Shouldn't have DoBind here"

substTy :: Type -> NormM Type
substTy ty = do
  env <- ask
  return $ subst (envMapMaybe f env, mempty) ty
  where
    f :: LorT (Either NAtom TLamEnv) Type -> Maybe (LorT (Either Name TLam) Type)
    f (L _) = Nothing
    f (T t) = Just (T t)
