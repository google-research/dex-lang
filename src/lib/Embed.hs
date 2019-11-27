-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}

module Embed (emit, emitTo, withBinders, buildNLam, buildNScan, buildNestedNScans,
              NEmbedT, NEmbedEnv, NEmbedScope, buildScoped, askType, wrapNDecls,
              runEmbedT, emitUnpack) where

import Env
import Fresh
import Syntax
import Cat
import Type

type NEmbedT m = CatT NEmbedEnv m  -- TODO: consider a full newtype wrapper
type NEmbedScope = FullEnv NType ()
type NEmbedEnv = (NEmbedScope, [NDecl])

-- Only produces atoms without binders (i.e. no NLam or NAtomicFor) so that we
-- don't have to deshadow them again later wrt newly in scope variables.
emit :: MonadCat NEmbedEnv m => NExpr -> m [NAtom]
emit expr = case expr of
  NAtoms atoms | all noBinders atoms -> return atoms
  _ -> do
    tys <- askType expr
    -- TODO: use suggestive names based on types (e.g. "f" for function)
    emitTo (map (rawName "v" :>) tys) expr

-- Promises to make a new decl with given names (maybe with different counter).
emitTo :: MonadCat NEmbedEnv m => [NBinder] -> NExpr -> m [NAtom]
emitTo bs expr = do
  bs' <- traverse freshenNBinder bs
  extend $ asSnd [NLet bs' expr]
  return [NVar v | v:>_ <- bs']

noBinders :: NAtom -> Bool
noBinders atom = case atom of
  NLam _ _ _     -> False
  NAtomicFor _ _ -> False
  _              -> True

emitUnpack :: MonadCat NEmbedEnv m =>
                Name -> NExpr -> m (NType, [NBinder] -> m [NAtom])
emitUnpack tv expr = do
  scope <- looks fst
  let tv' = rename tv scope
  extend $ asFst (tv' @> T ())
  let finish bs = do bs' <- traverse freshenNBinder bs
                     extend $ asSnd [NUnpack bs' tv' expr]
                     return [NVar v | v:>_ <- bs']
  return (NTypeVar tv', finish)

freshenNBinder :: MonadCat NEmbedEnv m => NBinder -> m NBinder
freshenNBinder (v:>ty) = do
  scope <- looks fst
  let v' = rename v scope
  extend $ asFst (v' @> L ty)
  return (v':>ty)

withBinders :: (MonadCat NEmbedEnv m) =>
                 [NBinder] -> ([NAtom] -> m a) -> m (a, [NBinder], [NDecl])
withBinders bs f = do
  ((ans, bs'), (_, decls)) <- scoped $ do
      bs' <- traverse freshenNBinder bs
      ans <- f [NVar v | v:>_ <- bs']
      return (ans, bs')
  return (ans, bs', decls)

buildNLam :: (MonadCat NEmbedEnv m) =>
              Lin -> [NBinder] -> ([NAtom] -> m NExpr) -> m NAtom
buildNLam l bs f = do
  (body, bs', decls) <- withBinders bs f
  return $ NLam l bs' $ wrapNDecls decls body

buildNestedNScans :: (MonadCat NEmbedEnv m)
    => [NBinder]                           -- index binders
    -> [NBinder]                           -- state binders
    -> [NAtom]                             -- initial data
    -> ([NAtom] -> [NAtom] -> m NExpr) -- body of scan
    -> m NExpr
buildNestedNScans [] _ xsInit f = f [] xsInit
buildNestedNScans (ib:ibs) xbs xsInit f =
  buildNScan ib xbs xsInit $ \i xs ->
    buildNestedNScans ibs xbs xs (\is -> f (i:is))

buildNScan :: (MonadCat NEmbedEnv m)
               => NBinder -> [NBinder] -> [NAtom]
               -> (NAtom -> [NAtom] -> m NExpr) -> m NExpr
buildNScan ib xbs xsInit f = do
  ~(body, (ib':xbs'), decls) <- withBinders (ib:xbs) $ \(i:xs) -> f i xs
  return $ NScan ib' xbs' xsInit (wrapNDecls decls body)

buildScoped :: (MonadCat NEmbedEnv m) => m NExpr -> m NExpr
buildScoped m = do
  (body, (_, decls)) <- scoped m
  return $ wrapNDecls decls body

askType :: (MonadCat NEmbedEnv m) => NExpr -> m [NType]
askType expr = do
  tyEnv <- looks fst
  return $ getNExprType tyEnv expr

runEmbedT :: Monad m => CatT NEmbedEnv m a -> NEmbedScope -> m (a, NEmbedEnv)
runEmbedT m scope = runCatT m (scope, [])

-- TODO: `(x,y) = e; (x,y)` --> `e`  optimization
wrapNDecls :: [NDecl] -> NExpr -> NExpr
wrapNDecls [] expr = expr
wrapNDecls (decl:decls) expr = NDecl decl (wrapNDecls decls expr)
