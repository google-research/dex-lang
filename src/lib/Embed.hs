-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Embed (emit, emitTo, withBinders, buildNLam, buildNScan, buildNestedNScans,
              NEmbedT, NEmbed, NEmbedEnv, NEmbedScope, buildScoped, askType,
              wrapNDecls, runEmbedT, runEmbed, emitUnpack, nGet, wrapAtomicFor,
              buildNAtomicFor, zeroAt, addAt, sumAt, sumsAt) where

import Control.Monad
import Data.List (transpose)

import Env
import Fresh
import Syntax
import Cat
import Type
import Subst

type NEmbedT m = CatT NEmbedEnv m  -- TODO: consider a full newtype wrapper
type NEmbed = Cat NEmbedEnv
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
    emitTo (map ("v":>) tys) expr

-- Promises to make a new decl with given names (maybe with different counter).
emitTo :: MonadCat NEmbedEnv m => [NBinder] -> NExpr -> m [NAtom]
emitTo [] _ = return []
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

buildNAtomicFor :: (MonadCat NEmbedEnv m) =>
                     NBinder -> (NAtom -> m NAtom) -> m NAtom
buildNAtomicFor ib f = do
  ~(body, [ib'@(i':>_)], _) <- withBinders [ib] (\[x] -> f x) -- TODO: fail if nonempty decls
  return $ case body of
    NGet e (NVar i) | i == i' && not (isin i (freeVars e)) -> e
    _ -> NAtomicFor ib' body

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

runEmbed :: Cat NEmbedEnv a -> NEmbedScope -> (a, NEmbedEnv)
runEmbed m scope = runCat m (scope, [])

-- TODO: `(x,y) = e; (x,y)` --> `e`  optimization
wrapNDecls :: [NDecl] -> NExpr -> NExpr
wrapNDecls [] expr = expr
wrapNDecls (decl:decls) expr = NDecl decl (wrapNDecls decls expr)

nGet :: NAtom -> NAtom -> NAtom
nGet (NAtomicFor (v:>_) body) i = nSubst (v@>L i, scope) body
  where scope = fmap (const ()) (freeVars i)
nGet e i = NGet e i

wrapAtomicFor :: NBinder -> [NBinder] -> NAtom -> NAtom
wrapAtomicFor b@(i:>_) bs atom = NAtomicFor b atom'
  where atom' = nSubst (env, mempty) atom
        env = foldMap (\(v:>_) -> v @> L (NGet (NVar v) (NVar i))) bs

zeroAt :: MonadCat NEmbedEnv m => NType -> m NAtom
zeroAt (NBaseType RealType) = return $ NLit (RealLit 0.0)
zeroAt _ = error "Not implemented"

addAt :: MonadCat NEmbedEnv m => NType -> NAtom -> NAtom -> m NExpr
addAt (NBaseType RealType) x y = return $ NPrimOp FAdd [] [x, y]
addAt _ _ _ = error "Not implemented"

sumAt :: MonadCat NEmbedEnv m => NType -> [NAtom] -> m NAtom
sumAt ty [] = zeroAt ty
sumAt _ [x] = return x
sumAt ty (x:xs) = do
  xsSum <- sumAt ty xs
  ~[ans] <- addAt ty xsSum x >>= emit
  return ans

sumsAt :: MonadCat NEmbedEnv m => [NType] -> [NExpr] -> m NExpr
sumsAt tys xss = do
  xss' <- liftM transpose $ mapM emit xss
  liftM NAtoms $ sequence [sumAt ty xs | (ty, xs) <- zip tys xss']
