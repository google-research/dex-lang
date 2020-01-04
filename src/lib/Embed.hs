-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Embed (emit, emitTo, withBinders, buildNLam, buildNScan, buildNestedNScans,
              NEmbedT, NEmbed, NEmbedEnv, buildScoped, wrapNDecls, runEmbedT,
              runEmbed, emitUnpack, nGet, flipIdx,
              buildNAtomicFor, zeroAt, addAt, sumAt, sumsAt, deShadow,
              emitOneAtom, emitNamed, materializeAtom, add, mul, sub, neg, div',
              selectAt) where

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
type NEmbedEnv = (Scope, [NDecl])

-- Only produces atoms without binders (i.e. no NLam or NAtomicFor) so that we
-- don't have to deshadow them again later wrt newly in scope variables.
-- TODO: use suggestive names based on types (e.g. "f" for function)
emit :: MonadCat NEmbedEnv m => NExpr -> m [NAtom]
emit expr = emitNamed "v" expr

emitNamed :: MonadCat NEmbedEnv m => Name -> NExpr -> m [NAtom]
emitNamed v expr = case expr of
  NAtoms atoms | all noBinders atoms -> return atoms
  -- TODO: use suggestive names based on types (e.g. "f" for function)
  _ -> emitTo (map (v:>) (getNExprType expr)) expr

-- Promises to make a new decl with given names (maybe with different counter).
emitTo :: MonadCat NEmbedEnv m => [NBinder] -> NExpr -> m [NAtom]
emitTo [] _ = return []
emitTo bs expr = do
  bs' <- traverse freshenNBinder bs
  extend $ asSnd [NLet bs' expr]
  return $ map binderToVar bs'

deShadow :: MonadCat NEmbedEnv m => NSubst a => a -> m a
deShadow x = do
  scope <- looks fst
  return $ nSubst (mempty, scope) x

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
  extend $ asFst (tv' @> ())
  let finish bs = do bs' <- traverse freshenNBinder bs
                     extend $ asSnd [NUnpack bs' tv' expr]
                     return [NVar v ty | v:>ty <- bs']
  return (NTypeVar tv', finish)

freshenNBinder :: MonadCat NEmbedEnv m => NBinder -> m NBinder
freshenNBinder (v:>ty) = do
  scope <- looks fst
  let v' = rename v scope
  extend $ asFst (v' @> ())
  return (v':>ty)

withBinders :: (MonadCat NEmbedEnv m) =>
                 [NBinder] -> ([NAtom] -> m a) -> m (a, [NBinder], NEmbedEnv)
withBinders bs f = do
  ((ans, bs'), env) <- scoped $ do
      bs' <- traverse freshenNBinder bs
      ans <- f $ map binderToVar bs'
      return (ans, bs')
  return (ans, bs', env)

buildNLam :: (MonadCat NEmbedEnv m) =>
              Multiplicity -> [NBinder] -> ([NAtom] -> m NExpr) -> m NAtom
buildNLam l bs f = do
  (body, bs', (_, decls)) <- withBinders bs f
  return $ NLam l bs' $ wrapNDecls decls body

buildNFor :: (MonadCat NEmbedEnv m) => NBinder -> (NAtom -> m NExpr) -> m NExpr
buildNFor b f = buildNScan b [] [] $ \i _ -> f i

buildNAtomicFor :: (MonadCat NEmbedEnv m) =>
                     NBinder -> (NAtom -> m NAtom) -> m NAtom
buildNAtomicFor ib f = do
  ~(body, [ib'@(i':>_)], _) <- withBinders [ib] (\[x] -> f x) -- TODO: fail if nonempty decls
  return $ case body of
    NGet e (NVar i _) | i == i' && not (isin i (freeNVars e)) -> e
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
  ~(body, (ib':xbs'), (_, decls)) <- withBinders (ib:xbs) $ \(i:xs) -> f i xs
  return $ NScan ib' xbs' xsInit (wrapNDecls decls body)

buildScoped :: (MonadCat NEmbedEnv m) => m NExpr -> m NExpr
buildScoped m = do
  (body, (_, decls)) <- scoped m
  return $ wrapNDecls decls body

materializeAtom :: (MonadCat NEmbedEnv m) => NAtom -> m NAtom
materializeAtom atom = case atom of
  NAtomicFor ib@(iv:>_) body -> do
    ans <- buildNScan ib [] [] $ \i _ -> do
      scope <- looks fst  -- really only need `i` in scope
      body' <- materializeAtom $ nSubst (iv @> L i, scope) body
      return $ NAtoms [body']
    emitOneAtom ans
  NLam _ _ _ -> error $ "Can't materialize lambda"
  _ -> return atom

runEmbedT :: Monad m => CatT NEmbedEnv m a -> Scope -> m (a, NEmbedEnv)
runEmbedT m scope = runCatT m (scope, [])

runEmbed :: Cat NEmbedEnv a -> Scope -> (a, NEmbedEnv)
runEmbed m scope = runCat m (scope, [])

wrapNDecls :: [NDecl] -> NExpr -> NExpr
wrapNDecls [] expr = expr
wrapNDecls [NLet [v:>_] expr] (NAtoms [NVar v' _]) | v == v' = expr  -- optimization
wrapNDecls (decl:decls) expr = NDecl decl (wrapNDecls decls expr)

nGet :: NAtom -> NAtom -> NAtom
nGet (NAtomicFor (v:>_) body) i = nSubst (v@>L i, scope) body
  where scope = fmap (const ()) (freeNVars i)
nGet e i = NGet e i

flipIdx :: MonadCat NEmbedEnv m => NAtom -> m NAtom
flipIdx i = do
  let n = atomType i
  iInt  <- emitOneAtom $ NPrimOp IndexAsInt [[n]] [i]
  nInt  <- emitOneAtom $ NPrimOp IdxSetSize [[n]] []
  nInt' <- isub nInt (NLit (IntLit 1))
  iFlipped <- isub nInt' iInt
  emitOneAtom $ NPrimOp IntAsIndex [[n]] [iFlipped]

isub :: MonadCat NEmbedEnv m => NAtom -> NAtom -> m NAtom
isub x y = emitOneAtom $ NPrimOp ISub [] [x, y]

zeroAt :: MonadCat NEmbedEnv m => NType -> m NAtom
zeroAt ty = do
  ~[x] <- mapScalars (\_ _ -> return [NLit (RealLit 0.0)]) ty []
  return x

addAt :: MonadCat NEmbedEnv m => NType -> NAtom -> NAtom -> m NAtom
addAt ty xs ys = do
  ~[x] <- mapScalars (\_ [x, y] -> liftM pure (add x y)) ty [xs, ys]
  return x

selectAt :: MonadCat NEmbedEnv m => NAtom -> NType -> NAtom -> NAtom -> m NAtom
selectAt p ty xs ys = do
  ~[x] <- mapScalars (\t [x, y] -> liftM pure (select p t x y)) ty [xs, ys]
  return x

sumAt :: MonadCat NEmbedEnv m => NType -> [NAtom] -> m NAtom
sumAt ty [] = zeroAt ty
sumAt _ [x] = return x
sumAt ty (x:xs) = do
  xsSum <- sumAt ty xs
  addAt ty xsSum x

sumsAt :: MonadCat NEmbedEnv m => [NType] -> [NExpr] -> m NExpr
sumsAt tys xss = do
  xss' <- liftM transpose $ mapM emit xss
  liftM NAtoms $ sequence [sumAt ty xs | (ty, xs) <- zip tys xss']

neg :: MonadCat NEmbedEnv m => NAtom -> m NAtom
neg x = emitOneAtom $ NPrimOp FNeg [] [x]

add :: MonadCat NEmbedEnv m => NAtom -> NAtom -> m NAtom
add x y = emitOneAtom $ NPrimOp FAdd [] [x, y]

mul :: MonadCat NEmbedEnv m => NAtom -> NAtom -> m NAtom
mul x y = emitOneAtom $ NPrimOp FMul [] [x, y]

sub :: MonadCat NEmbedEnv m => NAtom -> NAtom -> m NAtom
sub x y = emitOneAtom $ NPrimOp FSub [] [x, y]

select :: MonadCat NEmbedEnv m => NAtom -> NType -> NAtom -> NAtom -> m NAtom
select p ty x y = emitOneAtom $ NPrimOp Select [[ty]] [p, x, y]

div' :: MonadCat NEmbedEnv m => NAtom -> NAtom -> m NAtom
div' x y = emitOneAtom $ NPrimOp FDiv [] [x, y]

binderToVar :: NBinder -> NAtom
binderToVar (v:>ty) = NVar v ty

emitOneAtom :: MonadCat NEmbedEnv m => NExpr -> m NAtom
emitOneAtom expr = liftM head $ emit expr

mapScalars :: MonadCat NEmbedEnv m
                     => (NType -> [NAtom] -> m [NAtom])
                     -> NType -> [NAtom] -> m [NAtom]
mapScalars f ty xs = case ty of
  NBaseType _ -> f ty xs
  NTabType n a -> do
    ans <- buildNFor ("i":>n) $ \i ->
             liftM NAtoms $ mapScalars f a [nGet x i | x <- xs]
    emit ans
  _ -> error "Not implemented"
