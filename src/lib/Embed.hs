-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Embed (emit, emitTo, withBinders, buildNLam, buildNScan, buildNestedNScans,
              NEmbedT, NEmbed, NEmbedEnv, NEmbedScope, buildScoped, askType, askAtomType,
              wrapNDecls, runEmbedT, runEmbed, emitUnpack, nGet, flipIdx,
              buildNAtomicFor, zeroAt, addAt, sumAt, sumsAt, deShadow,
              emitOneAtom, emitNamed, materializeAtom, add, mul, sub, neg, div') where

import Control.Monad
import Data.List (transpose)

import Env
import Fresh
import Syntax
import Cat
import Type
import Subst
import PPrint

type NEmbedT m = CatT NEmbedEnv m  -- TODO: consider a full newtype wrapper
type NEmbed = Cat NEmbedEnv
type NEmbedScope = FullEnv NType ()
type NEmbedEnv = (NEmbedScope, [NDecl])

-- Only produces atoms without binders (i.e. no NLam or NAtomicFor) so that we
-- don't have to deshadow them again later wrt newly in scope variables.
-- TODO: use suggestive names based on types (e.g. "f" for function)
emit :: MonadCat NEmbedEnv m => NExpr -> m [NAtom]
emit expr = emitNamed "v" expr

emitNamed :: MonadCat NEmbedEnv m => Name -> NExpr -> m [NAtom]
emitNamed v expr = case expr of
  NAtoms atoms | all noBinders atoms -> return atoms
  _ -> do
    tys <- askType expr
    -- TODO: use suggestive names based on types (e.g. "f" for function)
    emitTo (map (v:>) tys) expr

-- Promises to make a new decl with given names (maybe with different counter).
emitTo :: MonadCat NEmbedEnv m => [NBinder] -> NExpr -> m [NAtom]
emitTo [] _ = return []
emitTo bs expr = do
  bs' <- traverse freshenNBinder bs
  extend $ asSnd [NLet bs' expr]
  return [NVar v | v:>_ <- bs']

deShadow :: MonadCat NEmbedEnv m => NSubst a => a -> m a
deShadow x = do
  scope <- looks fst
  return $ nSubst (mempty, fmap (const ()) scope) x

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
                 [NBinder] -> ([NAtom] -> m a) -> m (a, [NBinder], NEmbedEnv)
withBinders bs f = do
  ((ans, bs'), env) <- scoped $ do
      bs' <- traverse freshenNBinder bs
      ans <- f [NVar v | v:>_ <- bs']
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
  ~(body, (ib':xbs'), (_, decls)) <- withBinders (ib:xbs) $ \(i:xs) -> f i xs
  return $ NScan ib' xbs' xsInit (wrapNDecls decls body)

buildScoped :: (MonadCat NEmbedEnv m) => m NExpr -> m NExpr
buildScoped m = do
  (body, (_, decls)) <- scoped m
  return $ wrapNDecls decls body

askType :: (MonadCat NEmbedEnv m) => NExpr -> m [NType]
askType expr = do
  tyEnv <- looks fst
  return $ getNExprType tyEnv expr

askAtomType :: (MonadCat NEmbedEnv m) => NAtom -> m NType
askAtomType x = liftM head $ askType $ NAtoms [x]

materializeAtom :: (MonadCat NEmbedEnv m) => NAtom -> m NAtom
materializeAtom atom = case atom of
  NAtomicFor ib@(iv:>_) body -> do
    ans <- buildNScan ib [] [] $ \i _ -> do
      scope <- liftM (fmap (const ())) $ looks fst  -- really only need `i` in scope
      body' <- materializeAtom $ nSubst (iv @> L i, scope) body
      return $ NAtoms [body']
    emitOneAtom ans
  NLam _ _ _ -> error $ "Can't materialize lambda"
  _ -> return atom

runEmbedT :: Monad m => CatT NEmbedEnv m a -> NEmbedScope -> m (a, NEmbedEnv)
runEmbedT m scope = runCatT m (scope, [])

runEmbed :: Cat NEmbedEnv a -> NEmbedScope -> (a, NEmbedEnv)
runEmbed m scope = runCat m (scope, [])

wrapNDecls :: [NDecl] -> NExpr -> NExpr
wrapNDecls [] expr = expr
wrapNDecls [NLet [v:>_] expr] (NAtoms [NVar v']) | v == v' = expr  -- optimization
wrapNDecls (decl:decls) expr = NDecl decl (wrapNDecls decls expr)

atomAsNExpr :: NAtom -> NExpr
atomAsNExpr x = NAtoms [x]

nGet :: NAtom -> NAtom -> NAtom
nGet (NAtomicFor (v:>_) body) i = nSubst (v@>L i, scope) body
  where scope = fmap (const ()) (freeVars i)
nGet e i = NGet e i

flipIdx :: MonadCat NEmbedEnv m => NAtom -> m NAtom
flipIdx i = do
  n <- askAtomType i
  iInt  <- emitOneAtom $ NPrimOp IndexAsInt [[n]] [i]
  nInt  <- emitOneAtom $ NPrimOp IdxSetSize [[n]] []
  nInt' <- isub nInt (NLit (IntLit 1))
  iFlipped <- isub nInt' iInt
  emitOneAtom $ NPrimOp IntAsIndex [[n]] [iFlipped]

isub :: MonadCat NEmbedEnv m => NAtom -> NAtom -> m NAtom
isub x y = emitOneAtom $ NPrimOp ISub [] [x, y]

zeroAt :: MonadCat NEmbedEnv m => NType -> m NAtom
zeroAt (NBaseType RealType) = return $ NLit (RealLit 0.0)
-- TODO: is there a problem that we're emitting binders here?
zeroAt (NTabType n a) = do
  body <- zeroAt a
  ans <- buildNFor ("_":>n) $ \_ -> return (atomAsNExpr body)
  emitOneAtom ans
zeroAt ty = error $ "Zeros not implemented for " ++ pprint ty

addAt :: MonadCat NEmbedEnv m => NType -> NAtom -> NAtom -> m NAtom
addAt (NBaseType RealType) x y = do
  emitOneAtom $ NPrimOp FAdd [] [x, y]
addAt (NTabType n a) x y = do
  ans <- buildNFor ("i":>n) $ \i -> liftM atomAsNExpr $ addAt a (nGet x i) (nGet y i)
  emitOneAtom ans
addAt _ _ _ = error "Not implemented"

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

div' :: MonadCat NEmbedEnv m => NAtom -> NAtom -> m NAtom
div' x y = emitOneAtom $ NPrimOp FDiv [] [x, y]

emitOneAtom :: MonadCat NEmbedEnv m => NExpr -> m NAtom
emitOneAtom expr = liftM head $ emit expr

type NAtomProd = NAtom  -- the thing we're trying to zip/fold over

embedZipWith :: MonadCat NEmbedEnv m
                  => (NType -> NAtom -> NAtom -> m NAtom)
                  -> [NType] -> [NAtomProd] -> [NAtomProd] -> m [NAtomProd]
embedZipWith f ty x y = undefined

embedFold :: MonadCat NEmbedEnv m
               => (NType -> NAtom -> [NAtom] -> m [NAtom])
               -> NType -> NAtomProd -> [NAtom] -> m [NAtom]
embedFold f ty initCarry xs = undefined
