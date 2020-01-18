-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Embed (emit, emitTo, withBinder, buildNLam, buildNScan, buildNestedNScans,
              NEmbedT, NEmbed, NEmbedEnv, buildScoped, wrapNDecls, runEmbedT,
              runEmbed, emitUnpack, nGet, flipIdx, withBinders,
              buildNAtomicFor, zeroAt, addAt, sumAt, deShadow,
              emitNamed, materializeAtom, add, mul, sub, neg, div',
              selectAt, freshNVar, unitBinder, nUnitCon, buildNFor,
              nRecGet, recGetFst, recGetSnd, fromPair, fromTup, makePair) where

import Control.Monad
import Data.List (transpose)

import Env
import Fresh
import Syntax
import Cat
import Type
import Subst
import Record
import PPrint
import Data.Foldable (toList)

type NEmbedT m = CatT NEmbedEnv m  -- TODO: consider a full newtype wrapper
type NEmbed = Cat NEmbedEnv
type NEmbedEnv = (Scope, [NDecl])

-- Only produces atoms without binders (i.e. no NLam or NAtomicFor) so that we
-- don't have to deshadow them again later wrt newly in scope variables.
-- TODO: use suggestive names based on types (e.g. "f" for function)
emit :: MonadCat NEmbedEnv m => NExpr -> m NAtom
emit expr = emitNamed "v" expr

emitNamed :: MonadCat NEmbedEnv m => Name -> NExpr -> m NAtom
emitNamed v expr = case expr of
  NAtom atom | noBinders atom -> return atom
  -- TODO: use suggestive names based on types (e.g. "f" for function)
  _ -> emitTo (v:>getNExprType expr) expr

-- Promises to make a new decl with given names (maybe with different counter).
emitTo :: MonadCat NEmbedEnv m => NBinder -> NExpr -> m NAtom
emitTo b expr = do
  b' <- freshenNBinder b
  extend $ asSnd [NLet b' expr]
  return $ binderToVar b'

deShadow :: MonadCat NEmbedEnv m => NSubst a => a -> m a
deShadow x = do
   scope <- looks fst
   return $ nSubst (mempty, scope) x

noBinders :: NAtom -> Bool
noBinders atom = case atom of
  NLam _ _       -> False
  NAtomicFor _ _ -> False
  _              -> True

freshNVar :: MonadCat NEmbedEnv m => Name -> m Name
freshNVar v = do
  scope <- looks fst
  let v' = rename v scope
  extend $ asFst (v' @> ())
  return v'

emitUnpack :: MonadCat NEmbedEnv m
           => Name -> NExpr -> m (Type, NBinder -> m NAtom)
emitUnpack tv expr = do
  tv' <- freshNVar tv
  let finish b = do b'@(v:>ty) <- freshenNBinder b
                    extend $ asSnd [NUnpack b' tv' expr]
                    return $ NVar v ty
  return (TypeVar tv', finish)

freshenNBinder :: MonadCat NEmbedEnv m => NBinder -> m NBinder
freshenNBinder (v:>ty) = do
  v' <- freshNVar v
  return (v':>ty)

withBinder :: (MonadCat NEmbedEnv m)
           => NBinder -> (NAtom -> m a) -> m (a, NBinder, NEmbedEnv)
withBinder b f = do
  (ans, ~[b'], env) <- withBinders [b] (f . head)
  return (ans, b', env)

withBinders :: (MonadCat NEmbedEnv m)
            => [NBinder] -> ([NAtom] -> m a) -> m (a, [NBinder], NEmbedEnv)
withBinders bs f = do
  ((ans, bs'), env) <- scoped $ do
      bs' <- mapM freshenNBinder bs
      ans <- f $ map binderToVar bs'
      return (ans, bs')
  return (ans, bs', env)

buildNLam :: (MonadCat NEmbedEnv m) => [NBinder] -> ([NAtom] -> m NExpr) -> m NLamExpr
buildNLam bs f = do
  (body, bs', (_, decls)) <- withBinders bs f
  return $ NLamExpr bs' (wrapNDecls decls body)

buildNFor :: (MonadCat NEmbedEnv m) => NBinder -> (NAtom -> m NExpr) -> m NExpr
buildNFor ib f = do
  xb <- unitBinder
  scanAns <- buildNScan ib xb nUnitCon $ \i _ -> do
    ans <- f i >>= emit
    return $ NAtom $ makePair nUnitCon ans
  scanAns' <- emit scanAns
  liftM NAtom $ recGetSnd scanAns'

buildNAtomicFor :: (MonadCat NEmbedEnv m) =>
                     NBinder -> (NAtom -> m NExpr) -> m NAtom
buildNAtomicFor ib f = do
  ~(body, ib'@(i':>_), _) <- withBinder ib f -- TODO: fail if nonempty decls
  return $ case body of
    NAtom (NGet e (NVar i _)) | i == i' && not (isin i (freeVars e)) -> e
    _ -> NAtomicFor ib' body

buildNestedNScans :: (MonadCat NEmbedEnv m)
    => [NBinder]                         -- index binders
    -> NBinder                           -- state binder
    -> NAtom                             -- initial data
    -> ([NAtom] -> NAtom -> m NExpr) -- body of scan
    -> m NExpr
buildNestedNScans [] _ xsInit f = f [] xsInit
buildNestedNScans (ib:ibs) xbs xsInit f =
  buildNScan ib xbs xsInit $ \i xs ->
    buildNestedNScans ibs xbs xs (\is -> f (i:is))

buildNScan :: (MonadCat NEmbedEnv m)
           => NBinder -> NBinder -> NAtom
           -> (NAtom -> NAtom -> m NExpr) -> m NExpr
buildNScan ib xb xsInit f = do
  ~(body, [ib', xb'], (_, decls)) <- withBinders [ib, xb] $ \[i, xs] -> f i xs
  return $ NScan xsInit $ NLamExpr [ib', xb'] (wrapNDecls decls body)

buildScoped :: (MonadCat NEmbedEnv m) => m NExpr -> m NExpr
buildScoped m = do
  (body, (_, decls)) <- scoped m
  return $ wrapNDecls decls body

materializeAtom :: (MonadCat NEmbedEnv m) => NAtom -> m NAtom
materializeAtom atom = case atom of
  NAtomicFor ib@(iv:>_) (NAtom body) -> do
    ans <- buildNFor ib $ \i -> do
      scope <- looks fst  -- really only need `i` in scope
      body' <- materializeAtom $ nSubst (iv @> L i, scope) body
      return $ NAtom body'
    emit ans
  NLam _ _ -> error $ "Can't materialize lambda"
  NRecCon m r -> liftM (NRecCon m) $ traverse materializeAtom r
  _ -> return atom

runEmbedT :: Monad m => CatT NEmbedEnv m a -> Scope -> m (a, NEmbedEnv)
runEmbedT m scope = runCatT m (scope, [])

runEmbed :: Cat NEmbedEnv a -> Scope -> (a, NEmbedEnv)
runEmbed m scope = runCat m (scope, [])

wrapNDecls :: [NDecl] -> NExpr -> NExpr
wrapNDecls [] expr = expr
wrapNDecls [NLet (v:>_) expr] (NAtom (NVar v' _)) | v == v' = expr  -- optimization
wrapNDecls (decl:decls) expr = NDecl decl (wrapNDecls decls expr)

nGet :: MonadCat NEmbedEnv m => NAtom -> NAtom -> m NAtom
nGet (NAtomicFor (v:>_) body) i = emitDecls $ nSubst (v@>L i, scope) body
  where scope = fmap (const ()) (freeVars i)
nGet e i = return $ NGet e i

emitDecls :: MonadCat NEmbedEnv m => NExpr -> m NAtom
emitDecls (NDecl decl body) = do
  extend $ asSnd [decl]
  emitDecls body
emitDecls expr = emit expr

flipIdx :: MonadCat NEmbedEnv m => NAtom -> m NAtom
flipIdx i = do
  let n = atomType i
  iInt  <- emit $ NPrimOp IndexAsInt [n] [i]
  nInt  <- emit $ NPrimOp IdxSetSize [n] []
  nInt' <- isub nInt (NLit (IntLit 1))
  iFlipped <- isub nInt' iInt
  emit $ NPrimOp IntAsIndex [n] [iFlipped]

isub :: MonadCat NEmbedEnv m => NAtom -> NAtom -> m NAtom
isub x y = emit $ NPrimOp ISub [] [x, y]

zeroAt :: MonadCat NEmbedEnv m => Type -> m NAtom
zeroAt ty = mapScalars (\_ _ -> return $ NLit (RealLit 0.0)) ty []

addAt :: MonadCat NEmbedEnv m => Type -> NAtom -> NAtom -> m NAtom
addAt ty xs ys = mapScalars (\_ [x, y] -> add x y) ty [xs, ys]

selectAt :: MonadCat NEmbedEnv m => NAtom -> Type -> NAtom -> NAtom -> m NAtom
selectAt p ty xs ys = mapScalars (\t [x, y] -> select p t x y) ty [xs, ys]

-- sumAt :: MonadCat NEmbedEnv m => Type -> [NAtom] -> m NAtom
-- sumAt ty [] = zeroAt ty
-- sumAt _ [x] = return x
-- sumAt ty (x:xs) = do
--   xsSum <- sumAt ty xs
--   addAt ty xsSum x

sumAt :: MonadCat NEmbedEnv m => Type -> [NExpr] -> m NExpr
sumAt = undefined

-- sumsAt tys xss = do
--   xss' <- liftM transpose $ mapM emit xss
--   liftM NAtom $ sequence [sumAt ty xs | (ty, xs) <- zip tys xss']

neg :: MonadCat NEmbedEnv m => NAtom -> m NAtom
neg x = emit $ NPrimOp FNeg [] [x]

add :: MonadCat NEmbedEnv m => NAtom -> NAtom -> m NAtom
add x y = emit $ NPrimOp FAdd [] [x, y]

mul :: MonadCat NEmbedEnv m => NAtom -> NAtom -> m NAtom
mul x y = emit $ NPrimOp FMul [] [x, y]

sub :: MonadCat NEmbedEnv m => NAtom -> NAtom -> m NAtom
sub x y = emit $ NPrimOp FSub [] [x, y]

select :: MonadCat NEmbedEnv m => NAtom -> Type -> NAtom -> NAtom -> m NAtom
select p ty x y = emit $ NPrimOp Select [ty] [p, x, y]

div' :: MonadCat NEmbedEnv m => NAtom -> NAtom -> m NAtom
div' x y = emit $ NPrimOp FDiv [] [x, y]

binderToVar :: NBinder -> NAtom
binderToVar (v:>ty) = NVar v ty

nUnitCon :: NAtom
nUnitCon = NRecCon Cart (Tup [])

unitBinder :: MonadCat NEmbedEnv m => m NBinder
unitBinder = do
  v <- freshNVar "_"
  return $ v:>unitTy

nRecGet :: MonadCat NEmbedEnv m => NAtom -> RecField -> m NAtom
nRecGet (NRecCon _ r) i = return $ recGet r i
nRecGet x i = emit $ NRecGet x i

recGetFst :: MonadCat NEmbedEnv m => NAtom -> m NAtom
recGetFst x = nRecGet x fstField

recGetSnd :: MonadCat NEmbedEnv m => NAtom -> m NAtom
recGetSnd x = nRecGet x sndField

unpackRec :: MonadCat NEmbedEnv m => NAtom -> m (Record NAtom)
unpackRec (NRecCon _ r) = return r
unpackRec x = case atomType x of
  RecType _ r -> traverse (nRecGet x . fst) $ recNameVals r
  ty          -> error $ "Not a tuple: " ++ pprint ty

fromTup :: MonadCat NEmbedEnv m => NAtom -> m [NAtom]
fromTup x = liftM toList $ unpackRec x

fromPair :: MonadCat NEmbedEnv m => NAtom -> m (NAtom, NAtom)
fromPair x = do
  ~[a, b] <- fromTup x
  return (a, b)

makePair :: NAtom -> NAtom -> NAtom
makePair x y = NRecCon Cart (Tup [x, y])

mapScalars :: MonadCat NEmbedEnv m
                     => (Type -> [NAtom] -> m NAtom)
                     -> Type -> [NAtom] -> m NAtom
mapScalars f ty xs = case ty of
  BaseType _  -> f ty xs
  IdxSetLit _ -> f ty xs
  TabType n a -> do
    ans <- buildNFor ("i":>n) $ \i ->
             liftM NAtom $ mapScalars f a [NGet x i | x <- xs]
    emit ans
  RecType m r -> do
    xs' <- liftM (transposeRecord r) $ mapM unpackRec xs
    liftM (NRecCon m) $ sequence $ recZipWith (mapScalars f) r xs'
  _ -> error $ "Not implemented " ++ pprint ty

transposeRecord :: Record b -> [Record a] -> Record [a]
transposeRecord r [] = fmap (const []) r
transposeRecord r (x:xs) = recZipWith (:) x $ transposeRecord r xs

