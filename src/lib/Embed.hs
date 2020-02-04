-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Embed (emit, emitTo, withBinder, buildLam,
              EmbedT, Embed, EmbedEnv, buildScoped, wrapDecls, runEmbedT,
              runEmbed, emitUnpack, flipIdx, zeroAt, addAt, sumAt, deShadow,
              emitNamed, add, mul, sub, neg, div',
              selectAt, freshVar, unitBinder, nUnitCon,
              recGetFst, recGetSnd, buildFor, buildScan,
              makeTup, fromTup, makePair, fromPair) where

import Control.Monad
import Data.Foldable (toList)

import Env
import Fresh
import Syntax
import Cat
import Type
import Subst
import Record
import PPrint

type EmbedT m = CatT EmbedEnv m  -- TODO: consider a full newtype wrapper
type Embed = Cat EmbedEnv
type EmbedEnv = (Scope, [Decl])

-- TODO: use suggestive names based on types (e.g. "f" for function)
emit :: MonadCat EmbedEnv m => CExpr -> m Atom
emit expr = emitNamed "v" expr

emitNamed :: MonadCat EmbedEnv m => Name -> CExpr -> m Atom
emitNamed v expr = emitTo (v:>getType expr) expr

-- Promises to make a new decl with given names (maybe with different counter).
emitTo :: MonadCat EmbedEnv m => Var -> CExpr -> m Atom
emitTo b expr = do
  expr' <- deShadow expr
  b' <- freshVar b
  extend $ asSnd [Let b' expr']
  return $ Var b'

deShadow :: MonadCat EmbedEnv m => Subst a => a -> m a
deShadow x = do
   scope <- looks fst
   return $ subst (mempty, scope) x

freshVar :: MonadCat EmbedEnv m => VarP ann -> m (VarP ann)
freshVar v = do
  scope <- looks fst
  let v' = rename v scope
  extend $ asFst (v' @> ())
  return v'

emitUnpack :: MonadCat EmbedEnv m
           => TVar -> Atom -> m (Type, Var -> m Atom)
emitUnpack tv expr = do
  tv' <- freshVar tv
  let finish b = do b' <- freshVar b
                    extend $ asSnd [Unpack b' tv' expr]
                    return $ Var b'
  return (TypeVar tv', finish)

withBinder :: (MonadCat EmbedEnv m)
            => Var -> (Atom -> m a) -> m (a, Var, EmbedEnv)
withBinder b f = do
  ((ans, b'), env) <- scoped $ do
      b' <- freshVar b
      ans <- f $ Var b'
      return (ans, b')
  return (ans, b', env)

buildLam :: (MonadCat EmbedEnv m) => Var -> (Atom -> m Atom) -> m LamExpr
buildLam b f = do
  (ans, b', (_, decls)) <- withBinder b f
  return $ LamExpr b' (wrapDecls decls ans)

buildFor :: (MonadCat EmbedEnv m) => Var -> (Atom -> m Atom) -> m Atom
buildFor ib f = do
  xb <- unitBinder
  liftM recGetSnd $ buildScan ib xb nUnitCon $ \i _ ->
    liftM (makePair nUnitCon) $ f i

buildScan :: (MonadCat EmbedEnv m)
           => Var -> Var -> Atom
           -> (Atom -> Atom -> m Atom) -> m Atom
buildScan (_:>n) (_:>cTy) xsInit f = do
  ~(ans, b, (_, decls)) <- withBinder ("v":> pairTy n cTy) $ \ix -> do
      let (i, xs) = fromPair ix
      f i xs
  emit $ Scan xsInit $ LamExpr b (wrapDecls decls ans)

buildScoped :: (MonadCat EmbedEnv m) => m Atom -> m Expr
buildScoped m = do
  (ans, (_, decls)) <- scoped m
  return $ wrapDecls decls ans

runEmbedT :: Monad m => CatT EmbedEnv m a -> Scope -> m (a, EmbedEnv)
runEmbedT m scope = runCatT m (scope, [])

runEmbed :: Cat EmbedEnv a -> Scope -> (a, EmbedEnv)
runEmbed m scope = runCat m (scope, [])

wrapDecls :: [Decl] -> Atom -> Expr
wrapDecls [] atom = Atom atom
wrapDecls [Let v expr] (Var v') | v == v' = CExpr expr  -- optimization
wrapDecls (decl:decls) expr = Decl decl (wrapDecls decls expr)

flipIdx :: MonadCat EmbedEnv m => Atom -> m Atom
flipIdx i = do
  let n = getType i
  iInt  <- undefined -- emit $ IndexAsInt i
  nInt  <- emit $ IdxSetSize n
  nInt' <- isub nInt (PrimCon $ Lit (IntLit 1))
  iFlipped <- isub nInt' iInt
  emit $ IntAsIndex n iFlipped

isub :: MonadCat EmbedEnv m => Atom -> Atom -> m Atom
isub x y = emit $ ScalarBinOp ISub x y

zeroAt :: MonadCat EmbedEnv m => Type -> m Atom
zeroAt ty = mapScalars (\_ _ -> return $ PrimCon $ Lit (RealLit 0.0)) ty []

addAt :: MonadCat EmbedEnv m => Type -> Atom -> Atom -> m Atom
addAt ty xs ys = mapScalars (\_ [x, y] -> add x y) ty [xs, ys]

selectAt :: MonadCat EmbedEnv m => Type -> Atom -> Atom -> Atom -> m Atom
selectAt ty p xs ys = mapScalars (\t [x, y] -> select t p x y) ty [xs, ys]

sumAt :: MonadCat EmbedEnv m => Type -> [Atom] -> m Atom
sumAt ty [] = zeroAt ty
sumAt _ [x] = return x
sumAt ty (x:xs) = do
  xsSum <- sumAt ty xs
  addAt ty xsSum x

neg :: MonadCat EmbedEnv m => Atom -> m Atom
neg x = emit $ ScalarUnOp FNeg x

add :: MonadCat EmbedEnv m => Atom -> Atom -> m Atom
add x y = emit $ ScalarBinOp FAdd x y

mul :: MonadCat EmbedEnv m => Atom -> Atom -> m Atom
mul x y = emit $ ScalarBinOp FMul x y

sub :: MonadCat EmbedEnv m => Atom -> Atom -> m Atom
sub x y = emit $ ScalarBinOp FSub x y

select :: MonadCat EmbedEnv m => Type -> Atom -> Atom -> Atom -> m Atom
select ty p x y = emit $ Select ty p x y

div' :: MonadCat EmbedEnv m => Atom -> Atom -> m Atom
div' x y = emit $ ScalarBinOp FDiv x y

nUnitCon :: Atom
nUnitCon = PrimCon $ RecCon (Tup [])

unitBinder :: MonadCat EmbedEnv m => m Var
unitBinder = freshVar ("_":>unitTy)

recGetFst :: Atom -> Atom
recGetFst x = nRecGet x fstField

recGetSnd :: Atom -> Atom
recGetSnd x = nRecGet x sndField

unpackRec :: Atom -> Record Atom
unpackRec (PrimCon (RecCon r)) = r
unpackRec x = case getType x of
  RecType r -> fmap (nRecGet x . fst) $ recNameVals r
  ty        -> error $ "Not a tuple: " ++ pprint ty

makeTup :: [Atom] -> Atom
makeTup xs = PrimCon $ RecCon $ Tup xs

fromTup :: Atom -> [Atom]
fromTup x = toList $ unpackRec x

makePair :: Atom -> Atom -> Atom
makePair x y = PrimCon $ RecCon (Tup [x, y])

fromPair :: Atom -> (Atom, Atom)
fromPair x = (a, b)
  where [a, b] = fromTup x

mapScalars :: MonadCat EmbedEnv m
           => (Type -> [Atom] -> m Atom) -> Type -> [Atom] -> m Atom
mapScalars f ty xs = case ty of
  BaseType _  -> f ty xs
  IdxSetLit _ -> f ty xs
  TabType n a -> buildFor ("i":>n) $ \i -> mapScalars f a [nTabGet x i | x <- xs]
  RecType r ->
    liftM (PrimCon . RecCon) $ sequence $ recZipWith (mapScalars f) r xs'
    where xs' = transposeRecord r $ map unpackRec xs
  _ -> error $ "Not implemented " ++ pprint ty

transposeRecord :: Record b -> [Record a] -> Record [a]
transposeRecord r [] = fmap (const []) r
transposeRecord r (x:xs) = recZipWith (:) x $ transposeRecord r xs

