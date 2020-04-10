-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Embed (emit, emitTo, buildLamExpr, buildLam, buildTLam,
              EmbedT, Embed, EmbedEnv, buildScoped, wrapDecls, runEmbedT,
              runEmbed, zeroAt, addAt, sumAt, deShadow, withIndexed,
              nRecGet, nTabGet, emitNamed, add, mul, sub, neg, div',
              selectAt, freshVar, unitBinder, unitCon, unpackRec,
              makeTup, makePair, substEmbed, fromPair, buildLamExprAux,
              emitExpr, unzipTab) where

import Control.Monad
import Control.Monad.Reader

import Env
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
emitNamed v expr = emitTo (v:> getType expr) expr

-- Promises to make a new decl with given names (maybe with different counter).
emitTo :: MonadCat EmbedEnv m => Var -> CExpr -> m Atom
emitTo b expr = do
  expr' <- deShadow expr
  b' <- freshVar b
  extend $ asSnd [Let b' expr']
  return $ Var b'

-- Assumes the decl binders are already fresh wrt current scope
emitExpr :: MonadCat EmbedEnv m => Expr -> m Atom
emitExpr (Decl decl@(Let v _) body) = extend (v@>(), [decl]) >> emitExpr body
emitExpr (Atom atom) = return atom
emitExpr (CExpr expr) = emit expr

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

withBinder :: (MonadCat EmbedEnv m)
            => Var -> (Atom -> m a) -> m (a, Var, EmbedEnv)
withBinder b f = do
  ((ans, b'), env) <- scoped $ do
      b' <- freshVar b
      ans <- f $ Var b'
      return (ans, b')
  return (ans, b', env)

buildLam :: MonadCat EmbedEnv m
         => Mult -> Var -> (Atom -> m (Atom, Effect)) -> m Atom
buildLam l v f = do
  (lam, eff) <- buildLamExprAux v $ \v' -> f v'
  return $ Con $ Lam l eff lam

buildLamExpr :: (MonadCat EmbedEnv m)
             => Var -> (Atom -> m Atom) -> m LamExpr
buildLamExpr b f = do
  (ans, b', (_, decls)) <- withBinder b f
  return $ LamExpr b' (wrapDecls decls ans)

buildLamExprAux :: (MonadCat EmbedEnv m)
                => Var -> (Atom -> m (Atom, a)) -> m (LamExpr, a)
buildLamExprAux b f = do
  ((ans, aux), b', (_, decls)) <- withBinder b f
  return (LamExpr b' (wrapDecls decls ans), aux)

buildTLam :: (MonadCat EmbedEnv m)
          => [TVar] -> ([Type] -> m ([TyQual], Atom)) -> m Atom
buildTLam bs f = do
  -- TODO: refresh type vars in qs
  (((qs, body), bs'), (_, decls)) <- scoped $ do
      bs' <- mapM freshVar bs
      ans <- f (map TypeVar bs')
      return (ans, bs')
  return $ TLam bs' qs (wrapDecls decls body)

buildScoped :: (MonadCat EmbedEnv m) => m Atom -> m Expr
buildScoped m = do
  (ans, (_, decls)) <- scoped m
  return $ wrapDecls decls ans

withIndexed :: (MonadCat EmbedEnv m)
            => EffectName -> Atom -> Atom -> (Atom -> m Atom) -> m Atom
withIndexed eff ~ref@(Var refVar) i f = do
  lam <- buildLamExpr ("ref":>Ref a) $ \ref' -> f ref'
  emit $ IndexEff eff (Dep refVar) ref i lam
  where (Ref (TabType _ a)) = getType ref

runEmbedT :: Monad m => CatT EmbedEnv m a -> Scope -> m (a, EmbedEnv)
runEmbedT m scope = runCatT m (scope, [])

runEmbed :: Cat EmbedEnv a -> Scope -> (a, EmbedEnv)
runEmbed m scope = runCat m (scope, [])

wrapDecls :: [Decl] -> Atom -> Expr
wrapDecls [] atom = Atom atom
wrapDecls [Let v expr] (Var v') | v == v' = CExpr expr  -- optimization
wrapDecls (decl:decls) expr = Decl decl (wrapDecls decls expr)

-- TODO: consider broadcasted literals as atoms, so we don't need the monad here
zeroAt :: MonadCat EmbedEnv m => Type -> m Atom
zeroAt ty = mapScalars (\_ _ -> return $ Con $ Lit (RealLit 0.0)) ty []

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

unitCon :: Atom
unitCon = Con $ RecCon (Tup [])

unitBinder :: MonadCat EmbedEnv m => m Var
unitBinder = freshVar (NoName:>unitTy)

nRecGet :: MonadCat EmbedEnv m => Atom -> RecField -> m Atom
nRecGet (Con (RecCon r)) i = return $ recGet r i
nRecGet x i = emit $ RecGet x i

nTabGet :: MonadCat EmbedEnv m => Atom -> Atom -> m Atom
nTabGet x i = emit $ TabGet x i

unpackRec :: MonadCat EmbedEnv m => Atom -> m (Record Atom)
unpackRec (Con (RecCon r)) = return r
unpackRec x = case getType x of
  RecType r -> mapM (nRecGet x . fst) $ recNameVals r
  ty        -> error $ "Not a tuple: " ++ pprint ty

makeTup :: [Atom] -> Atom
makeTup xs = Con $ RecCon $ Tup xs

makePair :: Atom -> Atom -> Atom
makePair x y = Con $ RecCon (Tup [x, y])

fromPair :: MonadCat EmbedEnv m => Atom -> m (Atom, Atom)
fromPair pair = do
  r <- unpackRec pair
  case r of
    Tup [x, y] -> return (x, y)
    _          -> error $ "Not a pair: " ++ pprint pair

buildFor :: (MonadCat EmbedEnv m) => Var -> (Atom -> m Atom) -> m Atom
buildFor i body = do
  lam <- buildLamExpr i body
  emit $ For lam

unzipTab :: (MonadCat EmbedEnv m) => Atom -> m (Atom, Atom)
unzipTab tab = do
  fsts <- buildFor ("i":>n) $ \i ->
            liftM fst $ emit (TabGet tab i) >>= fromPair
  snds <- buildFor ("i":>n) $ \i ->
            liftM snd $ emit (TabGet tab i) >>= fromPair
  return (fsts, snds)
  where (TabType n _) = getType tab

mapScalars :: MonadCat EmbedEnv m
           => (Type -> [Atom] -> m Atom) -> Type -> [Atom] -> m Atom
mapScalars f ty xs = case ty of
  BaseType _  -> f ty xs
  IdxSetLit _ -> f ty xs
  TabType n a -> do
    lam <- buildLamExpr ("i":>n) $ \i -> do
      xs' <- mapM (flip nTabGet i) xs
      mapScalars f a xs'
    emit $ For lam
  RecType r -> do
    xs' <- liftM (transposeRecord r) $ mapM unpackRec xs
    liftM (Con . RecCon) $ sequence $ recZipWith (mapScalars f) r xs'
  _ -> error $ "Not implemented " ++ pprint ty

transposeRecord :: Record b -> [Record a] -> Record [a]
transposeRecord r [] = fmap (const []) r
transposeRecord r (x:xs) = recZipWith (:) x $ transposeRecord r xs

substEmbed :: (MonadCat EmbedEnv m, MonadReader (FullEnv Atom Type) m, Subst a)
           => a -> m a
substEmbed x = do
  env <- ask
  scope <- looks fst
  return $ subst (env, scope) x
