-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}

module Embed (emit, emitTo, buildLamExpr, buildLam, buildTLam,
              EmbedT, Embed, EmbedEnv, MonadEmbed, buildScoped, wrapDecls, runEmbedT,
              runEmbed, zeroAt, addAt, sumAt, getScope, withIndexed,
              nRecGet, nTabGet, add, mul, sub, neg, div', andE,
              select, selectAt, freshVar, unitBinder, unpackRec,
              substEmbed, fromPair, buildLamExprAux,
              emitExpr, unzipTab, buildFor, isSingletonType, emitDecl,
              singletonTypeVal, mapScalars, scopedDecls, embedScoped, extendScope,
              boolToInt, intToReal, boolToReal) where

import Control.Monad
import Control.Monad.Fail
import Control.Monad.Except hiding (Except)
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Identity

import Env
import Syntax
import Cat
import Type
import Subst
import Record
import PPrint

newtype EmbedT m a = EmbedT (CatT EmbedEnv m a)
  deriving (Functor, Applicative, Monad, MonadTrans, MonadIO, MonadFail)

type Embed = EmbedT Identity
type EmbedEnv = (Scope, [Decl])

runEmbedT :: Monad m => EmbedT m a -> Scope -> m (a, [Decl])
runEmbedT (EmbedT m) scope = do
  (ans, (_, decls)) <- runCatT m (scope, [])
  return (ans, decls)

runEmbed :: Embed a -> Scope -> (a, [Decl])
runEmbed m scope = runIdentity $ runEmbedT m scope

-- TODO: use suggestive names based on types (e.g. "f" for function)
emit :: MonadEmbed m => CExpr -> m Atom
emit expr = emitTo ("v":>NoAnn) expr

-- Promises to make a new decl with given names (maybe with different counter).
emitTo :: MonadEmbed m => Var -> CExpr -> m Atom
emitTo (v:>_) expr = case singletonTypeVal ty of
  Nothing -> do
    expr' <- deShadow expr <$> getScope
    v' <- freshVar (v:>ty)
    emitDecl $ Let v' expr'
    return $ Var v'
  Just x
    | eff == noEffect -> return x
    | otherwise -> do
        expr' <- deShadow expr <$> getScope
        emitDecl $ Let (NoName:>ty) expr'
        return x
  where (eff, ty) = getEffType expr

-- Assumes the decl binders are already fresh wrt current scope
emitExpr :: MonadEmbed m => Expr -> m Atom
emitExpr (Decl decl@(Let v _) body) = do
  extendScope (v@>())
  emitDecl decl
  emitExpr body
emitExpr (Atom atom) = return atom
emitExpr (CExpr expr) = emit expr

freshVar :: MonadEmbed m => VarP ann -> m (VarP ann)
freshVar v = do
  scope <- getScope
  let v' = rename v scope
  extendScope $ v' @> ()
  return v'

-- Runs second argument on a fresh binder variable and returns its result,
-- the fresh variable name and the EmbedEnv accumulated during its execution.
-- The first argument specifies the type of the binder variable, and is used
-- as a hint for its name.
withBinder :: (MonadEmbed m)
            => Var -> (Atom -> m a) -> m (a, Var, [Decl])
withBinder b f = do
  ((ans, b'), decls) <- scopedDecls $ do
      b' <- freshVar b
      ans <- f $ Var b'
      return (ans, b')
  return (ans, b', decls)

buildLam :: MonadEmbed m
         => Mult -> Var -> (Atom -> m (Atom, Effect)) -> m Atom
buildLam l v f = do
  (lam, eff) <- buildLamExprAux v $ \v' -> f v'
  return $ Con $ Lam Expl l eff lam

buildLamExpr :: (MonadEmbed m)
             => Var -> (Atom -> m Atom) -> m LamExpr
buildLamExpr b f = do
  (ans, b', decls) <- withBinder b f
  return $ LamExpr b' (wrapDecls decls ans)

buildLamExprAux :: (MonadEmbed m)
                => Var -> (Atom -> m (Atom, a)) -> m (LamExpr, a)
buildLamExprAux b f = do
  ((ans, aux), b', decls) <- withBinder b f
  return (LamExpr b' (wrapDecls decls ans), aux)

buildTLam :: (MonadEmbed m)
          => [Var] -> ([Type] -> m ([TyQual], Atom)) -> m Atom
buildTLam bs f = do
  -- TODO: refresh type vars in qs
  (((qs, body), bs'), decls) <- scopedDecls $ do
      bs' <- mapM freshVar bs
      ans <- f (map Var bs')
      return (ans, bs')
  return $ TLam bs' qs (wrapDecls decls body)

buildScoped :: (MonadEmbed m) => m Atom -> m Expr
buildScoped m = do
  (ans, decls) <- scopedDecls m
  return $ wrapDecls decls ans

withIndexed :: (MonadEmbed m)
            => EffectName -> Atom -> Atom -> (Atom -> m Atom) -> m Atom
withIndexed eff ref i f = do
  lam <- buildLamExpr ("ref":> RefTy a) $ \ref' -> f ref'
  emit $ IndexEff eff ref i lam
  where (RefTy (TabTy _ a)) = getType ref

wrapDecls :: [Decl] -> Atom -> Expr
wrapDecls [Let v expr] (Var v') | v == v' = CExpr expr  -- optimization
wrapDecls decls result = foldr Decl (Atom result) decls

-- TODO: consider broadcasted literals as atoms, so we don't need the monad here
zeroAt :: MonadEmbed m => Type -> m Atom
zeroAt ty = mapScalars (\_ _ -> return $ Con $ Lit (RealLit 0.0)) ty []

addAt :: MonadEmbed m => Type -> Atom -> Atom -> m Atom
addAt ty xs ys = mapScalars (\_ [x, y] -> add x y) ty [xs, ys]

selectAt :: MonadEmbed m => Type -> Atom -> Atom -> Atom -> m Atom
selectAt ty p xs ys = mapScalars (\t [x, y] -> select t p x y) ty [xs, ys]

sumAt :: MonadEmbed m => Type -> [Atom] -> m Atom
sumAt ty [] = zeroAt ty
sumAt _ [x] = return x
sumAt ty (x:xs) = do
  xsSum <- sumAt ty xs
  addAt ty xsSum x

neg :: MonadEmbed m => Atom -> m Atom
neg x = emit $ ScalarUnOp FNeg x

add :: MonadEmbed m => Atom -> Atom -> m Atom
add (RealVal 0) y = return y
add x y           = emit $ ScalarBinOp FAdd x y

mul :: MonadEmbed m => Atom -> Atom -> m Atom
mul x y = emit $ ScalarBinOp FMul x y

sub :: MonadEmbed m => Atom -> Atom -> m Atom
sub x y = emit $ ScalarBinOp FSub x y

andE :: MonadEmbed m => Atom -> Atom -> m Atom
andE (BoolVal True) y = return y
andE x y              = emit $ ScalarBinOp And x y

select :: MonadEmbed m => Type -> Atom -> Atom -> Atom -> m Atom
select ty p x y = emit $ Select ty p x y

div' :: MonadEmbed m => Atom -> Atom -> m Atom
div' x y = emit $ ScalarBinOp FDiv x y

unitBinder :: MonadEmbed m => m Var
unitBinder = freshVar (NoName:>UnitTy)

nRecGet :: MonadEmbed m => Atom -> RecField -> m Atom
nRecGet (RecVal r) i = return $ recGet r i
nRecGet x i = emit $ RecGet x i

nTabGet :: MonadEmbed m => Atom -> Atom -> m Atom
nTabGet x i = emit $ TabGet x i

unpackRec :: MonadEmbed m => Atom -> m (Record Atom)
unpackRec (RecVal r) = return r
unpackRec x = case getType x of
  RecTy r -> mapM (nRecGet x . fst) $ recNameVals r
  ty -> error $ "Not a tuple: " ++ pprint ty

fromPair :: MonadEmbed m => Atom -> m (Atom, Atom)
fromPair pair = do
  r <- unpackRec pair
  case r of
    Tup [x, y] -> return (x, y)
    _          -> error $ "Not a pair: " ++ pprint pair

buildFor :: (MonadEmbed m) => Direction -> Var -> (Atom -> m Atom) -> m Atom
buildFor d i body = do
  lam <- buildLamExpr i body
  emit $ For d lam

unzipTab :: (MonadEmbed m) => Atom -> m (Atom, Atom)
unzipTab tab = do
  fsts <- buildFor Fwd ("i":>n) $ \i ->
            liftM fst $ emit (TabGet tab i) >>= fromPair
  snds <- buildFor Fwd ("i":>n) $ \i ->
            liftM snd $ emit (TabGet tab i) >>= fromPair
  return (fsts, snds)
  where (TabTy n _) = getType tab

mapScalars :: MonadEmbed m => (Type -> [Atom] -> m Atom) -> Type -> [Atom] -> m Atom
mapScalars f ty xs = case ty of
  TabTy n a -> do
    lam <- buildLamExpr ("i":>n) $ \i -> do
      xs' <- mapM (flip nTabGet i) xs
      mapScalars f a xs'
    emit $ For Fwd lam
  RecTy r   -> do
    xs' <- liftM (transposeRecord r) $ mapM unpackRec xs
    liftM RecVal $ sequence $ recZipWith (mapScalars f) r xs'
  BaseTy _           -> f ty xs
  TC con -> case con of
    -- NOTE: Sum types not implemented, because they don't have a total zipping function!
    IntRange _ _     -> f ty xs
    IndexRange _ _ _ -> f ty xs
    _ -> error $ "Not implemented " ++ pprint ty
  _ -> error $ "Not implemented " ++ pprint ty

transposeRecord :: Record b -> [Record a] -> Record [a]
transposeRecord r [] = fmap (const []) r
transposeRecord r (x:xs) = recZipWith (:) x $ transposeRecord r xs

substEmbed :: (MonadEmbed m, MonadReader SubstEnv m, Subst a)
           => a -> m a
substEmbed x = do
  env <- ask
  scope <- getScope
  return $ subst (env, scope) x

isSingletonType :: Type -> Bool
isSingletonType ty = case singletonTypeVal ty of
  Nothing -> False
  Just _  -> True

singletonTypeVal :: Type -> Maybe Atom
singletonTypeVal (TabTy n a) = liftM (Con . AFor n) $ singletonTypeVal a
singletonTypeVal (TC con) = case con of
  -- XXX: This returns Nothing if it's a record that is not an empty tuple (or contains
  --      anything else than only empty tuples inside)!
  RecType r   -> liftM RecVal $ traverse singletonTypeVal r
  _           -> Nothing
singletonTypeVal _ = Nothing

boolToInt :: MonadEmbed m => Atom -> m Atom
boolToInt b = emit $ ScalarUnOp BoolToInt b

intToReal :: MonadEmbed m => Atom -> m Atom
intToReal i = emit $ ScalarUnOp IntToReal i

boolToReal :: MonadEmbed m => Atom -> m Atom
boolToReal = boolToInt >=> intToReal

class Monad m => MonadEmbed m where
  embedLook   :: m EmbedEnv
  embedExtend :: EmbedEnv -> m ()
  embedScoped :: m a -> m (a, EmbedEnv)

instance Monad m => MonadEmbed (EmbedT m) where
  embedLook = EmbedT look
  embedExtend env = EmbedT $ extend env
  embedScoped (EmbedT m) = EmbedT $ scoped m

instance MonadEmbed m => MonadEmbed (ReaderT r m) where
  embedLook = lift embedLook
  embedExtend x = lift $ embedExtend x
  embedScoped m = do
    r <- ask
    lift $ embedScoped $ runReaderT m r

instance (Monoid env, MonadCat env m) => MonadCat env (EmbedT m) where
  look = lift look
  extend x = lift $ extend x
  scoped _ = undefined

instance (Monoid env, MonadEmbed m) => MonadEmbed (CatT env m) where
  embedLook = undefined
  embedExtend _ = error "not implemented"
  embedScoped _ = error "not implemented"

instance (Monoid w, MonadEmbed m) => MonadEmbed (WriterT w m) where
  embedLook = lift embedLook
  embedExtend x = lift $ embedExtend x
  embedScoped m = do
    ((x, w), env) <- lift $ embedScoped $ runWriterT m
    tell w
    return (x, env)

instance MonadError e m => MonadError e (EmbedT m) where
  throwError = lift . throwError
  catchError m catch = do
    env <- embedLook
    (ans, env') <- lift $ runEmbedT' m env `catchError` (\e -> runEmbedT' (catch e) env)
    embedExtend env'
    return ans

runEmbedT' :: Monad m => EmbedT m a -> EmbedEnv -> m (a, EmbedEnv)
runEmbedT' (EmbedT m) env = runCatT m env

getScope :: MonadEmbed m => m Scope
getScope = fst <$> embedLook

extendScope :: MonadEmbed m => Scope -> m ()
extendScope scope = embedExtend $ asFst scope

emitDecl :: MonadEmbed m => Decl -> m ()
emitDecl decl = embedExtend $ asSnd [decl]

scopedDecls :: MonadEmbed m => m a -> m (a, [Decl])
scopedDecls m = do
  (ans, (_, decls)) <- embedScoped m
  return (ans, decls)
