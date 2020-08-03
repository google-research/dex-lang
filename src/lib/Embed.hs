-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module Embed (emit, emitTo, emitAnn, emitOp, buildDepEffLam, buildLamAux, buildPi,
              getAllowedEffects, withEffects, modifyAllowedEffects,
              buildLam, EmbedT, Embed, MonadEmbed, buildScoped, runEmbedT,
              runSubstEmbed, runEmbed, zeroAt, addAt, sumAt, getScope, reduceBlock,
              app, add, mul, sub, neg, div', andE, iadd, imul, isub, idiv, reduceScoped,
              select, substEmbed, substEmbedR, emitUnpack,
              fromPair, getFst, getSnd, naryApp, appReduce,
              emitBlock, unzipTab, buildFor, isSingletonType, emitDecl, withNameHint,
              singletonTypeVal, scopedDecls, embedScoped, extendScope, checkEmbed,
              embedExtend, boolToInt, intToReal, boolToReal, reduceAtom,
              unpackConsList, emitRunWriter, emitRunReader, tabGet,
              SubstEmbedT, SubstEmbed, runSubstEmbedT, dceBlock, dceModule,
              TraversalDef, traverseDecls, traverseBlock, traverseExpr,
              traverseAtom, arrOffset, arrLoad, evalBlockE, substTraversalDef,
              clampPositive, buildNAbs,
              indexSetSizeE, indexToIntE, intToIndexE, anyValue) where

import Control.Applicative
import Control.Monad
import Control.Monad.Fail
import Control.Monad.Except hiding (Except)
import Control.Monad.Reader
import Control.Monad.Writer hiding (Alt)
import Control.Monad.Identity
import Data.Foldable (toList)
import Data.Maybe
import GHC.Stack

import Env
import Syntax
import Cat
import Type
import PPrint
import Util (bindM2, scanM, restructure)

newtype EmbedT m a = EmbedT (ReaderT EmbedEnvR (CatT EmbedEnvC m) a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail, Alternative)

type Embed = EmbedT Identity
type EmbedEnv = (EmbedEnvR, EmbedEnvC)

type SubstEmbedT m = ReaderT SubstEnv (EmbedT m)
type SubstEmbed    = SubstEmbedT Identity

-- Carries the vars in scope (with optional definitions) and the emitted decls
type EmbedEnvC = (Scope, Nest Decl)
-- Carries a name suggestion and the allowable effects
type EmbedEnvR = (Tag, EffectRow)

runEmbedT :: Monad m => EmbedT m a -> Scope -> m (a, EmbedEnvC)
runEmbedT (EmbedT m) scope = do
  (ans, env) <- runCatT (runReaderT m ("tmp", Pure)) (scope, Empty)
  return (ans, env)

runEmbed :: Embed a -> Scope -> (a, EmbedEnvC)
runEmbed m scope = runIdentity $ runEmbedT m scope

runSubstEmbedT :: Monad m => SubstEmbedT m a -> Scope -> m (a, EmbedEnvC)
runSubstEmbedT m scope = runEmbedT (runReaderT m mempty) scope

runSubstEmbed :: SubstEmbed a -> Scope -> (a, EmbedEnvC)
runSubstEmbed m scope = runIdentity $ runEmbedT (runReaderT m mempty) scope

emit :: MonadEmbed m => Expr -> m Atom
emit expr     = emitAnn PlainLet expr

emitAnn :: MonadEmbed m => LetAnn -> Expr -> m Atom
emitAnn ann expr = do
  v <- getNameHint
  emitTo v ann expr

-- Guarantees that the name will be used, possibly with a modified counter
emitTo :: MonadEmbed m => Name -> LetAnn -> Expr -> m Atom
emitTo name ann expr = do
  scope <- getScope
  -- Deshadow type because types from DataDef may have binders that shadow local vars
  let ty    = deShadow (getType expr) scope
  let expr' = deShadow expr scope
  v <- freshVar (LetBound ann expr') $ Bind (name:>ty)
  embedExtend $ asSnd $ Nest (Let ann (Bind v) expr') Empty
  return $ Var v

emitOp :: MonadEmbed m => Op -> m Atom
emitOp op = emit $ Op op

emitUnpack :: MonadEmbed m => Expr -> m [Atom]
emitUnpack expr = do
  bs <- case getType expr of
    TypeCon def params -> do
      let [DataConDef _ bs] = applyDataDefParams def params
      return bs
    RecordTy types -> do
      -- TODO: is using Ignore here appropriate? We don't have any existing
      -- binders to bind, but we still plan to use the results.
      let bs = toNest $ map Ignore $ toList types
      return bs
    _ -> error $ "Unpacking a type that doesn't support unpacking: " ++ pprint (getType expr)
  expr' <- deShadow expr <$> getScope
  vs <- freshNestedBinders bs
  embedExtend $ asSnd $ Nest (Unpack (fmap Bind vs) expr') Empty
  return $ map Var $ toList vs

-- Assumes the decl binders are already fresh wrt current scope
emitBlock :: MonadEmbed m => Block -> m Atom
emitBlock (Block decls result) = mapM_ emitDecl decls >> emit result

freshVar :: MonadEmbed m => BinderInfo -> Binder -> m Var
freshVar bInfo b = do
  v <- case b of
    Ignore _    -> getNameHint
    Bind (v:>_) -> return v
  scope <- getScope
  let v' = genFresh v scope
  embedExtend $ asFst $ v' @> (binderType b, bInfo)
  return $ v' :> binderType b

freshNestedBinders :: MonadEmbed m => Nest Binder -> m (Nest Var)
freshNestedBinders bs = freshNestedBindersRec mempty bs

freshNestedBindersRec :: MonadEmbed m => Env Atom -> Nest Binder -> m (Nest Var)
freshNestedBindersRec _ Empty = return Empty
freshNestedBindersRec substEnv (Nest b bs) = do
  scope <- getScope
  v  <- freshVar PatBound $ subst (substEnv, scope) b
  vs <- freshNestedBindersRec (substEnv <> b@>Var v) bs
  return $ Nest v vs

buildPi :: (MonadError Err m, MonadEmbed m)
        => Binder -> (Atom -> m (Arrow, Type)) -> m Atom
buildPi b f = do
  (piTy, decls) <- scopedDecls $ do
     v <- freshVar PiBound b
     (arr, ans) <- f $ Var v
     return $ Pi $ makeAbs (Bind v) (arr, ans)
  unless (null decls) $ throw CompilerErr $ "Unexpected decls: " ++ pprint decls
  return piTy

buildLam :: MonadEmbed m => Binder -> Arrow -> (Atom -> m Atom) -> m Atom
buildLam b arr body = buildDepEffLam b (const (return arr)) body

buildDepEffLam :: MonadEmbed m
               => Binder -> (Atom -> m Arrow) -> (Atom -> m Atom) -> m Atom
buildDepEffLam b fArr fBody = liftM fst $ buildLamAux b fArr $ \x -> (,()) <$> fBody x

buildLamAux :: MonadEmbed m
            => Binder -> (Atom -> m Arrow) -> (Atom -> m (Atom, a)) -> m (Atom, a)
buildLamAux b fArr fBody = do
  ((b', arr, ans, aux), decls) <- scopedDecls $ do
     v <- freshVar UnknownBinder b
     let x = Var v
     arr <- fArr x
     -- overwriting the previous binder info know that we know more
     embedExtend $ asFst $ v @> (varType v, LamBound (void arr))
     (ans, aux) <- withEffects (arrowEff arr) $ fBody x
     return (Bind v, arr, ans, aux)
  return (Lam $ makeAbs b' (arr, wrapDecls decls ans), aux)

buildNAbs :: MonadEmbed m
          => Nest Binder -> ([Atom] -> m Atom) -> m (Abs (Nest Binder) Block)
buildNAbs bs body = do
  ((bs', ans), decls) <- scopedDecls $ do
     vs <- freshNestedBinders bs
     ans <- body $ map Var $ toList vs
     return (fmap Bind vs, ans)
  return $ Abs bs' $ wrapDecls decls ans

buildScoped :: MonadEmbed m => m Atom -> m Block
buildScoped m = do
  (ans, decls) <- scopedDecls m
  return $ wrapDecls decls ans

wrapDecls :: Nest Decl -> Atom -> Block
wrapDecls decls atom = dceBlock $ Block decls $ Atom atom

zeroAt :: Type -> Atom
zeroAt ty = case ty of
  RealTy -> asRealVal 0.0
  TabTy (Ignore n) a ->
    Lam $ Abs (Ignore n) (TabArrow,  Block Empty $ Atom $ zeroAt a)
  UnitTy -> UnitVal
  PairTy a b -> PairVal (zeroAt a) (zeroAt b)
  _ -> error $ "Not implemented: " ++ pprint ty

addAt :: MonadEmbed m => Type -> Atom -> Atom -> m Atom
addAt ty xs ys = mapScalars (\_ [x, y] -> add x y) ty [xs, ys]

sumAt :: MonadEmbed m => Type -> [Atom] -> m Atom
sumAt ty [] = return $ zeroAt ty
sumAt _ [x] = return x
sumAt ty (x:xs) = do
  xsSum <- sumAt ty xs
  addAt ty xsSum x

neg :: MonadEmbed m => Atom -> m Atom
neg x = emitOp $ ScalarUnOp FNeg x

add :: MonadEmbed m => Atom -> Atom -> m Atom
add (RealLit l) y | getRealLit l == 0.0 = return y
add x y = emitOp $ ScalarBinOp FAdd x y

-- TODO: We should be more careful about the precision in which we carry out
--       constant-folded expressions, because we might not preserve the full
--       program semantics.
-- TODO: Implement constant folding for fixed-width integer types as well!
iadd :: MonadEmbed m => Atom -> Atom -> m Atom
iadd (IntLit l)  y           | getIntLit l == 0                 = return y
iadd x           (IntLit l)  | getIntLit l == 0                 = return x
iadd (IntLit xl) (IntLit yl) | [x, y] <- getIntLit <$> [xl, yl] = return $ asIntVal $ x + y
iadd x y = emitOp $ ScalarBinOp IAdd x y

mul :: MonadEmbed m => Atom -> Atom -> m Atom
mul x y = emitOp $ ScalarBinOp FMul x y

imul :: MonadEmbed m => Atom -> Atom -> m Atom
imul (IntLit l)  y           | getIntLit l == 1                 = return y
imul x           (IntLit l)  | getIntLit l == 1                 = return x
imul (IntLit xl) (IntLit yl) | [x, y] <- getIntLit <$> [xl, yl] = return $ asIntVal $ x * y
imul x y = emitOp $ ScalarBinOp IMul x y

sub :: MonadEmbed m => Atom -> Atom -> m Atom
sub x y = emitOp $ ScalarBinOp FSub x y

isub :: MonadEmbed m => Atom -> Atom -> m Atom
isub x           (IntLit l)  | getIntLit l == 0                 = return x
isub (IntLit xl) (IntLit yl) | [x, y] <- getIntLit <$> [xl, yl] = return $ asIntVal $ x - y
isub x y = emitOp $ ScalarBinOp ISub x y

andE :: MonadEmbed m => Atom -> Atom -> m Atom
andE (BoolLit l)  y            | getBoolLit l                      = return y
andE x            (BoolLit l)  | getBoolLit l                      = return x
andE (BoolLit xl) (BoolLit yl) | [x, y] <- getBoolLit <$> [xl, yl] = return $ asBoolVal $ x && y
andE x y = emit $ Op $ ScalarBinOp BAnd x y

select :: MonadEmbed m => Atom -> Atom -> Atom -> m Atom
select (BoolLit l) x y | b <- getBoolLit l = return $ if b then x else y
select p x y = emitOp $ Select p x y

div' :: MonadEmbed m => Atom -> Atom -> m Atom
div' x y = emitOp $ ScalarBinOp FDiv x y

idiv :: MonadEmbed m => Atom -> Atom -> m Atom
idiv x           (IntLit l)  | getIntLit l == 1                 = return x
idiv (IntLit xl) (IntLit yl) | [x, y] <- getIntLit <$> [xl, yl] = return $ asIntVal $ x `div` y
idiv x y = emitOp $ ScalarBinOp IDiv x y

irem :: MonadEmbed m => Atom -> Atom -> m Atom
irem x y = emitOp $ ScalarBinOp IRem x y

ilt :: MonadEmbed m => Atom -> Atom -> m Atom
ilt (IntLit xl) (IntLit yl) | [x, y] <- getIntLit <$> [xl, yl] = return $ asBoolVal $ x < y
ilt x y = emitOp $ ScalarBinOp (ICmp Less) x y

getFst :: MonadEmbed m => Atom -> m Atom
getFst (PairVal x _) = return x
getFst p = emitOp $ Fst p

getSnd :: MonadEmbed m => Atom -> m Atom
getSnd (PairVal _ y) = return y
getSnd p = emitOp $ Snd p

getUnpacked :: MonadEmbed m => Atom -> m [Atom]
getUnpacked (DataCon _ _ _ xs) = return xs
getUnpacked (Record items) = return $ toList items
getUnpacked a = emitUnpack (Atom a)

app :: MonadEmbed m => Atom -> Atom -> m Atom
app x i = emit $ App x i

naryApp :: MonadEmbed m => Atom -> [Atom] -> m Atom
naryApp f xs = foldM app f xs

appReduce :: MonadEmbed m => Atom -> Atom -> m Atom
appReduce (Lam (Abs v (_, b))) a =
  runReaderT (evalBlockE substTraversalDef b) (v @> a)
appReduce _ _ = error "appReduce expected a lambda as the first argument"

arrOffset :: MonadEmbed m => Atom -> Atom -> Atom -> m Atom
arrOffset x idx off = emitOp $ ArrayOffset x idx off

arrLoad :: MonadEmbed m => Atom -> m Atom
arrLoad x = emitOp $ ArrayLoad x

fromPair :: MonadEmbed m => Atom -> m (Atom, Atom)
fromPair pair = (,) <$> getFst pair <*> getSnd pair

unpackConsList :: MonadEmbed m => Atom -> m [Atom]
unpackConsList xs = case getType xs of
  UnitTy -> return []
  _ -> do
    (x, rest) <- fromPair xs
    liftM (x:) $ unpackConsList rest

emitRunWriter :: MonadEmbed m => Name -> Type -> (Atom -> m Atom) -> m Atom
emitRunWriter v ty body = do
  eff <- getAllowedEffects
  lam <- buildLam (Bind ("r":>TyKind)) PureArrow $ \r@(Var (rName:>_)) -> do
    let arr = PlainArrow $ extendEffect (Writer, rName) eff
    buildLam (Bind (v:> RefTy r ty)) arr body
  emit $ Hof $ RunWriter lam

emitRunReader :: MonadEmbed m => Name -> Atom -> (Atom -> m Atom) -> m Atom
emitRunReader v x0 body = do
  eff <- getAllowedEffects
  lam <- buildLam (Bind ("r":>TyKind)) PureArrow $ \r@(Var (rName:>_)) -> do
    let arr = PlainArrow $ extendEffect (Reader, rName) eff
    buildLam (Bind (v:> RefTy r (getType x0))) arr body
  emit $ Hof $ RunReader x0 lam

buildFor :: MonadEmbed m => Direction -> Binder -> (Atom -> m Atom) -> m Atom
buildFor d i body = do
  -- TODO: track effects in the embedding env so we can add them here
  eff <- getAllowedEffects
  lam <- buildLam i (PlainArrow eff) body
  emit $ Hof $ For d lam

tabGet :: MonadEmbed m => Atom -> Atom -> m Atom
tabGet x i = emit $ App x i

unzipTab :: MonadEmbed m => Atom -> m (Atom, Atom)
unzipTab tab = do
  fsts <- buildLam (Bind ("i":>binderType v)) TabArrow $ \i ->
            liftM fst $ app tab i >>= fromPair
  snds <- buildLam (Bind ("i":>binderType v)) TabArrow $ \i ->
            liftM snd $ app tab i >>= fromPair
  return (fsts, snds)
  where TabTy v _ = getType tab

mapScalars :: HasCallStack => MonadEmbed m => (Type -> [Atom] -> m Atom) -> Type -> [Atom] -> m Atom
mapScalars f ty xs = case ty of
  TabTy b a -> do
    buildFor Fwd (Bind ("i":>binderType b)) $ \i -> do
      xs' <- mapM (flip app i) xs
      mapScalars f a xs'
  BaseTy _           -> f ty xs
  UnitTy -> return UnitVal
  PairTy a b -> do
    (ys, zs) <- unzip <$> mapM fromPair xs
    PairVal <$> mapScalars f a ys <*> mapScalars f b zs
  TC con -> case con of
    -- NOTE: Sum types not implemented, because they don't have a total zipping function!
    IntRange _ _     -> f ty xs
    IndexRange _ _ _ -> f ty xs
    _ -> error $ "Not implemented " ++ pprint ty
  _ -> error $ "Not implemented " ++ pprint ty

substEmbedR :: (MonadEmbed m, MonadReader SubstEnv m, Subst a)
           => a -> m a
substEmbedR x = do
  env <- ask
  substEmbed env x

substEmbed :: (MonadEmbed m, Subst a)
           => SubstEnv -> a -> m a
substEmbed env x = do
  scope <- getScope
  return $ subst (env, scope) x

checkEmbed :: (HasCallStack, MonadEmbed m, HasType a) => a -> m a
checkEmbed  x = do
  scope <- getScope
  eff <- getAllowedEffects
  case checkType scope eff x of
    Left e   -> error $ pprint e
    Right () -> return x

isSingletonType :: Type -> Bool
isSingletonType ty = case singletonTypeVal ty of
  Nothing -> False
  Just _  -> True

singletonTypeVal :: Type -> Maybe Atom
singletonTypeVal (TabTy v a) = TabValA v <$> singletonTypeVal a
singletonTypeVal (TC con) = case con of
  PairType a b -> liftM2 PairVal (singletonTypeVal a) (singletonTypeVal b)
  UnitType     -> return UnitVal
  _            -> Nothing
singletonTypeVal _ = Nothing

boolToInt :: MonadEmbed m => Atom -> m Atom
boolToInt b = emitOp $ ScalarUnOp BoolToInt b

intToReal :: MonadEmbed m => Atom -> m Atom
intToReal i = emitOp $ ScalarUnOp IntToReal i

boolToReal :: MonadEmbed m => Atom -> m Atom
boolToReal = boolToInt >=> intToReal

indexAsInt :: MonadEmbed m => Atom -> m Atom
indexAsInt idx = emitOp $ IndexAsInt idx

cast :: MonadEmbed m => Type -> Atom -> m Atom
cast ty x = emitOp $ CastOp ty x

boolCase :: MonadEmbed m => Atom -> m Atom -> m Atom -> m Atom
boolCase baseBoolCond trueBlock falseBlock = do
  preludeBoolCond <- cast PreludeBoolTy baseBoolCond
  trueCase@(Abs _ trueBody) <- buildNAbs Empty $ \[] -> trueBlock
  falseCase <- buildNAbs Empty $ \[] -> falseBlock
  let ty = getType trueBody
  emit $ Case preludeBoolCond [falseCase, trueCase] ty

instance MonadTrans EmbedT where
  lift m = EmbedT $ lift $ lift m

class Monad m => MonadEmbed m where
  embedLook   :: m EmbedEnvC
  embedExtend :: EmbedEnvC -> m ()
  embedScoped :: m a -> m (a, EmbedEnvC)
  embedAsk    :: m EmbedEnvR
  embedLocal  :: (EmbedEnvR -> EmbedEnvR) -> m a -> m a

instance Monad m => MonadEmbed (EmbedT m) where
  embedLook = EmbedT look
  embedExtend env = EmbedT $ extend env
  embedScoped (EmbedT m) = EmbedT $ scoped m
  embedAsk = EmbedT ask
  embedLocal f (EmbedT m) = EmbedT $ local f m

instance MonadEmbed m => MonadEmbed (ReaderT r m) where
  embedLook = lift embedLook
  embedExtend x = lift $ embedExtend x
  embedScoped m = ReaderT $ \r -> embedScoped $ runReaderT m r
  embedAsk = lift embedAsk
  embedLocal v m = ReaderT $ \r -> embedLocal v $ runReaderT m r

instance (Monoid env, MonadEmbed m) => MonadEmbed (CatT env m) where
  embedLook = undefined
  embedExtend _ = error "not implemented"
  embedScoped _ = error "not implemented"
  embedAsk = lift embedAsk
  embedLocal = undefined

instance (Monoid w, MonadEmbed m) => MonadEmbed (WriterT w m) where
  embedLook = lift embedLook
  embedExtend x = lift $ embedExtend x
  embedScoped m = do
    ((x, w), env) <- lift $ embedScoped $ runWriterT m
    tell w
    return (x, env)
  embedAsk = lift embedAsk
  embedLocal v m = WriterT $ embedLocal v $ runWriterT m

instance (Monoid env, MonadCat env m) => MonadCat env (EmbedT m) where
  look = lift look
  extend x = lift $ extend x
  scoped (EmbedT m) = EmbedT $ do
    name <- ask
    env <- look
    ((ans, env'), scopeEnv) <- lift $ lift $ scoped $ runCatT (runReaderT m name) env
    extend env'
    return (ans, scopeEnv)

instance MonadError e m => MonadError e (EmbedT m) where
  throwError = lift . throwError
  catchError m catch = do
    envC <- embedLook
    envR <- embedAsk
    (ans, envC') <- lift $ runEmbedT' m (envR, envC)
                     `catchError` (\e -> runEmbedT' (catch e) (envR, envC))
    embedExtend envC'
    return ans

getNameHint :: MonadEmbed m => m Name
getNameHint = do
  tag <- fst <$> embedAsk
  return $ Name GenName tag 0

-- This is purely for human readability. `const id` would be a valid implementation.
withNameHint :: (MonadEmbed m, HasName a) => a -> m b -> m b
withNameHint name m = embedLocal (\(_, eff) -> (tag, eff)) m
  where
    tag = case getName name of
      Just (Name _ t _)        -> t
      Just (GlobalName t)      -> t
      Just (GlobalArrayName _) -> "arr"
      Nothing                  -> "tmp"

runEmbedT' :: Monad m => EmbedT m a -> EmbedEnv -> m (a, EmbedEnvC)
runEmbedT' (EmbedT m) (envR, envC) = runCatT (runReaderT m envR) envC

getScope :: MonadEmbed m => m Scope
getScope = fst <$> embedLook

extendScope :: MonadEmbed m => Scope -> m ()
extendScope scope = embedExtend $ asFst scope

getAllowedEffects :: MonadEmbed m => m EffectRow
getAllowedEffects = snd <$> embedAsk

withEffects :: MonadEmbed m => EffectRow -> m a -> m a
withEffects effs m = modifyAllowedEffects (const effs) m

modifyAllowedEffects :: MonadEmbed m => (EffectRow -> EffectRow) -> m a -> m a
modifyAllowedEffects f m = embedLocal (\(name, eff) -> (name, f eff)) m

emitDecl :: MonadEmbed m => Decl -> m ()
emitDecl decl = embedExtend (bindings, Nest decl Empty)
  where bindings = case decl of
          Let ann b expr -> b @> (binderType b, LetBound ann expr)
          Unpack bs _ -> foldMap (\b -> b @> (binderType b, PatBound)) bs

scopedDecls :: MonadEmbed m => m a -> m (a, Nest Decl)
scopedDecls m = do
  (ans, (_, decls)) <- embedScoped m
  return (ans, decls)

-- === generic traversal ===

type TraversalDef m = (Expr -> m Expr, Atom -> m Atom)

substTraversalDef :: (MonadEmbed m, MonadReader SubstEnv m) => TraversalDef m
substTraversalDef = (traverseExpr substTraversalDef, traverseAtom substTraversalDef)

-- With `def = (traverseExpr def, traverseAtom def)` this should be a no-op
traverseDecls :: (MonadEmbed m, MonadReader SubstEnv m)
               => TraversalDef m -> Nest Decl -> m (Nest Decl)
traverseDecls def decls = liftM snd $ scopedDecls $ traverseDeclsOpen def decls

traverseDeclsOpen :: (MonadEmbed m, MonadReader SubstEnv m)
                  => TraversalDef m -> Nest Decl -> m SubstEnv
traverseDeclsOpen _ Empty = return mempty
traverseDeclsOpen def (Nest decl decls) = do
  env <- traverseDecl def decl
  env' <- extendR env $ traverseDeclsOpen def decls
  return (env <> env')

traverseDecl :: (MonadEmbed m, MonadReader SubstEnv m)
             => TraversalDef m -> Decl -> m SubstEnv
traverseDecl (fExpr, _) decl = case decl of
  Let letAnn b expr -> do
    expr' <- fExpr expr
    x <- emitTo (binderNameHint b) letAnn expr'
    return $ b @> x
  Unpack bs expr -> do
    expr' <- fExpr expr
    xs <- emitUnpack expr'
    return $ newEnv bs xs

traverseBlock :: (MonadEmbed m, MonadReader SubstEnv m)
              => TraversalDef m -> Block -> m Block
traverseBlock def block = buildScoped $ evalBlockE def block

evalBlockE :: (MonadEmbed m, MonadReader SubstEnv m)
              => TraversalDef m -> Block -> m Atom
evalBlockE def@(fExpr, _) (Block decls result) = do
  env <- traverseDeclsOpen def decls
  resultExpr <- extendR env $ fExpr result
  case resultExpr of
    Atom a -> return a
    _      -> emit resultExpr

traverseExpr :: (MonadEmbed m, MonadReader SubstEnv m)
             => TraversalDef m -> Expr -> m Expr
traverseExpr def@(_, fAtom) expr = case expr of
  App g x -> App  <$> fAtom g <*> fAtom x
  Atom x  -> Atom <$> fAtom x
  Op  op  -> Op   <$> traverse fAtom op
  Hof hof -> Hof  <$> traverse fAtom hof
  Case e alts ty ->
    Case <$> fAtom e <*> mapM (traverseAlt def) alts <*> fAtom ty

traverseAlt :: (MonadEmbed m, MonadReader SubstEnv m)
             => TraversalDef m -> Alt -> m Alt
traverseAlt def@(_, fAtom) (Abs bs body) = do
  bs' <- mapM (mapM fAtom) bs
  buildNAbs bs' $ \xs -> extendR (newEnv bs' xs) $ evalBlockE def body

traverseAtom :: (MonadEmbed m, MonadReader SubstEnv m)
             => TraversalDef m -> Atom -> m Atom
traverseAtom def@(_, fAtom) atom = case atom of
  Var _ -> substEmbedR atom
  Lam (Abs b (arr, body)) -> do
    b' <- mapM fAtom b
    buildDepEffLam b'
      (\x -> extendR (b'@>x) (substEmbedR arr))
      (\x -> extendR (b'@>x) (evalBlockE def body))
  Pi _ -> substEmbedR atom
  Con con -> Con <$> traverse fAtom con
  TC  tc  -> TC  <$> traverse fAtom tc
  Eff _   -> substEmbedR atom
  DataCon dataDef params con args -> DataCon dataDef <$>
    traverse fAtom params <*> pure con <*> traverse fAtom args
  TypeCon dataDef params -> TypeCon dataDef <$> traverse fAtom params
  Record items -> Record <$> traverse fAtom items
  RecordTy items -> RecordTy <$> traverse fAtom items
  Variant types label i value -> Variant <$>
    traverse fAtom types <*> pure label <*> pure i <*> fAtom value
  VariantTy items -> VariantTy <$> traverse fAtom items

-- === DCE ===

type DceM = WriterT [Decl] (Cat Scope)

dceModule :: Module -> Module
dceModule (Module ir decls bindings) =
  Module ir (dceDecls (freeVars bindings) decls) bindings

dceBlock :: Block -> Block
dceBlock (Block decls result) =
  inlineLastDecl $ Block (dceDecls (freeVars result) decls) result

dceDecls :: Scope -> Nest Decl -> Nest Decl
dceDecls varsNeeded decls = toNest $ reverse $ fst $ flip runCat varsNeeded $
  execWriterT $ mapM dceDecl $ reverse $ toList decls

inlineLastDecl :: Block -> Block
inlineLastDecl block@(Block decls result) =
  case (reverse (toList decls), result) of
    (Let _ (Bind v) expr:rest, Atom atom)
      | atom == Var v || sameSingletonVal (varType v) (getType atom) ->
          Block (toNest (reverse rest)) expr
    _ -> block

dceDecl :: Decl -> DceM ()
dceDecl decl = do
  varsNeeded <- look
  case decl of
    Let ann b expr -> do
      if b `isin` varsNeeded
        then tell [decl] >> extend (freeVars expr)
        else case exprEffs expr of
          NoEffects   -> return ()
          SomeEffects -> do
            tell [Let ann (Ignore (binderType b)) expr]
            extend (freeVars expr)
    Unpack bs expr -> do
      if any (`isin` varsNeeded) bs || (not $ isPure expr)
        then tell [decl] >> extend (freeVars expr)
        else return ()

sameSingletonVal :: Type -> Type -> Bool
sameSingletonVal t1 t2 = case singletonTypeVal t1 of
  Just x1 -> case singletonTypeVal t2 of
    Just x2 | x1 == x2 -> True
    _ -> False
  _ -> False

-- === partial evaluation using definitions in scope ===

reduceScoped :: MonadEmbed m => m Atom -> m (Maybe Atom)
reduceScoped m = do
  block <- buildScoped m
  scope <- getScope
  return $ reduceBlock scope block

reduceBlock :: Scope -> Block -> Maybe Atom
reduceBlock scope (Block decls result) = do
  let localScope = foldMap boundVars decls
  ans <- reduceExpr (scope <> localScope) result
  [] <- return $ toList $ localScope `envIntersect` freeVars ans
  return ans

reduceAtom :: Scope -> Atom -> Atom
reduceAtom scope x = case x of
  Var v -> case snd (scope ! v) of
    -- TODO: worry about effects!
    LetBound PlainLet expr -> fromMaybe x $ reduceExpr scope expr
    _ -> x
  _ -> x

reduceExpr :: Scope -> Expr -> Maybe Atom
reduceExpr scope expr = case expr of
  Atom val -> return $ reduceAtom scope val
  App f x -> do
    let f' = reduceAtom scope f
    let x' = reduceAtom scope x
    -- TODO: Worry about variable capture. Should really carry a substitution.
    case f' of
      Lam (Abs b (PureArrow, block)) ->
        reduceBlock scope $ subst (b@>x', scope) block
      TypeCon con xs -> Just $ TypeCon con $ xs ++ [x']
      _ -> Nothing
  _ -> Nothing

indexSetSizeE :: MonadEmbed m => Type -> m Atom
indexSetSizeE (TC con) = case con of
  UnitType                   -> return $ asIntVal 1
  IntRange low high -> clampPositive =<< high `isub` low
  IndexRange n low high -> do
    low' <- case low of
      InclusiveLim x -> indexToIntE n x
      ExclusiveLim x -> indexToIntE n x >>= iadd (asIntVal 1)
      Unlimited      -> return $ asIntVal 0
    high' <- case high of
      InclusiveLim x -> indexToIntE n x >>= iadd (asIntVal 1)
      ExclusiveLim x -> indexToIntE n x
      Unlimited      -> indexSetSizeE n
    clampPositive =<< high' `isub` low'
  PairType a b -> bindM2 imul (indexSetSizeE a) (indexSetSizeE b)
  _ -> error $ "Not implemented " ++ pprint con
  where
indexSetSizeE (RecordTy types) = do
  sizes <- traverse indexSetSizeE types
  foldM imul (asIntVal 1) sizes
indexSetSizeE (VariantTy types) = do
  sizes <- traverse indexSetSizeE types
  foldM iadd (asIntVal 0) sizes
indexSetSizeE ty = error $ "Not implemented " ++ pprint ty

clampPositive :: MonadEmbed m => Atom -> m Atom
clampPositive x = do
  isNegative <- x `ilt` (asIntVal 0)
  select isNegative (asIntVal 0) x

-- XXX: Be careful if you use this function as an interpretation for
--      IndexAsInt instruction, as for Int and IndexRanges it will
--      generate the same instruction again, potentially leading to an
--      infinite loop.
indexToIntE :: MonadEmbed m => Type -> Atom -> m Atom
indexToIntE ty idx = case ty of
  UnitTy  -> return $ asIntVal 0
  BoolTy  -> boolToInt idx
  PairTy lType rType -> do
    (lVal, rVal) <- fromPair idx
    lIdx  <- indexToIntE lType lVal
    rIdx  <- indexToIntE rType rVal
    rSize <- indexSetSizeE rType
    imul rSize lIdx >>= iadd rIdx
  TC (IntRange _ _)     -> indexAsInt idx
  TC (IndexRange _ _ _) -> indexAsInt idx
  RecordTy types -> do
    sizes <- traverse indexSetSizeE types
    (strides, _) <- scanM
      (\sz prev -> do {v <- imul sz prev; return (prev, v)}) sizes (asIntVal 1)
    -- Unpack and sum the strided contributions
    subindices <- getUnpacked idx
    subints <- traverse (uncurry indexToIntE) (zip (toList types) subindices)
    scaled <- mapM (uncurry imul) $ zip (toList strides) subints
    foldM iadd (asIntVal 0) scaled
  VariantTy types -> do
    sizes <- traverse indexSetSizeE types
    (offsets, _) <- scanM
      (\sz prev -> do {v <- iadd sz prev; return (prev, v)}) sizes (asIntVal 0)
    -- Build and apply a case expression
    alts <- flip mapM (zip (toList offsets) (toList types)) $
      \(offset, subty) -> buildNAbs (toNest [Ignore subty]) $ \[subix] -> do
        i <- indexToIntE subty subix
        iadd offset i
    emit $ Case idx alts IntTy
  _ -> error $ "Unexpected type " ++ pprint ty

intToIndexE :: MonadEmbed m => Type -> Atom -> m Atom
intToIndexE ty@(TC con) i = case con of
  IntRange   _ _             -> iAsIdx
  IndexRange _ _ _           -> iAsIdx
  UnitType                   -> return $ UnitVal
  PairType a b -> do
    bSize <- indexSetSizeE b
    iA <- intToIndexE a =<< idiv i bSize
    iB <- intToIndexE b =<< irem i bSize
    return $ PairVal iA iB
  _ -> error $ "Unexpected type " ++ pprint con
  where iAsIdx = return $ Con $ Coerce ty i
intToIndexE (RecordTy types) i = do
  sizes <- traverse indexSetSizeE types
  (strides, _) <- scanM
    (\sz prev -> do {v <- imul sz prev; return ((prev, v), v)}) sizes (asIntVal 1)
  offsets <- flip mapM (zip (toList types) (toList strides)) $
    \(ty, (s1, s2)) -> do
      x <- irem i s2
      y <- idiv x s1
      intToIndexE ty y
  return $ Record (restructure offsets types)
intToIndexE (VariantTy types) i = do
  sizes <- traverse indexSetSizeE types
  (offsets, _) <- scanM
    (\sz prev -> do {v <- iadd sz prev; return (prev, v)}) sizes (asIntVal 0)
  let
    reflect = reflectLabels types
    -- Find the right index by looping through the possible offsets
    -- TODO: is there a better way than generating a case statement? Select
    -- doesn't work because variants aren't primitive types
    go prev ((label, repeatNum), ty, offset) = do
      beforeThis <- ilt i offset
      boolCase beforeThis (return prev) $ do
        shifted <- isub i offset
        index <- intToIndexE ty shifted
        return $ Variant types label repeatNum index
    ((l0, 0), ty0, _):zs =
      zip3 (toList reflect) (toList types) (toList offsets)
  start <- Variant types l0 0 <$> intToIndexE ty0 i
  foldM go start zs
intToIndexE ty _ = error $ "Unexpected type " ++ pprint ty

anyValue :: Type -> Atom
anyValue (TC RealType) = asRealVal 1.0
anyValue (TC IntType)  = asIntVal  1
anyValue (TC BoolType) = asBoolVal False
-- TODO: Base types!
-- XXX: This is not strictly correct, because those types might not have any
--      inhabitants. We might want to consider emitting some run-time code that
--      aborts the program if this really ends up being the case.
anyValue t@(TC (IntRange _ _))             = Con $ Coerce t $ asIntVal 0
anyValue t@(TC (IndexRange _ _ _))         = Con $ Coerce t $ asIntVal 0
anyValue t = error $ "Expected a scalar type in anyValue, got: " ++ pprint t
