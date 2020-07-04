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
              buildLam, EmbedT, Embed, MonadEmbed, buildScoped, wrapDecls, runEmbedT,
              runSubstEmbed, runEmbed, zeroAt, addAt, sumAt, getScope, reduceBlock,
              app, add, mul, sub, neg, div', andE, iadd, imul, isub, idiv, reduceScoped,
              select, selectAt, substEmbed, fromPair, getFst, getSnd,
              emitBlock, unzipTab, buildFor, isSingletonType, emitDecl, withNameHint,
              singletonTypeVal, mapScalars, scopedDecls, embedScoped, extendScope,
              embedExtend, boolToInt, intToReal, boolToReal, reduceAtom,
              unpackConsList, emitRunWriter, emitRunReader, tabGet,
              SubstEmbedT, runSubstEmbedT,
              TraversalDef, traverseDecls, traverseBlock, traverseExpr,
              traverseAtom, arrOffset, arrLoad,
              sumTag, getLeft, getRight, fromSum, clampPositive,
              indexSetSizeE, indexToIntE, intToIndexE, anyValue) where

import Control.Applicative
import Control.Monad
import Control.Monad.Fail
import Control.Monad.Except hiding (Except)
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Identity
import Data.Foldable (toList)
import Data.Maybe

import Env
import Syntax
import Cat
import Type
import PPrint
import Util (bindM2)

newtype EmbedT m a = EmbedT (ReaderT EmbedEnvR (CatT EmbedEnvC m) a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail, Alternative)

type Embed = EmbedT Identity
type EmbedEnv = (EmbedEnvR, EmbedEnvC)

type SubstEmbedT m = ReaderT SubstEnv (EmbedT m)

-- Carries the vars in scope (with optional definitions) and the emitted decls
type EmbedEnvC = (Scope, [Decl])
-- Carries a name suggestion and the allowable effects
type EmbedEnvR = (Tag, EffectRow)

runEmbedT :: Monad m => EmbedT m a -> Scope -> m (a, EmbedEnvC)
runEmbedT (EmbedT m) scope = do
  (ans, env) <- runCatT (runReaderT m ("tmp", Pure)) (scope, [])
  return (ans, env)

runEmbed :: Embed a -> Scope -> (a, EmbedEnvC)
runEmbed m scope = runIdentity $ runEmbedT m scope

runSubstEmbedT :: Monad m => SubstEmbedT m a -> Scope -> m (a, EmbedEnvC)
runSubstEmbedT m scope = runEmbedT (runReaderT m mempty) scope

runSubstEmbed :: SubstEmbedT Identity a -> Scope -> (a, EmbedEnvC)
runSubstEmbed m scope = runIdentity $ runEmbedT (runReaderT m mempty) scope

emit :: MonadEmbed m => Expr -> m Atom
emit = emitAnn PlainLet

emitAnn :: MonadEmbed m => LetAnn -> Expr -> m Atom
emitAnn ann expr = do
  v <- getNameHint
  emitTo v ann expr

-- Guarantees that the name will be used, possibly with a modified counter
emitTo :: MonadEmbed m => Name -> LetAnn -> Expr -> m Atom
emitTo v ann expr = do
  let ty = getType expr
  expr' <- deShadow expr <$> getScope
  v' <- freshVar (v:>ty)
  emitDecl $ Let ann v' expr'
  return $ Var v'

-- Disabling this path for now because we need to be more careful to not throw
-- away global names
  -- case singletonTypeVal ty of
  --   Just x
  --     | isPure expr -> return x
  --     | otherwise -> do
  --         expr' <- deShadow expr <$> getScope
  --         emitDecl $ Let ann (NoName:>ty) expr'
  --         return x

emitOp :: MonadEmbed m => Op -> m Atom
emitOp op = emit $ Op op

-- Assumes the decl binders are already fresh wrt current scope
emitBlock :: MonadEmbed m => Block -> m Atom
emitBlock (Block decls result) = mapM_ emitDecl decls >> emit result

freshVar :: MonadEmbed m => VarP ann -> m (VarP ann)
freshVar v = do
  scope <- getScope
  let v' = rename v scope
  return v'

buildPi :: (MonadError Err m, MonadEmbed m)
        => Var -> (Atom -> m (Arrow, Type)) -> m Atom
buildPi b f = do
  (piTy, decls) <- scopedDecls $ do
     b' <- freshVar b
     embedExtend $ asFst $ b' @> (varType b', PiBound)
     (arr, ans) <- f $ Var b'
     return $ Pi $ Abs b' (arr, ans)
  unless (null decls) $ throw CompilerErr $ "Unexpected decls: " ++ pprint decls
  return piTy

buildLam :: MonadEmbed m => Var -> Arrow -> (Atom -> m Atom) -> m Atom
buildLam b arr body = buildDepEffLam b (const (return arr)) body

buildDepEffLam :: MonadEmbed m
               => Var -> (Atom -> m Arrow) -> (Atom -> m Atom) -> m Atom
buildDepEffLam b fArr fBody = liftM fst $ buildLamAux b fArr $ \x -> (,()) <$> fBody x

buildLamAux :: MonadEmbed m
            => Var -> (Atom -> m Arrow) -> (Atom -> m (Atom, a)) -> m (Atom, a)
buildLamAux b fArr fBody = do
  ((b', arr, ans, aux), decls) <- scopedDecls $ do
     b' <- freshVar b
     -- TODO: we can't extend the scope until we know the arrow, but we really
     -- ought to extend it before we run fArr. Since effects don't contain
     -- binders, we're probably ok. But it would be cleaner if we just
     -- decoupled arrow from effect.
     let x = Var b'
     arr <- fArr x
     embedExtend $ asFst $ b' @> (varType b', LamBound (void arr))
     (ans, aux) <- withEffects (arrowEff arr) $ fBody x
     return (b', arr, ans, aux)
  return (Lam $ Abs b' (arr, wrapDecls decls ans), aux)

buildScoped :: MonadEmbed m => m Atom -> m Block
buildScoped m = do
  (ans, decls) <- scopedDecls m
  return $ wrapDecls decls ans

wrapDecls :: [Decl] -> Atom -> Block
wrapDecls decls atom = case reverse decls of
  -- decluttering optimization
  Let _ v expr:rest | atom == Var v -> Block (reverse rest) expr
  _ -> Block decls (Atom atom)

-- TODO: consider broadcasted literals as atoms, so we don't need the monad here
zeroAt :: MonadEmbed m => Type -> m Atom
zeroAt ty = mapScalars (\_ _ -> return $ Con $ Lit (RealLit 0.0)) ty []

addAt :: MonadEmbed m => Type -> Atom -> Atom -> m Atom
addAt ty xs ys = mapScalars (\_ [x, y] -> add x y) ty [xs, ys]

selectAt :: MonadEmbed m => Type -> Atom -> Atom -> Atom -> m Atom
selectAt ty p xs ys = mapScalars (\_ [x, y] -> select p x y) ty [xs, ys]

sumAt :: MonadEmbed m => Type -> [Atom] -> m Atom
sumAt ty [] = zeroAt ty
sumAt _ [x] = return x
sumAt ty (x:xs) = do
  xsSum <- sumAt ty xs
  addAt ty xsSum x

neg :: MonadEmbed m => Atom -> m Atom
neg x = emitOp $ ScalarUnOp FNeg x

add :: MonadEmbed m => Atom -> Atom -> m Atom
add (RealVal 0) y = return y
add x y           = emitOp $ ScalarBinOp FAdd x y

iadd :: MonadEmbed m => Atom -> Atom -> m Atom
iadd (IntVal 0) y          = return y
iadd x          (IntVal 0) = return x
iadd (IntVal x) (IntVal y) = return $ IntVal $ x + y
iadd x y          = emitOp $ ScalarBinOp IAdd x y

mul :: MonadEmbed m => Atom -> Atom -> m Atom
mul x y = emitOp $ ScalarBinOp FMul x y

imul :: MonadEmbed m => Atom -> Atom -> m Atom
imul (IntVal 1) y          = return y
imul x          (IntVal 1) = return x
imul (IntVal x) (IntVal y) = return $ IntVal $ x * y
imul x y = emitOp $ ScalarBinOp IMul x y

sub :: MonadEmbed m => Atom -> Atom -> m Atom
sub x y = emitOp $ ScalarBinOp FSub x y

isub :: MonadEmbed m => Atom -> Atom -> m Atom
isub x          (IntVal 0) = return x
isub (IntVal x) (IntVal y) = return $ IntVal $ x - y
isub x y = emitOp $ ScalarBinOp ISub x y

andE :: MonadEmbed m => Atom -> Atom -> m Atom
andE (BoolVal True) y = return y
andE x y              = emit $ Op $ ScalarBinOp And x y

select :: MonadEmbed m => Atom -> Atom -> Atom -> m Atom
select (BoolVal b) x y = return $ if b then x else y
select p x y = emitOp $ Select p x y

div' :: MonadEmbed m => Atom -> Atom -> m Atom
div' x y = emitOp $ ScalarBinOp FDiv x y

idiv :: MonadEmbed m => Atom -> Atom -> m Atom
idiv x          (IntVal 1) = return x
idiv (IntVal x) (IntVal y) = return $ IntVal $ x `div` y
idiv x y = emitOp $ ScalarBinOp IDiv x y

irem :: MonadEmbed m => Atom -> Atom -> m Atom
irem x y = emitOp $ ScalarBinOp Rem x y

ilt :: MonadEmbed m => Atom -> Atom -> m Atom
ilt (IntVal x) (IntVal y) = return $ BoolVal $ x < y
ilt x y = emitOp $ ScalarBinOp (ICmp Less) x y

getFst :: MonadEmbed m => Atom -> m Atom
getFst (PairVal x _) = return x
getFst p = emitOp $ Fst p

getSnd :: MonadEmbed m => Atom -> m Atom
getSnd (PairVal _ y) = return y
getSnd p = emitOp $ Snd p

app :: MonadEmbed m => Atom -> Atom -> m Atom
app x i = emit $ App x i

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

sumTag :: MonadEmbed m => Atom -> m Atom
sumTag (SumVal t _ _) = return t
sumTag s = emitOp $ SumTag s

getLeft :: MonadEmbed m => Atom -> m Atom
getLeft (SumVal _ l _) = return l
getLeft s = emitOp $ SumGet s True

getRight :: MonadEmbed m => Atom -> m Atom
getRight (SumVal _ _ r) = return r
getRight s = emitOp $ SumGet s False

fromSum :: MonadEmbed m => Atom -> m (Atom, Atom, Atom)
fromSum s = (,,) <$> sumTag s <*> getLeft s <*> getRight s

emitRunWriter :: MonadEmbed m => Name -> Type -> (Atom -> m Atom) -> m Atom
emitRunWriter v ty body = do
  eff <- getAllowedEffects
  lam <- buildLam ("r":>TyKind) PureArrow $ \r@(Var (rName:>_)) -> do
    let arr = PlainArrow $ extendEffect (Writer, rName) eff
    buildLam (v:> RefTy r ty) arr body
  emit $ Hof $ RunWriter lam

emitRunReader :: MonadEmbed m => Name -> Atom -> (Atom -> m Atom) -> m Atom
emitRunReader v x0 body = do
  eff <- getAllowedEffects
  lam <- buildLam ("r":>TyKind) PureArrow $ \r@(Var (rName:>_)) -> do
    let arr = PlainArrow $ extendEffect (Reader, rName) eff
    buildLam (v:> RefTy r (getType x0)) arr body
  emit $ Hof $ RunReader x0 lam

buildFor :: MonadEmbed m => Direction -> Var -> (Atom -> m Atom) -> m Atom
buildFor d i body = do
  -- TODO: track effects in the embedding env so we can add them here
  eff <- getAllowedEffects
  lam <- buildLam i (PlainArrow eff) body
  emit $ Hof $ For d lam

tabGet :: MonadEmbed m => Atom -> Atom -> m Atom
tabGet x i = emit $ App x i

unzipTab :: MonadEmbed m => Atom -> m (Atom, Atom)
unzipTab tab = do
  fsts <- buildFor Fwd ("i":>varType v) $ \i ->
            liftM fst $ app tab i >>= fromPair
  snds <- buildFor Fwd ("i":>varType v) $ \i ->
            liftM snd $ app tab i >>= fromPair
  return (fsts, snds)
  where TabTy v _ = getType tab

mapScalars :: MonadEmbed m => (Type -> [Atom] -> m Atom) -> Type -> [Atom] -> m Atom
mapScalars f ty xs = case ty of
  TabTy v a -> do
    buildFor Fwd ("i":>varType v) $ \i -> do
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

substEmbed :: (MonadEmbed m, MonadReader SubstEnv m, HasVars a)
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

unsafeIntToBool :: MonadEmbed m => Atom -> m Atom
unsafeIntToBool b = emitOp $ ScalarUnOp UnsafeIntToBool b

indexAsInt :: MonadEmbed m => Atom -> m Atom
indexAsInt idx = emitOp $ IndexAsInt idx

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
withNameHint :: MonadEmbed m => Name -> m a -> m a
withNameHint name m = embedLocal (\(_, eff) -> (tag, eff)) m
  where
    tag = case name of
      Name _ t _   -> t
      GlobalName t -> t
      NoName       -> "tmp"

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
emitDecl decl@(Let ann v expr) = embedExtend (bindings, [decl])
  where bindings = v @> (varType v, LetBound ann expr)

scopedDecls :: MonadEmbed m => m a -> m (a, [Decl])
scopedDecls m = do
  (ans, (_, decls)) <- embedScoped m
  return (ans, decls)

-- === generic traversal ===

type TraversalDef m = (Expr -> m Expr, Atom -> m Atom)

-- With `def = (traverseExpr def, traverseAtom def)` this should be a no-op
traverseDecls :: (MonadEmbed m, MonadReader SubstEnv m)
               => TraversalDef m -> [Decl] -> m [Decl]
traverseDecls def decls = liftM snd $ scopedDecls $ traverseDeclsOpen def decls

traverseDeclsOpen :: (MonadEmbed m, MonadReader SubstEnv m)
               => TraversalDef m -> [Decl] -> m SubstEnv
traverseDeclsOpen _ [] = return mempty
traverseDeclsOpen def@(fExpr, _) (Let letAnn b expr : decls) = do
    expr' <- fExpr expr
    x <- emitTo (varName b) letAnn expr'
    let env = b @> x
    env' <- extendR env $ traverseDeclsOpen def decls
    return (env <> env')

traverseBlock :: (MonadEmbed m, MonadReader SubstEnv m)
              => TraversalDef m -> Block -> m Block
traverseBlock def block = buildScoped $ traverseBlock' def block

traverseBlock' :: (MonadEmbed m, MonadReader SubstEnv m)
              => TraversalDef m -> Block -> m Atom
traverseBlock' def@(fExpr, _) (Block decls result) = do
  env <- traverseDeclsOpen def decls
  extendR env $ fExpr result >>= emit

traverseExpr :: (MonadEmbed m, MonadReader SubstEnv m)
             => TraversalDef m -> Expr -> m Expr
traverseExpr (_, fAtom) expr = case expr of
  App g x -> App  <$> fAtom g <*> fAtom x
  Atom x  -> Atom <$> fAtom x
  Op  op  -> Op   <$> traverse fAtom op
  Hof hof -> Hof  <$> traverse fAtom hof

traverseAtom :: (MonadEmbed m, MonadReader SubstEnv m)
             => TraversalDef m -> Atom -> m Atom
traverseAtom def@(_, fAtom) atom = case atom of
  Var _ -> substEmbed atom
  Lam (Abs b (arr, body)) -> do
    b' <- mapM fAtom b
    buildDepEffLam b'
      (\x -> extendR (b'@>x) (substEmbed arr))
      (\x -> extendR (b'@>x) (traverseBlock' def body))
  Pi _ -> substEmbed atom
  Con con -> Con <$> traverse fAtom con
  TC  tc  -> TC  <$> traverse fAtom tc
  Eff _   -> substEmbed atom

-- === partial evaluation using definitions in scope ===

reduceScoped :: MonadEmbed m => m Atom -> m (Maybe Atom)
reduceScoped m = do
  block <- buildScoped m
  scope <- getScope
  return $ reduceBlock scope block

reduceBlock :: Scope -> Block -> Maybe Atom
reduceBlock scope (Block decls result) = do
  let localScope = foldMap declAsScope decls
  ans <- reduceExpr (scope <> localScope) result
  [] <- return $ toList $ localScope `envIntersect` freeVars ans
  return ans

reduceAtom :: Scope -> Atom -> Atom
reduceAtom scope x = case x of
  Var v -> case snd (scope ! v) of
    -- TODO: worry about effects!
    LetBound PlainLet expr -> fromMaybe x $ reduceExpr scope expr
    LetBound NewtypeLet _  -> TC $ NewtypeApp x []
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
      TC (NewtypeApp wrapper xs) ->
        Just $ TC $ NewtypeApp wrapper (xs ++ [x'])
      _ -> Nothing
  _ -> Nothing

indexSetSizeE :: MonadEmbed m => Type -> m Atom
indexSetSizeE (TC con) = case con of
  BaseType (Scalar BoolType) -> return $ IntVal 2
  IntRange low high -> clampPositive =<< high `isub` low
  IndexRange n low high -> do
    low' <- case low of
      InclusiveLim x -> indexToIntE n x
      ExclusiveLim x -> indexToIntE n x >>= iadd (IntVal 1)
      Unlimited      -> return $ IntVal 0
    high' <- case high of
      InclusiveLim x -> indexToIntE n x >>= iadd (IntVal 1)
      ExclusiveLim x -> indexToIntE n x
      Unlimited      -> indexSetSizeE n
    clampPositive =<< high' `isub` low'
  PairType a b -> bindM2 imul (indexSetSizeE a) (indexSetSizeE b)
  SumType l r -> bindM2 iadd (indexSetSizeE l) (indexSetSizeE r)
  _ -> error $ "Not implemented " ++ pprint con
  where
indexSetSizeE ty = error $ "Not implemented " ++ pprint ty

clampPositive :: MonadEmbed m => Atom -> m Atom
clampPositive x = do
  isNegative <- x `ilt` (IntVal 0)
  select isNegative (IntVal 0) x

-- XXX: Be careful if you use this function as an interpretation for
--      IndexAsInt instruction, as for Int and IndexRanges it will
--      generate the same instruction again, potentially leading to an
--      infinite loop.
indexToIntE :: MonadEmbed m => Type -> Atom -> m Atom
indexToIntE ty idx = case ty of
  BoolTy  -> boolToInt idx
  SumTy lType rType -> do
    (tag, lVal, rVal) <- fromSum idx
    lTypeSize <- indexSetSizeE lType
    lInt      <- indexToIntE lType lVal
    rInt      <- iadd lTypeSize =<< indexToIntE rType rVal
    select tag lInt rInt
  PairTy lType rType -> do
    (lVal, rVal) <- fromPair idx
    lIdx  <- indexToIntE lType lVal
    rIdx  <- indexToIntE rType rVal
    rSize <- indexSetSizeE rType
    imul rSize lIdx >>= iadd rIdx
  TC (IntRange _ _)     -> indexAsInt idx
  TC (IndexRange _ _ _) -> indexAsInt idx
  _ -> error $ "Unexpected type " ++ pprint ty

intToIndexE :: MonadEmbed m => Type -> Atom -> m Atom
intToIndexE ty@(TC con) i = case con of
  IntRange _ _      -> iAsIdx
  IndexRange _ _ _  -> iAsIdx
  BaseType (Scalar BoolType) -> unsafeIntToBool i
  PairType a b -> do
    bSize <- indexSetSizeE b
    iA <- intToIndexE a =<< idiv i bSize
    iB <- intToIndexE b =<< irem i bSize
    return $ PairVal iA iB
  SumType l r -> do
    lSize <- indexSetSizeE l
    isLeft <- i `ilt` lSize
    li <- intToIndexE l i
    ri <- intToIndexE r =<< i `isub` lSize
    return $ Con $ SumCon isLeft li ri
  _ -> error $ "Unexpected type " ++ pprint con
  where iAsIdx = return $ Con $ Coerce ty i
intToIndexE ty _ = error $ "Unexpected type " ++ pprint ty

anyValue :: Type -> Atom
anyValue (TC (BaseType (Scalar RealType))) = RealVal 1.0
anyValue (TC (BaseType (Scalar IntType)))  = IntVal 1
anyValue (TC (BaseType (Scalar BoolType))) = BoolVal False
anyValue (TC (BaseType (Scalar StrType)))  = Con $ Lit $ StrLit ""
-- XXX: This is not strictly correct, because those types might not have any
--      inhabitants. We might want to consider emitting some run-time code that
--      aborts the program if this really ends up being the case.
anyValue t@(TC (IntRange _ _))             = Con $ Coerce t $ IntVal 0
anyValue t@(TC (IndexRange _ _ _))         = Con $ Coerce t $ IntVal 0
anyValue t = error $ "Expected a scalar type in anyValue, got: " ++ pprint t
