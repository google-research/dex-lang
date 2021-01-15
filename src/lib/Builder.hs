-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module Builder (emit, emitTo, emitAnn, emitOp, buildDepEffLam, buildLamAux, buildPi,
                getAllowedEffects, withEffects, modifyAllowedEffects,
                buildLam, BuilderT, Builder, MonadBuilder, buildScoped, runBuilderT,
                runSubstBuilder, runBuilder, getScope, builderLook, liftBuilder,
                app,
                add, mul, sub, neg, div',
                iadd, imul, isub, idiv, ilt, ieq,
                fpow, flog, fLitLike, recGetHead, buildImplicitNaryLam,
                select, substBuilder, substBuilderR, emitUnpack, getUnpacked,
                fromPair, getFst, getSnd, getFstRef, getSndRef,
                naryApp, appReduce, appTryReduce, buildAbs,
                buildFor, buildForAux, buildForAnn, buildForAnnAux,
                emitBlock, unzipTab, isSingletonType, emitDecl, withNameHint,
                singletonTypeVal, scopedDecls, builderScoped, extendScope, checkBuilder,
                builderExtend, applyPreludeFunction,
                unpackConsList, unpackLeftLeaningConsList,
                emitRunWriter, emitRunWriters, mextendForRef, monoidLift,
                emitRunState, emitMaybeCase, emitWhile, buildDataDef,
                emitRunReader, tabGet, SubstBuilderT, SubstBuilder, runSubstBuilderT,
                ptrOffset, ptrLoad, unsafePtrLoad,
                evalBlockE, substTraversalDef,
                TraversalDef, traverseDecls, traverseDecl, traverseDeclsOpen,
                traverseBlock, traverseExpr, traverseAtom,
                clampPositive, buildNAbs, buildNAbsAux, buildNestedLam,
                transformModuleAsBlock, dropSub, appReduceTraversalDef,
                indexSetSizeE, indexToIntE, intToIndexE, freshVarE) where

import Control.Applicative
import Control.Monad
import Control.Monad.Except hiding (Except)
import Control.Monad.Reader
import Control.Monad.Writer hiding (Alt)
import Control.Monad.Identity
import Control.Monad.State.Strict
import Data.Foldable (toList)
import Data.List (elemIndex)
import Data.Maybe (fromJust)
import Data.String (fromString)
import Data.Tuple (swap)
import GHC.Stack

import Env
import Syntax
import Cat
import Type
import PPrint
import Util (bindM2, scanM, restructure)

newtype BuilderT m a = BuilderT (ReaderT BuilderEnvR (CatT BuilderEnvC m) a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail, Alternative)

type Builder = BuilderT Identity
type BuilderEnv = (BuilderEnvR, BuilderEnvC)

type SubstBuilderT m = ReaderT SubstEnv (BuilderT m)
type SubstBuilder    = SubstBuilderT Identity

-- Carries the vars in scope (with optional definitions) and the emitted decls
type BuilderEnvC = (Scope, Nest Decl)
-- Carries a name suggestion and the allowable effects
type BuilderEnvR = (Tag, EffectRow)

runBuilderT :: Monad m => BuilderT m a -> Scope -> m (a, BuilderEnvC)
runBuilderT (BuilderT m) scope = do
  (ans, env) <- runCatT (runReaderT m ("tmp", Pure)) (scope, Empty)
  return (ans, env)

runBuilder :: Builder a -> Scope -> (a, BuilderEnvC)
runBuilder m scope = runIdentity $ runBuilderT m scope

runSubstBuilderT :: Monad m => SubstBuilderT m a -> Scope -> m (a, BuilderEnvC)
runSubstBuilderT m scope = runBuilderT (runReaderT m mempty) scope

runSubstBuilder :: SubstBuilder a -> Scope -> (a, BuilderEnvC)
runSubstBuilder m scope = runIdentity $ runBuilderT (runReaderT m mempty) scope

emit :: MonadBuilder m => Expr -> m Atom
emit expr     = emitAnn PlainLet expr

emitAnn :: MonadBuilder m => LetAnn -> Expr -> m Atom
emitAnn ann expr = do
  v <- getNameHint
  emitTo v ann expr

-- Guarantees that the name will be used, possibly with a modified counter
emitTo :: MonadBuilder m => Name -> LetAnn -> Expr -> m Atom
emitTo name ann expr = do
  scope <- getScope
  -- Deshadow type because types from DataDef may have binders that shadow local vars
  let ty    = deShadow (getType expr) scope
  let expr' = deShadow expr scope
  v <- freshVarE (LetBound ann expr') $ Bind (name:>ty)
  builderExtend $ asSnd $ Nest (Let ann (Bind v) expr') Empty
  return $ Var v

emitOp :: MonadBuilder m => Op -> m Atom
emitOp op = emit $ Op op

emitUnpack :: MonadBuilder m => Expr -> m [Atom]
emitUnpack expr = getUnpacked =<< emit expr

emitBlock :: MonadBuilder m => Block -> m Atom
emitBlock block = emitBlockRec mempty block

emitBlockRec :: MonadBuilder m => SubstEnv -> Block -> m Atom
emitBlockRec env (Block (Nest (Let ann b expr) decls) result) = do
  expr' <- substBuilder env expr
  x <- emitTo (binderNameHint b) ann expr'
  emitBlockRec (env <> b@>x) $ Block decls result
emitBlockRec env (Block Empty (Atom atom)) = substBuilder env atom
emitBlockRec env (Block Empty expr) = substBuilder env expr >>= emit

freshVarE :: MonadBuilder m => BinderInfo -> Binder -> m Var
freshVarE bInfo b = do
  v <- case b of
    Ignore _    -> getNameHint
    Bind (v:>_) -> return v
  scope <- getScope
  let v' = genFresh v scope
  builderExtend $ asFst $ v' @> (binderType b, bInfo)
  return $ v' :> binderType b

freshNestedBinders :: MonadBuilder m => Nest Binder -> m (Nest Var)
freshNestedBinders bs = freshNestedBindersRec mempty bs

freshNestedBindersRec :: MonadBuilder m => Env Atom -> Nest Binder -> m (Nest Var)
freshNestedBindersRec _ Empty = return Empty
freshNestedBindersRec substEnv (Nest b bs) = do
  scope <- getScope
  v  <- freshVarE PatBound $ subst (substEnv, scope) b
  vs <- freshNestedBindersRec (substEnv <> b@>Var v) bs
  return $ Nest v vs

buildPi :: (MonadError Err m, MonadBuilder m)
        => Binder -> (Atom -> m (Arrow, Type)) -> m Atom
buildPi b f = do
  scope <- getScope
  (ans, decls) <- scopedDecls $ do
     v <- freshVarE PiBound b
     (arr, ans) <- f $ Var v
     return $ Pi $ makeAbs (Bind v) (arr, ans)
  let block = wrapDecls decls ans
  case typeReduceBlock scope block of
    Just piTy -> return piTy
    Nothing -> throw CompilerErr $
      "Unexpected irreducible decls in pi type: " ++ pprint decls

buildAbs :: MonadBuilder m => Binder -> (Atom -> m a) -> m (Abs Binder (Nest Decl, a))
buildAbs b f = do
  ((b', ans), decls) <- scopedDecls $ do
     v <- freshVarE UnknownBinder b
     ans <- f $ Var v
     return (b, ans)
  return (Abs b' (decls, ans))

buildLam :: MonadBuilder m => Binder -> Arrow -> (Atom -> m Atom) -> m Atom
buildLam b arr body = buildDepEffLam b (const (return arr)) body

buildDepEffLam :: MonadBuilder m
               => Binder -> (Atom -> m Arrow) -> (Atom -> m Atom) -> m Atom
buildDepEffLam b fArr fBody = liftM fst $ buildLamAux b fArr \x -> (,()) <$> fBody x

buildLamAux :: MonadBuilder m
            => Binder -> (Atom -> m Arrow) -> (Atom -> m (Atom, a)) -> m (Atom, a)
buildLamAux b fArr fBody = do
  ((b', arr, ans, aux), decls) <- scopedDecls $ do
     v <- freshVarE UnknownBinder b
     let x = Var v
     arr <- fArr x
     -- overwriting the previous binder info know that we know more
     builderExtend $ asFst $ v @> (varType v, LamBound (void arr))
     (ans, aux) <- withEffects (arrowEff arr) $ fBody x
     return (Bind v, arr, ans, aux)
  return (Lam $ makeAbs b' (arr, wrapDecls decls ans), aux)

buildNAbs :: MonadBuilder m => Nest Binder -> ([Atom] -> m Atom) -> m Alt
buildNAbs bs body = liftM fst $ buildNAbsAux bs \xs -> (,()) <$> body xs

buildNAbsAux :: MonadBuilder m => Nest Binder -> ([Atom] -> m (Atom, a)) -> m (Alt, a)
buildNAbsAux bs body = do
  ((bs', (ans, aux)), decls) <- scopedDecls $ do
     vs <- freshNestedBinders bs
     result <- body $ map Var $ toList vs
     return (fmap Bind vs, result)
  return (Abs bs' $ wrapDecls decls ans, aux)

buildDataDef :: MonadBuilder m
             => Name -> Nest Binder -> ([Atom] -> m [DataConDef]) -> m DataDef
buildDataDef tyConName paramBinders body = do
  ((paramBinders', dataDefs), _) <- scopedDecls $ do
     vs <- freshNestedBinders paramBinders
     result <- body $ map Var $ toList vs
     return (fmap Bind vs, result)
  return $ DataDef tyConName paramBinders' dataDefs

buildImplicitNaryLam :: MonadBuilder m => (Nest Binder) -> ([Atom] -> m Atom) -> m Atom
buildImplicitNaryLam Empty body = body []
buildImplicitNaryLam (Nest b bs) body =
  buildLam b ImplicitArrow \x -> do
    bs' <- substBuilder (b@>x) bs
    buildImplicitNaryLam bs' \xs -> body $ x:xs

recGetHead :: Label -> Atom -> Atom
recGetHead l x = do
  let (RecordTy (Ext r _)) = getType x
  let i = fromJust $ elemIndex l $ map fst $ toList $ reflectLabels r
  getProjection [i] x

buildScoped :: MonadBuilder m => m Atom -> m Block
buildScoped m = do
  (ans, decls) <- scopedDecls m
  return $ wrapDecls decls ans

wrapDecls :: Nest Decl -> Atom -> Block
wrapDecls decls atom = inlineLastDecl $ Block decls $ Atom atom

inlineLastDecl :: Block -> Block
inlineLastDecl block@(Block decls result) =
  case (reverse (toList decls), result) of
    (Let _ (Bind v) expr:rest, Atom atom) | atom == Var v ->
      Block (toNest (reverse rest)) expr
    _ -> block

fLitLike :: Double -> Atom -> Atom
fLitLike x t = case getType t of
  BaseTy (Scalar Float64Type) -> Con $ Lit $ Float64Lit x
  BaseTy (Scalar Float32Type) -> Con $ Lit $ Float32Lit $ realToFrac x
  _ -> error "Expected a floating point scalar"

neg :: MonadBuilder m => Atom -> m Atom
neg x = emitOp $ ScalarUnOp FNeg x

add :: MonadBuilder m => Atom -> Atom -> m Atom
add x y = emitOp $ ScalarBinOp FAdd x y

-- TODO: Implement constant folding for fixed-width integer types as well!
iadd :: MonadBuilder m => Atom -> Atom -> m Atom
iadd (Con (Lit l)) y | getIntLit l == 0 = return y
iadd x (Con (Lit l)) | getIntLit l == 0 = return x
iadd x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntBinOp (+) x y
iadd x y = emitOp $ ScalarBinOp IAdd x y

mul :: MonadBuilder m => Atom -> Atom -> m Atom
mul x y = emitOp $ ScalarBinOp FMul x y

imul :: MonadBuilder m => Atom -> Atom -> m Atom
imul   (Con (Lit l)) y               | getIntLit l == 1 = return y
imul x                 (Con (Lit l)) | getIntLit l == 1 = return x
imul x@(Con (Lit _)) y@(Con (Lit _))                    = return $ applyIntBinOp (*) x y
imul x y = emitOp $ ScalarBinOp IMul x y

sub :: MonadBuilder m => Atom -> Atom -> m Atom
sub x y = emitOp $ ScalarBinOp FSub x y

isub :: MonadBuilder m => Atom -> Atom -> m Atom
isub x (Con (Lit l)) | getIntLit l == 0 = return x
isub x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntBinOp (-) x y
isub x y = emitOp $ ScalarBinOp ISub x y

select :: MonadBuilder m => Atom -> Atom -> Atom -> m Atom
select (Con (Lit (Word8Lit p))) x y = return $ if p /= 0 then x else y
select p x y = emitOp $ Select p x y

div' :: MonadBuilder m => Atom -> Atom -> m Atom
div' x y = emitOp $ ScalarBinOp FDiv x y

idiv :: MonadBuilder m => Atom -> Atom -> m Atom
idiv x (Con (Lit l)) | getIntLit l == 1 = return x
idiv x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntBinOp div x y
idiv x y = emitOp $ ScalarBinOp IDiv x y

irem :: MonadBuilder m => Atom -> Atom -> m Atom
irem x y = emitOp $ ScalarBinOp IRem x y

fpow :: MonadBuilder m => Atom -> Atom -> m Atom
fpow x y = emitOp $ ScalarBinOp FPow x y

flog :: MonadBuilder m => Atom -> m Atom
flog x = emitOp $ ScalarUnOp Log x

ilt :: MonadBuilder m => Atom -> Atom -> m Atom
ilt x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntCmpOp (<) x y
ilt x y = emitOp $ ScalarBinOp (ICmp Less) x y

ieq :: MonadBuilder m => Atom -> Atom -> m Atom
ieq x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntCmpOp (==) x y
ieq x y = emitOp $ ScalarBinOp (ICmp Equal) x y

fromPair :: MonadBuilder m => Atom -> m (Atom, Atom)
fromPair pair = do
  ~[x, y] <- getUnpacked pair
  return (x, y)

getFst :: MonadBuilder m => Atom -> m Atom
getFst p = fst <$> fromPair p

getSnd :: MonadBuilder m => Atom -> m Atom
getSnd p = snd <$> fromPair p

getFstRef :: MonadBuilder m => Atom -> m Atom
getFstRef r = emitOp $ FstRef r

getSndRef :: MonadBuilder m => Atom -> m Atom
getSndRef r = emitOp $ SndRef r

-- XXX: getUnpacked must reduce its argument to enforce the invariant that
-- ProjectElt atoms are always fully reduced (to avoid type errors between two
-- equivalent types spelled differently).
getUnpacked :: MonadBuilder m => Atom -> m [Atom]
getUnpacked atom = do
  scope <- getScope
  let len = projectLength $ getType atom
      atom' = typeReduceAtom scope atom
      res = map (\i -> getProjection [i] atom') [0..(len-1)]
  return res

app :: MonadBuilder m => Atom -> Atom -> m Atom
app x i = emit $ App x i

naryApp :: MonadBuilder m => Atom -> [Atom] -> m Atom
naryApp f xs = foldM app f xs

appReduce :: MonadBuilder m => Atom -> Atom -> m Atom
appReduce (Lam (Abs v (_, b))) a =
  runReaderT (evalBlockE substTraversalDef b) (v @> a)
appReduce _ _ = error "appReduce expected a lambda as the first argument"

-- TODO: this would be more convenient if we could add type inference too
applyPreludeFunction :: MonadBuilder m => String -> [Atom] -> m Atom
applyPreludeFunction s xs = do
  scope <- getScope
  case envLookup scope fname of
    Nothing -> error $ "Function not defined yet: " ++ s
    Just (ty, _) -> naryApp (Var (fname:>ty)) xs
  where fname = GlobalName (fromString s)

appTryReduce :: MonadBuilder m => Atom -> Atom -> m Atom
appTryReduce f x = case f of
  Lam _ -> appReduce f x
  _     -> app f x

ptrOffset :: MonadBuilder m => Atom -> Atom -> m Atom
ptrOffset x i = emitOp $ PtrOffset x i

unsafePtrLoad :: MonadBuilder m => Atom -> m Atom
unsafePtrLoad x = emit $ Hof $ RunIO $ Lam $ Abs (Ignore UnitTy) $
  (PlainArrow (oneEffect IOEffect), Block Empty (Op (PtrLoad x)))

ptrLoad :: MonadBuilder m => Atom -> m Atom
ptrLoad x = emitOp $ PtrLoad x

unpackConsList :: MonadBuilder m => Atom -> m [Atom]
unpackConsList xs = case getType xs of
  UnitTy -> return []
  --PairTy _ UnitTy -> (:[]) <$> getFst xs
  PairTy _ _ -> do
    (x, rest) <- fromPair xs
    liftM (x:) $ unpackConsList rest
  _ -> error $ "Not a cons list: " ++ pprint (getType xs)

-- ((...((ans, x{n}), x{n-1})..., x2), x1) -> (ans, [x1, ..., x{n}])
-- This is useful for unpacking results of stacked effect handlers (as produced
-- by e.g. emitRunWriters).
unpackLeftLeaningConsList :: MonadBuilder m => Int -> Atom -> m (Atom, [Atom])
unpackLeftLeaningConsList depth atom = go depth atom []
  where
    go 0        curAtom xs = return (curAtom, reverse xs)
    go remDepth curAtom xs = do
      (consTail, x) <- fromPair curAtom
      go (remDepth - 1) consTail (x : xs)

emitWhile :: MonadBuilder m => m Atom -> m ()
emitWhile body = do
  eff <- getAllowedEffects
  lam <- buildLam (Ignore UnitTy) (PlainArrow eff) \_ -> body
  void $ emit $ Hof $ While lam

emitMaybeCase :: MonadBuilder m => Atom -> m Atom -> (Atom -> m Atom) -> m Atom
emitMaybeCase scrut nothingCase justCase = do
  let (MaybeTy a) = getType scrut
  nothingAlt <- buildNAbs Empty                        \[]  -> nothingCase
  justAlt    <- buildNAbs (Nest (Bind ("x":>a)) Empty) \[x] -> justCase x
  let (Abs _ nothingBody) = nothingAlt
  let resultTy = getType nothingBody
  emit $ Case scrut [nothingAlt, justAlt] resultTy

monoidLift :: Type -> Type -> Nest Binder
monoidLift baseTy accTy = case baseTy == accTy of
  True  -> Empty
  False -> case accTy of
    TabTy n b -> Nest n $ monoidLift baseTy b
    _         -> error $ "Base monoid type mismatch: can't lift " ++
                         pprint baseTy ++ " to " ++ pprint accTy

mextendForRef :: MonadBuilder m => Atom -> BaseMonoid -> Atom -> m Atom
mextendForRef ref (BaseMonoid _ combine) update = do
  buildLam (Bind $ "refVal":>accTy) PureArrow \refVal ->
    buildNestedFor (fmap (Fwd,) $ toList liftIndices) $ \indices -> do
      refElem <- tabGetNd refVal indices
      updateElem <- tabGetNd update indices
      bindM2 appTryReduce (appTryReduce combine refElem) (return updateElem)
  where
    TC (RefType _ accTy) = getType ref
    FunTy (BinderAnn baseTy) _ _ = getType combine
    liftIndices = monoidLift baseTy accTy

emitRunWriter :: MonadBuilder m => Name -> Type -> BaseMonoid -> (Atom -> m Atom) -> m Atom
emitRunWriter v accTy bm body = do
  emit . Hof . RunWriter bm =<< mkBinaryEffFun Writer v accTy body

emitRunWriters :: MonadBuilder m => [(Name, Type, BaseMonoid)] -> ([Atom] -> m Atom) -> m Atom
emitRunWriters inits body = go inits []
  where
    go [] refs = body $ reverse refs
    go ((v, accTy, bm):rest) refs = emitRunWriter v accTy bm $ \ref -> go rest (ref:refs)

emitRunReader :: MonadBuilder m => Name -> Atom -> (Atom -> m Atom) -> m Atom
emitRunReader v x0 body = do
  emit . Hof . RunReader x0 =<< mkBinaryEffFun Reader v (getType x0) body

emitRunState :: MonadBuilder m => Name -> Atom -> (Atom -> m Atom) -> m Atom
emitRunState v x0 body = do
  emit . Hof . RunState x0 =<< mkBinaryEffFun State v (getType x0) body

mkBinaryEffFun :: MonadBuilder m => RWS -> Name -> Type -> (Atom -> m Atom) -> m Atom
mkBinaryEffFun rws v ty body = do
  eff <- getAllowedEffects
  buildLam (Bind ("h":>TyKind)) PureArrow \r@(Var (rName:>_)) -> do
    let arr = PlainArrow $ extendEffect (RWSEffect rws rName) eff
    buildLam (Bind (v:> RefTy r ty)) arr body

buildForAnnAux :: MonadBuilder m => ForAnn -> Binder -> (Atom -> m (Atom, a)) -> m (Atom, a)
buildForAnnAux ann i body = do
  -- TODO: consider only tracking the effects that are actually needed.
  eff <- getAllowedEffects
  (lam, aux) <- buildLamAux i (const $ return $ PlainArrow eff) body
  (,aux) <$> (emit $ Hof $ For ann lam)

buildForAnn :: MonadBuilder m => ForAnn -> Binder -> (Atom -> m Atom) -> m Atom
buildForAnn ann i body = fst <$> buildForAnnAux ann i (\x -> (,()) <$> body x)

buildForAux :: MonadBuilder m => Direction -> Binder -> (Atom -> m (Atom, a)) -> m (Atom, a)
buildForAux = buildForAnnAux . RegularFor

-- Do we need this variant?
buildFor :: MonadBuilder m => Direction -> Binder -> (Atom -> m Atom) -> m Atom
buildFor = buildForAnn . RegularFor

buildNestedFor :: forall m. MonadBuilder m => [(Direction, Binder)] -> ([Atom] -> m Atom) -> m Atom
buildNestedFor specs body = go specs []
  where
    go :: [(Direction, Binder)] -> [Atom] -> m Atom
    go []        indices = body $ reverse indices
    go ((d,b):t) indices = buildFor d b $ \i -> go t (i:indices)

buildNestedLam :: MonadBuilder m => Arrow -> [Binder] -> ([Atom] -> m Atom) -> m Atom
buildNestedLam _ [] f = f []
buildNestedLam arr (b:bs) f =
  buildLam b arr \x -> buildNestedLam arr bs \xs -> f (x:xs)

tabGet :: MonadBuilder m => Atom -> Atom -> m Atom
tabGet tab idx = emit $ App tab idx

tabGetNd :: MonadBuilder m => Atom -> [Atom] -> m Atom
tabGetNd tab idxs = foldM (flip tabGet) tab idxs

unzipTab :: MonadBuilder m => Atom -> m (Atom, Atom)
unzipTab tab = do
  fsts <- buildLam (Bind ("i":>binderType v)) TabArrow \i ->
            liftM fst $ app tab i >>= fromPair
  snds <- buildLam (Bind ("i":>binderType v)) TabArrow \i ->
            liftM snd $ app tab i >>= fromPair
  return (fsts, snds)
  where TabTy v _ = getType tab

substBuilderR :: (MonadBuilder m, MonadReader SubstEnv m, Subst a)
           => a -> m a
substBuilderR x = do
  env <- ask
  substBuilder env x

substBuilder :: (MonadBuilder m, Subst a)
           => SubstEnv -> a -> m a
substBuilder env x = do
  scope <- getScope
  return $ subst (env, scope) x

checkBuilder :: (HasCallStack, MonadBuilder m, HasVars a, HasType a) => a -> m a
checkBuilder x = do
  scope <- getScope
  let globals = freeVars x `envDiff` scope
  unless (all (isGlobal . (:>())) $ envNames globals) $
    error $ "Found a non-global free variable in " ++ pprint x
  eff <- getAllowedEffects
  case checkType (scope <> globals) eff x of
    Left e   -> error $ pprint e
    Right () -> return x

isSingletonType :: Type -> Bool
isSingletonType ty = case singletonTypeVal ty of
  Nothing -> False
  Just _  -> True

-- TODO: TypeCon with a single case?
singletonTypeVal :: Type -> Maybe Atom
singletonTypeVal (TabTy v a) = TabValA v <$> singletonTypeVal a
singletonTypeVal (RecordTy (NoExt items)) = Record <$> traverse singletonTypeVal items
singletonTypeVal (TC con) = case con of
  PairType a b -> PairVal <$> singletonTypeVal a <*> singletonTypeVal b
  UnitType     -> return UnitVal
  _            -> Nothing
singletonTypeVal _ = Nothing

indexAsInt :: MonadBuilder m => Atom -> m Atom
indexAsInt idx = emitOp $ ToOrdinal idx

instance MonadTrans BuilderT where
  lift m = BuilderT $ lift $ lift m

class Monad m => MonadBuilder m where
  builderLook   :: m BuilderEnvC
  builderExtend :: BuilderEnvC -> m ()
  builderScoped :: m a -> m (a, BuilderEnvC)
  builderAsk    :: m BuilderEnvR
  builderLocal  :: (BuilderEnvR -> BuilderEnvR) -> m a -> m a

instance Monad m => MonadBuilder (BuilderT m) where
  builderLook = BuilderT look
  builderExtend env = BuilderT $ extend env
  builderScoped (BuilderT m) = BuilderT $ scoped m
  builderAsk = BuilderT ask
  builderLocal f (BuilderT m) = BuilderT $ local f m

instance MonadBuilder m => MonadBuilder (ReaderT r m) where
  builderLook = lift builderLook
  builderExtend x = lift $ builderExtend x
  builderScoped m = ReaderT \r -> builderScoped $ runReaderT m r
  builderAsk = lift builderAsk
  builderLocal v m = ReaderT \r -> builderLocal v $ runReaderT m r

instance MonadBuilder m => MonadBuilder (StateT s m) where
  builderLook = lift builderLook
  builderExtend x = lift $ builderExtend x
  builderScoped m = do
    s <- get
    ((x, s'), env) <- lift $ builderScoped $ runStateT m s
    put s'
    return (x, env)
  builderAsk = lift builderAsk
  builderLocal v m = do
    s <- get
    (x, s') <- lift $ builderLocal v $ runStateT m s
    put s'
    return x

instance (Monoid env, MonadBuilder m) => MonadBuilder (CatT env m) where
  builderLook = lift builderLook
  builderExtend x = lift $ builderExtend x
  builderScoped m = do
    env <- look
    ((ans, env'), scopeEnv) <- lift $ builderScoped $ runCatT m env
    extend env'
    return (ans, scopeEnv)
  builderAsk = lift builderAsk
  builderLocal v m = do
    env <- look
    (ans, env') <- lift $ builderLocal v $ runCatT m env
    extend env'
    return ans

instance (Monoid w, MonadBuilder m) => MonadBuilder (WriterT w m) where
  builderLook = lift builderLook
  builderExtend x = lift $ builderExtend x
  builderScoped m = do
    ((x, w), env) <- lift $ builderScoped $ runWriterT m
    tell w
    return (x, env)
  builderAsk = lift builderAsk
  builderLocal v m = WriterT $ builderLocal v $ runWriterT m

instance (Monoid env, MonadCat env m) => MonadCat env (BuilderT m) where
  look = lift look
  extend x = lift $ extend x
  scoped (BuilderT m) = BuilderT $ do
    name <- ask
    env <- look
    ((ans, env'), scopeEnv) <- lift $ lift $ scoped $ runCatT (runReaderT m name) env
    extend env'
    return (ans, scopeEnv)

instance MonadError e m => MonadError e (BuilderT m) where
  throwError = lift . throwError
  catchError m catch = do
    envC <- builderLook
    envR <- builderAsk
    (ans, envC') <- lift $ runBuilderT' m (envR, envC)
                     `catchError` (\e -> runBuilderT' (catch e) (envR, envC))
    builderExtend envC'
    return ans

instance MonadReader r m => MonadReader r (BuilderT m) where
  ask = lift ask
  local r m = do
    envC <- builderLook
    envR <- builderAsk
    (ans, envC') <- lift $ local r $ runBuilderT' m (envR, envC)
    builderExtend envC'
    return ans

instance MonadState s m => MonadState s (BuilderT m) where
  get = lift get
  put = lift . put

getNameHint :: MonadBuilder m => m Name
getNameHint = do
  tag <- fst <$> builderAsk
  return $ Name GenName tag 0

-- This is purely for human readability. `const id` would be a valid implementation.
withNameHint :: (MonadBuilder m, HasName a) => a -> m b -> m b
withNameHint name m = builderLocal (\(_, eff) -> (tag, eff)) m
  where
    tag = case getName name of
      Just (Name _ t _)        -> t
      Just (GlobalName t)      -> t
      Just (GlobalArrayName _) -> "arr"
      Nothing                  -> "tmp"

runBuilderT' :: Monad m => BuilderT m a -> BuilderEnv -> m (a, BuilderEnvC)
runBuilderT' (BuilderT m) (envR, envC) = runCatT (runReaderT m envR) envC

getScope :: MonadBuilder m => m Scope
getScope = fst <$> builderLook

extendScope :: MonadBuilder m => Scope -> m ()
extendScope scope = builderExtend $ asFst scope

getAllowedEffects :: MonadBuilder m => m EffectRow
getAllowedEffects = snd <$> builderAsk

withEffects :: MonadBuilder m => EffectRow -> m a -> m a
withEffects effs m = modifyAllowedEffects (const effs) m

modifyAllowedEffects :: MonadBuilder m => (EffectRow -> EffectRow) -> m a -> m a
modifyAllowedEffects f m = builderLocal (\(name, eff) -> (name, f eff)) m

emitDecl :: MonadBuilder m => Decl -> m ()
emitDecl decl = builderExtend (bindings, Nest decl Empty)
  where bindings = case decl of
          Let ann b expr -> b @> (binderType b, LetBound ann expr)

scopedDecls :: MonadBuilder m => m a -> m (a, Nest Decl)
scopedDecls m = do
  (ans, (_, decls)) <- builderScoped m
  return (ans, decls)

liftBuilder :: MonadBuilder m => Builder a -> m a
liftBuilder action = do
  envR <- builderAsk
  envC <- builderLook
  let (ans, envC') = runIdentity $ runBuilderT' action (envR, envC)
  builderExtend envC'
  return ans

-- === generic traversal ===

type TraversalDef m = (Decl -> m SubstEnv, Expr -> m Expr, Atom -> m Atom)

substTraversalDef :: (MonadBuilder m, MonadReader SubstEnv m) => TraversalDef m
substTraversalDef = ( traverseDecl substTraversalDef
                    , traverseExpr substTraversalDef
                    , traverseAtom substTraversalDef
                    )

appReduceTraversalDef :: (MonadBuilder m, MonadReader SubstEnv m) => TraversalDef m
appReduceTraversalDef = ( traverseDecl appReduceTraversalDef
                        , reduceAppExpr
                        , traverseAtom appReduceTraversalDef
                        )
  where
    reduceAppExpr expr = case expr of
      App f' x' -> do
        f <- traverseAtom appReduceTraversalDef f'
        x <- traverseAtom appReduceTraversalDef x'
        case f of
          TabVal b body ->
            Atom <$> (dropSub $ extendR (b@>x) $ evalBlockE appReduceTraversalDef body)
          _ -> return $ App f x
      _ -> traverseExpr appReduceTraversalDef expr

-- With `def = (traverseExpr def, traverseAtom def)` this should be a no-op
traverseDecls :: (MonadBuilder m, MonadReader SubstEnv m)
              => TraversalDef m -> Nest Decl -> m ((Nest Decl), SubstEnv)
traverseDecls def decls = liftM swap $ scopedDecls $ traverseDeclsOpen def decls

traverseDeclsOpen :: (MonadBuilder m, MonadReader SubstEnv m)
                  => TraversalDef m -> Nest Decl -> m SubstEnv
traverseDeclsOpen _ Empty = return mempty
traverseDeclsOpen def@(fDecl, _, _) (Nest decl decls) = do
  env <- fDecl decl
  env' <- extendR env $ traverseDeclsOpen def decls
  return (env <> env')

traverseDecl :: (MonadBuilder m, MonadReader SubstEnv m)
             => TraversalDef m -> Decl -> m SubstEnv
traverseDecl (_, fExpr, _) decl = case decl of
  Let letAnn b expr -> do
    expr' <- fExpr expr
    case expr' of
      Atom a | not (isGlobalBinder b) && letAnn == PlainLet -> return $ b @> a
      _ -> (b@>) <$> emitTo (binderNameHint b) letAnn expr'

traverseBlock :: (MonadBuilder m, MonadReader SubstEnv m)
              => TraversalDef m -> Block -> m Block
traverseBlock def block = buildScoped $ evalBlockE def block

evalBlockE :: (MonadBuilder m, MonadReader SubstEnv m)
              => TraversalDef m -> Block -> m Atom
evalBlockE def@(_, fExpr, _) (Block decls result) = do
  env <- traverseDeclsOpen def decls
  resultExpr <- extendR env $ fExpr result
  case resultExpr of
    Atom a -> return a
    _      -> emit resultExpr

traverseExpr :: (MonadBuilder m, MonadReader SubstEnv m)
             => TraversalDef m -> Expr -> m Expr
traverseExpr def@(_, _, fAtom) expr = case expr of
  App g x -> App  <$> fAtom g <*> fAtom x
  Atom x  -> Atom <$> fAtom x
  Op  op  -> Op   <$> traverse fAtom op
  Hof hof -> Hof  <$> traverse fAtom hof
  Case e alts ty -> Case <$> fAtom e <*> mapM traverseAlt alts <*> fAtom ty
  where
    traverseAlt (Abs bs body) = do
      bs' <- mapM (mapM fAtom) bs
      buildNAbs bs' \xs -> extendR (newEnv bs' xs) $ evalBlockE def body

traverseAtom :: forall m . (MonadBuilder m, MonadReader SubstEnv m)
             => TraversalDef m -> Atom -> m Atom
traverseAtom def@(_, _, fAtom) atom = case atom of
  Var _ -> substBuilderR atom
  Lam (Abs b (arr, body)) -> do
    b' <- mapM fAtom b
    buildDepEffLam b'
      (\x -> extendR (b'@>x) (substBuilderR arr))
      (\x -> extendR (b'@>x) (evalBlockE def body))
  Pi _ -> substBuilderR atom
  Con con -> Con <$> traverse fAtom con
  TC  tc  -> TC  <$> traverse fAtom tc
  Eff _   -> substBuilderR atom
  DataCon dataDef params con args -> DataCon dataDef <$>
    traverse fAtom params <*> pure con <*> traverse fAtom args
  TypeCon dataDef params -> TypeCon dataDef <$> traverse fAtom params
  LabeledRow (Ext items rest) -> do
    items' <- traverse fAtom items
    return $ LabeledRow $ Ext items' rest
  Record items -> Record <$> traverse fAtom items
  RecordTy (Ext items rest) -> do
    items' <- traverse fAtom items
    return $ RecordTy $ Ext items' rest
  Variant (Ext types rest) label i value -> do
    types' <- traverse fAtom types
    Variant (Ext types' rest) label i <$> fAtom value
  VariantTy (Ext items rest) -> do
    items' <- traverse fAtom items
    return $ VariantTy $ Ext items' rest
  ACase e alts ty -> ACase <$> fAtom e <*> mapM traverseAAlt alts <*> fAtom ty
  DataConRef dataDef params args -> DataConRef dataDef <$>
    traverse fAtom params <*> traverseNestedArgs args
  BoxedRef b ptr size body -> do
    ptr'  <- fAtom ptr
    size' <- buildScoped $ evalBlockE def size
    Abs b' (decls, body') <- buildAbs b \x ->
      extendR (b@>x) $ evalBlockE def (Block Empty $ Atom body)
    case decls of
      Empty -> return $ BoxedRef b' ptr' size' body'
      _ -> error "Traversing the body atom shouldn't produce decls"
  ProjectElt _ _ -> substBuilderR atom
  where
    traverseNestedArgs :: Nest DataConRefBinding -> m (Nest DataConRefBinding)
    traverseNestedArgs Empty = return Empty
    traverseNestedArgs (Nest (DataConRefBinding b ref) rest) = do
      ref' <- fAtom ref
      b' <- substBuilderR b
      v <- freshVarE UnknownBinder b'
      rest' <- extendR (b @> Var v) $ traverseNestedArgs rest
      return $ Nest (DataConRefBinding (Bind v) ref') rest'

    traverseAAlt (Abs bs a) = do
      bs' <- mapM (mapM fAtom) bs
      (Abs bs'' b) <- buildNAbs bs' \xs -> extendR (newEnv bs' xs) $ fAtom a
      case b of
        Block Empty (Atom r) -> return $ Abs bs'' r
        _                    -> error "ACase alternative traversal has emitted decls or exprs!"

transformModuleAsBlock :: (Block -> Block) -> Module -> Module
transformModuleAsBlock transform (Module ir decls bindings) = do
  let localVars = filter (not . isGlobal) $ bindingsAsVars $ freeVars bindings
  let block = Block decls $ Atom $ mkConsList $ map Var localVars
  let (Block newDecls (Atom newResult)) = transform block
  let newLocalVals = ignoreExcept $ fromConsList newResult
  Module ir newDecls $ scopelessSubst (newEnv localVars newLocalVals) bindings

dropSub :: MonadReader SubstEnv m => m a -> m a
dropSub m = local mempty m

indexSetSizeE :: MonadBuilder m => Type -> m Atom
indexSetSizeE (TC con) = case con of
  UnitType                   -> return $ IdxRepVal 1
  IntRange low high -> clampPositive =<< high `isub` low
  IndexRange n low high -> do
    low' <- case low of
      InclusiveLim x -> indexToIntE x
      ExclusiveLim x -> indexToIntE x >>= iadd (IdxRepVal 1)
      Unlimited      -> return $ IdxRepVal 0
    high' <- case high of
      InclusiveLim x -> indexToIntE x >>= iadd (IdxRepVal 1)
      ExclusiveLim x -> indexToIntE x
      Unlimited      -> indexSetSizeE n
    clampPositive =<< high' `isub` low'
  PairType a b -> bindM2 imul (indexSetSizeE a) (indexSetSizeE b)
  ParIndexRange _ _ _ -> error "Shouldn't be querying the size of a ParIndexRange"
  _ -> error $ "Not implemented " ++ pprint con
indexSetSizeE (RecordTy (NoExt types)) = do
  sizes <- traverse indexSetSizeE types
  foldM imul (IdxRepVal 1) sizes
indexSetSizeE (VariantTy (NoExt types)) = do
  sizes <- traverse indexSetSizeE types
  foldM iadd (IdxRepVal 0) sizes
indexSetSizeE ty = error $ "Not implemented " ++ pprint ty

clampPositive :: MonadBuilder m => Atom -> m Atom
clampPositive x = do
  isNegative <- x `ilt` (IdxRepVal 0)
  select isNegative (IdxRepVal 0) x

-- XXX: Be careful if you use this function as an interpretation for
--      IndexAsInt instruction, as for Int and IndexRanges it will
--      generate the same instruction again, potentially leading to an
--      infinite loop.
indexToIntE :: MonadBuilder m => Atom -> m Atom
indexToIntE (Con (IntRangeVal _ _ i))     = return i
indexToIntE (Con (IndexRangeVal _ _ _ i)) = return i
indexToIntE idx = case getType idx of
  UnitTy  -> return $ IdxRepVal 0
  PairTy _ rType -> do
    (lVal, rVal) <- fromPair idx
    lIdx  <- indexToIntE lVal
    rIdx  <- indexToIntE rVal
    rSize <- indexSetSizeE rType
    imul rSize lIdx >>= iadd rIdx
  TC (IntRange _ _)     -> indexAsInt idx
  TC (IndexRange _ _ _) -> indexAsInt idx
  TC (ParIndexRange _ _ _) -> error "Int casts unsupported on ParIndexRange"
  RecordTy (NoExt types) -> do
    sizes <- traverse indexSetSizeE types
    (strides, _) <- scanM (\sz prev -> (prev,) <$> imul sz prev) sizes (IdxRepVal 1)
    -- Unpack and sum the strided contributions
    subindices <- getUnpacked idx
    subints <- traverse indexToIntE subindices
    scaled <- mapM (uncurry imul) $ zip (toList strides) subints
    foldM iadd (IdxRepVal 0) scaled
  VariantTy (NoExt types) -> do
    sizes <- traverse indexSetSizeE types
    (offsets, _) <- scanM (\sz prev -> (prev,) <$> iadd sz prev) sizes (IdxRepVal 0)
    -- Build and apply a case expression
    alts <- flip mapM (zip (toList offsets) (toList types)) $
      \(offset, subty) -> buildNAbs (toNest [Ignore subty]) \[subix] -> do
        i <- indexToIntE subix
        iadd offset i
    emit $ Case idx alts IdxRepTy
  ty -> error $ "Unexpected type " ++ pprint ty

intToIndexE :: MonadBuilder m => Type -> Atom -> m Atom
intToIndexE (TC con) i = case con of
  IntRange        low high   -> return $ Con $ IntRangeVal        low high i
  IndexRange from low high   -> return $ Con $ IndexRangeVal from low high i
  UnitType                   -> return $ UnitVal
  PairType a b -> do
    bSize <- indexSetSizeE b
    iA <- intToIndexE a =<< idiv i bSize
    iB <- intToIndexE b =<< irem i bSize
    return $ PairVal iA iB
  ParIndexRange _ _ _ -> error "Int casts unsupported on ParIndexRange"
  _ -> error $ "Unexpected type " ++ pprint con
intToIndexE (RecordTy (NoExt types)) i = do
  sizes <- traverse indexSetSizeE types
  (strides, _) <- scanM
    (\sz prev -> do {v <- imul sz prev; return ((prev, v), v)}) sizes (IdxRepVal 1)
  offsets <- flip mapM (zip (toList types) (toList strides)) $
    \(ty, (s1, s2)) -> do
      x <- irem i s2
      y <- idiv x s1
      intToIndexE ty y
  return $ Record (restructure offsets types)
intToIndexE (VariantTy (NoExt types)) i = do
  sizes <- traverse indexSetSizeE types
  (offsets, _) <- scanM (\sz prev -> (prev,) <$> iadd sz prev) sizes (IdxRepVal 0)
  let
    reflect = reflectLabels types
    -- Find the right index by looping through the possible offsets
    go prev ((label, repeatNum), ty, offset) = do
      shifted <- isub i offset
      -- TODO: This might run intToIndex on negative indices. Fix this!
      index   <- intToIndexE ty shifted
      beforeThis <- ilt i offset
      select beforeThis prev $ Variant (NoExt types) label repeatNum index
    ((l0, 0), ty0, _):zs = zip3 (toList reflect) (toList types) (toList offsets)
  start <- Variant (NoExt types) l0 0 <$> intToIndexE ty0 i
  foldM go start zs
intToIndexE ty _ = error $ "Unexpected type " ++ pprint ty
