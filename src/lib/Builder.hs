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

module Builder (emit, emitAnn, emitOp, emitBinding, buildDepEffLam, buildLamAux, buildPi,
                getAllowedEffects, withEffects, modifyAllowedEffects,
                buildLam, BuilderT, Builder, MonadBuilder (..), buildScoped, runBuilderT,
                runSubstBuilder, runBuilder, runBuilderT', getScope, getSynthCandidates,
                liftBuilder,
                app,
                add, mul, sub, neg, div',
                iadd, imul, isub, idiv, ilt, ieq,
                fpow, flog, fLitLike, recGetHead, buildNaryLam,
                select, substBuilder, substBuilderR, emitUnpack, getUnpacked,
                fromPair, getFst, getSnd, getProj, getProjRef,
                naryApp, appReduce, appTryReduce, buildAbs, buildAAbs, buildAAbsAux,
                buildFor, buildForAux, buildForAnn, buildForAnnAux,
                emitBlock, unzipTab, isSingletonType, withNameHint,
                singletonTypeVal, scopedDecls, extendScope, checkBuilder,
                unpackLeftLeaningConsList, unpackRightLeaningConsList,
                unpackBundle, unpackBundleTab,
                emitRunWriter, emitRunWriters, mextendForRef, monoidLift,
                emitRunState, emitMaybeCase, emitWhile, emitDecl,
                buildDataDef, emitDataDef, emitClassDef, emitDataConName, emitTyConName,
                emitSuperclass, emitMethodType, getDataDef, getClassDef,
                emitRunReader, tabGet, SubstBuilderT, SubstBuilder, runSubstBuilderT,
                ptrOffset, ptrLoad, unsafePtrLoad,
                evalBlockE, substTraversalDef,
                TraversalDef, traverseDecls, traverseDecl, traverseDeclsOpen,
                traverseBlock, traverseExpr, traverseAtom,
                clampPositive, buildNAbs, buildNAbsAux, buildNestedLam,
                transformModuleAsBlock, dropSub, appReduceTraversalDef,
                indexSetSizeE, indexToIntE, intToIndexE, freshVarE,
                catMaybesE, runMaybeWhile, makeClassDataDef) where

import Control.Applicative
import Control.Monad
import Control.Monad.Except hiding (Except)
import Control.Monad.Reader
import Control.Monad.Writer hiding (Alt)
import Control.Monad.Identity
import Control.Monad.State.Strict
import Data.Functor ((<&>))
import Data.Foldable (toList)
import Data.List (elemIndex)
import Data.Maybe (fromJust)
import Data.Tuple (swap)
import GHC.Stack

import Env
import Syntax
import LabeledItems
import Cat
import Type
import Err
import PPrint ()
import Util (bindM2, scanM, restructure)

newtype BuilderT m a = BuilderT (ReaderT BuilderEnvR (CatT BuilderEnvC m) a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail, Fallible, Alternative)

type Builder = BuilderT Identity
type BuilderEnv = (BuilderEnvR, BuilderEnvC)

type SubstBuilderT m = ReaderT SubstEnv (BuilderT m)
type SubstBuilder    = SubstBuilderT Identity

-- Carries the vars in scope (with optional definitions) and the emitted decls
-- TODO: The only reason to have the inference candidates here is that we want
-- to use traversal template in dictinoary synthesis. We should come up with a
-- different design that's more modular.
type BuilderEnvC = ((Scope, SynthCandidates), Nest Decl)
-- Carries a name suggestion and the allowable effects
type BuilderEnvR = (Tag, EffectRow)

runBuilderT :: Monad m => Scope -> SynthCandidates -> BuilderT m a -> m (a, BuilderEnvC)
runBuilderT scope scs (BuilderT m) = do
  (ans, env) <- runCatT (runReaderT m ("tmp", Pure)) ((scope, scs), Empty)
  return (ans, env)

runBuilder :: Scope -> SynthCandidates -> Builder a -> (a, BuilderEnvC)
runBuilder scope scs m = runIdentity $ runBuilderT scope scs m

runSubstBuilderT :: Monad m => Scope -> SynthCandidates -> SubstBuilderT m a -> m (a, BuilderEnvC)
runSubstBuilderT scope scs m = runBuilderT scope scs $ runReaderT m mempty

runSubstBuilder :: Scope -> SynthCandidates -> SubstBuilder a -> (a, BuilderEnvC)
runSubstBuilder scope scs m = runIdentity $ runBuilderT scope scs $ runReaderT m mempty

emit :: MonadBuilder m => Expr -> m Atom
emit expr = emitAnn PlainLet expr

emitAnn :: MonadBuilder m => LetAnn -> Expr -> m Atom
emitAnn ann expr = do
  let ty = getType expr
  v <- freshVarE (LetBound ann expr) ty
  builderExtend $ asSnd $ Nest (Let ann (Bind v) expr) Empty
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
  x <- withNameHint b $ emitAnn ann expr'
  emitBlockRec (env <> b@>SubstVal x) $ Block decls result
emitBlockRec env (Block Empty (Atom atom)) = substBuilder env atom
emitBlockRec env (Block Empty expr) = substBuilder env expr >>= emit

freshVarE :: MonadBuilder m => BinderInfo -> Type -> m Var
freshVarE bInfo ty = do
  hint <- getNameHint
  scope <- getScope
  let v = genFresh hint scope
  extendScope $ v @> AtomBinderInfo ty bInfo
  return $ v :> ty

freshNestedBinders :: MonadBuilder m => Nest Binder -> m (Nest Var)
freshNestedBinders bs = freshNestedBindersRec mempty bs

freshNestedBindersRec :: MonadBuilder m => SubstEnv -> Nest Binder -> m (Nest Var)
freshNestedBindersRec _ Empty = return Empty
freshNestedBindersRec substEnv (Nest b bs) = do
  scope <- getScope
  v  <- withNameHint b $ freshVarE PatBound $ subst (substEnv, scope) (binderType b)
  vs <- freshNestedBindersRec (substEnv <> b @> SubstVal (Var v)) bs
  return $ Nest v vs

buildPi :: (Fallible m, MonadBuilder m)
        => Binder -> (Atom -> m (Arrow, Type)) -> m Atom
buildPi b f = do
  scope <- getScope
  (ans, decls) <- scopedDecls $ do
     v <- withNameHint b $ freshVarE PiBound $ binderType b
     (arr, ans) <- f $ Var v
     return $ Pi $ makeAbs (Bind v) (arr, ans)
  let block = wrapDecls decls ans
  case typeReduceBlock scope block of
    Right piTy -> return piTy
    Left _ -> throw CompilerErr $
      "Unexpected irreducible decls in pi type: " ++ pprint decls

buildAbsAux :: (MonadBuilder m, HasVars a) => Binder -> (Atom -> m (a, b)) -> m (Abs Binder (Nest Decl, a), b)
buildAbsAux b f = do
  ((b', ans, aux), decls) <- scopedDecls $ do
     v <- freshVarE UnknownBinder $ binderType b
     (ans, aux) <- f $ Var v
     return (Bind v, ans, aux)
  return (makeAbs b' (decls, ans), aux)

buildAbs :: (MonadBuilder m, HasVars a) => Binder -> (Atom -> m a) -> m (Abs Binder (Nest Decl, a))
buildAbs b f = fst <$> buildAbsAux b (\x -> (,()) <$> f x)

buildAAbsAux :: (MonadBuilder m, HasVars a) => Binder -> (Atom -> m (a, b)) -> m (Abs Binder a, b)
buildAAbsAux b' f = do
  (Abs b (decls, a), aux) <- buildAbsAux b' f
  case decls of
    Empty -> return $ (Abs b a, aux)
    _     -> error $ "buildAAbsAux with non-empty body: " ++ pprint decls

buildAAbs :: (MonadBuilder m, HasVars a) => Binder -> (Atom -> m a) -> m (Abs Binder a)
buildAAbs b' f = fst <$> buildAAbsAux b' (\x -> (,()) <$> f x)

buildLam :: MonadBuilder m => Binder -> Arrow -> (Atom -> m Atom) -> m Atom
buildLam b arr body = buildDepEffLam b (const (return arr)) body

buildDepEffLam :: MonadBuilder m
               => Binder -> (Atom -> m Arrow) -> (Atom -> m Atom) -> m Atom
buildDepEffLam b fArr fBody = liftM fst $ buildLamAux b fArr \x -> (,()) <$> fBody x

buildLamAux :: MonadBuilder m
            => Binder -> (Atom -> m Arrow) -> (Atom -> m (Atom, a)) -> m (Atom, a)
buildLamAux b fArr fBody = do
  ((b', arr, ans, aux), decls) <- scopedDecls $ do
     v <- withNameHint b $ freshVarE UnknownBinder $ binderType b
     let x = Var v
     arr <- fArr x
     -- overwriting the previous binder info know that we know more
     extendScope $ v @> AtomBinderInfo (varType v) (LamBound (void arr))
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
             => SourceName -> Nest Binder -> ([Atom] -> m [DataConDef]) -> m DataDef
buildDataDef tyConName paramBinders body = do
  ((paramBinders', dataDefs), _) <- scopedDecls $ do
     vs <- freshNestedBinders paramBinders
     result <- body $ map Var $ toList vs
     return (fmap Bind vs, result)
  return $ DataDef tyConName paramBinders' dataDefs

emitBinding :: MonadBuilder m => AnyBinderInfo -> m Name
emitBinding binfo = do
  scope <- getScope
  hint <- getNameHint
  let name = genFresh hint scope
  extendScope $ name @> binfo
  return name

emitDataDef :: MonadBuilder m => DataDef -> m DataDefName
emitDataDef dataDef =
  -- XXX: the hint shouldn't be necssary but ...
  withNameHint (Name GenName "_data_def_" 0) $
    emitBinding $ DataDefName dataDef

emitClassDef :: MonadBuilder m => ClassDef -> m ClassDefName
emitClassDef classDef = emitBinding $ ClassDefName classDef

emitDataConName :: MonadBuilder m => DataDefName -> Int -> m Name
emitDataConName dataDefName conIdx = do
  DataDef _ _ dataCons <- getDataDef dataDefName
  let (DataConDef name _) = dataCons !! conIdx
  withNameHint name $ emitBinding $ DataConName dataDefName conIdx

emitTyConName :: MonadBuilder m => DataDefName -> m Name
emitTyConName dataDefName =
  withNameHint dataDefName $ emitBinding $ TyConName dataDefName

getDataDef :: MonadBuilder m => DataDefName -> m DataDef
getDataDef dataDefName = do
  scope <- getScope
  case scope ! dataDefName of
    DataDefName dataDef -> return dataDef
    _ -> error "Not a data def"

getClassDef :: MonadBuilder m => ClassDefName -> m ClassDef
getClassDef classDefName = do
  scope <- getScope
  case scope ! classDefName of
    ClassDefName classDef -> return classDef
    _ -> error "Not a data def"

emitSuperclass :: MonadBuilder m => ClassDefName -> Int -> m Name
emitSuperclass dataDef idx = do
  getter <- makeSuperclassGetter dataDef idx
  emitBinding $ SuperclassName dataDef idx getter

emitMethodType :: MonadBuilder m => [Bool] -> ClassDefName -> Int -> m Name
emitMethodType explicit classDef idx = do
  getter <- makeMethodGetter explicit classDef idx
  emitBinding $ MethodName classDef idx getter

makeMethodGetter :: MonadBuilder m => [Bool] -> ClassDefName -> Int -> m Atom
makeMethodGetter explicit classDefName methodIdx = do
  ClassDef def@(_, DataDef _ paramBs _) _ <- getClassDef classDefName
  let arrows = explicit <&> \case True -> PureArrow; False -> ImplicitArrow
  let bs = toNest $ zip (toList paramBs) arrows
  buildNestedLam bs \params -> do
    buildLam (Bind ("d":> TypeCon def params)) ClassArrow \dict -> do
      return $ getProjection [methodIdx] $ getProjection [1, 0] dict

makeSuperclassGetter :: MonadBuilder m => DataDefName -> Int -> m Atom
makeSuperclassGetter classDefName methodIdx = do
  ClassDef def@(_, DataDef _ paramBs _) _ <- getClassDef classDefName
  buildNaryLam ImplicitArrow paramBs \params -> do
    buildLam (Bind ("d":> TypeCon def params)) PureArrow \dict -> do
      return $ getProjection [methodIdx] $ getProjection [0, 0] dict

buildNaryLam :: MonadBuilder m => Arrow -> (Nest Binder) -> ([Atom] -> m Atom) -> m Atom
buildNaryLam _   Empty       body = body []
buildNaryLam arr (Nest b bs) body =
  buildLam b arr \x -> do
    bs' <- substBuilder (b@>SubstVal x) bs
    buildNaryLam arr bs' \xs -> body $ x:xs

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

getProj :: MonadBuilder m => Int -> Atom -> m Atom
getProj i x = do
  xs <- getUnpacked x
  return $ xs !! i

getFst :: MonadBuilder m => Atom -> m Atom
getFst p = fst <$> fromPair p

getSnd :: MonadBuilder m => Atom -> m Atom
getSnd p = snd <$> fromPair p

getProjRef :: MonadBuilder m => Int -> Atom -> m Atom
getProjRef i r = emitOp $ ProjRef i r

-- XXX: getUnpacked must reduce its argument to enforce the invariant that
-- ProjectElt atoms are always fully reduced (to avoid type errors between two
-- equivalent types spelled differently).
getUnpacked :: MonadBuilder m => Atom -> m [Atom]
getUnpacked (ProdVal xs) = return xs
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
  runReaderT (evalBlockE substTraversalDef b) (v @> SubstVal a)
appReduce _ _ = error "appReduce expected a lambda as the first argument"

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

unpackRightLeaningConsList :: HasCallStack => MonadBuilder m => Atom -> m [Atom]
unpackRightLeaningConsList xs = case getType xs of
  UnitTy -> return []
  -- PairTy _ UnitTy -> (:[]) <$> getFst xs
  PairTy _ _ -> do
    (x, rest) <- fromPair xs
    liftM (x:) $ unpackRightLeaningConsList rest
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

unpackBundle :: MonadBuilder m => Atom -> BundleDesc -> m [Atom]
unpackBundle b size = case size of
  0 -> return []
  1 -> return [b]
  _ -> do
    (h, t) <- fromPair b
    (h:) <$> unpackBundle t (size - 1)

unpackBundleTab :: MonadBuilder m => Atom -> BundleDesc -> m [Atom]
unpackBundleTab tab size = case size of
  0 -> return []
  1 -> return [tab]
  _ -> do
    (h, t) <- unzipTab tab
    (h:) <$> unpackBundleTab t (size - 1)

emitWhile :: MonadBuilder m => m Atom -> m ()
emitWhile body = do
  eff <- getAllowedEffects
  lam <- buildLam (Ignore UnitTy) (PlainArrow eff) \_ -> body
  void $ emit $ Hof $ While lam

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

buildNestedLam :: MonadBuilder m => Nest (Binder, Arrow) -> ([Atom] -> m Atom) -> m Atom
buildNestedLam Empty f = f []
buildNestedLam (Nest (b, arr) t) f =
  buildLam b arr \x -> buildNestedLam t \xs -> f (x:xs)

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
  eff <- getAllowedEffects
  case checkType (scope <> globals) eff x of
    Failure e  -> error $ pprint e
    Success () -> return x

isSingletonType :: Type -> Bool
isSingletonType ty = case singletonTypeVal ty of
  Nothing -> False
  Just _  -> True

-- TODO: TypeCon with a single case?
singletonTypeVal :: Type -> Maybe Atom
singletonTypeVal (TabTy v a) = TabValA v <$> singletonTypeVal a
singletonTypeVal (RecordTy (NoExt items)) = Record <$> traverse singletonTypeVal items
singletonTypeVal (TC con) = case con of
  ProdType tys -> ProdVal <$> traverse singletonTypeVal tys
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

instance MonadReader r m => MonadReader r (BuilderT m) where
  ask = lift ask
  local r m = do
    envC <- builderLook
    envR <- builderAsk
    (ans, envC') <- lift $ local r $ runBuilderT' m (envR, envC)
    builderExtend envC'
    return ans

instance MonadWriter w m => MonadWriter w (BuilderT m) where
  tell = lift . tell
  listen m = do
    envC <- builderLook
    envR <- builderAsk
    ((ans, envC'), w) <- lift $ listen $ runBuilderT' m (envR, envC)
    builderExtend envC'
    return (ans, w)
  pass m = do
    envC <- builderLook
    envR <- builderAsk
    (ans, envC') <- lift $ pass $ (\((a, wf), e) -> ((a, e), wf)) <$> runBuilderT' m (envR, envC)
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
withNameHint :: HasCallStack => (MonadBuilder m, NameHint hint) => hint -> m a -> m a
withNameHint hint m =
  flip builderLocal m \(prevHint, eff) -> case asNameHint hint of
    Nothing      -> (prevHint, eff)
    Just newHint -> (newHint , eff)

runBuilderT' :: Monad m => BuilderT m a -> BuilderEnv -> m (a, BuilderEnvC)
runBuilderT' (BuilderT m) (envR, envC) = runCatT (runReaderT m envR) envC

getSynthCandidates :: MonadBuilder m => m SynthCandidates
getSynthCandidates = snd . fst <$> builderLook

getScope :: MonadBuilder m => m Scope
getScope = fst . fst <$> builderLook

extendScope :: MonadBuilder m => Scope -> m ()
extendScope scope = builderExtend $ asFst (scope, scs)
  where scs = foldMap (uncurry binderInfoAsSynthCandidates) $ envPairs scope

binderInfoAsSynthCandidates :: Name -> AnyBinderInfo -> SynthCandidates
binderInfoAsSynthCandidates name binfo = case binfo of
  AtomBinderInfo ty (LamBound ClassArrow)    -> mempty { lambdaDicts       = [Var (name:>ty)]}
  SuperclassName _ _ superclassGetter        -> mempty { superclassGetters = [superclassGetter]}
  AtomBinderInfo ty (LetBound InstanceLet _) -> mempty { instanceDicts     = [Var (name:>ty)]}
  _ -> mempty

getAllowedEffects :: MonadBuilder m => m EffectRow
getAllowedEffects = snd <$> builderAsk

withEffects :: MonadBuilder m => EffectRow -> m a -> m a
withEffects effs m = modifyAllowedEffects (const effs) m

modifyAllowedEffects :: MonadBuilder m => (EffectRow -> EffectRow) -> m a -> m a
modifyAllowedEffects f m = builderLocal (\(name, eff) -> (name, f eff)) m

-- XXX: this doesn't generate fresh names so be careful!
emitDecl :: MonadBuilder m => Decl -> m ()
emitDecl decl = do
  extendScope bindings
  builderExtend $ asSnd $ Nest decl Empty
  where bindings = case decl of
          Let ann b expr -> b @> (AtomBinderInfo (binderType b) (LetBound ann expr))

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
            Atom <$> (dropSub $ extendR (b@>SubstVal x) $ evalBlockE appReduceTraversalDef body)
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
    ((b@>) . SubstVal) <$> withNameHint b (emitAnn letAnn expr')

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
      buildNAbs bs' \xs -> extendR (newEnv bs' $ map SubstVal xs) $ evalBlockE def body

traverseAtom :: forall m . (HasCallStack, MonadBuilder m, MonadReader SubstEnv m)
             => TraversalDef m -> Atom -> m Atom
traverseAtom def@(_, _, fAtom) atom = case atom of
  Var _ -> substBuilderR atom
  Lam (Abs b (arr, body)) -> do
    b' <- mapM fAtom b
    buildDepEffLam b'
      (\x -> extendR (b'@>SubstVal x) (substBuilderR arr))
      (\x -> extendR (b'@>SubstVal x) (evalBlockE def body))
  Pi (Abs b (arr, ty)) -> do
    b' <- mapM fAtom b
    Pi <$> buildAAbs b' \x ->
      extendR (b'@>SubstVal x) $ (,) <$> (substBuilderR arr) <*> (fAtom ty)
  DepPairTy (Abs b ty) -> do
    b' <- mapM fAtom b
    DepPairTy <$> buildAAbs b' \x -> extendR (b'@>SubstVal x) $ fAtom ty
  DepPair x y (Abs b ty) -> do
    x' <- fAtom x
    y' <- fAtom y
    b' <- mapM fAtom b
    DepPair x' y' <$> buildAAbs b' \xb -> extendR (b'@>SubstVal xb) $ fAtom ty
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
  DepPairRef _ _ _ -> undefined  -- Should be unnecessary, those refs are only used in Imp lowering
  BoxedRef b ptr size body -> do
    ptr'  <- fAtom ptr
    size' <- buildScoped $ evalBlockE def size
    Abs b' (decls, body') <- buildAbs b \x ->
      extendR (b@>SubstVal x) $ evalBlockE def (Block Empty $ Atom body)
    case decls of
      Empty -> return $ BoxedRef b' ptr' size' body'
      _ -> error "Traversing the body atom shouldn't produce decls"
  ProjectElt _ _ -> substBuilderR atom
  where
    traverseNestedArgs :: Nest DataConRefBinding -> m (Nest DataConRefBinding)
    traverseNestedArgs Empty = return Empty
    traverseNestedArgs (Nest (DataConRefBinding b ref) rest) = do
      ref' <- fAtom ref
      ty <- substBuilderR $ binderType b
      v <- withNameHint b $ freshVarE UnknownBinder ty
      rest' <- extendR (b @> SubstVal (Var v)) $ traverseNestedArgs rest
      return $ Nest (DataConRefBinding (Bind v) ref') rest'

    traverseAAlt (Abs bs a) = do
      bs' <- mapM (mapM fAtom) bs
      (Abs bs'' b) <- buildNAbs bs' \xs -> extendR (newEnv bs' (map SubstVal xs)) $ fAtom a
      case b of
        Block Empty (Atom r) -> return $ Abs bs'' r
        _                    -> error "ACase alternative traversal has emitted decls or exprs!"

transformModuleAsBlock :: (Block -> Block) -> Module -> Module
transformModuleAsBlock transform (Module ir decls bindings) = do
  let localVars = bindingsAsVars $ freeVars bindings
  let block = Block decls $ Atom $ ProdVal $ map Var localVars
  let (Block newDecls (Atom (ProdVal newLocalVals))) = transform block
  Module ir newDecls $ scopelessSubst (newEnv localVars $ map SubstVal newLocalVals) bindings

dropSub :: MonadReader SubstEnv m => m a -> m a
dropSub m = local mempty m

indexSetSizeE :: MonadBuilder m => Type -> m Atom
indexSetSizeE (TC con) = case con of
  IntRange low high -> clampPositive =<< high `isub` low
  SumType types -> foldM iadd (IdxRepVal 0) =<< traverse indexSetSizeE types
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
  ProdType tys -> foldM imul (IdxRepVal 1) =<< traverse indexSetSizeE tys
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

data IterOrder = MinorToMajor | MajorToMinor

-- XXX: Be careful if you use this function as an interpretation for
--      IndexAsInt instruction, as for Int and IndexRanges it will
--      generate the same instruction again, potentially leading to an
--      infinite loop.
indexToIntE :: MonadBuilder m => Atom -> m Atom
indexToIntE (Con (IntRangeVal _ _ i))     = return i
indexToIntE (Con (IndexRangeVal _ _ _ i)) = return i
indexToIntE idx = case getType idx of
  TC (IntRange _ _)     -> indexAsInt idx
  TC (IndexRange _ _ _) -> indexAsInt idx
  TC (ParIndexRange _ _ _) -> error "Int casts unsupported on ParIndexRange"
  ProdTy           types  -> prodToInt MajorToMinor types
  RecordTy  (NoExt types) -> prodToInt MinorToMajor types
  SumTy            types  -> sumToInt  types
  VariantTy (NoExt types) -> sumToInt  types
  ty -> error $ "Unexpected type " ++ pprint ty
  where
    -- XXX: Assumes minor-to-major iteration order
    prodToInt :: (MonadBuilder m, Traversable t) => IterOrder -> t Type -> m Atom
    prodToInt order types = do
      sizes <- toList <$> traverse indexSetSizeE types
      let rev = case order of MinorToMajor -> id; MajorToMinor -> reverse
      strides <- rev . fst <$> scanM (\sz prev -> (prev,) <$> imul sz prev) (rev sizes) (IdxRepVal 1)
      -- Unpack and sum the strided contributions
      subindices <- getUnpacked idx
      subints <- traverse indexToIntE subindices
      scaled <- mapM (uncurry imul) $ zip strides subints
      foldM iadd (IdxRepVal 0) scaled
    sumToInt :: (MonadBuilder m, Traversable t) => t Type -> m Atom
    sumToInt types = do
      sizes <- traverse indexSetSizeE types
      (offsets, _) <- scanM (\sz prev -> (prev,) <$> iadd sz prev) sizes (IdxRepVal 0)
      alts <- flip mapM (zip (toList offsets) (toList types)) $
        \(offset, subty) -> buildNAbs (toNest [Ignore subty]) \[subix] -> do
          i <- indexToIntE subix
          iadd offset i
      emit $ Case idx alts IdxRepTy

intToIndexE :: MonadBuilder m => Type -> Atom -> m Atom
intToIndexE ty i = case ty of
  TC con -> case con of
    IntRange        low high   -> return $ Con $ IntRangeVal        low high i
    IndexRange from low high   -> return $ Con $ IndexRangeVal from low high i
    -- Strategically placed reverses make intToProd major-to-minor
    ProdType types             -> intToProd (reverse types) (ProdVal . reverse)
    SumType  types             -> intToSum  types [0..] $ SumVal ty
    ParIndexRange _ _ _ -> error "Int casts unsupported on ParIndexRange"
    _ -> error $ "Unexpected type " ++ pprint ty
  RecordTy  (NoExt types) -> intToProd types Record
  VariantTy (NoExt types) -> intToSum  types (reflectLabels types) $ uncurry $ Variant (NoExt types)
  _ -> error $ "Unexpected type " ++ pprint ty
  where
    -- XXX: Expects that the types are in a minor-to-major order
    intToProd :: (MonadBuilder m, Traversable t) => t Type -> (t Atom -> Atom) -> m Atom
    intToProd types mkProd = do
      sizes <- traverse indexSetSizeE types
      (strides, _) <- scanM
        (\sz prev -> do {v <- imul sz prev; return ((prev, v), v)}) sizes (IdxRepVal 1)
      offsets <- flip mapM (zip (toList types) (toList strides)) $
        \(ety, (s1, s2)) -> do
          x <- irem i s2
          y <- idiv x s1
          intToIndexE ety y
      return $ mkProd (restructure offsets types)
    intToSum :: (MonadBuilder m, Traversable t) => t Type -> t l -> (l -> Atom -> Atom) -> m Atom
    intToSum types labels mkSum = do
      sizes <- traverse indexSetSizeE types
      (offsets, _) <- scanM (\sz prev -> (prev,) <$> iadd sz prev) sizes (IdxRepVal 0)
      let
        -- Find the right index by looping through the possible offsets
        go prev (label, cty, offset) = do
          shifted <- isub i offset
          -- TODO: This might run intToIndex on negative indices. Fix this!
          index   <- intToIndexE cty shifted
          beforeThis <- ilt i offset
          select beforeThis prev $ mkSum label index
        (l, ty0, _):zs = zip3 (toList labels) (toList types) (toList offsets)
      start <- mkSum l <$> intToIndexE ty0 i
      foldM go start zs

-- === pseudo-prelude ===

-- Monoid a -> (n=>a) -> a
reduceE :: MonadBuilder m => BaseMonoid -> Atom -> m Atom
reduceE monoid xs = do
  let TabTy n a = getType xs
  getSnd =<< emitRunWriter "ref" a monoid \ref ->
    buildFor Fwd n \i -> do
      x <- emit $ App xs i
      updater <- emit $ App (baseCombine monoid) x
      emitOp $ PrimEffect ref $ MExtend updater

-- (a-> {|eff} b) -> n=>a -> {|eff} (n=>b)
mapE :: MonadBuilder m => (Atom -> m Atom) -> Atom -> m Atom
mapE f xs = do
  let TabTy n _ = getType xs
  buildFor Fwd n \i -> do
    x <- emit $ App xs i
    f x

emitMaybeCase :: MonadBuilder m => Atom -> m Atom -> (Atom -> m Atom) -> m Atom
emitMaybeCase scrut nothingCase justCase = do
  let (MaybeTy a) = getType scrut
  nothingAlt <- buildNAbs (Nest (Ignore UnitTy) Empty) \[_] -> nothingCase
  justAlt    <- buildNAbs (Nest (Bind ("x":>a)) Empty) \[x] -> justCase x
  let (Abs _ nothingBody) = nothingAlt
  let resultTy = getType nothingBody
  emit $ Case scrut [nothingAlt, justAlt] resultTy

-- Maybe a -> a
fromJustE :: MonadBuilder m => Atom -> m Atom
fromJustE x = do
  let MaybeTy a = getType x
  emitMaybeCase x
    (emitOp $ ThrowError a)
    return

-- Maybe a -> Bool
isJustE :: MonadBuilder m => Atom -> m Atom
isJustE x = emitMaybeCase x (return FalseAtom) (\_ -> return TrueAtom)

andMonoid :: MonadBuilder m => m BaseMonoid
andMonoid = do
  combiner <-
    buildLam (Ignore BoolTy) PureArrow \x ->
      buildLam (Ignore BoolTy) PureArrow \y -> do
        emitOp $ ScalarBinOp BAnd x y
  return $ BaseMonoid TrueAtom combiner

-- Bool -> (Unit -> {|eff} a) -> (() -> {|eff} a) -> {|eff} a
-- XXX: the first argument is the true case, following the
-- surface-level `if ... then ... else ...`, but the order
-- is flipped in the actual `Case`, because False acts like 0.
emitIf :: MonadBuilder m => Atom -> m Atom -> m Atom -> m Atom
emitIf predicate trueCase falseCase = do
  predicate' <- emitOp $ ToEnum (SumTy [UnitTy, UnitTy]) predicate
  falseCaseAbs <- buildNAbs (Nest (Ignore UnitTy) Empty) \[_] -> falseCase
  trueCaseAbs  <- buildNAbs (Nest (Ignore UnitTy) Empty) \[_] -> trueCase
  let (Abs _ trueBody) = trueCaseAbs
  let resultTy = getType trueBody
  emit $ Case predicate' [falseCaseAbs, trueCaseAbs] resultTy

-- (n:Type) ?-> (a:Type) ?-> (xs : n=>Maybe a) : Maybe (n => a) =
catMaybesE :: MonadBuilder m => Atom -> m Atom
catMaybesE maybes = do
  let TabTy n (MaybeTy a) = getType maybes
  justs <- mapE isJustE maybes
  monoid <- andMonoid
  allJust <- reduceE monoid justs
  emitIf allJust
    (JustAtom (TabTy n a) <$> mapE fromJustE maybes)
    (return (NothingAtom (TabTy n a)))

-- Dex implementation, for reference
-- def whileMaybe (eff:Effects) -> (body: Unit -> {|eff} (Maybe Word8)) : {|eff} Maybe Unit =
--   hadError = yieldState False \ref.
--     while do
--       ans = liftState ref body ()
--       case ans of
--         Nothing ->
--           ref := True
--           False
--         Just cond -> W8ToB cond
--   if hadError
--     then Nothing
--     else Just ()

runMaybeWhile :: MonadBuilder m => Atom -> m Atom
runMaybeWhile lam = do
  hadError <- getSnd =<< emitRunState "ref" FalseAtom \ref -> do
    emitWhile do
      ans <- emit $ App lam UnitVal
      emitMaybeCase ans
        (emitOp (PrimEffect ref $ MPut TrueAtom) >> return FalseAtom)
        return
    return UnitVal
  emitIf hadError
    (return $ NothingAtom UnitTy)
    (return $ JustAtom    UnitTy UnitVal)

makeClassDataDef :: SourceName -> Nest Binder -> [Type] -> [Type] -> DataDef
makeClassDataDef className params superclasses methods =
  DataDef className params [DataConDef ("Mk"<>className) (Nest (Ignore dictContents) Empty)]
  where dictContents = PairTy (ProdTy superclasses) (ProdTy methods)
