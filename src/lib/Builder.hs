-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ConstraintKinds #-}


module Builder (emit, emitOp, buildDepEffLam, buildPi,
                getAllowedEffects, withEffects, modifyAllowedEffects,
                emitAnn,
                buildLam, BuilderT, Builder, MonadBuilder (..),
                WithDecls (..), SubstBuilderT, SubstBuilder,
                substBuilderR, dropSubst, extendSubstR, lookupBindings,
                buildScoped, runBuilderT, app, add, mul, sub, neg, div',
                iadd, imul, isub, idiv, ilt, ieq,
                fpow, flog, fLitLike, recGetHead, buildImplicitNaryLam,
                select, substBuilder, renameBuilder, emitUnpack, getUnpacked,
                fromPair, getFst, getSnd, getFstRef, getSndRef,
                naryApp, appReduce, appTryReduce,
                buildFor, buildForAnn, emitBlock, unzipTab,
                isSingletonType, withNameHint,
                singletonTypeVal, applyPreludeFunction,
                unpackConsList, unpackLeftLeaningConsList,
                unpackBundle, unpackBundleTab,
                emitRunWriter, emitRunWriters, mextendForRef, monoidLift,
                emitRunState, emitMaybeCase, emitWhile, buildDataDef,
                emitRunReader, tabGet,
                ptrOffset, ptrLoad, unsafePtrLoad,
                evalBlockE, substTraversalDef,
                TraversalDef, traverseDecl, traverseDeclsOpen,
                traverseBlock, traverseExpr, traverseAtom,
                clampPositive, buildNAbs, buildNestedLam,
                appReduceTraversalDef,
                indexSetSizeE, indexToIntE, intToIndexE) where

-- import Control.Applicative
import Control.Monad
import Control.Monad.Except hiding (Except)
import Control.Monad.Reader
-- import Control.Monad.Writer hiding (Alt)
import Control.Monad.Identity
-- import Control.Monad.State.Strict
import Data.Foldable (toList)
import Data.List (elemIndex)
import Data.Maybe (fromJust)
-- import Data.String (fromString)
-- import Data.Tuple (swap)
-- import GHC.Stack

import Name
import Syntax
-- import Cat
import Type
import PPrint
import Util (bindM2, scanM, restructure)

type BuilderT = BuilderPT TypedBinderInfo
type Builder = BuilderT Identity
type MonadBuilder = MonadBuilderP TypedBinderInfo

type SubstBuilderT (m :: * -> *) (i :: *) (o :: *) =
       ReaderT (SubstEnv i o) (BuilderT m o)
type SubstBuilder i o = SubstBuilderT Identity i o

data WithDecls e n where WithDecls :: Nest Decl n l -> e l -> WithDecls e n

dropSubst :: SubstBuilder o o a -> SubstBuilder i o a
dropSubst = undefined

extendSubstR :: SubstEnvFrag i i' o -> SubstBuilder i' o a -> SubstBuilder i o a
extendSubstR = undefined

runBuilderT :: Bindings n
            -> (forall l. Ext n l -> BuilderT  m l (e l))
            -> m (WithDecls e n)
runBuilderT _ _ = undefined

lookupBindings :: MonadBuilder n m => Name n -> m (TypedBinderInfo n)
lookupBindings = undefined

emitAnn :: MonadBuilder n m => LetAnn -> Expr n -> m (Atom n)
emitAnn = undefined

emit :: MonadBuilder n m => Expr n -> m (Atom n)
emit expr = emitAnn PlainLet expr

emitOp :: MonadBuilder n m => Op n -> m (Atom n)
emitOp op = emit $ Op op

emitUnpack :: MonadBuilder n m => Expr n -> m [Atom n]
emitUnpack expr = getUnpacked =<< emit expr

emitBlock :: MonadBuilder n m => Block n -> m (Atom n)
emitBlock block = undefined -- emitBlockRec idEnv block

emitBlockRec :: MonadBuilder o m => SubstEnv i o -> Block i -> m (Atom o)
-- emitBlockRec env (Block (Nest (Let ann b expr) decls) result) = do
--   expr' <- substBuilder env expr
--   x <- emitTo (binderNameHint b) ann expr'
--   emitBlockRec (env <> b@>x) $ Block decls result
emitBlockRec env (Block Empty (Atom atom)) = substBuilder env atom
emitBlockRec env (Block Empty expr) = substBuilder env expr >>= emit

-- freshVarE :: MonadBuilder n m => BinderInfo -> Binder -> m Var
-- freshVarE bInfo b = do
--   v <- case b of
--     Ignore _    -> getNameHint
--     Bind (v:>_) -> return v
--   scope <- getScope
--   let v' = genFresh v scope
--   builderExtend $ asFst $ v' @> (binderType b, bInfo)
--   return $ v' :> binderType b

-- freshNestedBinders :: MonadBuilder n m => Nest Binder -> m (Nest Var)
-- freshNestedBinders bs = freshNestedBindersRec mempty bs

-- freshNestedBindersRec :: MonadBuilder n m => Env Atom -> Nest Binder -> m (Nest Var)
-- freshNestedBindersRec _ Empty = return Empty
-- freshNestedBindersRec substEnv (Nest b bs) = do
--   scope <- getScope
--   v  <- freshVarE PatBound $ subst (substEnv, scope) b
--   vs <- freshNestedBindersRec (substEnv <> b@>Var v) bs
--   return $ Nest v vs

buildPi :: (MonadError Err m, MonadBuilder n m)
        => Type n -> (Atom n -> m (WithArrow Type n)) -> m (Atom n)
buildPi b f = undefined
--   scope <- getScope
--   (ans, decls) <- scopedDecls $ do
--      v <- freshVarE PiBound b
--      (arr, ans) <- f $ Var v
--      return $ Pi $ makeAbs (Bind v) (arr, ans)
--   let block = wrapDecls decls ans
--   case typeReduceBlock scope block of
--     Just piTy -> return piTy
--     Nothing -> throw CompilerErr $
--       "Unexpected irreducible decls in pi type: " ++ pprint decls

-- instance (Ext a b, Ext b c) => Ext a c

-- binderAsVar :: Ext n l => Binder n l -> Atom l
-- binderAsVar b = Var $ binderName b :> liftNames (binderAnn b)




-- buildAbs :: MonadBuilder n m
--          => Type n
--          -> (Atom n -> m (e n))
--          -> m (Abs Binder (WithDecls e) n)
-- buildAbs = undefined  ty f = do
-- buildAbs ty f = do
--   withFreshBinder ty \b -> do
--     body <- scopedDecls $ f $ binderAsVar b
--     return $ Abs b body

-- buildAbs b f = do
--   ((b', ans), decls) <- scopedDecls $ do
--      v <- freshVarE UnknownBinder b
--      ans <- f $ Var v
--      return (b, ans)
--   return (Abs b' (decls, ans))

buildLam :: MonadBuilder n m
         => Type n -> Arrow n
         -> (Atom n -> m (Atom n))
         -> m (Atom n)
buildLam ty arr body = buildDepEffLam ty (const $ return arr) body

buildDepEffLam :: MonadBuilder n m
               => Type n
               -> (Atom n -> m (Arrow n))
               -> (Atom n -> m (Atom  n))
               -> m (Atom n)
buildDepEffLam ty fArr fBody = undefined

buildNAbs :: MonadBuilder n m => EmptyNest Binder n -> ([Atom n] -> m (Atom n)) -> m (Alt n)
buildNAbs bs body = undefined -- liftM fst $ buildNAbsAux bs \xs -> (,()) <$> body xs

  --  buildAbs ty \v -> do
 --    let x = Var v
 --    arr <- fArr x

-- ** TODO ** : we don't need this "overwriting" trick. either we're building a
-- ** plain lambda, in which case we know the arrow flavor ahead of time and we
-- ** can just ask for a function to produce the effect, or else we're building
-- ** a table/implicit lambda, in which case we don't have any dependence.

  --    -- overwriting the previous binder info know that we know more
 --    builderExtend $ asFst $ v @> (varType v, LamBound (void arr))
 --    (ans, aux) <- withEffects (arrowEff arr) $ fBody x
 --    return (Bind v, arr, ans, aux)
 -- return (Lam $ makeAbs ty' (arr, wrapDecls decls ans), aux)

 --  arr <- fArr
--   ((ty', arr, ans, aux), decls) <- scopedDecls $ do
--      v <- freshVarE UnknownBinder ty
--      let x = Var v
--      arr <- fArr x
--      -- overwriting the previous binder info know that we know more
--      builderExtend $ asFst $ v @> (varType v, LamBound (void arr))
--      (ans, aux) <- withEffects (arrowEff arr) $ fBody x
--      return (Bind v, arr, ans, aux)
--   return (Lam $ makeAbs ty' (arr, wrapDecls decls ans), aux)


  -- liftM fst $ buildLamAux ty fArr \x -> (,()) <$> fBody x



-- buildLamAux :: MonadBuilder n m
--             => Type n
--             -> (Atom n -> m (Arrow n))
--             -> (Atom n -> m (PairH Atom e n ))
--             -> m (PairH n, a)
-- buildLamAux _ _ _ = undefined
-- buildLamAux ty fArr fBody = do



--   ((ty', arr, ans, aux), decls) <- scopedDecls $ do
--      v <- freshVarE UnknownBinder ty
--      let x = Var v
--      arr <- fArr x
--      -- overwriting the previous binder info know that we know more
--      builderExtend $ asFst $ v @> (varType v, LamBound (void arr))
--      (ans, aux) <- withEffects (arrowEff arr) $ fBody x
--      return (Bind v, arr, ans, aux)
--   return (Lam $ makeAbs ty' (arr, wrapDecls decls ans), aux)

-- buildNAbsAux :: MonadBuilder n m => Nest Binder -> ([Atom] -> m (Atom, a)) -> m (Alt, a)
-- buildNAbsAux bs body = do
--   ((bs', (ans, aux)), decls) <- scopedDecls $ do
--      vs <- freshNestedBinders bs
--      result <- body $ map Var $ toList vs
--      return (fmap Bind vs, result)
--   return (Abs bs' $ wrapDecls decls ans, aux)

buildDataDef :: MonadBuilder n m
             => Name n -> EmptyNest Binder n
             -> ([Atom n] -> m [DataConDef n]) -> m (DataDef n)
buildDataDef tyConName paramBinders body = undefined
-- buildDataDef tyConName paramBinders body = do
--   ((paramBinders', dataDefs), _) <- scopedDecls $ do
--      vs <- freshNestedBinders paramBinders
--      result <- body $ map Var $ toList vs
--      return (fmap Bind vs, result)
--   return $ DataDef tyConName paramBinders' dataDefs

buildImplicitNaryLam :: MonadBuilder n m => Nest Binder n l
                     -> ([Atom n] -> m (Atom n)) -> m (Atom n)
buildImplicitNaryLam Empty body = body []
-- buildImplicitNaryLam (Nest b bs) body =
--   buildLam b ImplicitArrow \x -> do
--     bs' <- substBuilder (b@>x) bs
--     buildImplicitNaryLam bs' \xs -> body $ x:xs

recGetHead :: Label -> Atom n -> Atom n
recGetHead l x = do
  let (RecordTy (Ext r _)) = getType x
  let i = fromJust $ elemIndex l $ map fst $ toList $ reflectLabels r
  getProjection [i] x

buildScoped :: MonadBuilder n m => m (Atom n) -> m (Block n)
buildScoped m = undefined
  -- (ans, decls) <- scopedDecls m
  -- return $ wrapDecls decls ans

inlineLastDecl :: Block n -> Block n
inlineLastDecl = undefined
-- inlineLastDecl block@(Block decls result) =
--   case (reverse (toList decls), result) of
--     (Let _ (Bind v) expr:rest, Atom atom) | atom == Var v ->
--       Block (toNest (reverse rest)) expr
--     _ -> block

fLitLike :: Double -> Atom n -> Atom n
fLitLike x t = case getType t of
  BaseTy (Scalar Float64Type) -> Con $ Lit $ Float64Lit x
  BaseTy (Scalar Float32Type) -> Con $ Lit $ Float32Lit $ realToFrac x
  _ -> error "Expected a floating point scalar"

neg :: MonadBuilder n m => Atom n -> m (Atom n)
neg x = emitOp $ ScalarUnOp FNeg x

add :: MonadBuilder n m => Atom n -> Atom n -> m (Atom n)
add x y = emitOp $ ScalarBinOp FAdd x y

-- TODO: Implement constant folding for fixed-width integer types as well!
iadd :: MonadBuilder n m => Atom n -> Atom n -> m (Atom n)
iadd (Con (Lit l)) y | getIntLit l == 0 = return y
iadd x (Con (Lit l)) | getIntLit l == 0 = return x
iadd x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntBinOp (+) x y
iadd x y = emitOp $ ScalarBinOp IAdd x y

mul :: MonadBuilder n m => Atom n -> Atom n -> m (Atom n)
mul x y = emitOp $ ScalarBinOp FMul x y

imul :: MonadBuilder n m => Atom n -> Atom n -> m (Atom n)
imul   (Con (Lit l)) y               | getIntLit l == 1 = return y
imul x                 (Con (Lit l)) | getIntLit l == 1 = return x
imul x@(Con (Lit _)) y@(Con (Lit _))                    = return $ applyIntBinOp (*) x y
imul x y = emitOp $ ScalarBinOp IMul x y

sub :: MonadBuilder n m => Atom n -> Atom n -> m (Atom n)
sub x y = emitOp $ ScalarBinOp FSub x y

isub :: MonadBuilder n m => Atom n -> Atom n -> m (Atom n)
isub x (Con (Lit l)) | getIntLit l == 0 = return x
isub x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntBinOp (-) x y
isub x y = emitOp $ ScalarBinOp ISub x y

select :: MonadBuilder n m => Atom n -> Atom n -> Atom n -> m (Atom n)
select (Con (Lit (Word8Lit p))) x y = return $ if p /= 0 then x else y
select p x y = emitOp $ Select p x y

div' :: MonadBuilder n m => Atom n -> Atom n -> m (Atom n)
div' x y = emitOp $ ScalarBinOp FDiv x y

idiv :: MonadBuilder n m => Atom n -> Atom n -> m (Atom n)
idiv x (Con (Lit l)) | getIntLit l == 1 = return x
idiv x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntBinOp div x y
idiv x y = emitOp $ ScalarBinOp IDiv x y

irem :: MonadBuilder n m => Atom n -> Atom n -> m (Atom n)
irem x y = emitOp $ ScalarBinOp IRem x y

fpow :: MonadBuilder n m => Atom n -> Atom n -> m (Atom n)
fpow x y = emitOp $ ScalarBinOp FPow x y

flog :: MonadBuilder n m => Atom n -> m (Atom n)
flog x = emitOp $ ScalarUnOp Log x

ilt :: MonadBuilder n m => Atom n -> Atom n -> m (Atom n)
ilt x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntCmpOp (<) x y
ilt x y = emitOp $ ScalarBinOp (ICmp Less) x y

ieq :: MonadBuilder n m => Atom n -> Atom n -> m (Atom n)
ieq x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntCmpOp (==) x y
ieq x y = emitOp $ ScalarBinOp (ICmp Equal) x y

fromPair :: MonadBuilder n m => Atom n -> m (Atom n, Atom n)
fromPair pair = do
  ~[x, y] <- getUnpacked pair
  return (x, y)

getFst :: MonadBuilder n m => Atom n -> m (Atom n)
getFst p = fst <$> fromPair p

getSnd :: MonadBuilder n m => Atom n -> m (Atom n)
getSnd p = snd <$> fromPair p

getFstRef :: MonadBuilder n m => Atom n -> m (Atom n)
getFstRef r = emitOp $ FstRef r

getSndRef :: MonadBuilder n m => Atom n -> m (Atom n)
getSndRef r = emitOp $ SndRef r

-- XXX: getUnpacked must reduce its argument to enforce the invariant that
-- ProjectElt atoms are always fully reduced (to avoid type errors between two
-- equivalent types spelled differently).
getUnpacked :: MonadBuilder n m => Atom n -> m [Atom n]
getUnpacked = undefined
-- getUnpacked atom = do
--   scope <- getScope
--   let len = projectLength $ getType atom
--       atom' = typeReduceAtom scope atom
--       res = map (\i -> getProjection [i] atom') [0..(len-1)]
--   return res

app :: MonadBuilder n m => Atom n -> Atom n -> m (Atom n)
app x i = emit $ App x i

naryApp :: MonadBuilder n m => Atom n -> [Atom n] -> m (Atom n)
naryApp f xs = foldM app f xs

appReduce :: MonadBuilder n m => Atom n -> Atom n -> m (Atom n)
-- appReduce (Lam (Abs v (WithArrow _ b))) a =
--   runReaderT (evalBlockE substTraversalDef b) (v @> a)
appReduce _ _ = error "appReduce expected a lambda as the first argument"

-- TODO: this would be more convenient if we could add type inference too
applyPreludeFunction :: MonadBuilder n m => String -> [Atom n] -> m (Atom n)
applyPreludeFunction = undefined
-- applyPreludeFunction s xs = do
--   scope <- getScope
--   case envLookup scope fname of
--     Nothing -> error $ "Function not defined yet: " ++ s
--     Just (ty, _) -> naryApp (Var (fname:>ty)) xs
--   where fname = GlobalName (fromString s)

appTryReduce :: MonadBuilder n m => Atom n -> Atom n -> m (Atom n)
appTryReduce f x = case f of
  Lam _ -> appReduce f x
  _     -> app f x

ptrOffset :: MonadBuilder n m => Atom n -> Atom n -> m (Atom n)
ptrOffset x i = emitOp $ PtrOffset x i

unsafePtrLoad :: MonadBuilder n m => Atom n -> m (Atom n)
unsafePtrLoad x = emit $ Hof $ RunIO $ Lam $ Abs (Ignore :> UnitTy) $
  (WithArrow (PlainArrow (oneEffect IOEffect)) (Block Empty (Op (PtrLoad x))))

ptrLoad :: MonadBuilder n m => Atom n -> m (Atom n)
ptrLoad x = emitOp $ PtrLoad x

unpackConsList :: MonadBuilder n m => Atom n -> m [Atom n]
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
unpackLeftLeaningConsList :: MonadBuilder n m => Int -> Atom n -> m (Atom n, [Atom n])
unpackLeftLeaningConsList depth atom = go depth atom []
  where
    go 0        curAtom xs = return (curAtom, reverse xs)
    go remDepth curAtom xs = do
      (consTail, x) <- fromPair curAtom
      go (remDepth - 1) consTail (x : xs)

unpackBundle :: MonadBuilder n m => Atom n -> BundleDesc -> m [Atom n]
unpackBundle b size = case size of
  0 -> return []
  1 -> return [b]
  _ -> do
    (h, t) <- fromPair b
    (h:) <$> unpackBundle t (size - 1)

unpackBundleTab :: MonadBuilder n m => Atom n -> BundleDesc -> m [Atom n]
unpackBundleTab tab size = case size of
  0 -> return []
  1 -> return [tab]
  _ -> do
    (h, t) <- unzipTab tab
    (h:) <$> unpackBundleTab t (size - 1)

emitWhile :: MonadBuilder n m => m (Atom n) -> m ()
emitWhile body = do
  eff <- getAllowedEffects
  lam <- buildLam UnitTy (PlainArrow eff) \_ -> body
  void $ emit $ Hof $ While lam

emitMaybeCase :: MonadBuilder n m => Atom n -> m (Atom n)
              -> (Atom n -> m (Atom n)) -> m (Atom n)
emitMaybeCase = undefined
-- emitMaybeCase scrut nothingCase justCase = do
--   let (MaybeTy a) = getType scrut
--   nothingAlt <- buildNAbs Empty                        \[]  -> nothingCase
--   justAlt    <- buildNAbs (Nest (Bind ("x":>a)) Empty) \[x] -> justCase x
--   let (Abs _ nothingBody) = nothingAlt
--   let resultTy = getType nothingBody
--   emit $ Case scrut [nothingAlt, justAlt] resultTy

monoidLift :: Type n -> Type n -> EmptyNest Binder n
monoidLift = undefined
-- monoidLift baseTy accTy = case baseTy == accTy of
--   True  -> Empty
--   False -> case accTy of
--     TabTy n b -> Nest n $ monoidLift baseTy b
--     _         -> error $ "Base monoid type mismatch: can't lift " ++
--                          pprint baseTy ++ " to " ++ pprint accTy

mextendForRef :: MonadBuilder n m => Atom n -> BaseMonoid n -> Atom n -> m (Atom n)
mextendForRef = undefined
-- mextendForRef ref (BaseMonoid _ combine) update = do
--   buildLam (Bind $ "refVal":>accTy) PureArrow \refVal ->
--     buildNestedFor (fmap (Fwd,) $ toList liftIndices) $ \indices -> do
--       refElem <- tabGetNd refVal indices
--       updateElem <- tabGetNd update indices
--       bindM2 appTryReduce (appTryReduce combine refElem) (return updateElem)
--   where
--     TC (RefType _ accTy) = getType ref
--     FunTy (BinderAnn baseTy) _ _ = getType combine
--     liftIndices = monoidLift baseTy accTy

emitRunWriter :: MonadBuilder n m => Name n -> Type n -> BaseMonoid n
              -> (Atom n -> m (Atom n)) -> m (Atom n)
emitRunWriter v accTy bm body = do
  emit . Hof . RunWriter bm =<< mkBinaryEffFun Writer v accTy body

emitRunWriters :: MonadBuilder n m => [(Name n, Type n, BaseMonoid n)]
               -> ([Atom n] -> m (Atom n)) -> m (Atom n)
emitRunWriters inits body = go inits []
  where
    go [] refs = body $ reverse refs
    go ((v, accTy, bm):rest) refs = emitRunWriter v accTy bm $ \ref -> go rest (ref:refs)

emitRunReader :: MonadBuilder n m => Name n -> Atom n -> (Atom n -> m (Atom n)) -> m (Atom n)
emitRunReader v x0 body = do
  emit . Hof . RunReader x0 =<< mkBinaryEffFun Reader v (getType x0) body

emitRunState :: MonadBuilder n m => Name n -> Atom n
             -> (Atom n -> m (Atom n)) -> m (Atom n)
emitRunState v x0 body = do
  emit . Hof . RunState x0 =<< mkBinaryEffFun State v (getType x0) body

mkBinaryEffFun :: MonadBuilder n m => RWS -> Name n -> Type n
               -> (Atom n -> m (Atom n)) -> m (Atom n)
mkBinaryEffFun rws v ty body = do
  eff <- getAllowedEffects
  buildLam TyKind PureArrow \r@(Var (AnnVar rName _)) -> do
    let arr = PlainArrow $ extendEffect (RWSEffect rws rName) eff
    buildLam (RefTy r ty) arr body

-- buildForAnnAux :: MonadBuilder n m => ForAnn -> Binder -> (Atom n -> m (Atom, a)) -> m (Atom, a)
-- buildForAnnAux ann i body = do
--   -- TODO: consider only tracking the effects that are actually needed.
--   eff <- getAllowedEffects
--   (lam, aux) <- buildLamAux i (const $ return $ PlainArrow eff) body
--   (,aux) <$> (emit $ Hof $ For ann lam)

buildForAnn :: MonadBuilder n m => ForAnn -> Type n -> (Atom n -> m (Atom n)) -> m (Atom n)
buildForAnn ann iTy body = do
  eff <- getAllowedEffects
  lam <- buildLam iTy (PlainArrow eff) body
  emit $ Hof $ For ann lam

  -- fst <$> buildForAnnAux ann i (\x -> (,()) <$> body x)

-- buildForAux :: MonadBuilder n m => Direction -> Binder -> (Atom n -> m (Atom, a)) -> m (Atom, a)
-- buildForAux = buildForAnnAux . RegularFor

-- Do we need this variant?
buildFor :: MonadBuilder n m => Direction -> Type n -> (Atom n -> m (Atom n)) -> m (Atom n)
buildFor = buildForAnn . RegularFor

-- buildNestedFor :: forall m. MonadBuilder n m => [(Direction, Binder)] -> ([Atom] -> m (Atom n)) -> m (Atom n)
-- buildNestedFor specs body = go specs []
--   where
--     go :: [(Direction, Binder)] -> [Atom] -> m (Atom n)
--     go []        indices = body $ reverse indices
--     go ((d,b):t) indices = buildFor d b $ \i -> go t (i:indices)

buildNestedLam :: MonadBuilder n m => Arrow n -> [Type n]
               -> ([Atom n] -> m (Atom n)) -> m (Atom n)
buildNestedLam _ [] f = f []
buildNestedLam arr (b:bs) f =
  buildLam b arr \x -> buildNestedLam arr bs \xs -> f (x:xs)

tabGet :: MonadBuilder n m => Atom n -> Atom n -> m (Atom n)
tabGet tab idx = emit $ App tab idx

tabGetNd :: MonadBuilder n m => Atom n -> [Atom n] -> m (Atom n)
tabGetNd tab idxs = foldM (flip tabGet) tab idxs

unzipTab :: MonadBuilder n m => Atom n -> m (Atom n, Atom n)
unzipTab tab =
  case getType tab of
    TabTy b _ -> do
      fsts <- buildLam iTy TabArrow \i ->
                liftM fst $ app tab i >>= fromPair
      snds <- buildLam iTy TabArrow \i ->
                liftM snd $ app tab i >>= fromPair
      return (fsts, snds)
      where iTy = binderType b
    _ -> error "Not a table type"

renameBuilder :: (MonadBuilder o m, HasNames e) => RenameEnv i o -> e i -> m (e o)
renameBuilder env x = do
  bindings <- fromRecEnvFrag <$> riskyGetBindings
  return $ applyRename (asScopeFrag bindings) env x

substBuilder :: (MonadBuilder o m, Subst e) => SubstEnv i o -> e i -> m (e o)
substBuilder env x = do
  bindings <- fromRecEnvFrag <$> riskyGetBindings
  return $ applySubst (asScopeFrag bindings) env x

substBuilderR :: (MonadReader (SubstEnv i o) m, MonadBuilder o m, Subst e)
              => e i -> m (e o)
substBuilderR = undefined

-- checkBuilder :: (HasCallStack, MonadBuilder n m, HasVars a, HasType a) => a -> m a
-- checkBuilder x = do
--   scope <- getScope
--   let globals = freeVars x `envDiff` scope
--   unless (all (isGlobal . (:>())) $ envNames globals) $
--     error $ "Found a non-global free variable in " ++ pprint x
--   eff <- getAllowedEffects
--   case checkType (scope <> globals) eff x of
--     Left e   -> error $ pprint e
--     Right () -> return x

isSingletonType :: Type n -> Bool
isSingletonType ty = case singletonTypeVal ty of
  Nothing -> False
  Just _  -> True

-- TODO: TypeCon with a single case?
singletonTypeVal :: Type n -> Maybe (Atom n)
singletonTypeVal (TabTy v a) = TabValA v <$> singletonTypeVal a
singletonTypeVal (RecordTy (NoExt items)) = Record <$> traverse singletonTypeVal items
singletonTypeVal (TC con) = case con of
  PairType a b -> PairVal <$> singletonTypeVal a <*> singletonTypeVal b
  UnitType     -> return UnitVal
  _            -> Nothing
singletonTypeVal _ = Nothing

indexAsInt :: MonadBuilder n m => Atom n -> m (Atom n)
indexAsInt idx = emitOp $ ToOrdinal idx

-- This is purely for human readability. `const id` would be a valid implementation.
-- TODO: implement this!
withNameHint :: MonadBuilder n m => RawName -> m a -> m a
withNameHint _ = id

-- runBuilderT' :: Monad m => BuilderT m a -> BuilderEnv -> m (a, BuilderEnvC)
-- runBuilderT' (BuilderT m) (envR, envC) = runCatT (runReaderT m envR) envC

-- getScope :: MonadBuilder n m => m Scope
-- getScope = fst <$> builderLook

-- extendScope :: MonadBuilder n m => Scope -> m ()
-- extendScope scope = builderExtend $ asFst scope

getAllowedEffects :: MonadBuilder n m => m (EffectRow n)
getAllowedEffects = undefined  -- snd <$> builderAsk

withEffects :: MonadBuilder n m => EffectRow n -> m a -> m a
withEffects effs m = modifyAllowedEffects (const effs) m

modifyAllowedEffects :: MonadBuilder n m => (EffectRow n -> EffectRow n) -> m a -> m a
modifyAllowedEffects f m = undefined -- builderLocal (\(name, eff) -> (name, f eff)) m

-- emitDecl :: MonadBuilder n m => Decl -> m ()
-- emitDecl decl = builderExtend (bindings, Nest decl Empty)
--   where bindings = case decl of
--           Let ann b expr -> b @> (binderType b, LetBound ann expr)

-- scopedDecls :: MonadBuilder n m => m a -> m (a, Nest Decl)
-- scopedDecls m = do
--   (ans, (_, decls)) <- builderScoped m
--   return (ans, decls)

-- liftBuilder :: MonadBuilder n m => Builder a -> m a
-- liftBuilder action = do
--   envR <- builderAsk
--   envC <- builderLook
--   let (ans, envC') = runIdentity $ runBuilderT' action (envR, envC)
--   builderExtend envC'
--   return ans

-- === generic traversal ===

data TraversalDef o m = TraversalDef
  { traverseDeclDef :: forall i l. SubstEnv i o -> Decl i l -> m (SubstEnv l o)
  , traverseExprDef :: forall i  . SubstEnv i o -> Expr i   -> m (Expr o)
  , traverseAtomDef :: forall i  . SubstEnv i o -> Atom i   -> m (Atom o)}

substTraversalDef :: MonadBuilder n m => TraversalDef n m
substTraversalDef = undefined
-- substTraversalDef = ( traverseDecl substTraversalDef
--                     , traverseExpr substTraversalDef
--                     , traverseAtom substTraversalDef
--                     )

appReduceTraversalDef :: MonadBuilder n m => TraversalDef n m
appReduceTraversalDef = undefined
-- appReduceTraversalDef = ( traverseDecl appReduceTraversalDef
--                         , reduceAppExpr
--                         , traverseAtom appReduceTraversalDef
--                         )
--   where
--     reduceAppExpr expr = case expr of
--       App f' x' -> do
--         f <- traverseAtom appReduceTraversalDef f'
--         x <- traverseAtom appReduceTraversalDef x'
--         case f of
--           TabVal b body ->
--             Atom <$> (dropSub $ extendR (b@>x) $ evalBlockE appReduceTraversalDef body)
--           _ -> return $ App f x
--       _ -> traverseExpr appReduceTraversalDef expr

-- -- With `def = (traverseExpr def, traverseAtom def)` this should be a no-op
-- traverseDecls :: MonadBuilder n m => TraversalDef m
--               -> SubstEnv i o -> Nest Decl n l -> m ((Nest Decl), SubstEnv)
-- traverseDecls def decls = liftM swap $ scopedDecls $ traverseDeclsOpen def decls

traverseDeclsOpen :: MonadBuilder o m => TraversalDef o m -> SubstEnv i o
                  -> Nest Decl i l -> m (SubstEnv l o)
traverseDeclsOpen = undefined
-- traverseDeclsOpen _ Empty = return mempty
-- traverseDeclsOpen def@(fDecl, _, _) (Nest decl decls) = do
--   env <- fDecl decl
--   env' <- extendR env $ traverseDeclsOpen def decls
--   return (env <> env')

traverseDecl :: MonadBuilder o m => TraversalDef o m -> SubstEnv i o
             -> Decl i l -> m (SubstEnv l o)
traverseDecl def subst decl = case decl of
  Let letAnn b expr -> do
    expr' <- traverseExprDef def subst expr
    undefined
    -- case expr' of
    --   Atom a | not (isGlobalBinder b) && letAnn == PlainLet -> return $ b @> a
    --   _ -> (b@>) <$> emitTo (binderNameHint b) letAnn expr'

traverseBlock :: MonadBuilder o m => TraversalDef o m -> SubstEnv i o
              -> Block i -> m (Block o)
traverseBlock def subst block = buildScoped $ evalBlockE def subst block

evalBlockE :: MonadBuilder o m => TraversalDef o m -> SubstEnv i o
           -> Block i -> m (Atom o)
evalBlockE def subst (Block decls result) = do
  subst' <- traverseDeclsOpen def subst decls
  resultExpr <- traverseExprDef def subst' result
  case resultExpr of
    Atom a -> return a
    _      -> emit resultExpr

traverseExpr :: MonadBuilder o m => TraversalDef o m -> SubstEnv i o
             -> Expr i -> m (Expr o)
traverseExpr def subst expr = case expr of
  App g x -> App  <$> recur g <*> recur x
  Atom x  -> Atom <$> recur x
  Op  op  -> Op   <$> traverse recur op
  Hof hof -> Hof  <$> traverse recur hof
--   Case e alts ty -> Case <$> fAtom e <*> mapM traverseAlt alts <*> fAtom ty
--   where
--     traverseAlt (Abs bs body) = do
--       bs' <- mapM (mapM fAtom) bs
--       buildNAbs bs' \xs -> extendR (newEnv bs' xs) $ evalBlockE def body
  where recur = traverseAtomDef def subst

traverseAtom :: MonadBuilder o m => TraversalDef o m -> SubstEnv i o
             -> Atom i -> m (Atom o)
traverseAtom def subst atom = case atom of
--   Var _ -> substBuilderR atom
--   Lam (Abs b (arr, body)) -> do
--     b' <- mapM fAtom b
--     buildDepEffLam b'
--       (\x -> extendR (b'@>x) (substBuilderR arr))
--       (\x -> extendR (b'@>x) (evalBlockE def body))
--   Pi _ -> substBuilderR atom
  Con con -> Con <$> traverse recur con
  TC  tc  -> TC  <$> traverse recur tc
--   Eff _   -> substBuilderR atom
--   DataCon dataDef params con args -> DataCon dataDef <$>
--     traverse fAtom params <*> pure con <*> traverse fAtom args
--   TypeCon dataDef params -> TypeCon dataDef <$> traverse fAtom params
--   LabeledRow (Ext items rest) -> do
--     items' <- traverse fAtom items
--     return $ LabeledRow $ Ext items' rest
--   Record items -> Record <$> traverse fAtom items
--   RecordTy (Ext items rest) -> do
--     items' <- traverse fAtom items
--     return $ RecordTy $ Ext items' rest
--   Variant (Ext types rest) label i value -> do
--     types' <- traverse fAtom types
--     Variant (Ext types' rest) label i <$> fAtom value
--   VariantTy (Ext items rest) -> do
--     items' <- traverse fAtom items
--     return $ VariantTy $ Ext items' rest
--   ACase e alts ty -> ACase <$> fAtom e <*> mapM traverseAAlt alts <*> fAtom ty
--   DataConRef dataDef params args -> DataConRef dataDef <$>
--     traverse fAtom params <*> traverseNestedArgs args
--   BoxedRef b ptr size body -> do
--     ptr'  <- fAtom ptr
--     size' <- buildScoped $ evalBlockE def size
--     Abs b' (decls, body') <- buildAbs b \x ->
--       extendR (b@>x) $ evalBlockE def (Block Empty $ Atom body)
--     case decls of
--       Empty -> return $ BoxedRef b' ptr' size' body'
--       _ -> error "Traversing the body atom shouldn't produce decls"
--   ProjectElt _ _ -> substBuilderR atom
--   where
--     traverseNestedArgs :: Nest DataConRefBinding -> m (Nest DataConRefBinding)
--     traverseNestedArgs Empty = return Empty
--     traverseNestedArgs (Nest (DataConRefBinding b ref) rest) = do
--       ref' <- fAtom ref
--       b' <- substBuilderR b
--       v <- freshVarE UnknownBinder b'
--       rest' <- extendR (b @> Var v) $ traverseNestedArgs rest
--       return $ Nest (DataConRefBinding (Bind v) ref') rest'

--     traverseAAlt (Abs bs a) = do
--       bs' <- mapM (mapM fAtom) bs
--       (Abs bs'' b) <- buildNAbs bs' \xs -> extendR (newEnv bs' xs) $ fAtom a
--       case b of
--         Block Empty (Atom r) -> return $ Abs bs'' r
--         _                    -> error "ACase alternative traversal has emitted decls or exprs!"
  where recur = traverseAtomDef def subst

-- transformModuleAsBlock :: (Block -> Block) -> Module -> Module
-- transformModuleAsBlock transform (Module ir decls bindings) = do
--   let localVars = filter (not . isGlobal) $ bindingsAsVars $ freeVars bindings
--   let block = Block decls $ Atom $ mkConsList $ map Var localVars
--   let (Block newDecls (Atom newResult)) = transform block
--   let newLocalVals = ignoreExcept $ fromConsList newResult
--   Module ir newDecls $ scopelessSubst (newEnv localVars newLocalVals) bindings

indexSetSizeE :: MonadBuilder n m => Type n -> m (Atom n)
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

clampPositive :: MonadBuilder n m => Atom n -> m (Atom n)
clampPositive x = do
  isNegative <- x `ilt` (IdxRepVal 0)
  select isNegative (IdxRepVal 0) x

-- XXX: Be careful if you use this function as an interpretation for
--      IndexAsInt instruction, as for Int and IndexRanges it will
--      generate the same instruction again, potentially leading to an
--      infinite loop.
indexToIntE :: MonadBuilder n m => Atom n -> m (Atom n)
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
  -- VariantTy (NoExt types) -> do
  --   sizes <- traverse indexSetSizeE types
  --   (offsets, _) <- scanM (\sz prev -> (prev,) <$> iadd sz prev) sizes (IdxRepVal 0)
  --   -- Build and apply a case expression
  --   alts <- flip mapM (zip (toList offsets) (toList types)) $
  --     \(offset, subty) -> buildNAbs (toNest [Ignore subty]) \[subix] -> do
  --       i <- indexToIntE subix
  --       iadd offset i
  --   emit $ Case idx alts IdxRepTy
  ty -> error $ "Unexpected type " ++ pprint ty

intToIndexE :: MonadBuilder n m => Type n -> Atom n -> m (Atom n)
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
