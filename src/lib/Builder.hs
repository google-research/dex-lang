-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ConstraintKinds #-}

module Builder (
  Builder, emit, emitAnn, emitOp, emitUnOp,
  imul, iadd, idiv,
  neg, add, sub, mul, div, div', fpow, flog, fLitLike,
  app, tabGet, buildTabLam, buildPureLam, getProjection, buildFor,
  clampPositive, ptrOffset, indexSetSizeE, unzipTab,
  unsafePtrLoad, appReduce, intToIndexE, indexToIntE,
  getIntLit
  ) where

import Data.List (elemIndex)
import qualified Data.List.NonEmpty as NE
import Data.String (fromString)
import Data.Text.Prettyprint.Doc
import Data.Tuple (swap)

import Preamble
import Base
import Naming
import Syntax
import Cat
import Type

-- === Builder monad ===

type Builder n m = (DefWriter n m, EffectCtx n m)

emit :: Builder n m => Expr n -> m (Atom n)
emit expr = emitAnn PlainLet expr

emitAnn :: Builder n m => LetAnn -> Expr n -> m (Atom n)
emitAnn = undefined

emitOp :: Builder n m => PrimOp (Atom n) -> m (Atom n)
emitOp op = emit $ Op op

-- === Helpers for building lambdas and other scoped constructs ===

-- === Helpers for effects  ===

-- === Misc helpers ===

emitUnpack :: Builder n m => Expr n -> m [Atom n]
emitUnpack expr = getUnpacked =<< emit expr

emitBlock :: Builder n m => Block n -> m (Atom n)
emitBlock block = undefined -- emitBlockRec mempty block

-- emitBlockRec = undefined
-- emitBlockRec env (Block (Nest (Let ann b expr) decls) result) = do
--   expr' <- substBuilder env expr
--   x <- withNameHint b $ emitAnn ann expr'
--   emitBlockRec (env <> b@>x) $ Block decls result
-- emitBlockRec env (Block Empty (Atom atom)) = substBuilder env atom
-- emitBlockRec env (Block Empty expr) = substBuilder env expr >>= emit

-- freshNestedBinders :: Builder n m => Nest Binder n -> m (Nest Var n)
-- freshNestedBinders bs = freshNestedBindersRec mempty bs

-- freshNestedBindersRec :: Builder n m => Env n (Atom n)
--                       -> Nest Binder n -> m (Nest Var n)
-- freshNestedBindersRec = undefined
-- freshNestedBindersRec _ Empty = return Empty
-- freshNestedBindersRec substEnv (Nest b bs) = do
--   bindings <- getBindings
--   v  <- freshVarE PatBound $ subst (substEnv, bindings) b
--   vs <- freshNestedBindersRec (substEnv <> b@>Var v) bs
--   return $ Nest v vs

-- buildPi :: (MonadError Err m, Builder n m)
--         => Type n -> (Atom n -> m (Arrow n, Type n)) -> m (Atom n)
-- buildPi = undefined
-- buildPi ty f = do
--   bindings <- getBindings
--   (ans, decls) <- scopedDecls $ do
--      (b, x) <- freshVarE PiBound ty
--      (arr, ans) <- f x
--      return $ Pi $ makeAbs b (WithArrow arr ans)
--   let block = wrapDecls decls ans
--   case typeReduceBlock bindings block of
--     Just piTy -> return piTy
--     Nothing -> throw CompilerErr $
--       "Unexpected irreducible decls in pi type: " ++ pprint decls

-- buildAbs :: Builder n m
--          => Type n -> Binding n
--          -> (Atom n -> m (e n))
--          -> m (Abs Type (WithBindings e) n)
-- buildAbs ty f = do
--   ((b, ans), decls) <- scopedDecls $ do
--      (b, x) <- freshVarE UnknownBinder ty
--      ans <- f x
--      return (b, ans)
--   return (Abs b (Abs decls ans))

-- buildLam :: Builder n m
--          => Arrow -> Type n
--          -> (Atom n -> m (Atom n)) -> m (Atom n)
-- buildLam ty arr body = buildDepEffLam ty (const (return arr)) body


buildTabLam :: Builder n m => Type n -> (Atom n -> m (Atom n)) -> m (Atom n)
buildTabLam = undefined -- liftM fst $ buildLamAux b fArr \x -> (,()) <$> fBody x

buildPureLam :: Builder n m => Type n -> (Atom n -> m (Atom n)) -> m (Atom n)
buildPureLam = undefined -- liftM fst $ buildLamAux b fArr \x -> (,()) <$> fBody x


buildLam :: Builder n m
         => Arrow
         -> (Atom n -> m (EffectRow n))
         -> Type n
         -> (Atom n -> m (Atom n))
         -> m (Atom n)
buildLam = undefined -- liftM fst $ buildLamAux b fArr \x -> (,()) <$> fBody x

-- buildLamAux :: Builder n m
--             => Type n
--             -> (Atom n -> m (Arrow n))
--             -> (Atom n -> m (Atom n, a))
--             -> m (Atom n, a)
-- buildLamAux b fArr fBody = do
--   ((b', arr, ans, aux), decls) <- scopedDecls $ do
--      (b, x) <- freshVarE UnknownBinder b
--      arr <- fArr x
--      -- overwriting the previous binder info know that we know more
--      builderExtend $ asFst $ v @> (varType v, LamBound (void arr))
--      (ans, aux) <- withEffects (arrowEff arr) $ fBody x
--      return (Bind v, arr, ans, aux)
--   return (Lam $ makeAbs b' (WithArrow arr $ wrapDecls decls ans), aux)

-- buildNAbs :: Builder n m => NAbs Type HUnit n
--           -> ([Atom n] -> m (Atom n)) -> m (NAbs Type Block n)
-- buildNAbs bs body = undefined -- liftM fst $ buildNAbsAux bs \xs -> (,()) <$> body xs

-- buildNAbsAux :: Builder n m => Nest Binder n
--              -> ([Atom n] -> m (Atom n, a)) -> m (Alt n, a)
-- buildNAbsAux bs body = do
--   ((bs', (ans, aux)), decls) <- scopedDecls $ do
--      vs <- freshNestedBinders bs
--      result <- body $ map Var $ toList vs
--      return (fmap Bind vs, result)
--   return (Abs bs' $ wrapDecls decls ans, aux)

-- buildTypeDef :: Builder n m
-- buildTypeDef tyConName paramBinders body = do
--   ((paramBinders', dataDefs), _) <- scopedDecls $ do
--      vs <- freshNestedBinders paramBinders
--      result <- body $ map Var $ toList vs
--      return (fmap Bind vs, result)
--   return $ TypeDef tyConName paramBinders' dataDefs

-- buildImplicitNaryLam :: Builder n m => (Nest Binder n)
--                      -> ([Atom n] -> m (Atom n)) -> m (Atom n)
-- buildImplicitNaryLam Empty body = body []
-- buildImplicitNaryLam (Nest b bs) body =
--   buildLam b ImplicitArrow \x -> do
--     bs' <- substBuilder (b@>x) bs
--     buildImplicitNaryLam bs' \xs -> body $ x:xs

-- buildTypeDef :: Builder n m
--              => NameStr -> [NameStr] -> Type n
--              -> (Atom n -> m [Type n])
--              -> m (Atom n, [Atom n])
-- buildTypeDef tyConHint dataConHints tyConType dataConTyBuilders = undefined

recGetHead :: Builder n m => Label -> Atom n -> m (Atom n)
recGetHead = undefined
-- recGetHead l x = do
--   ~(RecordTy (Ext r _)) <- getType x
--   let i = fromJust $ elemIndex l $ map fst $ toList $ reflectLabels r
--   return $ getProjection [i] x

buildScopedBlock :: Builder n m => m (Atom n) -> m (Block n)
buildScopedBlock = undefined

emitWithBindings :: Builder n m => WithDefs e n -> m (e n)
emitWithBindings = undefined

wrapDecls :: [Decl n] -> Atom n -> Block n
wrapDecls = undefined
-- wrapDecls decls atom = inlineLastDecl $ Block decls $ Atom atom

inlineLastDecl :: Block n -> Block n
inlineLastDecl = undefined
-- inlineLastDecl block@(Block decls result) =
--   case (reverse (fromNest decls), result) of
--     (Let _ (Just v :> ty) expr:rest, Atom atom) | atom == Var (Occ v ty) ->
--       Block (toNest (reverse rest)) expr
--     _ -> block

fLitLike :: Builder n m => Double -> Atom n -> m (Atom n)
fLitLike x t = do
  ty <- getType t
  return case ty of
    BaseTy (Scalar Float64Type) -> PrimCon $ Lit $ Float64Lit x
    BaseTy (Scalar Float32Type) -> PrimCon $ Lit $ Float32Lit $ realToFrac x
    _ -> error "Expected a floating point scalar"

emitUnOp :: Builder n m => UnOp -> Atom n -> m (Atom n)
emitUnOp op x = emitOp $ ScalarUnOp op x

neg :: Builder n m => Atom n -> m (Atom n)
neg x = emitOp $ ScalarUnOp FNeg x

add :: Builder n m => Atom n -> Atom n -> m (Atom n)
add x y = emitOp $ ScalarBinOp FAdd x y

-- TODO: Implement constant folding for fixed-width integer types as well!
iadd :: Builder n m => Atom n -> Atom n -> m (Atom n)
iadd (PrimCon (Lit l)) y | getIntLit l == 0 = return y
iadd x (PrimCon (Lit l)) | getIntLit l == 0 = return x
iadd x@(PrimCon (Lit _)) y@(PrimCon (Lit _)) = return $ applyIntBinOp (+) x y
iadd x y = emitOp $ ScalarBinOp IAdd x y

mul :: Builder n m => Atom n -> Atom n -> m (Atom n)
mul x y = emitOp $ ScalarBinOp FMul x y

imul :: Builder n m => Atom n -> Atom n -> m (Atom n)
imul   (PrimCon (Lit l)) y               | getIntLit l == 1 = return y
imul x                 (PrimCon (Lit l)) | getIntLit l == 1 = return x
imul x@(PrimCon (Lit _)) y@(PrimCon (Lit _))                    = return $ applyIntBinOp (*) x y
imul x y = emitOp $ ScalarBinOp IMul x y

sub :: Builder n m => Atom n -> Atom n -> m (Atom n)
sub x y = emitOp $ ScalarBinOp FSub x y

isub :: Builder n m => Atom n -> Atom n -> m (Atom n)
isub x (PrimCon (Lit l)) | getIntLit l == 0 = return x
isub x@(PrimCon (Lit _)) y@(PrimCon (Lit _)) = return $ applyIntBinOp (-) x y
isub x y = emitOp $ ScalarBinOp ISub x y

select :: Builder n m => Atom n -> Atom n -> Atom n -> m (Atom n)
select (PrimCon (Lit (Word8Lit p))) x y = return $ if p /= 0 then x else y
select p x y = emitOp $ Select p x y

div' :: Builder n m => Atom n -> Atom n -> m (Atom n)
div' x y = emitOp $ ScalarBinOp FDiv x y

idiv :: Builder n m => Atom n -> Atom n -> m (Atom n)
idiv x (PrimCon (Lit l)) | getIntLit l == 1 = return x
idiv x@(PrimCon (Lit _)) y@(PrimCon (Lit _)) = return $ applyIntBinOp div x y
idiv x y = emitOp $ ScalarBinOp IDiv x y

irem :: Builder n m => Atom n -> Atom n -> m (Atom n)
irem x y = emitOp $ ScalarBinOp IRem x y

fpow :: Builder n m => Atom n -> Atom n -> m (Atom n)
fpow x y = emitOp $ ScalarBinOp FPow x y

flog :: Builder n m => Atom n -> m (Atom n)
flog x = emitOp $ ScalarUnOp Log x

ilt :: Builder n m => Atom n -> Atom n -> m (Atom n)
ilt x@(PrimCon (Lit _)) y@(PrimCon (Lit _)) = return $ applyIntCmpOp (<) x y
ilt x y = emitOp $ ScalarBinOp (ICmp Less) x y

ieq :: Builder n m => Atom n -> Atom n -> m (Atom n)
ieq x@(PrimCon (Lit _)) y@(PrimCon (Lit _)) = return $ applyIntCmpOp (==) x y
ieq x y = emitOp $ ScalarBinOp (ICmp Equal) x y

fromPair :: Builder n m => Atom n -> m (Atom n, Atom n)
fromPair pair = do
  ~[x, y] <- getUnpacked pair
  return (x, y)

getFst :: Builder n m => Atom n -> m (Atom n)
getFst p = fst <$> fromPair p

getSnd :: Builder n m => Atom n -> m (Atom n)
getSnd p = snd <$> fromPair p

getFstRef :: Builder n m => Atom n -> m (Atom n)
getFstRef r = emitOp $ FstRef r

getSndRef :: Builder n m => Atom n -> m (Atom n)
getSndRef r = emitOp $ SndRef r

-- XXX: getUnpacked must reduce its argument to enforce the invariant that
-- ProjectElt atoms are always fully reduced (to avoid type errors between two
-- equivalent types spelled differently).
getUnpacked :: Builder n m => Atom n -> m [Atom n]
getUnpacked = undefined
-- getUnpacked atom = do
--   bindings <- getBindings
--   len <- projectLength <$> getType atom
--   let atom' = typeReduceAtom bindings atom
--   let res = map (\i -> getProjection [i] atom') [0..(len-1)]
--   return res

getProjection :: [Int] -> Atom n -> Atom n
getProjection [] a = a
getProjection (i:is) a = case getProjection is a of
  Var v -> ProjectElt (NE.fromList [i]) v
  ProjectElt idxs' a' -> ProjectElt (NE.cons i idxs') a'
  -- Con _ xs -> xs !! i  -- need to look up to decide how many params there are
  Record items -> toList items !! i
  PairVal x _ | i == 0 -> x
  PairVal _ y | i == 1 -> y
  _ -> error $ "Not a valid projection: " ++ show i ++ " of " ++ show a

app :: Builder n m => Atom n -> Atom n -> m (Atom n)
app x i = emit $ App PlainArrow x i

naryApp :: Builder n m => Atom n -> [Atom n] -> m (Atom n)
naryApp f xs = foldM app f xs

appReduce :: Builder n m => Atom n -> Atom n -> m (Atom n)
appReduce = undefined
-- appReduce (Lam _ (UnsafeMakeAbs _ v b)) a =
--   runReaderT (evalBlockE substTraversalDef b) (foldMap (@>a) v)
-- appReduce _ _ = error "appReduce expected a lambda as the first argument"

-- TODO: this would be more convenient if we could add type inference too
applyPreludeFunction :: Builder n m => SourceName -> [Atom n] -> m (Atom n)
applyPreludeFunction = undefined
-- applyPreludeFunction s xs = do
--   bindings <- getBindings
--   case envLookup bindings fname of
--     Nothing -> error $ "Function not defined yet: " ++ s
--     Just (ty, _) -> naryApp (Var (Occ fname ty)) xs

appTryReduce :: Builder n m => Atom n -> Atom n -> m (Atom n)
appTryReduce f x = case f of
  Lam _ _ _ _ -> appReduce f x
  _ -> app f x

ptrOffset :: Builder n m => Atom n -> Atom n -> m (Atom n)
ptrOffset x i = emitOp $ PtrOffset x i

unsafePtrLoad :: Builder n m => Atom n -> m (Atom n)
unsafePtrLoad = undefined
-- unsafePtrLoad x = emit $ Hof $ RunIO $ Lam $ Abs (Ignore UnitTy) $
--   WithArrow (PlainArrow (oneEffect IOEffect)) $ Block (NAbsBody (Op (PtrLoad x)))

ptrLoad :: Builder n m => Atom n -> m (Atom n)
ptrLoad x = emitOp $ PtrLoad x

unpackConsList :: Builder n m => Atom n -> m [Atom n]
unpackConsList xs = do
  ty <- getType xs
  case ty of
    UnitTy -> return []
    PairTy _ UnitTy -> (:[]) <$> getFst xs
    PairTy _ _ -> do
      (x, rest) <- fromPair xs
      liftM (x:) $ unpackConsList rest
    _ -> error $ "Not a cons list: " ++ pprint ty

-- ((...((ans, x{n}), x{n-1})..., x2), x1) -> (ans, [x1, ..., x{n}])
-- This is useful for unpacking results of stacked effect handlers (as produced
-- by e.g. emitRunWriters).
unpackLeftLeaningConsList :: Builder n m
                          => Int -> Atom n -> m (Atom n, [Atom n])
unpackLeftLeaningConsList depth atom = go depth atom []
  where
    go 0        curAtom xs = return (curAtom, reverse xs)
    go remDepth curAtom xs = do
      (consTail, x) <- fromPair curAtom
      go (remDepth - 1) consTail (x : xs)

emitWhile :: Builder n m => m (Atom n) -> m ()
emitWhile = undefined
-- emitWhile body = do
--   eff <- getAllowedEffects
--   lam <- buildLam PlainArrow (const $ return eff) UnitTy \_ -> body
--   void $ emit $ Hof $ While lam

emitMaybeCase :: Builder n m => Atom n -> m (Atom n)
              -> (Atom n -> m (Atom n)) -> m (Atom n)
emitMaybeCase = undefined
-- emitMaybeCase scrut nothingCase justCase = do
--   let (MaybeTy a) = getType scrut
--   nothingAlt <- buildNAbs Empty                        \[]  -> nothingCase
--   justAlt    <- buildNAbs (Nest (Just "x" :> a) Empty) \[x] -> justCase x
--   let (Abs _ nothingBody) = nothingAlt
--   let resultTy = getType nothingBody
--   emit $ Case scrut [nothingAlt, justAlt] resultTy

monoidLift :: Type n -> Type n -> IndexStructure n
monoidLift = undefined
-- monoidLift baseTy accTy = case baseTy == accTy of
--   True  -> Empty
--   False -> case accTy of
--     TabTy n b -> Nest n $ monoidLift baseTy b
--     _         -> error $ "Base monoid type mismatch: can't lift " ++
--                          pprint baseTy ++ " to " ++ pprint accTy

mextendForRef :: Builder n m => Atom n -> BaseMonoid n -> Atom n -> m (Atom n)
mextendForRef = undefined
-- mextendForRef ref (BaseMonoid _ combine) update = do
--   buildLam accTy PureArrow \refVal ->
--     buildNestedFor (repeat Fwd) (ClosedBindings liftIndices) $ \indices -> do
--       refElem <- tabGetNd refVal indices
--       updateElem <- tabGetNd update indices
--       bindM2 appTryReduce (appTryReduce combine refElem) (return updateElem)
--   where
--     TC (RefType _ accTy) = getType ref
--     Pi _ _ baseTy _ = getType combine
--     liftIndices = monoidLift baseTy accTy

emitRunWriter :: Builder n m
              => Type n -> BaseMonoid n
              -> (Atom n -> m (Atom n)) -> m (Atom n)
emitRunWriter accTy bm body = do
  emit . Hof . RunWriter bm =<< mkBinaryEffFun Writer accTy body

emitRunWriters :: Builder n m
               => [(Type n, BaseMonoid n)]
               -> ([Atom n] -> m (Atom n)) -> m (Atom n)
emitRunWriters inits body = go inits []
  where
    go [] refs = body $ reverse refs
    go ((accTy, bm):rest) refs = emitRunWriter accTy bm $ \ref -> go rest (ref:refs)

emitRunReader :: Builder n m
              => Atom n -> (Atom n -> m (Atom n)) -> m (Atom n)
emitRunReader x0 body = do
  ty <- getType x0
  emit . Hof . RunReader x0 =<< mkBinaryEffFun Reader ty body

emitRunState :: Builder n m
             => Atom n -> (Atom n -> m (Atom n)) -> m (Atom n)
emitRunState x0 body = do
  ty <- getType x0
  emit . Hof . RunState x0 =<< mkBinaryEffFun State ty body

mkBinaryEffFun :: Builder n m
               => RWS -> Type n -> (Atom n -> m (Atom n)) -> m (Atom n)
mkBinaryEffFun = undefined
-- mkBinaryEffFun rws ty body = do
--   eff <- getAllowedEffects
--   buildLam TyKind PureArrow \r@(Var rName) -> do
--     let arr = PlainArrow $ extendEffect (RWSEffect rws rName) eff
--     buildLam (RefTy r ty) arr body

buildFor :: Builder n m => Direction -> Type n
         -> (Atom n -> m (Atom n)) -> m (Atom n)
buildFor = undefined -- buildForAnn . RegularFor

buildView :: Builder n m => Type n -> (Atom n -> m (Atom n)) -> m (Atom n)
buildView = undefined

buildNestedFor :: forall n m. Builder n m
               => [Direction]
               -> IndexStructure n
               -> ([Atom n] -> m (Atom n)) -> m (Atom n)
buildNestedFor = undefined
-- buildNestedFor specs body = go specs []
--   where
--     go :: [(Direction, Binder n)] -> [Atom n] -> m (Atom n)
--     go []        indices = body $ reverse indices
--     go ((d,b):t) indices = buildFor d b $ \i -> go t (i:indices)

tabGet :: Builder n m => Atom n -> Atom n -> m (Atom n)
tabGet tab idx = emit $ App TabArrow tab idx

tabGetNd :: Builder n m => Atom n -> [Atom n] -> m (Atom n)
tabGetNd tab idxs = foldM (flip tabGet) tab idxs

unzipTab :: Builder n m => Atom n -> m (Atom n, Atom n)
unzipTab tab = do
  ~(Pi _ _ ty _) <- getType tab
  fsts <- buildView ty \i -> liftM fst $ app tab i >>= fromPair
  snds <- buildView ty \i -> liftM snd $ app tab i >>= fromPair
  return (fsts, snds)

isSingletonType :: Type n -> Bool
isSingletonType ty = case singletonTypeVal ty of
  Nothing -> False
  Just _  -> True

-- TODO: TypeCon with a single case?
singletonTypeVal :: Type n -> Maybe (Atom n)
-- singletonTypeVal (TabTy v a) = TabValA v <$> singletonTypeVal a
-- singletonTypeVal (RecordTy (NoExt items)) = Record <$> traverse singletonTypeVal items
singletonTypeVal (PrimTC con) = case con of
  PairType a b -> PairVal <$> singletonTypeVal a <*> singletonTypeVal b
  UnitType     -> return UnitVal
  _            -> Nothing
singletonTypeVal _ = Nothing

indexAsInt :: Builder n m => Atom n -> m (Atom n)
indexAsInt idx = emitOp $ ToOrdinal idx

indexSetSizeE :: Builder n m => Type n -> m (Atom n)
indexSetSizeE = undefined
-- indexSetSizeE (TC con) = case con of
--   UnitType                   -> return $ IdxRepVal 1
--   IntRange low high -> clampPositive =<< high `isub` low
--   IndexRange n low high -> do
--     low' <- case low of
--       InclusiveLim x -> indexToIntE x
--       ExclusiveLim x -> indexToIntE x >>= iadd (IdxRepVal 1)
--       Unlimited      -> return $ IdxRepVal 0
--     high' <- case high of
--       InclusiveLim x -> indexToIntE x >>= iadd (IdxRepVal 1)
--       ExclusiveLim x -> indexToIntE x
--       Unlimited      -> indexSetSizeE n
--     clampPositive =<< high' `isub` low'
--   PairType a b -> bindM2 imul (indexSetSizeE a) (indexSetSizeE b)
--   ParIndexRange _ _ _ -> error "Shouldn't be querying the size of a ParIndexRange"
--   _ -> error $ "Not implemented " ++ pprint con
-- indexSetSizeE (RecordTy (NoExt types)) = do
--   sizes <- traverse indexSetSizeE types
--   foldM imul (IdxRepVal 1) sizes
-- indexSetSizeE (VariantTy (NoExt types)) = do
--   sizes <- traverse indexSetSizeE types
--   foldM iadd (IdxRepVal 0) sizes
-- indexSetSizeE ty = error $ "Not implemented " ++ pprint ty

clampPositive :: Builder n m => Atom n -> m (Atom n)
clampPositive x = do
  isNegative <- x `ilt` (IdxRepVal 0)
  select isNegative (IdxRepVal 0) x

-- XXX: Be careful if you use this function as an interpretation for
--      IndexAsInt instruction, as for Int and IndexRanges it will
--      generate the same instruction again, potentially leading to an
--      infinite loop.
indexToIntE :: Builder n m => Atom n -> m (Atom n)
indexToIntE = undefined
-- indexToIntE (Con (IntRangeVal _ _ i))     = return i
-- indexToIntE (Con (IndexRangeVal _ _ _ i)) = return i
-- indexToIntE idx = case getType idx of
--   UnitTy  -> return $ IdxRepVal 0
--   PairTy _ rType -> do
--     (lVal, rVal) <- fromPair idx
--     lIdx  <- indexToIntE lVal
--     rIdx  <- indexToIntE rVal
--     rSize <- indexSetSizeE rType
--     imul rSize lIdx >>= iadd rIdx
--   TC (IntRange _ _)     -> indexAsInt idx
--   TC (IndexRange _ _ _) -> indexAsInt idx
--   TC (ParIndexRange _ _ _) -> error "Int casts unsupported on ParIndexRange"
--   RecordTy (NoExt types) -> do
--     sizes <- traverse indexSetSizeE types
--     (strides, _) <- scanM (\sz prev -> (prev,) <$> imul sz prev) sizes (IdxRepVal 1)
--     -- Unpack and sum the strided contributions
--     subindices <- getUnpacked idx
--     subints <- traverse indexToIntE subindices
--     scaled <- mapM (uncurry imul) $ zip (toList strides) subints
--     foldM iadd (IdxRepVal 0) scaled
--   VariantTy (NoExt types) -> do
--     sizes <- traverse indexSetSizeE types
--     (offsets, _) <- scanM (\sz prev -> (prev,) <$> iadd sz prev) sizes (IdxRepVal 0)
--     -- Build and apply a case expression
--     alts <- flip mapM (zip (toList offsets) (toList types)) $
--       \(offset, subty) -> buildNAbs (toNest [Ignore subty]) \[subix] -> do
--         i <- indexToIntE subix
--         iadd offset i
--     emit $ Case idx alts IdxRepTy
--   ty -> error $ "Unexpected type " ++ pprint ty

intToIndexE :: Builder n m => Type n -> Atom n -> m (Atom n)
intToIndexE = undefined
-- intToIndexE (TC con) i = case con of
--   IntRange        low high   -> return $ Con $ IntRangeVal        low high i
--   IndexRange from low high   -> return $ Con $ IndexRangeVal from low high i
--   UnitType                   -> return $ UnitVal
--   PairType a b -> do
--     bSize <- indexSetSizeE b
--     iA <- intToIndexE a =<< idiv i bSize
--     iB <- intToIndexE b =<< irem i bSize
--     return $ PairVal iA iB
--   ParIndexRange _ _ _ -> error "Int casts unsupported on ParIndexRange"
--   _ -> error $ "Unexpected type " ++ pprint con
-- intToIndexE (RecordTy (NoExt types)) i = do
--   sizes <- traverse indexSetSizeE types
--   (strides, _) <- scanM
--     (\sz prev -> do {v <- imul sz prev; return ((prev, v), v)}) sizes (IdxRepVal 1)
--   offsets <- flip mapM (zip (toList types) (toList strides)) $
--     \(ty, (s1, s2)) -> do
--       x <- irem i s2
--       y <- idiv x s1
--       intToIndexE ty y
--   return $ Record (restructure offsets types)
-- intToIndexE (VariantTy (NoExt types)) i = do
--   sizes <- traverse indexSetSizeE types
--   (offsets, _) <- scanM (\sz prev -> (prev,) <$> iadd sz prev) sizes (IdxRepVal 0)
--   let
--     reflect = reflectLabels types
--     -- Find the right index by looping through the possible offsets
--     go prev ((label, repeatNum), ty, offset) = do
--       shifted <- isub i offset
--       -- TODO: This might run intToIndex on negative indices. Fix this!
--       index   <- intToIndexE ty shifted
--       beforeThis <- ilt i offset
--       select beforeThis prev $ Variant (NoExt types) label repeatNum index
--     ((l0, 0), ty0, _):zs = zip3 (toList reflect) (toList types) (toList offsets)
--   start <- Variant (NoExt types) l0 0 <$> intToIndexE ty0 i
--   foldM go start zs
-- intToIndexE ty _ = error $ "Unexpected type " ++ pprint ty










-- === Helpers for function evaluation over fixed-width types ===

applyIntBinOp' :: (forall a. (Eq a, Ord a, Num a, Integral a)
               => (a -> Atom n) -> a -> a -> Atom n)
               -> Atom n -> Atom n -> Atom n
applyIntBinOp' f x y = case (x, y) of
  (PrimCon (Lit (Int64Lit xv)), PrimCon (Lit (Int64Lit yv))) -> f (PrimCon . Lit . Int64Lit) xv yv
  (PrimCon (Lit (Int32Lit xv)), PrimCon (Lit (Int32Lit yv))) -> f (PrimCon . Lit . Int32Lit) xv yv
  (PrimCon (Lit (Word8Lit xv)), PrimCon (Lit (Word8Lit yv))) -> f (PrimCon . Lit . Word8Lit) xv yv
  _ -> error "Expected integer atoms"

applyIntBinOp :: (forall a. (Num a, Integral a) => a -> a -> a) -> Atom n -> Atom n -> Atom n
applyIntBinOp f x y = applyIntBinOp' (\w -> w ... f) x y

applyIntCmpOp :: (forall a. (Eq a, Ord a) => a -> a -> Bool) -> Atom n -> Atom n -> Atom n
applyIntCmpOp f x y = applyIntBinOp' (\_ -> (PrimCon . Lit . Word8Lit . fromIntegral . fromEnum) ... f) x y

applyFloatBinOp :: (forall a. (Num a, Fractional a) => a -> a -> a) -> Atom n -> Atom n -> Atom n
applyFloatBinOp f x y = case (x, y) of
  (PrimCon (Lit (Float64Lit xv)), PrimCon (Lit (Float64Lit yv))) -> PrimCon $ Lit $ Float64Lit $ f xv yv
  (PrimCon (Lit (Float32Lit xv)), PrimCon (Lit (Float32Lit yv))) -> PrimCon $ Lit $ Float32Lit $ f xv yv
  _ -> error "Expected float atoms"

applyFloatUnOp :: (forall a. (Num a, Fractional a) => a -> a) -> Atom n -> Atom n
applyFloatUnOp f x = applyFloatBinOp (\_ -> f) undefined x

getIntLit :: LitVal -> Int
getIntLit l = case l of
  Int64Lit i -> fromIntegral i
  Int32Lit i -> fromIntegral i
  Word8Lit  i -> fromIntegral i
  _ -> error $ "Expected an integer literal"

getFloatLit :: LitVal -> Double
getFloatLit l = case l of
  Float64Lit f -> f
  Float32Lit f -> realToFrac f
  _ -> error $ "Expected a floating-point literal"
