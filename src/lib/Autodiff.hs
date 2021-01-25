-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}

module Autodiff (linearize, transpose) where

import qualified Data.List.NonEmpty as NE
import qualified Data.Set as S

import Preamble
import Base
import Core

-- === core linearization machinery ===

newtype IList a = IList [a]

data LinSubstVal n = LinSubstVal (Atom n) TangentIdx
data TangentIdx = TangentIdx Int | Inactive

type LinSubst         = Subst         LinSubstVal
type DeferredLinSubst = DeferredSubst LinSubstVal

data LinCtx n = LinCtx { _activeEffs :: [Effect n]
                       , derivTypes  :: IList (Type n) }
data TangentCtx n = TangentCtx { activeRefs :: [Name n]
                               , derivVals  :: IList (Atom n) }

-- LinA lets us do the same operations in both the primal and tangent
-- computations, which is common. We can unwrap it to handle them separately.
newtype LinA n m a = LinA { runLinA :: PrimalT n m (a, TangentT n m a) }

type PrimalT  n m = ReaderT (LinCtx     n) m
type TangentT n m = ReaderT (TangentCtx n) m

instance Monad m => Functor     (LinA n m) where fmap = liftA
instance Monad m => Applicative (LinA n m) where
  pure x = LinA $ return (x, return x)
  liftA2 f (LinA m1) (LinA m2) = LinA $ do
    (x1, t1) <- m1
    (x2, t2) <- m2
    return (f x1 x2, liftM2 f t1 t2)

instance FromName LinSubstVal where
  fromName v = LinSubstVal (Var v) Inactive

linearize :: Builder n m => Atom n -> m (Atom n)
linearize ~(Lam _ _ argTy abs) = runPrimalT $
  buildPureLam argTy \x -> do
    Defer subst block <- openAbsLin idSubst abs x
    tangentFunAsLambda $ linearizeBlock subst block

openAbsLin :: Builder n m => LinSubst i n -> Abs e i
           -> Atom n -> PrimalT n m (DeferredLinSubst e n)
openAbsLin = undefined

runPrimalT :: Builder n m => PrimalT n m a -> m a
runPrimalT = undefined


-- Abstract the tangent action as a lambda. Also accepts binders for variables that might
-- be used in the tangent function and abstracts over them (useful when they're easy to
-- reconstruct at application sites).
-- TODO: curried linear functions somehow?
tangentFunAsLambda :: Builder n m => LinA n m (Atom n) -> PrimalT n m (Atom n)
tangentFunAsLambda = undefined
-- tangentFunAsLambda m = do
--   LinCtx _ derivTypes <- ask
--   (ans, tanFun) <- runLinA m
--   liftM (PairVal ans) $
--     buildNaryLam (toList derivTypes) \xs ->
--       runReaderT tanFun $ TangentCtx [] (newIList xs)

-- tangentFunAsLambda :: Builder n m => LinA n m (Atom n) -> PrimalT n m (Atom n)
-- tangentFunAsLambda = undefined
-- tangentFunAsLambda m = do
--   (ans, tanFun) <- runLinA m
--   DerivWrt activeVars effs remats <- ask
--   let hs = map (Bind . (:>TyKind) . effectRegion) effs
--   let rematList = envAsVars remats
--   liftM (PairVal ans) $ lift $ do
--     tanLam <- makeLambdas rematList \rematArgs ->
--       buildNestedLam PureArrow hs \hVals -> do
--         let hVarNames = map (\(Var (v:>_)) -> v) hVals
--         -- TODO: handle exception effect too
--         let effs' = zipWith (\(RWSEffect rws _) v -> RWSEffect rws v) effs hVarNames
--         -- want to use tangents here, not the original binders
--         let regionMap = newEnv (map ((:>()) . effectRegion) effs) hVals
--         -- TODO: Only bind tangents for free variables?
--         let activeVarBinders = map (Bind . fmap (tangentRefRegion regionMap)) $ envAsVars activeVars
--         buildNestedLam PureArrow activeVarBinders \activeVarArgs ->
--           buildLam (Ignore UnitTy) (PlainArrow $ EffectRow (S.fromList effs') Nothing) \_ ->
--             runReaderT tanFun $ TangentEnv
--                  (newEnv (envNames activeVars) activeVarArgs) hVarNames
--                  (newEnv rematList $ fmap Var rematArgs)
--     case rematList of
--       [] -> return tanLam
--       _  -> deShadow tanLam <$> getScope
--   where
--     -- Like buildLam, but doesn't try to deshadow the binder.
--     makeLambda v f = do
--       block <- buildScoped $ do
--         builderExtend $ asFst $ v @> (varType v, LamBound (void PureArrow))
--         f v
--       return $ Lam $ makeAbs (Just v :>) (PureArrow, block)

--     makeLambdas [] f = f []
--     makeLambdas (v:vs) f = makeLambda v \x -> makeLambdas vs \xs -> f (x:xs)

--     -- This doesn't work if we have references inside pairs, tables etc.
--     -- TODO: something more general and cleaner.
--     tangentRefRegion :: Env n (Atom n) -> Type n -> Type n
--     tangentRefRegion regEnv ty = case ty of
--       RefTy ~(Var h) a -> RefTy (regEnv ! h) $ tangentType a
--       _ -> tangentType ty

--     effectRegion eff = case eff of
--       RWSEffect _ h -> h
--       ExceptionEffect -> error "TODO!"
--       IOEffect        -> error "TODO!"

-- Inverse of tangentFunAsLambda. Should be used inside a returned tangent action.
applyLinToTangents :: Builder n m => Atom n -> TangentT n m (Atom n)
applyLinToTangents = undefined
-- -- applyLinToTangents f = do
-- --   TangentEnv{..} <- ask
-- --   let hs' = map (Var . (`Occ` TyKind)) activeRefs
-- --   let tangents = fmap snd $ envPairs $ tangentVals
-- --   let args = (toList rematVals) ++ hs' ++ tangents ++ [UnitVal]
-- --   naryApp f args








-- === all the linearization rules ===

linearizeAtom :: Builder n m => LinSubst i n -> Atom i -> LinA n m (Atom n)
linearizeAtom subst atom = case atom of
  Var v -> do
    let LinSubstVal x tangentIdx = lookupSubst v subst
    case tangentIdx of
      Inactive -> emitWithZero
      TangentIdx idx -> LinA $ return (x, lookupDerivVar idx)
  PrimCon con -> linearizePrimCon subst con
--   TabVal (i,ty) body -> LinA $ do
--     wrt <- ask
--     return (atom, buildLam ty TabArrow \i' ->
--                     rematPrimal wrt $ linearizeBlock (i@>i') body)
--   Record elems    -> Record <$> traverse linearizeAtom elems
--   Variant t l i e -> Variant t l i <$> linearizeAtom e
  Con _ _         -> notImplemented  -- Need to synthesize or look up a tangent ADT
  LabeledRow _    -> emitWithZero
  RecordTy _      -> emitWithZero
  VariantTy _     -> emitWithZero
  Pi _ _ _ _      -> emitWithZero
  PrimTC _        -> emitWithZero
  Eff _           -> emitWithZero
  ProjectElt idxs v -> getProjection (toList idxs) <$> linearizeAtom subst (Var v)
  -- Those should be gone after simplification
  Lam _ _ _ _     -> error "Unexpected non-table lambda"
  ACase _ _ _     -> error "Unexpected ACase"
  DataConRef _ _ _ -> error "Unexpected ref"
  BoxedRef _ _ _ _ -> error "Unexpected ref"
  where emitWithZero = withZeroTangentSubst subst atom


linearizeBlock :: Builder n m => LinSubst i n -> Block i -> LinA n m (Atom n)
linearizeBlock = undefined
-- linearizeBlock env (Block decls result) = case decls of
--   Empty -> linearizeExpr env result
--   Nest (Let _ b expr) rest -> LinA do
--     let body = Block rest result
--     -- Don't linearize expressions with no free active variables.
--     -- Technically, we could do this and later run the code through a simplification
--     -- pass that would eliminate a bunch of multiplications with zeros, but this seems
--     -- simpler to do for now.
--     freeAtoms <- traverse (substBuilder env . Var) $ bindingsAsVars $ freeVars expr
--     varsAreActive <- traverse isActive $ bindingsAsVars $ foldMap freeVars freeAtoms
--     if any id varsAreActive
--       then do
--         (x, boundLin) <- runLinA $ linearizeExpr env expr
--         ~(Var v) <- emit $ Atom x
--         -- NB: This can still overestimate the set of active variables (e.g.
--         --     when multiple values are returned from a case statement).
--         -- Don't mark variables with trivial tangent types as active. This lets us avoid
--         -- pretending that we're differentiating wrt e.g. equality tests which yield discrete results.
--         -- TODO: This check might fail if the result type does not have a defined tangent type.
--         --       For example, what if it's a reference? Some of those should be marked as active
--         --       variables, but I don't think that we want to define them to have tangents.
--         --       We should delete this check, but to do that we would have to support differentiation
--         --       through case statements with active scrutinees.
--         let vIsTrivial = isSingletonType $ tangentType $ varType v
--         let nontrivialVs = if vIsTrivial then [] else [v]
--         (ans, bodyLin) <- extendWrt nontrivialVs [] $ runLinA $
--           linearizeBlock (env <> b @> Var v) body
--         return (ans, do
--           t <- boundLin
--           -- Tangent environment needs to be synced between the primal and tangent
--           -- monads (tangentFunAsLambda and applyLinToTangents need that).
--           let nontrivialTs = if vIsTrivial then [] else [t]
--           extendTangentEnv (newEnv nontrivialVs nontrivialTs) [] bodyLin)
--       else do
--         expr' <- substBuilder env expr
--         x <- emit expr'
--         runLinA $ linearizeBlock (env <> b @> x) body

linearizeExpr :: Builder n m
               => LinSubst i n -> Expr i -> LinA n m (Atom n)
linearizeExpr subst expr = case expr of
  Hof  e        -> linearizeHof subst e
  -- Case e alts _ -> LinA $ do
  --   e' <- substBuilder subst e
  --   hasActiveScrutinee <- any id <$> (mapM isActive $ bindingsAsVars $ freeVars e')
  --   case hasActiveScrutinee of
  --     True  -> notImplemented
  --     False -> do
  --       alts' <- traverse linearizeInactiveAlt alts
  --       result <- emit $ Case e' alts' $ (\((Abs _ body):_) -> getType body) alts'
  --       (ans, linLam) <- fromPair result
  --       return (ans, applyLinToTangents linLam)
  --   where
  --     linearizeInactiveAlt (Abs bs body) = do
  --       Abs bs' HUnit <- substBuilder subst $ Abs bs HUnit
  --       buildNAbs bs' \xs -> tangentFunAsLambda $
  --         linearizeBlock (subst <> newSubst (fromNest bs) xs) body
    -- runLinA $ case expr of
  TabGet x i -> (TabGet <$> linearizeAtom subst x <*> pureSubst subst i) `bindLin` emit
  Op   e     -> linearizeOp   subst e
  Atom e     -> linearizeAtom subst e
  App _ _ _  -> error "Unexpected non-table application"
  Case _ _ _ -> error "Case should be handled above"

linearizeOp :: Builder n m
            => LinSubst i n -> PrimOp (Atom i) -> LinA n m (Atom n)
linearizeOp subst op = case op of
  ScalarUnOp  uop x   -> linearizeUnOp  subst uop x
  ScalarBinOp bop x y -> linearizeBinOp subst bop x y
  -- PrimEffect refArg (MExtend ~(LamVal b body)) -> LinA $ do
  --   (primalRef, mkTangentRef) <- runLinA $ la refArg
  --   (primalUpdate, mkTangentUpdate) <-
  --     buildLamAux (binderType b) (const $ return PureArrow) \x@(Var v) ->
  --       extendWrt [v] [] $ runLinA $ linearizeBlock (b @> x) body
  --   let LamVal (primalStateVar, primalStateTy) _ = primalUpdate
  --   ans <- emitOp $ PrimEffect primalRef $ MExtend primalUpdate
  --   return (ans, do
  --     tangentRef <- mkTangentRef
  --     -- TODO: Assert that tangent update doesn't close over anything?
  --     --       (maybe by being more precise with namespace types?)
  --     tangentUpdate <- buildLam (tangentType primalStateTy) PureArrow \tx ->
  --       extendTangentEnv (primalStateVar @> tx) [] $ mkTangentUpdate
  --     emitOp $ PrimEffect tangentRef $ MExtend tangentUpdate)
  PrimEffect refArg m ->
    liftA2 PrimEffect (la refArg)
      (case m of
         MAsk      -> pure MAsk
         MExtend _ -> error "Unhandled MExtend"
         MGet      -> pure MGet
         MPut    x -> liftA MPut $ la x) `bindLin` emitOp
  IndexRef ref i -> (IndexRef <$> la ref <*> ps i       ) `bindLin` emitOp
  FstRef   ref   -> (FstRef   <$> la ref                ) `bindLin` emitOp
  SndRef   ref   -> (SndRef   <$> la ref                ) `bindLin` emitOp
  Select p t f   -> (Select   <$> ps p <*> la t <*> la f) `bindLin` emitOp
  -- -- XXX: This assumes that pointers are always constants
  -- PtrLoad _              -> emitWithZero
  PtrStore _ _           -> emitDiscrete
  PtrOffset _ _          -> emitDiscrete
  IOAlloc _ _            -> emitDiscrete
  IOFree _               -> emitDiscrete
  TabCon ty xs           -> (TabCon <$> ps ty <*> traverse la xs) `bindLin` emitOp
  Inject _               -> emitDiscrete
  SliceOffset _ _        -> emitDiscrete
  SliceCurry  _ _        -> emitDiscrete
  VectorBinOp _ _ _      -> notImplemented
  VectorPack  vals       -> (VectorPack  <$> traverse la vals) `bindLin` emitOp
  VectorIndex v i        -> (VectorIndex <$> la v <*> ps i   ) `bindLin` emitOp
  UnsafeFromOrdinal _ _  -> emitDiscrete
  ToOrdinal _            -> emitDiscrete
  IdxSetSize _           -> emitDiscrete
  -- ThrowError _           -> emitWithZero
  DataConTag _           -> emitDiscrete
  ToEnum _ _             -> emitDiscrete
  -- CastOp t v             -> do
  --   if tangentType vt == vt && tangentType t == t
  --     then (CastOp t <$> la v) `bindLin` emitOp
  --     else castWithTrivial
  --   where
  --     vt = getType v
  --     castWithTrivial = LinA $ do
  --       (x, xt) <- runLinA $ la v
  --       let yt = case (tangentType vt, tangentType t) of
  --             (_     , UnitTy) -> UnitVal
  --             (UnitTy, tt    ) -> zeroAt tt
  --             _                -> error "Expected at least one side of the CastOp to have a trivial tangent type"
  --       (emitOp $ CastOp t x) <$$> (,xt >> return yt)
  RecordCons   vs r      -> (RecordCons   <$> traverse la vs <*> la r) `bindLin` emitOp
  RecordSplit  vs r      -> (RecordSplit  <$> traverse la vs <*> la r) `bindLin` emitOp
  VariantLift  ts v      -> (VariantLift  <$> traverse ps ts <*> la v) `bindLin` emitOp
  VariantSplit ts v      -> (VariantSplit <$> traverse ps ts <*> la v) `bindLin` emitOp
  FFICall _ _ _          -> error $ "Can't differentiate through an FFI call"
  ThrowException _       -> notImplemented
  where
    emitDiscrete = LinA $ do
      op' <- traverse (applyLinSubst subst) op
      runLinA $ emitDiscreteOp op'
    ps = pureSubst     subst
    la = linearizeAtom subst
    -- emitWithZero :: LinA n (Atom n)
    -- emitWithZero = LinA $ withZeroTangent <$> emitOp op

linearizeUnOp :: Builder n m => LinSubst i n -> UnOp -> Atom i -> LinA n m (Atom n)
linearizeUnOp subst op x' = LinA $ do
  (x, tx) <- runLinA $ linearizeAtom subst x'
  let primalOp = ScalarUnOp op x
  case op of
    Exp    -> do
      y <- emitUnOp Exp x
      return (y, bindM2 mul tx (pure y))
    Exp2   -> notImplemented
    Log    -> emitUnOp Log x <$$> (,tx >>= (`div'` x))
    Log2   -> notImplemented
    Log10  -> notImplemented
    Log1p  -> notImplemented
    Sin    -> emitUnOp Sin x <$$> (,bindM2 mul tx $ emitUnOp Cos x)
    Cos    -> emitUnOp Cos x <$$> (,bindM2 mul tx $ neg =<< emitUnOp Sin x)
    Tan    -> notImplemented
    Sqrt   -> do
      y <- emitUnOp Sqrt x
      return (y, do y2 <- 2 `fLitLike` y >>= mul y
                    tx' <- tx
                    div' tx' y2)
    Floor  -> runLinA $ emitDiscreteOp primalOp
    Ceil   -> runLinA $ emitDiscreteOp primalOp
    Round  -> runLinA $ emitDiscreteOp primalOp
    LGamma -> notImplemented
    FNeg   -> neg x <$$> (,neg =<< tx)
    BNot   -> runLinA $ emitDiscreteOp primalOp

linearizeBinOp :: Builder n m => LinSubst i n -> BinOp -> Atom i -> Atom i
               -> LinA n m (Atom n)
linearizeBinOp subst op x' y' = LinA $ do
  (x, tx) <- runLinA $ linearizeAtom subst x'
  (y, ty) <- runLinA $ linearizeAtom subst y'
  let primalOp = ScalarBinOp op x y
  runLinA $ case op of
    IAdd   -> emitDiscreteOp primalOp
    ISub   -> emitDiscreteOp primalOp
    IMul   -> emitDiscreteOp primalOp
    IDiv   -> emitDiscreteOp primalOp
    IRem   -> emitDiscreteOp primalOp
    ICmp _ -> emitDiscreteOp primalOp
    FAdd   -> LinA $ add x y  <$$> (,bindM2 add tx ty)
    FSub   -> LinA $ sub x y  <$$> (,bindM2 sub tx ty)
    FMul   -> LinA $ mul x y  <$$> (,bindM2 add (bindM2 mul (pure x) ty)
                                                (bindM2 mul tx (pure y)))
    FDiv   -> LinA $ div' x y <$$>
        (,do
             tx' <- bindM2 div' tx (pure y)
             ty' <- bindM2 div' (bindM2 mul (pure x) ty) (mul y y)
             sub tx' ty')
    FPow   -> LinA $ (emitOp $ ScalarBinOp FPow x y) <$$>
        (,do
             c <- fpow x =<< sub y =<< 1.0 `fLitLike` y
             tx' <- bindM2 mul tx (pure y)
             ty' <- bindM2 mul (bindM2 mul (pure x) ty) (flog x)
             mul c =<< add tx' ty')
    FCmp _ -> emitDiscreteOp primalOp
    BAnd   -> emitDiscreteOp primalOp
    BOr    -> emitDiscreteOp primalOp
    BShL   -> emitDiscreteOp primalOp
    BShR   -> emitDiscreteOp primalOp


emitDiscreteOp :: Builder n m => PrimOp (Atom n) -> LinA n m (Atom n)
emitDiscreteOp op = LinA $ do
  ans <- emitOp op
  runLinA $ withZeroTangent ans

-- Here, we want to take advantage of simplification's automatic desugaring of
-- Hofs that return functions into Hofs that return residual values, so the where
-- part implements functions that convert the TangentM actions into lambdas that
-- abstract over the whole tangent state.
linearizeHof :: Builder n m => LinSubst i n -> PrimHof (Atom i) -> LinA n m (Atom n)
linearizeHof subst hof = case hof of
  For ~(RegularFor d) ~(LamVal iTy' abs) -> LinA $ do
    iTy <- applyLinSubst subst iTy'
    (ans, linTab) <- unzipTab =<< buildFor d iTy \i -> do
                       Defer subst' body <- openAbsLin subst abs i
                       tangentFunAsLambda $ linearizeBlock subst' body
    return (ans, buildFor d iTy \i -> tabGet linTab i >>= applyLinToTangents)
  Tile _ _ _        -> notImplemented
  -- RunWriter bm ~lam@(BinaryFunVal _ refBinder _ _) -> LinA $ do
  --   unless (checkZeroPlusFloatMonoid bm) $
  --     error "AD of Accum effect only supported when the base monoid is (0, +) on Float"
  --   bm' <- traverse (substBuilder subst) bm
  --   ~(RefTy _ accTy) <- substBuilder subst $ binderType refBinder
  --   linearizeEff subst lam Writer (RunWriter bm') (emitRunWriter accTy bm')

  -- RunReader r ~(RWSActionVal action) -> LinA $ do
  --   (r', rLin) <- runLinA <$> linearizeAtom subst r





--   (lam', ref) <- linearizeEffectFun subst eff lam
--   -- The reader effect doesn't return any additional values
--   (ans, linBody) <- case eff of
--       Reader -> fromPair =<< emit (Hof $ primalHofCon lam')
--       _      -> do
--         (ansLin, w)    <- fromPair =<< emit (Hof $ primalHofCon lam')
--         (ans, linBody) <- fromPair ansLin
--         return (PairVal ans w, linBody)
--   let lin = tangentEmitter \ref'@(Var (Occ _ (RefTy (Var (Occ h _)) _))) -> do
--               extendTangentEnv (ref @> ref') [h] $ applyLinToTangents linBody
--   return (ans, lin)



    -- linearizeEff subst action Reader (RunReader val') \f ->
    --   mkLinInit >>= emitRunReader `flip` f

--   RunState val lam -> LinA $ do
--     (val', mkLinInit) <- runLinA <$> linearizeAtom =<< substBuilder subst val
--     linearizeEff subst lam State (RunState val') \f ->
--       mkLinInit >>= emitRunState `flip` f
  RunIO _ -> error "Unexpected IO"
  -- TODO: Consider providing an upper bound for the number of while iterations as a hint.
  --       In the current form the best we can do is try to use some dynamically growing lists,
  --       but that won't work on the GPU.
  While _          -> notImplemented
  CatchException _ -> notImplemented
  Linearize _ -> error "Unexpected linearization"
  Transpose _ -> error "Unexpected transposition"
  PTileReduce _ _ _ -> error "Unexpected PTileReduce"

-- linearizeEff :: Builder n m => Subst i n -> Atom i -> RWS
--              -> (Atom n -> Hof n)
--              -> ((Atom n -> TangentM o (Atom o)) -> TangentM o (Atom o))
--              -> PrimalM o (Atom o, TangentM o (Atom o))
-- linearizeEff = undefined
-- linearizeEff subst lam eff primalHofCon tangentEmitter = do
--   (lam', ref) <- linearizeEffectFun subst eff lam
--   -- The reader effect doesn't return any additional values
--   (ans, linBody) <- case eff of
--       Reader -> fromPair =<< emit (Hof $ primalHofCon lam')
--       _      -> do
--         (ansLin, w)    <- fromPair =<< emit (Hof $ primalHofCon lam')
--         (ans, linBody) <- fromPair ansLin
--         return (PairVal ans w, linBody)
--   let lin = tangentEmitter \ref'@(Var (Occ _ (RefTy (Var (Occ h _)) _))) -> do
--               extendTangentEnv (ref @> ref') [h] $ applyLinToTangents linBody
--   return (ans, lin)

-- linearizeEffectFun :: Subst i o -> RWS -> Atom i -> PrimalM o (Atom o, Name o)
-- linearizeEffectFun = undefined
-- -- linearizeEffectFun env rws ~(BinaryFunVal (h,hTy) (ref,refTy) eff body) = do
-- --   hTy' <- substBuilder subst hTy
-- --   buildLamAux hTy' (const $ return PureArrow) \h''@(Var hVar) -> do
-- --     let subst' = subst <> h@>h''
-- --     eff' <- substBuilder subst' eff
-- --     refTy' <- substBuilder subst' refTy
-- --     buildLamAux refTy' (const $ return $ PlainArrow eff')
-- --       \ref''@(Var refVar) ->
-- --         extendWrt [refVar] [RWSEffect rws (varName hVar)] $
-- --           (,refVar) <$> (tangentFunAsLambda $ linearizeBlock (subst' <> ref@>ref'') body)

linearizePrimCon :: Builder n m => LinSubst i n -> PrimCon (Atom i) -> LinA n  m (Atom n)
linearizePrimCon subst con = case con of
  Lit _                 -> emitWithZero
  PairCon x y           -> PairVal <$> linearizeAtom subst x <*> linearizeAtom subst y
  UnitCon               -> emitWithZero
  SumAsProd ty tg elems -> PrimCon <$> (SumAsProd <$>
    pureSubst subst ty <*>
    pureSubst subst tg <*>
    traverse (traverse (linearizeAtom subst)) elems)
  IntRangeVal _ _ _     -> emitWithZero
  IndexRangeVal _ _ _ _ -> emitWithZero
  IndexSliceVal _ _ _   -> emitWithZero
  BaseTypeRef _  -> error "Unexpected ref"
  TabRef _       -> error "Unexpected ref"
  ConRef _       -> error "Unexpected ref"
  RecordRef _    -> error "Unexpected ref"
  ParIndexCon   _ _ -> error "Unexpected ParIndexCon"
  ClassDictHole _ _ -> error "Unexpected ClassDictHole"
  where emitWithZero = withZeroTangentSubst subst (PrimCon con)

applyLinSubst :: (MaySubstAtoms e, HasScope n m) => LinSubst i n -> e i -> m (e n)
applyLinSubst = undefined

pureSubst ::(MaySubstAtoms e, HasScope n m) => LinSubst i n -> e i -> LinA n m (e n) 
pureSubst subst x = LinA do
  x' <- applyLinSubst subst x
  return (x', return x')

withZeroTangentSubst :: Builder n m => LinSubst i n -> Atom i -> LinA n m (Atom n)
withZeroTangentSubst = undefined

withZeroTangent :: Builder n m => Atom n -> LinA n m (Atom n)
withZeroTangent = undefined

-- withZeroTangent :: Builder n m => Atom n -> PirimalT n m (Atom n, TangentT n m (Atom n))

-- withZeroTangent :: Builder n m => Atom n -> PrimalT n m (Atom n, TangentT n m (Atom n))
-- withZeroTangent x = undefined
-- withZeroTangent x = (x, return $ zeroAt (tangentType (getType x)))

tangentType :: Type n -> Type n
tangentType ty = case ty of
  RecordTy (NoExt items) -> RecordTy $ NoExt $ fmap tangentType items
  Con _ _ -> notImplemented -- Need to synthesize or look up a tangent ADT
  n :==> a -> n :==> tangentType a
  PrimTC con    -> case con of
    BaseType (Scalar Float64Type) -> PrimTC con
    BaseType (Scalar Float32Type) -> PrimTC con
    BaseType (Vector Float64Type) -> PrimTC con
    BaseType (Vector Float32Type) -> PrimTC con
    BaseType   _                  -> UnitTy
    IntRange   _ _                -> UnitTy
    IndexRange _ _ _              -> UnitTy
    IndexSlice _ _                -> UnitTy
    UnitType                      -> UnitTy
    PairType a b                  -> PairTy (tangentType a) (tangentType b)
    -- XXX: This assumes that arrays are always constants.
    _ -> unsupported
  _ -> unsupported
  where unsupported = error $ "Can't differentiate wrt type " ++ pprint ty

isTrivialForAD :: DefReader n m => Expr n -> m Bool
isTrivialForAD = undefined
-- isTrivialForAD expr = isSingletonType tangentTy && exprEffs expr == mempty
--   where tangentTy = tangentType $ getType expr

bindLin :: Builder n m => LinA n m a -> (a -> m b) -> LinA n m b
bindLin (LinA m) f = LinA $ do
  (e, t) <- m
  x <- lift $ f e
  return (x, t >>= (lift . f))

lookupDerivVar :: Builder n m => Int -> TangentT n m (Atom n)
lookupDerivVar = undefined

-- isActive :: Builder n m => Name n -> PrimalT n m Bool
-- isActive v = asks ((v `isin`) . activeVars)

-- extendWrt :: [Name n] -> [Effect n] -> PrimalM n a -> PrimalM n a
-- extendWrt = undefined
-- -- extendWrt active effs m = local update m
-- --   where update (DerivWrt active' effs' remats) = DerivWrt (active' <> foldMap varAsEnv active) (effs' <> effs) remats

-- extendTangentEnv :: Subst n n -> [Name n] -> TangentM n a -> TangentM n a
-- extendTangentEnv tv effs m = local update m
--   where update (TangentEnv tv' effs' remats) = TangentEnv (tv' <> tv) (effs' <> effs) remats

notImplemented :: HasCallStack => a
notImplemented = error "Not implemented"

-- === transposition ===

-- `linRefs` contains all linear variables with non-reference types. It maps
-- them to references to their cotangent regions. As an optimization, we do not
-- allocate the regions for trivial vector spaces and in this case the mapping
-- points to Nothing (but the membership still implies that the name is linear).
--
-- `linRefSubst` contains all linear variables with reference types. It maps
-- them to references to their cotangent regions.
--
-- `linRegions` contains all names of linear regions that appear in the original
-- program.
--
-- `nonlinSubst` is a substitution that should be applied to any non-linear atom
-- that is to be emitted into the transposed program. It replaces the original names
-- of non-linear local variables with their instances in the transposed program.

-- data TransposeEnv = TransposeEnv { linRefs        :: Env (Maybe Atom)
--                                  , linRefSubst    :: SubstEnv
--                                  , linRegions     :: Env ()
--                                  , nonlinSubst    :: SubstEnv
--                                  }

-- instance Semigroup TransposeEnv where
--   (TransposeEnv x y z w) <> (TransposeEnv x' y' z' w') =
--     TransposeEnv (x <> x') (y <> y') (z <> z') (w <> w')

-- instance Monoid TransposeEnv where
--   mempty = TransposeEnv mempty mempty mempty mempty

-- type TransposeM a = ReaderT TransposeEnv Builder a

transpose :: Scope n -> Atom n -> Atom n
transpose = undefined
-- transpose scope ~(Lam (Abs b (_, block))) = fst $ flip runBuilder scope $ do
--   buildLam (Bind $ "ct" :> getType block) LinArrow \ct -> do
--     snd <$> (flip runReaderT mempty $ withLinVar b $ transposeBlock block ct)

-- transposeBlock :: Block -> Atom -> TransposeM ()
-- transposeBlock (Block decls result) ct = case decls of
--   Empty -> transposeExpr result ct
--   Nest decl rest -> case decl of
--     (Let _ b expr) -> transposeBinding b expr
--     where
--       body = Block rest result
--       transposeBinding b expr = do
--         isLinearExpr <- (||) <$> isLinEff (exprEffs expr) <*> isLin expr
--         if isLinearExpr
--           then do
--             cts <- withLinVars [b] $ transposeBlock body ct
--             transposeExpr expr $ head cts
--           else do
--             expr' <- substNonlin expr
--             x <- emit expr'
--             localNonlinSubst (b @> x) $ transposeBlock body ct

--       withLinVars :: [Binder] -> TransposeM () -> TransposeM [Atom]
--       withLinVars [] m     = m >> return []
--       withLinVars (b:bs) m = uncurry (flip (:)) <$> (withLinVar b $ withLinVars bs m)

-- transposeExpr :: Expr -> Atom -> TransposeM ()
-- transposeExpr expr ct = case expr of
--   App x i -> case getType x of
--     TabTy _ _ -> do
--       i' <- substNonlin i
--       ref <- traverse (\ref -> emitOp $ IndexRef ref i') =<< linAtomRef x
--       emitCTToRef ref ct
--     _ -> error $ "shouldn't have non-table app left"
--   Hof hof       -> transposeHof hof ct
--   Op op         -> transposeOp op ct
--   Atom atom     -> transposeAtom atom ct
--   Case e alts _ -> do
--     linearScrutinee <- isLin e
--     case linearScrutinee of
--       True  -> notImplemented
--       False -> do
--         alts' <- traverse transposeNonlinAlt alts
--         e' <- substNonlin e
--         void $ emit $ Case e' alts' UnitTy
--   where
--     transposeNonlinAlt (Abs bs body) =
--       buildNAbs bs \xs -> do
--         localNonlinSubst (newEnv bs xs) $ transposeBlock body ct
--         return UnitVal

-- transposeOp :: Op -> Atom -> TransposeM ()
-- transposeOp op ct = case op of
--   ScalarUnOp  FNeg x    -> transposeAtom x =<< neg ct
--   ScalarUnOp  _    _    -> notLinear
--   ScalarBinOp FAdd x y  -> transposeAtom x ct >> transposeAtom y ct
--   ScalarBinOp FSub x y  -> transposeAtom x ct >> (transposeAtom y =<< neg ct)
--   ScalarBinOp FMul x y  -> do
--     xLin <- isLin x
--     if xLin
--       then transposeAtom x =<< mul ct =<< substNonlin y
--       else transposeAtom y =<< mul ct =<< substNonlin x
--   ScalarBinOp FDiv x y  -> transposeAtom x =<< div' ct =<< substNonlin y
--   ScalarBinOp _    _ _  -> notLinear
--   PrimEffect refArg m   -> do
--     refArg' <- substTranspose linRefSubst refArg
--     let emitEff = emitOp . PrimEffect refArg'
--     case m of
--       MAsk      -> void $ emitEff . MExtend =<< (updateAddAt ct)
--       -- XXX: This assumes that the update function uses a tangent (0, +) monoid,
--       --      which is why we can ignore the binder (we even can't; we only have a
--       --      reader reference!). This should have been checked in the transposeHof
--       --      rule for RunWriter.
--       MExtend ~(LamVal _ body) -> transposeBlock body =<< emitEff MAsk
--       -- TODO: Do something more efficient for state. We should be able
--       --       to do in-place addition, just like we do for the Writer effect.
--       MGet      -> void $ emitEff . MPut =<< addTangent ct =<< emitEff MGet
--       MPut  x   -> do
--         transposeAtom x =<< emitEff MGet
--         void $ emitEff $ MPut $ zeroAt $ getType x
--   TabCon ~(TabTy b _) es -> forM_ (enumerate es) \(i, e) -> do
--     transposeAtom e =<< tabGet ct =<< intToIndexE (binderType b) (IdxRepVal $ fromIntegral i)
--   IndexRef     _ _      -> notImplemented
--   FstRef       _        -> notImplemented
--   SndRef       _        -> notImplemented
--   Select       _ _ _    -> notImplemented
--   VectorBinOp  _ _ _    -> notImplemented
--   VectorPack   _        -> notImplemented
--   VectorIndex  _ _      -> notImplemented
--   CastOp       _ _      -> notImplemented
--   RecordCons   _ _      -> notImplemented
--   RecordSplit  _ _      -> notImplemented
--   VariantLift  _ _      -> notImplemented
--   VariantSplit _ _      -> notImplemented
--   PtrStore _ _          -> notLinear
--   PtrLoad    _          -> notLinear
--   PtrOffset _ _         -> notLinear
--   IOAlloc _ _           -> notLinear
--   IOFree _              -> notLinear
--   Inject       _        -> notLinear
--   SliceOffset  _ _      -> notLinear
--   SliceCurry   _ _      -> notLinear
--   UnsafeFromOrdinal _ _ -> notLinear
--   ToOrdinal    _        -> notLinear
--   IdxSetSize   _        -> notLinear
--   ThrowError   _        -> notLinear
--   FFICall _ _ _         -> notLinear
--   DataConTag _          -> notLinear
--   ToEnum _ _            -> notLinear
--   ThrowException _      -> notLinear
--   where
--     -- Both nonlinear operations and operations on discrete types, where linearity doesn't make sense
--     notLinear = error $ "Can't transpose a non-linear operation: " ++ pprint op

-- linAtomRef :: Atom -> TransposeM (Maybe Atom)
-- linAtomRef (Var x) = do
--   refs <- asks linRefs
--   case envLookup refs x of
--     Just ref -> return ref
--     _ -> error $ "Not a linear var: " ++ pprint (Var x)
-- linAtomRef (ProjectElt (i NE.:| is) x) =
--   let subproj = case NE.nonEmpty is of
--         Just is' -> ProjectElt is' x
--         Nothing -> Var x
--   in case getType subproj of
--     PairTy _ _ -> do
--       ref <- linAtomRef subproj
--       (traverse $ emitOp . getter) ref
--       where getter = case i of 0 -> FstRef
--                                1 -> SndRef
--                                _ -> error "bad pair projection"
--     ty -> error $ "Projecting references not implemented for type " <> pprint ty
-- linAtomRef a = error $ "Not a linear var: " ++ pprint a

-- transposeHof :: Hof -> Atom -> TransposeM ()
-- transposeHof hof ct = case hof of
--   For ~(RegularFor d) ~(Lam (Abs b (_, body))) ->
--     void $ buildFor (flipDir d) b \i -> do
--       ct' <- tabGet ct i
--       localNonlinSubst (b@>i) $ transposeBlock body ct'
--       return UnitVal
--     where flipDir dir = case dir of Fwd -> Rev; Rev -> Fwd
--   RunReader r ~(BinaryFunVal (Bind (h:>_)) b _ body) -> do
--     let RefTy _ valTy = binderType b
--     let baseTy = getBaseMonoidType valTy
--     baseMonoid <- tangentBaseMonoidFor baseTy
--     (_, ctr) <- (fromPair =<<) $ emitRunWriter "w" valTy baseMonoid \ref -> do
--       localLinRegion h $ localLinRefSubst (b@>ref) $ transposeBlock body ct
--       return UnitVal
--     transposeAtom r ctr
--   RunWriter bm ~(BinaryFunVal (Bind (h:>_)) b _ body) -> do
--     unless (checkZeroPlusFloatMonoid bm) $
--       error "AD of Accum effect only supported when the base monoid is (0, +) on Float"
--     (ctBody, ctEff) <- fromPair ct
--     void $ emitRunReader "r" ctEff \ref -> do
--       localLinRegion h $ localLinRefSubst (b@>ref) $ transposeBlock body ctBody
--       return UnitVal
--   RunState s ~(BinaryFunVal (Bind (h:>_)) b _ body) -> do
--     (ctBody, ctState) <- fromPair ct
--     (_, cts) <- (fromPair =<<) $ emitRunState "s" ctState \ref -> do
--       localLinRegion h $ localLinRefSubst (b@>ref) $ transposeBlock body ctBody
--       return UnitVal
--     transposeAtom s cts
--   Tile      _ _ _  -> notImplemented
--   While         _  -> notImplemented
--   RunIO _          -> notImplemented
--   CatchException _ -> notImplemented
--   Linearize     _  -> error "Unexpected linearization"
--   Transpose     _  -> error "Unexpected transposition"
--   PTileReduce _ _ _  -> error "Unexpected PTileReduce"

-- transposeAtom :: Atom -> Atom -> TransposeM ()
-- transposeAtom atom ct = case atom of
--   Var v -> do
--     refs <- asks linRefs
--     case envLookup refs v of
--       Just ref -> emitCTToRef ref ct
--       Nothing  -> return ()
--   Con con         -> transposeCon con ct
--   Record  e       -> void $ zipWithT transposeAtom e =<< getUnpacked ct
--   DataCon _ _ _ e -> void $ zipWithT transposeAtom e =<< getUnpacked ct
--   Variant _ _ _ _ -> notImplemented
--   TabVal b body   ->
--     void $ buildFor Fwd b \i -> do
--       ct' <- tabGet ct i
--       localNonlinSubst (b@>i) $ transposeBlock body ct'
--       return UnitVal
--   Lam _           -> notTangent
--   TypeCon _ _     -> notTangent
--   LabeledRow _    -> notTangent
--   RecordTy _      -> notTangent
--   VariantTy _     -> notTangent
--   Pi _            -> notTangent
--   TC _            -> notTangent
--   Eff _           -> notTangent
--   ACase _ _ _     -> error "Unexpected ACase"
--   DataConRef _ _ _ -> error "Unexpected ref"
--   BoxedRef _ _ _ _ -> error "Unexpected ref"
--   ProjectElt _ v -> do
--     lin <- isLin $ Var v
--     when lin $ flip emitCTToRef ct =<< linAtomRef atom
--   where notTangent = error $ "Not a tangent atom: " ++ pprint atom

-- transposeCon :: Con -> Atom -> TransposeM ()
-- transposeCon con ct = case con of
--   Lit _             -> return ()
--   UnitCon           -> return ()
--   PairCon x y       -> do
--     getFst ct >>= transposeAtom x
--     getSnd ct >>= transposeAtom y
--   SumAsProd _ _ _   -> notImplemented
--   ClassDictHole _ _ -> notTangent
--   IntRangeVal _ _ _     -> notTangent
--   IndexRangeVal _ _ _ _ -> notTangent
--   IndexSliceVal _ _ _   -> notTangent
--   ParIndexCon _ _       -> notTangent
--   BaseTypeRef _  -> notTangent
--   TabRef _       -> notTangent
--   ConRef _       -> notTangent
--   RecordRef _    -> notTangent
--   where notTangent = error $ "Not a tangent atom: " ++ pprint (Con con)

-- freeLinVars :: HasVars a => a -> TransposeM [Var]
-- freeLinVars x = do
--   refs <- asks linRefs
--   return $ bindingsAsVars $ envIntersect refs (freeVars x)

-- isLin :: HasVars a => a -> TransposeM Bool
-- isLin x = not . null <$> freeLinVars x

-- isLinEff :: EffectRow -> TransposeM Bool
-- isLinEff (EffectRow effs Nothing) = do
--   regions <- asks linRegions
--   return $ not $ null $ effRegions `envIntersect` regions
--   where effRegions = freeVars $ toList effs
-- isLinEff _ = error "Can't transpose polymorphic effects"

-- emitCTToRef :: Maybe Atom -> Atom -> TransposeM ()
-- emitCTToRef mref ct = case mref of
--   Just ref -> void . emitOp . PrimEffect ref . MExtend =<< updateAddAt ct
--   Nothing  -> return ()

-- substTranspose :: Subst a => (TransposeEnv -> SubstEnv) -> a -> TransposeM a
-- substTranspose sel x = do
--   env <- asks sel
--   scope <- getScope
--   return $ subst (env, scope) x

-- substNonlin :: Subst a => a -> TransposeM a
-- substNonlin = substTranspose nonlinSubst

-- withLinVar :: Binder -> TransposeM a -> TransposeM (a, Atom)
-- withLinVar b body = case singletonTypeVal (binderType b) of
--   Nothing -> flip evalStateT Nothing $ do
--     let accTy = binderType b
--     let baseTy = getBaseMonoidType accTy
--     baseMonoid <- tangentBaseMonoidFor baseTy
--     ans <- emitRunWriter "ref" accTy baseMonoid \ref -> do
--       lift (localLinRef (b@>Just ref) body) >>= put . Just >> return UnitVal
--     (,) <$> (fromJust <$> get) <*> (getSnd ans)
--   Just x -> (,x) <$> (localLinRef (b@>Nothing) body)  -- optimization to avoid accumulating into unit

-- localLinRef :: Env (Maybe Atom) -> TransposeM a -> TransposeM a
-- localLinRef refs = local (<> mempty { linRefs = refs })

-- localLinRegion :: Name -> TransposeM a -> TransposeM a
-- localLinRegion h = local (<> mempty { linRegions = h @> () })

-- localLinRefSubst :: SubstEnv -> TransposeM a -> TransposeM a
-- localLinRefSubst s = local (<> mempty { linRefSubst = s })

-- localNonlinSubst :: SubstEnv -> TransposeM a -> TransposeM a
-- localNonlinSubst s = local (<> mempty { nonlinSubst = s })

-- === The (0, +) monoid for tangent types ===

-- zeroAt :: Type n -> Atom n
-- zeroAt ty = case ty of
--   BaseTy bt  -> Con $ Lit $ zeroLit bt
--   -- i :==> a  -> TabValA i $ zeroAt a
--   UnitTy     -> UnitVal
--   PairTy a b -> PairVal (zeroAt a) (zeroAt b)
--   RecordTy (Ext tys Nothing) -> Record $ fmap zeroAt tys
--   _          -> unreachable
--   where
--     unreachable = error $ "Missing zero case for a tangent type: " ++ pprint ty
--     zeroLit bt = case bt of
--       Scalar Float64Type -> Float64Lit 0.0
--       Scalar Float32Type -> Float32Lit 0.0
--       Vector st          -> VecLit $ replicate vectorWidth $ zeroLit $ Scalar st
--       _                  -> unreachable

-- updateAddAt :: Builder n m => Atom n -> m (Atom n)
-- updateAddAt x = do
--   ty <- getTypeE x
--   buildLam ty PureArrow $ addTangent x

-- addTangent :: Builder n m => Atom n -> Atom n -> m (Atom n)
-- addTangent x y = do
--  ty <- getTypeE x
--  let notTangent = error $ "Not a tangent type: " ++ pprint ty
--  case ty of
--   RecordTy (NoExt tys) -> do
--     elems <- bindM2 (zipWithT addTangent) (getUnpacked x) (getUnpacked y)
--     return $ Record $ restructure elems tys
--   TabTy abs -> buildFor Fwd (absTy abs) \i ->
--                   bindM2 addTangent (tabGet x i) (tabGet y i)
--   TC con -> case con of
--     BaseType (Scalar _) -> emitOp $ ScalarBinOp FAdd x y
--     BaseType (Vector _) -> emitOp $ VectorBinOp FAdd x y
--     UnitType            -> return UnitVal
--     PairType _ _        -> do
--       (xa, xb) <- fromPair x
--       (ya, yb) <- fromPair y
--       PairVal <$> addTangent xa ya <*> addTangent xb yb
--     _ -> notTangent
--   _ -> notTangent

-- tangentBaseMonoidFor :: Builder n m => Type n -> m (BaseMonoid n)
-- tangentBaseMonoidFor ty =
--   BaseMonoid (zeroAt ty) <$> buildLam ty PureArrow updateAddAt

-- checkZeroPlusFloatMonoid :: BaseMonoid n -> Bool
-- checkZeroPlusFloatMonoid = undefined
-- -- checkZeroPlusFloatMonoid (BaseMonoid zero plus) = checkZero zero && checkPlus plus
-- --   where
-- --     checkZero z = z == (Con (Lit (Float32Lit 0.0)))
-- --     checkPlus f = case f of
-- --       BinaryFunVal (Bind x) (Bind y) Pure (Block Empty (Op (ScalarBinOp FAdd (Var x') (Var y')))) ->
-- --         (x == x' && y == y') || (x == y' && y == x')
-- --       _ -> False
