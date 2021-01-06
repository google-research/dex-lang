-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}

module Autodiff (linearize, transpose) where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State.Strict
import qualified Data.List.NonEmpty as NE
import Data.Maybe
import Data.Foldable
import qualified Data.Set as S

import Type
import Env
import Syntax
import PPrint
import Embed
import Cat
import Util (bindM2, zipWithT, enumerate, restructure)
import GHC.Stack

-- === linearization ===

-- `DerivWrt` holds the (out-expr) variables that we're differentiating with
-- respect to (including refs but not regions).
data DerivWrt = DerivWrt { activeVars  :: Env Type
                         , _activeEffs :: [Effect]
                         , rematVars   :: Env Type }
-- `Tangents` holds the tangent values and the region variables that are
-- arguments to the linearized function.
data TangentEnv = TangentEnv { tangentVals :: SubstEnv, activeRefs :: [Name], rematVals :: SubstEnv }

type PrimalM  = ReaderT DerivWrt   Embed
type TangentM = ReaderT TangentEnv Embed
newtype LinA a = LinA { runLinA :: PrimalM (a, TangentM a) }

linearize :: Scope -> Atom -> Atom
linearize scope ~(Lam (Abs b (_, block))) = fst $ flip runEmbed scope $ do
  buildLam b PureArrow \x@(Var v) -> do
    (y, yt) <- flip runReaderT (DerivWrt (varAsEnv v) [] mempty) $ runLinA $ linearizeBlock (b@>x) block
    -- TODO: check linearity
    fLin <- buildLam (fmap tangentType b) LinArrow \xt -> runReaderT yt $ TangentEnv (v @> xt) [] mempty
    fLinChecked <- checkEmbed fLin
    return $ PairVal y fLinChecked

linearizeBlock :: SubstEnv -> Block -> LinA Atom
linearizeBlock env (Block decls result) = case decls of
  Empty -> linearizeExpr env result
  Nest decl rest -> case decl of
    (Let _ b expr) -> linearizeBinding b expr
    where
      body = Block rest result
      linearizeBinding :: Binder -> Expr -> LinA Atom
      linearizeBinding b expr = LinA $ do
        -- Don't linearize expressions with no free active variables.
        -- Technically, we could do this and later run the code through a simplification
        -- pass that would eliminate a bunch of multiplications with zeros, but this seems
        -- simpler to do for now.
        freeAtoms <- traverse (substEmbed env . Var) $ bindingsAsVars $ freeVars expr
        varsAreActive <- traverse isActive $ bindingsAsVars $ freeVars freeAtoms
        if any id varsAreActive
          then do
            (x, boundLin) <- runLinA $ linearizeExpr env expr
            ~(Var v) <- emit $ Atom x
            -- NB: This can still overestimate the set of active variables (e.g.
            --     when multiple values are returned from a case statement).
            -- Don't mark variables with trivial tangent types as active. This lets us avoid
            -- pretending that we're differentiating wrt e.g. equality tests which yield discrete results.
            -- TODO: This check might fail if the result type does not have a defined tangent type.
            --       For example, what if it's a reference? Some of those should be marked as active
            --       variables, but I don't think that we want to define them to have tangents.
            --       We should delete this check, but to do that we would have to support differentiation
            --       through case statements with active scrutinees.
            let vIsTrivial = isSingletonType $ tangentType $ varType v
            let nontrivialVs = if vIsTrivial then [] else [v]
            (ans, bodyLin) <- extendWrt nontrivialVs [] $ runLinA $
              linearizeBlock (env <> b @> Var v) body
            return (ans, do
              t <- boundLin
              -- Tangent environment needs to be synced between the primal and tangent
              -- monads (tangentFunAsLambda and applyLinToTangents need that).
              let nontrivialTs = if vIsTrivial then [] else [t]
              extendTangentEnv (newEnv nontrivialVs nontrivialTs) [] bodyLin)
          else do
            expr' <- substEmbed env expr
            x <- emit expr'
            runLinA $ linearizeBlock (env <> b @> x) body

linearizeExpr :: SubstEnv -> Expr -> LinA Atom
linearizeExpr env expr = case expr of
  Hof  e        -> linearizeHof env e
  Case e alts _ -> LinA $ do
    e'   <- substEmbed env e
    hasActiveScrutinee <- any id <$> (mapM isActive $ bindingsAsVars $ freeVars e')
    case hasActiveScrutinee of
      True  -> notImplemented
      False -> do
        alts' <- traverse linearizeInactiveAlt alts
        result <- emit $ Case e' alts' $ (\((Abs _ body):_) -> getType body) alts'
        (ans, linLam) <- fromPair result
        return (ans, applyLinToTangents linLam)
    where
      linearizeInactiveAlt (Abs bs body) = do
        buildNAbs bs \xs -> tangentFunAsLambda $ linearizeBlock (env <> newEnv bs xs) body
  _ -> LinA $ do
    expr' <- substEmbed env expr
    runLinA $ case expr' of
      App x i | isTabTy (getType x) -> liftA (flip App i) (linearizeAtom x) `bindLin` emit
      Op   e     -> linearizeOp   e
      Atom e     -> linearizeAtom e
      App _ _    -> error "Unexpected non-table application"
      Case _ _ _ -> error "Case should be handled above"
      Hof _      -> error "Hofs should be handled above"

linearizeOp :: Op -> LinA Atom
linearizeOp op = case op of
  ScalarUnOp  uop x       -> linearizeUnOp  uop x
  ScalarBinOp bop x y     -> linearizeBinOp bop x y
  PrimEffect refArg m ->
    liftA2 PrimEffect (la refArg)
      (case m of
         MAsk    -> pure MAsk
         MTell x -> liftA MTell $ la x
         MGet    -> pure MGet
         MPut  x -> liftA MPut $ la x) `bindLin` emitOp
  IndexRef ref i         -> (IndexRef <$> la ref <*> pure i) `bindLin` emitOp
  FstRef   ref           -> (FstRef   <$> la ref           ) `bindLin` emitOp
  SndRef   ref           -> (SndRef   <$> la ref           ) `bindLin` emitOp
  Select p t f           -> (Select p <$> la t   <*> la f  ) `bindLin` emitOp
  -- XXX: This assumes that pointers are always constants
  PtrLoad _              -> emitWithZero
  PtrStore _ _           -> emitDiscrete
  PtrOffset _ _          -> emitDiscrete
  IOAlloc _ _            -> emitDiscrete
  IOFree _               -> emitDiscrete
  TabCon ty xs           -> (TabCon ty <$> traverse la xs) `bindLin` emitOp
  Inject _               -> emitDiscrete
  SliceOffset _ _        -> emitDiscrete
  SliceCurry  _ _        -> emitDiscrete
  VectorBinOp _ _ _      -> notImplemented
  VectorPack  vals       -> (VectorPack  <$> traverse la vals) `bindLin` emitOp
  VectorIndex v i        -> (VectorIndex <$> la v <*> pure i ) `bindLin` emitOp
  UnsafeFromOrdinal _ _  -> emitDiscrete
  ToOrdinal _            -> emitDiscrete
  IdxSetSize _           -> emitDiscrete
  ThrowError _           -> emitWithZero
  DataConTag _           -> emitDiscrete
  ToEnum _ _             -> emitDiscrete
  CastOp t v             -> do
    if tangentType vt == vt && tangentType t == t
      then (CastOp t <$> la v) `bindLin` emitOp
      else castWithTrivial
    where
      vt = getType v
      castWithTrivial = LinA $ do
        (x, xt) <- runLinA $ la v
        let yt = case (tangentType vt, tangentType t) of
              (_     , UnitTy) -> UnitVal
              (UnitTy, tt    ) -> zeroAt tt
              _                -> error "Expected at least one side of the CastOp to have a trivial tangent type"
        (emitOp $ CastOp t x) <$$> (,xt >> return yt)
  RecordCons   vs r      -> (RecordCons      <$> traverse la vs <*> la r) `bindLin` emitOp
  RecordSplit  vs r      -> (RecordSplit     <$> traverse la vs <*> la r) `bindLin` emitOp
  VariantLift  ts v      -> (VariantLift  ts <$> la v) `bindLin` emitOp
  VariantSplit ts v      -> (VariantSplit ts <$> la v) `bindLin` emitOp
  FFICall _ _ _          -> error $ "Can't differentiate through an FFI call"
  ThrowException _       -> notImplemented
  where
    emitDiscrete = if isTrivialForAD (Op op)
      then LinA $ withZeroTangent <$> emitOp op
      else error $ "Op expected to have a discrete result: " ++ pprint op
    la = linearizeAtom
    emitWithZero :: LinA Atom
    emitWithZero = LinA $ withZeroTangent <$> emitOp op

emitUnOp :: MonadEmbed m => UnOp -> Atom -> m Atom
emitUnOp op x = emitOp $ ScalarUnOp op x

linearizeUnOp :: UnOp -> Atom -> LinA Atom
linearizeUnOp op x' = LinA $ do
  (x, tx) <- runLinA $ linearizeAtom x'
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
      return (y, bindM2 div' tx (mul (2 `fLitLike` y) y))
    Floor  -> withZeroTangent <$> emitUnOp Floor x
    Ceil   -> withZeroTangent <$> emitUnOp Ceil  x
    Round  -> withZeroTangent <$> emitUnOp Round x
    LGamma -> notImplemented
    FNeg   -> neg x <$$> (,neg =<< tx)
    BNot   -> emitDiscrete
  where
    emitDiscrete = if isTrivialForAD (Op $ ScalarUnOp op x')
      then withZeroTangent <$> emitOp (ScalarUnOp op x')
      else error $ "Op expected to have a discrete result: " ++ show op

linearizeBinOp :: BinOp -> Atom -> Atom -> LinA Atom
linearizeBinOp op x' y' = LinA $ do
  (x, tx) <- runLinA $ linearizeAtom x'
  (y, ty) <- runLinA $ linearizeAtom y'
  case op of
    IAdd   -> emitDiscrete
    ISub   -> emitDiscrete
    IMul   -> emitDiscrete
    IDiv   -> emitDiscrete
    IRem   -> emitDiscrete
    ICmp _ -> emitDiscrete
    FAdd   -> add x y  <$$> (,bindM2 add tx ty)
    FSub   -> sub x y  <$$> (,bindM2 sub tx ty)
    FMul   -> mul x y  <$$> (,bindM2 add (bindM2 mul (pure x) ty) (bindM2 mul tx (pure y)))
    FDiv   -> div' x y <$$>
        (,do
             tx' <- bindM2 div' tx (pure y)
             ty' <- bindM2 div' (bindM2 mul (pure x) ty) (mul y y)
             sub tx' ty')
    FPow   -> (emitOp $ ScalarBinOp FPow x y) <$$>
        (,do
             c <- fpow x =<< sub y (1.0 `fLitLike` y)
             tx' <- bindM2 mul tx (pure y)
             ty' <- bindM2 mul (bindM2 mul (pure x) ty) (flog x)
             mul c =<< add tx' ty')
    FCmp _ -> emitDiscrete
    BAnd   -> emitDiscrete
    BOr    -> emitDiscrete
    BShL   -> emitDiscrete
    BShR   -> emitDiscrete
  where
    emitDiscrete = if isTrivialForAD (Op $ ScalarBinOp op x' y')
      then withZeroTangent <$> emitOp (ScalarBinOp op x' y')
      else error $ "Op expected to have a discrete result: " ++ show op

-- Here, we want to take advantage of simplification's automatic desugaring of
-- Hofs that return functions into Hofs that return residual values, so the where
-- part implements functions that convert the TangentM actions into lambdas that
-- abstract over the whole tangent state.
linearizeHof :: SubstEnv -> Hof -> LinA Atom
linearizeHof env hof = case hof of
  For ~(RegularFor d) ~(LamVal i body) -> LinA $ do
    i' <- mapM (substEmbed env) i
    (ansWithLinTab, vi'') <- buildForAux d i' \i''@(Var vi'') ->
       (,vi'') <$> (willRemat vi'' $ tangentFunAsLambda $ linearizeBlock (env <> i@>i'') body)
    (ans, linTab) <- unzipTab ansWithLinTab
    return (ans, buildFor d i' \i'' -> provideRemat vi'' i'' $ app linTab i'' >>= applyLinToTangents)
  Tile _ _ _        -> notImplemented
  RunWriter     lam -> linearizeEff Nothing    lam True  (const RunWriter) (emitRunWriter "r") Writer
  RunReader val lam -> linearizeEff (Just val) lam False RunReader         (emitRunReader "r") Reader
  RunState  val lam -> linearizeEff (Just val) lam True  RunState          (emitRunState  "r") State
  RunIO ~(Lam (Abs _ (arrow, body))) -> LinA $ do
    arrow' <- substEmbed env arrow
    -- TODO: consider the possibility of other effects here besides IO
    lam <- buildLam (Ignore UnitTy) arrow' \_ ->
      tangentFunAsLambda $ linearizeBlock env body
    result <- emit $ Hof $ RunIO lam
    (ans, linLam) <- fromPair result
    return (ans, applyLinToTangents linLam)
  -- TODO: Consider providing an upper bound for the number of while iterations as a hint.
  --       In the current form the best we can do is try to use some dynamically growing lists,
  --       but that won't work on the GPU.
  While _          -> notImplemented
  CatchException _ -> notImplemented
  Linearize _ -> error "Unexpected linearization"
  Transpose _ -> error "Unexpected transposition"
  PTileReduce _ _ -> error "Unexpected PTileReduce"
  where
    linearizeEff maybeInit lam hasResult hofMaker emitter eff = LinA $ do
      (valHofMaker, maybeLinInit) <- case maybeInit of
          Just val -> do
            (val', linVal) <- runLinA <$> linearizeAtom =<< substEmbed env val
            return (hofMaker val', Just linVal)
          Nothing -> return (hofMaker undefined, Nothing)
      (lam', ref)    <- linearizeEffectFun eff lam
      (ans, linBody) <- case hasResult of
          True -> do
            (ansLin, w)    <- fromPair =<< emit (Hof $ valHofMaker lam')
            (ans, linBody) <- fromPair ansLin
            return (PairVal ans w, linBody)
          False -> fromPair =<< emit (Hof $ valHofMaker lam')
      let lin = do
                  valEmitter <- case maybeLinInit of
                    Just linVal -> emitter <$> linVal
                    Nothing     -> do
                      let (BinaryFunTy _ b _ _) = getType lam'
                      let RefTy _ wTy = binderType b
                      return $ emitter $ tangentType wTy
                  valEmitter \ref'@(Var (_:> RefTy (Var (h:>_)) _)) -> do
                      extendTangentEnv (ref @> ref') [h] $ applyLinToTangents linBody
      return (ans, lin)

    linearizeEffectFun :: RWS -> Atom -> PrimalM (Atom, Var)
    linearizeEffectFun rws ~(BinaryFunVal h ref eff body) = do
      h' <- mapM (substEmbed env) h
      buildLamAux h' (const $ return PureArrow) \h''@(Var hVar) -> do
        let env' = env <> h@>h''
        eff' <- substEmbed env' eff
        ref' <- mapM (substEmbed env') ref
        buildLamAux ref' (const $ return $ PlainArrow eff') \ref''@(Var refVar) ->
          extendWrt [refVar] [RWSEffect rws (varName hVar)] $
            (,refVar) <$> (tangentFunAsLambda $ linearizeBlock (env' <> ref@>ref'') body)

linearizePrimCon :: Con -> LinA Atom
linearizePrimCon con = case con of
  Lit _                 -> emitWithZero
  PairCon x y           -> PairVal <$> linearizeAtom x <*> linearizeAtom y
  UnitCon               -> emitWithZero
  SumAsProd ty tg elems -> Con . SumAsProd ty tg <$> traverse (traverse linearizeAtom) elems
  IntRangeVal _ _ _     -> emitWithZero
  IndexRangeVal _ _ _ _ -> emitWithZero
  IndexSliceVal _ _ _   -> emitWithZero
  BaseTypeRef _  -> error "Unexpected ref"
  TabRef _       -> error "Unexpected ref"
  ConRef _       -> error "Unexpected ref"
  RecordRef _    -> error "Unexpected ref"
  ParIndexCon   _ _ -> error "Unexpected ParIndexCon"
  ClassDictHole _ _ -> error "Unexpected ClassDictHole"
  where emitWithZero = LinA $ return $ withZeroTangent $ Con con

linearizeAtom :: Atom -> LinA Atom
linearizeAtom atom = case atom of
  Var v -> LinA $ do
    active <- isActive v
    if active
      then return $ (atom, asks $ (!v) . tangentVals)
      else return $ withZeroTangent atom
  Con con -> linearizePrimCon con
  Lam (Abs i (TabArrow, body)) -> LinA $ do
    wrt <- ask
    return (atom, buildLam i TabArrow \i' ->
                    rematPrimal wrt $ linearizeBlock (i@>i') body)
  DataCon _ _ _ _ -> notImplemented  -- Need to synthesize or look up a tangent ADT
  Record elems    -> Record <$> traverse linearizeAtom elems
  Variant t l i e -> Variant t l i <$> linearizeAtom e
  TypeCon _ _     -> emitWithZero
  LabeledRow _    -> emitWithZero
  RecordTy _      -> emitWithZero
  VariantTy _     -> emitWithZero
  Pi _            -> emitWithZero
  TC _            -> emitWithZero
  Eff _           -> emitWithZero
  ProjectElt idxs v -> getProjection (toList idxs) <$> linearizeAtom (Var v)
  -- Those should be gone after simplification
  Lam _           -> error "Unexpected non-table lambda"
  ACase _ _ _     -> error "Unexpected ACase"
  DataConRef _ _ _ -> error "Unexpected ref"
  BoxedRef _ _ _ _ -> error "Unexpected ref"
  where
    emitWithZero = LinA $ return $ withZeroTangent atom
    rematPrimal wrt m = do
      (_, lin) <- lift $ runReaderT (runLinA m) wrt
      lin

withZeroTangent :: Atom -> (Atom, TangentM Atom)
withZeroTangent x = (x, return $ zeroAt (tangentType (getType x)))

tangentType :: Type -> Type
tangentType ty = case ty of
  RecordTy (NoExt items) -> RecordTy $ NoExt $ fmap tangentType items
  TypeCon  _ _ -> notImplemented -- Need to synthesize or look up a tangent ADT
  TabTy n a -> TabTy n (tangentType a)
  TC con    -> case con of
    BaseType (Scalar Float64Type) -> TC con
    BaseType (Scalar Float32Type) -> TC con
    BaseType (Vector Float64Type) -> TC con
    BaseType (Vector Float32Type) -> TC con
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

addTangent :: MonadEmbed m => Atom -> Atom -> m Atom
addTangent x y = case getType x of
  RecordTy (NoExt tys) -> do
    elems <- bindM2 (zipWithT addTangent) (getUnpacked x) (getUnpacked y)
    return $ Record $ restructure elems tys
  TabTy b _  -> buildFor Fwd b \i -> bindM2 addTangent (tabGet x i) (tabGet y i)
  TC con -> case con of
    BaseType (Scalar _) -> emitOp $ ScalarBinOp FAdd x y
    BaseType (Vector _) -> emitOp $ VectorBinOp FAdd x y
    UnitType            -> return UnitVal
    PairType _ _        -> do
      (xa, xb) <- fromPair x
      (ya, yb) <- fromPair y
      PairVal <$> addTangent xa ya <*> addTangent xb yb
    _ -> notTangent
  _ -> notTangent
  where notTangent = error $ "Not a tangent type: " ++ pprint (getType x)

isTrivialForAD :: Expr -> Bool
isTrivialForAD expr = isSingletonType tangentTy && exprEffs expr == mempty
  where tangentTy = tangentType $ getType expr

-- Abstract the tangent action as a lambda. Also accepts binders for variables that might
-- be used in the tangent function and abstracts over them (useful when they're easy to
-- reconstruct at application sites).
-- TODO: curried linear functions somehow?
tangentFunAsLambda :: LinA Atom -> PrimalM Atom
tangentFunAsLambda m = do
  (ans, tanFun) <- runLinA m
  DerivWrt activeVars effs remats <- ask
  let hs = map (Bind . (:>TyKind) . effectRegion) effs
  let rematList = envAsVars remats
  liftM (PairVal ans) $ lift $ do
    tanLam <- makeLambdas rematList \rematArgs ->
      buildNestedLam PureArrow hs \hVals -> do
        let hVarNames = map (\(Var (v:>_)) -> v) hVals
        -- TODO: handle exception effect too
        let effs' = zipWith (\(RWSEffect rws _) v -> RWSEffect rws v) effs hVarNames
        -- want to use tangents here, not the original binders
        let regionMap = newEnv (map ((:>()) . effectRegion) effs) hVals
        -- TODO: Only bind tangents for free variables?
        let activeVarBinders = map (Bind . fmap (tangentRefRegion regionMap)) $ envAsVars activeVars
        buildNestedLam PureArrow activeVarBinders \activeVarArgs ->
          buildLam (Ignore UnitTy) (PlainArrow $ EffectRow (S.fromList effs') Nothing) \_ ->
            runReaderT tanFun $ TangentEnv
                 (newEnv (envNames activeVars) activeVarArgs) hVarNames
                 (newEnv rematList $ fmap Var rematArgs)
    case rematList of
      [] -> return tanLam
      _  -> deShadow tanLam <$> getScope
  where
    -- Like buildLam, but doesn't try to deshadow the binder.
    makeLambda v f = do
      block <- buildScoped $ do
        embedExtend $ asFst $ v @> (varType v, LamBound (void PureArrow))
        f v
      return $ Lam $ makeAbs (Bind v) (PureArrow, block)

    makeLambdas [] f = f []
    makeLambdas (v:vs) f = makeLambda v \x -> makeLambdas vs \xs -> f (x:xs)

    -- This doesn't work if we have references inside pairs, tables etc.
    -- TODO: something more general and cleaner.
    tangentRefRegion :: Env Atom -> Type -> Type
    tangentRefRegion regEnv ty = case ty of
      RefTy ~(Var h) a -> RefTy (regEnv ! h) $ tangentType a
      _ -> tangentType ty

    effectRegion eff = case eff of
      RWSEffect _ h -> h
      ExceptionEffect -> error "TODO!"
      IOEffect        -> error "TODO!"

-- Inverse of tangentFunAsLambda. Should be used inside a returned tangent action.
applyLinToTangents :: Atom -> TangentM Atom
applyLinToTangents f = do
  TangentEnv{..} <- ask
  let hs' = map (Var . (:>TyKind)) activeRefs
  let tangents = fmap snd $ envPairs $ tangentVals
  let args = (toList rematVals) ++ hs' ++ tangents ++ [UnitVal]
  naryApp f args

bindLin :: LinA a -> (a -> Embed b) -> LinA b
bindLin (LinA m) f = LinA $ do
  (e, t) <- m
  x <- lift $ f e
  return (x, t >>= (lift . f))

instance Functor LinA where
  fmap = liftA

instance Applicative LinA where
  pure x = LinA $ return (x, return x)
  liftA2 f (LinA m1) (LinA m2) = LinA $ do
    (x1, t1) <- m1
    (x2, t2) <- m2
    return (f x1 x2, liftM2 f t1 t2)

isActive :: Var -> PrimalM Bool
isActive v = asks ((v `isin`) . activeVars)

extendWrt :: [Var] -> [Effect] -> PrimalM a -> PrimalM a
extendWrt active effs m = local update m
  where update (DerivWrt active' effs' remats) = DerivWrt (active' <> foldMap varAsEnv active) (effs' <> effs) remats

willRemat :: Var -> PrimalM a -> PrimalM a
willRemat v = local update
  where update wrt = wrt { rematVars = rematVars wrt <> varAsEnv v }

extendTangentEnv :: SubstEnv -> [Name] -> TangentM a -> TangentM a
extendTangentEnv tv effs m = local update m
  where update (TangentEnv tv' effs' remats) = TangentEnv (tv' <> tv) (effs' <> effs) remats

provideRemat :: Var -> Atom -> TangentM a -> TangentM a
provideRemat v a = local update
  where update env = env { rematVals = rematVals env <> (v @> a) }

(<$$>) :: Functor f => f a -> (a -> b) -> f b
(<$$>) = flip (<$>)

notImplemented :: HasCallStack => a
notImplemented = error "Not implemented"

-- -- === transposition ===

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
data TransposeEnv = TransposeEnv { linRefs        :: Env (Maybe Atom)
                                 , linRefSubst    :: SubstEnv
                                 , linRegions     :: Env ()
                                 , nonlinSubst    :: SubstEnv
                                 }

instance Semigroup TransposeEnv where
  (TransposeEnv x y z w) <> (TransposeEnv x' y' z' w') =
    TransposeEnv (x <> x') (y <> y') (z <> z') (w <> w')

instance Monoid TransposeEnv where
  mempty = TransposeEnv mempty mempty mempty mempty

type TransposeM a = ReaderT TransposeEnv Embed a

transpose :: Scope -> Atom -> Atom
transpose scope ~(Lam (Abs b (_, block))) = fst $ flip runEmbed scope $ do
  buildLam (Bind $ "ct" :> getType block) LinArrow \ct -> do
    snd <$> (flip runReaderT mempty $ withLinVar b $ transposeBlock block ct)

transposeBlock :: Block -> Atom -> TransposeM ()
transposeBlock (Block decls result) ct = case decls of
  Empty -> transposeExpr result ct
  Nest decl rest -> case decl of
    (Let _ b expr) -> transposeBinding b expr
    where
      body = Block rest result
      transposeBinding b expr = do
        isLinearExpr <- (||) <$> isLinEff (exprEffs expr) <*> isLin expr
        if isLinearExpr
          then do
            cts <- withLinVars [b] $ transposeBlock body ct
            transposeExpr expr $ head cts
          else do
            expr' <- substNonlin expr
            x <- emit expr'
            localNonlinSubst (b @> x) $ transposeBlock body ct

      withLinVars :: [Binder] -> TransposeM () -> TransposeM [Atom]
      withLinVars [] m     = m >> return []
      withLinVars (b:bs) m = uncurry (flip (:)) <$> (withLinVar b $ withLinVars bs m)

transposeExpr :: Expr -> Atom -> TransposeM ()
transposeExpr expr ct = case expr of
  App x i -> case getType x of
    TabTy _ _ -> do
      i' <- substNonlin i
      ref <- traverse (\ref -> emitOp $ IndexRef ref i') =<< linAtomRef x
      emitCTToRef ref ct
    _ -> error $ "shouldn't have non-table app left"
  Hof hof       -> transposeHof hof ct
  Op op         -> transposeOp op ct
  Atom atom     -> transposeAtom atom ct
  Case e alts _ -> do
    linearScrutinee <- isLin e
    case linearScrutinee of
      True  -> notImplemented
      False -> do
        alts' <- traverse transposeNonlinAlt alts
        e' <- substNonlin e
        void $ emit $ Case e' alts' UnitTy
  where
    transposeNonlinAlt (Abs bs body) =
      buildNAbs bs \xs -> do
        localNonlinSubst (newEnv bs xs) $ transposeBlock body ct
        return UnitVal

transposeOp :: Op -> Atom -> TransposeM ()
transposeOp op ct = case op of
  ScalarUnOp  FNeg x    -> transposeAtom x =<< neg ct
  ScalarUnOp  _    _    -> notLinear
  ScalarBinOp FAdd x y  -> transposeAtom x ct >> transposeAtom y ct
  ScalarBinOp FSub x y  -> transposeAtom x ct >> (transposeAtom y =<< neg ct)
  ScalarBinOp FMul x y  -> do
    xLin <- isLin x
    if xLin
      then transposeAtom x =<< mul ct =<< substNonlin y
      else transposeAtom y =<< mul ct =<< substNonlin x
  ScalarBinOp FDiv x y  -> transposeAtom x =<< div' ct =<< substNonlin y
  ScalarBinOp _    _ _  -> notLinear
  PrimEffect refArg m   -> do
    refArg' <- substTranspose linRefSubst refArg
    let emitEff = emitOp . PrimEffect refArg'
    case m of
      MAsk    -> void $ emitEff $ MTell ct
      MTell x -> transposeAtom x =<< emitEff MAsk
      -- TODO: Do something more efficient for state. We should be able
      --       to do in-place addition, just like we do for the Writer effect.
      MGet    -> void $ emitEff . MPut =<< addTangent ct =<< emitEff MGet
      MPut  x -> do
        transposeAtom x =<< emitEff MGet
        void $ emitEff $ MPut $ zeroAt $ getType x
  TabCon ~(TabTy b _) es -> forM_ (enumerate es) \(i, e) -> do
    transposeAtom e =<< tabGet ct =<< intToIndexE (binderType b) (IdxRepVal $ fromIntegral i)
  IndexRef     _ _      -> notImplemented
  FstRef       _        -> notImplemented
  SndRef       _        -> notImplemented
  Select       _ _ _    -> notImplemented
  VectorBinOp  _ _ _    -> notImplemented
  VectorPack   _        -> notImplemented
  VectorIndex  _ _      -> notImplemented
  CastOp       _ _      -> notImplemented
  RecordCons   _ _      -> notImplemented
  RecordSplit  _ _      -> notImplemented
  VariantLift  _ _      -> notImplemented
  VariantSplit _ _      -> notImplemented
  PtrStore _ _          -> notLinear
  PtrLoad    _          -> notLinear
  PtrOffset _ _         -> notLinear
  IOAlloc _ _           -> notLinear
  IOFree _              -> notLinear
  Inject       _        -> notLinear
  SliceOffset  _ _      -> notLinear
  SliceCurry   _ _      -> notLinear
  UnsafeFromOrdinal _ _ -> notLinear
  ToOrdinal    _        -> notLinear
  IdxSetSize   _        -> notLinear
  ThrowError   _        -> notLinear
  FFICall _ _ _         -> notLinear
  DataConTag _          -> notLinear
  ToEnum _ _            -> notLinear
  ThrowException _      -> notLinear
  where
    -- Both nonlinear operations and operations on discrete types, where linearity doesn't make sense
    notLinear = error $ "Can't transpose a non-linear operation: " ++ pprint op

linAtomRef :: Atom -> TransposeM (Maybe Atom)
linAtomRef (Var x) = do
  refs <- asks linRefs
  case envLookup refs x of
    Just ref -> return ref
    _ -> error $ "Not a linear var: " ++ pprint (Var x)
linAtomRef (ProjectElt (i NE.:| is) x) =
  let subproj = case NE.nonEmpty is of
        Just is' -> ProjectElt is' x
        Nothing -> Var x
  in case getType subproj of
    PairTy _ _ -> do
      ref <- linAtomRef subproj
      (traverse $ emitOp . getter) ref
      where getter = case i of 0 -> FstRef
                               1 -> SndRef
                               _ -> error "bad pair projection"
    ty -> error $ "Projecting references not implemented for type " <> pprint ty
linAtomRef a = error $ "Not a linear var: " ++ pprint a

transposeHof :: Hof -> Atom -> TransposeM ()
transposeHof hof ct = case hof of
  For ~(RegularFor d) ~(Lam (Abs b (_, body))) ->
    void $ buildFor (flipDir d) b \i -> do
      ct' <- tabGet ct i
      localNonlinSubst (b@>i) $ transposeBlock body ct'
      return UnitVal
    where flipDir dir = case dir of Fwd -> Rev; Rev -> Fwd
  RunReader r ~(BinaryFunVal (Bind (h:>_)) b _ body) -> do
    (_, ctr) <- (fromPair =<<) $ emitRunWriter "w" (getType r) \ref -> do
      localLinRegion h $ localLinRefSubst (b@>ref) $ transposeBlock body ct
      return UnitVal
    transposeAtom r ctr
  RunWriter ~(BinaryFunVal (Bind (h:>_)) b _ body) -> do
    (ctBody, ctEff) <- fromPair ct
    void $ emitRunReader "r" ctEff \ref -> do
      localLinRegion h $ localLinRefSubst (b@>ref) $ transposeBlock body ctBody
      return UnitVal
  RunState s ~(BinaryFunVal (Bind (h:>_)) b _ body) -> do
    (ctBody, ctState) <- fromPair ct
    (_, cts) <- (fromPair =<<) $ emitRunState "s" ctState \ref -> do
      localLinRegion h $ localLinRefSubst (b@>ref) $ transposeBlock body ctBody
      return UnitVal
    transposeAtom s cts
  Tile      _ _ _  -> notImplemented
  While         _  -> notImplemented
  RunIO _          -> notImplemented
  CatchException _ -> notImplemented
  Linearize     _  -> error "Unexpected linearization"
  Transpose     _  -> error "Unexpected transposition"
  PTileReduce _ _  -> error "Unexpected PTileReduce"

transposeAtom :: Atom -> Atom -> TransposeM ()
transposeAtom atom ct = case atom of
  Var v -> do
    refs <- asks linRefs
    case envLookup refs v of
      Just ref -> emitCTToRef ref ct
      Nothing  -> return ()
  Con con         -> transposeCon con ct
  Record  e       -> void $ zipWithT transposeAtom e =<< getUnpacked ct
  DataCon _ _ _ e -> void $ zipWithT transposeAtom e =<< getUnpacked ct
  Variant _ _ _ _ -> notImplemented
  TabVal b body   ->
    void $ buildFor Fwd b \i -> do
      ct' <- tabGet ct i
      localNonlinSubst (b@>i) $ transposeBlock body ct'
      return UnitVal
  Lam _           -> notTangent
  TypeCon _ _     -> notTangent
  LabeledRow _    -> notTangent
  RecordTy _      -> notTangent
  VariantTy _     -> notTangent
  Pi _            -> notTangent
  TC _            -> notTangent
  Eff _           -> notTangent
  ACase _ _ _     -> error "Unexpected ACase"
  DataConRef _ _ _ -> error "Unexpected ref"
  BoxedRef _ _ _ _ -> error "Unexpected ref"
  ProjectElt _ v -> do
    lin <- isLin $ Var v
    when lin $ flip emitCTToRef ct =<< linAtomRef atom
  where notTangent = error $ "Not a tangent atom: " ++ pprint atom

transposeCon :: Con -> Atom -> TransposeM ()
transposeCon con ct = case con of
  Lit _             -> return ()
  UnitCon           -> return ()
  PairCon x y       -> do
    getFst ct >>= transposeAtom x
    getSnd ct >>= transposeAtom y
  SumAsProd _ _ _   -> notImplemented
  ClassDictHole _ _ -> notTangent
  IntRangeVal _ _ _     -> notTangent
  IndexRangeVal _ _ _ _ -> notTangent
  IndexSliceVal _ _ _   -> notTangent
  ParIndexCon _ _       -> notTangent
  BaseTypeRef _  -> notTangent
  TabRef _       -> notTangent
  ConRef _       -> notTangent
  RecordRef _    -> notTangent
  where notTangent = error $ "Not a tangent atom: " ++ pprint (Con con)

freeLinVars :: HasVars a => a -> TransposeM [Var]
freeLinVars x = do
  refs <- asks linRefs
  return $ bindingsAsVars $ envIntersect refs (freeVars x)

isLin :: HasVars a => a -> TransposeM Bool
isLin x = not . null <$> freeLinVars x

isLinEff :: EffectRow -> TransposeM Bool
isLinEff (EffectRow effs Nothing) = do
  regions <- asks linRegions
  return $ not $ null $ effRegions `envIntersect` regions
  where effRegions = freeVars $ toList effs
isLinEff _ = error "Can't transpose polymorphic effects"

emitCTToRef :: Maybe Atom -> Atom -> TransposeM ()
emitCTToRef mref ct = case mref of
  Just ref -> void $ emitOp $ PrimEffect ref (MTell ct)
  Nothing  -> return ()

substTranspose :: Subst a => (TransposeEnv -> SubstEnv) -> a -> TransposeM a
substTranspose sel x = do
  env <- asks sel
  scope <- getScope
  return $ subst (env, scope) x

substNonlin :: Subst a => a -> TransposeM a
substNonlin = substTranspose nonlinSubst

withLinVar :: Binder -> TransposeM a -> TransposeM (a, Atom)
withLinVar b body = case
  singletonTypeVal (binderType b) of
    Nothing -> flip evalStateT Nothing $ do
      ans <- emitRunWriter "ref" (binderType b) \ref -> do
        lift (localLinRef (b@>Just ref) body) >>= put . Just >> return UnitVal
      (,) <$> (fromJust <$> get) <*> (getSnd ans)
    Just x -> (,x) <$> (localLinRef (b@>Nothing) body)  -- optimization to avoid accumulating into unit

localLinRef :: Env (Maybe Atom) -> TransposeM a -> TransposeM a
localLinRef refs = local (<> mempty { linRefs = refs })

localLinRegion :: Name -> TransposeM a -> TransposeM a
localLinRegion h = local (<> mempty { linRegions = h @> () })

localLinRefSubst :: SubstEnv -> TransposeM a -> TransposeM a
localLinRefSubst s = local (<> mempty { linRefSubst = s })

localNonlinSubst :: SubstEnv -> TransposeM a -> TransposeM a
localNonlinSubst s = local (<> mempty { nonlinSubst = s })
