-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

module Inference (inferModule) where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Except hiding (Except)
import Data.Foldable (fold)
import qualified Data.Map.Strict as M
import Data.Text.Prettyprint.Doc

import Syntax
import Embed  hiding (sub)
import Env
import Record
import Type
import PPrint
import Cat
import Subst

-- TODO: consider just carrying an `Atom` (since the type is easily recovered)
type InfEnv = Env (Atom, Type)
type UInferM = ReaderT InfEnv (EmbedT (SolverT (Either Err)))

type SigmaType = Type  -- may     start with an implicit lambda
type RhoType   = Type  -- doesn't start with an implicit lambda
data RequiredTy a = Check a | Infer
data InferredTy a = Checked | Inferred a

inferModule :: TopEnv -> UModule -> Except (Module, TopInfEnv)
inferModule topEnv (UModule imports exports decls) = do
  let env = infEnvFromTopEnv topEnv
  let unboundVars = filter (\v -> not $ (v:>()) `isin` env) imports
  unless (null unboundVars) $
    throw UnboundVarErr $ pprintList unboundVars
  let shadowedVars = filter (\v -> (v:>()) `isin` env) exports
  unless (null shadowedVars) $
    throw RepeatedVarErr $ pprintList shadowedVars
  (env', decls') <- runUInferM (inferUDecls noEffect decls) env
  let combinedEnv = env <> env'
  let imports' = [v :> snd (env         ! (v:>())) | v <- imports]
  let exports' = [v :> snd (combinedEnv ! (v:>())) | v <- exports]
  let resultVals = [fst    (combinedEnv ! (v:>())) | v <- exports]
  let body = wrapDecls decls' $ TupVal resultVals
  return (Module Nothing (imports', exports') body, (fmap snd env', mempty))

runUInferM :: (Subst a, Pretty a) => UInferM a -> InfEnv -> Except (a, [Decl])
runUInferM m env = runSolverT $ runEmbedT (runReaderT m env) scope
  where scope = fmap (const Nothing) env

infEnvFromTopEnv :: TopEnv -> InfEnv
infEnvFromTopEnv (TopEnv (tyEnv, _) substEnv _) =
  fold [v' @> (substEnv ! v', ty) | (v, ty) <- envPairs tyEnv, let v' = v:>()]

-- TODO: think about effects
checkSigma :: UExpr -> Effect -> SigmaType -> UInferM Atom
checkSigma expr eff ty = case ty of
  ArrowType im@(ImplicitArg _) _ piTy@(Pi a _) -> do
    lamExpr <- buildLamExpr ("a":>a) $ \x ->
                 checkSigma expr eff $ snd $ applyPi piTy x
    return $ Con $ Lam im NonLin noEffect lamExpr
  _ -> checkRho expr eff ty

inferSigma :: UExpr -> Effect -> UInferM (Atom, SigmaType)
inferSigma (UPos pos expr) eff = case expr of
  ULam ImplicitArrow lamExpr -> addSrcContext (Just pos) $ do
    -- TODO: effects
    (lamExpr', piTy) <- inferULam lamExpr
    let lam = lamWithArrowHead ImplicitArrow lamExpr'
    let ty = arrowTyWithArrowHead ImplicitArrow piTy
    return (lam, ty)
  _ ->
    inferRho (UPos pos expr) eff

checkRho :: UExpr -> Effect -> RhoType -> UInferM Atom
checkRho expr eff ty = do
  (val, Checked) <- checkOrInferRho expr eff (Check ty)
  return val

inferRho :: UExpr -> Effect -> UInferM (Atom, RhoType)
inferRho expr eff = do
  (val, Inferred ty) <- checkOrInferRho expr eff Infer
  return (val, ty)

-- This is necessary so that embed's `getType` doesn't get confused
-- TODO: figure out a better way. It's probably enough to just solve locally as
-- part of leak checking when we construct dependent lambdas.
emitZonked :: CExpr -> UInferM Atom
emitZonked expr = zonk expr >>= emit

instantiateSigma :: (Atom, SigmaType) -> UInferM (Atom, RhoType)
instantiateSigma (f,  ArrowType (ImplicitArg _) _ piTy@(Pi argTy _)) = do
  x <- freshInfVar argTy
  ans <- emitZonked $ App NonLin f x
  let (_, ansTy) = applyPi piTy x
  return (ans, ansTy)
instantiateSigma (x, ty) = return (x, ty)

checkOrInferRho :: UExpr -> Effect -> RequiredTy RhoType
                -> UInferM (Atom, InferredTy RhoType)
checkOrInferRho (UPos pos expr) eff reqTy = addSrcContext (Just pos) $ case expr of
  UVar v -> asks (! v) >>= instantiateSigma >>= matchRequirement
  ULam ImplicitArrow (ULamExpr (RecLeaf b) body) -> do
    argTy <- checkAnn $ varAnn b
    x <- freshInfVar argTy
    extendR (b@>(x, argTy)) $ checkOrInferRho body eff reqTy
  ULam ah lamExpr -> case reqTy of
    -- TODO: effects
    Check ty -> do
      (ahReq, piTy) <- fromArrowType ty
      checkArrowHead ahReq ah
      lamExpr' <- checkULam lamExpr piTy
      let lam = lamWithArrowHead ahReq lamExpr'
      return (lam, Checked)
    Infer -> do
      (lamExpr', piTy) <- inferULam lamExpr
      let lam = lamWithArrowHead ah lamExpr'
      let ty = arrowTyWithArrowHead ah piTy
      return (lam, Inferred ty)
  -- This looks like it needs de-duping with ULam case, but it might look quite
  -- different once we have effects
  UFor dir lamExpr -> case reqTy of
    Check ty -> do
      (ahReq, piTy) <- fromArrowType ty
      checkArrowHead ahReq TabArrow
      lamExpr' <- checkULam lamExpr piTy
      result <- emitZonked $ For dir lamExpr'
      return (result, Checked)
    Infer -> do
      (lamExpr', piTy) <- inferULam lamExpr
      let ty = arrowTyWithArrowHead TabArrow piTy
      result <- emitZonked $ For dir lamExpr'
      return (result, Inferred ty)
  -- Feels like it needs de-duping with ULam case, but it's going to look quite
  -- different once we have effects
  UApp ah f x -> do
    (fVal, fTy) <- inferRho f eff
    (ahReq, piTy@(Pi argTy _)) <- fromArrowType fTy
    checkArrowHead ahReq ah
    xVal <- checkSigma x eff argTy
    let (appEff, appTy) = applyPi piTy xVal
    checkEffect eff appEff
    appVal <- emitZonked $ appWithArrowHead ahReq fVal xVal
    instantiateSigma (appVal, appTy) >>= matchRequirement
  UArrow ah (UPi (v:>a) b) -> do
    -- TODO: make sure there's no effect if it's an implicit or table arrow
    a' <- checkUType a
    -- TODO: freshen as we go under the binder
    b' <- extendR ((v:>())@>(Var (v:>a'), a')) $ do
            extendScope ((v:>())@>Nothing)
            checkUType b
    let ty = arrowTyWithArrowHead ah $ makePi (v:>a') (noEffect, b')
    matchRequirement (ty, TyKind)
  UDecl decl body -> do
    env <- inferUDecl eff decl
    extendR env $ checkOrInferRho body eff reqTy
  UPrimExpr prim -> do
    prim' <- traverseExpr prim lookupName lookupName (error "not implemented")
    val <- case prim' of
      OpExpr  op  -> emitZonked op
      ConExpr con -> return $ Con con
      TyExpr  con -> return $ TC con
    matchRequirement (val, getType val)
    where lookupName v = fst <$> asks (! (v:>()))
  UAnnot e ty -> do
    ty' <- checkUType ty
    val <- checkSigma e eff ty'
    matchRequirement (val, ty')
  where
    matchRequirement :: (Atom, Type) -> UInferM (Atom, InferredTy RhoType)
    matchRequirement (x, ty) = liftM (x,) $
      case reqTy of
        Infer -> return $ Inferred ty
        Check req -> do
          constrainEq req ty
          return Checked

inferUDecl :: Effect -> UDecl -> UInferM InfEnv
inferUDecl eff (ULet (RecLeaf b@(_:>ann)) rhs) = case ann of
  Nothing -> do
    valAndTy <- inferSigma rhs eff
    return $ b@>valAndTy
  Just ty -> do
    ty' <- checkUType ty
    val <- checkSigma rhs eff ty'
    return $ b@>(val, ty')

inferUDecls :: Effect -> [UDecl] -> UInferM InfEnv
inferUDecls eff decls = do
  initEnv <- ask
  liftM snd $ flip runCatT initEnv $ forM_ decls $ \decl -> do
    cur <- look
    new <- lift $ local (const cur) $ inferUDecl eff decl
    extend new

inferULam :: ULamExpr -> UInferM (LamExpr, PiType EffectiveType)
inferULam (ULamExpr (RecLeaf b@(v:>ann)) body) = do
  argTy <- checkAnn ann
  buildLamExprAux (v:>argTy) $ \x@(Var v') -> do
    extendR (b @> (x, argTy)) $ do
      (resultVal, resultTy) <- inferRho body noEffect
      return (resultVal, makePi v' (noEffect, resultTy))

checkULam :: ULamExpr -> PiType EffectiveType -> UInferM LamExpr
checkULam (ULamExpr (RecLeaf b@(v:>ann)) body) piTy@(Pi argTy' _) = do
  argTy <- checkAnn ann
  constrainEq argTy' argTy
  buildLamExpr (v:>argTy) $ \x -> do
    let (lamEff, resultTy) = applyPi piTy x
    extendR (b @> (x, argTy')) $ do
      resultVal <- checkSigma body lamEff resultTy
      return resultVal

checkAnn :: Maybe UType -> UInferM Type
checkAnn ann = case ann of
  Just ty -> checkUType ty
  Nothing -> freshInfVar TyKind

checkUType :: UType -> UInferM Type
checkUType ty = do
  ty' <- checkRho ty noEffect TyKind
  scope <- getScope
  return $ reduceAtom scope ty'

checkEffect :: Effect -> Effect -> UInferM ()
checkEffect allowedEff eff = do
  eff' <- openUEffect eff
  constrainEq allowedEff eff'

freshInfVar :: Type -> UInferM Atom
freshInfVar ty = do
  (tv:>()) <- looks $ rename (rawName InferenceName "?" :> ()) . solverVars
  extend $ SolverEnv ((tv:>()) @> TyKind) mempty
  return $ Var $ tv:>ty

openUEffect :: Effect -> UInferM Effect
openUEffect eff = return eff -- TODO!

checkArrowHead :: ArrowHead -> ArrowHead -> UInferM ()
checkArrowHead ahReq ahOff = case (ahReq, ahOff) of
  (PlainArrow, PlainArrow) -> return ()
  (LinArrow,   PlainArrow) -> return ()
  (TabArrow,   TabArrow)   -> return ()
  _ -> throw TypeErr $   "Wrong arrow type:" ++
                       "\nExpected: " ++ pprint ahReq ++
                       "\nActual:   " ++ pprint ahOff

-- These *withArrowHead functions are adapters for `Expr` which doesn't use
-- arrowheads yet. TODO: remove them once we switch
lamWithArrowHead :: ArrowHead -> LamExpr -> Atom
lamWithArrowHead ah lam = case ah of
  PlainArrow    -> Con $ Lam Expl NonLin noEffect lam
  LinArrow      -> Con $ Lam Expl Lin    noEffect lam
  ImplicitArrow -> Con $ Lam (ImplicitArg "") NonLin noEffect lam
  TabArrow      -> error "should have table lambda in source program"

arrowTyWithArrowHead :: ArrowHead -> PiType EffectiveType -> Type
arrowTyWithArrowHead ah piTy = case ah of
  PlainArrow    -> ArrowType Expl NonLin piTy
  LinArrow      -> ArrowType Expl Lin    piTy
  ImplicitArrow -> ArrowType (ImplicitArg "") NonLin piTy
  TabArrow      -> TabType $ Pi a b
    where Pi a (eff,b) = piTy

appWithArrowHead :: ArrowHead -> Atom -> Atom -> CExpr
appWithArrowHead ah a b = case ah of
  PlainArrow    -> App NonLin a b
  LinArrow      -> App Lin    a b
  ImplicitArrow -> App NonLin a b
  TabArrow      -> TabGet a b

fromArrowType :: Type -> UInferM (ArrowHead, PiType EffectiveType)
fromArrowType (ArrowType im m piTy) = return (ah, piTy)
  where
    ah = case (im, m) of
      (Expl, NonLin)          -> PlainArrow
      (Expl, Lin)             -> LinArrow
      (ImplicitArg _, NonLin) -> ImplicitArrow
      _ -> error "Unexpected arrow"
fromArrowType (TabType (Pi a b)) = return (TabArrow, Pi a (noEffect, b))
fromArrowType ty = error $ "Not a pi type: " ++ pprint ty

-- === constraint solver ===

data SolverEnv = SolverEnv { solverVars :: Env Kind
                           , solverSub  :: Env Type }
type SolverT m = CatT SolverEnv m

runSolverT :: (MonadError Err m, Subst a, Pretty a)
           => CatT SolverEnv m a -> m a
runSolverT m = liftM fst $ flip runCatT mempty $ do
   ans <- m
   applyDefaults
   ans' <- zonk ans
   vs <- looks $ envNames . unsolved
   throwIf (not (null vs)) TypeErr $ "Ambiguous type variables: "
                                   ++ pprint vs ++ "\n\n" ++ pprint ans
   return ans'

applyDefaults :: MonadCat SolverEnv m => m ()
applyDefaults = do
  vs <- looks unsolved
  forM_ (envPairs vs) $ \(v, k) -> case k of
    TC MultKind   -> addSub v NonLin
    TC EffectKind -> addSub v noEffect
    _ -> return ()
  where addSub v ty = extend $ SolverEnv mempty ((v:>()) @> ty)

solveLocal :: (Pretty a, MonadCat SolverEnv m, MonadError Err m, Subst a)
           => m a -> m a
solveLocal m = do
  (ans, env@(SolverEnv freshVars sub)) <- scoped (m >>= zonk)
  extend $ SolverEnv (unsolved env) (sub `envDiff` freshVars)
  return ans

checkLeaks :: (Pretty a, MonadCat SolverEnv m, MonadError Err m, Subst a)
           => [Var] -> m a -> m a
checkLeaks tvs m = do
  (ans, env) <- scoped $ solveLocal m
  forM_ (solverSub env) $ \ty ->
    forM_ tvs $ \tv ->
      throwIf (tv `occursIn` ty) TypeErr $ "Leaked type variable: " ++ pprint tv
  extend env
  return ans

unsolved :: SolverEnv -> Env Kind
unsolved (SolverEnv vs sub) = vs `envDiff` sub

freshInferenceVar :: (MonadError Err m, MonadCat SolverEnv m) => Kind -> m Type
freshInferenceVar k = do
  tv <- looks $ rename (rawName InferenceName "?" :> k) . solverVars
  extend $ SolverEnv (tv @> k) mempty
  return (Var tv)

constrainEq :: (MonadCat SolverEnv m, MonadError Err m)
             => Type -> Type -> m ()
constrainEq t1 t2 = do
  t1' <- zonk t1
  t2' <- zonk t2
  let msg = "\nExpected: " ++ pprint t1'
         ++ "\n  Actual: " ++ pprint t2'
  addContext msg $ unify t1' t2'

zonk :: (Subst a, MonadCat SolverEnv m) => a -> m a
zonk x = do
  s <- looks solverSub
  return $ tySubst s x

-- TODO: check kinds
unify :: (MonadCat SolverEnv m, MonadError Err m)
       => Type -> Type -> m ()
unify t1 t2 = do
  t1' <- zonk t1
  t2' <- zonk t2
  vs <- looks solverVars
  case (t1', t2') of
    _ | t1' == t2' -> return ()
    (t, Var v) | v `isin` vs -> bindQ v t
    (Var v, t) | v `isin` vs -> bindQ v t
    (ArrowType im l (Pi a (eff, b)), ArrowType im' l' (Pi a' (eff', b')))
      | im == im' -> do
        -- TODO: think very hard about the leak checks we need to add here
        unify l l' >> unify a a' >> unify b b' >> unify eff eff'
    (Effect r t, Effect r' t') -> do
      let shared = rowMeet r r'
      forM_ shared $ \((e, et), (e', et')) -> do
        when (e /= e') $ throw TypeErr "Effect mismatch"
        unify et et'
      newTail <- liftM Just $ freshInferenceVar $ TC EffectKind
      matchTail t  $ Effect (envDiff r' shared) newTail
      matchTail t' $ Effect (envDiff r  shared) newTail
    (TabTy a b, TabTy a' b') -> unify a a' >> unify b b'
    (TC con, TC con') -> case (con, con') of
      (RefType a, RefType a') -> unify a a'
      (RecType r, RecType r') ->
        case zipWithRecord unify r r' of
          Nothing -> throw TypeErr ""
          Just unifiers -> void $ sequence unifiers
      (SumType (l, r), SumType (l', r')) -> unify l l' >> unify r r'
      (TypeApp f xs, TypeApp f' xs') | length xs == length xs' ->
        unify f f' >> zipWithM_ unify xs xs'
      _   -> throw TypeErr ""
    _   -> throw TypeErr ""

rowMeet :: Env a -> Env b -> Env (a, b)
rowMeet (Env m) (Env m') = Env $ M.intersectionWith (,) m m'

-- TODO: can we make this less complicated?
matchTail :: (MonadCat SolverEnv m, MonadError Err m)
          => Maybe Type -> Effect -> m ()
matchTail t ~eff@(Effect row t') = do
  vs <- looks solverVars
  case (t, t') of
    _                     | t == t' && row == mempty     -> return ()
    (Just (Var v), _) | v `isin` vs                  -> zonk eff               >>= bindQ v
    (_, Just (Var v)) | v `isin` vs && row == mempty -> zonk (Effect mempty t) >>= bindQ v
    _ -> throw TypeErr ""

-- TODO: check we're not unifying with deBruijn/skolem vars
bindQ :: (MonadCat SolverEnv m, MonadError Err m) => Var -> Type -> m ()
bindQ v t | v `occursIn` t = throw TypeErr (pprint (v, t))
          | otherwise = extend $ mempty { solverSub = v @> t }

occursIn :: Var -> Type -> Bool
occursIn v t = v `isin` freeVars t

instance Semigroup SolverEnv where
  -- TODO: as an optimization, don't do the subst when sub2 is empty
  -- TODO: make concatenation more efficient by maintaining a reverse-lookup map
  SolverEnv scope1 sub1 <> SolverEnv scope2 sub2 =
    SolverEnv (scope1 <> scope2) (sub1' <> sub2)
    where sub1' = fmap (tySubst sub2) sub1

instance Monoid SolverEnv where
  mempty = SolverEnv mempty mempty
  mappend = (<>)

tySubst :: Subst a => Env Type -> a -> a
tySubst env atom = subst (env, mempty) atom
