-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module Inference (inferModule) where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Except hiding (Except)
import Data.Foldable (fold, toList)
import qualified Data.Map.Strict as M
import Data.String (fromString)
import Data.Text.Prettyprint.Doc

import Syntax
import Embed  hiding (sub)
import Env
import Type
import PPrint
import Cat

-- TODO: consider just carrying an `Atom` (since the type is easily recovered)
type InfEnv = Env (Atom, Type)
type UInferM = ReaderT InfEnv (ReaderT Effects (EmbedT (SolverT (Either Err))))

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
  (env', decls') <- runUInferM (inferUDecls decls) env
  let combinedEnv = env <> env'
  let imports' = [v :> snd (env         ! (v:>())) | v <- imports]
  let exports' = [v :> snd (combinedEnv ! (v:>())) | v <- exports]
  let resultVals = [fst    (combinedEnv ! (v:>())) | v <- exports]
  let body = wrapDecls decls' $ mkConsList resultVals
  return (Module Nothing imports' exports' body, (fmap snd env', mempty))

runUInferM :: (HasVars a, Pretty a) => UInferM a -> InfEnv -> Except (a, [Decl])
runUInferM m env =
  runSolverT $ runEmbedT (runReaderT (runReaderT m env) Pure) scope
  where scope = fmap (const Nothing) env

infEnvFromTopEnv :: TopEnv -> InfEnv
infEnvFromTopEnv (TopEnv (tyEnv, _) substEnv _) =
  fold [v' @> (substEnv ! v', ty) | (v, ty) <- envPairs tyEnv, let v' = v:>()]

checkSigma :: UExpr -> SigmaType -> UInferM Atom
checkSigma expr sTy = case sTy of
  Pi piTy@(Abs _ (ImplicitArrow, _)) -> case expr of
    WithSrc _ (ULam b ImplicitArrow body) ->
      checkULam b body piTy
    _ -> do
      buildLam ("a":> absArgType piTy) $ \x ->
        liftM (ImplicitArrow,) $ checkSigma expr $ snd $ applyAbs piTy x
  _ -> checkRho expr sTy

inferSigma :: UExpr -> UInferM (Atom, SigmaType)
inferSigma (WithSrc pos expr) = case expr of
  ULam pat ImplicitArrow body -> addSrcContext (Just pos) $
    inferULam pat ImplicitArrow body
  _ ->
    inferRho (WithSrc pos expr)

checkRho :: UExpr -> RhoType -> UInferM Atom
checkRho expr ty = do
  (val, Checked) <- checkOrInferRho expr (Check ty)
  return val

inferRho :: UExpr -> UInferM (Atom, RhoType)
inferRho expr = do
  (val, Inferred ty) <- checkOrInferRho expr Infer
  return (val, ty)

-- This is necessary so that embed's `getType` doesn't get confused
-- TODO: figure out a better way. It's probably enough to just solve locally as
-- part of leak checking when we construct dependent lambdas.
emitZonked :: Expr -> UInferM Atom
emitZonked expr = zonk expr >>= emit

instantiateSigma :: (Atom, SigmaType) -> UInferM (Atom, RhoType)
instantiateSigma (f, Pi piTy@(Abs _ (ImplicitArrow, _))) = do
  x <- freshInfVar $ absArgType piTy
  ans <- emitZonked $ App f x
  let (_, ansTy) = applyAbs piTy x
  instantiateSigma (ans, ansTy)
instantiateSigma (x, ty) = return (x, ty)

checkOrInferRho :: UExpr -> RequiredTy RhoType
                -> UInferM (Atom, InferredTy RhoType)
checkOrInferRho (WithSrc pos expr) reqTy =
 addSrcContext (Just pos) $ case expr of
  UVar v -> asks (! v) >>= instantiateSigma >>= matchRequirement
  ULam (p, ann) ImplicitArrow body -> do
    argTy <- checkAnn ann
    x <- freshInfVar argTy
    withBindPat p (x, argTy) $ checkOrInferRho body reqTy
  ULam b arr body -> case reqTy of
    Check ty -> do
      piTy@(Abs _ (arrReq, _)) <- fromPiType arr ty
      checkArrow arrReq arr
      lam <- checkULam b body piTy
      return (lam, Checked)
    Infer -> do
      (lam, ty) <- inferULam b (fmap (const Pure) arr) body
      return (lam, Inferred ty)
  UFor dir b body -> case reqTy of
    Check ty -> do
      Abs n (arr, a) <- fromPiType TabArrow ty
      unless (arr == TabArrow) $
        throw TypeErr $ "Not an table arrow type: " ++ pprint arr
      allowedEff <- lift ask
      lam <- checkULam b body $ Abs n (PlainArrow allowedEff, a)
      result <- emitZonked $ Hof $ For dir lam
      return (result, Checked)
    Infer -> do
      allowedEff <- lift ask
      ~(lam, Pi (Abs n (_, a))) <- inferULam b (PlainArrow allowedEff) body
      result <- emitZonked $ Hof $ For dir lam
      return (result, Inferred $ Pi $ Abs n (TabArrow, a))
  UApp arr f x -> do
    (fVal, fTy) <- inferRho f
    piTy <- fromPiType arr fTy
    xVal <- checkSigma x (absArgType piTy)
    let (arr', appTy) = applyAbs piTy xVal
    checkEffectsAllowed $ arrowEff arr'
    appVal <- emitZonked $ App fVal xVal
    instantiateSigma (appVal, appTy) >>= matchRequirement
  UPi (p, a) arr ty -> do
    -- TODO: make sure there's no effect if it's an implicit or table arrow
    -- TODO: check leaks
    a'  <- checkUType a
    abs <- buildAbs (patNameHint p :> a') $ \x ->
             withBindPat p (x, a') $
               (,) <$> mapM checkUEff arr <*> checkUType ty
    matchRequirement (Pi abs, TyKind)
  UDecl decl body -> do
    env <- inferUDecl decl
    extendR env $ checkOrInferRho body reqTy
  UTabCon xs ann -> inferTabCon xs ann >>= matchRequirement
  UPrimExpr prim -> do
    prim' <- traverse lookupName prim
    val <- case prim' of
      TCExpr  e -> return $ TC e
      ConExpr e -> return $ Con e
      OpExpr  e -> emitZonked $ Op e
      HofExpr e -> emitZonked $ Hof e
    matchRequirement (val, getType val)
    where lookupName  v = fst <$> asks (! (v:>()))
  where
    matchRequirement :: (Atom, Type) -> UInferM (Atom, InferredTy RhoType)
    matchRequirement (x, ty) = liftM (x,) $
      case reqTy of
        Infer -> return $ Inferred ty
        Check req -> do
          constrainEq req ty
          return Checked

inferUDecl :: UDecl -> UInferM InfEnv
inferUDecl (ULet (p, ann) rhs) = case ann of
  Nothing -> do
    valAndTy <- withPatHint p $ inferSigma rhs
    bindPat p valAndTy
  Just ty -> do
    ty' <- checkUType ty
    val <- withPatHint p $ checkSigma rhs ty'
    bindPat p (val, ty')

inferUDecls :: [UDecl] -> UInferM InfEnv
inferUDecls decls = do
  initEnv <- ask
  liftM snd $ flip runCatT initEnv $ forM_ decls $ \decl -> do
    cur <- look
    new <- lift $ local (const cur) $ inferUDecl decl
    extend new

inferULam :: UBinder -> Arrow -> UExpr -> UInferM (Atom, Type)
inferULam (p, ann) arr body = do
  argTy <- checkAnn ann
  buildLamAux (patNameHint p :> argTy) $ \x@(Var v') -> do
    withBindPat p (x, argTy) $ do
      (resultVal, resultTy) <- withEffects (arrowEff arr) $ inferSigma body
      let ty = Pi $ makeAbs v' (arr, resultTy)
      return ((arr, resultVal), ty)

checkULam :: UBinder -> UExpr -> PiType -> UInferM Atom
checkULam (p, ann) body piTy = do
  let argTy = absArgType piTy
  checkAnn ann >>= constrainEq argTy
  buildLam (patNameHint p :> argTy) $ \x -> do
    let (arr, resultTy) = applyAbs piTy x
    withBindPat p (x, argTy) $ withEffects (arrowEff arr) $ do
      result <- checkSigma body resultTy
      return (arr, result)

withBindPat :: UPat -> (Atom, Type) -> UInferM a -> UInferM a
withBindPat pat valTy m = do
  env <- bindPat pat valTy
  extendR env m

bindPat :: UPat -> (Atom, Type) -> UInferM InfEnv
bindPat (WithSrc pos pat) (val,ty) = addSrcContext (Just pos) $ case pat of
  PatBind b -> return (b @> (val, ty))
  PatUnit -> constrainEq UnitTy ty >> return mempty
  PatPair p1 p2 -> do
    (t1, t2) <- fromPairType ty
    x1 <- getFst val
    x2 <- getSnd val
    env1 <- bindPat p1 (x1,t1)
    env2 <- bindPat p2 (x2,t2)
    return $ env1 <> env2

patNameHint :: UPat -> Name
patNameHint (WithSrc _ (PatBind (v:>()))) = v
patNameHint _ = "pat"

withPatHint :: UPat -> UInferM a -> UInferM a
withPatHint p m = withNameHint (patNameHint p) m

checkUEff :: UEffects -> UInferM Effects
checkUEff (UEffects effs tailVar) = case effs of
  [] -> case tailVar of
    Nothing -> return Pure
    Just v  -> checkRho v (TC EffectsKind)
  (effName, region):rest -> do
    region' <- checkRho region TyKind
    rest' <- checkUEff (UEffects rest tailVar)
    return $ Eff $ ExtendEff (effName, region') rest'

checkAnn :: Maybe UType -> UInferM Type
checkAnn ann = case ann of
  Just ty -> checkUType ty
  Nothing -> freshInfVar TyKind

checkUType :: UType -> UInferM Type
checkUType ty = do
  Just ty' <- reduceScoped $ withEffects Pure $ checkRho ty TyKind
  return ty'

freshInfVar :: Type -> UInferM Atom
freshInfVar ty = do
  (tv:>()) <- looks $ rename (rawName InferenceName "?" :> ()) . solverVars
  extend $ SolverEnv ((tv:>()) @> TyKind) mempty
  extendScope ((tv:>())@>Nothing)
  return $ Var $ tv:>ty

checkArrow :: Arrow -> ULamArrow -> UInferM ()
checkArrow ahReq ahOff = case (ahReq, ahOff) of
  (PlainArrow _, PlainArrow ()) -> return ()
  (LinArrow,     PlainArrow ()) -> return ()
  (TabArrow, TabArrow) -> return ()
  _ -> throw TypeErr $   "Wrong arrow type:" ++
                       "\nExpected: " ++ pprint ahReq ++
                       "\nActual:   " ++ pprint (fmap (const Pure) ahOff)

inferTabCon :: [UExpr] -> Maybe UType -> UInferM (Atom, Type)
inferTabCon xs ann = do
  (n, ty) <- inferTabTy xs ann
  let tabTy = n==>ty
  xs' <- mapM (flip checkRho ty) xs
  ans <- emitOp $ TabCon tabTy xs'
  return (ans, tabTy)

inferTabTy :: [UExpr] -> Maybe UType -> UInferM (Type, Type)
inferTabTy xs ann = case ann of
  Just ty -> do
    ty' <- checkUType ty
    case ty' of
      TabTy n a -> do
        unless (indexSetConcreteSize n == Just (length xs)) $
           throw TypeErr $ "Table size doesn't match annotation"
        return (n, a)
      _ -> throw TypeErr $ "Table constructor annotation must be a table type"
  Nothing -> case xs of
   [] -> throw TypeErr $ "Empty table constructor must have type annotation"
   (x:_) -> do
    (_, ty) <- inferRho x
    return (FixedIntRange 0 (length xs), ty)

fromPiType :: ULamArrow -> Type -> UInferM PiType
fromPiType _ (Pi piTy) = return piTy -- TODO: check arrow
fromPiType arr ty = do
  a <- freshInfVar TyKind
  b <- freshInfVar TyKind
  let piTy = Abs (NoName:>a) (fmap (const Pure) arr, b)
  constrainEq (Pi piTy) ty
  return piTy

fromPairType :: Type -> UInferM (Type, Type)
fromPairType (PairTy t1 t2) = return (t1, t2)
fromPairType ty = do
  a <- freshInfVar TyKind
  b <- freshInfVar TyKind
  constrainEq (PairTy a b) ty
  return (a, b)

checkEffectsAllowed :: Effects -> UInferM ()
checkEffectsAllowed eff = do
  eff' <- zonk eff
  allowedEffects <- lift ask
  case forbiddenEffects allowedEffects eff' of
    Pure -> return ()
    extraEffs -> throw TypeErr $ "Unexpected effects: " ++ pprint extraEffs

withEffects :: Effects -> UInferM a -> UInferM a
withEffects effs m = modifyAllowedEffects (const effs) m

modifyAllowedEffects :: (Effects -> Effects) -> UInferM a -> UInferM a
modifyAllowedEffects f m = do
  env <- ask
  lift $ local f (runReaderT m env)

-- === constraint solver ===

data SolverEnv = SolverEnv { solverVars :: Env Kind
                           , solverSub  :: Env Type }
type SolverT m = CatT SolverEnv m

runSolverT :: (MonadError Err m, HasVars a, Pretty a)
           => CatT SolverEnv m a -> m a
runSolverT m = liftM fst $ flip runCatT mempty $ do
   ans <- m >>= zonk
   vs <- looks $ envNames . unsolved
   throwIf (not (null vs)) TypeErr $ "Ambiguous type variables: "
                                   ++ pprint vs ++ "\n\n" ++ pprint ans
   return ans

solveLocal :: (Pretty a, MonadCat SolverEnv m, MonadError Err m, HasVars a)
           => m a -> m a
solveLocal m = do
  (ans, env@(SolverEnv freshVars sub)) <- scoped (m >>= zonk)
  extend $ SolverEnv (unsolved env) (sub `envDiff` freshVars)
  return ans

checkLeaks :: (Pretty a, MonadCat SolverEnv m, MonadError Err m, HasVars a)
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
  let ((t1Pretty, t2Pretty), infVars) = renameForPrinting (t1', t2')
  let msg = "\nExpected: " ++ pprint t1Pretty
         ++ "\n  Actual: " ++ pprint t2Pretty
         ++ (if null infVars then "" else "\nSolving for: " ++ pprint infVars)
  addContext msg $ unify t1' t2'

zonk :: (HasVars a, MonadCat SolverEnv m) => a -> m a
zonk x = do
  s <- looks solverSub
  return $ tySubst s x

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
    (Pi piTy, Pi piTy') -> do
       unify (absArgType piTy) (absArgType piTy')
       let v = Var $ freshSkolemVar (piTy, piTy') (absArgType piTy)
       -- TODO: think very hard about the leak checks we need to add here
       let (arr , resultTy ) = applyAbs piTy  v
       let (arr', resultTy') = applyAbs piTy' v
       unify resultTy resultTy'
       unify (arrowEff arr) (arrowEff arr')
    -- (Effect r t, Effect r' t') ->
    (TC con, TC con') | void con == void con' ->
      zipWithM_ unify (toList con) (toList con')
    _   -> throw TypeErr ""

rowMeet :: Env a -> Env b -> Env (a, b)
rowMeet (Env m) (Env m') = Env $ M.intersectionWith (,) m m'

bindQ :: (MonadCat SolverEnv m, MonadError Err m) => Var -> Type -> m ()
bindQ v t | v `occursIn` t = throw TypeErr (pprint (v, t))
          | hasSkolems t = throw TypeErr "Can't unify with skolem vars"
          | otherwise = extend $ mempty { solverSub = v @> t }

hasSkolems :: HasVars a => a -> Bool
hasSkolems x = not $ null [() | Name Skolem _ _ <- envNames $ freeVars x]

occursIn :: Var -> Type -> Bool
occursIn v t = v `isin` freeVars t

renameForPrinting :: HasVars a => a -> (a, [Var])
renameForPrinting x = (scopelessSubst substEnv x, newNames)
  where
    fvs = freeVars x
    infVars = filter ((==InferenceName) . nameSpace . varName) $ envAsVars fvs
    newNames = [ rename (fromString name:> varAnn v) fvs
               | (v, name) <- zip infVars nameList]
    substEnv = fold $ zipWith (\v v' -> v@>Var v') infVars newNames
    nameList = map (:[]) ['a'..'z'] ++ map show [(0::Int)..]

instance Semigroup SolverEnv where
  -- TODO: as an optimization, don't do the subst when sub2 is empty
  -- TODO: make concatenation more efficient by maintaining a reverse-lookup map
  SolverEnv scope1 sub1 <> SolverEnv scope2 sub2 =
    SolverEnv (scope1 <> scope2) (sub1' <> sub2)
    where sub1' = fmap (tySubst sub2) sub1

instance Monoid SolverEnv where
  mempty = SolverEnv mempty mempty
  mappend = (<>)

tySubst :: HasVars a => Env Type -> a -> a
tySubst env atom = subst (env, mempty) atom
