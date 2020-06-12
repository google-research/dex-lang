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
type UInferM = ReaderT InfEnv (ReaderT EffectRow (EmbedT (SolverT (Either Err))))

type SigmaType = Type  -- may     start with an implicit lambda
type RhoType   = Type  -- doesn't start with an implicit lambda
data RequiredTy a = Check a | Infer
data InferredTy a = Checked | Inferred a

inferModule :: TopEnv -> UModule -> Except Module
inferModule (TopEnv topEnv) m@(UModule imports exports decls) = do
  checkVars topEnv m
  let infEnv = fold [(v:>()) @> (Var (v:>getType x), getType x) | (v, x) <- envPairs topEnv]
  let scope  = fold [(v:>()) @> Just (Atom x)  | (v, x) <- envPairs topEnv]
  (infEnv', decls') <- runUInferM (inferUDecls decls) infEnv scope
  let combinedEnv = infEnv <> infEnv'
  let imports' = [v :> snd (infEnv      ! (v:>())) | v <- imports]
  let exports' = [v :> snd (combinedEnv ! (v:>())) | v <- exports]
  let resultVals = [fst    (combinedEnv ! (v:>())) | v <- exports]
  let body = wrapDecls decls' $ mkConsList resultVals
  return $ Module Nothing imports' exports' body

checkVars :: Env a -> UModule -> Except ()
checkVars env (UModule imports exports _) = do
  let unboundVars = filter (\v -> not $ (v:>()) `isin` env) imports
  unless (null unboundVars) $
    throw UnboundVarErr $ pprintList unboundVars
  let shadowedVars = filter (\v -> (v:>()) `isin` env) exports
  unless (null shadowedVars) $
    throw RepeatedVarErr $ pprintList shadowedVars

runUInferM :: (HasVars a, Pretty a)
           => UInferM a -> InfEnv -> Scope -> Except (a, [Decl])
runUInferM m env scope =
  runSolverT $ runEmbedT (runReaderT (runReaderT m env) Pure) scope

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

instantiateSigma :: (Atom, SigmaType) -> UInferM (Atom, RhoType)
instantiateSigma (f, Pi piTy@(Abs _ (ImplicitArrow, _))) = do
  x <- freshType $ absArgType piTy
  ans <- emit $ App f x
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
    x <- freshType argTy
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
      result <- emit $ Hof $ For dir lam
      return (result, Checked)
    Infer -> do
      allowedEff <- lift ask
      ~(lam, Pi (Abs n (_, a))) <- inferULam b (PlainArrow allowedEff) body
      result <- emit $ Hof $ For dir lam
      return (result, Inferred $ Pi $ Abs n (TabArrow, a))
  UApp arr f x -> do
    (fVal, fTy) <- inferRho f
    piTy <- fromPiType arr fTy
    fVal' <- zonk fVal
    xVal <- checkSigma x (absArgType piTy)
    ((arr', appTy), xVal') <- case piTy of
      Abs (NoName:>_) rhs -> return (rhs, xVal)
      _ -> do
        scope <- getScope
        let xVal' = reduceAtom scope xVal
        return (applyAbs piTy xVal', xVal')
    addEffects $ arrowEff arr'
    appVal <- emit $ App fVal' xVal'
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
      OpExpr  e -> emit $ Op e
      HofExpr e -> emit $ Hof e
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
inferUDecl (ULet (p, ann) rhs) = do
  (val,ty) <- case ann of
    Nothing -> inferSigma rhs
    Just ty -> do
      ty' <- checkUType ty
      val <- checkSigma rhs ty'
      return (val, ty')
  val' <- withPatHint p $ emit $ Atom val
  bindPat p (val', ty)

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
    -- TODO: check leaks here too
    withBindPat p (x, argTy) $ do
      (resultVal, resultTy) <- withEffects (arrowEff arr) $ inferSigma body
      let ty = Pi $ makeAbs v' (arr, resultTy)
      return ((arr, resultVal), ty)

checkULam :: UBinder -> UExpr -> PiType -> UInferM Atom
checkULam (p, ann) body piTy = do
  let argTy = absArgType piTy
  checkAnn ann >>= constrainEq argTy
  buildLam (patNameHint p :> argTy) $ \x@(Var v) ->
    checkLeaks [v] $ do
      let (arr, resultTy) = applyAbs piTy x
      withBindPat p (x, argTy) $ withEffects (arrowEff arr) $ do
        result <- checkSigma body resultTy
        return (arr, result)

checkUEff :: EffectRow -> UInferM EffectRow
checkUEff (EffectRow effs t) = do
   effs' <- forM effs $ \(effName, region) -> (effName,) <$> lookupVarName TyKind region
   t'    <- forM t $ \tv -> lookupVarName EffKind tv
   return $ EffectRow effs' t'
   where
     lookupVarName :: Type -> Name -> UInferM Name
     lookupVarName ty v = do
       -- TODO: more graceful errors on error
       (Var (v':>_), ty') <- asks (!(v:>()))
       constrainEq ty ty'
       return v'

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
    val' <- zonk val  -- ensure it has a pair type before unpacking
    x1 <- getFst val'
    x2 <- getSnd val'
    env1 <- bindPat p1 (x1,t1)
    env2 <- bindPat p2 (x2,t2)
    return $ env1 <> env2

patNameHint :: UPat -> Name
patNameHint (WithSrc _ (PatBind (v:>()))) = v
patNameHint _ = "pat"

withPatHint :: UPat -> UInferM a -> UInferM a
withPatHint p m = withNameHint (patNameHint p) m

checkAnn :: Maybe UType -> UInferM Type
checkAnn ann = case ann of
  Just ty -> checkUType ty
  Nothing -> freshType TyKind

checkUType :: UType -> UInferM Type
checkUType ty = do
  Just ty' <- reduceScoped $ withEffects Pure $ checkRho ty TyKind
  return ty'

checkArrow :: Arrow -> UArrow -> UInferM ()
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

fromPiType :: UArrow -> Type -> UInferM PiType
fromPiType _ (Pi piTy) = return piTy -- TODO: check arrow
fromPiType arr ty = do
  a <- freshType TyKind
  b <- freshType TyKind
  let piTy = Abs (NoName:>a) (fmap (const Pure) arr, b)
  constrainEq (Pi piTy) ty
  return piTy

fromPairType :: Type -> UInferM (Type, Type)
fromPairType (PairTy t1 t2) = return (t1, t2)
fromPairType ty = do
  a <- freshType TyKind
  b <- freshType TyKind
  constrainEq (PairTy a b) ty
  return (a, b)

addEffects :: EffectRow -> UInferM ()
addEffects eff = do
  eff' <- openEffectRow eff
  allowedEffects <- lift ask
  constrainEq (Eff allowedEffects) (Eff eff')

openEffectRow :: EffectRow -> UInferM EffectRow
openEffectRow (EffectRow effs Nothing) = extendEffRow effs <$> freshEff
openEffectRow effRow = return effRow

withEffects :: EffectRow -> UInferM a -> UInferM a
withEffects effs m = modifyAllowedEffects (const effs) m

modifyAllowedEffects :: (EffectRow -> EffectRow) -> UInferM a -> UInferM a
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
   applyDefaults
   ans' <- zonk ans
   vs <- looks $ envNames . unsolved
   throwIf (not (null vs)) TypeErr $ "Ambiguous type variables: "
                                   ++ pprint vs ++ "\n\n" ++ pprint ans'
   return ans'

applyDefaults :: MonadCat SolverEnv m => m ()
applyDefaults = do
  vs <- looks unsolved
  forM_ (envPairs vs) $ \(v, k) -> case k of
    EffKind -> addSub v $ Eff Pure
    _ -> return ()
  where addSub v ty = extend $ SolverEnv mempty ((v:>()) @> ty)

solveLocal :: HasVars a => UInferM a -> UInferM a
solveLocal m = do
  (ans, env@(SolverEnv freshVars sub)) <- scoped $ do
    -- This might get expensive. TODO: revisit once we can measure performance.
    (ans, embedEnv) <- zonk =<< embedScoped m
    embedExtend embedEnv
    return ans
  extend $ SolverEnv (unsolved env) (sub `envDiff` freshVars)
  return ans

checkLeaks :: HasVars a => [Var] -> UInferM a -> UInferM a
checkLeaks tvs m = do
  (ans, env) <- scoped $ solveLocal $ m
  forM_ (solverSub env) $ \ty ->
    forM_ tvs $ \tv ->
      throwIf (tv `occursIn` ty) TypeErr $ "Leaked type variable: " ++ pprint tv
  extend env
  return ans

unsolved :: SolverEnv -> Env Kind
unsolved (SolverEnv vs sub) = vs `envDiff` sub

freshType :: (MonadError Err m, MonadCat SolverEnv m) => Kind -> m Type
freshType EffKind = Eff <$> freshEff
freshType k = do
  tv <- freshVar k
  extend $ SolverEnv (tv @> k) mempty
  return $ Var tv

freshEff :: (MonadError Err m, MonadCat SolverEnv m) => m EffectRow
freshEff = do
  v <- freshVar ()
  extend $ SolverEnv (v@>EffKind) mempty
  return $ EffectRow [] $ Just $ varName v

freshVar :: MonadCat SolverEnv m => ann -> m (VarP ann)
freshVar ann = looks $ rename (rawName InferenceName "?" :> ann) . solverVars

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
  return $ scopelessSubst s x

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
       unifyEff (arrowEff arr) (arrowEff arr')
    (TC con, TC con') | void con == void con' ->
      zipWithM_ unify (toList con) (toList con')
    (Eff eff, Eff eff') -> unifyEff eff eff'
    _ -> throw TypeErr ""

unifyEff :: (MonadCat SolverEnv m, MonadError Err m)
         => EffectRow -> EffectRow -> m ()
unifyEff r1 r2 = do
  r1' <- zonk r1
  r2' <- zonk r2
  vs <- looks solverVars
  case (r1', r2') of
    _ | r1 == r2 -> return ()
    (r, EffectRow [] (Just v)) | (v:>()) `isin` vs -> bindQ (v:>EffKind) (Eff r)
    (EffectRow [] (Just v), r) | (v:>()) `isin` vs -> bindQ (v:>EffKind) (Eff r)
    (EffectRow effs1@(_:_) t1, EffectRow effs2@(_:_) t2) -> do
      let extras1 = effs1 `setDiff` effs2
      let extras2 = effs2 `setDiff` effs1
      newRow <- freshEff
      unifyEff (EffectRow [] t1) (extendEffRow extras2 newRow)
      unifyEff (extendEffRow extras1 newRow) (EffectRow [] t2)
    _ -> throw TypeErr ""

setDiff :: Eq a => [a] -> [a] -> [a]
setDiff xs ys = filter (`notElem` ys) xs

bindQ :: (MonadCat SolverEnv m, MonadError Err m) => Var -> Type -> m ()
bindQ v t | v `occursIn` t = throw TypeErr $ "Occurs check failure: " ++ pprint (v, t)
          | hasSkolems t = throw TypeErr "Can't unify with skolem vars"
          | otherwise = extend $ mempty { solverSub = v @> t }

hasSkolems :: HasVars a => a -> Bool
hasSkolems x = not $ null [() | Name Skolem _ _ <- envNames $ freeVars x]

occursIn :: HasVars a => Var -> a -> Bool
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
    where sub1' = fmap (scopelessSubst sub2) sub1

instance Monoid SolverEnv where
  mempty = SolverEnv mempty mempty
  mappend = (<>)
