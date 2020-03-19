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
import Data.Foldable (toList, fold)
import Data.Text.Prettyprint.Doc

import Syntax
import Env
import Record
import Type
import PPrint
import Cat
import Subst

type InferM a = ReaderT TypeEnv (SolverT (Either Err)) a

inferModule :: TopEnv -> FModule -> Except FModule
inferModule (TopEnv tyEnv subEnv _) m = do
  let (Module (imports, exports) (FModBody body _)) = m
  checkImports tyEnv m
  let tySubEnv = flip envMapMaybe subEnv $ \case L _ -> Nothing; T ty -> Just ty
  (body', tySub) <- expandTyAliases tySubEnv body
  (body'', envOut) <- runInferM tyEnv $ catTraverse (inferDecl noEffect) body'
  let imports' = imports `envIntersect` tyEnv
  let exports' = exports `envIntersect` (tyEnv <> envOut <> tySubEnvType)
       where tySubEnvType = fmap (T . getKind) tySub
  return $ Module (imports', exports') (FModBody body'' tySub)

runInferM :: (TySubst a, Pretty a) => TypeEnv -> InferM a -> Except a
runInferM env m = runSolverT (runReaderT m env)

expandTyAliases :: Env Type -> [FDecl] -> Except ([FDecl], Env Type)
expandTyAliases envInit decls =
  liftM snd $ flip runCatT ([], envInit) $ forM_ decls expandTyAliasDecl

expandTyAliasDecl :: FDecl -> CatT ([FDecl], Env Type) (Either Err) ()
expandTyAliasDecl decl = do
  env <- looks snd
  case decl of
    TyDef v ty -> do
      let ty' = tySubst env ty
      ty'' <- liftEither $ runInferKinds mempty ty'
      extend ([], v @> ty'')
    _ -> extend ([tySubst env decl], mempty)

checkImports :: TypeEnv -> FModule -> Except ()
checkImports env m = do
  let unboundVars = envNames $ imports `envDiff` env
  unless (null unboundVars) $ throw UnboundVarErr $ pprintList unboundVars
  let shadowedVars = envNames $ exports `envIntersect` env
  unless (null shadowedVars) $ throw RepeatedVarErr $ pprintList shadowedVars
  where (imports, exports) = moduleType m

inferDecl :: Effect -> FDecl -> InferM (FDecl, TypeEnv)
inferDecl eff decl = case decl of
  LetMono p bound -> do
    -- TOOD: better errors - infer polymorphic type to suggest annotation
    liftEither $ checkPatShadow p
    p' <- annotPat p
    bound' <- check bound (eff, getType p')
    return (LetMono p' bound', foldMap asEnv p')
  LetPoly b@(v:>ty) tlam -> do
    ty' <- inferKinds ty
    tlam' <- checkTLam ty' tlam
    return (LetPoly (v:>ty') tlam', b @> L ty')
  FRuleDef ann annTy tlam -> do
    -- TODO: check against expected type for the particular rule
    annTy' <- inferKinds annTy
    tlam' <- checkTLam annTy' tlam
    return (FRuleDef ann annTy' tlam', mempty)
  TyDef _ _ -> error "Shouldn't have TyDef left"

check :: FExpr -> EffectiveType -> InferM FExpr
check expr reqEffTy@(allowedEff, reqTy) = case expr of
  FDecl decl body -> do
    (decl', env') <- inferDecl allowedEff decl
    body' <- extendR env' $ check body reqEffTy
    return $ FDecl decl' body'
  FVar v -> do
    ty <- asks $ fromL . (! v)
    case ty of
      Forall _ _ _ -> check (fTyApp v []) reqEffTy
      _ -> constrainReq ty >> return (FVar (varName v :> ty))
  FPrimExpr (OpExpr (TApp (FVar v) ts)) -> do
    ty <- asks $ fromL . (! v)
    case ty of
      Forall bs _ body -> do
        let kinds = map varAnn bs
        ts' <- mapM inferKinds ts
        zipWithM_ checkKindIs kinds ts'
        vs <- mapM freshInferenceVar (drop (length ts) kinds)
        let ts'' = ts' ++ vs
        let env = fold [tv @> T t | (tv, t) <- zip bs ts'']
        constrainReq (subst (env, mempty) body)
        return $ fTyApp (varName v :> ty) ts''
      _ -> throw TypeErr "Unexpected type application"
  FPrimExpr (OpExpr op) -> do
    opTy <- generateOpSubExprTypes op
    -- TODO: don't ignore explicit annotations (via `snd`)
    (eff, ansTy) <- traverseOpType (fmapExpr opTy snd snd snd)
                      (\t1 t2 -> constrainEq t1 t2 (pprint expr))
                      (\_ _ -> return ())
                      (\_ _ -> return ())
    op' <- traverseExpr opTy
      (uncurry checkAnn) (uncurry checkPure) (uncurry checkLam)
    constrainReq ansTy
    eff' <- openEffect eff
    constrainEq allowedEff eff' (pprint expr)
    return $ FPrimExpr $ OpExpr $ op'
  FPrimExpr (ConExpr con) -> do
    conTy <- generateConSubExprTypes con
    -- TODO: don't ignore explicit annotations (via `snd`)
    ansTy <- traverseConType (fmapExpr conTy snd snd snd)
               (\t1 t2 -> constrainEq t1 t2 (pprint expr))
               (\_ _ -> return ())
               (\_ _ -> return ())
    constrainReq ansTy
    con' <- traverseExpr conTy
      (uncurry checkAnn) (uncurry checkPure) (uncurry checkLam)
    return $ FPrimExpr $ ConExpr con'
  Annot e annTy -> do
    -- TODO: check that the annotation is a monotype
    constrainReq annTy
    check e reqEffTy
  SrcAnnot e pos -> do
    e' <- addSrcContext (Just pos) $ check e reqEffTy
    return $ SrcAnnot e' pos
  where
    constrainReq ty = constrainEq reqTy  ty       (pprint expr)

checkPure :: FExpr -> Type -> InferM FExpr
checkPure expr ty = check expr (noEffect, ty)

checkTLam :: Type -> FTLam -> InferM FTLam
checkTLam ~(Forall tbs qs tyBody) (FTLam _ _ tlamBody) = do
  let env = foldMap tbind tbs
  liftM (FTLam tbs qs) $ checkLeaks tbs $ extendR env $
    check tlamBody (noEffect, tyBody)

checkLam :: FLamExpr -> (Type, EffectiveType) -> InferM FLamExpr
checkLam (FLamExpr p _ body) (a, b@(eff,_)) = do
  p' <- checkPat p a
  body' <- extendR (foldMap asEnv p') (check body b)
  return $ FLamExpr p' eff body'

checkPat :: Pat -> Type -> InferM Pat
checkPat p ty = do
  liftEither $ checkPatShadow p
  p' <- annotPat p
  constrainEq ty (getType p') (pprint p)
  return p'

fTyApp :: Var -> [Type] -> FExpr
fTyApp v tys = FPrimExpr $ OpExpr $ TApp (FVar v) tys

checkPatShadow :: Pat -> Except ()
checkPatShadow pat = do
  let dups = filter (/= underscore) $ findDups $ map varName $ toList pat
  unless (null dups) $ throw RepeatedVarErr $ pprintList dups
  where underscore = rawName SourceName "_"

findDups :: Eq a => [a] -> [a]
findDups [] = []
findDups (x:xs) | x `elem` xs = x : findDups xs
                | otherwise   =     findDups xs

checkAnn :: Type -> Type -> InferM Type
checkAnn NoAnn ty = return ty
checkAnn ty' ty   = constrainEq ty' ty "annotation" >> return ty

openEffect :: Effect -> InferM Effect
openEffect eff = do
  ~(Effect row tailVar) <- zonk eff
  case tailVar of
    Nothing -> liftM (Effect row . Just) $ freshInferenceVar EffectKind
    Just _  -> return $ Effect row tailVar

generateConSubExprTypes :: PrimCon ty e lam
  -> InferM (PrimCon (ty, Type) (e, Type) (lam, (Type, EffectiveType)))
generateConSubExprTypes con = case con of
  Lam l lam -> do
    l' <- freshInferenceVar MultKind
    (a, b) <- freshLamType
    return $ Lam (l,l') (lam, (a,b))
  LensCon (LensCompose l1 l2) -> do
    a <- freshQ
    b <- freshQ
    c <- freshQ
    return $ LensCon $ LensCompose (l1, Lens a b) (l2, Lens b c)
  _ -> traverseExpr con (doMSnd freshQ) (doMSnd freshQ) (doMSnd freshLamType)

generateOpSubExprTypes :: PrimOp ty e lam
  -> InferM (PrimOp (ty, Type) (e, Type) (lam, (Type, EffectiveType)))
generateOpSubExprTypes op = case op of
  App l f x -> do
    l'  <- freshInferenceVar MultKind
    (a, b) <- freshLamType
    return $ App (l,l') (f, ArrowType l' a b) (x, a)
  TabGet xs i -> do
    n <- freshQ
    a <- freshQ
    return $ TabGet (xs, TabType n a) (i, n)
  LensGet x l -> do
    a <- freshQ
    b <- freshQ
    return $ LensGet (x,a) (l, Lens a b)
  PrimEffect l m -> do
    l'   <- liftM2 Lens freshQ freshQ
    m'   <- traverse (doMSnd freshQ) m
    return $ PrimEffect (l, l') m'
  RunLinReader r f -> do
    r' <- freshQ
    a  <- freshQ
    tailVar <- freshInferenceVar EffectKind
    let fTy = (unitTy, (Effect (linReaderRow r') (Just tailVar), a))
    return $ RunLinReader (r, r') (f, fTy)
  RunReader r f -> do
    r' <- freshQ
    a  <- freshQ
    tailVar <- freshInferenceVar EffectKind
    let fTy = (unitTy, (Effect (readerRow r') (Just tailVar), a))
    return $ RunReader (r, r') (f, fTy)
  RunWriter f -> do
    w  <- freshQ
    a  <- freshQ
    tailVar <- freshInferenceVar EffectKind
    let fTy = (unitTy, (Effect (writerRow w) (Just tailVar), a))
    return $ RunWriter (f, fTy)
  RunState s f -> do
    s' <- freshQ
    a  <- freshQ
    tailVar <- freshInferenceVar EffectKind
    let fTy = (unitTy, (Effect (stateRow s') (Just tailVar), a))
    return $ RunState (s, s') (f, fTy)
  _ -> traverseExpr op (doMSnd freshQ) (doMSnd freshQ) (doMSnd freshLamType)

freshLamType :: InferM (Type, EffectiveType)
freshLamType = do
  a <- freshQ
  b <- freshQ
  eff <- liftM (Effect mempty . Just) $ freshInferenceVar EffectKind
  return (a, (eff, b))

doMSnd :: Monad m => m b -> a -> m (a, b)
doMSnd m x = do { y <- m; return (x, y) }

annotPat :: Pat -> InferM Pat
annotPat pat = traverse annotBinder pat

annotBinder :: Var -> InferM Var
annotBinder (v:>ann) = liftM (v:>) (fromAnn ann)

fromAnn :: Type -> InferM Type
fromAnn NoAnn = freshQ
fromAnn ty    = inferKinds ty

asEnv :: Var -> TypeEnv
asEnv b = b @> L (varAnn b)

-- === kind inference ===

type InferKindM a = CatT TypeEnv (Either Err) a

inferKinds :: Type -> InferM Type
inferKinds ty = do
  env <- ask
  liftEither $ runInferKinds env ty

runInferKinds :: TypeEnv -> Type -> Except Type
runInferKinds env ty = liftM fst $ runCatT (inferKindsM TyKind ty) env

inferKindsM :: Kind -> Type -> InferKindM Type
inferKindsM kind ty = case ty of
  TypeVar tv@(v:>_) -> do
    x <- looks $ flip envLookup tv
    case x of
      Just (T NoKindAnn) -> extend (tv @> T kind)
      Just (T k)         -> checkKindEq kind k
      _                  -> error "Lookup failed"
    return $ TypeVar (v:>kind)
  Forall vs qs body -> liftM fst $ scoped $ do
    extend (foldMap tbind vs)
    body' <- inferKindsM TyKind body
    vs' <- mapM addKindAnn vs
    let substEnv = fold [v @> T (TypeVar v') | (v, v') <- zip vs vs']
    let qs' = map (subst (substEnv, mempty)) $ qs ++ impliedClasses body
    return $ Forall vs' qs' body'
  TypeAlias vs body -> do
    extend (foldMap tbind vs)
    body' <- inferKindsM TyKind body
    vs' <- mapM addKindAnn vs
    return $ TypeAlias vs' body'
  _ -> traverseType inferKindsM ty

addKindAnn :: TVar -> InferKindM TVar
addKindAnn tv@(v:>_) = do
  env <- look
  case envLookup env tv of
    Just (T NoKindAnn) ->
      throw KindErr $ "Ambiguous kind for type variable: " ++ pprint tv
    Just (T k) -> return (v:>k)
    _ -> error "Lookup failed"

-- TODO: this is quite ad-hoc
impliedClasses :: Type -> [TyQual]
impliedClasses ty =  map (flip TyQual Data  ) (dataVars   ty)
                  <> map (flip TyQual IdxSet) (idxSetVars ty)

idxSetVars :: Type -> [TVar]
idxSetVars ty = case ty of
  ArrowType _ a (_, b) -> recur a <> recur b
  TabType a b   -> map (:>NoKindAnn) (envNames (freeVars a)) <> recur b
  RecType r     -> foldMap recur r
  _             -> []
  where recur = idxSetVars

dataVars :: Type -> [TVar]
dataVars ty = case ty of
  ArrowType _ a (_, b) -> recur a <> recur b
  TabType _ b   -> map (:>NoKindAnn) (envNames (freeVars b))
  RecType r     -> foldMap recur r
  _             -> []
  where recur = dataVars

-- === constraint solver ===

data SolverEnv = SolverEnv { solverVars :: Env Kind
                           , solverSub  :: Env Type }
type SolverT m = CatT SolverEnv m

runSolverT :: (MonadError Err m, TySubst a, Pretty a)
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
    MultKind   -> addSub v NonLin
    EffectKind -> addSub v noEffect
    _ -> return ()
  where addSub v ty = extend $ SolverEnv mempty ((v:>()) @> ty)

solveLocal :: (Pretty a, MonadCat SolverEnv m, MonadError Err m, TySubst a)
           => m a -> m a
solveLocal m = do
  (ans, env@(SolverEnv freshVars sub)) <- scoped (m >>= zonk)
  extend $ SolverEnv (unsolved env) (sub `envDiff` freshVars)
  return ans

checkLeaks :: (Pretty a, MonadCat SolverEnv m, MonadError Err m, TySubst a)
           => [TVar] -> m a -> m a
checkLeaks tvs m = do
  (ans, env) <- scoped $ solveLocal m
  forM_ (solverSub env) $ \ty ->
    forM_ tvs $ \tv ->
      throwIf (tv `occursIn` ty) TypeErr $ "Leaked type variable: " ++ pprint tv
  extend env
  return ans

unsolved :: SolverEnv -> Env Kind
unsolved (SolverEnv vs sub) = vs `envDiff` sub

freshQ :: MonadCat SolverEnv m => m Type
freshQ = freshInferenceVar $ TyKind

freshInferenceVar :: MonadCat SolverEnv m => Kind -> m Type
freshInferenceVar k = do
  tv <- looks $ rename (rawName InferenceName "?" :> k) . solverVars
  extend $ SolverEnv (tv @> k) mempty
  return (TypeVar tv)

constrainEq :: (MonadCat SolverEnv m, MonadError Err m)
             => Type -> Type -> String -> m ()
constrainEq t1 t2 s = do
  t1' <- zonk t1
  t2' <- zonk t2
  let msg = "\nExpected: " ++ pprint t1'
         ++ "\n  Actual: " ++ pprint t2'
         ++ "\nIn: "       ++ s
  addContext msg $ unify t1' t2'

zonk :: (TySubst a, MonadCat SolverEnv m) => a -> m a
zonk x = do
  s <- looks solverSub
  return $ tySubst s x

-- TODO: check kinds
unify :: (MonadCat SolverEnv m, MonadError Err m)
       => Type -> Type -> m ()
unify t1 t2 = do
  t1' <- zonk t1
  t2' <- zonk t2
  case (t1', t2') of
    _ | t1' == t2' -> return ()
    (t, TypeVar v) | isQ v -> bindQ v t
    (TypeVar v, t) | isQ v -> bindQ v t
    (ArrowType l a (eff, b), ArrowType l' a' (eff', b')) ->
      unify l l' >> unify a a' >> unify b b' >> unify eff eff'
    (TabType a b, TabType a' b') -> unify a a' >> unify b b'
    (Lens a b, Lens a' b') -> unify a a' >> unify b b'
    (RecType r, RecType r') ->
      case zipWithRecord unify r r' of
        Nothing -> throw TypeErr ""
        Just unifiers -> void $ sequence unifiers
    (TypeApp f xs, TypeApp f' xs') | length xs == length xs' ->
      unify f f' >> zipWithM_ unify xs xs'
    (Effect r t, Effect r' t') -> do
      let shared = rowMeet r r'
      mapM_ (uncurry unify) shared
      newTail <- liftM Just $ freshInferenceVar EffectKind
      matchTail t  $ Effect (rowDiff r' shared) newTail
      matchTail t' $ Effect (rowDiff r  shared) newTail
    _ -> throw TypeErr ""

-- TODO: can we make this less complicated?
matchTail :: (MonadCat SolverEnv m, MonadError Err m)
          => Maybe Type -> Effect -> m ()
matchTail t ~eff@(Effect row t') = case (t, t') of
  _                     | t == t' && row == mempty -> return ()
  (Just (TypeVar v), _) | isQ v                  -> zonk eff               >>= bindQ v
  (_, Just (TypeVar v)) | isQ v && row == mempty -> zonk (Effect mempty t) >>= bindQ v
  _ -> throw TypeErr ""

bindQ :: (MonadCat SolverEnv m, MonadError Err m) => TVar -> Type -> m ()
bindQ v t | v `occursIn` t = throw TypeErr (pprint (v, t))
          | otherwise = extend $ mempty { solverSub = v @> t }

isQ :: TVar -> Bool
isQ (v :> _) | nameSpace v == InferenceName = True
             | otherwise = False

occursIn :: TVar -> Type -> Bool
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

-- === type substitutions ===

class TySubst a where
  tySubst :: Env Type -> a -> a

instance TySubst Type where
  tySubst env ty = subst (fmap T env, mempty) ty

instance TySubst FExpr where
  tySubst env expr = case expr of
    FDecl decl body  -> FDecl (tySubst env decl) (tySubst env body)
    FVar (v:>ty)     -> FVar (v:>tySubst env ty)
    Annot e ty       -> Annot (tySubst env e) (tySubst env ty)
    SrcAnnot e src   -> SrcAnnot (tySubst env e) src
    FPrimExpr e -> FPrimExpr $ tySubst env e

instance (TraversableExpr expr, TySubst ty, TySubst e, TySubst lam)
         => TySubst (expr ty e lam) where
  tySubst env expr = fmapExpr expr (tySubst env) (tySubst env) (tySubst env)

instance TySubst FLamExpr where
  tySubst env (FLamExpr p eff body) =
    FLamExpr (tySubst env p) (tySubst env eff) (tySubst env body)

instance TySubst FDecl where
  tySubst env decl = case decl of
    LetMono p e -> LetMono (fmap (tySubst env) p) (tySubst env e)
    LetPoly ~(v:>Forall ks qs ty) lam ->
      LetPoly (v:>Forall ks qs (tySubst env ty)) (tySubst env lam)
    TyDef v ty -> TyDef v (tySubst env ty)
    FRuleDef ann ty lam -> FRuleDef ann (tySubst env ty) (tySubst env lam)

instance TySubst FTLam where
  tySubst env (FTLam bs qs body) = FTLam bs qs (tySubst env body)

instance (TySubst a, TySubst b) => TySubst (a, b) where
  tySubst env (x, y) = (tySubst env x, tySubst env y)

instance TySubst a => TySubst (VarP a) where
  tySubst env (v:>ty) = v:> tySubst env ty

instance TySubst a => TySubst (RecTree a) where
  tySubst env p = fmap (tySubst env) p

instance TySubst a => TySubst (Env a) where
  tySubst env xs = fmap (tySubst env) xs

instance (TySubst a, TySubst b) => TySubst (LorT a b) where
  tySubst env (L x) = L (tySubst env x)
  tySubst env (T y) = T (tySubst env y)

instance TySubst a => TySubst [a] where
  tySubst env xs = map (tySubst env) xs

instance TySubst Kind where
  tySubst _ k = k
