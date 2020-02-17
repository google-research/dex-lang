-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Inference (inferModule, inferExpr) where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Except hiding (Except)
import Data.Foldable (toList)
import Data.Text.Prettyprint.Doc

import Syntax
import Env
import Record
import Type
import PPrint
import Cat
import Subst

type InferM a = ReaderT TypeEnv (SolverT (Either Err)) a

inferModule :: SubstEnv -> FModule -> Except FModule
inferModule topEnv (Module (imports, exports) (FModBody body)) = do
  let envIn = topEnvType topEnv
  (body', envOut) <- runInferM  envIn $ catTraverse inferDecl body
  let imports' = imports `envIntersect` envIn
  let exports' = exports `envIntersect` (envIn <> envOut)
  return $ Module (imports', exports') (FModBody body')

runInferM :: (TySubst a, Pretty a) => TypeEnv -> InferM a -> Except a
runInferM env m = runSolverT (runReaderT m env)

inferExpr :: FExpr -> Except (Type, FExpr)
inferExpr expr = runInferM mempty $ infer expr

inferDecl :: FDecl -> InferM (FDecl, TypeEnv)
inferDecl decl = case decl of
  LetMono p bound -> do
    -- TOOD: better errors - infer polymorphic type to suggest annotation
    (p', bound') <- do
                      p' <- annotPat p
                      bound' <- check bound (getType p')
                      return (p', bound')
    return (LetMono p' bound', foldMap asEnv p')
  LetPoly ~b@(_:> Forall _ tyBody) (FTLam tbs tlamBody) -> do
    let tyBody' = instantiateTVs (map TypeVar tbs) tyBody
    -- TODO: check if bound vars leaked (can look at constraints from solve)
    let env = foldMap (\tb -> tb @> T (varAnn tb)) tbs
    tlamBody' <- checkLeaks tbs $ extendR env $ check tlamBody tyBody'
    return (LetPoly b (FTLam tbs tlamBody'), b @> L (varAnn b))
  TyDef v ty -> return (TyDef v ty, v @> T (TyKind []))
  FRuleDef _ _ _ -> return (decl, mempty)  -- TODO

infer :: FExpr -> InferM (Type, FExpr)
infer expr = do ty <- freshQ
                expr' <- check expr ty
                return (ty, expr')

check :: FExpr -> Type -> InferM FExpr
check expr reqTy = case expr of
  FDecl decl body -> do
    (decl', env') <- inferDecl decl
    body' <- extendR env' $ check body reqTy
    return $ FDecl decl' body'
  FVar v ts -> do
    ty <- asks $ fromL . (! v)
    let (kinds, body) = asForall ty
    vs <- mapM (const freshQ) (drop (length ts) kinds)
    let ts' = ts ++ vs
    constrainReq (instantiateTVs ts' body)
    return $ FVar (varName v :> ty) ts'
  FPrimExpr prim -> do
    primTy <- generateSubExprTypes prim
    -- TODO: don't ignore explicit annotations (via `snd`)
    let types = fmapExpr primTy snd snd snd
    ansTy <- traversePrimExprType types
               (\t1 t2 -> constrainEq t1 t2 (pprint expr))
               (\_ _ -> return ())
    let constrainArgs = liftM FPrimExpr $ traverseExpr primTy
                          (uncurry checkAnn) (uncurry check) (uncurry checkLam)
    if constrainTopDown prim
      then constrainReq ansTy >> constrainArgs
      else constrainArgs      <* constrainReq ansTy
  Annot e annTy -> do
    -- TODO: check that the annotation is a monotype
    constrainReq annTy
    check e reqTy
  SrcAnnot e pos -> do
    e' <- addSrcContext (Just pos) $ check e reqTy
    return $ SrcAnnot e' pos
  where
    constrainReq ty = constrainEq reqTy ty (pprint expr)

constrainTopDown :: PrimExpr e ty lam -> Bool
constrainTopDown expr = case expr of
  OpExpr _ -> False
  ConExpr    _ -> True

checkLam :: FLamExpr -> (Type, Type) -> InferM FLamExpr
checkLam (FLamExpr p body) (a, b) = do
  p' <- checkPat p a
  body' <- extendR (foldMap asEnv p') (check body b)
  return $ FLamExpr p' body'

checkPat :: Pat -> Type -> InferM Pat
checkPat p ty = do
  p' <- annotPat p
  constrainEq ty (getType p') (pprint p)
  return p'

checkAnn :: Type -> Type -> InferM Type
checkAnn NoAnn ty = return ty
checkAnn ty' ty   = constrainEq ty' ty "annotation" >> return ty

generateSubExprTypes :: PrimExpr ty e lam
                     -> InferM (PrimExpr (ty, Type) (e, Type) (lam, (Type, Type)))
generateSubExprTypes (ConExpr op) = liftM ConExpr $ case op of
  Lam l lam -> do
    l' <- freshInferenceVar Multiplicity
    a <- freshQ
    b <- freshQ
    return $ Lam (l,l') (lam, (a,b))
  LensCon (LensCompose l1 l2) -> do
    a <- freshQ
    b <- freshQ
    c <- freshQ
    return $ LensCon $ LensCompose (l1, Lens a b) (l2, Lens b c)
  Bind m1 lam -> do
    a <- freshQ
    m1' <- freshMonadType
    m2' <- freshMonadType
    return $ Bind (m1,m1') (lam, (a,m2'))
  Seq lam -> do
    m <- freshMonadType
    n <- freshQ
    return $ Seq (lam, (n, m))
  _ -> traverseExpr op (doMSnd freshQ) (doMSnd freshQ) (doMSnd (liftM2 (,) freshQ freshQ))
generateSubExprTypes (OpExpr  op) = liftM OpExpr $ case op of
  App l f x -> do
    l' <- freshInferenceVar Multiplicity
    a <- freshQ
    b <- freshQ
    return $ App (l,l') (f, ArrowType l' a b) (x, a)
  TabGet xs i -> do
    n <- freshQ
    a <- freshQ
    return $ TabGet (xs, TabType n a) (i, n)
  MonadRun r s m -> do
    ~m'@(Monad (Effect r' _ s') _) <- freshMonadType
    return $ MonadRun (r,r') (s,s') (m,m')
  LensGet x l -> do
    a <- freshQ
    b <- freshQ
    return $ LensGet (x,a) (l, Lens a b)
  _ -> traverseExpr op (doMSnd freshQ) (doMSnd freshQ) (doMSnd (liftM2 (,) freshQ freshQ))

doMSnd :: Monad m => m b -> a -> m (a, b)
doMSnd m x = do { y <- m; return (x, y) }

freshMonadType :: InferM Type
freshMonadType = liftM2 Monad (liftM3 Effect freshQ freshQ freshQ) freshQ

annotPat :: Pat -> InferM Pat
annotPat pat = traverse annotBinder pat

annotBinder :: Var -> InferM Var
annotBinder (v:>ann) = liftM (v:>) (fromAnn ann)

fromAnn :: Type -> InferM Type
fromAnn NoAnn = freshQ
fromAnn ty    = return ty

asEnv :: Var -> TypeEnv
asEnv b = b @> L (varAnn b)

-- === constraint solver ===

data SolverEnv = SolverEnv { solverVars :: Env Kind
                           , solverSub  :: Env Type }
type SolverT m = CatT SolverEnv m

runSolverT :: (MonadError Err m, TySubst a, Pretty a)
           => CatT SolverEnv m a -> m a
runSolverT m = liftM fst $ flip runCatT mempty $ do
   ans <- m
   applyNonlinDefault
   ans' <- zonk ans
   vs <- looks $ envNames . unsolved
   throwIf (not (null vs)) TypeErr $ "Ambiguous type variables: "
                                   ++ pprint vs ++ "\n\n" ++ pprint ans
   return ans'

applyNonlinDefault :: MonadCat SolverEnv m => m ()
applyNonlinDefault = do
  vs <- looks unsolved
  let multVars = filter isMult $ map (uncurry (:>)) $ envPairs vs
  extend $ SolverEnv mempty $ foldMap (\v -> v @> Mult NonLin) multVars

solveLocal :: (MonadCat SolverEnv m, MonadError Err m, TySubst a)
           => m a -> m a
solveLocal m = do
  (ans, env@(SolverEnv freshVars sub)) <- scoped (m >>= zonk)
  extend $ SolverEnv (unsolved env) (sub `envDiff` freshVars)
  return ans

checkLeaks :: (MonadCat SolverEnv m, MonadError Err m, TySubst a)
           => [TVar] -> m a -> m a
checkLeaks tvs m = do
  (ans, env) <- scoped $ solveLocal m
  flip mapM_ (solverSub env) $ \ty ->
    flip mapM_ tvs $ \tv ->
      throwIf (tv `occursIn` ty) TypeErr $ "Leaked type variable: " ++ pprint tv
  extend env
  return ans

unsolved :: SolverEnv -> Env Kind
unsolved (SolverEnv vs sub) = vs `envDiff` sub

freshQ :: InferM Type
freshQ = freshInferenceVar $ TyKind []

freshInferenceVar :: Kind -> InferM Type
freshInferenceVar k = do
  tv <- looks $ rename ("?":>k) . solverVars
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
    (ArrowType l a b, ArrowType l' a' b') -> unify l l' >> unify a a' >> unify b b'
    (TabType a b, TabType a' b') -> unify a a' >> unify b b'
    (Monad eff a, Monad eff' a') -> do
      zipWithM_ unify (toList eff) (toList eff')
      unify a a'
    (Lens a b, Lens a' b') -> unify a a' >> unify b b'
    (RecType r, RecType r') ->
      case zipWithRecord unify r r' of
        Nothing -> throw TypeErr ""
        Just unifiers -> void $ sequence unifiers
    (TypeApp f xs, TypeApp f' xs') | length xs == length xs' ->
      unify f f' >> zipWithM_ unify xs xs'
    _ -> throw TypeErr ""

bindQ :: (MonadCat SolverEnv m, MonadError Err m) => TVar -> Type -> m ()
bindQ v t | v `occursIn` t = throw TypeErr (pprint (v, t))
          | otherwise = extend $ mempty { solverSub = v @> t }

-- TODO: something a little less hacky
isQ :: TVar -> Bool
isQ (Name tag _ :> _) = case tagToStr tag of
  '?':_ -> True
  _     -> False

isMult :: TVar -> Bool
isMult (_ :> TyKind _    ) = False
isMult (_ :> Multiplicity) = True

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
    FVar (v:>ty) tyArgs -> FVar (v:>tySubst env ty) (map (tySubst env) tyArgs)
    Annot e ty       -> Annot (tySubst env e) (tySubst env ty)
    SrcAnnot e src   -> SrcAnnot (tySubst env e) src
    FPrimExpr e -> FPrimExpr $ tySubst env e

instance (TraversableExpr expr, TySubst ty, TySubst e, TySubst lam)
         => TySubst (expr ty e lam) where
  tySubst env expr = fmapExpr expr (tySubst env) (tySubst env) (tySubst env)

instance TySubst FLamExpr where
  tySubst env (FLamExpr p body) = FLamExpr (tySubst env p) (tySubst env body)

instance TySubst FDecl where
  tySubst env decl = case decl of
    LetMono p e -> LetMono (fmap (tySubst env) p) (tySubst env e)
    LetPoly ~(v:>Forall ks ty) lam ->
      LetPoly (v:>Forall ks (tySubst env ty)) (tySubst env lam)
    TyDef v ty -> TyDef v (tySubst env ty)
    FRuleDef ann ty lam -> FRuleDef ann (tySubst env ty) (tySubst env lam)

instance TySubst FTLam where
  tySubst env (FTLam bs body) = FTLam bs (tySubst env body)

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
