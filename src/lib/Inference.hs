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
import Control.Monad.Except (liftEither)
import Control.Monad.Writer
import Control.Monad.Except (throwError)
import Data.Foldable (fold, toList)
import Data.Text.Prettyprint.Doc

import Syntax
import Env
import Record
import Type
import PPrint
import Fresh
import Cat
import Subst

data Constraint = Constraint Type Type String SrcCtx
type TypeEnv = FullEnv Type Kind
type QVars = Env ()
type UExpr = FExpr
type InferM a = ReaderT (SrcCtx, TypeEnv) (
                  WriterT [Constraint]
                    (CatT QVars (Either Err))) a

inferModule :: TopEnv -> FModule -> Except FModule
inferModule topEnv (FModule imports body exports) = do
  let envIn = topEnvToTypeEnv topEnv
  (body', env') <- runInferM envIn (inferDecls body)
  let envOut = envIn <> env'
  let imports' = imports `envIntersect` envIn
  let exports' = exports `envIntersect` envOut
  return $ FModule imports' body' exports'

topEnvToTypeEnv :: TopEnv -> TypeEnv
topEnvToTypeEnv env = flip fmap env $ \ann -> case ann of
  L (Left atom)  -> L $ Forall [] $ getType atom
  L (Right tlam) -> L $ getType tlam
  T _    -> T $ Kind []

runInferM :: TypeEnv -> InferM a -> Except a
runInferM env m = do
  -- TODO: check returned qs and cs are empty
  ((ans, _), _) <- flip runCatT mempty $
                     runWriterT $ flip runReaderT (Nothing, env) $ m
  return ans

-- TODO: put src ctx in an inner ReaderT so we can just use cat here
inferDecls :: [FDecl] -> InferM ([FDecl], TypeEnv)
inferDecls [] = return ([], mempty)
inferDecls (decl:decls) = do
  (decl' , env ) <- inferDecl decl
  (decls', env') <- extendRSnd env $ inferDecls decls
  return (decl':decls', env <> env')

inferExpr :: UExpr -> Except (Type, FExpr)
inferExpr expr = runInferM mempty $ solveLocalMonomorphic (infer expr)

inferDecl :: FDecl -> InferM (FDecl, TypeEnv)
inferDecl decl = case decl of
  LetMono p bound -> do
    -- TOOD: better errors - infer polymorphic type to suggest annotation
    (p', bound') <- solveLocalMonomorphic $ do
                      p' <- annotPat p
                      bound' <- check bound (getType p')
                      return (p', bound')
    return (LetMono p' bound', foldMap asEnv p')
  LetPoly b@(_:> Forall _ tyBody) (TLam tbs tlamBody) -> do
    let tyBody' = instantiateTVs (map TypeVar tbs) tyBody
    -- TODO: check if bound vars leaked (can look at constraints from solve)
    let env = foldMap (\tb -> tb @> T (varAnn tb)) tbs
    tlamBody' <- checkLeaks tbs $ solveLocalMonomorphic $
                   extendRSnd env $ check tlamBody tyBody'
    return (LetPoly b (TLam tbs tlamBody'), b @> L (varAnn b))
  FUnpack (v:>_) tv bound -> do
    (maybeEx, bound') <- solveLocalMonomorphic $ infer bound
    boundTy <- case maybeEx of Exists t -> return $ instantiateTVs [TypeVar tv] t
                               _ -> throw TypeErr (pprint maybeEx)
    -- TODO: check possible type annotation
    let b' = v :> boundTy
    return (FUnpack b' tv bound', asEnv b')
  TyDef v bs ty -> return (TyDef v bs ty, mempty)
  FRuleDef _ _ _ -> return (decl, mempty)  -- TODO

infer :: UExpr -> InferM (Type, FExpr)
infer expr = do ty <- freshQ
                expr' <- check expr ty
                return (ty, expr')

check :: UExpr -> Type -> InferM FExpr
check expr reqTy = case expr of
  FDecl decl@(FUnpack _ tv _) body -> do
    (decl', env') <- inferDecl decl
    body' <- checkLeaks [tv] $ solveLocalMonomorphic $ extendRSnd env' $
               check body reqTy
    return $ FDecl decl' body'
  FDecl decl body -> do
    (decl', env') <- inferDecl decl
    body' <- extendRSnd env' $ check body reqTy
    return $ FDecl decl' body'
  FVar v ts -> do
    ~(Forall kinds body) <- asks $ fromL . (! v) . snd
    vs <- mapM (const freshQ) (drop (length ts) kinds)
    let ts' = ts ++ vs
    constrainReq (instantiateTVs ts' body)
    return $ FVar (varName v :> reqTy) ts'
  -- TODO: consider special-casing App for better error messages
  -- (e.g. in `f x`, infer `f` then check `x` rather than checking `f` first)
  FPrimExpr prim -> do
    (primTy, unc) <- solveLocal $ do
       typed <- generateSubExprTypes prim
       let types = fmapExpr typed snd snd snd
       ansTy <- traversePrimExprType types
                  (\t1 t2 -> constrainEq t1 t2 (pprint expr))
                  (\_ _ -> return ())
       constrainReq ansTy
       return typed
    -- TODO: don't ignore explicit annotations (via `snd`)
    extend $ foldMap (\v -> (v:>())@>()) unc
    liftM FPrimExpr $ traverseExpr primTy (uncurry checkAnn) (uncurry check) (uncurry checkLam)
  Annot e annTy -> do
    -- TODO: check that the annotation is a monotype
    constrainReq annTy
    check e reqTy
  SrcAnnot e pos -> do
    e' <- local (\(_,env) -> (Just pos, env)) (check e reqTy)
    return $ SrcAnnot e' pos
  where
    constrainReq ty = constrainEq reqTy ty (pprint expr)

checkLeaks :: [TVar] -> InferM a -> InferM a
checkLeaks vs m = do
  (ans, cs) <- captureW m
  sequence_ [checkVarConstraint v c | v <- vs, c <- cs]
  tell cs
  return ans

checkVarConstraint :: TVar -> Constraint -> InferM ()
checkVarConstraint v (Constraint t1 t2 _ ctx) =
  if v `isin` (freeVars t1 <> freeVars t2)
    then throwError $ Err TypeErr ctx $
           "\nLeaked type variable: " ++ pprint v
    else return ()

constrainEq :: Type -> Type -> String -> InferM ()
constrainEq t1 t2 s = do
  ctx <- asks fst
  tell [Constraint t1 t2 s ctx]

checkLam :: FLamExpr -> (Type, Type) -> InferM FLamExpr
checkLam (FLamExpr p body) (a, b) = do
  p' <- solveLocalMonomorphic $ checkPat p a
  body' <- extendRSnd (foldMap asEnv p') (check body b)
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
generateSubExprTypes (PrimConExpr op) = liftM PrimConExpr $ case op of
  Lam l lam -> do
    l' <- freshLin
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
  TabGet xs i -> do
    n <- freshQ
    a <- freshQ
    return $ TabGet (xs, TabType n a) (i, n)
  _ -> traverseExpr op (doMSnd freshQ) (doMSnd freshQ) (doMSnd (liftM2 (,) freshQ freshQ))
generateSubExprTypes (PrimOpExpr  op) = liftM PrimOpExpr $ case op of
  App f x -> do
    l <- freshLin
    a <- freshQ
    b <- freshQ
    return $ App (f, ArrType l a b) (x, a)
  MonadRun r s m -> do
    ~m'@(Monad (Effect r' _ s') _) <- freshMonadType
    return $ MonadRun (r,r') (s,s') (m,m')
  LensGet x l -> do
    a <- freshQ
    b <- freshQ
    return $ LensGet (x,a) (l, Lens a b)
  Scan x lam -> do
    n <- freshQ
    c <- freshQ
    y <- freshQ
    return $ Scan (x,c) (lam,(pairTy n c, pairTy c y))
  _ -> traverseExpr op (doMSnd freshQ) (doMSnd freshQ) (doMSnd (liftM2 (,) freshQ freshQ))

doMSnd :: Monad m => m b -> a -> m (a, b)
doMSnd m x = do { y <- m; return (x, y) }

freshMonadType :: InferM Type
freshMonadType = liftM2 Monad (liftM3 Effect freshQ freshQ freshQ) freshQ

annotPat :: MonadCat QVars m => Pat -> m Pat
annotPat pat = traverse annotBinder pat

annotBinder :: MonadCat QVars m => Var -> m Var
annotBinder (v:>ann) = liftM (v:>) (fromAnn ann)

fromAnn :: MonadCat QVars m => Type -> m Type
fromAnn NoAnn = freshQ
fromAnn ty    = return ty

asEnv :: Var -> TypeEnv
asEnv b = b @> L (Forall [] (varAnn b))

freshQ :: MonadCat QVars m => m Type
freshQ = do
  tv <- looks $ rename ("?":>Kind [])
  extend $ tv @> ()
  return (TypeVar tv)

freshLin :: MonadCat QVars m => m Type
freshLin = do
  tv <- looks $ rename ("*":>Kind [])
  extend $ tv @> ()
  return (TypeVar tv)

-- TODO: introduce a multiplicity kind
defaultLinearSubst :: [Name] -> (TSubst, QVars)
defaultLinearSubst vs = (TSubst s, foldMap (\v -> (v:>())@>()) vs `envDiff` s)
  where multVars = filter isMult vs
        s = foldMap (\v -> (v:>())@> Mult NonLin) multVars

solveLocalMonomorphic :: (Pretty a, TySubst a) => InferM a -> InferM a
solveLocalMonomorphic m = do
  (ans, uncQs) <- solveLocal m
  let (s, uncQs') = defaultLinearSubst uncQs
  let ans' = applySubst s ans
  case envNames uncQs' of
    [] -> return ans'
    vs -> throw TypeErr $ "Ambiguous type variables: " ++ pprint vs
                        ++ "\n\n" ++ pprint ans'

solveLocal :: TySubst a => InferM a -> InferM (a, [Name])
solveLocal m = do
  ((ans, freshQs), cs) <- captureW $ scoped m
  (s, cs') <- liftEither $ solvePartial freshQs cs
  tell $ cs'
  let freshQs' = freshQs `envDiff` fromTSubst s
  let unconstrained = freshQs' `envDiff` fold [freeVars t1 <> freeVars t2
                                               | Constraint t1 t2 _ _ <- cs']
  extend $ freshQs' `envDiff` unconstrained
  return (applySubst s ans, envNames unconstrained)

solvePartial :: QVars -> [Constraint] -> Except (TSubst, [Constraint])
solvePartial qs cs = do
  s <- solve cs
  return (TSubst (envIntersect qs s), substAsConstraints (s `envDiff` qs))
  where
    -- We lost the source context when we solved this the first time
    -- TODO: add context to subst
    substAsConstraints env =
          [Constraint (TypeVar (v:>Kind [])) ty "<unknown source>" Nothing | (v, ty) <- envPairs env]

-- === constraint solver ===

solve :: [Constraint] -> Except (Env Type)
solve cs = do
  ((), TSubst s) <- runCatT (mapM_ unifyC cs) mempty
  return s
  where
    unifyC (Constraint t1 t2 s ctx) = do
      t1' <- zonk t1
      t2' <- zonk t2
      let err = Err TypeErr ctx $
                  "\nExpected: " ++ pprint t1'
               ++ "\n  Actual: " ++ pprint t2'
               ++ "\nIn: "       ++ s
      unify err t1' t2'

newtype TSubst = TSubst { fromTSubst :: Env Type }
type SolveM a = CatT TSubst (Either Err) a

-- TODO: check kinds
unify :: Err -> Type -> Type -> SolveM ()
unify err t1 t2 = do
  t1' <- zonk t1
  t2' <- zonk t2
  case (t1', t2') of
    _ | t1' == t2' -> return ()
    (t, TypeVar (v:>_)) | isQ v -> bindQ v t
    (TypeVar (v:>_), t) | isQ v -> bindQ v t
    (ArrType l a b, ArrType l' a' b') -> recur l l' >> recur a a' >> recur b b'
    (TabType a b, TabType a' b') -> recur a a' >> recur b b'
    (Exists t, Exists t')        -> recur t t'
    (Monad eff a, Monad eff' a') -> do
      zipWithM_ recur (toList eff) (toList eff')
      recur a a'
    (Lens a b, Lens a' b') -> recur a a' >> recur b b'
    (RecType r, RecType r') ->
      case zipWithRecord recur r r' of
        Nothing -> throwError err
        Just unifiers -> void $ sequence unifiers
    (TypeApp f xs, TypeApp f' xs') | length xs == length xs' ->
      recur f f' >> zipWithM_ recur xs xs'
    _ -> throwError err
  where
    recur = unify err

-- TODO: something a little less hacky
isQ :: Name -> Bool
isQ (Name tag _) = case tagToStr tag of
  '?':_ -> True
  '*':_ -> True
  _     -> False

isMult :: Name -> Bool
isMult (Name tag _) = case tagToStr tag of
  '*':_ -> True
  _     -> False

bindQ :: Name -> Type -> SolveM ()
bindQ v t | v `occursIn` t = throw TypeErr (pprint (v, t))
          | otherwise = extend $ TSubst ((v:>()) @> t)

occursIn :: Name -> Type -> Bool
occursIn v t = (v:>()) `isin` freeVars t

zonk :: Type -> SolveM Type
zonk ty = do
  s <- look
  return $ applySubst s ty

instance Semigroup TSubst where
  -- TODO: make concatenation more efficient by maintaining a reverse-lookup map
  TSubst s1 <> TSubst s2 = TSubst (s1' <> s2)
    where s1' = fmap (applySubst (TSubst s2)) s1

instance Monoid TSubst where
  mempty = TSubst mempty
  mappend = (<>)

-- === misc ===

applySubst :: TySubst a => TSubst -> a -> a
applySubst (TSubst s) x = tySubst s x

extendRSnd :: (Monoid env, MonadReader (b, env) m) => env -> m a -> m a
extendRSnd env m = local (\(x, env') -> (x, env' <> env)) m

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
    LetPoly (v:>Forall ks ty) (TLam bs body) ->
       LetPoly (v:>Forall ks (tySubst env ty)) (TLam bs (tySubst env body))
    FUnpack (v:>ty) tv e -> FUnpack (v:>(tySubst env ty)) tv (tySubst env e)

instance (TySubst a, TySubst b) => TySubst (a, b) where
  tySubst env (x, y) = (tySubst env x, tySubst env y)

instance TySubst a => TySubst (VarP a) where
  tySubst env (v:>ty) = v:> tySubst env ty

instance TySubst a => TySubst (RecTree a) where
  tySubst env p = fmap (tySubst env) p
