-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Inference (typePass) where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Except (liftEither)
import Control.Monad.Writer
import Control.Monad.Except (throwError)
import Data.Foldable (fold)
import Data.Text.Prettyprint.Doc

import Syntax
import Env
import Record
import Type
import PPrint
import Fresh
import Pass
import Cat
import Subst

data Constraint = Constraint Type Type String SrcCtx
type QVars = Env ()

type InferM a = ReaderT (SrcCtx, TypeEnv) (
                  WriterT [Constraint]
                    (CatT QVars (Either Err))) a

typePass :: TopPass UTopDecl TopDecl
typePass = TopPass $ \tdecl -> case tdecl of
  TopDecl ann decl -> do
    (decl', env') <- liftTop $ inferDecl decl
    extend env'
    return [TopDecl ann decl']
  RuleDef ann ty tlam -> do
    ~(LetPoly _ tlam', _) <- liftTop $ inferDecl $ LetPoly ("_":>ty) tlam
    return [RuleDef ann ty tlam']
  EvalCmd (Command GetType (SrcAnnot (Var v []) _)) -> do
    env <- look
    case envLookup env v of
      Nothing -> throwTopErr $ Err UnboundVarErr Nothing (pprint v)
      Just ty -> emitOutput $ TextOut $ pprint $ fromL ty
  EvalCmd (Command cmd expr) -> do
    (_, expr') <- liftTop $ solveLocalMonomorphic $ infer expr
    case cmd of
      ShowTyped -> emitOutput $ TextOut $ pprint expr'
      _ -> return [EvalCmd (Command cmd expr')]

liftTop :: InferM a -> TopPassM TypeEnv a
liftTop m = do
  env <- look
  -- TODO: check returned qs and cs are empty
  ((ans, _), _) <- liftExceptTop $ flip runCatT mempty $
                        runWriterT $ flip runReaderT (Nothing, env) $ m
  return ans

inferDecl :: UDecl -> InferM (Decl, TypeEnv)
inferDecl decl = case decl of
  LetMono p bound -> do
    -- TOOD: better errors - infer polymorphic type to suggest annotation
    (p', bound') <- solveLocalMonomorphic $ do
                      p' <- annotPat p
                      bound' <- check bound (patType p')
                      return (p', bound')
    return (LetMono p' bound', foldMap asEnv p')
  LetPoly b@(_:> Forall _ tyBody) (TLam tbs tlamBody) -> do
    let vs = [v | (v:>_) <- tbs]
        tyBody' = instantiateTVs (map TypeVar vs) tyBody
    -- TODO: check if bound vars leaked (can look at constraints from solve)
    tlamBody' <- checkLeaks vs $ solveLocalMonomorphic $
                   extendRSnd (foldMap tbind tbs) $ check tlamBody tyBody'
    return (LetPoly b (TLam tbs tlamBody'), lbind b)
  Unpack (v:>_) tv bound -> do
    (maybeEx, bound') <- solveLocalMonomorphic $ infer bound
    boundTy <- case maybeEx of Exists t -> return $ instantiateTVs [TypeVar tv] t
                               _ -> throw TypeErr (pprint maybeEx)
    -- TODO: check possible type annotation
    let b' = v :> boundTy
    return (Unpack b' tv bound', asEnv b')
  TyDef NewType v ty -> return (TyDef NewType v ty, v @> T (Kind []))
  TyDef TyAlias _ _ -> error "Shouldn't have TAlias left"

infer :: UExpr -> InferM (Type, Expr)
infer expr = do ty <- freshQ
                expr' <- check expr ty
                return (ty, expr')

check :: UExpr -> Type -> InferM Expr
check expr reqTy = case expr of
  Lit c -> do
    constrainReq (BaseType (litType c))
    return (Lit c)
  Var v ts -> do
    Forall kinds body <- asks $ fromL . (! v) . snd
    vs <- mapM (const freshQ) (drop (length ts) kinds)
    let ts' = ts ++ vs
    constrainReq (instantiateTVs ts' body)
    return $ Var v ts'
  PrimOp b ts args -> do
    let BuiltinType kinds _ argTys ansTy = builtinType b
    vs <- mapM (const freshQ) (drop (length ts) kinds)
    let ts' = ts ++ vs
    constrainReq (instantiateTVs vs ansTy)
    let argTys' = map (instantiateTVs ts') argTys
    args' <- zipWithM check args argTys'
    return $ PrimOp b ts' args'
  Decl decl@(Unpack _ tv _) body -> do
    (decl', env') <- inferDecl decl
    body' <- checkLeaks [tv] $ solveLocalMonomorphic $ extendRSnd env' $
               check body reqTy
    return $ Decl decl' body'
  Decl decl body -> do
    (decl', env') <- inferDecl decl
    body' <- extendRSnd env' $ check body reqTy
    return $ Decl decl' body'
  Lam mAnn p body -> do
    m <- case mAnn of Ann ty -> return ty
                      NoAnn  -> freshLin
    (m', a, b) <- splitFun expr reqTy
    constrainEq m m' (pprint expr)
    p' <- solveLocalMonomorphic $ checkPat p a
    body' <- extendRSnd (foldMap asEnv p') (check body b)
    return $ Lam m p' body'
  App fexpr arg -> do
    (f, fexpr') <- infer fexpr
    (_, a, b) <- splitFun fexpr f
    arg' <- check arg a
    constrainReq b
    return $ App fexpr' arg'
  For p body -> do
    (a, b) <- splitTab expr reqTy
    p' <- checkPat p a
    body' <- extendRSnd (foldMap asEnv p') (check body b)
    return $ For p' body'
  Get tabExpr idxExpr -> do
    (tabTy, tabExpr') <- infer tabExpr
    (i, v) <- splitTab tabExpr tabTy
    idxExpr' <- check idxExpr i
    constrainReq v
    return $ Get tabExpr' idxExpr'
  RecCon k r -> do
    tyExpr <- traverse infer r
    constrainReq (RecType k (fmap fst tyExpr))
    return $ RecCon k (fmap snd tyExpr)
  TabCon _ xs -> do
    (n, elemTy) <- splitTab expr reqTy
    xs' <- mapM (flip check elemTy) xs
    let n' = length xs
    -- `==> elemTy` for better messages
    constrainEq (n ==> elemTy) (IdxSetLit n' ==> elemTy) (pprint expr)
    return $ TabCon reqTy xs'
  Pack e ty exTy -> do
    let (Exists exBody) = exTy
    constrainReq exTy
    let t = instantiateTVs [ty] exBody
    e' <- check e t
    return $ Pack e' ty exTy
  Annot e annTy -> do
    -- TODO: check that the annotation is a monotype
    constrainReq annTy
    check e reqTy
  SrcAnnot e pos -> do
    e' <- local (\(_,env) -> (Just pos, env)) (check e reqTy)
    return $ SrcAnnot e' pos
  IdxLit n i -> do
    unless (0 <= i && i < n) $ throw TypeErr $ "Index out of bounds: "
                                 ++ pprint i ++ " of " ++ pprint n
    constrainReq (IdxSetLit n)
    return $ IdxLit n i
  where
    constrainReq ty = constrainEq reqTy ty (pprint expr)

checkLeaks :: [Name] -> InferM a -> InferM a
checkLeaks vs m = do
  (ans, cs) <- captureW m
  sequence_ [checkVarConstraint v c | v <- vs, c <- cs]
  tell cs
  return ans
  where
    checkVarConstraint v (Constraint t1 t2 _ ctx) =
      if v `isin` (freeVars t1 <> freeVars t2)
        then throwError $ Err TypeErr ctx $
               "\nLeaked type variable: " ++ pprint v
        else return ()

constrainEq :: Type -> Type -> String -> InferM ()
constrainEq t1 t2 s = do
  ctx <- asks fst
  tell [Constraint t1 t2 s ctx]

checkPat :: UPat -> Type -> InferM Pat
checkPat p ty = do
  p' <- annotPat p
  constrainEq ty (patType p') (pprint p)
  return p'

annotPat :: MonadCat QVars m => UPat -> m Pat
annotPat pat = traverse annotBinder pat

annotBinder :: MonadCat QVars m => UBinder -> m Binder
annotBinder (v:>ann) = liftM (v:>) (fromAnn ann)

fromAnn :: MonadCat QVars m => Ann -> m Type
fromAnn (NoAnn)  = freshQ
fromAnn (Ann ty) = return ty

asEnv :: Binder -> TypeEnv
asEnv (v:>ty) = v @> L (asSigma ty)

-- TODO: consider expected/actual distinction. App/Lam use it in opposite senses
splitFun :: UExpr -> Type -> InferM (Type, Type, Type)
splitFun expr f = case f of
  ArrType m a b -> return (m, a, b)
  _ -> do a <- freshQ
          b <- freshQ
          m <- freshLin
          constrainEq f (ArrType m a b) (pprint expr)
          return (m, a, b)

splitTab :: UExpr -> Type -> InferM (IdxSet, Type)
splitTab expr t = case t of
  TabType a b -> return (a, b)
  _ -> do a <- freshQ
          b <- freshQ
          constrainEq t (a ==> b) (pprint expr)
          return (a, b)

freshQ :: MonadCat QVars m => m Type
freshQ = do
  tv <- looks $ rename "?"
  extend $ tv @> ()
  return (TypeVar tv)

-- TODO: use typeclasses annotations instead of distinguishing multiplicity vars like this
freshLin :: MonadCat QVars m => m Type
freshLin = do
  tv <- looks $ rename "*"
  extend $ tv @> ()
  return (TypeVar tv)

-- We don't currently use this but might want to bring it back
-- inferAndGeneralize :: UExpr -> InferM (SigmaType, TLam)
-- inferAndGeneralize expr = do
--   ((ty, expr'), qs) <- solveLocal $ infer expr
--   let sigmaTy = Forall (map (const (Kind [])) qs) $ abstractTVs qs ty
--   return (sigmaTy, TLam [] expr')  -- TODO: type-lambda too

solveLocalMonomorphic :: (Pretty a, Subst a) => InferM a -> InferM a
solveLocalMonomorphic m = do
  (ans, uncQs) <- solveLocal m
  case uncQs of
    [] -> return ans
    vs -> throw TypeErr $ "Ambiguous type variables: " ++ pprint vs
                        ++ "\n\n" ++ pprint ans

solveLocal :: Subst a => InferM a -> InferM (a, [Name])
solveLocal m = do
  ((ans, freshQs), cs) <- captureW $ scoped m
  (s, cs') <- liftEither $ solvePartial freshQs cs
  tell $ cs'
  let freshQs' = freshQs `envDiff` fromTSubst s
  let unconstrained = freshQs' `envDiff` fold [freeTyVars t1 <> freeTyVars t2
                                               | Constraint t1 t2 _ _ <- cs']
  extend $ freshQs' `envDiff` unconstrained
  let (s', unconstrained') = defaultLinearSubst unconstrained
  return (applySubst (s <> s') ans, envNames unconstrained')

defaultLinearSubst :: QVars -> (TSubst, QVars)
defaultLinearSubst vs = (TSubst s, vs `envDiff` s)
  where multVars = filter isMult (envNames vs)
        s = foldMap (@> Mult NonLin) multVars

solvePartial :: QVars -> [Constraint] -> Except (TSubst, [Constraint])
solvePartial qs cs = do
  s <- solve cs
  return (TSubst (envIntersect qs s), substAsConstraints (s `envDiff` qs))
  where
    -- We lost the source context when we solved this the first time
    -- TODO: add context to subst
    substAsConstraints env =
          [Constraint (TypeVar v) ty "From subst" Nothing | (v, ty) <- envPairs env]

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
    (t, TypeVar v) | isQ v -> bindQ v t
    (TypeVar v, t) | isQ v -> bindQ v t
    (ArrType l a b, ArrType l' a' b') -> recur l l' >> recur a a' >> recur b b'
    (TabType a b, TabType a' b') -> recur a a' >> recur b b'
    (Exists t, Exists t')        -> recur t t'
    (RecType k r, RecType k' r') | k == k' ->
      case zipWithRecord recur r r' of
        Nothing -> throwError err
        Just unifiers -> void $ sequence unifiers
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
          | otherwise = extend $ TSubst (v @> t)

occursIn :: Name -> Type -> Bool
occursIn v t = v `isin` freeTyVars t

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

freeTyVars :: Type -> Env ()
freeTyVars ty = fmap (const ()) (freeVars ty)

applySubst :: Subst a => TSubst -> a -> a
applySubst (TSubst s) x = subst (fmap T s, mempty) x

extendRSnd :: (Monoid env, MonadReader (b, env) m) => env -> m a -> m a
extendRSnd env m = local (\(x, env') -> (x, env' <> env)) m
