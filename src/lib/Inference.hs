{-# LANGUAGE FlexibleContexts #-}

module Inference (typePass, inferKinds) where

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
import Interpreter

data Constraint = Constraint Type Type String Ctx
type QVars = Env ()
type Ctx = Maybe SrcPos

type InferM a = ReaderT (Ctx, TypeEnv) (
                  WriterT [Constraint]
                    (CatT QVars (Either Err))) a

typePass :: UTopDecl -> TopPass TypeEnv TopDecl
typePass tdecl = case tdecl of
  TopDecl decl -> do
    (decl', env') <- liftTop $ inferDecl decl
    putEnv env'
    return $ TopDecl decl'
  EvalCmd NoOp -> return (EvalCmd NoOp)
  -- TODO: special case for `GetType (Var v [])` which can be polymorphic
  EvalCmd (Command cmd expr) -> do
    case cmd of
      GetType -> do
        (ty, _) <- liftTop $ inferAndGeneralize expr
        writeOutText (pprint ty)
        return $ EvalCmd NoOp
      _ -> do
        (_, expr') <- liftTop $ solveLocalMonomorphic $ infer expr
        case cmd of Passes -> writeOutText ("\nSystem F\n" ++ pprint expr')
                    _      -> return ()
        return $ EvalCmd (Command cmd expr')

liftTop :: InferM a -> TopPass TypeEnv a
liftTop m = do
  env <- getEnv
  source <- getSource
  -- TODO: check returned qs and cs are empty
  ((ans, _), _) <- addErrSource source $ liftEither $ flip runCatT mempty $
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
    let tyBody' = instantiateTVs [TypeVar v | (v:>_) <- tbs] tyBody
    -- TODO: check if bound vars leaked (can look at constraints from solve)
    tlamBody' <- solveLocalMonomorphic $ extendRSnd (foldMap tbind tbs) $
                   check tlamBody tyBody'
    return (LetPoly b (TLam tbs tlamBody'), lbind b)
  Unpack (v:>_) tv bound -> do
    (maybeEx, bound') <- solveLocalMonomorphic $ infer bound
    boundTy <- case maybeEx of Exists t -> return $ instantiateTVs [TypeVar tv] t
                               _ -> throw TypeErr (pprint maybeEx)
    -- TODO: give tv to caller so it can check for leaks
    -- TODO: check possible type annotation
    let b' = v :> boundTy
    return (Unpack b' tv bound', asEnv b')
  TAlias _ _ -> error "Shouldn't have TAlias left"

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
    maybeTy <- asks $ flip envLookup v . snd
    Forall kinds body <- case maybeTy of
      Nothing -> throw UnboundVarErr (pprint v)
      Just (L ty) -> return ty
      Just (T _ ) -> error "Expected let-bound var"
    vs <- mapM (const freshQ) (drop (length ts) kinds)
    let ts' = ts ++ vs
    constrainReq (instantiateTVs ts' body)
    return $ Var v ts'
  PrimOp b [] args -> do
    let BuiltinType kinds argTys ansTy = builtinType b
    vs <- mapM (const freshQ) kinds
    constrainReq (instantiateTVs vs ansTy)
    let argTys' = map (instantiateTVs vs) argTys
    args' <- zipWithM check args argTys'
    return $ PrimOp b vs args'
  Decl decl body -> do
    (decl', env') <- inferDecl decl
    body' <- extendRSnd env' $ check body reqTy
    -- TODO: check leaks in unpack
    return $ Decl decl' body'
  Lam p body -> do
    (a, b) <- splitFun expr reqTy
    p' <- checkPat p a
    body' <- extendRSnd (foldMap asEnv p') (check body b)
    return $ Lam p' body'
  App fexpr arg -> do
    (f, fexpr') <- infer fexpr
    (a, b) <- splitFun fexpr f
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
  RecCon r -> do
    tyExpr <- traverse infer r
    constrainReq (RecType (fmap fst tyExpr))
    return $ RecCon (fmap snd tyExpr)
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
  DerivAnnot e ann -> do
    e' <- check e reqTy
    ann' <- check ann (tangentBunType reqTy) -- TODO: handle type vars and meta vars)
    return $ DerivAnnot e' ann'
  Annot e annTy -> do
    -- TODO: check that the annotation is a monotype
    constrainReq annTy
    check e reqTy
  SrcAnnot e pos -> local (\(_,env) -> (Just pos, env)) (check e reqTy)
  _ -> error $ "Unexpected expression: " ++ show expr
  where
    constrainReq ty = constrainEq reqTy ty (pprint expr)

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
annotBinder (v:>ann) = liftM (v:>) $ case ann of NoAnn  -> freshQ
                                                 Ann ty -> return ty

asEnv :: Binder -> TypeEnv
asEnv (v:>ty) = v @> L (asSigma ty)

-- TODO: consider expected/actual distinction. App/Lam use it in opposite senses
splitFun :: UExpr -> Type -> InferM (Type, Type)
splitFun expr f = case f of
  ArrType a b -> return (a, b)
  _ -> do a <- freshQ
          b <- freshQ
          constrainEq f (a --> b) (pprint expr)
          return (a, b)

splitTab :: UExpr -> Type -> InferM (IdxSet, Type)
splitTab expr t = case t of
  TabType a b -> return (a, b)
  _ -> do a <- freshQ
          b <- freshQ
          constrainEq t (a ==> b) (pprint expr)
          return (a, b)

freshQ :: MonadCat QVars m => m Type
freshQ = do
  tv <- looks $ rename (rawName "?")
  extend $ tv @> ()
  return (TypeVar tv)

inferAndGeneralize :: UExpr -> InferM (SigmaType, TLam)
inferAndGeneralize expr = do
  ((ty, expr'), qs) <- solveLocal $ infer expr
  let sigmaTy = Forall (map (const TyKind) qs) $ abstractTVs qs ty
  return (sigmaTy, TLam [] expr')  -- TODO: type-lambda too

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
  let freshQs' = freshQs `envDiff` s
      unconstrained = freshQs' `envDiff` fold [freeTyVars t1 <> freeTyVars t2
                                                | Constraint t1 t2 _ _ <- cs']
  extend $ freshQs' `envDiff` unconstrained
  return (applySubst s ans, envNames unconstrained)

solvePartial :: QVars -> [Constraint] -> Except (Env Type, [Constraint])
solvePartial qs cs = do
  s <- solve cs
  return (envIntersect qs s, substAsConstraints (s `envDiff` qs))
  where
    -- We lost the source context when we solved this the first time
    -- TODO: add context to subst
    substAsConstraints env =
          [Constraint (TypeVar v) ty "" Nothing | (v, ty) <- envPairs env]

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

newtype TSubst = TSubst (Env Type)
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
    (ArrType a b, ArrType a' b') -> recur a a' >> recur b b'
    (TabType a b, TabType a' b') -> recur a a' >> recur b b'
    (Exists t, Exists t')        -> recur t t'
    (RecType r, RecType r')      ->
      case zipWithRecord recur r r' of
             Nothing -> throwError err
             Just unifiers -> void $ sequence unifiers
    _ -> throwError err
  where
    recur = unify err

isQ :: Name -> Bool
isQ (Name ('?':_) _) = True  -- TODO: add an extra field to `Name` for such namespaces
isQ _ = False

bindQ :: Name -> Type -> SolveM ()
bindQ v t | v `occursIn` t = throw TypeErr (pprint (v, t))
          | otherwise = extend $ TSubst (v @> t)

occursIn :: Name -> Type -> Bool
occursIn v t = v `isin` freeTyVars t

zonk :: Type -> SolveM Type
zonk ty = do
  TSubst s <- look
  return $ applySubst s ty

instance Semigroup TSubst where
  -- TODO: make concatenation more efficient by maintaining a reverse-lookup map
  TSubst s1 <> TSubst s2 = TSubst (s1' <> s2)
    where s1' = fmap (applySubst s2) s1

instance Monoid TSubst where
  mempty = TSubst mempty
  mappend = (<>)

-- === misc ===

freeTyVars :: Type -> Env ()
freeTyVars ty = fmap (const ()) (freeVars ty)

inferKinds :: [Name] -> Type -> Except [Kind]
inferKinds vs _ = return $ map (const TyKind) vs  -- TODO: other kinds

applySubst :: Subst a => Env Type -> a -> a
applySubst s x = runReader (subst x) (fmap T s, mempty)

extendRSnd :: (Monoid env, MonadReader (b, env) m) => env -> m a -> m a
extendRSnd env m = local (\(x, env') -> (x, env' <> env)) m
