-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Subst (Subst, subst, scopelessSubst,
              abstractDepType, instantiateDepType) where

import Control.Monad.Identity
import Data.Foldable (fold)

import Env
import Record
import Syntax
import PPrint

scopelessSubst :: Subst a => SubstEnv -> a -> a
scopelessSubst env x = subst (env, scope) x
  where scope = fmap (const ()) $ foldMap freeVars env

class Subst a where
  subst :: (SubstEnv, Scope) -> a -> a

instance (TraversableExpr expr, Subst ty, Subst e, Subst lam)
         => Subst (expr ty e lam) where
  subst env expr = fmapExpr expr (subst env) (subst env) (subst env)

instance Subst Expr where
  subst env@(_, scope) expr = case expr of
    Decl decl body -> Decl decl' (subst (env <> env') body)
      where (decl', env') = refreshDecl scope (subst env decl)
    CExpr e  -> CExpr $ subst env e
    Atom  x  -> Atom  $ subst env x

instance Subst Atom where
  subst env@(_, scope) atom = case atom of
    Var v -> substVar env v
    TLam tvs qs body -> TLam tvs' qs' $ subst env'' body
      where (tvs', env') = refreshTBinders scope tvs
            env'' = env <> env'
            qs' = map (subst env'') qs
    Con con -> Con $ subst env con

substVar :: (SubstEnv, Scope) -> Var -> Atom
substVar env@(sub, scope) v = case envLookup sub v of
  Nothing -> Var $ fmap (subst env) v
  Just (L x') -> subst (mempty, scope) x'
  Just (T _ ) -> error "Expected let-bound variable"

instance Subst LamExpr where
  subst env@(_, scope) (LamExpr b body) = LamExpr b' body'
    where (b', env') = refreshBinder scope (subst env b)
          env'' = env <> env'
          body' = subst env'' body

instance Subst TyQual where
  subst env (TyQual tv c) = TyQual tv' c
    where (TypeVar tv') = subst env (TypeVar tv)

refreshDecl :: Env () -> Decl -> (Decl, (SubstEnv, Scope))
refreshDecl scope decl = case decl of
  Let b bound -> (Let b' bound, env)
    where (b', env) = refreshBinder scope (subst env b)

refreshBinder :: Env () -> Var -> (Var, (SubstEnv, Scope))
refreshBinder scope b = (b', env')
  where b' = rename b scope
        env' = (b@>L (Var b'), b'@>())

refreshTBinders :: Env () -> [TVar] -> ([TVar], (SubstEnv, Scope))
refreshTBinders scope bs = (bs', env')
  where (bs', scope') = renames bs scope
        env' = (newTEnv bs (map TypeVar bs'), scope')

instance Subst Type where
  subst env@(sub, _) ty = case ty of
    TypeVar v ->
      case envLookup sub v of
        Nothing      -> ty
        Just (T ty') -> ty'
        Just (L _)   -> error $ "Shadowed type var: " ++ pprint v
    ArrowType l p -> ArrowType (recur l) (subst env p)
    Forall    ks con body -> Forall    ks con (recur body)
    TypeAlias ks     body -> TypeAlias ks     (recur body)
    TypeApp f args -> reduceTypeApp (recur f) (map recur args)
    Effect row t -> case t of
      Nothing -> Effect row' Nothing
      Just v  -> substTail row' (recur v)
      where row' = foldMap (uncurry (@>))
                     [ (substName sub v :> (), (eff, recur effTy))
                     | (v, (eff, effTy)) <- envPairs row]
    _ -> runIdentity $ traverseType ty (\_ t -> return (subst env t))
                                       (\_ e -> return (subst env e))
    where recur = subst env

instance Subst PiType where
  subst env (Pi a b) = Pi (subst env a) (subst env b)

substName :: SubstEnv -> Name -> Name
substName env v = case envLookup env (v:>()) of
  Just (L (Var (v':>_))) -> v'
  Nothing -> v
  _ -> error $ "Lookup failed: " ++ pprint v

substTail :: EffectRow Type -> Type -> Effect
substTail row (Effect row' t) = Effect (row <> row') t
substTail row t = Effect row (Just t)

instance Subst Decl where
  subst env decl = case decl of
    Let    b    bound -> Let    (subst env b)    (subst env bound)

instance Subst Kind where
  subst _ k = k

instance Subst Var where
  subst env (v:>ty) = v:> subst env ty

instance Subst a => Subst (RecTree a) where
  subst env p = fmap (subst env) p

instance (Subst a, Subst b) => Subst (a, b) where
  subst env (x, y) = (subst env x, subst env y)

instance Subst a => Subst (Env a) where
  subst env xs = fmap (subst env) xs

instance Subst TopEnv where
  subst env (TopEnv e1 e2 e3) = TopEnv (subst env e1) (subst env e2) (subst env e3)

instance (Subst a, Subst b) => Subst (LorT a b) where
  subst env (L x) = L (subst env x)
  subst env (T y) = T (subst env y)

instance (Subst a, Subst b) => Subst (Either a b)where
  subst env (Left  x) = Left  (subst env x)
  subst env (Right x) = Right (subst env x)

-- TODO: check kinds before alias expansion
reduceTypeApp :: Type -> [Type] -> Type
reduceTypeApp (TypeAlias bs ty) xs
  | length bs == length xs = subst (newTEnv bs xs, mempty) ty
  | otherwise = error "Kind error"
reduceTypeApp f xs = TypeApp f xs

instantiateDepType :: Int -> Atom -> Type -> Type
instantiateDepType d x ty = case ty of
  TypeVar _ -> ty
  ArrowType m (Pi a (e, b)) -> ArrowType (recur m) $
    Pi (recur a) (instantiateDepType (d+1) x e, instantiateDepType (d+1) x b)
  Forall tbs cs body -> Forall tbs cs $ recur body
  Effect row tailVar -> Effect row' tailVar
    where row' = fold [ (lookupDBVar v :>()) @> (eff, recur ann)
                      | (v, (eff, ann)) <- envPairs row]
  _ -> runIdentity $ traverseType ty (const (return . recur)) $
         \_ atom -> return $ subst (((DeBruijn d :>()) @> L x), mempty) atom
  where
    recur ::Type -> Type
    recur = instantiateDepType d x

    lookupDBVar :: Name -> Name
    lookupDBVar v = case v of
      DeBruijn i | i == d -> v'  where (Var (v':>_)) = x
      _                   -> v

abstractDepType :: Var -> Int -> Type -> Type
abstractDepType v d ty = case ty of
  TypeVar _ -> ty
  ArrowType m (Pi a (e, b)) -> ArrowType (recur m) $
    Pi (recur a) (abstractDepType v (d+1) e, abstractDepType v (d+1) b)
  Forall tbs cs body -> Forall tbs cs $ recur body
  Effect row tailVar -> Effect row' tailVar
    where row' = fold [ (substWithDBVar v' :>()) @> (eff, recur ann)
                      | (v', (eff, ann)) <- envPairs row]
  _ -> runIdentity $ traverseType ty (const (return . recur)) $
          \_ atom -> return $ subst (v @> L (Var (DeBruijn d :> varAnn v)), mempty) atom
  where
    recur ::Type -> Type
    recur = abstractDepType v d

    substWithDBVar :: Name -> Name
    substWithDBVar v' | varName v == v' = DeBruijn d
                      | otherwise       = v'
