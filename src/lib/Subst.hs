-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Subst (Subst, subst, deShadow, scopelessSubst) where

import Env
import Record
import Syntax
import PPrint

scopelessSubst :: Subst a => SubstEnv -> a -> a
scopelessSubst env x = subst (env, scope) x
  where scope = fmap (const Nothing) $ foldMap freeVars env

class Subst a where
  -- NOTE: Scope is here only to allow the substitution to generate fresh variables
  -- See "Secrets of the Glasgow Haskell Compiler inliner", Section 3.2
  subst :: (SubstEnv, Scope) -> a -> a

instance (TraversableExpr expr, Subst ty, Subst e, Subst lam)
         => Subst (expr ty e lam) where
  subst env expr = fmapExpr expr (subst env) (subst env) (subst env)

instance Subst Block where
  -- TODO: effects
  subst env (Block [] result eff) = Block [] (subst env result) eff
  subst env@(_, scope) (Block (decl:decls) result eff) =
    Block (decl':decls') result' eff'
    where
      (decl', env') = refreshDecl scope (subst env decl)
      Block decls' result' eff' = subst (env <> env') $ Block decls result eff

instance Subst Atom where
  subst env@(sub, _) atom = case atom of
    Var v -> substVar env v
    Lam   h lam  -> Lam   h $ subst env lam
    Arrow h piTy -> Arrow h $ subst env piTy
    Effect row t -> case t of
      Nothing -> Effect row' Nothing
      Just v  -> substTail row' (recur v)
      where row' = foldMap (uncurry (@>))
                     [ (substName sub v :> (), (eff, recur effTy))
                     | (v, (eff, effTy)) <- envPairs row]
    TC con -> TC $ fmapTyCon con (subst env) (subst env)
    Con con -> Con $ subst env con
    where recur = subst env


substVar :: (SubstEnv, Scope) -> Var -> Atom
substVar env@(sub, scope) v = case envLookup sub v of
  Nothing -> Var $ fmap (subst env) v
  Just x' -> deShadow x' scope

instance Subst LamExpr where
  subst env@(_, scope) (LamExpr b body) = LamExpr b' body'
    where (b', env') = refreshBinder scope (subst env b)
          env'' = env <> env'
          body' = subst env'' body

instance Subst TyQual where
  subst env (TyQual tv c) = TyQual tv' c
    where (Var tv') = subst env (Var tv)

refreshDecl :: Scope -> Decl -> (Decl, (SubstEnv, Scope))
refreshDecl scope decl = case decl of
  Let b bound -> (Let b' bound, env)
    where (b', env) = refreshBinder scope (subst env b)

refreshBinder :: Scope -> Var -> (Var, (SubstEnv, Scope))
refreshBinder scope b = (b', env')
  where b' = rename b scope
        env' = (b@>Var b', b'@>Nothing)

instance Subst b => Subst (PiType b) where
  subst env (Pi a b) = Pi (subst env a) (subst env b)

substName :: SubstEnv -> Name -> Name
substName env v = case envLookup env (v:>()) of
  Just (Var (v':>_)) -> v'
  Nothing -> v
  _ -> error $ "Lookup failed: " ++ pprint v

substTail :: EffectRow Type -> Type -> Effect
substTail row (Effect row' t) = Effect (row <> row') t
substTail row t = Effect row (Just t)

instance Subst Decl where
  subst env (Let b bound) = Let (subst env b) (subst env bound)

instance Subst Expr where
  subst env expr = case expr of
    App h f x   -> App h (subst env f) (subst env x)
    For dir lam -> For dir $ subst env lam
    Atom x      -> Atom $ subst env x
    Op op       -> Op $ fmapExpr op (subst env) (subst env) (subst env)

instance Subst Var where
  subst env (v:>ty) = v:> subst env ty

instance Subst a => Subst (RecTree a) where
  subst env p = fmap (subst env) p

instance (Subst a, Subst b) => Subst (a, b) where
  subst env (x, y) = (subst env x, subst env y)

instance Subst a => Subst (Env a) where
  subst env xs = fmap (subst env) xs

instance Subst TopEnv where
  subst env (TopEnv e1 e2 e3) =
    TopEnv (subst env e1) (subst env e2) (subst env e3)

instance (Subst a, Subst b) => Subst (Either a b)where
  subst env (Left  x) = Left  (subst env x)
  subst env (Right x) = Right (subst env x)

instance Subst a => Subst [a] where
  subst env xs = map (subst env) xs

deShadow :: Subst a => a -> Scope -> a
deShadow x scope = subst (mempty, scope) x
