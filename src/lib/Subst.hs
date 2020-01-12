-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Subst (Scope, Subst, subst, NSubst, nSubst, NSubstEnv) where

import Data.Foldable

import Env
import Record
import Syntax
import PPrint
import Fresh

type Scope = Env ()
type SubstEnvP a = (Env a, Scope)

-- === Expr ===

type SubstVal = LorT (Either Name TLam) Type
type SubstEnv = SubstEnvP SubstVal

class Subst a where
  subst :: SubstEnv -> a -> a

instance Subst Expr where
  subst env@(sub, scope) expr = case expr of
    Lit _ -> expr
    Var v ty tys ->
      case envLookup sub v of
        Nothing -> Var v ty' tys'
        Just (L (Left v')) -> Var v' ty' tys'
        Just (L (Right (TLam tbs body))) -> subst (sub', scope) body
          where sub' = fold [tv @> T t | (tv:>_, t) <- zip tbs tys']
        Just (T _ ) -> error "Expected let-bound var"
      where
        tys' = map recurTy tys
        ty' = recurTy ty
    PrimOp op ts xs -> PrimOp op (map recurTy ts) (map recur xs)
    Decl decl body -> Decl decl'' body'
      where
        decl' = subst env decl
        (decl'', env') = substDeclEnv scope decl'
        body' = subst (env <> env') body
    Lam l p body -> Lam l' p'' body'
      where
        p' = fmap (subst env) p
        l' = recurTy l
        (p'', env') = renamePat scope p'
        body' = subst (env <> env') body
    App e1 e2 -> App (recur e1) (recur e2)
    For p body -> For p'' body'
      where
        p' = fmap (subst env) p
        (p'', env') = renamePat scope p'
        body' = subst (env <> env') body
    Get e1 e2 -> Get (recur e1) (recur e2)
    RecCon k r -> RecCon k (fmap recur r)
    IdxLit _ _ -> expr
    TabCon ty xs -> TabCon (recurTy ty) (map recur xs)
    Pack e ty exTy -> Pack (recur e) (recurTy ty) (recurTy exTy)
    Annot e t        -> Annot (recur e) (recurTy t)
    SrcAnnot e pos   -> SrcAnnot (recur e) pos
    where
      recur :: Expr -> Expr
      recur = subst env

      recurTy :: Type -> Type
      recurTy = subst env

substDeclEnv :: Scope -> Decl -> (Decl, SubstEnv)
substDeclEnv scope decl =
  case decl of
    LetMono p rhs -> (LetMono p' rhs, env)
      where (p', env) = renamePat scope p
    LetPoly (v:>ty) tlam -> (LetPoly (v':>ty) tlam, env)
      where
        v' = rename v scope
        env = (v @> L (Left v'), v' @> ())
    Unpack b tv bound -> (Unpack b' tv' bound, env <> env')
      where
        ([tv':>k], env) = renameTBinders scope [tv:>k]
        ([b'], env') = renamePat (scope <> snd env) [b]
    TyDef _ _ _ _ -> error "Shouldn't have type alias left"

instance Subst Decl where
  subst env decl = case decl of
    LetMono p bound   -> LetMono (fmap (subst env) p) (subst env bound)
    LetPoly b tlam    -> LetPoly (fmap (subst env) b) (subst env tlam)
    -- TODO:
    Unpack b tv bound -> Unpack (subst env b) tv (subst env bound)
    -- TODO: freshen binders
    TyDef dt v bs ty ->
      TyDef dt v bs (subst (subEnv `envDiff` bindFold bs, scope) ty)
      where (subEnv, scope) = env

instance Subst TLam where
   subst env@(_, scope) (TLam tbs body) = TLam tbs' body'
     where
       (tbs', env') = renameTBinders scope tbs
       body' = subst (env <> env') body

renamePat :: Traversable t => Scope -> t Binder -> (t Binder, SubstEnv)
renamePat scope p = (p', (fmap (L . Left . binderVar) env, scope'))
  where (p', (env, scope')) = renameBinders p scope

renameTBinders :: Scope -> [TBinder] -> ([TBinder], SubstEnv)
renameTBinders scope tbs = (tbs', (fmap (T . TypeVar . binderVar) env, scope'))
  where (tbs', (env, scope')) = renameBinders tbs scope

instance Subst Type where
   subst env@(sub, _) ty = case ty of
    BaseType _ -> ty
    TypeVar v ->
      case envLookup sub v of
        Nothing      -> ty
        Just (T ty') -> ty'
        Just (L _)   -> error $ "Shadowed type var: " ++ pprint v
    ArrType l a b -> ArrType (recur l) (recur a) (recur b)
    TabType a b -> TabType (recur a) (recur b)
    RecType k r -> RecType k $ fmap recur r
    TypeApp f args -> TypeApp (recur f) (map recur args)
    Exists body -> Exists (recur body)
    IdxSetLit _ -> ty
    BoundTVar _ -> ty
    Mult _      -> ty
    where recur = subst env

instance Subst SigmaType where
  subst env (Forall ks body) = Forall ks (subst env body)

instance Subst Binder where
  subst env (v:>ty) = v:> subst env ty

instance Subst a => Subst (RecTree a) where
  subst env p = fmap (subst env) p

instance (Subst a, Subst b) => Subst (a, b) where
  subst env (x, y) = (subst env x, subst env y)

-- -- === NExpr ===

type NSubstVal = LorT NAtom Name
type NSubstEnv = SubstEnvP NSubstVal

class NSubst a where
  nSubst :: NSubstEnv -> a -> a

instance NSubst NExpr where
  nSubst env expr = case expr of
    NDecl decl body -> case decl of
      NLet bs bound -> NDecl (NLet bs' (recur bound)) body'
        where
          (bs', env') = refreshNBinders env bs
          body' = nSubst (env <> env') body
      NUnpack _ _ _ -> error $ "NUnpack not implemented" -- TODO
    NScan b bs xs body -> NScan b' bs' (map recurA xs) body'
      where
        (b':bs', env') = refreshNBinders env (b:bs)
        body' = nSubst (env <> env') body
    NPrimOp b ts xs -> NPrimOp b (map (map (nSubst env)) ts) (map recurA xs)
    NApp f xs -> NApp (recurA f) (map recurA xs)
    NAtoms xs -> NAtoms $ map recurA xs
    NTabCon n t xs -> NTabCon (nSubst env n) (nSubst env t) (map recurA xs)
    where
      recur :: NExpr -> NExpr
      recur = nSubst env
      recurA :: NAtom -> NAtom
      recurA = nSubst env

instance NSubst NAtom where
  nSubst env@(sub, scope) atom = case atom of
    NLit _ -> atom
    NVar v ty ->
      case envLookup sub v of
        Nothing -> NVar v (nSubst env ty)
        Just (L x') -> nSubst (mempty, scope) x'
        Just (T _) -> error "Expected let-bound variable"
    NGet e i -> NGet (nSubst env e) (nSubst env i)
    NAtomicFor b body -> NAtomicFor b' body'
      where
        ([b'], env') = refreshNBinders env [b]
        body' = nSubst (env <> env') body
    NLam l bs body -> NLam l bs' body'
      where
        (bs', env') = refreshNBinders env bs
        body' = nSubst (env <> env') body

instance NSubst NType where
  nSubst env@(sub, _) ty = case ty of
    NBaseType _ -> ty
    NTypeVar v -> do
      case envLookup sub v of
        Nothing -> ty
        Just (T x') -> NTypeVar x'
        Just (L _) -> error "Expected type variable"
    NArrType l as bs -> NArrType l (map recur as) (map recur bs)
    NTabType a b   -> NTabType (recur a) (recur b)
    NExists ts -> NExists (map recur ts)
    NIdxSetLit _ -> ty
    NBoundTVar _ -> ty
    where recur = nSubst env

instance NSubst NDecl where
   nSubst env decl = case decl of
     NLet bs expr      -> NLet (map (nSubst env) bs) (nSubst env expr)
     NUnpack bs v expr -> NUnpack (map (nSubst env) bs) v (nSubst env expr)

instance NSubst NBinder where
   nSubst env (v:>ty) = v :> nSubst env ty

refreshNBinders :: Traversable t => NSubstEnv -> t NBinder -> (t NBinder, NSubstEnv)
refreshNBinders env@(_, scope) bs = renameNBinders scope bs'
  where bs' = fmap (nSubst env) bs

renameNBinders :: Traversable t => Scope -> t NBinder -> (t NBinder, NSubstEnv)
renameNBinders scope p = (p', (fmap (\(v:>ty) -> L (NVar v ty)) env, scope'))
  where (p', (env, scope')) = renameBinders p scope
