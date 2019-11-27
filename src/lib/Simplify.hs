-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Simplify (simpPass) where

import Control.Monad
import Control.Monad.Reader
import Data.Foldable

import Env
import Syntax
import Cat
import PPrint
import Fresh
import Type
import Pass
import Subst
import Embed

type NScope = FullEnv NType ()
type SimpEnv = (FullEnv NAtom Name, NScope)
type SimplifyM a = ReaderT SimpEnv (Either Err) a

-- TODO: consider maintaining free variables explicitly
-- ions are atoms with a few bits missing
data Ions = Ions NExpr [NBinder] [NAtom] | Unchanged

simpPass :: TopPass NTopDecl NTopDecl
simpPass = TopPass $ \topDecl -> case topDecl of
  NTopDecl decl -> do
    (decls, env) <- simpAsTopPassM $ simplifyDecl decl
    decl' <- case decls of

      [] -> return $ dummyDecl
      [decl'] -> return decl'
      _ -> error "Multiple decls not implemented"
    extend env
    return $ NTopDecl decl'
    where dummyDecl = NLet [] (NAtoms [])
  NEvalCmd (Command cmd (ty, ntys, expr)) -> do
    -- TODO: handle type vars
    expr' <- simpAsTopPassM $ simplify True expr
    case cmd of
      ShowSimp -> emitOutput $ TextOut $ pprint expr'
      _ -> return $ NEvalCmd (Command cmd (ty, ntys, expr'))

simpAsTopPassM :: SimplifyM a -> TopPassM SimpEnv a
simpAsTopPassM m = do
  env <- look
  liftExceptTop $ runReaderT m env

simplify :: Bool -> NExpr -> SimplifyM NExpr
simplify mat expr = case expr of
  NDecl decl body -> do
    (decls, env) <- simplifyDecl decl
    body' <- extendR env $ simplify mat body
    return $ wrapNDecls decls body'
  NScan b bs xs e -> do
    xs' <- mapM simplifyAtom xs
    (xs'', decls, env) <- materializeAtoms xs'
    extendR env $
      refreshBindersRSimp (b:bs) $ \(b':bs') -> do
        e' <- simplify mat e
        return $ wrapNDecls decls (NScan b' bs' xs'' e')
  NApp f xs -> do
    xs' <- mapM simplifyAtom xs
    f' <- simplifyAtom f
    case f' of
      NLam _ bs body -> local (\(_, scope) -> (env, scope)) (simplify mat body)
        where env = bindEnv bs xs'
      _ -> return $ NApp f' xs'
  NPrimOp b ts xs -> liftM2 (NPrimOp b) (mapM nSubstSimp ts) (mapM simplifyAtom xs)
  NAtoms xs -> do
    xs' <- mapM simplifyAtom xs
    if mat
      then do
        (xs'', decls, _) <- materializeAtoms xs'
        return $ wrapNDecls decls (NAtoms xs'')
      else return $ NAtoms xs'
  NTabCon n ts rows ->
    liftM3 NTabCon (nSubstSimp n) (mapM nSubstSimp ts) (mapM (simplify mat) rows)

simplifyAtom :: NAtom -> SimplifyM NAtom
simplifyAtom atom = case atom of
  NLit x -> return $ NLit x
  NVar v -> do
    x <- asks $ flip envLookup v . fst
    case x of
      Nothing -> return $ NVar v
      Just (L x') -> local (\(_, scope) -> (mempty, scope)) (simplifyAtom x')
      Just (T _) -> error "Expected let-bound var"
  NGet e i -> do
    e' <- simplifyAtom e
    i' <- simplifyAtom i
    return $ nGet e' i'
  NAtomicFor b body ->
    refreshBindersRSimp [b] $ \[b'@(i':>_)] -> do
      body' <- simplifyAtom body
      return $ case body' of
        NGet e (NVar i) | i == i' && not (isin i (freeVars e)) -> e
        _ -> NAtomicFor b' body'
  NLam l bs body ->
    refreshBindersRSimp bs $ \bs' -> do
      body' <- simplify False body
      return $ NLam l bs' body'

materializeAtoms :: [NAtom] -> SimplifyM ([NAtom], [NDecl], SimpEnv)
materializeAtoms xs = do
  (xsDecls, env) <- catTraverse materializeAtom xs
  let (xs', declss) = unzip xsDecls
  return (xs', concat declss, env)

materializeAtom :: NAtom -> SimplifyM ((NAtom, [NDecl]), SimpEnv)
materializeAtom atom = case atom of
  NAtomicFor _ _ -> do
    scope <- asks snd
    let ty = getAtomType scope atom
    atomExpr <- atomToNExpr atom
    let v = rename "tab" scope
    let env' = (mempty, v @> L ty)
    let decl = NLet [v:>ty] atomExpr
    return ((NVar v, [decl]), env')
  _ -> return ((atom, []), mempty)

atomToNExpr :: NAtom -> SimplifyM NExpr
atomToNExpr atom = case atom of
  NAtomicFor b body ->
    refreshBindersRSimp [b] $ \[b'] -> do
      bodyExpr <- atomToNExpr body
      return (NScan b' [] [] bodyExpr)
  _ -> return (NAtoms [atom])

simplifyDecl :: NDecl -> SimplifyM ([NDecl], SimpEnv)
simplifyDecl decl = case decl of
  NLet bs bound -> do
    -- As pointed out in the 'ghc inliner' paper, this can lead to exponential
    -- blowup in compile times. The solution will be to defer some
    -- simplification, pairing the expression with the env, to be forced later.
    bound' <- simplify False bound
    let v = case bs of [] -> error "no binders"
                       (v':>_):_ -> v'
    ions <- renameIons v $ decompose mempty bound'
    case ions of
      Unchanged -> do
        (bs', env) <- refreshBindersSimp bs
        return ([NLet bs' bound'], env)
      Ions bound'' bs' atoms ->
        return $ case bs' of [] -> ([]     , env)
                             _  -> ([decl'], env)
        where env = (bindEnv bs atoms, newScope bs')
              decl' = NLet bs' bound''
  NUnpack bs tv bound -> do
    bound' <- simplify True bound
    tv' <- asks $ rename tv . snd
    let tEnv = (tv @> T tv', tv' @> T ())
    (bs', lEnv) <- extendR tEnv $ refreshBindersSimp bs
    return ([NUnpack bs' tv' bound'], tEnv <> lEnv)

decompose :: Env NType -> NExpr -> Ions
decompose scope expr = case expr of
  NDecl decl body -> case body' of
    Ions e bs atoms -> Ions (NDecl decl e) bs atoms
    Unchanged -> Unchanged
    where
      body' = decompose (scope <> scope') body
      scope' = case decl of
        NLet bs _ -> bindFold bs
        _ -> error "Not implemented"
  NScan b@(_:>n) [] [] body -> case decompose mempty body of
    Unchanged -> Unchanged
    Ions body' bs atoms -> Ions (NScan b [] [] body') bs' atoms'
      where bs' = map (fmap (NTabType n)) bs
            atoms' = map (wrapAtomicFor b bs) atoms
  NScan _ _ _ _ -> Unchanged
  NPrimOp _ _ _ -> Unchanged
  NApp _ _      -> Unchanged
  NAtoms xs -> Ions expr' bs xs  -- TODO: special treatment of unchanged case
    where
      vs = foldMap freeVars xs
      bs = map (uncurry (:>)) $ envPairs $ envIntersect vs scope
      expr' = NAtoms $ fmap (NVar . binderVar) bs
  NTabCon _ _ _ -> Unchanged

bindEnv :: [BinderP c] -> [a] -> FullEnv a b
bindEnv bs xs = fold $ zipWith f bs xs
  where f (v:>_) x = v @> L x

newScope :: [NBinder] -> NScope
newScope bs = foldMap (\(v:>ty) -> v@>L ty) bs

-- TODO: de-dup with version in subst
refreshBindersSimp :: [NBinder] -> SimplifyM ([NBinder], SimpEnv)
refreshBindersSimp bs = catTraverse refreshBinderSimp bs

refreshBinderSimp :: NBinder -> SimplifyM (NBinder, SimpEnv)
refreshBinderSimp (v:>ty) = do
  scope <- asks snd
  ty' <- nSubstSimp ty
  let v' = rename v scope
  return (v':>ty', (v @> L (NVar v'), v' @> L ty'))

renameIons :: Name -> Ions -> SimplifyM Ions
renameIons _ Unchanged = return Unchanged
renameIons v (Ions expr bs atoms) = do
  (bs', (env, scope)) <- catTraverse (renameBinder v) bs
  let atoms' = map (nSubst (env, fmap (const ()) scope)) atoms
  return $ Ions expr bs' atoms'

renameBinder :: Name -> NBinder -> SimplifyM (NBinder, SimpEnv)
renameBinder proposal (v:>ty) = do
  scope <- asks snd
  let v' = rename proposal scope
  return (v':>ty, (v @> L (NVar v'), v' @> L ty))

nSubstSimp :: NSubst a => a -> SimplifyM a
nSubstSimp x = do
  (env, scope) <- ask
  return $ nSubst (env, fmap (const ()) scope) x

refreshBindersRSimp :: [NBinder] -> ([NBinder] -> SimplifyM a) -> SimplifyM a
refreshBindersRSimp bs cont = do (bs', env) <- refreshBindersSimp bs
                                 extendR env $ cont bs'
