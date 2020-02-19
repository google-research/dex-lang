-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Simplify (simplifyModule) where

import Control.Monad
import Control.Monad.Reader
import Data.Foldable

import Autodiff
import Env
import Syntax
import Cat
import Embed
import Record

type SimpEnv = SubstEnv
data SimpOpts = SimpOpts { preserveDerivRules :: Bool }
type SimplifyM a = ReaderT SimpEnv (ReaderT (TopEnv, SimpOpts) Embed) a

simplifyModule :: TopEnv -> Module -> Module
simplifyModule env (Module (_, exports) m) = Module (imports, exports) modBody
  where
    (ans', (_, decls)) = flip runEmbed mempty $ flip runReaderT (env, opts) $
                         flip runReaderT mempty $ simplifyModBody m
    modBody = ModBody decls ans'
    imports = freeVars modBody
    opts = SimpOpts False

simplifyModBody :: ModBody -> SimplifyM TopEnv
simplifyModBody (ModBody decls result) = do
  env <- catFold simplifyDecl decls
  extendR env $ substEmbed result

simplify :: Expr -> SimplifyM Atom
simplify expr = case expr of
  Decl decl body -> do
    env <- simplifyDecl decl
    extendR env $ simplify body
  CExpr e -> simplifyCExpr e
  Atom x -> simplifyAtom x

simplifyAtom :: Atom -> SimplifyM Atom
simplifyAtom atom = case atom of
  Var _         -> substEmbed atom
  -- We don't simplify bodies of lam/tlam because we'll beta-reduce them soon.
  TLam _ _      -> substEmbed atom
  Con (Lam _ _) -> substEmbed atom
  Con con -> liftM Con $ traverseExpr con substEmbed simplifyAtom simplifyLam

-- Simplifies bodies of first-order functions only.
-- Unlike `substEmbed`, this simplifies under the binder too.
simplifyLam :: LamExpr -> SimplifyM LamExpr
simplifyLam (LamExpr b body) = do
  b' <- substEmbed b
  buildLamExpr b' $ \x -> extendR (b @> L x) $ simplify body

-- TODO: come up with a coherent strategy for ordering these various reductions
simplifyCExpr :: CExpr -> SimplifyM Atom
simplifyCExpr (Linearize lam) = do
  (topEnv, _) <- lift ask
  lam' <- withRulesPreserved $ simplifyLam lam
  scope <- looks fst
  return $ linearize topEnv scope lam'
simplifyCExpr (Transpose lam) = do
  lam' <- simplifyLam lam
  scope <- looks fst
  return $ transposeMap scope lam'
simplifyCExpr expr = do
  expr' <- traverseExpr expr substEmbed simplifyAtom simplifyLam
  (topEnv, opts) <- lift ask
  -- TODO: consider looking for the reducible constructors first
  case substTopShallow opts topEnv expr' of
    App _ (Con (Lam _ (LamExpr b body))) x -> do
      dropSub $ extendR (b @> L x) $ simplify body
    TApp (TLam tbs body) ts -> do
      let env = fold [tv @> T t' | (tv, t') <- zip tbs ts]
      dropSub $ extendR env $ simplify body
    RecGet (Con (RecCon r)) i -> return $ recGet r i
    Select ty p x y -> selectAt ty p x y
    _ -> emit expr'

substTopShallow :: SimpOpts -> TopEnv -> CExpr -> CExpr
substTopShallow opts env expr = case expr of
  App l f x  -> App l (subst f) x
  TApp f ts  -> TApp (subst f) ts
  RecGet x i -> RecGet (subst x) i
  _ -> expr
  where
    subst :: Atom -> Atom
    subst x = case x of
      Var v | preserveDerivRules opts && v `isin` linRules env -> x
            | otherwise -> case envLookup (topSubstEnv env) v of
                             Just (L x') -> x'
                             _           -> x
      _ -> x

withRulesPreserved :: SimplifyM a -> SimplifyM a
withRulesPreserved m = do
  env <- ask
  lift $ local (\(e,_) -> (e, SimpOpts True)) $ runReaderT m env

simplifyDecl :: Decl -> SimplifyM SimpEnv
simplifyDecl decl = case decl of
  Let b bound -> do
    x <- simplifyCExpr bound
    return $ b @> L x

dropSub :: SimplifyM a -> SimplifyM a
dropSub m = local mempty m
