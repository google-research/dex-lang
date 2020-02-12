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
type SimplifyM a = ReaderT SimpEnv Embed a

simplifyModule :: SubstEnv -> Module -> Module
simplifyModule env (Module (_, exports) m) =
  Module (mempty, exports) (ModBody decls ans')
  where
    (ans', (_, decls)) = runEmbed (runReaderT (simplifyModBody m) env) mempty

simplifyModBody :: ModBody -> SimplifyM SubstEnv
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

simplifyCExpr :: CExpr -> SimplifyM Atom
simplifyCExpr expr = do
  expr' <- traverseExpr expr substEmbed simplifyAtom simplifyLam
  case expr' of
    App _ (Con (Lam _ (LamExpr b body))) x ->
      dropSub $ extendR (b @> L x) $ simplify body
    TApp (TLam tbs body) ts -> do
      let env = fold [tv @> T t' | (tv, t') <- zip tbs ts]
      dropSub $ extendR env $ simplify body
    RecGet (Con (RecCon r)) i -> return $ recGet r i
    Select ty p x y -> selectAt ty p x y
    Linearize lam -> do
      scope <- looks fst
      return $ linearize scope lam
    Transpose lam -> do
      scope <- looks fst
      return $ transposeMap scope lam
    _ -> emit expr'

simplifyDecl :: Decl -> SimplifyM SimpEnv
simplifyDecl decl = case decl of
  Let b bound -> do
    x <- simplifyCExpr bound
    return $ b @> L x

dropSub :: SimplifyM a -> SimplifyM a
dropSub m = local mempty m
