-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}

module Optimize (optimizeModule, dceModule, inlineModule) where

import Control.Monad.Reader
import Data.Foldable
import Data.Maybe

import Syntax
import Embed
import Cat
import Env
import Type
import PPrint (ignoreExcept)

optimizeModule :: Module -> Module
optimizeModule = dceModule . inlineModule . dceModule

-- === DCE ===

-- TODO: Track liveness more accurately. Right now we don't mark declared
--       variables as dead.
type DceM = Cat Scope

dceModule :: Module -> Module
dceModule (Module ir decls bindings) = evalCat $ do
  newBindings <- traverse dceBinding bindings
  extend (freeVars newBindings)
  newDecls <- dceDecls decls
  return $ Module ir newDecls newBindings
  where
    dceBinding (ty, LetBound ann expr) = (ty,) . LetBound ann <$> dceExpr expr
    dceBinding b = return b

dceBlock :: Block -> DceM Block
dceBlock (Block decls result) = do
  newResult <- dceExpr result
  extend (freeVars newResult)
  newDecls <- dceDecls decls
  return $ Block newDecls newResult

dceDecls :: Nest Decl -> DceM (Nest Decl)
dceDecls decls = do
  let revDecls = reverse $ toList decls
  revNewDecls <- catMaybes <$> mapM dceDecl revDecls
  return $ toNest $ reverse $ revNewDecls

dceDecl :: Decl -> DceM (Maybe Decl)
dceDecl decl = do
  varsNeeded <- look
  newDecl <- case decl of
    Let ann b expr -> do
      if b `isin` varsNeeded || (not $ isPure expr)
        then Just . Let ann b <$> dceExpr expr
        else return Nothing
    Unpack bs expr -> do
      if any (`isin` varsNeeded) bs || (not $ isPure expr)
        then Just . Unpack bs <$> dceExpr expr
        else return Nothing
  extend (freeVars newDecl)
  return newDecl

dceExpr :: Expr -> DceM Expr
dceExpr expr = case expr of
  App g x        -> App  <$> dceAtom g <*> dceAtom x
  Atom x         -> Atom <$> dceAtom x
  Op  op         -> Op   <$> traverse dceAtom op
  Hof hof        -> Hof  <$> traverse dceAtom hof
  Case e alts ty -> Case <$> dceAtom e <*> mapM dceAlt alts <*> dceAtom ty

dceAlt :: Alt -> DceM Alt
dceAlt (Abs bs block) = Abs bs <$> dceBlock block

dceAtom :: Atom -> DceM Atom
dceAtom atom = case atom of
  Lam (Abs v (arr, block)) -> Lam . (Abs v) . (arr,) <$> dceBlock block
  _ -> return atom

-- === For inlining ===

inlineTraversalDef :: TraversalDef SubstEmbed
inlineTraversalDef = (inlineTraverseExpr, traverseAtom inlineTraversalDef)

inlineModule :: Module -> Module
inlineModule (Module ir decls bindings) = do
  let localVars = filter (not . isGlobal) $ bindingsAsVars $ freeVars bindings
  let block = Block decls $ Atom $ mkConsList $ map Var localVars
  let (Block newDecls (Atom newResult)) = fst $ runSubstEmbed (traverseBlock inlineTraversalDef block) mempty
  let newLocalVals = ignoreExcept $ fromConsList newResult
  Module ir newDecls $ scopelessSubst (newEnv localVars newLocalVals) bindings

inlineTraverseExpr :: Expr -> SubstEmbed Expr
inlineTraverseExpr expr = case expr of
  Hof (For d body) -> do
    newBody <- traverseAtom inlineTraversalDef body
    case newBody of
      -- Trivial bodies
      LamVal ib block@(Block Empty (Atom _)) -> return $ Atom $ TabVal ib block
      -- Pure broadcasts
      LamVal ib@(Ignore _) block | blockEffs block == NoEffects -> do
        result <- dropSub $ evalBlockE inlineTraversalDef block
        Atom <$> buildLam ib TabArrow (\_ -> return $ result)
      _ -> return $ Hof $ For d newBody
  App f' x' -> do
    f <- traverseAtom inlineTraversalDef f'
    x <- traverseAtom inlineTraversalDef x'
    case f of
      TabVal b body -> Atom <$> (dropSub $ extendR (b@>x) $ evalBlockE inlineTraversalDef body)
      _ -> return $ App f x
  _ -> nope
  where nope = traverseExpr inlineTraversalDef expr

dropSub :: SubstEmbed a -> SubstEmbed a
dropSub m = local mempty m
