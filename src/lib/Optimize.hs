-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}

module Optimize (optimizeModule, dceModule, inlineModule) where

import Control.Monad.Reader
import Control.Monad.Writer hiding (Alt)
import Data.Foldable

import Syntax
import Embed
import Cat
import Env
import Type
import PPrint (ignoreExcept)

optimizeModule :: Module -> Module
optimizeModule = dceModule . inlineModule . dceModule

-- === DCE ===

type DceM = WriterT [Decl] (Cat Scope)

dceModule :: Module -> Module
dceModule (Module ir decls bindings) =
  Module ir (dceDecls (freeVars bindings) decls) bindings

dceDecls :: Scope -> Nest Decl -> Nest Decl
dceDecls varsNeeded decls = toNest $ reverse $ fst $ flip runCat varsNeeded $
  execWriterT $ mapM dceDecl $ reverse $ toList decls

dceDecl :: Decl -> DceM ()
dceDecl decl = do
  varsNeeded <- look
  case decl of
    Let ann b expr -> do
      if b `isin` varsNeeded
        then tell [decl] >> extend (freeVars expr)
        else case exprEffs expr of
          NoEffects   -> return ()
          SomeEffects -> do
            tell [Let ann (Ignore (binderType b)) expr]
            extend (freeVars expr)
    Unpack bs expr -> do
      if any (`isin` varsNeeded) bs || (not $ isPure expr)
        then tell [decl] >> extend (freeVars expr)
        else return ()

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
