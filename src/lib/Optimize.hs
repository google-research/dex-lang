-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}

module Optimize (optimizeModule, dceModule, inlineModule) where

import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Foldable
import Data.Maybe

import Syntax
import Embed
import Cat
import Env
import Type
import PPrint

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

type InlineM = SubstEmbedT (Reader (Env BinderUses))

data BinderUses = LocalOnly Int | InBindings

inlineTraversalDef :: TraversalDef InlineM
inlineTraversalDef = (inlineTraverseDecl, inlineTraverseExpr, traverseAtom inlineTraversalDef)

inlineModule :: Module -> Module
inlineModule m@(Module _ _ bindings) = transformModuleAsBlock inlineBlock m
  where
    usedInBindings = filter (not . isGlobal) $ bindingsAsVars $ freeVars bindings
    inlineBlock block = do
      let useCounts = countUses block
      let useCountsExports = (fmap LocalOnly useCounts) <> (newEnv usedInBindings (repeat InBindings))
      fst $ runReader (runSubstEmbedT (traverseBlock inlineTraversalDef block) mempty) useCountsExports

inlineTraverseDecl :: Decl -> InlineM SubstEnv
inlineTraverseDecl decl = case decl of
  Let _ b expr@(Hof (For _ body)) | isPure expr -> do
    uses <- lift $ lift $ asks (`envLookup` b)
    -- This is not a super safe condition for inlining, because it might still duplicate work
    -- unexpectedly (consider an `arr` that's only used as `for i. 2.0 .* arr`). Still, this is not
    -- the way arrays are usually used, so it should be good enough for now. In the future we should
    -- strengthen this check to better ensure that each element of the array is used at most once.
    case uses of
      Just (LocalOnly 1) -> do
        ~(LamVal ib block) <- traverseAtom inlineTraversalDef body
        return $ b @> TabVal ib block
      _ -> traverseDecl inlineTraversalDef decl
  _ -> traverseDecl inlineTraversalDef decl

inlineTraverseExpr :: Expr -> InlineM Expr
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

dropSub :: InlineM a -> InlineM a
dropSub m = local mempty m

type UseCountM = SubstEmbedT (Cat (Env Int))

countUses :: Block -> Env Int
countUses block = execCat $ runSubstEmbedT (traverseBlock useCountTraversalDef block) mempty

useCountTraversalDef :: TraversalDef UseCountM
useCountTraversalDef = (traverseDecl useCountTraversalDef, traverseExpr useCountTraversalDef, useCountAtom)

useCountAtom :: Atom -> UseCountM Atom
useCountAtom atom = case atom of
  Var v -> use v >> cont atom
  _ -> cont atom
  where cont = traverseAtom useCountTraversalDef

use :: VarP a -> UseCountM ()
use n = do
  c <- fromMaybe 0 <$> (looks (`envLookup` n))
  extend (n @> (c + 1))

-- === Helpers ===

transformModuleAsBlock :: (Block -> Block) -> Module -> Module
transformModuleAsBlock transform (Module ir decls bindings) = do
  let localVars = filter (not . isGlobal) $ bindingsAsVars $ freeVars bindings
  let block = Block decls $ Atom $ mkConsList $ map Var localVars
  let (Block newDecls (Atom newResult)) = transform block
  let newLocalVals = ignoreExcept $ fromConsList newResult
  Module ir newDecls $ scopelessSubst (newEnv localVars newLocalVals) bindings
