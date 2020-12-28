-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}

module Optimize (optimizeModule, dceModule, inlineModule) where

import Control.Monad.State.Strict
import Data.Foldable
import Data.Maybe

import Syntax
import Embed
import Cat
import Env
import Type

optimizeModule :: Module -> Module
optimizeModule = dceModule . inlineModule . dceModule

-- === DCE ===

type DceM = State Scope

dceModule :: Module -> Module
dceModule (Module ir decls bindings) = flip evalState mempty $ do
  newBindings <- traverse dceBinding bindings
  modify (<> freeVars newBindings)
  newDecls <- dceDecls decls
  return $ Module ir newDecls newBindings
  where
    dceBinding (ty, LetBound ann expr) = (ty,) . LetBound ann <$> dceExpr expr
    dceBinding b = return b

dceBlock :: Block -> DceM Block
dceBlock (Block decls result) = do
  newResult <- dceExpr result
  modify (<> freeVars newResult)
  newDecls <- dceDecls decls
  return $ Block newDecls newResult

dceDecls :: Nest Decl -> DceM (Nest Decl)
dceDecls decls = do
  let revDecls = reverse $ toList decls
  revNewDecls <- catMaybes <$> mapM dceDecl revDecls
  return $ toNest $ reverse $ revNewDecls

dceDecl :: Decl -> DceM (Maybe Decl)
dceDecl decl = do
  newDecl <- case decl of
    Let ann b expr -> go [b] expr $ Let ann b
  modify (<> freeVars newDecl)
  return newDecl
  where
    go bs expr mkDecl = do
      varsNeeded <- get
      forM_ bs $ modify . envDelete
      if any (`isin` varsNeeded) bs || (not $ isPure expr)
        then Just . mkDecl <$> dceExpr expr
        else return Nothing

dceExpr :: Expr -> DceM Expr
dceExpr expr = case expr of
  App g x        -> App  <$> dceAtom g <*> dceAtom x
  Atom x         -> Atom <$> dceAtom x
  Op  op         -> Op   <$> traverse dceAtom op
  Hof hof        -> Hof  <$> traverse dceAtom hof
  Case e alts ty -> Case <$> dceAtom e <*> mapM dceAlt alts <*> dceAtom ty

dceAlt :: Alt -> DceM Alt
dceAlt (Abs bs block) = Abs <$> traverse dceAbsBinder bs <*> dceBlock block

dceAbsBinder :: Binder -> DceM Binder
dceAbsBinder b = modify (envDelete b) >> return b

dceAtom :: Atom -> DceM Atom
dceAtom atom = case atom of
  Lam (Abs b (arr, block)) -> Lam <$> (Abs <$> dceAbsBinder b <*> ((arr,) <$> dceBlock block))
  _ -> return atom

-- === For inlining ===

type InlineM = SubstEmbed

inlineTraversalDef :: TraversalDef InlineM
inlineTraversalDef = (inlineTraverseDecl, inlineTraverseExpr, traverseAtom inlineTraversalDef)

inlineModule :: Module -> Module
inlineModule m = transformModuleAsBlock inlineBlock (computeInlineHints m)
  where
    inlineBlock block = fst $ runSubstEmbed (traverseBlock inlineTraversalDef block) mempty

inlineTraverseDecl :: Decl -> InlineM SubstEnv
inlineTraverseDecl decl = case decl of
  -- This is not a super safe condition for inlining, because it might still duplicate work
  -- unexpectedly (consider an `arr` that's only used as `for i. 2.0 .* arr`). Still, this is not
  -- the way arrays are usually used, so it should be good enough for now. In the future we should
  -- strengthen this check to better ensure that each element of the array is used at most once.
  Let _ b@(BindWithHint CanInline _) expr@(Hof (For _ body)) | isPure expr -> do
    ~(LamVal ib block) <- traverseAtom inlineTraversalDef body
    return $ b @> TabVal ib block
  _ -> traverseDecl inlineTraversalDef decl

-- TODO: This is a bit overeager. We should count under how many loops are we.
--       Even if the array is accessed in an injective fashion, the accesses might
--       be happen in a deeply nested loop and we might not want to repeat the
--       compute over and over.
inlineTraverseExpr :: Expr -> InlineM Expr
inlineTraverseExpr expr = case expr of
  Hof (For d body) -> do
    newBody <- traverseAtom inlineTraversalDef body
    case newBody of
      -- Trivial bodies
      -- XXX: The trivial body might be a table lambda, and those could technically
      --      get quite expensive. But I think this should never be the case in practice.
      -- XXX: This doesn't always have to end up being beneficial. If the result is
      --      significantly smaller than the intermediates it refers to, then this
      --      optimization will waste a bunch of memory by keeping the large intermediates alive.
      LamVal ib block@(Block Empty (Atom _)) -> return $ Atom $ TabVal ib block
      -- Pure broadcasts
      LamVal ib@(Ignore _) block | blockEffs block == Pure -> do
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

type InlineHintM = State (Env InlineHint)

computeInlineHints :: Module -> Module
computeInlineHints m@(Module _ _ bindings) =
    transformModuleAsBlock (flip evalState bindingsNoInline . hintBlock) m
  where
    usedInBindings = filter (not . isGlobal) $ bindingsAsVars $ freeVars bindings
    bindingsNoInline = newEnv usedInBindings (repeat NoInline)

    hintBlock (Block decls result) = do
      result' <- hintExpr result  -- Traverse result before decls!
      Block <$> hintDecls decls <*> pure result'

    hintDecls decls = do
      let revDecls = reverse $ toList decls
      revNewDecls <- mapM hintDecl revDecls
      return $ toNest $ reverse $ revNewDecls

    hintDecl decl = case decl of
      Let ann b expr -> go [b] expr $ Let ann . head
      where
        go bs expr mkDecl = do
          void $ noInlineFree bs
          bs' <- traverse hintBinder bs
          forM_ bs $ modify . envDelete
          mkDecl bs' <$> hintExpr expr

    hintExpr :: Expr -> InlineHintM Expr
    hintExpr expr = case expr of
      App (Var v) x  -> App  <$> (Var v <$ use v) <*> hintAtom x
      App g x        -> App  <$> hintAtom g       <*> hintAtom x
      Atom x         -> Atom <$> hintAtom x
      Op  op         -> Op   <$> traverse hintAtom op
      Hof hof        -> Hof  <$> traverse hintAtom hof
      Case e alts ty -> Case <$> hintAtom e <*> traverse hintAlt alts <*> hintAtom ty

    hintAlt (Abs bs block) = Abs <$> traverse hintAbsBinder bs <*> hintBlock block

    hintAtom :: Atom -> InlineHintM Atom
    hintAtom atom = case atom of
      -- TODO: Is it always ok to inline e.g. into a table lambda? Even if the
      --       lambda indicates that the access pattern would be injective, its
      --       body can still get instantiated multiple times!
      Lam (Abs b (arr, block)) -> Lam <$> (Abs <$> hintAbsBinder b <*> ((arr,) <$> hintBlock block))
      _ -> noInlineFree atom

    use n = do
      maybeHint <- gets $ (`envLookup` n)
      let newHint = case maybeHint of
                      Nothing -> CanInline
                      Just _  -> NoInline
      modify (<> (n @> newHint))

    hintBinder :: Binder -> InlineHintM Binder
    hintBinder b = do
      maybeHint <- gets $ (`envLookup` b)
      case (b, maybeHint) of
        (Bind v  , Just hint) -> return $ BindWithHint hint   v
        (Bind v  , Nothing  ) -> return $ BindWithHint NoHint v -- TODO: Change to Ignore?
        (Ignore _, Nothing  ) -> return b
        (Ignore _, Just _   ) -> error "Ignore binder is not supposed to have any uses"

    hintAbsBinder :: Binder -> InlineHintM Binder
    hintAbsBinder b = modify (envDelete b) >> traverse hintAtom b

    noInlineFree :: HasVars a => a -> InlineHintM a
    noInlineFree a = modify (<> (fmap (const NoInline) (freeVars a))) >> return a
