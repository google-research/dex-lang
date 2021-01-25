-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Optimize () where -- optimizeModule, dceModule, inlineModule) where

import Data.Maybe

import Preamble
import Base
import Core

import Cat

import Inference -- TODO: remove

-- optimizeModule :: Module i -> Module o
-- optimizeModule = dceModule . inlineModule . dceModule

-- -- === DCE ===

-- type DceM n = State (Scope n)

-- dceModule :: Module n -> Module n
-- dceModule = undefined
-- -- dceModule (Module ir decls bindings) = flip evalState mempty $ do
-- --   newBindings <- mapMH dceBinding bindings
-- --   modify (<> freeVars newBindings)
-- --   newDecls <- dceDecls decls
-- --   return $ Module ir newDecls newBindings
-- --   where
-- --     dceBinding (ty, LetBound ann expr) = (ty,) . LetBound ann <$> dceExpr expr
-- --     dceBinding b = return b

-- dceBlock :: Block n -> DceM n (Block n)
-- dceBlock = undefined
-- -- dceBlock (Block decls result) = do
-- --   newResult <- dceExpr result
-- --   modify (<> freeVars newResult)
-- --   newDecls <- dceDecls decls
-- --   return $ Block newDecls newResult

-- dceDecls :: Nest Decl n -> DceM n (Nest Decl n)
-- dceDecls = undefined
-- -- dceDecls decls = do
-- --   let revDecls = reverse $ fromNest decls
-- --   revNewDecls <- catMaybes <$> mapM dceDecl revDecls
-- --   return $ toNest $ reverse $ revNewDecls

-- dceDecl :: Decl n -> DceM n (Maybe (Decl n))
-- dceDecl = undefined
-- -- dceDecl (Let ann b expr) = do
-- --   varsNeeded <- get
-- --   modify (envDelete b)
-- --   if b `isin` varsNeeded || (not $ isPure expr)
-- --     then return $ Just $ Let ann b expr
-- --     else return Nothing

-- dceExpr :: Expr n -> DceM n (Expr n)
-- dceExpr expr = case expr of
--   App g x        -> App  <$> dceAtom g <*> dceAtom x
--   Atom x         -> Atom <$> dceAtom x
--   Op  op         -> Op   <$> traverse dceAtom op
--   Hof hof        -> Hof  <$> traverse dceAtom hof
--   -- Case e alts ty -> Case <$> dceAtom e <*> mapM dceAlt alts <*> dceAtom ty

-- dceAlt :: Alt n -> DceM n (Alt n)
-- dceAlt = undefined
-- -- dceAlt (Abs bs block) = Abs <$> mapMH dceAbsBinder bs <*> dceBlock block

-- dceAbsBinder :: Name n -> DceM n (Name n)
-- dceAbsBinder = undefined
-- -- dceAbsBinder v = modify (envDelete v) >> return b

-- dceAtom :: Atom n -> DceM n (Atom n)
-- dceAtom = undefined
-- -- dceAtom atom = case atom of
-- --   Lam (Abs b (WithArrow arr block)) ->
-- --     Lam <$> (Abs <$> dceAbsBinder b <*> (WithArrow arr <$> dceBlock block))
-- --   _ -> return atom

-- -- === For inlining ===

-- -- type InlineM i o = SubstBuilder i o

-- -- inlineTraversalDef :: TraversalDef i o (InlineM i o)
-- -- inlineTraversalDef = (inlineTraverseDecl, inlineTraverseExpr, traverseAtom inlineTraversalDef)

-- -- inlineModule :: Module i-> Module o
-- -- inlineModule = undefined
-- -- inlineModule m = transformModuleAsBlock inlineBlock (computeInlineHints m)
-- --   where
-- --     inlineBlock block = fst $ runSubstBuilder (traverseBlock inlineTraversalDef block) mempty

-- -- inlineTraverseDecl :: Decl i -> InlineM i o (Subst i o)
-- -- inlineTraverseDecl = undefined
-- -- inlineTraverseDecl decl = case decl of
--   -- Let _ b@(BindWithHint CanInline _ _) expr@(Hof (For _ body)) | isPure expr -> do
--   --   ~(LamVal ib block) <- traverseAtom inlineTraversalDef body
--   --   return $ b @> TabVal ib block
--   -- If `f` turns out to be an inlined table lambda, we expand its block and
--   -- call ourselves recursively on the block's result expression. This makes
--   -- it possible for us to e.g. discover that the result is a `for` loop, and
--   -- match the case above, to continue the inlining process.
--   -- Let letAnn letBinder (App f' x') -> do
--   --   f <- traverseAtom inlineTraversalDef f'
--   --   x <- traverseAtom inlineTraversalDef x'
--   --   case f of
--   --     TabVal b (Block body result) -> do
--   --       dropSub $ extendR (b@>x) $ do
--   --         blockEnv <- traverseDeclsOpen substTraversalDef body
--   --         extendR blockEnv $ inlineTraverseDecl $ Let letAnn letBinder result
--   --     _ -> (letBinder@>) <$> emitTo (binderNameHint letBinder) letAnn (App f x)
--   -- _ -> traverseDecl inlineTraversalDef decl

-- -- TODO: This is a bit overeager. We should count under how many loops are we.
-- --       Even if the array is accessed in an injective fashion, the accesses might
-- --       be happen in a deeply nested loop and we might not want to repeat the
-- --       compute over and over.
-- -- inlineTraverseExpr :: Expr i -> InlineM i o (Expr o)
-- -- inlineTraverseExpr expr = case expr of
--   -- Hof (For d body) -> do
--   --   newBody <- traverseAtom inlineTraversalDef body
--   --   case newBody of
--   --     -- XXX: The trivial body might be a table lambda, and those could technically
--   --     --      get quite expensive. But I think this should never be the case in practice.
--   --     -- Trivial bodies
--   --     LamVal ib block@(Block Empty (Atom _)) -> return $ Atom $ TabVal ib block
--   --     -- Pure broadcasts
--   --     LamVal ib@(Ignore _) block | blockEffs block == Pure -> do
--   --       result <- dropSub $ evalBlockE inlineTraversalDef block
--   --       Atom <$> buildLam ib TabArrow (\_ -> return $ result)
--   --     _ -> return $ Hof $ For d newBody
--   -- App f' x' -> do
--   --   f <- traverseAtom inlineTraversalDef f'
--   --   x <- traverseAtom inlineTraversalDef x'
--   --   case f of
--   --     TabVal b body -> Atom <$> (dropSub $ extendR (b@>x) $
--   --                                  evalBlockE inlineTraversalDef body)
--   --     _ -> return $ App f x
--   -- _ -> nope
--   -- where nope = traverseExpr inlineTraversalDef expr

-- -- type InlineHintM n = State (SimpleEnv n InlineHint)

-- computeInlineHints :: forall n. Module n -> Module n
-- computeInlineHints = undefined
-- -- computeInlineHints m@(Module _ _ bindings) =
-- --     transformModuleAsBlock (flip evalState bindingsNoInline . hintBlock) m
-- --   where
-- --     usedInBindings = filter (not . isGlobal . varName) $ bindingsAsVars $ freeVars bindings
-- --     bindingsNoInline = newEnv usedInBindings (repeat NoInline)

-- --     hintBlock :: Block n -> InlineHintM n (Block n)
-- --     hintBlock (Block decls result) = do
-- --       result' <- hintExpr result  -- Traverse result before decls!
-- --       Block <$> hintDecls decls <*> pure result'

-- --     hintDecls :: Nest Decl n -> InlineHintM n (Nest Decl n)
-- --     hintDecls decls = do
-- --       let revDecls = reverse $ fromNest decls
-- --       revNewDecls <- mapM hintDecl revDecls
-- --       return $ toNest $ reverse $ revNewDecls

-- --     hintDecl :: Decl n -> InlineHintM n (Decl n)
-- --     hintDecl (Let ann b expr) = do
-- --       void $ noInlineFree b
-- --       b' <- hintBinder b
-- --       modify $ envDelete b
-- --       expr' <- hintExpr expr
-- --       return $ Let ann b' expr'

-- --     hintExpr :: Expr n -> InlineHintM n (Expr n)
-- --     hintExpr expr = case expr of
-- --       App (Var v) x  -> App  <$> (Var v <$ use v) <*> hintAtom x
-- --       App g x        -> App  <$> hintAtom g       <*> hintAtom x
-- --       Atom x         -> Atom <$> hintAtom x
-- --       Op  op         -> Op   <$> traverse hintAtom op
-- --       Hof hof        -> Hof  <$> traverse hintAtom hof
-- --       Case e alts ty -> Case <$> hintAtom e <*> traverse hintAlt alts <*> hintAtom ty

-- --     hintAlt (Abs bs block) = undefined -- Abs <$> traverse hintAbsBinder bs <*> hintBlock block

-- --     hintAtom :: Atom n -> InlineHintM n (Atom n)
-- --     hintAtom atom = case atom of
-- --       -- TODO: Is it always ok to inline e.g. into a table lambda? Even if the
-- --       --       lambda indicates that the access pattern would be injective, its
-- --       --       body can still get instantiated multiple times!
-- --       Lam (Abs b (WithArrow arr block)) -> Lam <$> (Abs <$> hintAbsBinder b <*>
-- --                                             (WithArrow arr <$> hintBlock block))
-- --       _ -> noInlineFree atom

-- --     use n = do
-- --       maybeHint <- gets $ (`envLookup` n)
-- --       let newHint = case maybeHint of
-- --                       Nothing -> CanInline
-- --                       Just _  -> NoInline
-- --       modify (<> (n @> newHint))

-- --     hintBinder :: Binder n -> InlineHintM n (Binder n)
-- --     hintBinder b = do
-- --       maybeHint <- gets $ (`envLookup` b)
-- --       case (b, maybeHint) of
-- --         (Bind v  , Just hint) -> return $ BindWithHint hint   v
-- --         (Bind v  , Nothing  ) -> return $ BindWithHint NoHint v -- TODO: Change to Ignore?
-- --         (Ignore _, Nothing  ) -> return b
-- --         (Ignore _, Just _   ) -> error "Ignore binder is not supposed to have any uses"

-- --     hintAbsBinder :: Binder n -> InlineHintM n (Binder n)
-- --     hintAbsBinder b = undefined -- modify (envDelete b) >> traverse hintAtom b

-- --     noInlineFree :: HasVars e => e n -> InlineHintM n (e n)
-- --     noInlineFree a =
-- --       modify (<> (fmap (const NoInline) (freeVars a))) >> return a
