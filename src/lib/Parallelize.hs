-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}

module Parallelize (parallelizeModule, dceModule) where

import Control.Monad.State.Strict
import Control.Monad.Reader
import Data.Foldable

import Optimize
import Syntax
import Embed
import Cat
import Env
import Type
import PPrint

-- TODO: extractParallelism can benefit a lot from horizontal fusion (can happen be after)
-- TODO: Parallelism extraction can emit some really cheap (but not trivial)
--       fors and we should inline them.
parallelizeModule :: Module -> Module
parallelizeModule = dceModule . extractParallelism

-- === Flattening parallelism ===

-- It is more convenient to treat the block result as "cheap" and treat
-- all potentially expensive operations as appearing in decls for uniformity.
data ABlock = ABlock (Nest Decl) Atom

asABlock :: Block -> ABlock
asABlock block = ABlock decls result
  where
    scope = freeVars block
    ((result, decls), _) = flip runEmbed scope $ scopedDecls $ emitBlock block


data LoopEnv = LoopEnv
  { loopBinders :: [Var]              -- In scope of the original program
  , delayedApps :: Env (Atom, [Atom]) -- (n @> (arr, bs)), n and bs in scope of the original program
                                      --   arr in scope of the newly constructed program!
  }
type TLParallelM = SubstEmbed  -- Monad for the top-level non-parallel statements
type LoopM = ReaderT LoopEnv TLParallelM

runLoopM :: LoopM a -> TLParallelM a
runLoopM m = runReaderT m $ LoopEnv mempty mempty

extractParallelism :: Module -> Module
extractParallelism = transformModuleAsBlock go
  where go block = fst $ runSubstEmbed (traverseBlock parallelTrav block) mempty

parallelTrav :: TraversalDef TLParallelM
parallelTrav = ( traverseDecl parallelTrav
               , parallelTraverseExpr
               , traverseAtom parallelTrav
               )

parallelTraverseExpr :: Expr -> TLParallelM Expr
parallelTraverseExpr expr = case expr of
  Hof (For ParallelFor _) -> traverseExpr substTraversalDef expr
  Hof (For (RegularFor _) (LamVal b body)) | isPure expr -> do
    b' <- substEmbedR b
    liftM Atom $ runLoopM $ withLoopBinder b' $ buildParallelBlock $ asABlock body
  _ -> traverseExpr parallelTrav expr

-- Precondition: This is never called with no binders in the loop env
buildParallelBlock :: ABlock -> LoopM Atom
buildParallelBlock ablock@(ABlock decls result) = do
  decision <- analyzeDecls decls
  lbs <- asks loopBinders
  let loopVars = fmap Var lbs
  case decision of
    -- The only thing an empty ABlock can do is read indices and some local variables
    -- that have been gathered into arrays. Those things are really cheap though, and
    -- emitting a for in that case would only gather them into another table.
    Emit -> case decls of
      Empty -> reduce =<< unflattenConsTab lbs =<< emitLoops (flip buildLam TabArrow) ablock
        where reduce = lift . traverseAtom appReduceTraversalDef
      _     -> unflattenConsTab lbs =<< emitLoops (buildForAnn ParallelFor) ablock
    Split prologue (arrb, loop@(Abs i lbody)) epilogue -> do
      prologueApps <- case prologue of
            Empty -> return mempty
            _ -> do
              -- TODO: This can break miserably with dependent values!
              let freeContVars = freeVars loop <> freeVars epilogue
              let prologueCtxVars = bindingsAsVars $ boundVars prologue `envIntersect` freeContVars
              let prologueBlock = ABlock prologue $ mkConsList $ fmap Var prologueCtxVars
              prologueCtxAtom <- emitLoops (buildForAnn ParallelFor) prologueBlock
              prologueCtxArrs <- mapM (unflattenConsTab lbs) =<< unzipConsListTab prologueCtxAtom
              return $ foldMap (\(v, arr) -> v @> (arr, loopVars)) $ zip prologueCtxVars prologueCtxArrs
      delayApps prologueApps $ do
        i' <- lift $ substEmbedR i
        loopAtom <- withLoopBinder i' $ buildParallelBlock $ asABlock lbody
        delayApps (arrb @> (loopAtom, loopVars)) $
          buildParallelBlock $ ABlock epilogue result

unzipConsListTab :: MonadEmbed m => Atom -> m [Atom]
unzipConsListTab tab = case getType tab of
  TabTy _ UnitTy -> return []
  TabTy _ (PairTy _ _) -> do
    (x,t) <- unzipTab tab
    (x:) <$> unzipConsListTab t
  _ -> error $ "Expected a table cons list, got: " ++ pprint (getType tab)

unflattenConsTab :: MonadEmbed m => [Var] -> Atom -> m Atom
unflattenConsTab ivs arr = buildNestedLam TabArrow (fmap Bind ivs) $ app arr . mkConsList

type Loop = Abs Binder Block
data NestDecision = Emit | Split (Nest Decl) (Binder, Loop) (Nest Decl)

pattern LoopHof :: Binder -> Block -> Expr
pattern LoopHof i body <- Hof (For _ (Lam (Abs i (PureArrow, body))))

-- TODO: Implement something less aggressive, maybe choose between different tactics?
--       After all, we might have some interesting shape information available.
--       We might also want to limit ourselves to flattening only perfectly nested loops.
analyzeDecls :: Nest Decl -> LoopM NestDecision
analyzeDecls declsNest = splitAggressively
  where
    splitAggressively = do
      let decls = toList declsNest
      let (prologue, rest) = break (\case (Let _ _ (LoopHof _ _)) -> True; _ -> False) decls
      -- TODO: Don't split if the domain is known to be small (e.g. a 3D vector)
      -- TODO: If the prologue is cheap (and probably isn't used in the epilogue), then
      --       we could decide to inline it inside the loop and replicate the compute!
      --       For example, this will unnecessarily get split into three loops:
      --       for i.
      --         xi = x i
      --         for j.
      --           xij = xi j
      --           for z.
      --             xij z
      -- TODO: Check that the loop binder is in scope given only the other binders
      --       (i.e. it's not dependent on a loop-local variable.
      --       BTW we might be able to handle the loop-local cases too, right?
      --       Because the array of locals will be emitted anyway.
      --       We might just get a length-indexed array (not that we support them yet...)!
      return $ case rest of
        [] -> Emit
        ~(Let _ b (LoopHof i body):epilogue) -> Split (toNest prologue) (b, Abs i body) (toNest epilogue)

withLoopBinder :: Binder -> LoopM a -> LoopM a
withLoopBinder b m = do
  v <- case b of
    Bind v    -> return v
    Ignore ty -> freshVarE UnknownBinder $ Bind $ (Name LoopBinderName "i" 0) :> ty
  local (\env -> env { loopBinders = loopBinders env <> [v]}) m

delayApps :: Env (Atom, [Atom]) -> LoopM a -> LoopM a
delayApps apps = local (\env -> env { delayedApps = apps <> delayedApps env })

emitLoops :: (Binder -> (Atom -> LoopM Atom) -> LoopM Atom)
          -> ABlock -> LoopM Atom
emitLoops mkFor (ABlock decls result) = do
  -- TODO: Deal with dependent binders properly
  lbs <- asks loopBinders
  dapps <- asks delayedApps
  let iterTy = mkConsListTy $ fmap varType lbs
  mkFor (Bind $ "pari" :> iterTy) $ \pari -> do
    is <- unpackConsList pari
    lift $ extendR (newEnv lbs is) $ do
      ctxEnv <- flip traverseNames dapps $ \_ (arr, idx) ->
        -- XXX: arr is namespaced in the new program
        foldM appTryReduce arr =<< substEmbedR idx
      extendR ctxEnv $ evalBlockE appReduceTraversalDef $ Block decls $ Atom result
