-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Parallelize (parallelizeModule, dceModule) where

import Control.Monad.State.Strict
import Control.Monad.Reader
import Data.Foldable

import Optimize
import Syntax
import Builder
import Cat
import Subst
import Type
import Util (for)

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
    ((result, decls), _) = runBuilder scope mempty $ scopedDecls $ emitBlock block

data LoopSubst = LoopEnv
  { loopBinders :: [Var]              -- In scope of the original program
  , delayedApps :: Subst (Atom, [Atom]) -- (n @> (arr, bs)), n and bs in scope of the original program
                                      --   arr in scope of the newly constructed program!
  }
data AccSubst = AccEnv { activeAccs :: Env (Var, (Var, BaseMonoid)) } -- (original region, reference, its base monoid)

type TLParallelM = SubstBuilderT (State AccSubst)   -- Top-level non-parallel statements
type LoopM       = ReaderT LoopSubst TLParallelM  -- Generation of (parallel) loop nests

runLoopM :: LoopM a -> TLParallelM a
runLoopM m = runReaderT m $ LoopSubst mempty mempty

extractParallelism :: Module -> Module
extractParallelism = transformModuleAsBlock go
  where go block = fst $ evalState (runSubstBuilderT mempty mempty
                     (traverseBlock parallelTrav block)) $ AccSubst mempty

parallelTrav :: TraversalDef TLParallelM
parallelTrav = ( traverseDecl parallelTrav
               , parallelTraverseExpr
               , traverseAtom parallelTrav
               )

parallelTraverseExpr :: Expr -> TLParallelM Expr
parallelTraverseExpr expr = case expr of
  Hof (For ParallelFor _) -> traverseExpr substTraversalDef expr
  Hof (For (RegularFor _) fbody@(LamVal b body)) -> do
    -- TODO: functionEffs is an overapproximation of the effects that really appear inside
    refs <- gets activeAccs
    let allowedRegions = foldMap (\(varType . fst . snd -> RefTy (Var reg) _) -> reg @> ()) refs
    (EffectRow bodyEffs t) <- substBuilderR $ functionEffs fbody
    let onlyAllowedEffects = all (parallelizableEffect allowedRegions) $ toList bodyEffs
    case t == Nothing && onlyAllowedEffects of
      True -> do
        b' <- substBuilderR b
        liftM Atom $ runLoopM $ withLoopBinder b' $ buildParallelBlock $ asABlock body
      False -> nothingSpecial
  Hof (RunWriter bm (BinaryFunVal h@(Bind hName) b _ body)) -> do
    ~(RefTy _ accTy) <- traverseAtom substTraversalDef $ binderType b
    liftM Atom $ emitRunWriter (binderNameHint b) accTy bm \ref@(Var refVar) -> do
      let RefTy h' _ = varType refVar
      modify \accSubst -> accEnv { activeAccs = activeAccs accEnv <> b @> (hName, (refVar, bm)) }
      res <- extendR (h @> SubstVal h' <> b @> SubstVal ref) $ evalBlockE parallelTrav body
      modify \accSubst -> accEnv { activeAccs = activeAccs accEnv `envDiff` (b @> ()) }
      return res
  -- TODO: Do some alias analysis. This is not fundamentally hard, but it is a little annoying.
  --       We would have to track not only the base references, but also all the aliases, along
  --       with their relationships. Then, when we emit local effects in emitLoops, we would have
  --       to recreate all the aliases. We could do that by carrying around a block and using
  --       SubstBuilder to take care of renaming for us.
  Op (IndexRef ref _) -> disallowRef ref >> nothingSpecial
  Op (ProjRef  _ ref) -> disallowRef ref >> nothingSpecial
  _ -> nothingSpecial
  where
    nothingSpecial = traverseExpr parallelTrav expr
    disallowRef ~(Var refVar) =
      modify \accSubst -> accEnv { activeAccs = activeAccs accEnv `envDiff` (refVar @> ()) }

parallelizableEffect :: Subst () -> Effect -> Bool
parallelizableEffect allowedRegions effect = case effect of
  RWSEffect Writer h | h `isin` allowedRegions -> True
  -- TODO: we should be able to parallelize the exception effect too
  _ -> False

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
      Empty -> reduce =<< unflattenIndexBundle lbs =<< emitLoops (flip buildLam TabArrow) ablock
        where reduce = lift . traverseAtom appReduceTraversalDef
      _     -> unflattenIndexBundle lbs =<< emitLoops (buildForAnn ParallelFor) ablock
    Split prologue (arrb, loop@(Abs i lbody)) epilogue -> do
      prologueApps <- case prologue of
            Empty -> return mempty
            _ -> do
              -- TODO: This can break miserably with dependent values!
              let freeContVars = freeVars loop <> freeVars epilogue
              let prologueCtxVars = bindingsAsVars $ boundVars prologue `envIntersect` freeContVars
              let (prologueResult, prologueBundleDesc) = mkBundle $ fmap Var prologueCtxVars
              let prologueBlock = ABlock prologue prologueResult
              prologueCtxAtom <- emitLoops (buildForAnn ParallelFor) prologueBlock
              prologueCtxArrs <- mapM (unflattenIndexBundle lbs) =<<
                                    unpackBundleTab prologueCtxAtom prologueBundleDesc
              return $ foldMap (\(v, arr) -> v @> (arr, loopVars)) $ zip prologueCtxVars prologueCtxArrs
      delayApps prologueApps $ do
        i' <- lift $ substBuilderR i
        loopAtom <- withLoopBinder i' $ buildParallelBlock $ asABlock lbody
        delayApps (arrb @> (loopAtom, loopVars)) $
          buildParallelBlock $ ABlock epilogue result

unflattenIndexBundle :: MonadBuilder m => [Var] -> Atom -> m Atom
unflattenIndexBundle []  arr = return arr
unflattenIndexBundle [_] arr = return arr
unflattenIndexBundle ivs arr = buildNaryLam TabArrow (toNest $ fmap Bind ivs) $ app arr . fst . mkBundle

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
    Ignore ty -> withNameHint ("i"::String) $ freshVarE UnknownBinder ty
  local (\env -> env { loopBinders = loopBinders env <> [v]}) m

delayApps :: Subst (Atom, [Atom]) -> LoopM a -> LoopM a
delayApps apps = local (\env -> env { delayedApps = apps <> delayedApps env })

emitLoops :: (Binder -> (Atom -> TLParallelM Atom) -> TLParallelM Atom)
          -> ABlock -> LoopM Atom
emitLoops buildPureLoop (ABlock decls result) = do
  -- TODO: Deal with dependent binders properly
  lbs <- asks loopBinders
  dapps <- asks delayedApps
  refs  <- gets activeAccs
  -- TODO: Filter out the refs that are unused in the body.
  let oldRefNames = envNames refs
  let (oldRegionNames, newRefs) = unzip $ toList refs
  let (iterTy, iterBundleDesc) = mkBundleTy $ fmap varType lbs
  let buildBody pari = do
        is <- unpackBundle pari iterBundleDesc
        extendR (newSubst lbs $ map SubstVal is) $ do
          ctxSubst <- flip traverseNames dapps \_ (arr, idx) ->
            -- XXX: arr is namespaced in the new program
            SubstVal <$> (foldM appTryReduce arr =<< substBuilderR idx)
          extendR ctxSubst $ evalBlockE appReduceTraversalDef $ Block decls $ Atom result
  lift $ case null refs of
    True -> buildPureLoop (Bind $ "pari" :> iterTy) buildBody
    False -> do
      body <- do
        buildLam (Bind $ "gtid" :> IdxRepTy) PureArrow \gtid -> do
          buildLam (Bind $ "nthr" :> IdxRepTy) PureArrow \nthr -> do
            let threadRange = TC $ ParIndexRange iterTy gtid nthr
            let writerSpecs = for newRefs \(ref, bm) -> (varName ref, derefType (varType ref), bm)
            emitRunWriters writerSpecs $ \localRefs -> do
              buildFor Fwd (Bind $ "tidx" :> threadRange) \tidx -> do
                pari <- emitOp $ Sink tidx
                let regionSubst = newEnv oldRegionNames $ for localRefs \(getType -> RefTy h _) -> SubstVal h
                extendR (regionSubst <> newEnv oldRefNames (map SubstVal localRefs)) $ buildBody pari
      (ans, updateList) <- fromPair =<< (emit $ Hof $ PTileReduce (fmap snd newRefs) iterTy body)
      updates <- unpackRightLeaningConsList updateList
      forM_ (zip newRefs updates) $ \((ref, bm), update) -> do
        updater <- mextendForRef (Var ref) bm update
        emitOp $ PrimEffect (Var ref) $ MExtend updater
      return ans
  where
    derefType ~(RefTy _ accTy) = accTy
