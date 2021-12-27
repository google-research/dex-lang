-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Simplify
  ( simplifyModule, splitSimpModule, applyDataResults
  , simplifyBlock, liftSimplifyM) where

import Control.Category ((>>>))
import Control.Monad
import Control.Monad.Reader

import Err

import Name
import Builder
import Syntax
import Type
import Interpreter (traverseSurfaceAtomNames)
import Util (enumerate)
import Linearize
import Transpose

-- === simplification monad ===

class (Builder2 m, SubstReader AtomSubstVal m) => Simplifier m

newtype SimplifyM (i::S) (o::S) (a:: *) = SimplifyM
  { runSimplifyM' :: SubstReaderT AtomSubstVal (BuilderT HardFailM) i o a }
  deriving ( Functor, Applicative, Monad, ScopeReader, EnvExtender
           , EnvReader, SubstReader AtomSubstVal, MonadFail)

runSimplifyM :: Distinct n => Env n -> SimplifyM n n (e n) -> e n
runSimplifyM bindings cont =
  withImmutEvidence (toImmutEvidence bindings) $
    runHardFail $
      runBuilderT bindings $
        runSubstReaderT idSubst $
          runSimplifyM' cont

liftSimplifyM
  :: (EnvReader m, SinkableE e)
  => (forall l. (Immut l, DExt n l) => SimplifyM l l (e l))
  -> m n (e n)
liftSimplifyM cont = liftImmut do
  DB env <- getDB
  return $ runSimplifyM env $ cont

instance Simplifier SimplifyM

instance Fallible (SimplifyM i o) where
  throwErrs _ = undefined
  addErrCtx _ _ = undefined

-- TODO: figure out why we can't derive this one (here and elsewhere)
instance Builder (SimplifyM i) where
  emitDecl hint ann expr = SimplifyM $ emitDecl hint ann expr
  buildScoped cont = SimplifyM $ SubstReaderT $ ReaderT \env ->
    buildScoped $ runSubstReaderT (sink env) (runSimplifyM' cont)

-- === Top level ===

simplifyModule :: Distinct n => Env n -> Module n -> Module n
simplifyModule env (Module Core decls result) = runSimplifyM env do
  Immut <- return $ toImmutEvidence env
  DistinctAbs decls' result' <-
    buildScoped $ simplifyDecls decls $
      substEvaluatedModuleM result
  return $ Module Simp decls' result'
simplifyModule _ (Module ir _ _) = error $ "Expected Core, got: " ++ show ir

type AbsEvaluatedModule n = Abs (Nest (NameBinder AtomNameC)) EvaluatedModule n

splitSimpModule :: forall n. Distinct n
                 => Env n -> Module n
                -> (Block n , AbsEvaluatedModule n)
splitSimpModule env (Module _ decls result) = do
  runEnvReaderM env $ runSubstReaderT idNameSubst do
    Immut <- return $ toImmutEvidence env
    substBinders decls \decls' -> do
      result' <- substM result
      telescopicCaptureBlock decls' $ result'

applyDataResults :: EnvReader m
                 => AbsEvaluatedModule n -> Atom n
                 -> m n (EvaluatedModule n)
applyDataResults (Abs bs evaluated) x = do
  runSubstReaderT idSubst do
    xs <- liftM ignoreExcept $ runFallibleT1 $ unpackTelescope x
    extendSubst (bs @@> map SubstVal xs) $
      substEvaluatedModuleM evaluated

-- === All the bits of IR  ===

simplifyDecl ::  (Emits o, Simplifier m) => Decl i i' -> m i' o a -> m i o a
simplifyDecl (Let b (DeclBinding ann _ expr)) cont = case ann of
  NoInlineLet -> do
    x <- simplifyStandalone expr
    v <- emitDecl (getNameHint b) NoInlineLet (Atom x)
    extendSubst (b@>Rename v) cont
  _ -> do
    x <- simplifyExpr expr
    extendSubst (b@>SubstVal x) cont

simplifyDecls ::  (Emits o, Simplifier m) => Nest Decl i i' -> m i' o a -> m i o a
simplifyDecls Empty cont = cont
simplifyDecls (Nest decl rest) cont = simplifyDecl decl $ simplifyDecls rest cont

simplifyStandalone :: Simplifier m => Expr i -> m i o (Atom o)
simplifyStandalone (Atom (Lam (LamExpr (LamBinder b argTy arr Pure) body))) = do
  argTy' <- substM argTy
  buildPureLam (getNameHint b) arr argTy' \v ->
    extendSubst (b@>Rename v) $ simplifyBlock body
simplifyStandalone block =
  error $ "@noinline decorator applied to non-pure-function" ++ pprint block

simplifyExpr :: (Emits o, Simplifier m) => Expr i -> m i o (Atom o)
simplifyExpr expr = case expr of
  App f x -> do
    x' <- simplifyAtom x
    f' <- simplifyAtom f
    simplifyApp f' x'
  Op  op  -> mapM simplifyAtom op >>= emitOp
  Hof hof -> simplifyHof hof
  Atom x  -> simplifyAtom x
  Case e alts resultTy eff -> do
    e' <- simplifyAtom e
    eff' <- substM eff
    resultTy' <- substM resultTy
    case trySelectBranch e' of
      Just (i, args) -> do
        Abs bs body <- return $ alts !! i
        extendSubst (bs @@> map SubstVal args) $ simplifyBlock body
      Nothing -> do
        substM resultTy >>= isData >>= \case
          True -> do
            alts' <- forM alts \(Abs bs body) -> do
              bs' <- substM $ EmptyAbs bs
              buildNaryAbs bs' \xs ->
                extendSubst (bs @@> map Rename xs) $
                  buildBlock $ simplifyBlock body
            liftM Var $ emit $ Case e' alts' resultTy' eff'
          False -> defuncCase e' alts resultTy'

defuncCase :: (Emits o, Simplifier m) => Atom o -> [Alt i] -> Type o -> m i o (Atom o)
defuncCase scrut alts resultTy = do
  (alts', recons) <- unzip <$> mapM simplifyAbs alts
  closureTys <- mapM getAltTy alts'
  let closureSumTy = SumTy closureTys
  alts'' <- forM (enumerate alts') \(i, alt) -> injectAltResult closureSumTy i alt
  eff <- getAllowedEffects -- TODO: more precise effects
  sumVal <- liftM Var $ emit $ Case scrut alts'' closureSumTy eff
  reconAlts <- forM (zip closureTys recons) \(ty, recon) -> do
                 buildUnaryAtomAlt ty \v -> applyRecon (sink recon) $ Var v
  return $ ACase sumVal reconAlts resultTy

  where
    getAltTy :: EnvReader m => Alt n -> m n (Type n)
    getAltTy (Abs bs body) = liftImmut $ liftSubstEnvReaderM do
      substBinders bs \bs' -> do
        ty <- getTypeSubst body
        -- Result types of simplified abs should be hoistable past binder
        return $ ignoreHoistFailure $ hoist bs' ty

    injectAltResult :: EnvReader m => Type n -> Int -> Alt n -> m n (Alt n)
    injectAltResult sumTy con (Abs bs body) = liftBuilder do
      buildAlt (sink $ EmptyAbs bs) \vs -> do
        originalResult <- emitBlock =<< applySubst (bs@@>vs) body
        return $ Con $ SumCon (sink sumTy) con originalResult

simplifyApp :: (Emits o, Simplifier m) => Atom o -> Atom o -> m i o (Atom o)
simplifyApp f x = case f of
  Lam (LamExpr b body) ->
    dropSubst $ extendSubst (b@>SubstVal x) $ simplifyBlock body
  DataCon printName defName params con xs -> do
    DataDef _ paramBs _ <- lookupDataDef defName
    let (params', xs') = splitAt (nestLength paramBs) $ params ++ xs ++ [x]
    return $ DataCon printName defName params' con xs'
  ACase e alts (Pi piType) -> do
    -- TODO: optimization for common case where all branches are curried
    -- functions and we do the application under the ACase without emitting a
    -- case expression.
    Just (_, _, _, resultTy) <- return $ considerNonDepPiType piType
    alts' <- forM alts \(Abs bs a) -> do
      buildAlt (EmptyAbs bs) \vs -> do
        a' <- applyNaryAbs (sink $ Abs bs a) vs
        app a' (sink x)
    eff <- getAllowedEffects -- TODO: more precise effects
    dropSubst $ simplifyExpr $ Case e alts' resultTy eff
  TypeCon sn def params -> return $ TypeCon sn def params'
     where params' = params ++ [x]
  _ -> liftM Var $ emit $ App f x

simplifyAtom :: Simplifier m => Atom i -> m i o (Atom o)
simplifyAtom atom = traverseSurfaceAtomNames atom \v -> do
  env <- getSubst
  case env ! v of
    SubstVal x -> return x
    Rename v' -> do
      AtomNameBinding bindingInfo <- lookupEnv v'
      case bindingInfo of
        LetBound (DeclBinding ann _ (Atom x))
          | ann /= NoInlineLet -> dropSubst $ simplifyAtom x
        _ -> return $ Var v'

simplifyLam :: (Emits o, Simplifier m) => Atom i -> m i o (Atom o, ReconstructAtom o)
simplifyLam lam = do
  Lam (LamExpr b body) <- substM lam
  (Abs (Nest b' Empty) body', recon) <- dropSubst $ simplifyAbs $ Abs (Nest b Empty) body
  return (Lam $ LamExpr b' body', recon)

simplifyBinaryLam :: (Emits o, Simplifier m) => Atom i -> m i o (Atom o, ReconstructAtom o)
simplifyBinaryLam binaryLam = do
  Lam (LamExpr b1 (AtomicBlock (Lam (LamExpr b2 body)))) <- substM binaryLam
  (Abs (Nest b1' (Nest b2' Empty)) body', recon) <-
      dropSubst $ simplifyAbs $ Abs (Nest b1 (Nest b2 Empty)) body
  let binaryLam' = Lam $ LamExpr b1' $ AtomicBlock $ Lam $ LamExpr b2' body'
  return (binaryLam', recon)

simplifyAbs
  :: (Simplifier m, BindsEnv b, SubstB AtomSubstVal b)
  => Abs b Block i -> m i o (Abs b Block o, ReconstructAtom o)
simplifyAbs (Abs bs body) = fromPairE <$> liftImmut do
  substBinders bs \bs' -> do
    DistinctAbs decls result <- buildScoped $ simplifyBlock body
    -- TODO: this would be more efficient if we had the two-computation version of buildScoped
    extendEnv (toEnvFrag decls) do
      resultTy <- getType result
      isData resultTy >>= \case
        True -> do
          block <- makeBlock decls $ Atom result
          return $ PairE (Abs bs' block) IdentityRecon
        False -> do
          let locals = toScopeFrag bs' >>> toScopeFrag decls
          -- TODO: this might be too cautious. The type only needs to be hoistable
          -- above the delcs. In principle it can still mention vars from the lambda
          -- binders.
          (newResult, newResultTy, reconAbs) <- telescopicCapture locals result
          let block = Block (BlockAnn $ sink newResultTy) decls (Atom newResult)
          return $ PairE (Abs bs' block) (LamRecon reconAbs)

simplifyHof :: (Emits o, Simplifier m) => Hof i -> m i o (Atom o)
simplifyHof hof = case hof of
  For d lam@(Lam lamExpr) -> do
    ixTy <- substM $ lamArgType lamExpr
    (lam', recon) <- simplifyLam lam
    ans <- liftM Var $ emit $ Hof $ For d lam'
    case recon of
      IdentityRecon -> return ans
      LamRecon reconAbs ->
        buildPureLam "i" TabArrow ixTy \i' -> do
          elt <- app (sink ans) $ Var i'
          applyReconAbs (sink reconAbs) elt
  While body -> do
    (lam', IdentityRecon) <- simplifyLam body
    liftM Var $ emit $ Hof $ While lam'
  RunReader r lam -> do
    r' <- simplifyAtom r
    (lam', recon) <- simplifyBinaryLam lam
    ans <- emit $ Hof $ RunReader r' lam'
    applyRecon recon $ Var ans
  RunWriter (BaseMonoid e combine) lam -> do
    e' <- simplifyAtom e
    (combine', IdentityRecon) <- simplifyBinaryLam combine
    (lam', recon) <- simplifyBinaryLam lam
    let hof' = Hof $ RunWriter (BaseMonoid e' combine') lam'
    (ans, w) <- fromPair =<< liftM Var (emit hof')
    ans' <- applyRecon recon ans
    return $ PairVal ans' w
  RunState s lam -> do
    s' <- simplifyAtom s
    (lam', recon) <- simplifyBinaryLam lam
    resultPair <- emit $ Hof $ RunState s' lam'
    (ans, sOut) <- fromPair $ Var resultPair
    ans' <- applyRecon recon ans
    return $ PairVal ans' sOut
  RunIO lam -> do
    (lam', recon) <- simplifyLam lam
    ans <- emit $ Hof $ RunIO lam'
    applyRecon recon $ Var ans
  Linearize lam -> do
    ~(lam', IdentityRecon) <- simplifyLam lam
    -- TODO: simplify the result to remove functions introduced by linearization
    linearize lam'
  Transpose lam -> do
    ~(lam', IdentityRecon) <- simplifyLam lam
    -- TODO: simplify the result to remove functions introduced by linearization
    transpose lam'
  _ -> error $ "not implemented: " ++ pprint hof

simplifyBlock :: (Emits o, Simplifier m) => Block i -> m i o (Atom o)
simplifyBlock (Block _ decls result) = simplifyDecls decls $ simplifyExpr result
