-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Simplify
  ( simplifyModule, splitSimpModule, applyDataResults) where

import Control.Category ((>>>))
import Control.Monad
import Control.Monad.Reader
import Data.Foldable (toList)

import Err

import Name
import Builder
import Syntax
import Type

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
simplifyModule bindings (Module Core decls result) = runSimplifyM bindings do
  Immut <- return $ toImmutEvidence bindings
  DistinctAbs decls' result' <-
    buildScoped $ simplifyDecls decls $
      substEvaluatedModuleM result
  return $ Module Simp decls' result'
simplifyModule _ (Module ir _ _) = error $ "Expected Core, got: " ++ show ir

type AbsEvaluatedModule n = Abs (Nest (NameBinder AtomNameC)) EvaluatedModule n

splitSimpModule :: Distinct n => Env n -> Module n
                -> (Block n , AbsEvaluatedModule n)
splitSimpModule bindings (Module _ decls result) = do
  let (vs, recon) = captureClosure decls result
  let resultTup = Atom $ ProdVal $ map Var vs
  let block = runHardFail $ runEnvReaderT bindings $
                refreshAbsM (Abs decls resultTup) \decls' result' ->
                  makeBlock decls' result'
  (block, recon)

applyDataResults :: EnvReader m
                 => AbsEvaluatedModule n -> Atom n
                 -> m n (EvaluatedModule n)
applyDataResults (Abs bs evaluated) x = do
  runSubstReaderT idSubst do
    xs <- liftM ignoreExcept $ runFallibleT1 $ getUnpacked x
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
  Op  op  -> mapM simplifyAtom op >>= simplifyOp
  Hof hof -> simplifyHof hof
  Atom x  -> simplifyAtom x
  Case e alts resultTy -> do
    e' <- simplifyAtom e
    resultTy' <- substM resultTy
    case trySelectBranch e' of
      Just (i, args) -> do
        Abs bs body <- return $ alts !! i
        extendSubst (bs @@> map SubstVal args) $ simplifyBlock body
      Nothing -> do
        alts' <- forM alts \(Abs bs body) -> do
          bs' <- substM $ EmptyAbs bs
          buildNaryAbs bs' \xs ->
            extendSubst (bs @@> map Rename xs) $
              buildBlock $ simplifyBlock body
        liftM Var $ emit $ Case e' alts' resultTy'

simplifyApp :: (Emits o, Simplifier m) => Atom o -> Atom o -> m i o (Atom o)
simplifyApp f x = case f of
  Lam (LamExpr b body) ->
    dropSubst $ extendSubst (b@>SubstVal x) $ simplifyBlock body
  DataCon printName defName params con xs -> do
    DataDef _ paramBs _ <- lookupDataDef defName
    let (params', xs') = splitAt (nestLength paramBs) $ params ++ xs ++ [x]
    return $ DataCon printName defName params' con xs'
  ACase _ _ ~(Pi _) -> undefined
  TypeCon sn def params -> return $ TypeCon sn def params'
     where params' = params ++ [x]
  _ -> liftM Var $ emit $ App f x

simplifyAtom :: (Emits o, Simplifier m) => Atom i -> m i o (Atom o)
simplifyAtom atom = case atom of
  Var v -> do
    env <- getSubst
    case env ! v of
      SubstVal x -> return x
      Rename v' -> do
        AtomNameBinding bindingInfo <- lookupEnv v'
        case bindingInfo of
          LetBound (DeclBinding ann _ (Atom x))
            | ann /= NoInlineLet -> dropSubst $ simplifyAtom x
          _ -> return $ Var v'
  Lam _ -> substM atom
  Pi  _ -> substM atom
  Con con -> Con <$> mapM simplifyAtom con
  TC  tc  -> TC  <$> mapM simplifyAtom tc
  Eff _ -> substM atom
  TypeCon sn defName params -> do
    defName' <- substM defName
    TypeCon sn defName' <$> mapM simplifyAtom params
  DataCon printName defName params con args -> do
    defName' <- substM defName
    DataCon printName defName' <$> mapM simplifyAtom params
                                       <*> pure con <*> mapM simplifyAtom args
  Record items -> Record <$> mapM simplifyAtom items
  DataConRef _ _ _ -> error "Should only occur in Imp lowering"
  BoxedRef _ _ _   -> error "Should only occur in Imp lowering"
  ProjectElt idxs v -> getProjection (toList idxs) <$> simplifyAtom (Var v)
  _ -> error "not implemented"

simplifyOp :: (Emits o, Simplifier m) => Op o -> m i o (Atom o)
simplifyOp op = case op of
  PrimEffect ref (MExtend f) -> dropSubst $ do
    (f', IdentityRecon) <- simplifyLam f
    emitOp $ PrimEffect ref $ MExtend f'
  _ -> emitOp op

data Reconstruct n =
   IdentityRecon
 | LamRecon (NaryAbs AtomNameC Atom n)

applyRecon :: (Emits n, Builder m) => Reconstruct n -> Atom n -> m n (Atom n)
applyRecon IdentityRecon x = return x
applyRecon (LamRecon ab) x = do
  xs <- getUnpacked x
  applyNaryAbs ab $ map SubstVal xs

simplifyLam :: (Emits o, Simplifier m) => Atom i -> m i o (Atom o, Reconstruct o)
simplifyLam lam = do
  Lam (LamExpr b body) <- substM lam
  (Abs (Nest b' Empty) body', recon) <- dropSubst $ simplifyNaryLam $ Abs (Nest b Empty) body
  return (Lam $ LamExpr b' body', recon)

simplifyBinaryLam :: (Emits o, Simplifier m) => Atom i -> m i o (Atom o, Reconstruct o)
simplifyBinaryLam binaryLam = do
  Lam (LamExpr b1 (AtomicBlock (Lam (LamExpr b2 body)))) <- substM binaryLam
  (Abs (Nest b1' (Nest b2' Empty)) body', recon) <-
      dropSubst $ simplifyNaryLam $ Abs (Nest b1 (Nest b2 Empty)) body
  let binaryLam' = Lam $ LamExpr b1' $ AtomicBlock $ Lam $ LamExpr b2' body'
  return (binaryLam', recon)

simplifyNaryLam :: Simplifier m => NaryLam i -> m i o (NaryLam o, Reconstruct o)
simplifyNaryLam (Abs bs body) = fromPairE <$> liftImmut do
  refreshBinders bs \bs' -> do
    DistinctAbs decls result <- buildScoped $ simplifyBlock body
    -- TODO: this would be more efficient if we had the two-computation version of buildScoped
    extendEnv (toEnvFrag decls) do
      (resultData, recon) <- defuncAtom (toScopeFrag bs' >>> toScopeFrag decls) result
      block <- makeBlock decls $ Atom resultData
      return $ PairE (Abs bs' block) recon

defuncAtom :: EnvReader m => ScopeFrag n l -> Atom l -> m l (Atom l, Reconstruct n)
defuncAtom _ x = do
  xTy <- getType x
  if isData xTy
    then return (x, IdentityRecon)
    else error "todo"

isData :: Type n -> Bool
isData _ = True  -- TODO!

simplifyHof :: (Emits o, Simplifier m) => Hof i -> m i o (Atom o)
simplifyHof hof = case hof of
  For d lam -> do
    (lam', recon) <- simplifyLam lam
    ans <- liftM Var $ emit $ Hof $ For d lam'
    case recon of
      IdentityRecon -> return ans
      LamRecon _ -> undefined
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
  _ -> error $ "not implemented: " ++ pprint hof

simplifyBlock :: (Emits o, Simplifier m) => Block i -> m i o (Atom o)
simplifyBlock (Block _ decls result) = simplifyDecls decls $ simplifyExpr result

-- === instances ===

instance GenericE Reconstruct where
  type RepE Reconstruct = EitherE UnitE (NaryAbs AtomNameC Atom)
  toE = undefined
  fromE = undefined

instance SinkableE Reconstruct
instance HoistableE  Reconstruct
instance SubstE Name Reconstruct
instance SubstE AtomSubstVal Reconstruct
instance AlphaEqE Reconstruct
