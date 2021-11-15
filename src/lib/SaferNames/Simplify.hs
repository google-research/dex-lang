-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}

module SaferNames.Simplify (simplifyModule, splitSimpModule) where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.Reader
import Data.Maybe
import Data.Foldable (toList)
import Data.Functor
import Data.List (partition, elemIndex)
import Data.Graph (graphFromEdges, topSort)
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import GHC.Stack

import Err
import PPrint
import Util

import SaferNames.Name
import SaferNames.Builder
import SaferNames.Syntax
import SaferNames.Type

-- === simplification monad ===

class (Builder2 m, EnvReader AtomSubstVal m) => Simplifier m

newtype SimplifyM (i::S) (o::S) (a:: *) = SimplifyM
  { runSimplifyM' :: EnvReaderT AtomSubstVal (BuilderT HardFailM) i o a }
  deriving ( Functor, Applicative, Monad, ScopeReader, Scopable
           , BindingsReader, EnvReader AtomSubstVal, MonadFail)

runSimplifyM :: Distinct n
             => Bindings n
             -> (forall l. Ext n l => SimplifyM l l (e l))
             -> e n
runSimplifyM bindings cont =
  runHardFail $
    runBuilderT bindings $
      runEnvReaderT idEnv $
        runSimplifyM' cont

instance Simplifier SimplifyM

-- TODO: figure out why we can't derive this one (here and elsewhere)
instance Builder (SimplifyM i) where
  emitDecl hint ann expr = SimplifyM $ emitDecl hint ann expr
  buildScopedGeneral ab cont = SimplifyM $
    buildScopedGeneral ab \x -> runSimplifyM' $ cont x

-- === Top level ===

simplifyModule :: Distinct n => Bindings n -> Module n -> Module n
simplifyModule bindings m@(Module Core _ _) = runSimplifyM bindings do
  Module _ decls result <- injectM m
  Abs decls' (AtomSubstEvaluatedModule result') <-
    buildScoped $ simplifyDecls decls $
      AtomSubstEvaluatedModule <$> substEvalautedModuleM result
  return $ Module Simp decls' result'
simplifyModule _ (Module ir _ _) = error $ "Expected Core, got: " ++ show ir

splitSimpModule :: Distinct n => Bindings n -> Module n
                -> (Block n , Abs Binder Module n)
splitSimpModule = undefined

-- === All the bits of IR  ===

simplifyDecl ::  (Emits o, Simplifier m) => Decl i i' -> m i' o a -> m i o a
simplifyDecl (Let b (DeclBinding ann _ expr)) cont = case ann of
  NoInlineLet -> do
    x <- simplifyStandalone expr
    v <- emitDecl (getNameHint b) NoInlineLet (Atom x)
    extendEnv (b@>Rename v) cont
  _ -> do
    x <- simplifyExpr expr
    extendEnv (b@>SubstVal x) cont

simplifyDecls ::  (Emits o, Simplifier m) => Nest Decl i i' -> m i' o a -> m i o a
simplifyDecls Empty cont = cont
simplifyDecls (Nest decl rest) cont = simplifyDecl decl $ simplifyDecls rest cont

simplifyStandalone :: Simplifier m => Expr i -> m i o (Atom o)
simplifyStandalone (Atom (Lam (LamExpr (LamBinder b argTy arr Pure) body))) = do
  argTy' <- substM argTy
  buildPureLam (getNameHint b) arr argTy' \v ->
    extendEnv (b@>Rename v) $ simplifyBlock body
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
    undefined

simplifyApp :: (Emits o, Simplifier m) => Atom o -> Atom o -> m i o (Atom o)
simplifyApp f x = case f of
  Lam (LamExpr b body) ->
    dropSubst $ extendEnv (b@>SubstVal x) $ simplifyBlock body
  DataCon printName namedDef@(defName, _) params con xs -> do
    DataDef _ paramBs _ <- getDataDef defName
    let (params', xs') = splitAt (nestLength paramBs) $ params ++ xs ++ [x]
    return $ DataCon printName namedDef params' con xs'
  ACase e alts ~(Pi ab) -> undefined
  TypeCon def params -> return $ TypeCon def params'
     where params' = params ++ [x]
  _ -> liftM Var $ emit $ App f x

simplifyAtom :: (Emits o, Simplifier m) => Atom i -> m i o (Atom o)
simplifyAtom atom = case atom of
  Var v -> do
    env <- getEnv
    case env ! v of
      SubstVal x -> return x
      Rename v' -> do
        AtomNameBinding bindingInfo <- lookupBindings v'
        case bindingInfo of
          LetBound (DeclBinding ann _ (Atom x))
            | ann /= NoInlineLet -> dropSubst $ simplifyAtom x
          _ -> return $ Var v'
  Lam _ -> substM atom
  Pi  _ -> substM atom
  Con con -> Con <$> mapM simplifyAtom con
  TC  tc  -> TC  <$> mapM simplifyAtom tc
  Eff _ -> substM atom
  TypeCon (defName, def) params -> do
    defName' <- substM defName
    def'     <- substM def
    TypeCon (defName', def') <$> mapM simplifyAtom params
  DataCon printName (defName, def) params con args -> do
    defName' <- substM defName
    def'     <- substM def
    DataCon printName (defName', def') <$> mapM simplifyAtom params
                                       <*> pure con <*> mapM simplifyAtom args
  Record items -> Record <$> mapM simplifyAtom items
  DataConRef _ _ _ -> error "Should only occur in Imp lowering"
  BoxedRef _ _ _   -> error "Should only occur in Imp lowering"
  ProjectElt idxs v -> getProjection (toList idxs) <$> simplifyAtom (Var v)

simplifyOp :: (Emits o, Simplifier m) => Op o -> m i o (Atom o)
simplifyOp op = case op of
  _ -> emitOp op

simplifyHof :: (Emits o, Simplifier m) => Hof i -> m i o (Atom o)
simplifyHof = undefined

simplifyBlock :: (Emits o, Simplifier m) => Block i -> m i o (Atom o)
simplifyBlock (Block _ decls result) = simplifyDecls decls $ simplifyExpr result

-- === Substitutible module hack ===

-- See also: "zonkable source map hack" in inference ...

newtype AtomSubstEvaluatedModule (n::S) =
  AtomSubstEvaluatedModule (EvaluatedModule n)
  deriving (HoistableE, InjectableE)

instance SubstE Name AtomSubstEvaluatedModule where
  substE env (AtomSubstEvaluatedModule e) =
    AtomSubstEvaluatedModule $ substE env e

instance SubstE AtomSubstVal AtomSubstEvaluatedModule where
  substE (scope, env) e = substE (scope, env') e
    where env' = newEnv \v -> case env ! v of
                   SubstVal (Var v') -> v'
                   SubstVal _ -> error "shouldn't happen"
                   Rename v' -> v'
