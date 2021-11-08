
-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}

module SaferNames.GenericTraversal
  (GenericTraverser (..), GenericallyTraversableE (..),
   traverseExprDefault, traverseAtomDefault) where

import SaferNames.Name
import SaferNames.Builder
import SaferNames.Syntax
import SaferNames.PPrint ()

import LabeledItems

class (Builder2 m, EnvReader Name m)
      => GenericTraverser (m::MonadKind2) where

  traverseExpr :: Emits o => Expr i -> m i o (Expr o)
  traverseExpr = traverseExprDefault

  traverseAtom :: Atom i -> m i o (Atom o)
  traverseAtom = traverseAtomDefault

traverseExprDefault :: GenericTraverser m => Emits o => Expr i -> m i o (Expr o)
traverseExprDefault expr = case expr of
  App g x -> App  <$> tge g <*> tge x
  Atom x  -> Atom <$> tge x
  Op  op  -> Op   <$> mapM tge op
  Hof hof -> Hof  <$> mapM tge hof
  Case scrut alts resultTy ->
    Case <$> tge scrut <*> mapM traverseAlt alts <*> tge resultTy

traverseAtomDefault :: GenericTraverser m => Atom i -> m i o (Atom o)
traverseAtomDefault atom = case atom of
  Var v -> Var <$> substM v
  Lam (LamExpr (LamBinder b ty arr eff) body) -> do
    ty' <- tge ty
    let hint = getNameHint b
    effAbs <- withFreshBinder hint ty' \v -> extendRenamer (b@>v) $ substM eff
    Abs b' body' <- withFreshLamBinder hint (LamBinding arr ty') effAbs \v -> do
                    extendRenamer (b@>v) $ tge body
    return $ Lam $ LamExpr b' body'
  Pi (PiType (PiBinder b ty arr) eff resultTy) -> do
    ty' <- tge ty
    ab <- withFreshPiBinder (getNameHint b) (PiBinding arr ty') \v -> do
      extendRenamer (b@>v) $
        PairE <$> substM eff <*> tge resultTy
    Abs b' (PairE effs' resultTy') <- return ab
    return $ Pi $ PiType b' effs' resultTy'
  Con con -> Con <$> mapM tge con
  TC  tc  -> TC  <$> mapM tge tc
  Eff _   -> substM atom
  DataCon sourceName (dataDefName, dataDef) params con args ->
    DataCon sourceName <$> ((,) <$> substM dataDefName <*> substM dataDef) <*>
      mapM tge params <*> pure con <*> mapM tge args
  TypeCon (dataDefName, dataDef) params ->
    TypeCon <$> ((,) <$> substM dataDefName <*> substM dataDef)
            <*> mapM tge params
  LabeledRow (Ext items rest) -> do
    items' <- mapM tge items
    rest'  <- mapM substM rest
    return $ LabeledRow $ Ext items' rest'
  Record items -> Record <$> mapM tge items
  RecordTy (Ext items rest) -> do
    items' <- mapM tge items
    rest'  <- mapM substM rest
    return $ RecordTy $ Ext items' rest'
  ProjectElt _ _ -> substM atom
  _ -> error "todo"

tge :: (GenericallyTraversableE e, GenericTraverser m) => e i -> m i o (e o)
tge = traverseGenericE

class GenericallyTraversableE (e::E) where
  traverseGenericE :: GenericTraverser m => e i -> m i o (e o)

instance GenericallyTraversableE Atom where
  traverseGenericE = traverseAtom

instance GenericallyTraversableE Module where
  traverseGenericE (Module ir decls result) = do
    Abs decls' (SubstEvaluatedModule result') <- buildScoped $
      traverseDeclNest decls $ substM $ SubstEvaluatedModule result
    return $ Module ir decls' result'

instance GenericallyTraversableE Block where
  traverseGenericE (Block ty decls result) = do
    ty' <- tge ty
    Abs decls' result' <- buildScoped $ traverseDeclNest decls $
                            traverseExpr result
    return $ Block ty' decls' result'

traverseDeclNest
  :: (GenericTraverser m, Emits o)
  => Nest Decl i i'
  -> (forall o'. (Emits o', Ext o o') => m i' o' (e o'))
  -> m i o (e o)
traverseDeclNest Empty cont = cont
traverseDeclNest (Nest (Let b (DeclBinding ann _ expr)) rest) cont = do
  expr' <- traverseExpr expr
  v <- emitDecl (getNameHint b) ann expr'
  extendEnv (b @> v) $ traverseDeclNest rest cont

traverseAlt
  :: GenericTraverser m
  => Alt i
  -> m i o (Alt o)
traverseAlt (Abs Empty body) = Abs Empty <$> tge body
traverseAlt (Abs (Nest (b:>ty) bs) body) = do
  ty' <- tge ty
  Abs b' (Abs bs' body') <-
    buildAbs ty' \v -> do
      extendRenamer (b@>v) $
        traverseAlt $ Abs bs body
  return $ Abs (Nest b' bs') body'

-- === Faking SubstE ===

-- We're pulling the same hack here as we do in inference. TODO: figure out
-- how to do scoped inference blocks without putting a `SubstE Atom`
-- on `buildScopedGeneral`.

newtype SubstEvaluatedModule (n::S) =
  SubstEvaluatedModule (EvaluatedModule n)
  deriving (HoistableE, InjectableE)

instance SubstE Name SubstEvaluatedModule where
  substE env (SubstEvaluatedModule e) = SubstEvaluatedModule $ substE env e

instance SubstE AtomSubstVal SubstEvaluatedModule where
  substE (scope, env) e = substE (scope, env') e
    where env' = newEnv \v -> case env ! v of
                   SubstVal (Var v') -> v'
                   SubstVal _ -> error "shouldn't happen"
                   Rename v' -> v'
