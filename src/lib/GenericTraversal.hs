
-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}

module GenericTraversal
  (GenericTraverser (..), GenericallyTraversableE (..),
   traverseExprDefault, traverseAtomDefault) where

import Control.Monad

import Name
import Builder
import Syntax
import Type
import PPrint

import LabeledItems

class (ScopableBuilder2 m, SubstReader Name m)
      => GenericTraverser (m::MonadKind2) where

  traverseExpr :: Emits o => Expr i -> m i o (Expr o)
  traverseExpr = traverseExprDefault

  traverseAtom :: Atom i -> m i o (Atom o)
  traverseAtom = traverseAtomDefault

traverseExprDefault :: Emits o => GenericTraverser m => Expr i -> m i o (Expr o)
traverseExprDefault expr = case expr of
  App g xs -> App <$> tge g <*> mapM tge xs
  Atom x  -> Atom <$> tge x
  Op  op  -> Op   <$> mapM tge op
  Hof hof -> Hof  <$> mapM tge hof
  Case scrut alts resultTy effs ->
    Case <$> tge scrut <*> mapM traverseAlt alts <*> tge resultTy <*> substM effs

traverseAtomDefault :: GenericTraverser m => Atom i -> m i o (Atom o)
traverseAtomDefault atom = case atom of
  Var v -> Var <$> substM v
  Lam (LamExpr (LamBinder b ty arr eff) body) -> do
    ty' <- tge ty
    let hint = getNameHint b
    effAbs <- withFreshBinder hint ty' \b' ->
      extendRenamer (b@>binderName b') do
        Abs (b':>ty') <$> substM eff
    withFreshLamBinder hint (LamBinding arr ty') effAbs \b' -> do
      extendRenamer (b@>binderName b') do
        body' <- tge body
        return $ Lam $ LamExpr b' body'
  Pi (PiType (PiBinder b ty arr) eff resultTy) -> do
    ty' <- tge ty
    withFreshPiBinder (getNameHint b) (PiBinding arr ty') \b' -> do
      extendRenamer (b@>binderName b') $
        Pi <$> (PiType b' <$> substM eff <*> tge resultTy)
  Con con -> Con <$> mapM tge con
  TC  tc  -> TC  <$> mapM tge tc
  Eff _   -> substM atom
  DataCon sourceName dataDefName params con args ->
    DataCon sourceName <$> substM dataDefName <*>
      mapM tge params <*> pure con <*> mapM tge args
  TypeCon sn dataDefName params ->
    TypeCon sn <$> substM dataDefName <*> mapM tge params
  LabeledRow elems -> LabeledRow <$> traverseGenericE elems
  Record items -> Record <$> mapM tge items
  RecordTy elems -> RecordTy <$> traverseGenericE elems
  Variant (Ext types rest) label i value -> do
    types' <- mapM tge types
    rest'  <- mapM substM rest
    value' <- tge value
    return $ Variant (Ext types' rest') label i value'
  VariantTy (Ext items rest) -> do
    items' <- mapM tge items
    rest'  <- mapM substM rest
    return $ VariantTy $ Ext items' rest'
  ProjectElt _ _ -> substM atom
  _ -> error $ "not implemented: " ++ pprint atom

tge :: (GenericallyTraversableE e, GenericTraverser m)
    => e i -> m i o (e o)
tge = traverseGenericE

class GenericallyTraversableE (e::E) where
  traverseGenericE :: GenericTraverser m => e i -> m i o (e o)

instance GenericallyTraversableE Atom where
  traverseGenericE = traverseAtom

instance GenericallyTraversableE Block where
  traverseGenericE (Block _ decls result) = do
    Abs decls' (PairE ty result') <-
      buildScoped $ traverseDeclNest decls do
        result' <- traverseExpr result
        resultTy <- getType result'
        return $ PairE resultTy result'
    ty' <- liftHoistExcept $ hoist decls' ty
    return $ Block (BlockAnn ty') decls' result'

instance GenericallyTraversableE FieldRowElems where
  traverseGenericE elems = do
    els' <- fromFieldRowElems <$> substM elems
    dropSubst $ fieldRowElemsFromList <$> forM els' \case
      StaticFields items  -> StaticFields <$> mapM tge items
      DynField  labVar ty -> DynField labVar <$> tge ty
      DynFields rowVar    -> return $ DynFields rowVar

traverseDeclNest
  :: (GenericTraverser m, Emits o)
  => Nest Decl i i'
  -> (forall o'. (Emits o', Ext o o') => m i' o' (e o'))
  -> m i o (e o)
traverseDeclNest Empty cont = cont
traverseDeclNest (Nest (Let b (DeclBinding ann _ expr)) rest) cont = do
  expr' <- traverseExpr expr
  v <- emitDecl (getNameHint b) ann expr'
  extendSubst (b @> v) $ traverseDeclNest rest cont

traverseAlt
  :: GenericTraverser m
  => Alt i
  -> m i o (Alt o)
traverseAlt (Abs Empty body) = Abs Empty <$> tge body
traverseAlt (Abs (Nest (b:>ty) bs) body) = do
  ty' <- tge ty
  Abs b' (Abs bs' body') <-
    buildAbs (getNameHint b) ty' \v -> do
      extendRenamer (b@>v) $
        traverseAlt $ Abs bs body
  return $ Abs (Nest b' bs') body'
