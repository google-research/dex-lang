-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE TypeFamilies #-}

module Transpose (transpose) where

import Control.Monad

import Type
import Name
import LabeledItems
import Syntax
import PPrint
import Builder
import Util (bindM2, zipWithT, enumerate, restructure)
import GHC.Stack

transpose :: EnvReader m => Atom n -> m n (Atom n)
transpose (Lam (LamExpr (LamBinder b ty LinArrow Pure) body)) = liftImmut do
  DB env <- getDB
  return $ runBuilderM env $ runSubstReaderT idSubst $
    buildLam "ct" LinArrow ty Pure \ct ->
      withAccumulator (sink ty) \ref ->
        extendSubst (b @> LinRef ref) $
          transposeBlock body (sink $ Var ct)
transpose _ = error "not a linear function"

-- === transposition monad ===

data TransposeSubstVal c n where
  RenameNonlin :: Name c n -> TransposeSubstVal c n
  -- accumulator references corresponding to non-ref linear variables
  LinRef :: Atom n -> TransposeSubstVal AtomNameC n
  -- as an optimization, we don't make references for trivial vector spaces
  LinTrivial :: TransposeSubstVal AtomNameC n

type TransposeM a = SubstReaderT TransposeSubstVal BuilderM a

-- TODO: it might make sense to replace substNonlin/isLin
-- with a single `trySubtNonlin :: e i -> Maybe (e o)`.
-- But for that we need a way to traverse names, like a monadic
-- version of `substE`.
substNonlin :: (SinkableE e, SubstE Name e) => e i -> TransposeM i o (e o)
substNonlin e = do
  subst <- getSubst
  fmapNamesM (\v -> case subst ! v of
                      RenameNonlin v' -> v'
                      _ -> error "not a nonlinear expression") e

isLin :: HoistableE e => e i -> TransposeM i o Bool
isLin e = do
  substVals <- mapM lookupSubstM $ freeVarsList AtomNameRep e
  return $ flip any substVals \case
    LinTrivial     -> True
    LinRef _       -> True
    RenameNonlin _ -> False

withAccumulatorSubst
  :: Emits o
  => AtomNameBinder i i'
  -> Type o
  -> (forall o'. (Emits o', DExt o o') => TransposeM i' o' ())
  -> TransposeM i o (Atom o)
withAccumulatorSubst b ty cont = do
  singletonTypeVal ty >>= \case
    -- as an optimization, don't make a trivial accumulator
    Just singletonVal -> extendSubst (b@>LinTrivial) do
      Distinct <- getDistinct
      cont
      return singletonVal
    Nothing -> withAccumulator ty \ref -> extendSubst (b@>LinRef ref) cont

withAccumulator
  :: Emits o
  => Type o
  -> (forall o'. (Emits o', DExt o o') => Atom o' -> TransposeM i o' ())
  -> TransposeM i o (Atom o)
withAccumulator ty cont = do
  baseTy <- getBaseMonoidType ty
  baseMonoid <- tangentBaseMonoidFor baseTy
  getSnd =<< emitRunWriter "ref" ty baseMonoid \ref ->
               cont (Var ref) >> return UnitVal

emitCTToRef :: (Emits n, Builder m) => Atom n -> Atom n -> m n ()
emitCTToRef ref ct =
  void . emitOp . PrimEffect ref . MExtend =<< updateAddAt ct

-- === actual pass ===

transposeBlock :: Emits o => Block i -> Atom o -> TransposeM i o ()
transposeBlock (Block _ decls result) ct = transposeWithDecls decls result ct

transposeWithDecls :: Emits o => Nest Decl i i' -> Expr i' -> Atom o -> TransposeM i o ()
transposeWithDecls Empty expr ct = transposeExpr expr ct
transposeWithDecls (Nest (Let b (DeclBinding _ ty expr)) rest) result ct =
  isLin expr >>= \case
    True  -> do
      ty' <- substNonlin ty
      ctExpr <- withAccumulator ty' \ref ->
                  extendSubst (b @> LinRef ref) $
                    transposeWithDecls rest result (sink ct)
      transposeExpr expr ctExpr
    False -> do
      v <- emit =<< substNonlin expr
      extendSubst (b @> RenameNonlin v) $
        transposeWithDecls rest result ct

transposeExpr :: Emits o => Expr i -> Atom o -> TransposeM i o ()
transposeExpr expr ct = case expr of
  Op op         -> transposeOp op ct
  Atom atom     -> transposeAtom atom ct

transposeOp :: Emits o => Op i -> Atom o -> TransposeM i o ()
transposeOp op ct = case op of
  ScalarUnOp  FNeg x    -> transposeAtom x =<< neg ct
  ScalarUnOp  _    _    -> notLinear
  ScalarBinOp FAdd x y  -> transposeAtom x ct >> transposeAtom y ct
  ScalarBinOp FSub x y  -> transposeAtom x ct >> (transposeAtom y =<< neg ct)
  ScalarBinOp FMul x y  -> do
    xLin <- isLin x
    if xLin
      then transposeAtom x =<< mul ct =<< substNonlin y
      else transposeAtom y =<< mul ct =<< substNonlin x
  where notLinear = error $ "Can't transpose a non-linear operation: " ++ pprint op

transposeAtom :: Emits o => Atom i -> Atom o -> TransposeM i o ()
transposeAtom atom ct = case atom of
  Var v -> do
    lookupSubstM v >>= \case
      RenameNonlin _ -> error "an error, I think?"
      LinRef ref -> emitCTToRef ref ct
      LinTrivial -> return ()
  Con con         -> transposeCon con ct
  Record e        -> void $ zipWithT transposeAtom e =<< getUnpacked ct
  DepPair _ _ _   -> notImplemented
  DataCon _ _ _ _ e -> void $ zipWithT transposeAtom e =<< getUnpacked ct
  Variant _ _ _ _ -> notImplemented
  TabVal b body   -> do
    ty <- substNonlin $ binderType b
    void $ buildFor "i" Fwd ty \i -> do
      ct' <- app (sink ct) (Var i)
      extendSubst (b@>RenameNonlin i) $ transposeBlock body ct'
      return UnitVal
  Lam _           -> notTangent
  TypeCon _ _ _   -> notTangent
  LabeledRow _    -> notTangent
  RecordTy _      -> notTangent
  VariantTy _     -> notTangent
  Pi _            -> notTangent
  DepPairTy _     -> notTangent
  TC _            -> notTangent
  Eff _           -> notTangent
  ACase _ _ _     -> error "Unexpected ACase"
  DataConRef _ _ _ -> error "Unexpected ref"
  BoxedRef _ _     -> error "Unexpected ref"
  DepPairRef _ _ _ -> error "Unexpected ref"
  ProjectElt _ _ -> undefined
  where notTangent = error $ "Not a tangent atom: " ++ pprint atom

transposeCon :: Con i -> Atom o -> TransposeM i o ()
transposeCon con ct = case con of
  Lit _             -> return ()
  ProdCon []        -> return ()

notImplemented :: HasCallStack => a
notImplemented = error "Not implemented"

-- === instances ===

instance GenericE (TransposeSubstVal c) where
  type RepE (TransposeSubstVal c) = EitherE (Name c) Atom

instance SinkableE (TransposeSubstVal c)
instance SinkableV TransposeSubstVal

instance FromName TransposeSubstVal where
  fromName v = RenameNonlin v
