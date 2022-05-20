-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Optimize (earlyOptimize) where

import Control.Monad

import Types.Core
import Types.Primitives
import MTL1
import Name
import Core
import GenericTraversal
import Builder
import QueryType

earlyOptimize :: EnvReader m => Block n -> m n (Block n)
earlyOptimize = unrollTrivialLoops

-- === Trivial loop unrolling ===
-- This pass unrolls loops that use Fin 0 or Fin 1 as an index set.

data UTLS n = UTLS
type UTLM = GenericTraverserM UTLS
instance SinkableE UTLS where
  sinkingProofE _ UTLS = UTLS
instance HoistableState UTLS where
  hoistState _ _ _ = UTLS
  {-# INLINE hoistState #-}

data IndexSetKind n
  = EmptyIxSet
  | SingletonIxSet (Atom n)
  | UnknownIxSet

isTrivialIndex :: Type i -> UTLM i o (IndexSetKind o)
isTrivialIndex = \case
  TC (Fin     (IdxRepVal n)) | n <= 0 -> return EmptyIxSet
  TC (Fin  nv@(IdxRepVal n)) | n == 1 ->
    liftM (SingletonIxSet . Con) $ FinVal <$> substM nv <*> pure (IdxRepVal 0)
  _ -> return UnknownIxSet

instance GenericTraverser UTLS where
  traverseExpr expr = case expr of
    Hof (For _ (IxTy ixTy) (Lam (LamExpr b body@(Block _ decls a)))) -> do
      isTrivialIndex (binderType b) >>= \case
        UnknownIxSet     -> traverseExprDefault expr
        SingletonIxSet i -> do
          ixTy' <- substM ixTy
          ans <- extendSubst (b @> SubstVal i) $ traverseDeclNest decls $ traverseAtom a
          liftM Atom $ buildTabLam noHint ixTy' $ const $ return $ sink ans
        EmptyIxSet -> do
          ixTy' <- substM ixTy
          liftM Atom $ buildTabLam noHint ixTy' \i -> do
            resTy' <- extendSubst (b @> Rename i) $ getTypeSubst body
            emitOp $ ThrowError (sink resTy')
    _ -> traverseExprDefault expr

unrollTrivialLoops :: EnvReader m => Block n -> m n (Block n)
unrollTrivialLoops b = liftM fst $ liftGenericTraverserM UTLS $ traverseGenericE b
