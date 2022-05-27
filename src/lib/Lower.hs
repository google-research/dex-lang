-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Lower (lowerFullySequential) where

import Data.Map.Strict qualified as M
import Control.Monad
import Unsafe.Coerce

import Types.Core
import Types.Primitives

import Name
import MTL1
import Core
import Builder
import QueryType
import GenericTraversal

lowerFullySequential :: EnvReader m => Block n -> m n (Block n)
lowerFullySequential b = liftM fst $ liftGenericTraverserM LFS $ traverseGenericE b

data LFS (n::S) = LFS
type LowerM = GenericTraverserM LFS
instance SinkableE LFS where
  sinkingProofE _ LFS = LFS
instance HoistableState LFS where
  hoistState _ _ LFS = LFS
  {-# INLINE hoistState #-}

instance GenericTraverser LFS where
  traverseExpr expr = case expr of
    Hof (For dir ixTy (Lam body)) -> traverseFor Nothing dir ixTy body
    _ -> traverseExprDefault expr

type Dest = Atom

traverseFor :: Emits o => Maybe (Dest o) -> ForAnn -> Atom i -> LamExpr i -> LowerM i o (Expr o)
traverseFor maybeDest dir ixTy lam@(LamExpr (LamBinder ib ty arr eff) body) = do
  initDest <- case maybeDest of
    Just  d -> return d
    Nothing -> emitOp . AllocDest =<< getTypeSubst (Hof $ For dir ixTy (Lam lam))
  destTy <- getType initDest
  ty' <- substM ty
  ixTy' <- substM ixTy
  eff' <- substM $ ignoreHoistFailure $ hoist ib eff
  body' <- buildLam noHint arr (PairTy ty' destTy) eff' \b' -> do
    (i, dest) <- fromPair $ Var b'
    idest <- emitOp $ IndexRef dest i
    extendSubst (ib @> SubstVal i) $ traverseBlockWithDest idest body
    return UnitVal
  let seqHof = Hof $ Seq dir ixTy' initDest body'
  case maybeDest of
    Just _  -> return seqHof
    Nothing -> Op . Freeze . Var <$> emit seqHof

-- Destination-passing traversals

type AtomNameMap (i'::S) (o::S) = M.Map (AtomName i') (Dest o)
type DestAssignment (i'::S) (o::S) = AtomNameMap i' o

lookupDest :: DestAssignment i' o -> AtomName i' -> Maybe (Dest o)
lookupDest = flip M.lookup

-- Matches up the free variables of the atom, with the given dest. For example, if the
-- atom is a pair of two variables, the dest might be split into per-component dests,
-- and a dest assignment mapping each side to its respective dest will be returned.
-- This function works on a best-effort basis. It's never an error to not split the dest
-- as much as possible, but it can lead to unnecessary copies being done at run-time.
decomposeDest :: Emits o => Dest o -> Atom i' -> LowerM i o (Maybe (DestAssignment i' o))
decomposeDest dest = \case
  Var v -> return $ Just $ M.singleton v dest
  _ -> return Nothing

traverseBlockWithDest :: Emits o => Dest o -> Block i -> LowerM i o ()
traverseBlockWithDest dest (Block _ decls ans) = do
  decomposeDest dest ans >>= \case
    Nothing -> do
      ans' <- traverseDeclNest decls $ traverseAtom ans
      void $ emitOp $ Place dest ans'
    Just destMap -> do
      s <- getSubst
      case isDistinctNest decls of
        Nothing -> error "Non-distinct decls?"
        Just DistinctBetween -> traverseDeclNestWithDestS destMap s decls
        -- Note that we ignore ans! Its components are written inplace through destMap.

traverseDeclNestWithDestS
  :: forall i i' l o. (Emits o, DistinctBetween l i')
  => DestAssignment i' o -> Subst AtomSubstVal l o -> Nest Decl l i' -> LowerM i o ()
traverseDeclNestWithDestS destMap s = \case
  Empty -> return ()
  Nest (Let b (DeclBinding ann _ expr)) rest -> do
    DistinctBetween <- return $ withExtEvidence rest $ shortenBetween @i' b
    let maybeDest = lookupDest destMap $ sinkBetween $ binderName b
    expr' <- withSubst s $ traverseExprWithDest maybeDest expr
    v <- emitDecl (getNameHint b) ann expr'
    traverseDeclNestWithDestS destMap (s <>> (b @> Rename v)) rest

traverseExprWithDest :: Emits o => Maybe (Dest o) -> Expr i -> LowerM i o (Expr o)
traverseExprWithDest dest expr = case expr of
  Hof (For dir ixTy (Lam body)) -> traverseFor dest dir ixTy body
  _ -> do
    expr' <- traverseExprDefault expr
    case dest of
      Nothing -> return expr'
      Just d  -> do
        ans <- Var <$> emit expr'
        void $ emitOp $ Place d ans
        return $ Atom ans

-- === Extensions to the name system ===

class DistinctBetween (n::S) (l::S)
instance DistinctBetween VoidS VoidS

data DistinctBetweenEvidence (n::S) (l::S) where
  DistinctBetween :: DistinctBetween n l => DistinctBetweenEvidence n l

fabricateDistinctBetweenEvidence :: forall n l. DistinctBetweenEvidence n l
fabricateDistinctBetweenEvidence = unsafeCoerce $ DistinctBetween @VoidS @VoidS

sinkBetween :: DistinctBetween n l => e n -> e l
sinkBetween = unsafeCoerceE

shortenBetween :: forall l n n' b. (ProvesExt b, Ext n' l, DistinctBetween n l) => b n n' -> DistinctBetweenEvidence n' l
shortenBetween _ = unsafeCoerce $ DistinctBetween @n @l

isDistinctNest :: Nest Decl n l -> Maybe (DistinctBetweenEvidence n l)
isDistinctNest nest = case noShadows $ toScopeFrag nest of
  True  -> Just $ fabricateDistinctBetweenEvidence
  False -> Nothing
