-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module Lower ( lowerFullySequential, DestExpr) where

import Prelude hiding ((.))
import Data.Functor
import Data.Maybe (fromJust)
import Data.List.NonEmpty qualified as NE
import Control.Category
import Control.Monad.Reader
import Unsafe.Coerce

import Builder
import Core
import Imp
import IRVariants
import Name
import Subst
import QueryType
import Types.Core
import Types.Primitives
import Util (enumerate)
import Visit

-- === For loop resolution ===

-- The `lowerFullySequential` pass makes two related changes:
-- - All `for` loops become `seq` loops
-- - Arrays are now explicily allocated as `Dest`s (whither the
--   content is written in due course)
--
-- We also perform destination passing here, to elide as many copies
-- as possible.
--
-- The idea for multithreading parallelism is to add IR elements that
-- specify parallelization strategy (`Seq` specifies sequential
-- execution) and add lowerings similar to lowerFullySequential that
-- choose which one(s) to use.

-- The `For` constructor of `PrimHof` disappears from the IR due to
-- this pass, and the `Seq`, `AllocDest`, `Place`, `RememberDest`, and
-- `Freeze` constructors appear.
--
-- All the `Place`s in the resulting IR are non-conflicting: every
-- array element is only written to once.
--
-- The traversal for a block or subexpression returns an `Atom`
-- representing the returned value.  If a destination was passed in,
-- the traversal is also responsible for arranging to write that value
-- into that destination (possibly by forwarding (a part of) the
-- destination to a sub-block or sub-expression, hence "desintation
-- passing style").

type DestExpr = Abs (SBinder) SExpr

lowerFullySequential :: EnvReader m => Bool -> STopLam n -> m n (STopLam n)
lowerFullySequential wantDestStyle (TopLam False piTy (LamExpr bs body)) = undefined
-- lowerFullySequential wantDestStyle (TopLam False piTy (LamExpr bs body)) = liftEnvReaderM $ do
--   lam <- case wantDestStyle of
--     True -> do
--       refreshAbs (Abs bs body) \bs' body' -> do
--         xs <- bindersToAtoms bs'
--         EffTy _ resultTy <- instantiate (sink piTy) xs
--         Abs b body'' <- lowerFullySequentialExpr resultTy body'
--         return $ LamExpr (bs' >>> UnaryNest b) body''
--     False -> do
--       refreshAbs (Abs bs body) \bs' body' -> do
--         body'' <- lowerFullySequentialExprNoDest body'
--         return $ LamExpr bs' body''
--   piTy' <- getLamExprType lam
--   return $ TopLam wantDestStyle piTy' lam
-- lowerFullySequential _ (TopLam True _ _) = error "already in destination style"

lowerFullySequentialExpr :: EnvReader m => SType n -> SExpr n -> m n (DestExpr n)
lowerFullySequentialExpr resultTy b = undefined
-- lowerFullySequentialExpr resultTy b = liftAtomSubstBuilder do
--   let resultDestTy = RawRefTy resultTy
--   withFreshBinder (getNameHint @String "ans") resultDestTy \destBinder -> do
--     Abs destBinder <$> buildBlockExpr do
--       let dest = Var $ sink $ binderVar destBinder
--       lowerExprWithDest dest b $> UnitVal
-- {-# SCC lowerFullySequentialExpr #-}

lowerFullySequentialExprNoDest :: EnvReader m => SExpr n -> m n (SExpr n)
lowerFullySequentialExprNoDest b = liftAtomSubstBuilder $ buildBlockExpr $ lowerExpr b
{-# SCC lowerFullySequentialExprNoDest #-}

data LowerTag
type LowerM = AtomSubstBuilder LowerTag SimpIR

instance NonAtomRenamer (LowerM i o) i o where renameN = substM

instance ExprVisitorEmits (LowerM i o) SimpIR i o where
  visitExprEmits = lowerExpr

instance Visitor (LowerM i o) SimpIR i o where
  visitExpr = undefined
  visitType = visitTypeDefault
  visitPi   = visitPiDefault
  visitLam  = visitLamEmits

lowerExpr :: Emits o => SExpr i -> LowerM i o (SAtom o)
lowerExpr expr = undefined
-- lowerExpr expr = emitExpr =<< case expr of
--   TabCon Nothing ty els -> lowerTabCon Nothing ty els
--   PrimOp (Hof (TypedHof (EffTy _ resultTy) (For dir ixDict body))) -> do
--     resultTy' <- substM resultTy
--     lowerFor resultTy' Nothing dir ixDict body
--   -- this case is important because this pass changes effects
--   PrimOp (Hof (TypedHof _ hof)) ->
--     PrimOp . Hof <$> (visitGeneric hof >>= mkTypedHof)
--   Case e alts (EffTy _ ty) -> lowerCase Nothing e alts ty
--   _ -> visitGeneric expr

-- lowerBlock :: Emits o => SBlock i -> LowerM i o (SAtom o)
-- lowerBlock = visitBlockEmits

type Dest = Atom

lowerFor
  :: Emits o
  => SType o -> Maybe (Dest SimpIR o) -> ForAnn -> IxType SimpIR i -> LamExpr SimpIR i
  -> LowerM i o (SExpr o)
lowerFor ansTy maybeDest dir ixTy (UnaryLamExpr (ib:>ty) body) = undefined
-- lowerFor ansTy maybeDest dir ixTy (UnaryLamExpr (ib:>ty) body) = do
--   ixTy' <- substM ixTy
--   ty' <- substM ty
--   case isSingletonType ansTy of
--     True -> do
--       body' <- buildUnaryLamExpr noHint (PairTy ty' UnitTy) \b' -> do
--         (i, _) <- fromPair $ Var b'
--         extendSubst (ib @> SubstVal i) $ lowerExpr body $> UnitVal
--       void $ emitSeq dir ixTy' UnitVal body'
--       Atom . fromJust <$> singletonTypeVal ansTy
--     False -> do
--       initDest <- ProdVal . (:[]) <$> case maybeDest of
--         Just  d -> return d
--         Nothing -> emitOp $ DAMOp $ AllocDest ansTy
--       let destTy = getType initDest
--       body' <- buildUnaryLamExpr noHint (PairTy ty' destTy) \b' -> do
--         (i, destProd) <- fromPair $ Var b'
--         dest <- normalizeProj (ProjectProduct 0) destProd
--         idest <- emitOp =<< mkIndexRef dest i
--         extendSubst (ib @> SubstVal i) $ lowerExprWithDest idest body $> UnitVal
--       ans <- emitSeq dir ixTy' initDest body' >>= getProj 0
--       return $ PrimOp $ DAMOp $ Freeze ans
-- lowerFor _ _ _ _ _ = error "expected a unary lambda expression"

lowerTabCon :: forall i o. Emits o
  => Maybe (Dest SimpIR o) -> SType i -> [SAtom i] -> LowerM i o (SExpr o)
lowerTabCon maybeDest tabTy elems = undefined
-- lowerTabCon maybeDest tabTy elems = do
--   TabPi tabTy' <- substM tabTy
--   dest <- case maybeDest of
--     Just  d -> return d
--     Nothing -> emitExpr $ PrimOp $ DAMOp $ AllocDest $ TabPi tabTy'
--   Abs bord ufoBlock <- buildAbs noHint IdxRepTy \ord -> do
--     buildBlock $ unsafeFromOrdinal (sink $ tabIxType tabTy') $ Var $ sink ord
--   -- This is emitting a chain of RememberDest ops to force `dest` to be used
--   -- linearly, and to force reads of the `Freeze dest'` result not to be
--   -- reordered in front of the writes.
--   -- TODO: We technically don't need to sequentialize the writes, since the
--   -- slices are all independent of each other.  Do we need a new `JoinDests`
--   -- operation to represent that pattern?
--   let go incoming_dest [] = return incoming_dest
--       go incoming_dest ((ord, e):rest) = do
--         i <- dropSubst $ extendSubst (bord@>SubstVal (IdxRepVal (fromIntegral ord))) $
--           lowerExpr ufoBlock
--         carried_dest <- buildRememberDest "dest" incoming_dest \local_dest -> do
--           idest <- indexRef (Var local_dest) (sink i)
--           place (FullDest idest) =<< visitAtom e
--           return UnitVal
--         go carried_dest rest
--   dest' <- go dest (enumerate elems)
--   return $ PrimOp $ DAMOp $ Freeze (toExpr dest')

lowerCase :: Emits o
  => Maybe (Dest SimpIR o) -> SAtom i -> [Alt SimpIR i] -> SType i
  -> LowerM i o (SExpr o)
lowerCase maybeDest scrut alts resultTy = undefined
-- lowerCase maybeDest scrut alts resultTy = do
--   resultTy' <- substM resultTy
--   dest <- case maybeDest of
--     Just  d -> return d
--     Nothing -> emitExpr $ PrimOp $ DAMOp $ AllocDest resultTy'
--   scrut' <- visitAtom scrut
--   dest' <- buildRememberDest "case_dest" dest \local_dest -> do
--     alts' <- forM alts \(Abs (b:>ty) body) -> do
--       ty' <- substM ty
--       buildAbs (getNameHint b) ty' \b' ->
--         extendSubst (b @> Rename (atomVarName b')) $
--           buildBlock do
--             lowerExprWithDest (Just $ AVar $ sink $ local_dest) body $> UnitVal
--     void $ mkCase (sink scrut') UnitTy alts' >>= emitExpr
--     return UnitVal
--   return $ PrimOp $ DAMOp $ Freeze dest'

-- Destination-passing traversals
--
-- The idea here is to try to reuse the memory already allocated for outputs of surrounding
-- higher order functions for values produced inside nested blocks. As an example,
-- consider two perfectly nested for loops:
--
-- for i:(Fin 10).
--   v = for j:(Fin 20). ...
--   v
--
-- (binding of the for as v is necessary since Blocks end with Atoms).
--
-- The outermost loop will have to allocate the memory for a 2D array. But it would be
-- a waste if the inner loop kept allocating 20-element blocks only to copy them into
-- that full outermost buffer. Instead, we invoke lowerBlockWithDest on the body
-- of the i-loop, which will realize that v has a valid destination. Then,
-- lowerExprWithDest will be called at the for decl and will translate the j-loop
-- so that it never allocates scratch space for its result, but will put it directly in
-- the corresponding slice of the full 2D buffer.

type DestAssignment (i'::S) (o::S) = NameMap (AtomNameC SimpIR) (ProjDest o) i'

data ProjDest o
  = FullDest (Dest SimpIR o)
  | ProjDest (NE.NonEmpty Projection) (Dest SimpIR o)  -- dest corresponds to the projection applied to name
  deriving (Show)

instance SinkableE ProjDest where
  sinkingProofE = todoSinkableProof

lookupDest :: DestAssignment i' o -> SAtomName i' -> Maybe (ProjDest o)
lookupDest dests = fmap fromLiftE . flip lookupNameMapE dests

-- Matches up the free variables of the atom, with the given dest. For example, if the
-- atom is a pair of two variables, the dest might be split into per-component dests,
-- and a dest assignment mapping each side to its respective dest will be returned.
-- This function works on a best-effort basis. It's never an error to not split the dest
-- as much as possible, but it can lead to unnecessary copies being done at run-time.
--
-- XXX: When adding more cases, be careful about potentially repeated vars in the output!
decomposeDest :: Emits o => Dest SimpIR o -> SAtom i' -> LowerM i o (Maybe (DestAssignment i' o))
decomposeDest dest = \case
  AVar v -> return $ Just $ singletonNameMapE (atomVarName v) $ LiftE $ FullDest dest
  _ -> return Nothing

-- lowerBlockWithDest :: Emits o => Dest SimpIR o -> SBlock i -> LowerM i o (SAtom o)
-- lowerBlockWithDest dest (Abs decls ans) = undefined
-- lowerBlockWithDest dest (Abs decls ans) = do
--   decomposeDest dest ans >>= \case
--     Nothing -> do
--       ans' <- visitDeclsEmits decls $ visitAtom ans
--       place (FullDest dest) ans'
--       return ans'
--     Just destMap -> do
--       s <- getSubst
--       case isDistinctNest decls of
--         Nothing -> error "Non-distinct decls?"
--         Just DistinctBetween -> do
--           s' <- traverseDeclNestWithDestS destMap s decls
--           -- But we have to emit explicit writes, for all the vars that are not defined in decls!
--           forM_ (toListNameMapE $ hoistNameMap decls destMap) \(n, (LiftE d)) -> do
--             x <- case s ! n of
--               Rename v -> Var <$> toAtomVar v
--               SubstVal a -> return a
--             place d x
--           withSubst s' $ substM ans

-- traverseDeclNestWithDestS
--   :: forall i i' l o. (Emits o, DistinctBetween l i')
--   => DestAssignment i' o -> Subst AtomSubstVal l o -> Nest (Decl SimpIR) l i'
--   -> LowerM i o (Subst AtomSubstVal i' o)
-- traverseDeclNestWithDestS destMap s = \case
--   Empty -> return s
--   Nest (Let b (DeclBinding ann expr)) rest -> do
--     DistinctBetween <- return $ withExtEvidence rest $ shortenBetween @i' b
--     let maybeDest = lookupDest destMap $ sinkBetween $ binderName b
--     expr' <- withSubst s $ lowerExprWithDest maybeDest expr
--     v <- emitDecl (getNameHint b) ann expr'
--     traverseDeclNestWithDestS destMap (s <>> (b @> Rename (atomVarName v))) rest

lowerExprWithDest :: forall i o. Emits o => Maybe (ProjDest o) -> SExpr i -> LowerM i o (SExpr o)
lowerExprWithDest dest expr = undefined
-- lowerExprWithDest dest expr = case expr of
--   TabCon Nothing ty els -> lowerTabCon tabDest ty els
--   PrimOp (Hof (TypedHof (EffTy _ ansTy) (For dir ixDict body))) -> do
--     ansTy' <- substM ansTy
--     lowerFor ansTy' tabDest dir ixDict body
--   PrimOp (Hof (TypedHof (EffTy _ ty) (RunWriter Nothing m body))) -> do
--     PairTy _ ansTy <- visitType ty
--     traverseRWS ansTy body \ref' body' -> do
--       m' <- visitGeneric m
--       return $ RunWriter ref' m' body'
--   PrimOp (Hof (TypedHof (EffTy _ ty) (RunState Nothing s body))) -> do
--     PairTy _ ansTy <- visitType ty
--     traverseRWS ansTy body \ref' body' -> do
--       s' <- visitExpr s
--       return $ RunState ref' s' body'
--   -- this case is important because this pass changes effects
--   PrimOp (Hof (TypedHof _ hof)) -> do
--     hof' <- PrimOp . Hof <$> (visitGeneric hof >>= mkTypedHof)
--     placeGeneric hof'
--   -- Case e alts (EffTy _ ty) -> case dest of
--   --   Nothing -> lowerCase Nothing e alts ty
--   --   Just (FullDest d) -> lowerCase (Just d) e alts ty
--   --   Just d -> do
--   --     ans <- lowerCase Nothing e alts ty >>= emitExpr
--   --     place d ans
--   --     return $ toExpr ans
--   -- _ -> generic
--   where
--     tabDest = dest <&> \case FullDest d -> d; ProjDest _ _ -> error "unexpected projection"

--     generic = visitGeneric expr >>= placeGeneric

--     placeGeneric e = do
--       case dest of
--         Nothing -> return e
--         Just d  -> do
--           ans <- AVar <$> emit e
--           place d ans
--           return $ toExpr ans

--     traverseRWS
--       :: SType o -> LamExpr SimpIR i
--       -> (Maybe (Dest SimpIR o) -> LamExpr SimpIR o -> LowerM i o (Hof SimpIR o))
--       -> LowerM i o (SExpr o)
--     traverseRWS referentTy (LamExpr (BinaryNest hb rb) body) cont = do
--       unpackRWSDest dest >>= \case
--         Nothing -> generic
--         Just (bodyDest, refDest) -> do
--           hof <- cont refDest =<<
--             buildEffLam (getNameHint rb) referentTy \hb' rb' ->
--               extendRenamer (hb@>atomVarName hb' <.> rb@>atomVarName rb') do
--                 case bodyDest of
--                   Nothing -> lowerExpr body
--                   -- Just bd -> lowerExprWithDest (sink bd) body
--           PrimOp . Hof <$> mkTypedHof hof

--     traverseRWS _ _ _ = error "Expected a binary lambda expression"

--     unpackRWSDest = \case
--       Nothing -> return Nothing
--       Just d -> case d of
--         FullDest fd -> do
--           bd <- getProjRef (ProjectProduct 0) fd
--           rd <- getProjRef (ProjectProduct 1) fd
--           return $ Just (Just bd, Just rd)
--         ProjDest (ProjectProduct 0 NE.:| []) pd -> return $ Just (Just pd, Nothing)
--         ProjDest (ProjectProduct 1 NE.:| []) pd -> return $ Just (Nothing, Just pd)
--         ProjDest _ _ -> return Nothing

place :: Emits o => ProjDest o -> SAtom o -> LowerM i o ()
place pd x = case pd of
  FullDest d   -> void $ emitOp $ DAMOp $ Place (toExpr d) (toExpr x)
  ProjDest p d -> undefined
    -- x' <- normalizeNaryProj (NE.toList p) x
    -- void $ emitOp $ DAMOp $ Place d x'

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

isDistinctNest :: Nest SDecl n l -> Maybe (DistinctBetweenEvidence n l)
isDistinctNest nest = case noShadows $ toScopeFrag nest of
  True  -> Just $ fabricateDistinctBetweenEvidence
  False -> Nothing
