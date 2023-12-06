-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module Lower
  ( lowerFullySequential, DestBlock
  ) where

import Prelude hiding ((.))
import Data.Functor
import Data.Maybe (fromJust)
import Control.Category
import Control.Monad.Reader
import Unsafe.Coerce

import Builder
import Core
import Imp
import CheapReduction
import IRVariants
import Name
import Subst
import QueryType
import Types.Core
import Types.Top
import Types.Primitives
import Util (enumerate)

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

type DestBlock = Abs (SBinder) SExpr

lowerFullySequential :: EnvReader m => Bool -> STopLam n -> m n (STopLam n)
lowerFullySequential wantDestStyle (TopLam False piTy (LamExpr bs body)) = liftEnvReaderM do
  lam <- refreshAbs (Abs bs body) \bs' body' ->
    liftAtomSubstBuilder case wantDestStyle of
      True -> do
        xs <- bindersToAtoms bs'
        EffTy _ resultTy <- instantiate (sink piTy) xs
        let resultDestTy = RawRefTy resultTy
        withFreshBinder "ans" resultDestTy \destBinder -> do
          let dest = toAtom $ binderVar destBinder
          LamExpr (bs' >>> UnaryNest destBinder) <$> buildBlock do
            lowerExpr (Just (sink dest)) body' $> UnitVal
      False -> LamExpr bs' <$> buildBlock (lowerExpr Nothing body')
  piTy' <- getLamExprType lam
  return $ TopLam wantDestStyle piTy' lam
lowerFullySequential _ (TopLam True _ _) = error "already in destination style"

data LowerTag
type LowerM = AtomSubstBuilder LowerTag SimpIR

instance NonAtomRenamer (LowerM i o) i o where renameN = substM

instance ExprVisitorEmits (LowerM i o) SimpIR i o where
  visitExprEmits = lowerExpr Nothing

instance Visitor (LowerM i o) SimpIR i o where
  visitAtom = visitAtomDefault
  visitType = visitTypeDefault
  visitPi   = visitPiDefault
  visitLam  = visitLamEmits

type Dest = SAtom
type OptDest n = Maybe (Dest n)

lowerFor
  :: Emits o
  => SType o -> OptDest o -> ForAnn -> IxType SimpIR i -> LamExpr SimpIR i
  -> LowerM i o (SAtom o)
lowerFor ansTy maybeDest dir ixTy (UnaryLamExpr (ib:>ty) body) = do
  ixTy' <- substM ixTy
  ty' <- substM ty
  case isSingletonType ansTy of
    True -> do
      body' <- buildUnaryLamExpr noHint (PairTy ty' UnitTy) \b' -> do
        (i, _) <- fromPair $ toAtom b'
        extendSubst (ib @> SubstVal i) $ lowerExpr Nothing body $> UnitVal
      void $ emitSeq dir ixTy' UnitVal body'
      fromJust <$> singletonTypeVal ansTy
    False -> do
      initDest <- Con . ProdCon . (:[]) <$> case maybeDest of
        Just  d -> return d
        Nothing -> emit $ AllocDest ansTy
      let destTy = getType initDest
      body' <- buildUnaryLamExpr noHint (PairTy ty' destTy) \b' -> do
        (i, destProd) <- fromPair $ toAtom b'
        dest <- proj 0 destProd
        idest <- emit =<< mkIndexRef dest i
        extendSubst (ib @> SubstVal i) $ lowerExpr (Just idest) body $> UnitVal
      ans <- emitSeq dir ixTy' initDest body' >>= proj 0
      emit $ Freeze ans
lowerFor _ _ _ _ _ = error "expected a unary lambda expression"

lowerTabCon :: Emits o => OptDest o -> SType i -> [SAtom i] -> LowerM i o (SAtom o)
lowerTabCon maybeDest tabTy elems = do
  TyCon (TabPi tabTy') <- substM tabTy
  dest <- case maybeDest of
    Just  d -> return d
    Nothing -> emit $ AllocDest $ TyCon $ TabPi tabTy'
  Abs bord ufoBlock <- buildAbs noHint IdxRepTy \ord -> do
    buildBlock $ unsafeFromOrdinal (sink $ tabIxType tabTy') $ toAtom $ sink ord
  -- This is emitting a chain of RememberDest ops to force `dest` to be used
  -- linearly, and to force reads of the `Freeze dest'` result not to be
  -- reordered in front of the writes.
  -- TODO: We technically don't need to sequentialize the writes, since the
  -- slices are all independent of each other.  Do we need a new `JoinDests`
  -- operation to represent that pattern?
  let go incoming_dest [] = return incoming_dest
      go incoming_dest ((ord, e):rest) = do
        i <- dropSubst $ extendSubst (bord@>SubstVal (IdxRepVal (fromIntegral ord))) $
          lowerExpr Nothing ufoBlock
        carried_dest <- buildRememberDest "dest" incoming_dest \local_dest -> do
          idest <- indexRef (toAtom local_dest) (sink i)
          place idest =<< visitAtom e
          return UnitVal
        go carried_dest rest
  dest' <- go dest (enumerate elems)
  emit $ Freeze dest'

lowerCase :: Emits o
  => OptDest o -> SAtom i -> [Alt SimpIR i] -> SType i
  -> LowerM i o (SAtom o)
lowerCase maybeDest scrut alts resultTy = do
  resultTy' <- substM resultTy
  dest <- case maybeDest of
    Just  d -> return d
    Nothing -> emit $ AllocDest resultTy'
  scrut' <- visitAtom scrut
  dest' <- buildRememberDest "case_dest" dest \local_dest -> do
    alts' <- forM alts \(Abs (b:>ty) body) -> do
      ty' <- substM ty
      buildAbs (getNameHint b) ty' \b' ->
        extendSubst (b @> Rename (atomVarName b')) $
          buildBlock do
            lowerExpr (Just (toAtom $ sink $ local_dest)) body $> UnitVal
    void $ mkCase (sink scrut') UnitTy alts' >>= emit
    return UnitVal
  emit $ Freeze dest'

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

type DestAssignment (i'::S) (o::S) = NameMap (AtomNameC SimpIR) (Dest o) i'

lookupDest :: DestAssignment i' o -> SAtomName i' -> OptDest o
lookupDest dests = fmap fromLiftE . flip lookupNameMapE dests

-- Matches up the free variables of the atom, with the given dest. For example, if the
-- atom is a pair of two variables, the dest might be split into per-component dests,
-- and a dest assignment mapping each side to its respective dest will be returned.
-- This function works on a best-effort basis. It's never an error to not split the dest
-- as much as possible, but it can lead to unnecessary copies being done at run-time.
--
-- XXX: When adding more cases, be careful about potentially repeated vars in the output!
decomposeDest :: Emits o => Dest o -> SExpr i' -> LowerM i o (Maybe (DestAssignment i' o))
decomposeDest dest = \case
  Atom (Stuck _ (Var v)) ->
    return $ Just $ singletonNameMapE (atomVarName v) $ LiftE dest
  _ -> return Nothing

traverseDeclNestWithDestS
  :: forall i i' l o. (Emits o, DistinctBetween l i')
  => DestAssignment i' o -> Subst AtomSubstVal l o -> Nest (Decl SimpIR) l i'
  -> LowerM i o (Subst AtomSubstVal i' o)
traverseDeclNestWithDestS destMap s = \case
  Empty -> return s
  Nest (Let b (DeclBinding _ expr)) rest -> do
    DistinctBetween <- return $ withExtEvidence rest $ shortenBetween @i' b
    let maybeDest = lookupDest destMap $ sinkBetween $ binderName b
    result <- withSubst s $ lowerExpr maybeDest expr
    traverseDeclNestWithDestS destMap (s <>> (b @> SubstVal result)) rest

traverseDeclNest :: Emits o => Nest SDecl i i' -> LowerM i'  o a -> LowerM i o a
traverseDeclNest decls cont = case decls of
  Empty -> cont
  Nest (Let b (DeclBinding _ expr)) rest -> do
    x <- lowerExpr Nothing expr
    extendSubst (b@>SubstVal x) $ traverseDeclNest rest cont

lowerExpr :: forall i o. Emits o => OptDest o -> SExpr i -> LowerM i o (SAtom o)
lowerExpr dest expr = case expr of
  Block _ (Abs decls result) -> case dest of
    Nothing -> traverseDeclNest decls $ lowerExpr Nothing result
    Just dest' -> do
      decomposeDest dest' result >>= \case
        Nothing -> do
          traverseDeclNest decls do
            lowerExpr (Just dest') result
        Just destMap -> do
          s <- getSubst
          case isDistinctNest decls of
            Nothing -> error "Non-distinct decls?"
            Just DistinctBetween -> do
              s' <- traverseDeclNestWithDestS destMap s decls
              -- But we have to emit explicit writes, for all the vars that are not defined in decls!
              forM_ (toListNameMapE $ hoistNameMap decls destMap) \(n, (LiftE d)) -> do
                x <- case s ! n of
                  Rename v -> toAtom <$> toAtomVar v
                  SubstVal a -> return a
                place d x
              withSubst s' (substM result) >>= emit
  TabCon Nothing ty els -> lowerTabCon dest ty els
  PrimOp (Hof (TypedHof (EffTy _ ansTy) (For dir ixDict body))) -> do
    ansTy' <- substM ansTy
    lowerFor ansTy' dest dir ixDict body
  PrimOp (Hof (TypedHof (EffTy _ ty) (RunWriter Nothing m body))) -> do
    PairTy _ ansTy <- visitType ty
    traverseRWS ansTy body \ref' body' -> do
      m' <- visitGeneric m
      emitHof $ RunWriter ref' m' body'
  PrimOp (Hof (TypedHof (EffTy _ ty) (RunState Nothing s body))) -> do
    PairTy _ ansTy <- visitType ty
    traverseRWS ansTy body \ref' body' -> do
      s' <- visitAtom s
      emitHof $ RunState ref' s' body'
  -- this case is important because this pass changes effects
  PrimOp (Hof (TypedHof _ hof)) -> do
    hof' <- emit =<< (visitGeneric hof >>= mkTypedHof)
    placeGeneric hof'
  Case e alts (EffTy _ ty) -> lowerCase dest e alts ty
  _ -> generic
  where
    generic :: LowerM i o (SAtom o)
    generic = visitGeneric expr >>= emit >>= placeGeneric

    placeGeneric :: SAtom o -> LowerM i o (SAtom o)
    placeGeneric e = do
      case dest of
        Nothing -> return e
        Just d  -> do
          place d e
          return e

    traverseRWS
      :: SType o -> LamExpr SimpIR i
      -> (OptDest o -> LamExpr SimpIR o -> LowerM i o (SAtom o))
      -> LowerM i o (SAtom o)
    traverseRWS referentTy (LamExpr (BinaryNest hb rb) body) cont = do
      unpackRWSDest dest >>= \case
        Nothing -> generic
        Just (bodyDest, refDest) -> do
          cont refDest =<<
            buildEffLam (getNameHint rb) referentTy \hb' rb' ->
              extendRenamer (hb@>atomVarName hb' <.> rb@>atomVarName rb') do
                lowerExpr (sink <$> bodyDest) body
    traverseRWS _ _ _ = error "Expected a binary lambda expression"

    unpackRWSDest = \case
      Nothing -> return Nothing
      Just d -> do
        bd <- getProjRef (ProjectProduct 0) d
        rd <- getProjRef (ProjectProduct 1) d
        return $ Just (Just bd, Just rd)

place :: Emits o => Dest o -> SAtom o -> LowerM i o ()
place d x = void $ emit $ Place d x

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
