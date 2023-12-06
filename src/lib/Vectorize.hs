-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Vectorize (vectorizeLoops) where

import Prelude hiding ((.))
import Data.Word
import Data.Functor
import Data.Text.Prettyprint.Doc (viaShow)
import Control.Category
import Control.Monad.Reader
import Control.Monad.State.Strict

import Builder
import Core
import Err
import CheapReduction
import IRVariants
import Lower (DestBlock)
import MTL1
import Name
import Subst
import PPrint
import QueryType
import Types.Core
import Types.Top
import Types.OpNames qualified as P
import Types.Primitives
import Util (allM, zipWithZ)

-- === Vectorization ===

-- WATCH OUT! This vectorization assumes that all raw references represent
-- destinations, and so no Place operations can cause write conflicts.

-- Vectorization occurs as two main passes, which slightly ambiguous names
-- - `vectorizeLoops`, in the `TopVectorizeM` monad, traverses the entire program
--   looking for loops to vectorize
-- - `vectorize`, in the `VectorizeM` monad, actually vectorizes a single loop
--
-- The inner `vectorize` pass may fail with `throwVectErr`.  The outer
-- `vectorizeLoops` pass takes an error like that to mean that vectorization of
-- this loop is not possible (rather than that there is an error in the user
-- program), and falls back to leaving the scalar loop in place.


-- TODO: Local vector values? We might want to pack short and pure for loops into vectors,
-- to support things like float3 etc.
data Stability
  -- Constant across vectorized dimension, represented as a scalar
  = Uniform
  -- Varying across vectorized dimension, represented as a vector
  | Varying
  -- Varying, but contiguous across vectorized dimension; represented as a
  -- scalar carrying the first value
  | Contiguous
  | ProdStability [Stability]
  deriving (Eq, Show)

data VSubstValC (c::C) (n::S) where
  VVal    :: Stability -> SAtom n -> VSubstValC (AtomNameC SimpIR) n
  VRename :: Name c n -> VSubstValC c n

type VAtom = VSubstValC (AtomNameC SimpIR)
instance SinkableV VSubstValC
instance SinkableE (VSubstValC c) where
  sinkingProofE fresh (VVal s x) = VVal s $ sinkingProofE fresh x
  sinkingProofE fresh (VRename n) = VRename $ sinkingProofE fresh n

instance Pretty (VSubstValC c n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (VSubstValC c n) where
  prettyPrec (VVal s atom) = atPrec LowestPrec $ "@" <> viaShow s <+> pretty atom
  prettyPrec (VRename v) = atPrec LowestPrec $ "Rename" <+> pretty v

data MonoidCommutes =
    Commutes
  | DoesNotCommute

type CommuteMap = NameMap (AtomNameC SimpIR) MonoidCommutes

newtype TopVectorizeM (i::S) (o::S) (a:: *) = TopVectorizeM
  { runTopVectorizeM ::
      SubstReaderT Name
        (ReaderT1 CommuteMap
          (ReaderT1 (LiftE Word32)
            (StateT1 (LiftE [Err]) (BuilderT SimpIR Except)))) i o a }
  deriving ( Functor, Applicative, Monad, MonadFail, MonadReader (CommuteMap o)
           , MonadState (LiftE [Err] o), Fallible, ScopeReader, EnvReader
           , EnvExtender, Builder SimpIR, ScopableBuilder SimpIR, Catchable
           , SubstReader Name)

vectorizeLoops :: EnvReader m => Word32 -> STopLam n -> m n (STopLam n, [Err])
vectorizeLoops width (TopLam d ty (LamExpr bsDestB body)) = liftEnvReaderM do
  case popNest bsDestB of
    Just (PairB bs b) ->
      refreshAbs (Abs bs (Abs b body)) \bs' body' -> do
        (Abs b'' body'', errs) <- liftTopVectorizeM width $ vectorizeLoopsDestBlock body'
        return $ (TopLam d ty (LamExpr (bs' >>> UnaryNest b'') body''), errs)
    Nothing -> error "expected a trailing dest binder"
{-# SCC vectorizeLoops #-}

liftTopVectorizeM :: (EnvReader m)
  => Word32 -> TopVectorizeM i i a -> m i (a, [Err])
liftTopVectorizeM vectorByteWidth action = do
  fallible <- liftBuilderT $
    flip runStateT1 mempty $ runReaderT1 (LiftE vectorByteWidth) $
      runReaderT1 mempty $ runSubstReaderT idSubst $
        runTopVectorizeM action
  case fallible of
    -- The failure case should not occur: vectorization errors should have been
    -- caught inside `vectorizeLoopsDecls` (and should have been added to the
    -- `Err` state of the `StateT` instance that is run with `runStateT` above).
    Failure errs -> error $ pprint errs
    Success (a, (LiftE errs)) -> return $ (a, errs)

throwVectErr :: Fallible m => String -> m a
throwVectErr msg = throwInternal msg

askVectorByteWidth :: TopVectorizeM i o Word32
askVectorByteWidth = TopVectorizeM $ liftSubstReaderT $ lift11 (fromLiftE <$> ask)

extendCommuteMap :: AtomName SimpIR o -> MonoidCommutes -> TopVectorizeM i o a -> TopVectorizeM i o a
extendCommuteMap name commutativity = local $ insertNameMapE name $ LiftE commutativity

vectorizeLoopsDestBlock :: DestBlock i
  -> TopVectorizeM i o (DestBlock o)
vectorizeLoopsDestBlock (Abs (destb:>destTy) body) = do
  destTy' <- renameM destTy
  withFreshBinder (getNameHint destb) destTy' \destb' -> do
    extendRenamer (destb @> binderName destb') do
      Abs destb' <$> buildBlock (vectorizeLoopsExpr body)

vectorizeLoopsDecls :: (Emits o)
  => Nest SDecl i i' -> TopVectorizeM i' o a -> TopVectorizeM i o a
vectorizeLoopsDecls nest cont =
  case nest of
    Empty -> cont
    Nest (Let b (DeclBinding _ expr)) rest -> do
      v <- emitToVar =<< vectorizeLoopsExpr expr
      extendSubst (b @> atomVarName v) $
        vectorizeLoopsDecls rest cont

vectorizeLoopsLamExpr :: LamExpr SimpIR i -> TopVectorizeM i o (LamExpr SimpIR o)
vectorizeLoopsLamExpr (LamExpr bs body) = case bs of
  Empty -> LamExpr Empty <$> buildBlock (vectorizeLoopsExpr body)
  Nest (b:>ty) rest -> do
    ty' <- renameM ty
    withFreshBinder (getNameHint b) ty' \b' -> do
      extendRenamer (b @> binderName b') do
        LamExpr bs' body' <- vectorizeLoopsLamExpr $ LamExpr rest body
        return $ LamExpr (Nest b' bs') body'

vectorizeLoopsExpr :: (Emits o) => SExpr i -> TopVectorizeM i o (SAtom o)
vectorizeLoopsExpr expr = do
  vectorByteWidth <- askVectorByteWidth
  narrowestTypeByteWidth <- getNarrowestTypeByteWidth =<< renameM expr
  let loopWidth = vectorByteWidth `div` narrowestTypeByteWidth
  case expr of
    Block _ (Abs decls body) -> vectorizeLoopsDecls decls $ vectorizeLoopsExpr body
    PrimOp (DAMOp (Seq effs dir ixty dest body)) -> do
      sz <- simplifyIxSize =<< renameM ixty
      case sz of
        Just n | n `mod` loopWidth == 0 -> (do
            safe <- vectorSafeEffect effs
            if safe
              then (do
                Distinct <- getDistinct
                let vn = n `div` loopWidth
                body' <- vectorizeSeq loopWidth ixty body
                dest' <- renameM dest
                emit =<< mkSeq dir (IxType IdxRepTy (DictCon (IxRawFin (IdxRepVal vn)))) dest' body')
              else renameM expr >>= emit)
          `catchErr` \err -> do
              modify (\(LiftE errs) -> LiftE (err:errs))
              recurSeq expr
        _ -> recurSeq expr
    PrimOp (Hof (TypedHof _ (RunReader item (BinaryLamExpr hb' refb' body)))) -> do
      item' <- renameM item
      itemTy <- return $ getType item'
      lam <- buildEffLam noHint itemTy \hb refb ->
        extendRenamer (hb' @> atomVarName hb) do
          extendRenamer (refb' @> atomVarName refb) do
            vectorizeLoopsExpr body
      emit =<< mkTypedHof (RunReader item' lam)
    PrimOp (Hof (TypedHof (EffTy _ ty)
                 (RunWriter (Just dest) monoid (BinaryLamExpr hb' refb' body)))) -> do
      dest' <- renameM dest
      monoid' <- renameM monoid
      commutativity <- monoidCommutativity monoid'
      PairTy _ accTy <- renameM ty
      lam <- buildEffLam noHint accTy \hb refb ->
        extendRenamer (hb' @> atomVarName hb) do
          extendRenamer (refb' @> atomVarName refb) do
            extendCommuteMap (atomVarName hb) commutativity do
              vectorizeLoopsExpr body
      emit =<< mkTypedHof (RunWriter (Just dest') monoid' lam)
    _ -> renameM expr >>= emit
  where
    recurSeq :: (Emits o) => SExpr i -> TopVectorizeM i o (SAtom o)
    recurSeq (PrimOp (DAMOp (Seq effs dir ixty dest body))) = do
      effs' <- renameM effs
      ixty' <- renameM ixty
      dest' <- renameM dest
      body' <- vectorizeLoopsLamExpr body
      emit $ Seq effs' dir ixty' dest' body'
    recurSeq _ = error "Impossible"

simplifyIxSize :: (EnvReader m, ScopableBuilder SimpIR m)
  => IxType SimpIR n -> m n (Maybe Word32)
simplifyIxSize ixty = do
  sizeMethod <- buildBlock $ applyIxMethod (sink $ ixTypeDict ixty) Size []
  reduceExpr sizeMethod >>= \case
    Just (IdxRepVal n) -> return $ Just n
    _ -> return Nothing
{-# INLINE simplifyIxSize #-}

-- Really we should check this by seeing whether there is an instance for a
-- `Commutative` class, or something like that, but for now just pattern-match
-- to detect scalar addition as the only monoid we recognize as commutative.
-- Potentially relevant ideas:
-- - Store commutativity or lack of it as a bit on the BaseMonoid object (but
--   get the bit from where?)
-- - Paramterize runWriter by a user-specified flag saying whether the monoid is
--   to be commutative; record that on the RunWriter Hof, and enforce it by
--   type-checking.
-- - Is there a way to automate checking for commutativity via the typeclass
--   system so the user doesn't have to keep writing "commutative" all the time?
-- - Or maybe make commutativity the default, and require an explicit annotation
--   to opt out?  (Which mention in the type error)
-- - Alternately, is there a way to parameterize the BaseMonoid class by a
--   Commutativity bit, such that commutative instances implement the class
--   parametrically in that bit, while not-known-to-be-commutative ones only
--   implement the non-commutative version?
--   - Will that bit be visible enough to the compiler to be picked up here?
monoidCommutativity :: (EnvReader m) => BaseMonoid SimpIR n -> m n MonoidCommutes
monoidCommutativity monoid = case isAdditionMonoid monoid of
  Just () -> return Commutes
  Nothing -> return DoesNotCommute
{-# INLINE monoidCommutativity #-}

isAdditionMonoid :: BaseMonoid SimpIR n -> Maybe ()
isAdditionMonoid monoid = do
  BaseMonoid { baseEmpty = (Con (Lit l))
             , baseCombine = BinaryLamExpr (b1:>_) (b2:>_) body } <- Just monoid
  unless (_isZeroLit l) Nothing
  PrimOp (BinOp op (Stuck _ (Var b1')) (Stuck _ (Var b2'))) <- return body
  unless (op `elem` [P.IAdd, P.FAdd]) Nothing
  case (binderName b1, atomVarName b1', binderName b2, atomVarName b2') of
    -- Checking the raw names here because (i) I don't know how to convince the
    -- name system to let me check the well-typed names (which is because b2
    -- might shadow b1), and (ii) there are so few patterns that I can just
    -- enumerate them.
    (UnsafeMakeName n1, UnsafeMakeName n1', UnsafeMakeName n2, UnsafeMakeName n2') -> do
      when (n1 == n2) Nothing
      unless ((n1 == n1' && n2 == n2') || (n1 == n2' && n2 == n1')) Nothing
      Just ()

_isZeroLit :: LitVal -> Bool
_isZeroLit = \case
  Int64Lit 0 -> True
  Int32Lit 0 -> True
  Word8Lit 0 -> True
  Word32Lit 0 -> True
  Word64Lit 0 -> True
  Float32Lit 0.0 -> True
  Float64Lit 0.0 -> True
  _ -> False

-- Vectorizing a loop with an effect is safe when the operation reordering
-- produced by vectorization doesn't change the semantics.  This is guaranteed
-- to happen when:
-- - It's the Init effect (because the writes are non-aliasing), or
-- - It's the Reader effect, or
-- - Every reference in the effect is accessed in non-aliasing
--   fashion across iterations (e.g., for i. ... ref!i ...), or
-- - It's a Writer effect with a commutative monoid, or
-- - It's a Writer effect and the body writes to each set of
--   potentially overlapping references in scope at most once
--   (and the vector operations have in-order reductions
--   available)
-- - The Exception effect should have been transformed away by now
-- - The IO effect is in general not safe
-- This check doesn't have enough information to test the above,
-- but we crudely approximate for now.
vectorSafeEffect :: EffectRow SimpIR i -> TopVectorizeM i o Bool
vectorSafeEffect (EffectRow effs NoTail) = allM safe $ eSetToList effs where
  safe :: Effect SimpIR i -> TopVectorizeM i o Bool
  safe InitEffect = return True
  safe (RWSEffect Reader _) = return True
  safe (RWSEffect Writer (Stuck _ (Var h))) = do
    h' <- renameM $ atomVarName h
    commuteMap <- ask
    case lookupNameMapE h' commuteMap of
      Just (LiftE Commutes) -> return True
      Just (LiftE DoesNotCommute) -> return False
      Nothing -> error $ "Handle " ++ pprint h ++ " not present in commute map?"
  safe _ = return False

vectorizeSeq :: Word32 -> IxType SimpIR i -> LamExpr SimpIR i
  -> TopVectorizeM i o (LamExpr SimpIR o)
vectorizeSeq loopWidth ixty (UnaryLamExpr (b:>ty) body) = do
  newLoopTy <- case ty of
    TyCon (ProdType [_ixType, ref]) -> do
      ref' <- renameM ref
      return $ TyCon $ ProdType [IdxRepTy, ref']
    _ -> error "Unexpected seq binder type"
  ixty' <- renameM ixty
  liftVectorizeM loopWidth $
    buildUnaryLamExpr (getNameHint b) newLoopTy \ci -> do
      -- The per-tile loop iterates on `Fin`
      (viOrd, dest) <- fromPair $ toAtom ci
      iOrd <- imul viOrd $ IdxRepVal loopWidth
      -- TODO: It would be nice to cancel this UnsafeFromOrdinal with the
      -- Ordinal that will be taken later when indexing, but that should
      -- probably be a separate pass.
      i <- applyIxMethod (sink $ ixTypeDict ixty') UnsafeFromOrdinal [iOrd]
      extendSubst (b @> VVal (ProdStability [Contiguous, ProdStability [Uniform]]) (PairVal i dest)) $
        vectorizeExpr body $> UnitVal
vectorizeSeq _ _ _ = error "expected a unary lambda expression"

newtype VectorizeM i o a =
  VectorizeM { runVectorizeM ::
    SubstReaderT VSubstValC (BuilderT SimpIR (ReaderT Word32 Except)) i o a }
  deriving ( Functor, Applicative, Monad, Fallible, MonadFail
           , SubstReader VSubstValC , Builder SimpIR, EnvReader, EnvExtender
           , ScopeReader, ScopableBuilder SimpIR)

liftVectorizeM :: (SubstReader Name m, EnvReader (m i), Fallible (m i o))
  => Word32 -> VectorizeM i o a -> m i o a
liftVectorizeM loopWidth action = do
  subst <- getSubst
  act <- liftBuilderT $ runSubstReaderT (newSubst $ vSubst subst) $ runVectorizeM action
  case flip runReaderT loopWidth act of
    Success a -> return a
    Failure errs -> throwErr errs  -- re-raise inside ambient monad
  where
    vSubst subst val = VRename $ subst ! val

getLoopWidth :: VectorizeM i o Word32
getLoopWidth = VectorizeM $ SubstReaderT $ const $ ask

-- TODO When needed, can code a variant of this that also returns the Stability
-- of the value returned by the LamExpr.
vectorizeLamExpr :: LamExpr SimpIR i -> [Stability]
  -> VectorizeM i o (LamExpr SimpIR o)
vectorizeLamExpr (LamExpr bs body) argStabilities = case (bs, argStabilities) of
  (Empty, []) -> do
    LamExpr Empty <$> buildBlock (do
      vectorizeExpr body >>= \case
        (VVal _ ans) -> return ans
        (VRename v) -> toAtom <$> toAtomVar v)
  (Nest (b:>ty) rest, (stab:stabs)) -> do
    ty' <- vectorizeType ty
    ty'' <- promoteTypeByStability ty' stab
    withFreshBinder (getNameHint b) ty'' \b' -> do
      var <- toAtomVar $ binderName b'
      extendSubst (b @> VVal stab (toAtom var)) do
        LamExpr rest' body' <- vectorizeLamExpr (LamExpr rest body) stabs
        return $ LamExpr (Nest b' rest') body'
  _ -> error "Zip error"

vectorizeExpr :: Emits o => SExpr i -> VectorizeM i o (VAtom o)
vectorizeExpr expr = do
  case expr of
    Block _ block -> vectorizeBlock block
    TabApp _ tbl ix -> do
      VVal Uniform tbl' <- vectorizeAtom tbl
      VVal Contiguous ix' <- vectorizeAtom ix
      case getType tbl' of
        TabTy _ tb a -> do
          vty <- getVectorType =<< case hoist tb a of
            HoistSuccess a' -> return a'
            HoistFailure _  -> throwVectErr "Can't vectorize dependent table application"
          VVal Varying <$> emit (VectorIdx tbl' ix' vty)
        tblTy -> do
          throwVectErr $ "bad type: " ++ pprint tblTy ++ "\ntbl' : " ++ pprint tbl'
    Atom atom -> vectorizeAtom atom
    PrimOp op -> vectorizePrimOp op
    _ -> throwVectErr $ "Cannot vectorize expr: " ++ pprint expr

vectorizeBlock :: Emits o => SBlock i -> VectorizeM i o (VAtom o)
vectorizeBlock (Abs Empty body) = vectorizeExpr body
vectorizeBlock (Abs (Nest (Let b (DeclBinding _ rhs)) rest) body) = do
  v <- vectorizeExpr rhs
  extendSubst (b @> v) $ vectorizeBlock (Abs rest body)

vectorizeDAMOp :: Emits o => DAMOp SimpIR i -> VectorizeM i o (VAtom o)
vectorizeDAMOp op =
  case op of
    Place ref' val' -> do
      VVal vref ref <- vectorizeAtom ref'
      sval@(VVal vval val) <- vectorizeAtom val'
      VVal Uniform <$> case (vref, vval) of
        (Uniform   , Uniform   ) -> emit $ Place ref val
        (Uniform   , _         ) -> throwVectErr "Write conflict? This should never happen!"
        (Varying   , _         ) -> throwVectErr "Vector scatter not implemented"
        (Contiguous, Varying   ) -> emit $ Place ref val
        (Contiguous, Contiguous) -> emit . Place ref =<< ensureVarying sval
        _ -> throwVectErr "Not implemented yet"
    _ -> throwVectErr $ "Can't vectorize op: " ++ pprint op

vectorizeRefOp :: Emits o => SAtom i -> RefOp SimpIR i -> VectorizeM i o (VAtom o)
vectorizeRefOp ref' op =
  case op of
    MAsk -> do
      -- TODO A contiguous reference becomes a vector load producing a varying
      -- result.
      VVal Uniform ref <- vectorizeAtom ref'
      VVal Uniform <$> emit (RefOp ref MAsk)
    MExtend basemonoid' x' -> do
      VVal refStab ref <- vectorizeAtom ref'
      VVal xStab x <- vectorizeAtom x'
      basemonoid <- case refStab of
        Uniform -> case xStab of
          Uniform -> do
            vectorizeBaseMonoid basemonoid' Uniform Uniform
          -- This case represents accumulating something loop-varying into a
          -- loop-invariant accumulator, as e.g. sum.  We can implement that for
          -- commutative monoids, but we would want to have started with private
          -- accumulators (one per lane), and then reduce them with an
          -- appropriate sequence of vector reduction intrinsics at the end.
          _ -> throwVectErr $ "Vectorizing non-sliced accumulation not implemented"
        Contiguous -> do
          vectorizeBaseMonoid basemonoid' Varying xStab
        s -> throwVectErr $ "Cannot vectorize reference with loop-varying stability " ++ show s
      VVal Uniform <$> emit (RefOp ref $ MExtend basemonoid x)
    IndexRef _ i' -> do
      VVal Uniform ref <- vectorizeAtom ref'
      VVal Contiguous i <- vectorizeAtom i'
      case getType ref of
        TyCon (RefType _ (TabTy _ tb a)) -> do
          vty <- getVectorType =<< case hoist tb a of
            HoistSuccess a' -> return a'
            HoistFailure _  -> throwVectErr "Can't vectorize dependent table application"
          VVal Contiguous <$> emit (VectorSubref ref i vty)
        refTy -> do
          throwVectErr do
            "bad type: " ++ pprint refTy ++ "\nref' : " ++ pprint ref'
    _ -> throwVectErr $ "Can't vectorize op: " ++ pprint (RefOp ref' op)

vectorizeBaseMonoid :: Emits o => BaseMonoid SimpIR i -> Stability -> Stability
  -> VectorizeM i o (BaseMonoid SimpIR o)
vectorizeBaseMonoid (BaseMonoid empty combine) accStab xStab = do
  -- TODO: This will probably create lots of vector broadcast of 0 instructions,
  -- which will often be dead code because only the combine operation is
  -- actually needed in that place.  We can (i) rely on LLVM to get rid of them,
  -- (ii) get rid of them ourselves by running DCE on Imp (which is problematic
  -- because we don't have the effect system at that point), or (iii) change the
  -- IR to not require the empty element for MExtend operations, since they
  -- don't use it.
  empty' <- ensureVarying =<< vectorizeAtom empty
  combine' <- vectorizeLamExpr combine [accStab, xStab]
  return $ BaseMonoid empty' combine'

vectorizePrimOp :: Emits o => PrimOp SimpIR i -> VectorizeM i o (VAtom o)
vectorizePrimOp op = case op of
  UnOp opk arg -> do
    sx@(VVal vx x) <- vectorizeAtom arg
    let v = case vx of Uniform -> Uniform; _ -> Varying
    x' <- if vx /= v then ensureVarying sx else return x
    VVal v <$> emit (UnOp opk x')
  BinOp opk arg1 arg2 -> do
    sx@(VVal vx x) <- vectorizeAtom arg1
    sy@(VVal vy y) <- vectorizeAtom arg2
    let v = case (opk, vx, vy) of
              (_, Uniform, Uniform) -> Uniform
              (IAdd, Uniform, Contiguous) -> Contiguous
              (IAdd, Contiguous, Uniform) -> Contiguous
              _ -> Varying
    x' <- if v == Varying then ensureVarying sx else return x
    y' <- if v == Varying then ensureVarying sy else return y
    VVal v <$> emit (BinOp opk x' y')
  MiscOp (CastOp tyArg arg) -> do
    ty <- vectorizeType tyArg
    VVal vx x <- vectorizeAtom arg
    ty' <- case vx of
      Uniform    -> return ty
      Varying    -> getVectorType ty
      Contiguous -> return ty
      ProdStability _ -> throwVectErr "Unexpected cast of product type"
    VVal vx <$> emit (CastOp ty' x)
  DAMOp op' -> vectorizeDAMOp op'
  RefOp ref op' -> vectorizeRefOp ref op'
  MemOp (PtrOffset arg1 arg2) -> do
    VVal Uniform ptr    <- vectorizeAtom arg1
    VVal Contiguous off <- vectorizeAtom arg2
    VVal Contiguous <$> emit (PtrOffset ptr off)
  MemOp (PtrLoad arg) -> do
    VVal Contiguous ptr <- vectorizeAtom arg
    BaseTy (PtrType (addrSpace, a)) <- return $ getType ptr
    BaseTy av <- getVectorType $ BaseTy a
    ptr' <- emit $ CastOp (BaseTy $ PtrType (addrSpace, av)) ptr
    VVal Varying <$> emit (PtrLoad ptr')
  -- Vectorizing IO might not always be safe! Here, we depend on vectorizeOp
  -- being picky about the IO-inducing ops it supports, and expect it to
  -- complain about FFI calls and the like.
  Hof (TypedHof _ (RunIO body)) -> do
  -- TODO: buildBlockAux?
    Abs decls (LiftE vy `PairE` y) <- buildScoped do
      VVal vy y <- vectorizeExpr body
      return $ PairE (LiftE vy) y
    block <- mkBlock (Abs decls y)
    VVal vy <$> emitHof (RunIO block)
  _ -> throwVectErr $ "Can't vectorize op: " ++ pprint op

vectorizeType :: SType i -> VectorizeM i o (SType o)
vectorizeType t = do
  subst <- getSubst
  fmapNamesM (uniformSubst subst) t

vectorizeAtom :: SAtom i -> VectorizeM i o (VAtom o)
vectorizeAtom atom = do
  case atom of
    Stuck _ e -> vectorizeStuck e
    Con con -> case con of
      Lit l -> return $ VVal Uniform $ Con $ Lit l
      _ -> do
        subst <- getSubst
        VVal Uniform <$> fmapNamesM (uniformSubst subst) atom

vectorizeStuck :: SStuck i -> VectorizeM i o (VAtom o)
vectorizeStuck = \case
  Var v -> lookupSubstM (atomVarName v) >>= \case
    VRename v' -> VVal Uniform . toAtom <$> toAtomVar v'
    v' -> return v'
  StuckProject i x -> do
    VVal vv x' <- vectorizeStuck x
    ov <- case vv of
      ProdStability sbs -> return $ sbs !! i
      _ -> throwVectErr "Invalid projection"
    x'' <- reduceProj i x'
    return $ VVal ov x''
  -- TODO: think about this case
  StuckTabApp _ _ -> throwVectErr $ "Cannot vectorize atom"
  PtrVar _ _      -> throwVectErr $ "Cannot vectorize atom"
  RepValAtom _    -> throwVectErr $ "Cannot vectorize atom"

uniformSubst :: Color c => Subst VSubstValC i o -> Name c i -> AtomSubstVal c o
uniformSubst subst n = case subst ! n of
  VVal Uniform x -> SubstVal x
  VRename name -> Rename name
  -- TODO(nrink): Throw instead of `error`.
  _ -> error "Can't vectorize atom"

getVectorType :: SType o -> VectorizeM i o (SType o)
getVectorType ty = case ty of
  BaseTy (Scalar sbt) -> do
    els <- getLoopWidth
    return $ BaseTy $ Vector [els] sbt
  -- TODO: Should we support tables?
  _ -> throwVectErr $ "Can't make a vector of " ++ pprint ty

ensureVarying :: Emits o => VAtom o -> VectorizeM i o (SAtom o)
ensureVarying (VVal s val) = case s of
  Varying -> return val
  Uniform -> do
    vty <- getVectorType $ getType val
    emit $ VectorBroadcast val vty
  -- Note that the implementation of this case will depend on val's type.
  Contiguous -> do
    let ty = getType val
    vty <- getVectorType ty
    case ty of
      BaseTy (Scalar sbt) -> do
        bval <- emit $ VectorBroadcast val vty
        iota <- emit $ VectorIota vty
        emit $ BinOp (if isIntegral sbt then IAdd else FAdd) bval iota
      _ -> throwVectErr "Not implemented"
  ProdStability _ -> throwVectErr "Not implemented"
ensureVarying (VRename v) = do
  x <- toAtom <$> toAtomVar v
  ensureVarying (VVal Uniform x)

promoteTypeByStability :: SType o -> Stability -> VectorizeM i o (SType o)
promoteTypeByStability ty = \case
  Uniform -> return ty
  Contiguous -> return ty
  Varying -> getVectorType ty
  ProdStability stabs -> case ty of
    TyCon (ProdType elts) -> TyCon <$> ProdType <$> zipWithZ promoteTypeByStability elts stabs
    _ -> throwInternal "Zip error"

-- === computing byte widths ===

newtype CalcWidthM i o a = CalcWidthM {
  runTypeWidthM :: SubstReaderT Name (StateT1 (LiftE Word32) EnvReaderM) i o a}
  deriving (Functor, Applicative, Monad, SubstReader Name, EnvExtender,
            ScopeReader, EnvReader, MonadState (LiftE Word32 o))

instance NonAtomRenamer (CalcWidthM i o) i o where renameN = renameM
instance Visitor (CalcWidthM i o) SimpIR i o where
  visitAtom = visitAtomDefault
  visitType = visitTypeDefault
  visitPi   = visitPiDefault
  visitLam  = visitLamNoEmits

instance ExprVisitorNoEmits (CalcWidthM i o) SimpIR i o where
  visitExprNoEmits expr = case expr of
    PrimOp (Hof     _) -> fallback
    PrimOp (DAMOp _  ) -> fallback
    PrimOp (RefOp _ _) -> fallback
    PrimOp _ -> do
      expr' <- renameM expr
      let ty = getType expr'
      modify (\(LiftE x) -> LiftE $ min (typeByteWidth ty) x)
      return expr'
    Block _ (Abs decls result) -> mkBlock =<< visitDeclsNoEmits decls \decls' -> do
      Abs decls' <$> visitExprNoEmits result
    _ -> fallback
    where fallback = visitGeneric expr

typeByteWidth :: SType n -> Word32
typeByteWidth ty = case ty of
 BaseTy bt -> case bt of
  -- Currently only support vectorization of scalar types (cf. `getVectorType` above):
  Scalar _ -> fromInteger . toInteger $ sizeOf bt
  _ -> maxWord32
 _ -> maxWord32

maxWord32 :: Word32
maxWord32 = maxBound

getNarrowestTypeByteWidth :: (EnvReader m) => Expr SimpIR n -> m n Word32
getNarrowestTypeByteWidth x = do
  (_, LiftE result) <-  liftEnvReaderM $ runStateT1
    (runSubstReaderT idSubst $ runTypeWidthM $ visitExprNoEmits x) (LiftE maxWord32)
  if result == maxWord32
    then return 1
    else return result
