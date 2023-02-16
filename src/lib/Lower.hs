-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module Lower
  ( lowerFullySequential, vectorizeLoops
  ) where

import Prelude hiding (abs, id, (.))
import Data.Word
import Data.Functor
import Data.Maybe (fromJust)
import Data.List.NonEmpty qualified as NE
import Data.Text.Prettyprint.Doc (pretty, viaShow, (<+>))
import Control.Category
import Control.Monad.Reader
import Control.Monad.State.Strict
import Unsafe.Coerce
import GHC.Exts (inline)

import Builder
import Core
import Err
import GenericTraversal
import CheapReduction
import IRVariants
import MTL1
import Name
import Subst
import PPrint
import QueryType
import Types.Core
import Types.Primitives
import Util (foldMapM, enumerate)

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

lowerFullySequential :: EnvReader m => SLam n -> m n (DestLamExpr SimpIR n)
lowerFullySequential (LamExpr bs body) = liftEnvReaderM $ do
  refreshAbs (Abs bs body) \bs' body' -> do
    body'' <- lowerFullySequentialBlock body'
    return $ DestLamExpr bs' body''

lowerFullySequentialBlock :: EnvReader m => SBlock n -> m n (DestBlock SimpIR n)
lowerFullySequentialBlock b = liftM fst $ liftGenericTraverserM LFS do
  resultDestTy <- RawRefTy <$> getTypeSubst b
  withFreshBinder (getNameHint @String "ans") resultDestTy \destBinder -> do
    DestBlock destBinder <$> buildBlock do
      let dest = Var $ sink $ binderName destBinder
      traverseBlockWithDest dest b $> UnitVal
{-# SCC lowerFullySequentialBlock #-}

data LFS (n::S) = LFS
type LowerM = GenericTraverserM SimpIR UnitB LFS
instance SinkableE LFS where
  sinkingProofE _ LFS = LFS
instance HoistableState LFS where
  hoistState _ _ LFS = LFS
  {-# INLINE hoistState #-}

-- It would be nice to figure out a way to not have to update the effect
-- annotations manually... The only interesting cases below are really For and TabCon.
instance GenericTraverser SimpIR UnitB LFS where
  traverseExpr expr = case expr of
    -- TODO: re-enable after fixing traverseTabCon bug
    -- TabCon ty els -> traverseTabCon Nothing ty els
    Hof (For dir ixDict body) -> traverseFor Nothing dir ixDict body
    Case _ _ _ _ -> do
      Case e alts ty _ <- traverseExprDefault expr
      eff' <- foldMapM getEffects alts
      return $ Case e alts ty eff'
    _ -> traverseExprDefault expr
  traverseAtom atom = traverseAtomDefault atom

type Dest = Atom

traverseFor
  :: Emits o => Maybe (Dest SimpIR o) -> ForAnn -> IxDict SimpIR i -> LamExpr SimpIR i
  -> LowerM i o (SExpr o)
traverseFor maybeDest dir ixDict lam@(UnaryLamExpr (ib:>ty) body) = do
  ansTy <- getTypeSubst $ Hof $ For dir ixDict $ lam
  ixDict' <- substM ixDict
  ty' <- substM ty
  case isSingletonType ansTy of
    True -> do
      body' <- buildUnaryLamExpr noHint (PairTy ty' UnitTy) \b' -> do
        (i, _) <- fromPair $ Var b'
        extendSubst (ib @> SubstVal i) $ traverseBlock body $> UnitVal
      void $ emit $ DAMOp $ Seq dir ixDict' UnitVal body'
      Atom . fromJust <$> singletonTypeVal ansTy
    False -> do
      initDest <- ProdVal . (:[]) <$> case maybeDest of
        Just  d -> return d
        Nothing -> emitExpr $ DAMOp $ AllocDest ansTy
      destTy <- getType initDest
      body' <- buildUnaryLamExpr noHint (PairTy ty' destTy) \b' -> do
        (i, destProd) <- fromPair $ Var b'
        dest <- normalizeProj (ProjectProduct 0) destProd
        idest <- emitExpr $ RefOp dest $ IndexRef i
        extendSubst (ib @> SubstVal i) $ traverseBlockWithDest idest body $> UnitVal
      let seqHof = DAMOp $ Seq dir ixDict' initDest body'
      DAMOp . Freeze . ProjectElt (ProjectProduct 0) <$> (Var <$> emit seqHof)
traverseFor _ _ _ _ = error "expected a unary lambda expression"

-- This is buggy. Slicing `indexRef` violates the linearity constraints on dest.
_traverseTabCon :: Emits o => Maybe (Dest SimpIR o) -> SType i -> [SAtom i] -> LowerM i o (SExpr o)
_traverseTabCon maybeDest tabTy elems = do
  tabTy'@(TabPi (TabPiType (_:>ixTy') _)) <- substM tabTy
  dest <- case maybeDest of
    Just  d -> return d
    Nothing -> emitExpr $ DAMOp $ AllocDest tabTy'
  Abs bord ufoBlock <- buildAbs noHint IdxRepTy \ord -> do
    buildBlock $ unsafeFromOrdinal (sink ixTy') $ Var $ sink ord
  forM_ (enumerate elems) \(ord, e) -> do
    i <- dropSubst $ extendSubst (bord@>SubstVal (IdxRepVal (fromIntegral ord))) $
      traverseBlock ufoBlock
    idest <- indexRef dest i
    place (FullDest idest) =<< traverseAtom e
  return $ DAMOp $ Freeze dest


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
-- that full outermost buffer. Instead, we invoke traverseBlockWithDest on the body
-- of the i-loop, which will realize that v has a valid destination. Then,
-- traverseExprWithDest will be called at the for decl and will translate the j-loop
-- so that it never allocates scratch space for its result, but will put it directly in
-- the corresponding slice of the full 2D buffer.

type DestAssignment (i'::S) (o::S) = AtomNameMap SimpIR (ProjDest o) i'

data ProjDest o
  = FullDest (Dest SimpIR o)
  | ProjDest (NE.NonEmpty Projection) (Dest SimpIR o)  -- dest corresponds to the projection applied to name

lookupDest :: DestAssignment i' o -> SAtomName i' -> Maybe (ProjDest o)
lookupDest = flip lookupNameMap

-- Matches up the free variables of the atom, with the given dest. For example, if the
-- atom is a pair of two variables, the dest might be split into per-component dests,
-- and a dest assignment mapping each side to its respective dest will be returned.
-- This function works on a best-effort basis. It's never an error to not split the dest
-- as much as possible, but it can lead to unnecessary copies being done at run-time.
--
-- XXX: When adding more cases, be careful about potentially repeated vars in the output!
decomposeDest :: Emits o => Dest SimpIR o -> SAtom i' -> LowerM i o (Maybe (DestAssignment i' o))
decomposeDest dest = \case
  Var v -> return $ Just $ singletonNameMap v $ FullDest dest
  ProjectElt p x -> do
    (ps, v) <- return $ asNaryProj p x
    return $ Just $ singletonNameMap v $ ProjDest ps dest
  _ -> return Nothing

traverseBlockWithDest :: Emits o => Dest SimpIR o -> SBlock i -> LowerM i o (SAtom o)
traverseBlockWithDest dest (Block _ decls ans) = do
  decomposeDest dest ans >>= \case
    Nothing -> do
      ans' <- traverseDeclNest decls $ traverseAtom ans
      place (FullDest dest) ans'
      return ans'
    Just destMap -> do
      s <- getSubst
      case isDistinctNest decls of
        Nothing -> error "Non-distinct decls?"
        Just DistinctBetween -> do
          s' <- traverseDeclNestWithDestS destMap s decls
          -- But we have to emit explicit writes, for all the vars that are not defined in decls!
          forM_ (toListNameMap $ hoistFilterNameMap decls destMap) \(n, d) ->
            place d $ case s ! n of Rename v -> Var v; SubstVal a -> a
          withSubst s' $ substM ans


traverseDeclNestWithDestS
  :: forall i i' l o. (Emits o, DistinctBetween l i')
  => DestAssignment i' o -> Subst AtomSubstVal l o -> Nest (Decl SimpIR) l i'
  -> LowerM i o (Subst AtomSubstVal i' o)
traverseDeclNestWithDestS destMap s = \case
  Empty -> return s
  Nest (Let b (DeclBinding ann _ expr)) rest -> do
    DistinctBetween <- return $ withExtEvidence rest $ shortenBetween @i' b
    let maybeDest = lookupDest destMap $ sinkBetween $ binderName b
    expr' <- withSubst s $ traverseExprWithDest maybeDest expr
    v <- emitDecl (getNameHint b) ann expr'
    traverseDeclNestWithDestS destMap (s <>> (b @> Rename v)) rest

traverseExprWithDest :: forall i o. Emits o => Maybe (ProjDest o) -> SExpr i -> LowerM i o (SExpr o)
traverseExprWithDest dest expr = case expr of
  -- TODO: re-enable after fixing traverseTabCon bug
  -- TabCon ty els -> traverseTabCon tabDest ty els
  Hof (For dir ixDict body) -> traverseFor tabDest dir ixDict body
  Hof (RunWriter Nothing m body) -> traverseRWS body \ref' body' -> do
    m' <- traverseGenericE m
    return $ RunWriter ref' m' body'
  Hof (RunState Nothing s body) -> traverseRWS body \ref' body' -> do
    s' <- traverseAtom s
    return $ RunState ref' s' body'
  _ -> generic
  where
    tabDest = dest <&> \case FullDest d -> d; ProjDest _ _ -> error "unexpected projection"

    generic = do
      expr' <- traverseExprDefault expr
      case dest of
        Nothing -> return expr'
        Just d  -> do
          ans <- Var <$> emit expr'
          place d ans
          return $ Atom ans

    traverseRWS
      :: LamExpr SimpIR i
      -> (Maybe (Dest SimpIR o) -> LamExpr SimpIR o -> LowerM i o (Hof SimpIR o))
      -> LowerM i o (SExpr o)
    traverseRWS (LamExpr (BinaryNest hb rb) body) mkHof = do
      unpackRWSDest dest >>= \case
        Nothing -> generic
        Just (bodyDest, refDest) -> do
          let RefTy _ ty = binderType rb
          ty' <- traverseGenericE $ ignoreHoistFailure $ hoist hb ty
          liftM Hof $ mkHof refDest =<<
            buildEffLam (getNameHint rb) ty' \hb' rb' ->
              extendRenamer (hb@>hb' <.> rb@>rb') do
                case bodyDest of
                  Nothing -> traverseBlock body
                  Just bd -> traverseBlockWithDest (sink bd) body
    traverseRWS _ _ = error "Expected a binary lambda expression"

    unpackRWSDest = \case
      Nothing -> return Nothing
      Just d -> case d of
        FullDest fd -> do
          bd <- getProjRef 0 fd
          rd <- getProjRef 1 fd
          return $ Just (Just bd, Just rd)
        ProjDest (ProjectProduct 0 NE.:| []) pd -> return $ Just (Just pd, Nothing)
        ProjDest (ProjectProduct 1 NE.:| []) pd -> return $ Just (Nothing, Just pd)
        ProjDest _ _ -> return Nothing


place :: Emits o => ProjDest o -> SAtom o -> LowerM i o ()
place pd x = case pd of
  FullDest d   -> void $ emitExpr $ DAMOp $ Place d x
  ProjDest p d -> do
    x' <- normalizeNaryProj (NE.toList p) x
    void $ emitExpr $ DAMOp $ Place d x'

-- === Vectorization ===

-- WATCH OUT! This vectorization assumes that all raw references represent
-- destinations, and so no Place operations can cause write conflicts.

-- TODO: Local vector values? We might want to pack short and pure for loops into vectors,
-- to support things like float3 etc.
data Stability
  = Uniform    -- constant across vectorized dimension
  | Varying    -- varying across vectorized dimension
  | Contiguous -- varying, but contiguous across vectorized dimension
  | ProdStability [Stability]
  deriving (Eq, Show)

data VSubstValC (c::C) (n::S) where
  VVal :: Stability -> SAtom n -> VSubstValC (AtomNameC SimpIR) n
type VAtom = VSubstValC (AtomNameC SimpIR)
instance SinkableV VSubstValC
instance SinkableE (VSubstValC c) where
  sinkingProofE fresh (VVal s x) = VVal s $ sinkingProofE fresh x

instance PrettyPrec (VSubstValC c n) where
  prettyPrec (VVal s atom) = atPrec LowestPrec $ "@" <> viaShow s <+> pretty atom

type TopVectorizeM = BuilderT SimpIR (ReaderT Word32 (StateT Errs FallibleM))

vectorizeLoopsBlock :: (EnvReader m)
  => Word32 -> DestBlock SimpIR n
  -> m n (DestBlock SimpIR n, Errs)
vectorizeLoopsBlock vectorByteWidth (DestBlock destb body) = liftEnvReaderM do
  refreshAbs (Abs destb body) \d (Block _ decls ans) -> do
    vblock <- liftBuilderT $ buildBlock do
                s <- vectorizeLoopsRec emptyInFrag decls
                applyRename s ans
    case (runFallibleM . (`runStateT` mempty) . (`runReaderT` vectorByteWidth)) vblock of
      -- The failure case should not occur: vectorization errors should have been
      -- caught inside `vectorizeLoopsRec` (and should have been added to the
      -- `Errs` state of the `StateT` instance that is run with `runStateT` above).
      Failure errs -> error $ pprint errs
      Success (block', errs) -> return $ (DestBlock d block', errs)
{-# SCC vectorizeLoopsBlock #-}

vectorizeLoops  :: (EnvReader m)
  => Word32 -> DestLamExpr SimpIR n
  -> m n (DestLamExpr SimpIR n, Errs)
vectorizeLoops width (DestLamExpr bs body) = liftEnvReaderM do
  refreshAbs (Abs bs body) \bs' body' -> do
    (body'', errs) <- vectorizeLoopsBlock width body'
    return $ (DestLamExpr bs' body'', errs)

addVectErrCtx :: Fallible m => String -> String -> m a -> m a
addVectErrCtx name payload m =
  let ctx = mempty { messageCtx = ["In `" ++ name ++ "`:\n" ++ payload] }
  in addErrCtx ctx m

throwVectErr :: Fallible m => String -> m a
throwVectErr msg = throwErr (Err MiscErr mempty msg)

prependCtxToErrs :: ErrCtx -> Errs -> Errs
prependCtxToErrs ctx (Errs errs) =
  Errs $ map (\(Err ty ctx' msg) -> Err ty (ctx <> ctx') msg) errs

vectorizeLoopsRec :: (Ext i o, Emits o)
                  => SubstFrag Name i i' o -> Nest SDecl i' i''
                  -> TopVectorizeM o (SubstFrag Name i i'' o)
vectorizeLoopsRec frag nest =
  case nest of
    Empty -> return frag
    Nest (Let b (DeclBinding ann _ expr)) rest -> do
      vectorByteWidth <- ask
      expr' <- applyRename frag expr
      narrowestTypeByteWidth <- getNarrowestTypeByteWidth expr'
      let loopWidth = vectorByteWidth `div` narrowestTypeByteWidth
      v <- case expr of
        DAMOp (Seq dir (IxDictRawFin (IdxRepVal n)) dest@(ProdVal [_]) body)
          | n `mod` loopWidth == 0 -> (do
              Distinct <- getDistinct
              let vn = n `div` loopWidth
              body' <- vectorizeSeq loopWidth frag body
              dest' <- applyRename frag dest
              emit $ DAMOp $ Seq dir (IxDictRawFin (IdxRepVal vn)) dest' body')
            `catchErr` \errs -> do
                let msg = "In `vectorizeLoopsRec`:\nExpr:\n" ++ pprint expr
                    ctx = mempty { messageCtx = [msg] }
                    errs' = prependCtxToErrs ctx errs
                modify (<> errs')
                dest' <- applyRename frag dest
                body' <- applyRename frag body
                emit $ DAMOp $ Seq dir (IxDictRawFin (IdxRepVal n)) dest' body'
        _ -> emitDecl (getNameHint b) ann =<< applyRename frag expr
      vectorizeLoopsRec (frag <.> b @> v) rest

atMostInitEffect :: IRRep r => EffectRow r n -> Bool
atMostInitEffect scrutinee = case scrutinee of
  Pure -> True
  OneEffect InitEffect -> True
  _ -> False

vectorizeSeq :: forall i i' o. (Distinct o, Ext i o)
             => Word32 -> SubstFrag Name i i' o -> LamExpr SimpIR i'
             -> TopVectorizeM o (LamExpr SimpIR o)
vectorizeSeq loopWidth frag (UnaryLamExpr (b:>ty) body) = do
  if atMostInitEffect (blockEffects body)
    then do
      (_, ty') <- case ty of
        ProdTy [ixTy, ref] -> do
          ixTy' <- applyRename frag ixTy
          ref' <- applyRename frag ref
          return (ixTy', ProdTy [IdxRepTy, ref'])
        _ -> error "Unexpected seq binder type"
      result <- liftM (`runReaderT` loopWidth) $ liftBuilderT $
        buildUnaryLamExpr (getNameHint b) (sink ty') \ci -> do
          -- XXX: we're assuming `Fin n` here
          (viOrd, dest) <- fromPair $ Var ci
          iOrd <- imul viOrd $ IdxRepVal loopWidth
          let s = newSubst iSubst <>> b @> VVal (ProdStability [Contiguous, ProdStability [Uniform]]) (PairVal iOrd dest)
          runSubstReaderT s $ runVectorizeM $ vectorizeBlock body $> UnitVal
      case runReaderT (fromFallibleM result) mempty of
        Success s -> return s
        Failure errs -> throwErrs errs  -- re-raise inside `TopVectorizeM`
    else throwVectErr "Effectful loop vectorization not implemented!"
  where
    iSubst :: (Color c, DExt o o') => Name c i' -> VSubstValC c o'
    iSubst v = case lookupSubstFragProjected frag v of
      Left v'  -> sink $ fromNameVAtom v'
      Right v' -> sink $ fromNameVAtom v'
vectorizeSeq _ _ _ = error "expected a unary lambda expression"

fromNameVAtom :: forall c n. Color c => Name c n -> VSubstValC c n
fromNameVAtom v = case eqColorRep @c @(AtomNameC SimpIR) of
  Just ColorsEqual -> VVal Uniform $ Var v
  _ -> error "Unexpected non-atom name"

newtype VectorizeM i o a =
  VectorizeM { runVectorizeM :: SubstReaderT VSubstValC (BuilderT SimpIR (ReaderT Word32 FallibleM)) i o a }
  deriving ( Functor, Applicative, Monad, Fallible, MonadFail, SubstReader VSubstValC
           , Builder SimpIR, EnvReader, EnvExtender, ScopeReader, ScopableBuilder SimpIR)

getLoopWidth :: VectorizeM i o Word32
getLoopWidth = VectorizeM $ SubstReaderT $ ReaderT $ const $ ask

vectorizeBlock :: Emits o => SBlock i -> VectorizeM i o (VAtom o)
vectorizeBlock block@(Block _ decls (ans :: SAtom i')) =
  addVectErrCtx "vectorizeBlock" ("Block:\n" ++ pprint block) $
    go decls
    where
      go :: Emits o => Nest SDecl i i' -> VectorizeM i o (VAtom o)
      go = \case
        Empty -> vectorizeAtom ans
        Nest (Let b (DeclBinding _ _ expr)) rest -> do
          v <- vectorizeExpr expr
          extendSubst (b @> v) $ go rest

vectorizeExpr :: Emits o => SExpr i -> VectorizeM i o (VAtom o)
vectorizeExpr expr = addVectErrCtx "vectorizeExpr" ("Expr:\n" ++ pprint expr) do
  case expr of
    Atom atom -> vectorizeAtom atom
    PrimOp op -> vectorizePrimOp op
    DAMOp op -> vectorizeDAMOp op
    RefOp ref op -> vectorizeRefOp ref op
    -- Vectorizing IO might not always be safe! Here, we depend on vectorizeOp
    -- being picky about the IO-inducing ops it supports, and expect it to
    -- complain about FFI calls and the like.
    Hof (RunIO body) -> do
    -- TODO: buildBlockAux?
      Abs decls (LiftE vy `PairE` yWithTy) <- buildScoped do
        VVal vy y <- vectorizeBlock body
        PairE (LiftE vy) <$> withType y
      body' <- absToBlock =<< computeAbsEffects (Abs decls yWithTy)
      VVal vy . Var <$> emit (Hof (RunIO body'))
    _ -> throwVectErr $ "Cannot vectorize expr: " ++ pprint expr

vectorizeDAMOp :: Emits o => DAMOp SimpIR i -> VectorizeM i o (VAtom o)
vectorizeDAMOp op =
  case op of
    Place ref' val' -> do
      VVal vref ref <- vectorizeAtom ref'
      sval@(VVal vval val) <- vectorizeAtom val'
      VVal Uniform <$> case (vref, vval) of
        (Uniform   , Uniform   ) -> emitExpr $ DAMOp $ Place ref val
        (Uniform   , _         ) -> throwVectErr "Write conflict? This should never happen!"
        (Varying   , _         ) -> throwVectErr "Vector scatter not implemented"
        (Contiguous, Varying   ) -> emitExpr $ DAMOp $ Place ref val
        (Contiguous, Contiguous) -> emitExpr . DAMOp . Place ref =<< ensureVarying sval
        _ -> throwVectErr "Not implemented yet"
    _ -> throwVectErr $ "Can't vectorize op: " ++ pprint op

vectorizeRefOp :: Emits o => SAtom i -> RefOp SimpIR i -> VectorizeM i o (VAtom o)
vectorizeRefOp ref' op =
  case op of
    IndexRef i' -> do
      VVal Uniform ref <- vectorizeAtom ref'
      VVal Contiguous i <- vectorizeAtom i'
      getType ref >>= \case
        TC (RefType _ (TabTy tb a)) -> do
          vty <- getVectorType =<< case hoist tb a of
            HoistSuccess a' -> return a'
            HoistFailure _  -> throwVectErr "Can't vectorize dependent table application"
          VVal Contiguous <$> emitOp (VectorOp $ VectorSubref ref i vty)
        refTy -> do
          throwVectErr do
            "bad type: " ++ pprint refTy ++ "\nref' : " ++ pprint ref'
    _ -> throwVectErr $ "Can't vectorize op: " ++ pprint (RefOp ref' op)

vectorizePrimOp :: Emits o => PrimOp (Atom SimpIR i) -> VectorizeM i o (VAtom o)
vectorizePrimOp op = do
  op' <- (inline traversePrimOp) vectorizeAtom op
  case op' of
    UnOp opk sx@(VVal vx x) -> do
      let v = case vx of Uniform -> Uniform; _ -> Varying
      x' <- if vx /= v then ensureVarying sx else return x
      VVal v <$> emitOp (UnOp opk x')
    BinOp opk sx@(VVal vx x) sy@(VVal vy y) -> do
      let v = case (vx, vy) of (Uniform, Uniform) -> Uniform; _ -> Varying
      x' <- if vx /= v then ensureVarying sx else return x
      y' <- if vy /= v then ensureVarying sy else return y
      VVal v <$> emitOp (BinOp opk x' y')
    MiscOp (CastOp (VVal Uniform ty) (VVal vx x)) -> do
      ty' <- case vx of
        Uniform    -> return ty
        Varying    -> getVectorType ty
        Contiguous -> return ty
        ProdStability _ -> throwVectErr "Unexpected cast of product type"
      VVal vx <$> emitOp (MiscOp $ CastOp ty' x)
    MemOp (PtrOffset (VVal Uniform ptr) (VVal Contiguous off)) -> do
      VVal Contiguous <$> emitOp (MemOp $ PtrOffset ptr off)
    MemOp (PtrLoad (VVal Contiguous ptr)) -> do
      BaseTy (PtrType (addrSpace, a)) <- getType ptr
      BaseTy av <- getVectorType $ BaseTy a
      ptr' <- emitOp $ MiscOp $ CastOp (BaseTy $ PtrType (addrSpace, av)) ptr
      VVal Varying <$> emitOp (MemOp $ PtrLoad ptr')
    _ -> throwVectErr $ "Can't vectorize op: " ++ pprint op'

vectorizeAtom :: SAtom i -> VectorizeM i o (VAtom o)
vectorizeAtom atom = addVectErrCtx "vectorizeAtom" ("Atom:\n" ++ pprint atom) do
  case atom of
    Var v -> lookupSubstM v
    -- Vectors of base newtypes are already newtype-stripped.
    ProjectElt (ProjectProduct i) x -> do
      VVal vv x' <- vectorizeAtom x
      ov <- case vv of
        ProdStability sbs -> return $ sbs !! i
        _ -> throwVectErr "Invalid projection"
      x'' <- normalizeProj (ProjectProduct i) x'
      return $ VVal ov x''
    ProjectElt UnwrapNewtype _ -> error "Shouldn't have newtypes left" -- TODO: check statically
    Con (Lit l) -> return $ VVal Uniform $ Con $ Lit l
    _ -> do
      subst <- getSubst
      VVal Uniform <$> fmapNamesM (uniformSubst subst) atom
    where
      uniformSubst :: Color c => Subst VSubstValC i o -> Name c i -> AtomSubstVal c o
      uniformSubst subst n = case subst ! n of
        VVal Uniform x -> SubstVal x
        -- TODO(nrink): Throw instead of `error`.
        _ -> error $ "Can't vectorize atom " ++ pprint atom

getVectorType :: SType o -> VectorizeM i o (SAtom o)
getVectorType ty = addVectErrCtx "getVectorType" ("Type:\n" ++ pprint ty) do
  case ty of
    BaseTy (Scalar sbt) -> do
      els <- getLoopWidth
      return $ BaseTy $ Vector [els] sbt
    -- TODO: Should we support tables?
    _ -> throwVectErr $ "Can't make a vector of " ++ pprint ty

ensureVarying :: Emits o => VAtom o -> VectorizeM i o (SAtom o)
ensureVarying (VVal s val) = case s of
  Varying -> return val
  Uniform -> do
    vty <- getVectorType =<< getType val
    emitOp $ VectorOp $ VectorBroadcast val vty
  -- Note that the implementation of this case will depend on val's type.
  Contiguous -> do
    ty <- getType val
    vty <- getVectorType ty
    case ty of
      BaseTy (Scalar sbt) -> do
        bval <- emitOp $ VectorOp $ VectorBroadcast val vty
        iota <- emitOp $ VectorOp $ VectorIota vty
        emitOp $ BinOp (if isIntegral sbt then IAdd else FAdd) bval iota
      _ -> throwVectErr "Not implemented"
  ProdStability _ -> throwVectErr "Not implemented"

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

newtype Word32' (n::S) = Word32' Word32
                       deriving (Eq, Show)

toWord32 :: Word32' n -> Word32
toWord32 (Word32' x) = x

fromWord32 :: Word32 -> Word32' n
fromWord32 x = Word32' x

maxWord32' :: Word32' n
maxWord32' = Word32' (maxBound :: Word32)

instance Ord (Word32' n) where
  compare (Word32' x) (Word32' y) = compare x y

instance SinkableE Word32' where
  sinkingProofE _ (Word32' x) = Word32' x
instance HoistableState Word32' where
  hoistState _ _ (Word32' x) = Word32' x
  {-# INLINE hoistState #-}

instance GenericTraverser SimpIR UnitB Word32' where
  traverseExpr expr = case expr of
    PrimOp _ -> do
      expr' <- substM expr
      ty <- getType expr'
      modify (min $ typeByteWidth ty)
      return expr'
    _ -> traverseExprDefault expr

typeByteWidth :: SType n -> Word32' n
typeByteWidth ty = case ty of
 TC (BaseType bt) -> case bt of
  -- Currently only support vectorization of scalar types (cf. `getVectorType` above):
  Scalar _ -> fromWord32 . fromInteger . toInteger $ sizeOf bt
  _ -> maxWord32'
 _ -> maxWord32'

getNarrowestTypeByteWidth :: (Emits n, EnvReader m) => Expr SimpIR n -> m n Word32
getNarrowestTypeByteWidth x = do
  (_, result) <- liftGenericTraverserM maxWord32' (traverseExpr x)
  if result == maxWord32'
    then return 1
    else return $ toWord32 result
