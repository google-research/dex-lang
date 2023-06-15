-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Vectorize (vectorizeLoops) where

import Prelude hiding ((.))
import Data.Word
import Data.Functor
import Data.Text.Prettyprint.Doc (Pretty, pretty, viaShow, (<+>))
import Control.Category
import Control.Monad.Reader
import Control.Monad.State.Strict

import Builder
import Core
import Err
import CheapReduction
import IRVariants
import Lower (DestBlock, DestLamExpr)
import MTL1
import Name
import Subst
import PPrint
import QueryType
import Types.Core
import Types.Primitives

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
  = Uniform    -- constant across vectorized dimension
  | Varying    -- varying across vectorized dimension
  | Contiguous -- varying, but contiguous across vectorized dimension
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

newtype TopVectorizeM (i::S) (o::S) (a:: *) = TopVectorizeM
  { runTopVectorizeM ::
      SubstReaderT Name
       (ReaderT1 (LiftE Word32)
         (StateT1 (LiftE Errs) (BuilderT SimpIR FallibleM))) i o a }
  deriving ( Functor, Applicative, Monad, MonadFail, MonadReader (LiftE Word32 o)
           , MonadState (LiftE Errs o), Fallible, ScopeReader, EnvReader
           , EnvExtender, Builder SimpIR, ScopableBuilder SimpIR, Catchable
           , SubstReader Name)

vectorizeLoops :: EnvReader m => Word32 -> DestLamExpr n -> m n (DestLamExpr n, Errs)
vectorizeLoops width (LamExpr bsDestB body) = liftEnvReaderM do
  case popNest bsDestB of
    Just (PairB bs b) ->
      refreshAbs (Abs bs (Abs b body)) \bs' body' -> do
        (Abs b'' body'', errs) <- liftTopVectorizeM width $ vectorizeLoopsDestBlock body'
        return $ (LamExpr (bs' >>> UnaryNest b'') body'', errs)
    Nothing -> error "expected a trailing dest binder"

liftTopVectorizeM :: (EnvReader m)
  => Word32 -> TopVectorizeM i i a -> m i (a, Errs)
liftTopVectorizeM vectorByteWidth action = do
  fallible <- liftBuilderT $
    flip runStateT1 mempty $ runReaderT1 (LiftE vectorByteWidth) $
      runSubstReaderT idSubst $ runTopVectorizeM action
  case runFallibleM fallible of
    -- The failure case should not occur: vectorization errors should have been
    -- caught inside `vectorizeLoopsDecls` (and should have been added to the
    -- `Errs` state of the `StateT` instance that is run with `runStateT` above).
    Failure errs -> error $ pprint errs
    Success (a, (LiftE errs)) -> return $ (a, errs)

addVectErrCtx :: Fallible m => String -> String -> m a -> m a
addVectErrCtx name payload m =
  let ctx = mempty { messageCtx = ["In `" ++ name ++ "`:\n" ++ payload] }
  in addErrCtx ctx m

throwVectErr :: Fallible m => String -> m a
throwVectErr msg = throwErr (Err MiscErr mempty msg)

prependCtxToErrs :: ErrCtx -> Errs -> Errs
prependCtxToErrs ctx (Errs errs) =
  Errs $ map (\(Err ty ctx' msg) -> Err ty (ctx <> ctx') msg) errs

vectorizeLoopsDestBlock :: DestBlock i
  -> TopVectorizeM i o (DestBlock o)
vectorizeLoopsDestBlock (Abs (destb:>destTy) body) = do
  destTy' <- renameM destTy
  withFreshBinder (getNameHint destb) destTy' \destb' -> do
    extendRenamer (destb @> binderName destb') do
      Abs destb' <$> buildBlock (vectorizeLoopsBlock body)
{-# SCC vectorizeLoopsDestBlock #-}

vectorizeLoopsBlock :: (Emits o)
  => Block SimpIR i -> TopVectorizeM i o (SAtom o)
vectorizeLoopsBlock (Block _ decls ans) =
  vectorizeLoopsDecls decls $ renameM ans

vectorizeLoopsDecls :: (Emits o)
  => Nest SDecl i i' -> TopVectorizeM i' o a -> TopVectorizeM i o a
vectorizeLoopsDecls nest cont =
  case nest of
    Empty -> cont
    Nest (Let b (DeclBinding ann expr)) rest -> do
      v <- emitDecl (getNameHint b) ann =<< vectorizeLoopsExpr expr
      extendSubst (b @> atomVarName v) $
        vectorizeLoopsDecls rest cont

vectorizeLoopsExpr :: (Emits o) => SExpr i -> TopVectorizeM i o (SExpr o)
vectorizeLoopsExpr expr = do
  LiftE vectorByteWidth <- ask
  narrowestTypeByteWidth <- getNarrowestTypeByteWidth =<< renameM expr
  let loopWidth = vectorByteWidth `div` narrowestTypeByteWidth
  case expr of
    PrimOp (DAMOp (Seq _ dir (IxType IdxRepTy (IxDictRawFin (IdxRepVal n))) dest@(ProdVal [_]) body))
      | n `mod` loopWidth == 0 -> (do
          Distinct <- getDistinct
          let vn = n `div` loopWidth
          body' <- vectorizeSeq loopWidth body
          dest' <- renameM dest
          seqOp <- mkSeq dir (IxType IdxRepTy (IxDictRawFin (IdxRepVal vn))) dest' body'
          return $ PrimOp $ DAMOp seqOp)
        `catchErr` \errs -> do
            let msg = "In `vectorizeLoopsDecls`:\nExpr:\n" ++ pprint expr
                ctx = mempty { messageCtx = [msg] }
                errs' = prependCtxToErrs ctx errs
            modify (<> LiftE errs')
            dest' <- renameM dest
            body' <- renameM body
            seqOp <- mkSeq dir (IxType IdxRepTy (IxDictRawFin (IdxRepVal n))) dest' body'
            return $ PrimOp $ DAMOp seqOp
    PrimOp (Hof (TypedHof _ (RunReader item (BinaryLamExpr hb' refb' body)))) -> do
      item' <- renameM item
      itemTy <- return $ getType item'
      lam <- buildEffLam noHint itemTy \hb refb ->
        extendRenamer (hb' @> atomVarName hb) do
          extendRenamer (refb' @> atomVarName refb) do
            vectorizeLoopsBlock body
      PrimOp . Hof <$> mkTypedHof (RunReader item' lam)
    PrimOp (Hof (TypedHof _ (RunWriter (Just dest) monoid (BinaryLamExpr hb' refb' body)))) -> do
      dest' <- renameM dest
      monoid' <- renameM monoid
      accTy <- return $ getType $ baseEmpty monoid'
      lam <- buildEffLam noHint accTy \hb refb ->
        extendRenamer (hb' @> atomVarName hb) do
          extendRenamer (refb' @> atomVarName refb) do
            vectorizeLoopsBlock body
      PrimOp . Hof <$> mkTypedHof (RunWriter (Just dest') monoid' lam)
    _ -> renameM expr

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
vectorSafeEffect :: EffectRow SimpIR n -> Bool
vectorSafeEffect (EffectRow effs NoTail) = all safe $ eSetToList effs where
  safe InitEffect = True
  safe (RWSEffect Reader _) = True
  safe _ = False

vectorizeSeq :: Word32 -> LamExpr SimpIR i -> TopVectorizeM i o (LamExpr SimpIR o)
vectorizeSeq loopWidth (UnaryLamExpr (b:>ty) body) = do
  if vectorSafeEffect (getEffects body)
    then do
      (_, ty') <- case ty of
        ProdTy [ixTy, ref] -> do
          ixTy' <- renameM ixTy
          ref' <- renameM ref
          return (ixTy', ProdTy [IdxRepTy, ref'])
        _ -> error "Unexpected seq binder type"
      liftVectorizeM loopWidth $
        buildUnaryLamExpr (getNameHint b) ty' \ci -> do
          -- XXX: we're assuming `Fin n` here
          (viOrd, dest) <- fromPair $ Var ci
          iOrd <- imul viOrd $ IdxRepVal loopWidth
          extendSubst (b @> VVal (ProdStability [Contiguous, ProdStability [Uniform]]) (PairVal iOrd dest)) $
            vectorizeBlock body $> UnitVal
    else throwVectErr "Effectful loop vectorization not implemented!"
vectorizeSeq _ _ = error "expected a unary lambda expression"

newtype VectorizeM i o a =
  VectorizeM { runVectorizeM ::
    SubstReaderT VSubstValC (BuilderT SimpIR (ReaderT Word32 FallibleM)) i o a }
  deriving ( Functor, Applicative, Monad, Fallible, MonadFail
           , SubstReader VSubstValC , Builder SimpIR, EnvReader, EnvExtender
           , ScopeReader, ScopableBuilder SimpIR)

liftVectorizeM :: (SubstReader Name m, EnvReader (m i), Fallible (m i o))
  => Word32 -> VectorizeM i o a -> m i o a
liftVectorizeM loopWidth action = do
  subst <- getSubst
  act <- liftBuilderT $ runSubstReaderT (newSubst $ vSubst subst) $ runVectorizeM action
  let fallible = flip runReaderT loopWidth act
  case runFallibleM fallible of
    Success a -> return a
    Failure errs -> throwErrs errs  -- re-raise inside ambient monad
  where
    vSubst subst val = VRename $ subst ! val

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
        Nest (Let b (DeclBinding _ expr)) rest -> do
          v <- vectorizeExpr expr
          extendSubst (b @> v) $ go rest

vectorizeExpr :: Emits o => SExpr i -> VectorizeM i o (VAtom o)
vectorizeExpr expr = addVectErrCtx "vectorizeExpr" ("Expr:\n" ++ pprint expr) do
  case expr of
    TabApp _ tbl [ix] -> do
      VVal Uniform tbl' <- vectorizeAtom tbl
      VVal Contiguous ix' <- vectorizeAtom ix
      case getType tbl' of
        TabTy _ tb a -> do
          vty <- getVectorType =<< case hoist tb a of
            HoistSuccess a' -> return a'
            HoistFailure _  -> throwVectErr "Can't vectorize dependent table application"
          VVal Varying <$> emitOp (VectorOp $ VectorIdx tbl' ix' vty)
        tblTy -> do
          throwVectErr $ "bad type: " ++ pprint tblTy ++ "\ntbl' : " ++ pprint tbl'
    Atom atom -> vectorizeAtom atom
    PrimOp op -> vectorizePrimOp op
    _ -> throwVectErr $ "Cannot vectorize expr: " ++ pprint expr

vectorizeDAMOp :: Emits o => DAMOp SimpIR i -> VectorizeM i o (VAtom o)
vectorizeDAMOp op =
  case op of
    Place ref' val' -> do
      VVal vref ref <- vectorizeAtom ref'
      sval@(VVal vval val) <- vectorizeAtom val'
      VVal Uniform <$> case (vref, vval) of
        (Uniform   , Uniform   ) -> emitExpr $ PrimOp $ DAMOp $ Place ref val
        (Uniform   , _         ) -> throwVectErr "Write conflict? This should never happen!"
        (Varying   , _         ) -> throwVectErr "Vector scatter not implemented"
        (Contiguous, Varying   ) -> emitExpr $ PrimOp $ DAMOp $ Place ref val
        (Contiguous, Contiguous) -> emitExpr . PrimOp . DAMOp . Place ref =<< ensureVarying sval
        _ -> throwVectErr "Not implemented yet"
    _ -> throwVectErr $ "Can't vectorize op: " ++ pprint op

vectorizeRefOp :: Emits o => SAtom i -> RefOp SimpIR i -> VectorizeM i o (VAtom o)
vectorizeRefOp ref' op =
  case op of
    MAsk -> do
      -- TODO A contiguous reference becomes a vector load producing a varying
      -- result.
      VVal Uniform ref <- vectorizeAtom ref'
      VVal Uniform <$> emitOp (RefOp ref MAsk)
    IndexRef _ i' -> do
      VVal Uniform ref <- vectorizeAtom ref'
      VVal Contiguous i <- vectorizeAtom i'
      case getType ref of
        TC (RefType _ (TabTy _ tb a)) -> do
          vty <- getVectorType =<< case hoist tb a of
            HoistSuccess a' -> return a'
            HoistFailure _  -> throwVectErr "Can't vectorize dependent table application"
          VVal Contiguous <$> emitOp (VectorOp $ VectorSubref ref i vty)
        refTy -> do
          throwVectErr do
            "bad type: " ++ pprint refTy ++ "\nref' : " ++ pprint ref'
    _ -> throwVectErr $ "Can't vectorize op: " ++ pprint (RefOp ref' op)

vectorizePrimOp :: Emits o => PrimOp SimpIR i -> VectorizeM i o (VAtom o)
vectorizePrimOp op = case op of
  UnOp opk arg -> do
    sx@(VVal vx x) <- vectorizeAtom arg
    let v = case vx of Uniform -> Uniform; _ -> Varying
    x' <- if vx /= v then ensureVarying sx else return x
    VVal v <$> emitOp (UnOp opk x')
  BinOp opk arg1 arg2 -> do
    sx@(VVal vx x) <- vectorizeAtom arg1
    sy@(VVal vy y) <- vectorizeAtom arg2
    let v = case (vx, vy) of (Uniform, Uniform) -> Uniform; _ -> Varying
    x' <- if vx /= v then ensureVarying sx else return x
    y' <- if vy /= v then ensureVarying sy else return y
    VVal v <$> emitOp (BinOp opk x' y')
  MiscOp (CastOp tyArg arg) -> do
    ty <- vectorizeType tyArg
    VVal vx x <- vectorizeAtom arg
    ty' <- case vx of
      Uniform    -> return ty
      Varying    -> getVectorType ty
      Contiguous -> return ty
      ProdStability _ -> throwVectErr "Unexpected cast of product type"
    VVal vx <$> emitOp (MiscOp $ CastOp ty' x)
  DAMOp op' -> vectorizeDAMOp op'
  RefOp ref op' -> vectorizeRefOp ref op'
  MemOp (PtrOffset arg1 arg2) -> do
    VVal Uniform ptr    <- vectorizeAtom arg1
    VVal Contiguous off <- vectorizeAtom arg2
    VVal Contiguous <$> emitOp (MemOp $ PtrOffset ptr off)
  MemOp (PtrLoad arg) -> do
    VVal Contiguous ptr <- vectorizeAtom arg
    BaseTy (PtrType (addrSpace, a)) <- return $ getType ptr
    BaseTy av <- getVectorType $ BaseTy a
    ptr' <- emitOp $ MiscOp $ CastOp (BaseTy $ PtrType (addrSpace, av)) ptr
    VVal Varying <$> emitOp (MemOp $ PtrLoad ptr')
  -- Vectorizing IO might not always be safe! Here, we depend on vectorizeOp
  -- being picky about the IO-inducing ops it supports, and expect it to
  -- complain about FFI calls and the like.
  Hof (TypedHof _ (RunIO body)) -> do
  -- TODO: buildBlockAux?
    Abs decls (LiftE vy `PairE` yWithTy) <- buildScoped do
      VVal vy y <- vectorizeBlock body
      PairE (LiftE vy) <$> withType y
    body' <- absToBlock =<< computeAbsEffects (Abs decls yWithTy)
    VVal vy <$> emitHof (RunIO body')
  _ -> throwVectErr $ "Can't vectorize op: " ++ pprint op

vectorizeType :: SType i -> VectorizeM i o (SType o)
vectorizeType t = do
  subst <- getSubst
  fmapNamesM (uniformSubst subst) t

vectorizeAtom :: SAtom i -> VectorizeM i o (VAtom o)
vectorizeAtom atom = addVectErrCtx "vectorizeAtom" ("Atom:\n" ++ pprint atom) do
  case atom of
    Var v -> lookupSubstM (atomVarName v) >>= \case
      VRename v' -> VVal Uniform . Var <$> toAtomVar v'
      v' -> return v'
    -- Vectors of base newtypes are already newtype-stripped.
    ProjectElt _ (ProjectProduct i) x -> do
      VVal vv x' <- vectorizeAtom x
      ov <- case vv of
        ProdStability sbs -> return $ sbs !! i
        _ -> throwVectErr "Invalid projection"
      x'' <- normalizeProj (ProjectProduct i) x'
      return $ VVal ov x''
    ProjectElt _ UnwrapNewtype _ -> error "Shouldn't have newtypes left" -- TODO: check statically
    Con (Lit l) -> return $ VVal Uniform $ Con $ Lit l
    _ -> do
      subst <- getSubst
      VVal Uniform <$> fmapNamesM (uniformSubst subst) atom

uniformSubst :: Color c => Subst VSubstValC i o -> Name c i -> AtomSubstVal c o
uniformSubst subst n = case subst ! n of
  VVal Uniform x -> SubstVal x
  VRename name -> Rename name
  -- TODO(nrink): Throw instead of `error`.
  _ -> error "Can't vectorize atom"

getVectorType :: SType o -> VectorizeM i o (SType o)
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
    vty <- getVectorType $ getType val
    emitOp $ VectorOp $ VectorBroadcast val vty
  -- Note that the implementation of this case will depend on val's type.
  Contiguous -> do
    let ty = getType val
    vty <- getVectorType ty
    case ty of
      BaseTy (Scalar sbt) -> do
        bval <- emitOp $ VectorOp $ VectorBroadcast val vty
        iota <- emitOp $ VectorOp $ VectorIota vty
        emitOp $ BinOp (if isIntegral sbt then IAdd else FAdd) bval iota
      _ -> throwVectErr "Not implemented"
  ProdStability _ -> throwVectErr "Not implemented"
ensureVarying (VRename v) = do
  x <- Var <$> toAtomVar v
  ensureVarying (VVal Uniform x)

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
    _ -> fallback
    where fallback = visitGeneric expr

typeByteWidth :: SType n -> Word32
typeByteWidth ty = case ty of
 TC (BaseType bt) -> case bt of
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
