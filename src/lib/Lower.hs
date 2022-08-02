-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Lower (lowerFullySequential, vectorizeLoops) where

import Data.Word
import Data.Functor
import Data.Set qualified as S
import Data.List.NonEmpty qualified as NE
import Data.Text.Prettyprint.Doc (pretty, viaShow, (<+>))
import Control.Monad.Reader
import Unsafe.Coerce
import GHC.Exts (inline)

import Types.Core
import Types.Primitives

import Err
import Name
import MTL1
import Core
import Builder
import PPrint
import QueryType
import GenericTraversal
import Util (foldMapM)

lowerFullySequential :: EnvReader m => Block n -> m n (Block n)
lowerFullySequential (Block _ decls result) = liftM fst $ liftGenericTraverserM LFS $
    buildBlock $ traverseDeclNest decls $ substM result

data LFS (n::S) = LFS
type LowerM = GenericTraverserM LFS
instance SinkableE LFS where
  sinkingProofE _ LFS = LFS
instance HoistableState LFS where
  hoistState _ _ LFS = LFS
  {-# INLINE hoistState #-}

-- It would be nice to figure out a way to not have to update the effect
-- annotations manually... The only interesting case below is really the For.
instance GenericTraverser LFS where
  traverseExpr expr = case expr of
    Hof (For dir ixDict (Lam body)) -> traverseFor Nothing dir ixDict body
    Case _ _ _ _ -> do
      Case e alts ty _ <- traverseExprDefault expr
      eff' <- foldMapM getEffects alts
      return $ Case e alts ty eff'
    _ -> traverseExprDefault expr
  traverseAtom atom = case atom of
    Lam _ -> do
      traverseAtomDefault atom >>= \case
        Lam (LamExpr (LamBinder b ty arr _) body@(Block ann _ _)) -> do
          let eff' = case ann of BlockAnn _ e -> e; NoBlockAnn -> Pure
          return $ Lam $ LamExpr (LamBinder b ty arr eff') body
        _ -> error "Expected a lambda"
    _ -> traverseAtomDefault atom

type Dest = Atom

traverseFor :: Emits o => Maybe (Dest o) -> ForAnn -> Atom i -> LamExpr i -> LowerM i o (Expr o)
traverseFor maybeDest dir ixDict lam@(LamExpr (LamBinder ib ty arr eff) body) = do
  initDest <- case maybeDest of
    Just  d -> return d
    Nothing -> emitOp . AllocDest =<< getTypeSubst (Hof $ For dir ixDict (Lam lam))
  destTy <- getType initDest
  ty' <- substM ty
  ixDict' <- substM ixDict
  eff' <- substM $ ignoreHoistFailure $ hoist ib eff
  let eff'' = extendEffRow (S.singleton IOEffect) eff'
  body' <- buildLam noHint arr (PairTy ty' destTy) eff'' \b' -> do
    (i, dest) <- fromPair $ Var b'
    idest <- emitOp $ IndexRef dest i
    extendSubst (ib @> SubstVal i) $ traverseBlockWithDest idest body
    return UnitVal
  let seqHof = Hof $ Seq dir ixDict' initDest body'
  Op . Freeze . Var <$> emit seqHof

-- Destination-passing traversals

type DestAssignment (i'::S) (o::S) = AtomNameMap (Dest o) i'

lookupDest :: DestAssignment i' o -> AtomName i' -> Maybe (Dest o)
lookupDest = flip lookupNameMap

-- Matches up the free variables of the atom, with the given dest. For example, if the
-- atom is a pair of two variables, the dest might be split into per-component dests,
-- and a dest assignment mapping each side to its respective dest will be returned.
-- This function works on a best-effort basis. It's never an error to not split the dest
-- as much as possible, but it can lead to unnecessary copies being done at run-time.
decomposeDest :: Emits o => Dest o -> Atom i' -> LowerM i o (Maybe (DestAssignment i' o))
decomposeDest dest = \case
  Var v -> return $ Just $ singletonNameMap v dest
  _ -> return Nothing

traverseBlockWithDest :: Emits o => Dest o -> Block i -> LowerM i o ()
traverseBlockWithDest dest (Block _ decls ans) = do
  decomposeDest dest ans >>= \case
    Nothing -> do
      ans' <- traverseDeclNest decls $ traverseAtom ans
      place dest ans'
    Just destMap -> do
      s <- getSubst
      case isDistinctNest decls of
        Nothing -> error "Non-distinct decls?"
        Just DistinctBetween -> do
          -- Note that we ignore ans! Its components are written inplace through destMap.
          traverseDeclNestWithDestS destMap s decls
          -- But we have to emit explicit writes, for all the vars that are not defined in decls!
          forM_ (toListNameMap $ hoistFilterNameMap decls destMap) \(n, d) ->
            place d $ case s ! n of Rename v -> Var v; SubstVal a -> a

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
  Hof (For dir ixDict (Lam body)) -> traverseFor dest dir ixDict body
  _ -> do
    expr' <- traverseExprDefault expr
    case dest of
      Nothing -> return expr'
      Just d  -> do
        ans <- Var <$> emit expr'
        place d ans
        return $ Atom ans

place :: Emits o => Atom o -> Atom o -> LowerM i o ()
place d x = void $ emitOp $ Place d x
{-# INLINE place #-}

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
  VVal :: Stability -> Atom n -> VSubstValC AtomNameC n
type VAtom = VSubstValC AtomNameC
instance SinkableV VSubstValC
instance SinkableE (VSubstValC c) where
  sinkingProofE fresh (VVal s x) = VVal s $ sinkingProofE fresh x

instance PrettyPrec (VSubstValC c n) where
  prettyPrec (VVal s atom) = atPrec LowestPrec $ "@" <> viaShow s <+> pretty atom

type TopVectorizeM = BuilderT (ReaderT Word32 HardFailM)

vectorizeLoops :: EnvReader m => Word32 -> Block n -> m n (Block n)
vectorizeLoops vectorByteWidth (Block _ decls ans) = do
  liftM (runHardFail . (`runReaderT` vectorByteWidth)) $ liftBuilderT $ buildBlock $ do
    s <- vectorizeLoopsRec emptyInFrag decls
    applySubst s ans
{-# INLINE vectorizeLoops #-}

vectorizeLoopsRec :: (Ext i o, Emits o)
                  => SubstFrag Name i i' o -> Nest Decl i' i''
                  -> TopVectorizeM o (SubstFrag Name i i'' o)
vectorizeLoopsRec frag = \case
  Empty -> return frag
  Nest (Let b (DeclBinding ann _ expr)) rest -> do
    vectorByteWidth <- ask
    let narrowestTypeByteWidth = 1  -- TODO: This is too conservative! Find the shortest type in the loop.
    let loopWidth = vectorByteWidth `div` narrowestTypeByteWidth
    v <- case expr of
      Hof (Seq dir (DictCon (IxFin (IdxRepVal n))) dest (Lam body))
        | n `mod` loopWidth == 0 -> do
          Distinct <- getDistinct
          let vn = IdxRepVal $ n `div` loopWidth
          body' <- vectorizeSeq loopWidth (TC $ Fin vn) frag body
          dest' <- applySubst frag dest
          emit $ Hof $ Seq dir (DictCon $ IxFin vn) dest' body'
      _ -> emitDecl (getNameHint b) ann =<< applySubst frag expr
    vectorizeLoopsRec (frag <.> b @> v) rest

vectorizeSeq :: forall i i' o. (Distinct o, Ext i o)
             => Word32 -> Type o -> SubstFrag Name i i' o -> LamExpr i'
             -> TopVectorizeM o (Atom o)
vectorizeSeq loopWidth newIxTy frag (LamExpr (LamBinder b ty arr eff) body) = do
  case eff of
    Pure -> do
      ty' <- case ty of
        ProdTy [_, ref] -> do
          ref' <- applySubst frag ref
          return $ ProdTy [newIxTy, ref']
        _ -> error "Unexpected seq binder type"
      liftM (runHardFail . (`runReaderT` loopWidth)) $ liftBuilderT $ do
        buildLam (getNameHint b) arr (sink ty') Pure \ci -> do
          (vi, dest) <- fromPair $ Var ci
          viOrd <- emitOp $ CastOp IdxRepTy vi
          iOrd <- emitOp $ BinOp IMul viOrd (IdxRepVal loopWidth)
          i <- emitOp $ CastOp (sink newIxTy) iOrd
          let s = newSubst iSubst <>> b @> VVal (ProdStability [Contiguous, Uniform]) (PairVal i dest)
          runSubstReaderT s $ runVectorizeM $ vectorizeBlock body $> UnitVal
    _ -> error "Effectful loop vectorization not implemented!"
  where
    iSubst :: (DExt o o', Color c) => Name c i' -> VSubstValC c o'
    iSubst v = case lookupSubstFragProjected frag v of
      Left v'  -> sink $ fromNameVAtom v'
      Right v' -> sink $ fromNameVAtom v'

fromNameVAtom :: forall c n. Color c => Name c n -> VSubstValC c n
fromNameVAtom v = case eqColorRep @c @AtomNameC of
  Just ColorsEqual -> VVal Uniform $ Var v
  _ -> error "Unexpected non-atom name"

newtype VectorizeM i o a =
  VectorizeM { runVectorizeM :: SubstReaderT VSubstValC (BuilderT (ReaderT Word32 HardFailM)) i o a }
  deriving ( Functor, Applicative, Monad, Fallible, MonadFail, SubstReader VSubstValC
           , Builder, EnvReader, EnvExtender, ScopeReader, ScopableBuilder )

getLoopWidth :: VectorizeM i o Word32
getLoopWidth = VectorizeM $ SubstReaderT $ ReaderT $ const $ ask

vectorizeBlock :: Emits o => Block i -> VectorizeM i o (VAtom o)
vectorizeBlock (Block _ decls (ans :: Atom i')) = go decls
  where
    go :: Emits o => Nest Decl i i' -> VectorizeM i o (VAtom o)
    go = \case
      Empty -> vectorizeAtom ans
      Nest (Let b (DeclBinding ann _ expr)) rest -> do
        unless (ann == PlainLet) $ error "Encountered a non-plain let?"
        v <- vectorizeExpr expr
        extendSubst (b @> v) $ go rest

vectorizeExpr :: Emits o => Expr i -> VectorizeM i o (VAtom o)
vectorizeExpr expr = case expr of
  Atom atom -> vectorizeAtom atom
  Op op -> vectorizeOp op
  -- Vectorizing IO might not always be safe! Here, we depend on vectorizeOp
  -- being picky about the IO-inducing ops it supports, and expect it to
  -- complain about FFI calls and the like.
  Hof (RunIO (Lam (LamExpr (LamBinder b UnitTy PlainArrow _) body))) -> do
    -- TODO: buildBlockAux?
    (vy, lam') <- withFreshBinder (getNameHint b) UnitTy \b' -> do
      Abs decls (LiftE vy `PairE` yWithTy) <- buildScoped do
        VVal vy y <- extendSubst (b @> VVal Uniform UnitVal) $ vectorizeBlock body
        PairE (LiftE vy) <$> withType y
      body' <- absToBlock =<< computeAbsEffects (Abs decls yWithTy)
      effs' <- getEffects body'
      return (vy, LamExpr (LamBinder b' UnitTy PlainArrow effs') body')
    VVal vy . Var <$> emit (Hof (RunIO (Lam lam')))
  _ -> error $ "Cannot vectorize expr: " ++ pprint expr

vectorizeOp :: Emits o => Op i -> VectorizeM i o (VAtom o)
vectorizeOp op = do
  op' <- (inline traversePrimOp) vectorizeAtom op
  case op' of
    IndexRef (VVal Uniform ref) (VVal Contiguous i) -> do
      TC (RefType _ (TabTy tb a)) <- getType ref
      vty <- getVectorType $ case hoist tb a of
        HoistSuccess a' -> a'
        HoistFailure _  -> error "Can't vectorize dependent table application"
      VVal Contiguous <$> emitOp (VectorSubref ref i vty)
    Place (VVal vref ref) sval@(VVal vval val) -> do
      VVal Uniform <$> case (vref, vval) of
        (Uniform   , Uniform   ) -> emitOp $ Place ref val
        (Uniform   , _         ) -> error "Write conflict? This should never happen!"
        (Varying   , _         ) -> error "Vector scatter not implemented"
        (Contiguous, Varying   ) -> emitOp $ Place ref val
        (Contiguous, Contiguous) -> emitOp . Place ref =<< ensureVarying sval
        _ -> error "Not implemented yet"
    UnOp opk sx@(VVal vx x) -> do
      let v = case vx of Uniform -> Uniform; _ -> Varying
      x' <- if vx /= v then ensureVarying sx else return x
      VVal v <$> emitOp (UnOp opk x')
    BinOp opk sx@(VVal vx x) sy@(VVal vy y) -> do
      let v = case (vx, vy) of (Uniform, Uniform) -> Uniform; _ -> Varying
      x' <- if vx /= v then ensureVarying sx else return x
      y' <- if vy /= v then ensureVarying sy else return y
      VVal v <$> emitOp (BinOp opk x' y')
    CastOp (VVal Uniform ty) (VVal vx x) -> do
      ty' <- case vx of
        Uniform    -> return ty
        Varying    -> getVectorType ty
        Contiguous -> return ty
        ProdStability _ -> error "Unexpected cast of product type"
      VVal vx <$> emitOp (CastOp ty' x)
    PtrOffset (VVal Uniform ptr) (VVal Contiguous off) -> do
      VVal Contiguous <$> emitOp (PtrOffset ptr off)
    PtrLoad (VVal Contiguous ptr) -> do
      BaseTy (PtrType (addrSpace, a)) <- getType ptr
      BaseTy av <- getVectorType $ BaseTy a
      ptr' <- emitOp $ CastOp (BaseTy $ PtrType (addrSpace, av)) ptr
      VVal Varying <$> emitOp (PtrLoad ptr')
    _ -> error $ "Can't vectorize op: " ++ pprint op'

vectorizeAtom :: Atom i -> VectorizeM i o (VAtom o)
vectorizeAtom atom = case atom of
  Var v -> lookupSubstM v
  ProjectElt p v -> do
    VVal vv v' <- lookupSubstM v
    return $ VVal (projStability (reverse $ NE.toList p) vv) $ getProjection (NE.toList p) v'
  Con (Lit l) -> return $ VVal Uniform $ Con $ Lit l
  _ -> do
    subst <- getSubst
    VVal Uniform <$> fmapNamesM (uniformSubst subst) atom
  where
    uniformSubst :: Color c => Subst VSubstValC i o -> Name c i -> AtomSubstVal c o
    uniformSubst subst n = case subst ! n of
      VVal Uniform x -> SubstVal x
      _ -> error $ "Can't vectorize atom " ++ pprint atom
    projStability p s = case (p, s) of
      ([]  , _                ) -> s
      (i:is, ProdStability sbs) -> projStability is (sbs !! i)
      (_   , Uniform          ) -> s
      _ -> error "Invalid projection"

getVectorType :: Type o -> VectorizeM i o (Atom o)
getVectorType ty = case ty of
  BaseTy (Scalar sbt) -> do
    els <- getLoopWidth
    return $ BaseTy $ Vector [els] sbt
  -- TODO: Should we support tables?
  _ -> error $ "Can't make a vector of " ++ pprint ty

ensureVarying :: Emits o => VAtom o -> VectorizeM i o (Atom o)
ensureVarying (VVal s val) = case s of
  Varying -> return val
  Uniform -> do
    vty <- getVectorType =<< getType val
    emitOp $ VectorBroadcast val vty
  -- Note that the implementation of this case will depend on val's type.
  Contiguous -> do
    ty <- getType val
    vty <- getVectorType ty
    case ty of
      BaseTy (Scalar sbt) -> do
        bval <- emitOp $ VectorBroadcast val vty
        iota <- emitOp $ VectorIota vty
        emitOp $ BinOp (if isIntegral sbt then IAdd else FAdd) bval iota
      _ -> error "Not implemented"
  ProdStability _ -> error "Not implemented"

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
