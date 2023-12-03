-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Transpose (transpose, transposeTopFun) where

import Data.Foldable
import Data.Functor
import Control.Category ((>>>))
import GHC.Stack

import Builder
import Core
import Imp
import IRVariants
import Name
import PPrint
import Subst
import QueryType
import Types.Core
import Types.Top
import Types.Primitives
import Util (enumerate)

transpose
  :: (MonadFail1 m, Builder SimpIR m, Emits n)
  => LamExpr SimpIR n -> Atom SimpIR n -> m n (Atom SimpIR n)
transpose lam ct = liftEmitBuilder $ runTransposeM do
  UnaryLamExpr b body <- sinkM lam
  withAccumulator (binderType b) \refSubstVal ->
    extendSubst (b @> refSubstVal) $
      transposeExpr body (sink ct)
{-# SCC transpose #-}

runTransposeM :: TransposeM n n a -> BuilderM SimpIR n a
runTransposeM cont = runSubstReaderT idSubst $ cont

transposeTopFun :: (MonadFail1 m, EnvReader m) => STopLam n -> m n (STopLam n)
transposeTopFun (TopLam False _ lam) = liftBuilder $ runTransposeM do
  (Abs bsNonlin (Abs bLin body), Abs bsNonlin'' outTy)  <- unpackLinearLamExpr lam
  refreshBinders bsNonlin \bsNonlin' substFrag -> extendRenamer substFrag do
    outTy' <- applyRename (bsNonlin''@@> nestToNames bsNonlin') outTy
    withFreshBinder "ct" outTy' \bCT -> do
      let ct = toAtom $ binderVar bCT
      body' <- buildBlock do
        inTy <- substNonlin $ binderType bLin
        withAccumulator inTy \refSubstVal ->
          extendSubst (bLin @> refSubstVal) $
            transposeExpr body (sink ct)
      let piTy = PiType  (bsNonlin' >>> UnaryNest bCT) (EffTy Pure (getType body'))
      let lamT = LamExpr (bsNonlin' >>> UnaryNest bCT) body'
      return $ TopLam False piTy lamT
transposeTopFun (TopLam True _ _) = error "shouldn't be transposing in destination passing style"

unpackLinearLamExpr
  :: (MonadFail1 m, EnvReader m) => LamExpr SimpIR n
  -> m n ( Abs (Nest SBinder) (Abs SBinder SExpr) n
         , Abs (Nest SBinder) SType n)
unpackLinearLamExpr lam@(LamExpr bs body) = do
  let numNonlin = nestLength bs - 1
  PairB bsNonlin (UnaryNest bLin) <- return $ splitNestAt numNonlin bs
  PiType bsTy (EffTy _ resultTy) <- getLamExprType lam
  PairB bsNonlinTy (UnaryNest bLinTy) <- return $ splitNestAt numNonlin bsTy
  let resultTy' = ignoreHoistFailure $ hoist bLinTy resultTy
  return ( Abs bsNonlin $ Abs bLin body
         , Abs bsNonlinTy resultTy')

-- === transposition monad ===

type AtomTransposeSubstVal = TransposeSubstVal (AtomNameC SimpIR)
data TransposeSubstVal c n where
  RenameNonlin :: Name c n -> TransposeSubstVal c n
  -- accumulator references corresponding to non-ref linear variables
  LinRef :: SAtom n -> AtomTransposeSubstVal n
  -- as an optimization, we don't make references for trivial vector spaces
  LinTrivial :: AtomTransposeSubstVal n

type TransposeM a = SubstReaderT TransposeSubstVal (BuilderM SimpIR) a

substNonlin :: (PrettyE e, SinkableE e, RenameE e, HasCallStack) => e i -> TransposeM i o (e o)
substNonlin e = do
  subst <- getSubst
  fmapRenamingM (\v -> case subst ! v of
                         RenameNonlin v' -> v'
                         _ -> error $ "not a nonlinear expression: " ++ pprint e) e

withAccumulator
  :: Emits o
  => SType o
  -> (forall o'. (Emits o', DExt o o') => TransposeSubstVal (AtomNameC SimpIR) o' -> TransposeM i o' ())
  -> TransposeM i o (SAtom o)
withAccumulator ty cont = do
  singletonTypeVal ty >>= \case
    Nothing -> do
      baseMonoid <- tangentBaseMonoidFor ty
      getSnd =<< emitRunWriter noHint ty baseMonoid \_ ref ->
                   cont (LinRef $ toAtom ref) >> return UnitVal
    Just val -> do
      -- If the accumulator's type is inhabited by just one value, we
      -- don't need any actual accumulation, and can just return that
      -- value.  (We still run `cont` because it may emit decls that
      -- have effects.)
      Distinct <- getDistinct
      cont LinTrivial >> return val

emitCTToRef :: (Emits n, Builder SimpIR m) => SAtom n -> SAtom n -> m n ()
emitCTToRef ref ct = do
  baseMonoid <- tangentBaseMonoidFor (getType ct)
  void $ emitLin $ RefOp ref $ MExtend baseMonoid ct

-- === actual pass ===

transposeWithDecls :: forall i i' o. Emits o => Nest SDecl i i' -> SExpr i' -> SAtom o -> TransposeM i o ()
transposeWithDecls Empty atom ct = transposeExpr atom ct
transposeWithDecls (Nest (Let b (DeclBinding ann expr)) rest) result ct = case ann of
  LinearLet -> do
    ty' <- substNonlin $ getType expr
    case expr of
      Project _ i x -> do
        continue =<< projectLinearRef x \ref -> emitLin =<< mkProjRef ref (ProjectProduct i)
      TabApp _ x i -> do
        continue =<< projectLinearRef x \ref -> do
          i' <- substNonlin i
          emitLin =<< mkIndexRef ref i'
      _ -> do
        ctExpr <- withAccumulator ty' \refSubstVal -> continue refSubstVal
        transposeExpr expr ctExpr
  _ -> do
    v <- substNonlin expr >>= emitToVar
    continue $ RenameNonlin (atomVarName v)
  where
    continue :: forall o'. (Emits o', Ext o o') => AtomTransposeSubstVal o' -> TransposeM i o' ()
    continue substVal = do
      ct' <- sinkM ct
      extendSubst (b @> substVal) $ transposeWithDecls rest result ct'

projectLinearRef
  :: Emits o
  => SAtom i -> (SAtom o -> TransposeM i o (SAtom o))
  -> TransposeM i o (AtomTransposeSubstVal o)
projectLinearRef x f = do
  Stuck _ (Var v) <- return x
  lookupSubstM (atomVarName v) >>= \case
    RenameNonlin _ -> error "nonlinear"
    LinRef ref -> LinRef <$> f ref
    LinTrivial -> return LinTrivial

getTransposedTopFun :: EnvReader m => TopFunName n ->  m n (Maybe (TopFunName n))
getTransposedTopFun f = do
  cache <- transpositionCache <$> getCache
  return $ lookupEMap cache f

transposeExpr :: Emits o => SExpr i -> SAtom o -> TransposeM i o ()
transposeExpr expr ct = case expr of
  Block _ (Abs decls result) -> transposeWithDecls decls result ct
  Atom atom -> transposeAtom atom ct
  TopApp _ f xs -> do
    Just fT <- getTransposedTopFun =<< substNonlin f
    (xsNonlin, [xLin]) <- return $ splitAt (length xs - 1) xs
    xsNonlin' <- mapM substNonlin xsNonlin
    ct' <- naryTopApp fT (xsNonlin' ++ [ct])
    transposeAtom xLin ct'
  PrimOp op -> transposeOp op ct
  Case e alts _ -> do
    e' <- substNonlin e
    void $ buildCase e' UnitTy \i v -> do
      v' <- emitToVar v
      Abs b body <- return $ alts !! i
      extendSubst (b @> RenameNonlin (atomVarName v')) do
        transposeExpr body (sink ct)
      return UnitVal
  TabCon _ ty es -> do
    TabTy d b _ <- return ty
    idxTy <- substNonlin $ IxType (binderType b) d
    forM_ (enumerate es) \(ordinalIdx, e) -> do
      i <- unsafeFromOrdinal idxTy (IdxRepVal $ fromIntegral ordinalIdx)
      tabApp ct i >>= transposeAtom e
  TabApp _ _ _  -> error "should have been handled by reference projection"
  Project _ _ _ -> error "should have been handled by reference projection"

transposeOp :: Emits o => PrimOp SimpIR i -> SAtom o -> TransposeM i o ()
transposeOp op ct = case op of
  DAMOp _        -> error "unreachable" -- TODO: rule out statically
  RefOp refArg m   -> do
    refArg' <- substNonlin refArg
    let emitEff = emitLin . RefOp refArg'
    case m of
      MAsk -> do
        baseMonoid <- tangentBaseMonoidFor (getType ct)
        void $ emitEff $ MExtend baseMonoid ct
      -- XXX: This assumes that the update function uses a tangent (0, +) monoid
      --      rule for RunWriter.
      MExtend _ x -> transposeAtom x =<< emitEff MAsk
      MGet -> void $ emitEff . MPut =<< addTangent ct =<< emitEff MGet
      MPut x -> do
        ct' <- emitEff MGet
        transposeAtom x ct'
        zero <- zeroAt $ getType ct'
        void $ emitEff $ MPut zero
      IndexRef _ _ -> notImplemented
      ProjRef _ _  -> notImplemented
  Hof (TypedHof _ hof) -> transposeHof hof ct
  MiscOp miscOp   -> transposeMiscOp miscOp ct
  UnOp  FNeg x    -> transposeAtom x =<< (emitLin $ UnOp FNeg ct)
  UnOp  _    _    -> notLinear
  BinOp FAdd x y  -> transposeAtom x ct >> transposeAtom y ct
  BinOp FSub x y  -> transposeAtom x ct >> (transposeAtom y =<< (emitLin $ UnOp FNeg ct))
  -- XXX: linear argument to FMul is always first
  BinOp FMul x y  -> do
    y' <- substNonlin y
    tx <- emitLin $ BinOp FMul ct y'
    transposeAtom x tx
  BinOp FDiv x y  -> do
    y' <- substNonlin y
    tx <- emitLin $ BinOp FDiv ct y'
    transposeAtom x tx
  BinOp _    _ _  -> notLinear
  MemOp _         -> notLinear
  VectorOp _ -> unreachable
  where
    notLinear = error $ "Can't transpose a non-linear operation: " ++ pprint op
    unreachable = error $ "Shouldn't appear in transposition: " ++ pprint op

transposeMiscOp :: Emits o => MiscOp SimpIR i -> SAtom o -> TransposeM i o ()
transposeMiscOp op _ = case op of
  ThrowError   _        -> notLinear
  SumTag _              -> notLinear
  ToEnum _ _            -> notLinear
  ThrowException _      -> notLinear
  OutputStream          -> notLinear
  Select       _ _ _    -> notImplemented
  CastOp       _ _      -> notImplemented
  BitcastOp    _ _      -> notImplemented
  UnsafeCoerce _ _      -> notImplemented
  GarbageVal _          -> notImplemented
  ShowAny _    -> notLinear
  ShowScalar _ -> notLinear
  where notLinear = error $ "Can't transpose a non-linear operation: " ++ show op

transposeAtom :: HasCallStack => Emits o => SAtom i -> SAtom o -> TransposeM i o ()
transposeAtom atom ct = case atom of
  Con con -> transposeCon con ct
  Stuck _ stuck -> case stuck of
    PtrVar _ _      -> notTangent
    Var v -> do
      lookupSubstM (atomVarName v) >>= \case
        RenameNonlin _ -> error "nonlinear"
        LinRef ref -> emitCTToRef ref ct
        LinTrivial -> return ()
    StuckProject _ _ -> error "not linear"
    StuckTabApp  _ _ -> error "not linear"
    RepValAtom   _   -> error "not linear"
  where notTangent = error $ "Not a tangent atom: " ++ pprint atom

transposeHof :: Emits o => Hof SimpIR i -> SAtom o -> TransposeM i o ()
transposeHof hof ct = case hof of
  For ann ixTy' lam -> do
    UnaryLamExpr b  body <- return lam
    ixTy <- substNonlin ixTy'
    void $ emitLin =<< mkFor (getNameHint b) (flipDir ann) ixTy \i -> do
      ctElt <- tabApp (sink ct) (toAtom i)
      extendSubst (b@>RenameNonlin (atomVarName i)) $ transposeExpr body ctElt
      return UnitVal
  RunState Nothing s (BinaryLamExpr hB refB body) -> do
    (ctBody, ctState) <- fromPair ct
    (_, cts) <- (fromPair =<<) $ emitRunState noHint ctState \h ref -> do
      extendSubst (hB@>RenameNonlin (atomVarName h)) $ extendSubst (refB@>RenameNonlin (atomVarName ref)) $
         transposeExpr body (sink ctBody)
      return UnitVal
    transposeAtom s cts
  RunReader r (BinaryLamExpr hB refB body) -> do
    accumTy <- substNonlin $ getType r
    baseMonoid <- tangentBaseMonoidFor accumTy
    (_, ct') <- (fromPair =<<) $ emitRunWriter noHint accumTy baseMonoid \h ref -> do
      extendSubst (hB@>RenameNonlin (atomVarName h)) $ extendSubst (refB@>RenameNonlin (atomVarName ref)) $
        transposeExpr body (sink ct)
      return UnitVal
    transposeAtom r ct'
  RunWriter Nothing _ (BinaryLamExpr hB refB body)-> do
    -- TODO: check we have the 0/+ monoid
    (ctBody, ctEff) <- fromPair ct
    void $ emitRunReader noHint ctEff \h ref -> do
      extendSubst (hB@>RenameNonlin (atomVarName h)) $ extendSubst (refB@>RenameNonlin (atomVarName ref)) $
        transposeExpr body (sink ctBody)
      return UnitVal
  _ -> notImplemented

transposeCon :: Emits o => Con SimpIR i -> SAtom o -> TransposeM i o ()
transposeCon con ct = case con of
  Lit _             -> return ()
  ProdCon []        -> return ()
  ProdCon xs -> forM_ (enumerate xs) \(i, x) -> proj i ct >>= transposeAtom x
  SumCon _ _ _      -> notImplemented
  HeapVal -> notTangent
  DepPair _ _ _   -> notImplemented
  where notTangent = error $ "Not a tangent atom: " ++ pprint (Con con)

notImplemented :: HasCallStack => a
notImplemented = error "Not implemented"

flipDir :: ForAnn -> ForAnn
flipDir ann = case ann of
  Fwd -> Rev
  Rev -> Fwd

-- === instances ===

instance GenericE (TransposeSubstVal c) where
  type RepE (TransposeSubstVal c) = EitherE3 (Name c) SAtom UnitE
  fromE = error "todo"
  toE   = error "todo"

instance SinkableE (TransposeSubstVal c)
instance SinkableV TransposeSubstVal

instance FromName TransposeSubstVal where
  fromName v = RenameNonlin v
