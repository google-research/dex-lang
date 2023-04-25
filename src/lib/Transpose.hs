-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Transpose (transpose, transposeTopFun) where

import Data.Foldable
import Data.Functor
import Control.Category ((>>>))
import Control.Monad.Reader
import qualified Data.Set as S
import GHC.Stack

import Builder
import Core
import CheapReduction
import Err
import Imp
import IRVariants
import MTL1
import Name
import Subst
import QueryType
import Types.Core
import Types.Primitives
import Util (enumerate)

transpose
  :: (MonadFail1 m, Builder SimpIR m, Emits n)
  => LamExpr SimpIR n -> Atom SimpIR n -> m n (Atom SimpIR n)
transpose lam ct = liftEmitBuilder $ runTransposeM do
  UnaryLamExpr b body <- sinkM lam
  withAccumulator (binderType b) \refSubstVal ->
    extendSubst (b @> refSubstVal) $
      transposeBlock body (sink ct)
{-# SCC transpose #-}

runTransposeM :: TransposeM n n a -> BuilderM SimpIR n a
runTransposeM cont = runReaderT1 (ListE []) $ runSubstReaderT idSubst $ cont

transposeTopFun
  :: (MonadFail1 m, EnvReader m)
  => LamExpr SimpIR n -> m n (LamExpr SimpIR n)
transposeTopFun lam = liftBuilder $ runTransposeM do
  (Abs bsNonlin (Abs bLin body), Abs bsNonlin'' outTy)  <- unpackLinearLamExpr lam
  refreshBinders bsNonlin \bsNonlin' substFrag -> extendRenamer substFrag do
    outTy' <- applyRename (bsNonlin''@@> nestToNames bsNonlin') outTy
    withFreshBinder "ct" outTy' \bCT -> do
      let ct = Var $ binderName bCT
      body' <- buildBlock do
        inTy <- substNonlin $ binderType bLin
        withAccumulator inTy \refSubstVal ->
          extendSubst (bLin @> refSubstVal) $
            transposeBlock body (sink ct)
      return $ LamExpr (bsNonlin' >>> UnaryNest bCT) body'

unpackLinearLamExpr
  :: (MonadFail1 m, EnvReader m) => LamExpr SimpIR n
  -> m n ( Abs (Nest SBinder) (Abs SBinder SBlock) n
         , Abs (Nest SBinder) SType n)
unpackLinearLamExpr lam@(LamExpr bs body) = do
  let numNonlin = nestLength bs - 1
  PairB bsNonlin (UnaryNest bLin) <- return $ splitNestAt numNonlin bs
  PiType bsTy _ resultTy <- getLamExprType lam
  PairB bsNonlinTy (UnaryNest bLinTy) <- return $ splitNestAt numNonlin bsTy
  let resultTy' = ignoreHoistFailure $ hoist bLinTy resultTy
  return ( Abs bsNonlin $ Abs bLin body
         , Abs bsNonlinTy resultTy')

-- === transposition monad ===

data TransposeSubstVal c n where
  RenameNonlin :: Name c n -> TransposeSubstVal c n
  -- accumulator references corresponding to non-ref linear variables
  LinRef :: SAtom n -> TransposeSubstVal (AtomNameC SimpIR) n
  -- as an optimization, we don't make references for trivial vector spaces
  LinTrivial :: TransposeSubstVal (AtomNameC SimpIR) n

type LinRegions = ListE SAtomName

type TransposeM a = SubstReaderT TransposeSubstVal
                      (ReaderT1 LinRegions (BuilderM SimpIR)) a

type TransposeM' a = SubstReaderT AtomSubstVal
                       (ReaderT1 LinRegions (BuilderM SimpIR)) a

-- TODO: it might make sense to replace substNonlin/isLin
-- with a single `trySubtNonlin :: e i -> Maybe (e o)`.
-- But for that we need a way to traverse names, like a monadic
-- version of `substE`.
substNonlin :: (SinkableE e, RenameE e, HasCallStack) => e i -> TransposeM i o (e o)
substNonlin e = do
  subst <- getSubst
  fmapRenamingM (\v -> case subst ! v of
                         RenameNonlin v' -> v'
                         _ -> error "not a nonlinear expression") e

-- TODO: Can we generalize onNonLin to accept SubstReaderT Name instead of
-- SubstReaderT AtomSubstVal?  For that to work, we need another combinator,
-- that lifts a SubstReader AtomSubstVal into a SubstReader Name, because
-- effectsSubstE is currently typed as SubstReader AtomSubstVal.
-- Then we can presumably recode substNonlin as `onNonLin substM`.  We may
-- be able to do that anyway, except we will then need to restrict the type
-- of substNonlin to require `SubstE AtomSubstVal e`; but that may be fine.
onNonLin :: HasCallStack
         => TransposeM' i o a -> TransposeM i o a
onNonLin cont = do
  subst <- getSubst
  let subst' = newSubst (\v -> case subst ! v of
                                 RenameNonlin v' -> Rename v'
                                 _ -> error "not a nonlinear expression")
  liftSubstReaderT $ runSubstReaderT subst' cont

isLin :: HoistableE e => e i -> TransposeM i o Bool
isLin e = do
  substVals <- mapM lookupSubstM $ freeAtomVarsList @SimpIR e
  return $ flip any substVals \case
    LinTrivial     -> True
    LinRef _       -> True
    RenameNonlin _ -> False

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
                   cont (LinRef $ Var ref) >> return UnitVal
    Just val -> do
      -- If the accumulator's type is inhabited by just one value, we
      -- don't need any actual accumulation, and can just return that
      -- value.  (We still run `cont` because it may emit decls that
      -- have effects.)
      Distinct <- getDistinct
      cont LinTrivial >> return val

emitCTToRef :: (Emits n, Builder SimpIR m) => SAtom n -> SAtom n -> m n ()
emitCTToRef ref ct = do
  baseMonoid <- getType ct >>= tangentBaseMonoidFor
  void $ emitOp $ RefOp ref $ MExtend baseMonoid ct

getLinRegions :: TransposeM i o [SAtomName o]
getLinRegions = asks fromListE

extendLinRegions :: SAtomName o -> TransposeM i o a -> TransposeM i o a
extendLinRegions v cont = local (\(ListE vs) -> ListE (v:vs)) cont

-- === actual pass ===

transposeBlock :: Emits o => SBlock i -> SAtom o -> TransposeM i o ()
transposeBlock (Block _ decls result) ct = transposeWithDecls decls result ct

transposeWithDecls :: Emits o => Nest SDecl i i' -> SAtom i' -> SAtom o -> TransposeM i o ()
transposeWithDecls Empty atom ct = transposeAtom atom ct
transposeWithDecls (Nest (Let b (DeclBinding _ ty expr)) rest) result ct =
  substExprIfNonlin expr >>= \case
    Nothing  -> do
      ty' <- substNonlin ty
      ctExpr <- withAccumulator ty' \refSubstVal ->
                  extendSubst (b @> refSubstVal) $
                    transposeWithDecls rest result (sink ct)
      transposeExpr expr ctExpr
    Just nonlinExpr -> do
      v <- emit nonlinExpr
      extendSubst (b @> RenameNonlin v) $
        transposeWithDecls rest result ct

substExprIfNonlin :: SExpr i -> TransposeM i o (Maybe (SExpr o))
substExprIfNonlin expr =
  isLin expr >>= \case
    True -> return Nothing
    False -> do
      onNonLin (getEffectsSubst expr) >>= isLinEff >>= \case
        True -> return Nothing
        False -> Just <$> substNonlin expr

isLinEff :: EffectRow SimpIR o -> TransposeM i o Bool
isLinEff effs@(EffectRow _ NoTail) = do
  regions <- getLinRegions
  let effRegions = freeAtomVarsList effs
  return $ not $ null $ S.fromList effRegions `S.intersection` S.fromList regions

getTransposedTopFun :: EnvReader m => TopFunName n ->  m n (Maybe (TopFunName n))
getTransposedTopFun f = do
  cache <- transpositionCache <$> getCache
  return $ lookupEMap cache f

transposeExpr :: Emits o => SExpr i -> SAtom o -> TransposeM i o ()
transposeExpr expr ct = case expr of
  Atom atom -> transposeAtom atom ct
  TopApp f xs -> do
    Just fT <- getTransposedTopFun =<< substNonlin f
    (xsNonlin, [xLin]) <- return $ splitAt (length xs - 1) xs
    xsNonlin' <- mapM substNonlin xsNonlin
    ct' <- naryTopApp fT (xsNonlin' ++ [ct])
    transposeAtom xLin ct'
  -- TODO: Instead, should we handle table application like nonlinear
  -- expressions, where we just project the reference?
  TabApp x is -> do
    is' <- mapM substNonlin is
    case x of
      Var v -> do
        lookupSubstM v >>= \case
          RenameNonlin _ -> error "shouldn't happen"
          LinRef ref -> do
            refProj <- naryIndexRef ref (toList is')
            emitCTToRef refProj ct
          LinTrivial -> return ()
      ProjectElt i' x' -> do
        let (idxs, v) = asNaryProj i' x'
        lookupSubstM v >>= \case
          RenameNonlin _ -> error "an error, probably"
          LinRef ref -> do
            ref' <- getNaryProjRef (toList idxs) ref
            refProj <- naryIndexRef ref' (toList is')
            emitCTToRef refProj ct
          LinTrivial -> return ()
      _ -> error $ "shouldn't occur: " ++ pprint x
  PrimOp op -> transposeOp op ct
  Case e alts _ _ -> do
    linearScrutinee <- isLin e
    case linearScrutinee of
      True  -> notImplemented
      False -> do
        e' <- substNonlin e
        void $ buildCase e' UnitTy \i v -> do
          v' <- emit (Atom v)
          Abs b body <- return $ alts !! i
          extendSubst (b @> RenameNonlin v') do
            transposeBlock body (sink ct)
          return UnitVal
  TabCon _ ty es -> do
    TabTy b _ <- return ty
    idxTy <- substNonlin $ binderAnn b
    forM_ (enumerate es) \(ordinalIdx, e) -> do
      i <- unsafeFromOrdinal idxTy (IdxRepVal $ fromIntegral ordinalIdx)
      tabApp ct i >>= transposeAtom e

transposeOp :: Emits o => PrimOp SimpIR i -> SAtom o -> TransposeM i o ()
transposeOp op ct = case op of
  DAMOp _        -> error "unreachable" -- TODO: rule out statically
  RefOp refArg m   -> do
    refArg' <- substNonlin refArg
    let emitEff = emitOp . RefOp refArg'
    case m of
      MAsk -> do
        baseMonoid <- getType ct >>= tangentBaseMonoidFor
        void $ emitEff $ MExtend baseMonoid ct
      -- XXX: This assumes that the update function uses a tangent (0, +) monoid
      --      rule for RunWriter.
      MExtend _ x -> transposeAtom x =<< emitEff MAsk
      MGet -> void $ emitEff . MPut =<< addTangent ct =<< emitEff MGet
      MPut x -> do
        ct' <- emitEff MGet
        transposeAtom x ct'
        zero <- getType ct' >>= zeroAt
        void $ emitEff $ MPut zero
      IndexRef _ -> notImplemented
      ProjRef _  -> notImplemented
  Hof hof       -> transposeHof hof ct
  MiscOp miscOp   -> transposeMiscOp miscOp ct
  UnOp  FNeg x    -> transposeAtom x =<< neg ct
  UnOp  _    _    -> notLinear
  BinOp FAdd x y  -> transposeAtom x ct >> transposeAtom y ct
  BinOp FSub x y  -> transposeAtom x ct >> (transposeAtom y =<< neg ct)
  BinOp FMul x y  -> do
    xLin <- isLin x
    if xLin
      then transposeAtom x =<< mul ct =<< substNonlin y
      else transposeAtom y =<< mul ct =<< substNonlin x
  BinOp FDiv x y  -> transposeAtom x =<< div' ct =<< substNonlin y
  BinOp _    _ _  -> notLinear
  MemOp _               -> notLinear
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
  ShowAny _ -> error "Shouldn't have ShowAny in simplified IR"
  ShowScalar _ -> error "Shouldn't have ShowScalar in simplified IR"
  where
    notLinear = error $ "Can't transpose a non-linear operation: " ++ show op

transposeAtom :: HasCallStack => Emits o => SAtom i -> SAtom o -> TransposeM i o ()
transposeAtom atom ct = case atom of
  Var v -> do
    lookupSubstM v >>= \case
      RenameNonlin _ ->
        -- XXX: we seem to need this case, but it feels like it should be an error!
        return ()
      LinRef ref -> emitCTToRef ref ct
      LinTrivial -> return ()
  Con con         -> transposeCon con ct
  DepPair _ _ _   -> notImplemented
  PtrVar _        -> notTangent
  ProjectElt i' x' -> do
    let (idxs, v) = asNaryProj i' x'
    lookupSubstM v >>= \case
      RenameNonlin _ -> error "an error, probably"
      LinRef ref -> do
        ref' <- getNaryProjRef (toList idxs) ref
        emitCTToRef ref' ct
      LinTrivial -> return ()
  RepValAtom _ -> error "not implemented"
  where notTangent = error $ "Not a tangent atom: " ++ pprint atom

transposeHof :: Emits o => Hof SimpIR i -> SAtom o -> TransposeM i o ()
transposeHof hof ct = case hof of
  For ann d lam -> do
    UnaryLamExpr b  body <- return lam
    ixTy <- ixTyFromDict =<< substNonlin d
    void $ buildForAnn (getNameHint b) (flipDir ann) ixTy \i -> do
      ctElt <- tabApp (sink ct) (Var i)
      extendSubst (b@>RenameNonlin i) $ transposeBlock body ctElt
      return UnitVal
  RunState Nothing s (BinaryLamExpr hB refB body) -> do
    (ctBody, ctState) <- fromPair ct
    (_, cts) <- (fromPair =<<) $ emitRunState noHint ctState \h ref -> do
      extendSubst (hB@>RenameNonlin h) $ extendSubst (refB@>RenameNonlin ref) $
        extendLinRegions h $
          transposeBlock body (sink ctBody)
      return UnitVal
    transposeAtom s cts
  RunReader r (BinaryLamExpr hB refB body) -> do
    accumTy <- getReferentTy =<< substNonlin (EmptyAbs $ PairB hB refB)
    baseMonoid <- tangentBaseMonoidFor accumTy
    (_, ct') <- (fromPair =<<) $ emitRunWriter noHint accumTy baseMonoid \h ref -> do
      extendSubst (hB@>RenameNonlin h) $ extendSubst (refB@>RenameNonlin ref) $
        extendLinRegions h $
          transposeBlock body (sink ct)
      return UnitVal
    transposeAtom r ct'
  RunWriter Nothing _ (BinaryLamExpr hB refB body)-> do
    -- TODO: check we have the 0/+ monoid
    (ctBody, ctEff) <- fromPair ct
    void $ emitRunReader noHint ctEff \h ref -> do
      extendSubst (hB@>RenameNonlin h) $ extendSubst (refB@>RenameNonlin ref) $
        extendLinRegions h $
          transposeBlock body (sink ctBody)
      return UnitVal
  _ -> notImplemented

transposeCon :: Emits o => Con SimpIR i -> SAtom o -> TransposeM i o ()
transposeCon con ct = case con of
  Lit _             -> return ()
  ProdCon []        -> return ()
  ProdCon xs ->
    forM_ (enumerate xs) \(i, x) ->
      getProj i ct >>= transposeAtom x
  SumCon _ _ _      -> notImplemented
  HeapVal -> notTangent
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
