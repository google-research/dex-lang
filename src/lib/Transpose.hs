-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE TypeFamilies #-}

module Transpose (transpose) where

import Data.Foldable
import Control.Monad
import Control.Monad.Reader
import qualified Data.Set as S

import MTL1
import Type
import Err
import Name
import Syntax
import Builder
import Util (zipWithT, enumerate)
import GHC.Stack

transpose :: (MonadFail1 m, EnvReader m) => Atom n -> m n (Atom n)
transpose lam = liftBuilder do
  lam'@(Lam (LamExpr b body)) <- sinkM lam
  Pi (PiType piBinder _ resultTy) <- getType lam'
  let argTy = binderType b
  let resultTy' = ignoreHoistFailure $ hoist piBinder resultTy
  runReaderT1 (ListE []) $ runSubstReaderT idSubst $
    buildLam "ct" LinArrow resultTy' Pure \ct ->
      withAccumulator (sink argTy) \ref ->
        extendSubst (b @> LinRef ref) $
          transposeBlock body (sink $ Var ct)

-- === transposition monad ===

data TransposeSubstVal c n where
  RenameNonlin :: Name c n -> TransposeSubstVal c n
  -- accumulator references corresponding to non-ref linear variables
  LinRef :: Atom n -> TransposeSubstVal AtomNameC n
  -- as an optimization, we don't make references for trivial vector spaces
  LinTrivial :: TransposeSubstVal AtomNameC n

type LinRegions = ListE AtomName

type TransposeM a = SubstReaderT TransposeSubstVal
                      (ReaderT1 LinRegions BuilderM) a

-- TODO: it might make sense to replace substNonlin/isLin
-- with a single `trySubtNonlin :: e i -> Maybe (e o)`.
-- But for that we need a way to traverse names, like a monadic
-- version of `substE`.
substNonlin :: (SinkableE e, SubstE Name e, HasCallStack)
            => e i -> TransposeM i o (e o)
substNonlin e = do
  subst <- getSubst
  fmapNamesM (\v -> case subst ! v of
                      RenameNonlin v' -> v'
                      _ -> error "not a nonlinear expression") e

isLin :: HoistableE e => e i -> TransposeM i o Bool
isLin e = do
  substVals <- mapM lookupSubstM $ freeAtomVarsList e
  return $ flip any substVals \case
    LinTrivial     -> True
    LinRef _       -> True
    RenameNonlin _ -> False

withAccumulator
  :: Emits o
  => Type o
  -> (forall o'. (Emits o', DExt o o') => Atom o' -> TransposeM i o' ())
  -> TransposeM i o (Atom o)
withAccumulator ty cont = do
  baseMonoid <- getBaseMonoidType ty >>= tangentBaseMonoidFor
  getSnd =<< emitRunWriter "ref" ty baseMonoid \_ ref ->
               cont (Var ref) >> return UnitVal

emitCTToRef :: (Emits n, Builder m) => Atom n -> Atom n -> m n ()
emitCTToRef ref ct = do
  baseMonoid <- getType ct >>= getBaseMonoidType >>= tangentBaseMonoidFor
  void $ emitOp $ PrimEffect ref $ MExtend baseMonoid ct

getLinRegions :: TransposeM i o [AtomName o]
getLinRegions = asks fromListE

extendLinRegions :: AtomName o -> TransposeM i o a -> TransposeM i o a
extendLinRegions v cont = local (\(ListE vs) -> ListE (v:vs)) cont

-- === actual pass ===

transposeBlock :: Emits o => Block i -> Atom o -> TransposeM i o ()
transposeBlock (Block _ decls result) ct = transposeWithDecls decls result ct

transposeWithDecls :: Emits o => Nest Decl i i' -> Expr i' -> Atom o -> TransposeM i o ()
transposeWithDecls Empty expr ct = transposeExpr expr ct
transposeWithDecls (Nest (Let b (DeclBinding _ ty expr)) rest) result ct =
  substExprIfNonlin expr >>= \case
    Nothing  -> do
      ty' <- substNonlin ty
      ctExpr <- withAccumulator ty' \ref ->
                  extendSubst (b @> LinRef ref) $
                    transposeWithDecls rest result (sink ct)
      transposeExpr expr ctExpr
    Just nonlinExpr -> do
      v <- emit nonlinExpr
      extendSubst (b @> RenameNonlin v) $
        transposeWithDecls rest result ct

substExprIfNonlin :: Expr i -> TransposeM i o (Maybe (Expr o))
substExprIfNonlin expr =
  isLin expr >>= \case
    True -> return Nothing
    False -> do
      expr' <- substNonlin expr
      exprEffects expr' >>= isLinEff >>= \case
        True -> return Nothing
        False -> return $ Just expr'

isLinEff :: EffectRow o -> TransposeM i o Bool
isLinEff effs@(EffectRow _ Nothing) = do
  regions <- getLinRegions
  let effRegions = freeAtomVarsList effs
  return $ not $ null $ S.fromList effRegions `S.intersection` S.fromList regions
isLinEff _ = error "Can't transpose polymorphic effects"

transposeExpr :: Emits o => Expr i -> Atom o -> TransposeM i o ()
transposeExpr expr ct = case expr of
  Atom atom     -> transposeAtom atom ct
  -- TODO: Instead, should we handle table application like nonlinear
  -- expressions, where we just project the reference?
  App x is -> do
    -- TODO: we should check that it's a table type here, but it's awkward to do
    -- because we need something in the o-space to do that.
    is' <- mapM substNonlin is
    case x of
      Var v -> do
        lookupSubstM v >>= \case
          RenameNonlin _ -> error "shouldn't happen"
          LinRef ref -> do
            refProj <- naryIndexRef ref (toList is')
            emitCTToRef refProj ct
          LinTrivial -> return ()
      ProjectElt idxs v -> do
        lookupSubstM v >>= \case
          RenameNonlin _ -> error "an error, probably"
          LinRef ref -> do
            ref' <- getNaryProjRef (toList idxs) ref
            refProj <- naryIndexRef ref' (toList is')
            emitCTToRef refProj ct
          LinTrivial -> return ()
      _ -> error $ "shouldn't occur: " ++ pprint x
  Op op         -> transposeOp op ct
  Hof hof       -> transposeHof hof ct
  Case e alts _ _ -> do
    linearScrutinee <- isLin e
    case linearScrutinee of
      True  -> notImplemented
      False -> do
        e' <- substNonlin e
        void $ buildCase e' UnitTy \i vs -> do
          Abs bs body <- return $ alts !! i
          extendSubst (bs @@> map RenameNonlin vs) do
            transposeBlock body (sink ct)
          return UnitVal

transposeOp :: Emits o => Op i -> Atom o -> TransposeM i o ()
transposeOp op ct = case op of
  ScalarUnOp  FNeg x    -> transposeAtom x =<< neg ct
  ScalarUnOp  _    _    -> notLinear
  ScalarBinOp FAdd x y  -> transposeAtom x ct >> transposeAtom y ct
  ScalarBinOp FSub x y  -> transposeAtom x ct >> (transposeAtom y =<< neg ct)
  ScalarBinOp FMul x y  -> do
    xLin <- isLin x
    if xLin
      then transposeAtom x =<< mul ct =<< substNonlin y
      else transposeAtom y =<< mul ct =<< substNonlin x
  ScalarBinOp FDiv x y  -> transposeAtom x =<< div' ct =<< substNonlin y
  ScalarBinOp _    _ _  -> notLinear
  PrimEffect refArg m   -> do
    refArg' <- substNonlin refArg
    let emitEff = emitOp . PrimEffect refArg'
    case m of
      MAsk -> do
        baseMonoid <- getType ct >>= getBaseMonoidType >>= tangentBaseMonoidFor
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
  TabCon ty es -> do
    TabTy b _ <- return ty
    idxTy <- substNonlin $ binderType b
    forM_ (enumerate es) \(ordinalIdx, e) -> do
      i <- intToIndex idxTy (IdxRepVal $ fromIntegral ordinalIdx)
      app ct i >>= transposeAtom e
  IndexRef     _ _      -> notImplemented
  ProjRef      _ _      -> notImplemented
  Select       _ _ _    -> notImplemented
  VectorBinOp  _ _ _    -> notImplemented
  VectorPack   _        -> notImplemented
  VectorIndex  _ _      -> notImplemented
  CastOp       _ _      -> notImplemented
  RecordCons   _ _      -> notImplemented
  RecordConsDynamic _ _ _ -> notImplemented
  RecordSplitDynamic _ _  -> notImplemented
  RecordSplit  _ _      -> notImplemented
  VariantLift  _ _      -> notImplemented
  VariantSplit _ _      -> notImplemented
  SumToVariant _        -> notImplemented
  PtrStore _ _          -> notLinear
  PtrLoad    _          -> notLinear
  PtrOffset _ _         -> notLinear
  IOAlloc _ _           -> notLinear
  IOFree _              -> notLinear
  Inject       _        -> notLinear
  SliceOffset  _ _      -> notLinear
  SliceCurry   _ _      -> notLinear
  UnsafeFromOrdinal _ _ -> notLinear
  ToOrdinal    _        -> notLinear
  IdxSetSize   _        -> notLinear
  ThrowError   _        -> notLinear
  DataConTag _          -> notLinear
  ToEnum _ _            -> notLinear
  ThrowException _      -> notLinear
  OutputStreamPtr       -> notLinear
  SynthesizeDict _ _    -> notLinear
  where notLinear = error $ "Can't transpose a non-linear operation: " ++ pprint op

transposeAtom :: HasCallStack => Emits o => Atom i -> Atom o -> TransposeM i o ()
transposeAtom atom ct = case atom of
  Var v -> do
    lookupSubstM v >>= \case
      RenameNonlin _ ->
        -- XXX: we seem to need this case, but it feels like it should be an error!
        return ()
      LinRef ref -> emitCTToRef ref ct
      LinTrivial -> return ()
  Con con         -> transposeCon con ct
  Record e        -> void $ zipWithT transposeAtom e =<< getUnpacked ct
  DepPair _ _ _   -> notImplemented
  DataCon _ _ _ _ e -> void $ zipWithT transposeAtom e =<< getUnpacked ct
  Variant _ _ _ _ -> notImplemented
  TabVal b body   -> do
    ty <- substNonlin $ binderType b
    void $ buildFor "i" Fwd ty \i -> do
      ct' <- app (sink ct) (Var i)
      extendSubst (b@>RenameNonlin i) $ transposeBlock body ct'
      return UnitVal
  Lam _           -> notTangent
  TypeCon _ _ _   -> notTangent
  LabeledRow _    -> notTangent
  RecordTy _      -> notTangent
  VariantTy _     -> notTangent
  Pi _            -> notTangent
  DepPairTy _     -> notTangent
  TC _            -> notTangent
  Eff _           -> notTangent
  ACase _ _ _     -> error "Unexpected ACase"
  DataConRef _ _ _ -> error "Unexpected ref"
  BoxedRef _ _     -> error "Unexpected ref"
  DepPairRef _ _ _ -> error "Unexpected ref"
  ProjectElt idxs v -> do
    lookupSubstM v >>= \case
      RenameNonlin _ -> error "an error, probably"
      LinRef ref -> do
        ref' <- getNaryProjRef (toList idxs) ref
        emitCTToRef ref' ct
      LinTrivial -> return ()
  where notTangent = error $ "Not a tangent atom: " ++ pprint atom

transposeHof :: Emits o => Hof i -> Atom o -> TransposeM i o ()
transposeHof hof ct = case hof of
  For ann (Lam (LamExpr b  body)) -> do
    ty <- substNonlin $ binderType b
    void $ buildForAnn (getNameHint b) (flipDir ann) ty \i -> do
      ctElt <- app (sink ct) (Var i)
      extendSubst (b@>RenameNonlin i) $ transposeBlock body ctElt
      return UnitVal
  RunState s (Lam (BinaryLamExpr hB refB body)) -> do
    (ctBody, ctState) <- fromPair ct
    (_, cts) <- (fromPair =<<) $ emitRunState "s" ctState \h ref -> do
      extendSubst (hB@>RenameNonlin h) $ extendSubst (refB@>RenameNonlin ref) $
        extendLinRegions h $
          transposeBlock body (sink ctBody)
      return UnitVal
    transposeAtom s cts
  RunReader r (Lam (BinaryLamExpr hB refB body)) -> do
    accumTy <- getReferentTy =<< substNonlin (EmptyAbs $ PairB hB refB)
    baseMonoid <- getBaseMonoidType accumTy >>= tangentBaseMonoidFor
    (_, ct') <- (fromPair =<<) $ emitRunWriter "w" accumTy baseMonoid \h ref -> do
      extendSubst (hB@>RenameNonlin h) $ extendSubst (refB@>RenameNonlin ref) $
        extendLinRegions h $
          transposeBlock body (sink ct)
      return UnitVal
    transposeAtom r ct'
  RunWriter _ (Lam (BinaryLamExpr hB refB body))-> do
    -- TODO: check we have the 0/+ monoid
    (ctBody, ctEff) <- fromPair ct
    void $ emitRunReader "r" ctEff \h ref -> do
      extendSubst (hB@>RenameNonlin h) $ extendSubst (refB@>RenameNonlin ref) $
        extendLinRegions h $
          transposeBlock body (sink ctBody)
      return UnitVal
  _ -> notImplemented

transposeCon :: Emits o => Con i -> Atom o -> TransposeM i o ()
transposeCon con ct = case con of
  Lit _             -> return ()
  ProdCon []        -> return ()
  ProdCon xs ->
    forM_ (enumerate xs) \(i, x) ->
      getProj i ct >>= transposeAtom x
  SumCon _ _ _      -> notImplemented
  SumAsProd _ _ _   -> notImplemented
  ClassDictHole _ _ -> notTangent
  IntRangeVal _ _ _     -> notTangent
  IndexRangeVal _ _ _ _ -> notTangent
  IndexSliceVal _ _ _   -> notTangent
  ParIndexCon _ _       -> notTangent
  LabelCon _     -> notTangent
  BaseTypeRef _  -> notTangent
  TabRef _       -> notTangent
  ConRef _       -> notTangent
  RecordRef _    -> notTangent
  where notTangent = error $ "Not a tangent atom: " ++ pprint (Con con)

notImplemented :: HasCallStack => a
notImplemented = error "Not implemented"

flipDir :: ForAnn -> ForAnn
flipDir ann = case ann of
  RegularFor Fwd -> RegularFor Rev
  RegularFor Rev -> RegularFor Fwd
  ParallelFor -> ParallelFor

-- === instances ===

instance GenericE (TransposeSubstVal c) where
  type RepE (TransposeSubstVal c) = EitherE3 (Name c) Atom UnitE
  fromE = error "todo"
  toE   = error "todo"

instance SinkableE (TransposeSubstVal c)
instance SinkableV TransposeSubstVal

instance FromName TransposeSubstVal where
  fromName v = RenameNonlin v
