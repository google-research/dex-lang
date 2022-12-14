-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Transpose (transpose) where

import Data.Foldable
import Data.Functor
import Control.Monad.Reader
import qualified Data.Set as S

import MTL1
import Err
import Name
import Syntax
import Types.Core
import Types.Primitives
import Builder
import QueryType
import Util (enumerate)
import GHC.Stack

transpose :: (MonadFail1 m, EnvReader m) => LamExpr SimpIR n -> m n (LamExpr SimpIR n)
transpose lam = liftBuilder do
  lam'@(UnaryLamExpr b body) <- sinkM lam
  NaryPiType (UnaryNest piBinder) _ resultTy <- getNaryLamExprType lam'
  let argTy = binderType b
  let resultTy' = ignoreHoistFailure $ hoist piBinder resultTy
  runReaderT1 (ListE []) $ runSubstReaderT idSubst $
    buildUnaryLamExpr noHint resultTy' \ct ->
      withAccumulator (sink argTy) \refSubstVal ->
        extendSubst (b @> refSubstVal) $
          transposeBlock body (sink $ Var ct)
{-# SCC transpose #-}

-- === transposition monad ===

data TransposeSubstVal c n where
  RenameNonlin :: Name c n -> TransposeSubstVal c n
  -- accumulator references corresponding to non-ref linear variables
  LinRef :: SAtom n -> TransposeSubstVal AtomNameC n
  -- as an optimization, we don't make references for trivial vector spaces
  LinTrivial :: TransposeSubstVal AtomNameC n

type LinRegions = ListE SAtomName

type TransposeM a = SubstReaderT TransposeSubstVal
                      (ReaderT1 LinRegions (BuilderM SimpIR)) a

type TransposeM' a = SubstReaderT (AtomSubstVal SimpIR)
                       (ReaderT1 LinRegions (BuilderM SimpIR)) a

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
  substVals <- mapM lookupSubstM $ freeAtomVarsList e
  return $ flip any substVals \case
    LinTrivial     -> True
    LinRef _       -> True
    RenameNonlin _ -> False

withAccumulator
  :: Emits o
  => SType o
  -> (forall o'. (Emits o', DExt o o') => TransposeSubstVal AtomNameC o' -> TransposeM i o' ())
  -> TransposeM i o (SAtom o)
withAccumulator ty cont = do
  singletonTypeVal ty >>= \case
    Nothing -> do
      baseMonoid <- tangentBaseMonoidFor =<< getBaseMonoidType ty
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
  baseMonoid <- getType ct >>= getBaseMonoidType >>= tangentBaseMonoidFor
  void $ liftM Var $ emit $ RefOp ref $ MExtend baseMonoid ct

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

isLinEff :: EffectRow o -> TransposeM i o Bool
isLinEff effs@(EffectRow _ Nothing) = do
  regions <- getLinRegions
  let effRegions = freeAtomVarsList effs
  return $ not $ null $ S.fromList effRegions `S.intersection` S.fromList regions
isLinEff _ = error "Can't transpose polymorphic effects"

transposeExpr :: Emits o => SExpr i -> SAtom o -> TransposeM i o ()
transposeExpr expr ct = case expr of
  Atom atom     -> transposeAtom atom ct
  -- TODO: Instead, should we handle table application like nonlinear
  -- expressions, where we just project the reference?
  App _ _ -> error "shouldn't have App left"
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
      ProjectElt idxs v -> do
        lookupSubstM v >>= \case
          RenameNonlin _ -> error "an error, probably"
          LinRef ref -> do
            let idxs' = toList idxs <&> \case ProjectProduct i -> i; _ -> error "Not a product projection"
            ref' <- getNaryProjRef idxs' ref
            refProj <- naryIndexRef ref' (toList is')
            emitCTToRef refProj ct
          LinTrivial -> return ()
      _ -> error $ "shouldn't occur: " ++ pprint x
  PrimOp op -> transposeOp op ct
  RefOp refArg m   -> do
    refArg' <- substNonlin refArg
    let emitEff = liftM Var . emit . RefOp refArg'
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
      IndexRef _ -> notImplemented
      ProjRef _  -> notImplemented
  Hof hof       -> transposeHof hof ct
  Case e alts _ _ -> do
    linearScrutinee <- isLin e
    case linearScrutinee of
      True  -> notImplemented
      False -> do
        e' <- substNonlin e
        void $ buildCase e' UnitTy \i v -> do
          v' <- emitAtomToName noHint v
          Abs b body <- return $ alts !! i
          extendSubst (b @> RenameNonlin v') do
            transposeBlock body (sink ct)
          return UnitVal
  DAMOp _        -> error "unreachable" -- TODO: rule out statically
  ProjMethod _ _ -> error "unreachable" -- TODO: rule out statically
  TabCon ty es -> do
    TabTy b _ <- return ty
    idxTy <- substNonlin $ binderAnn b
    forM_ (enumerate es) \(ordinalIdx, e) -> do
      i <- unsafeFromOrdinal idxTy (IdxRepVal $ fromIntegral ordinalIdx)
      tabApp ct i >>= transposeAtom e

transposeOp :: Emits o => PrimOp (SAtom i) -> SAtom o -> TransposeM i o ()
transposeOp op ct = case op of
  MiscOp op       -> transposeMiscOp op ct
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

transposeMiscOp :: Emits o => MiscOp (SAtom i) -> SAtom o -> TransposeM i o ()
transposeMiscOp op ct = case op of
  ThrowError   _        -> notLinear
  SumTag _              -> notLinear
  ToEnum _ _            -> notLinear
  ThrowException _      -> notLinear
  OutputStream          -> notLinear
  Select       _ _ _    -> notImplemented
  CastOp       _ _      -> notImplemented
  BitcastOp    _ _      -> notImplemented
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
  TabVal b body   -> do
    ty <- substNonlin $ binderAnn b
    void $ buildFor noHint Fwd ty \i -> do
      ct' <- tabApp (sink ct) (Var i)
      extendSubst (b@>RenameNonlin i) $ transposeBlock body ct'
      return UnitVal
  TabLam _        -> notTangent
  DictCon _       -> notTangent
  DictTy _        -> notTangent
  TypeCon _ _ _   -> notTangent
  LabeledRow _    -> notTangent
  RecordTy _      -> notTangent
  VariantTy _     -> notTangent
  TabPi _         -> notTangent
  DepPairTy _     -> notTangent
  TC _            -> notTangent
  Eff _           -> notTangent
  PtrVar _        -> notTangent
  ACase _ _ _     -> error "Unexpected ACase"
  ProjectElt idxs v -> do
    lookupSubstM v >>= \case
      RenameNonlin _ -> error "an error, probably"
      LinRef ref -> do
        let idxs' = toList idxs <&> \case ProjectProduct i -> i; _ -> error "Not a product projection"
        ref' <- getNaryProjRef idxs' ref
        emitCTToRef ref' ct
      LinTrivial -> return ()
  where notTangent = error $ "Not a tangent atom: " ++ pprint atom

transposeHof :: Emits o => Hof SimpIR i -> SAtom o -> TransposeM i o ()
transposeHof hof ct = case hof of
  For ann d (UnaryLamExpr b  body) -> do
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
    baseMonoid <- getBaseMonoidType accumTy >>= tangentBaseMonoidFor
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
  Newtype ty e      -> case ty of
    TC (Fin _) -> notTangent
    StaticRecordTy _ -> transposeAtom e (unwrapCompoundNewtype ct)
    _ -> notImplemented
  SumCon _ _ _      -> notImplemented
  SumAsProd _ _ _   -> notImplemented
  LabelCon _     -> notTangent
  ExplicitDict _ _ -> notTangent
  DictHole _ _ -> notTangent
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
