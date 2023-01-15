-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module Simplify
  ( simplifyTopBlock, simplifyTopFunction, SimplifiedBlock (..), ReconstructAtom (..), applyReconTop,
    emitSpecialization, specializedFunCoreTypeTop) where

import Control.Category ((>>>))
import Control.Monad
import Control.Monad.Reader
import Data.Maybe
import Data.List (elemIndex)
import Data.Foldable (toList)
import Data.Text.Prettyprint.Doc (Pretty (..), hardline)
import qualified Data.List.NonEmpty as NE
import GHC.Exts (inline)

import Builder
import CheapReduction
import CheckType (CheckableE (..), isData)
import Core
import Err
import Generalize
import IRVariants
import LabeledItems
import Linearize
import Name
import Subst
import Optimize (peepholeOp)
import QueryType
import RuntimePrint
import Transpose
import Types.Core
import Types.Primitives
import Util (enumerate, foldMapM, restructure, splitAtExact, bindM2)

-- === Simplification ===

-- The purpose of simplification is that we want first-class functions
-- in the surface language, but we don't want to deal with them when
-- generating code.  To that end, simplification inlines almost all
-- functions everywhere they appear.

-- In particular, simplification also carries out AD by discharging
-- the `Linearize` and `Transpose` constructors of `PrimHof`.

-- The exception is functions explicitly tagged @noinline by the
-- programmer.  Those, however, are second-class: they are all
-- toplevel, and get specialized until they are first order.

-- Currently, simplification also discharges `CatchException` by
-- elaborating the expression into a Maybe-style monad.  Note: the
-- plan is for `CatchException` to become a user-defined effect, and
-- for simplification to discharge all of them.

-- Simplification also discharges bulk record and variant operations
-- by converting them into individual projections and constructors.

-- Simplification also opportunistically does peep-hole optimizations:
-- some constant folding, case-of-known-constructor, projecting known
-- elements from products, etc; but is not guaranteed to find all such
-- opportunities.

-- === Conversions between CoreIR, CoreToSimpIR, SimpIR ===

-- lift a Simp data atom to a CoreToSimp atom with an optional newtype-coercion
liftSimpAtom
  :: (MonadFail1 m, EnvReader m)
  => Maybe (Type CS n) -> SAtom n -> m n (Atom CS n)
liftSimpAtom maybeTy simpAtom = case maybeTy of
  Nothing -> liftPlainSimpAtom simpAtom
  Just ty -> liftSimpAtomWithType ty simpAtom

liftPlainSimpAtom :: (MonadFail1 m, EnvReader m) => SAtom n -> m n (Atom CS n)
liftPlainSimpAtom = \case
  Var v -> return $ SimpInCore Nothing $ Var v
  Con con -> Con <$> case con of
    Lit v -> return $ Lit v
    ProdCon xs -> ProdCon <$> mapM rec xs
    _ -> error $ "not implemented: " ++ pprint con
  atom -> error $ "not a data atom: " ++ pprint atom
  where rec = liftPlainSimpAtom

liftSimpAtomWithType :: (MonadFail1 m, EnvReader m) => Type CS n -> SAtom n -> m n (Atom CS n)
liftSimpAtomWithType ty simpAtom = case simpAtom of
  Var _          -> return $ SimpInCore (Just ty) simpAtom
  ProjectElt _ _ -> return $ SimpInCore (Just ty) simpAtom
  _ -> do
    (cons , ty') <- unwrapLeadingNewtypesType ty
    atom <- case (ty', simpAtom) of
      (BaseTy _  , Con (Lit v))      -> return $ Con $ Lit v
      (ProdTy tys, Con (ProdCon xs))   -> Con . ProdCon <$> zipWithM rec tys xs
      (SumTy  tys, Con (SumCon _ i x)) -> Con . SumCon tys i <$> rec (tys!!i) x
      (DepPairTy dpt@(DepPairType (b:>t1) t2), DepPair x1 x2 _) -> do
        x1' <- rec t1 x1
        t2' <- applySubst (b@>SubstVal x1') t2
        x2' <- rec t2' x2
        return $ DepPair x1' x2' dpt
      _ -> error $ "can't lift " <> pprint simpAtom <> " to " <> pprint ty'
    return $ wrapNewtypesData cons atom
  where rec = liftSimpAtomWithType

-- `Nothing` (the `Maybe (Type CS)` one) means that there's no newtype coercion
-- needed to get back to the original atom.
tryAsDataAtom :: Emits n => Atom CS n -> SimplifyM i n (Maybe (SAtom n, Maybe (Type CS n)))
tryAsDataAtom atom = do
  ty <- getType atom
  isData ty >>= \case
    False -> return Nothing
    True -> Just <$> do
      repAtom <- go atom
      return (repAtom, Just ty)
 where
  go :: Emits n => Atom CS n -> SimplifyM i n (SAtom n)
  go = \case
    -- TODO: this case might be dead. We shouldn't encounter `CS` vars in o-space.
    -- TODO: if we tag local names with IR parameters then this type will need
    Var v -> return $ Var v
    TabLam (TabLamExpr b body) -> dropSubst do
      let richIxTy = ixTypeType $ binderAnn b
      ixTy <- simplifyIxType $ binderAnn b
      buildFor (getNameHint b) Fwd ixTy \i -> do
        i' <- liftSimpAtom (Just $ sink richIxTy) (Var i)
        extendSubst (b@>SubstVal i') do
          toDataAtomIgnoreRecon =<< simplifyBlock body
    Con con -> Con <$> case con of
      Lit v -> return $ Lit v
      ProdCon xs -> ProdCon <$> mapM go xs
      SumCon  tys tag x -> SumCon <$> mapM getRepType tys <*> pure tag <*> go x
      SumAsProd tys tag xs ->
        SumAsProd <$> mapM getRepType tys <*> go tag <*> mapM go xs
      DictHole _ _ -> error "unexpected DictHole"
      HeapVal       -> return HeapVal
    PtrVar v        -> return $ PtrVar v
    DepPair x y ty -> do
      DepPairTy ty' <- getRepType $ DepPairTy ty
      DepPair <$> go x <*> go y <*> pure ty'
    ProjectElt UnwrapNewtype x -> go x
    -- TODO: do we need to think about a case like `fst (1, \x.x)`, where
    -- the projection is data but the argument isn't?
    ProjectElt (ProjectProduct i) x -> normalizeProj (ProjectProduct i) =<< go x
    NewtypeCon _ x  -> go x
    SimpInCore _ x -> return x
    ACase _ _ _     -> notData
    Lam _ _   _     -> notData
    DepPairTy _     -> notData
    Pi _            -> notData
    NewtypeTyCon _  -> notData
    DictCon _       -> notData
    DictTy _        -> notData
    Eff _           -> notData
    TC _            -> notData
    TabPi _         -> notData
    where
      notData = error $ "Not runtime-representable data: " ++ pprint atom

tryGetRepType :: Type CS n -> SimplifyM i n (Maybe (SType n))
tryGetRepType t = isData t >>= \case
  False -> return Nothing
  True  -> Just <$> getRepType t

getRepType :: Type CS n -> SimplifyM i n (SType n)
getRepType ty = go ty where
  go :: Type CS n -> SimplifyM i n (SType n)
  go = \case
    TC con -> TC <$> case con of
      BaseType b  -> return $ BaseType b
      ProdType ts -> ProdType <$> mapM go ts
      SumType  ts -> SumType  <$> mapM go ts
      RefType h a -> RefType  <$> toDataAtomIgnoreReconAssumeNoDecls h <*> go a
      TypeKind    -> error $ notDataType
      HeapType    -> return $ HeapType
    DepPairTy (DepPairType b@(_:>l) r) -> do
      l' <- go l
      withFreshBinder (getNameHint b) l' \b' -> do
        x <- liftSimpAtom (Just $ sink l) (Var $ binderName b')
        r' <- go =<< applySubst (b@>SubstVal x) r
        return $ DepPairTy $ DepPairType (b':>l') r'
    TabPi (TabPiType (b:>ixTy) bodyTy) -> do
      ixTy' <- simplifyIxType ixTy
      withFreshBinder (getNameHint b) ixTy' \b' -> do
        x <- liftSimpAtom (Just $ sink $ ixTypeType ixTy) (Var $ binderName b')
        bodyTy' <- go =<< applySubst (b@>SubstVal x) bodyTy
        return $ TabPi $ TabPiType (b':>ixTy') bodyTy'
    ACase _ _ _   -> error "not implemented"
    NewtypeTyCon con -> do
      (_, ty') <- unwrapNewtypeType con
      go ty'
    Pi _           -> error notDataType
    DictTy _       -> error notDataType
    DictCon _      -> error notType
    Eff _          -> error notType
    TabLam _       -> error notType
    Con _          -> error notType
    PtrVar _       -> error notType
    DepPair _ _ _  -> error notType
    ProjectElt _ _ -> error notType
    NewtypeCon _ _ -> error notType
    SimpInCore _ _ -> error notType
    Lam _ _   _    -> error notType
    Var _ -> error "Shouldn't have type variables in CS IR with SimpIR builder names"
    where
      notType     = "Not a type: " ++ pprint ty
      notDataType = "Not a type of runtime-representable data: " ++ pprint ty

toDataAtom :: Emits n => Atom CS n -> SimplifyM i n (SAtom n, Maybe (Type CS n))
toDataAtom x = tryAsDataAtom x >>= \case
  Just x' -> return x'
  Nothing -> error $ "Not a data atom: " ++ pprint x

toDataAtomIgnoreRecon :: Emits n => Atom CS n -> SimplifyM i n (SAtom n)
toDataAtomIgnoreRecon x = fst <$> toDataAtom x

toDataAtomIgnoreReconAssumeNoDecls :: Atom CS n -> SimplifyM i n (SAtom n)
toDataAtomIgnoreReconAssumeNoDecls x = do
  Abs decls result <- buildScoped $ fst <$> toDataAtom (sink x)
  case decls of
    Empty -> return result
    _ -> error "unexpected decls"

toDataOrRepType :: Emits n => Atom CS n -> SimplifyM i n (SAtom n)
toDataOrRepType x = getType x >>= \case
  TyKind -> getRepType x
  _ -> toDataAtomIgnoreRecon x

simplifiedPiType :: NaryPiType CoreIR n -> SimplifyM i n (NaryPiType SimpIR n)
simplifiedPiType (NaryPiType bsTop eff resultTy) =
 dropSubst $ go bsTop \bsTop' ->
  NaryPiType bsTop' <$> simplifyEffectRow eff <*> (substM resultTy >>= getRepType)
 where
   go :: Nest (PiBinder CoreIR) i i'
      -> (forall o'. DExt o o' => Nest (PiBinder SimpIR) o o' ->SimplifyM i' o' a)
      -> SimplifyM i o a
   go Empty cont = getDistinct >>= \Distinct -> cont Empty
   go (Nest (PiBinder b ty arr) bs) cont = do
     ty' <- substM ty
     simpTy <- getRepType ty'
     withFreshBinder (getNameHint b) simpTy \b' -> do
       x <- liftSimpAtom (Just $ sink ty') (Var $ binderName b')
       extendSubst (b@>SubstVal x) $
         go bs \bs' -> cont (Nest (PiBinder b' simpTy arr) bs')

simplifyEffectRow :: EffectRow CS i -> SimplifyM i o (EffectRow SimpIR o)
simplifyEffectRow effRow = do
  EffectRow effs maybeTail <- substM effRow
  case maybeTail of
    EffectRowTail _ -> error "shouldn't have a polymorphic tail left"
    NoTail -> do
      effs' <- eSetFromList <$> mapM simplifyEffect (eSetToList effs)
      return $ EffectRow effs' NoTail

simplifyEffect :: Effect CS o -> SimplifyM i o (Effect SimpIR o)
simplifyEffect = \case
   RWSEffect rws h -> RWSEffect rws <$> toDataAtomIgnoreReconAssumeNoDecls h
   ExceptionEffect -> return ExceptionEffect
   IOEffect        -> return IOEffect
   UserEffect v    -> return $ UserEffect v
   InitEffect      -> return InitEffect

-- === Reconstructions ===

data ReconstructAtom (r::IR) (n::S) =
   CoerceRecon (Type r n)
 | LamRecon (ReconAbs (Atom r) n)

applyRecon :: (EnvReader m, Fallible1 m) => ReconstructAtom CS n -> SAtom n -> m n (Atom CS n)
applyRecon (CoerceRecon ty) x = liftSimpAtom (Just ty) x
applyRecon (LamRecon ab) x = applyReconAbs ab =<< liftSimpAtom Nothing x

applyReconAbs
  :: (EnvReader m, Fallible1 m, SinkableE e, SubstE (AtomSubstVal r) e)
  => ReconAbs e n -> Atom r n -> m n (e n)
applyReconAbs (Abs bs result) x = do
  xs <- unpackTelescope x
  applySubst (bs @@> map SubstVal xs) result

-- === Simplification monad ===

class (ScopableBuilder2 SimpIR m, SubstReader (AtomSubstVal CS) m) => Simplifier m

data WillLinearize = WillLinearize | NoLinearize

-- Note that the substitution carried in this monad generally maps AtomName i to
-- simplified Atom o, but with one notable exception: top-level function names.
-- This is because top-level functions can have special (AD) rules associated with
-- them, and we try to preserve their identity for as long as we can. Since the only
-- elimination form for function is application, we do some extra handling in simplifyApp.
newtype SimplifyM (i::S) (o::S) (a:: *) = SimplifyM
  { runSimplifyM'
    :: SubstReaderT (AtomSubstVal CS) (DoubleBuilderT SimpIR TopEnvFrag (ReaderT WillLinearize HardFailM)) i o a }
  deriving ( Functor, Applicative, Monad, ScopeReader, EnvExtender, Fallible
           , EnvReader, SubstReader (AtomSubstVal CS), MonadFail
           , Builder SimpIR, HoistingTopBuilder TopEnvFrag)

type CS = CoreToSimpIR

liftSimplifyM
  :: (SinkableE e, RenameE e, TopBuilder m, Mut n)
  => (forall l. DExt n l => SimplifyM n l (e l))
  -> m n (e n)
liftSimplifyM cont = do
  Abs envFrag e <- liftM (runHardFail . flip runReaderT NoLinearize) $
    liftDoubleBuilderT $ runSubstReaderT (sink idSubst) $ runSimplifyM' cont
  emitEnv $ Abs envFrag e
{-# INLINE liftSimplifyM #-}

instance Simplifier SimplifyM

instance MonadReader WillLinearize (SimplifyM i o) where
  ask = SimplifyM $ SubstReaderT $ ReaderT \_ -> ask
  local f m = SimplifyM $ SubstReaderT $ ReaderT \s -> local f $ runSubstReaderT s $ runSimplifyM' m

-- TODO: figure out why we can't derive this one (here and elsewhere)
instance ScopableBuilder SimpIR (SimplifyM i) where
  buildScoped cont = SimplifyM $ SubstReaderT $ ReaderT \env ->
    buildScoped $ runSubstReaderT (sink env) (runSimplifyM' cont)
  {-# INLINE buildScoped #-}

-- === Top-level API ===

data SimplifiedBlock n = SimplifiedBlock (SBlock n) (ReconstructAtom CS n)

-- TODO: extend this to work on functions instead of blocks (with blocks still
-- accessible as nullary functions)
simplifyTopBlock :: (TopBuilder m, Mut n) => Block CoreIR n -> m n (SimplifiedBlock n)
simplifyTopBlock block = liftSimplifyM $ buildSimplifiedBlock $ simplifyBlock block
{-# SCC simplifyTopBlock #-}

simplifyTopFunction :: (TopBuilder m, Mut n) => LamExpr CoreIR n -> m n (LamExpr SimpIR n)
simplifyTopFunction f = liftSimplifyM do
  (lam, CoerceReconAbs) <- simplifyLam f
  return lam
{-# SCC simplifyTopFunction #-}

applyReconTop :: (EnvReader m, Fallible1 m) => ReconstructAtom CS n -> SAtom n -> m n (CAtom n)
applyReconTop = applyRecon

instance GenericE SimplifiedBlock where
  type RepE SimplifiedBlock = PairE SBlock (ReconstructAtom CS)
  fromE (SimplifiedBlock block recon) = PairE block recon
  {-# INLINE fromE #-}
  toE   (PairE block recon) = SimplifiedBlock block recon
  {-# INLINE toE #-}

instance SinkableE SimplifiedBlock
instance RenameE SimplifiedBlock
instance HoistableE SimplifiedBlock
instance CheckableE SimplifiedBlock where
  checkE (SimplifiedBlock block recon) =
    -- TODO: CheckableE instance for the recon too
    SimplifiedBlock <$> checkE block <*> renameM recon

instance Pretty (SimplifiedBlock n) where
  pretty (SimplifiedBlock block recon) =
    pretty block <> hardline <> pretty recon

-- === All the bits of IR  ===

simplifyDecls :: Emits o => Nest (Decl CS) i i' -> SimplifyM i' o a -> SimplifyM i o a
simplifyDecls topDecls cont = do
  s  <- getSubst
  s' <- simpDeclsSubst s topDecls
  withSubst s' cont
{-# INLINE simplifyDecls #-}

simpDeclsSubst
  :: Emits o => Subst (AtomSubstVal CS) l o -> Nest (Decl CS) l i'
  -> SimplifyM i o (Subst (AtomSubstVal CS) i' o)
simpDeclsSubst !s = \case
  Empty -> return s
  Nest (Let b (DeclBinding _ _ expr)) rest -> do
    let hint = (getNameHint b)
    x <- withSubst s $ simplifyExpr hint expr
    simpDeclsSubst (s <>> (b@>SubstVal x)) rest

simplifyExpr :: Emits o => NameHint -> Expr CS i -> SimplifyM i o (Atom CS o)
simplifyExpr hint expr = confuseGHC >>= \_ -> case expr of
  App f xs -> do
    xs' <- mapM simplifyAtom xs
    simplifyApp hint f xs'
  TopApp f xs -> do
    f' <- substM f
    xs' <- forM xs \x -> toDataAtomIgnoreRecon =<< simplifyAtom x
    liftSimpAtom Nothing =<< naryTopApp f' xs'
  TabApp f xs -> do
    xs' <- mapM simplifyAtom xs
    simplifyTabApp hint f xs'
  Atom x -> simplifyAtom x
  PrimOp  op  -> (inline traversePrimOp) simplifyAtom op >>= simplifyOp
  ProjMethod dict i -> bindM2 projectDictMethod (simplifyAtom dict) (pure i)
  RefOp ref eff -> do
    resultTy <- getTypeSubst expr
    ref' <- toDataAtomIgnoreRecon =<< simplifyAtom ref
    eff' <- simplifyRefOp eff
    ans <- emitExpr $ RefOp ref' eff'
    liftSimpAtom (Just resultTy) ans
  Hof hof -> simplifyHof hint hof
  RecordVariantOp op -> simplifyRecordVariantOp  =<< mapM simplifyAtom op
  TabCon ty xs -> do
    ty' <- substM ty
    tySimp <- getRepType ty'
    xs' <- forM xs \x -> toDataAtomIgnoreRecon =<< simplifyAtom x
    liftSimpAtom (Just ty') =<< emitExpr (TabCon tySimp xs')
  UserEffectOp _ -> error "not implemented"
  Case scrut alts resultTy eff -> do
    scrut' <- simplifyAtom scrut
    -- TODO: this can fail! We need to handle the case of a non-data scrutinee!
    scrutSimp <- toDataAtomIgnoreRecon scrut'
    case trySelectBranch scrut' of
      Just (i, arg) -> do
        Abs b body <- return $ alts !! i
        extendSubst (b @> SubstVal arg) $ simplifyBlock body
      Nothing -> do
        resultTy' <- substM resultTy
        tryGetRepType resultTy' >>= \case
          Nothing -> defuncCase scrutSimp alts resultTy'
          Just resultTyData -> do
            eff' <- simplifyEffectRow eff
            alts' <- forM alts \(Abs b body) -> do
              bTy <- substM $ binderType b
              bTy' <- getRepType bTy
              buildAbs (getNameHint b) bTy' \x -> do
                x' <- liftSimpAtom (Just $ sink bTy) (Var x)
                extendSubst (b @> SubstVal x') $
                  buildBlock do
                    -- This should succeed because of the `isData` test
                    toDataAtomIgnoreRecon =<< simplifyBlock body
            liftSimpAtom (Just resultTy') =<< emitExpr (Case scrutSimp alts' resultTyData eff')

simplifyRefOp :: Emits o => RefOp CS i -> SimplifyM i o (RefOp SimpIR o)
simplifyRefOp = \case
  MExtend (BaseMonoid em cb) x -> do
    em'  <- toDataAtomIgnoreRecon =<< simplifyAtom em
    x'   <- toDataAtomIgnoreRecon =<< simplifyAtom x
    (cb', CoerceReconAbs) <- simplifyLam cb
    return $ MExtend (BaseMonoid em' cb') x'
  MGet   -> return MGet
  MPut x -> MPut <$> (toDataAtomIgnoreRecon =<< simplifyAtom x)
  MAsk   -> return MAsk
  IndexRef x -> IndexRef <$> (toDataAtomIgnoreRecon =<< simplifyAtom x)
  ProjRef i -> return $ ProjRef i

caseComputingEffs
  :: forall m n r. (MonadFail1 m, EnvReader m)
  => Atom r n -> [Alt r n] -> Type r n -> m n (Expr r n)
caseComputingEffs scrut alts resultTy = do
  Case scrut alts resultTy <$> foldMapM getEffects alts
{-# INLINE caseComputingEffs #-}

defuncCase :: Emits o => Atom SimpIR o -> [Alt CS i] -> Type CS o -> SimplifyM i o (Atom CS o)
defuncCase scrut alts resultTy = do
  split <- splitDataComponents resultTy
  (alts', recons) <- unzip <$> mapM (simplifyAlt split) alts
  closureTys <- mapM getAltNonDataTy alts'
  let closureSumTy = SumTy closureTys
  let newNonDataTy = nonDataTy split
  alts'' <- forM (enumerate alts') \(i, alt) -> injectAltResult closureTys i alt
  caseExpr <- caseComputingEffs scrut alts'' (PairTy (dataTy split) closureSumTy)
  caseResult <- emitExpr $ caseExpr
  (dataVal, sumVal) <- fromPair caseResult
  reconAlts <- forM (zip closureTys recons) \(ty, recon) -> liftCSBuilder do
    buildUnaryAtomAlt (injectIRE ty) \v -> applyRecon (sink recon) (Var v)
  sumVal' <- liftSimpAtom Nothing sumVal
  let nonDataVal = ACase sumVal' reconAlts newNonDataTy
  Distinct <- getDistinct
  fromSplit split dataVal nonDataVal
  where
    getAltNonDataTy :: EnvReader m => Alt SimpIR n -> m n (SType n)
    getAltNonDataTy (Abs bs body) = liftSubstEnvReaderM do
      substBinders bs \bs' -> do
        ~(PairTy _ ty) <- getTypeSubst body
        -- Result types of simplified abs should be hoistable past binder
        return $ ignoreHoistFailure $ hoist bs' ty

    injectAltResult :: EnvReader m => [SType n] -> Int -> Alt SimpIR n -> m n (Alt SimpIR n)
    injectAltResult sumTys con (Abs b body) = liftBuilder do
      buildAlt (binderType b) \v -> do
        originalResult <- emitBlock =<< applyRename (b@>v) body
        (dataResult, nonDataResult) <- fromPair originalResult
        return $ PairVal dataResult $ Con $ SumCon (sinkList sumTys) con nonDataResult

    -- similar to `simplifyAbs` but assumes that the result is a pair
    -- whose first component is data. The reconstruction returned only
    -- applies to the second component.
    simplifyAlt
      :: SplitDataNonData n -> Abs (Binder CS) (Block CS) i
      -> SimplifyM i o (Abs (Binder SimpIR) (Block SimpIR) o, ReconstructAtom CS o)
    simplifyAlt split (Abs (b:>bTy) body) = fromPairE <$> do
      -- TODO: this can fail! We need to handle the case of a non-data scrutinee!
      bTyCS <- substM bTy
      bTy' <- getRepType bTyCS
      withFreshBinder (getNameHint b) bTy' \b' -> do
        x <- liftSimpAtom (Just $ sink bTyCS) (Var $ binderName b')
        extendSubst (b@>SubstVal x) do
          ab <- buildScoped $ simplifyBlock body
          (resultWithDecls, recon) <- refreshAbs ab \decls result -> do
            let locals = toScopeFrag b' >>> toScopeFrag decls
            -- TODO: this might be too cautious. The type only needs to
            -- be hoistable above the decls. In principle it can still
            -- mention vars from the lambda binders.
            Distinct <- getDistinct
            (resultData, resultNonData) <- toSplit split result
            (newResult, reconAbs) <- telescopicCapture locals resultNonData
            return (Abs decls (PairVal resultData newResult), LamRecon reconAbs)
          block <- makeBlockFromDecls resultWithDecls
          return $ PairE (Abs (b':>bTy') block) recon

simplifyApp :: forall i o. Emits o
  => NameHint -> Atom CS i -> NE.NonEmpty (Atom CS o) -> SimplifyM i o (Atom CS o)
simplifyApp hint f xs =
  simplifyFuncAtom f >>= \case
    Left  (lam, arr, eff)  -> fast lam arr eff
    Right atom -> slow atom
  where
    fast :: LamExpr CS i' -> Arrow -> EffAbs CS i' -> SimplifyM i' o (Atom CS o)
    fast lam arr eff = case fromNaryLam (NE.length xs) (Lam lam arr eff) of
      Just (bsCount, LamExpr bs (Block _ decls atom)) -> do
          let (xsPref, xsRest) = NE.splitAt bsCount xs
          extendSubst (bs@@>(SubstVal <$> xsPref)) $ simplifyDecls decls $
            case NE.nonEmpty xsRest of
              Nothing    -> simplifyAtom atom
              Just rest' -> simplifyApp hint atom rest'
      Nothing -> error "should never happen"

    slow :: Atom CS o -> SimplifyM i o (Atom CS o)
    slow atom = case atom of
      Lam lam arr eff -> dropSubst $ fast lam arr eff
      ACase e alts ty -> do
        -- TODO: Don't rebuild the alts here! Factor out Case simplification
        -- with lazy substitution and call it from here!
        resultTy <- getAppType ty $ toList xs
        alts' <- forM alts \(Abs b a) -> liftCSBuilder do
          buildAlt (binderType b) \v -> do
            a' <- applyRename (b@>v) a
            naryApp a' (map sink $ toList xs)
        caseExpr <- caseComputingEffs e alts' resultTy
        dropSubst $ simplifyExpr hint caseExpr
      Var v -> do
        fTy <- getType atom
        resultTy <- getAppType fTy $ toList xs
        lookupAtomName v >>= \case
          NoinlineFun numSpecializationArgs _ _ ->
            case splitAtExact numSpecializationArgs (toList xs) of
              Just (specializationArgs, runtimeArgs) -> do
                (spec, extraArgs) <- determineSpecializationSpec v specializationArgs
                ab <- getSpecializedFunction spec
                Just specializedFunction <- emitHoistedEnv ab
                allArgs <- mapM toDataAtomIgnoreRecon (extraArgs ++ runtimeArgs)
                liftSimpAtom (Just resultTy) =<< naryTopApp specializedFunction allArgs
              Nothing -> error $ "Specialization of " ++ pprint atom ++
                " requires saturated application of specialization args."
          FFIFunBound _ f' -> do
            xs' <- mapM toDataAtomIgnoreRecon $ toList xs
            liftSimpAtom Nothing =<< naryTopApp f' xs'
          b -> error $ "Should only have noinline functions left " ++ pprint b
      _ -> error $ "Unexpected function: " ++ pprint atom

    simplifyFuncAtom :: Atom CS i -> SimplifyM i o (Either (LamExpr CS i, Arrow, EffAbs CS i) (Atom CS o))
    simplifyFuncAtom func = case func of
      Lam lam arr eff -> return $ Left (lam, arr, eff)
      _ -> Right <$> simplifyAtomAndInline func

-- | Like `simplifyAtom`, but will try to inline function definitions found
-- in the environment. The only exception is when we're going to differentiate
-- and the function has a custom derivative rule defined.
simplifyAtomAndInline :: Atom CS i -> SimplifyM i o (Atom CS o)
simplifyAtomAndInline atom = confuseGHC >>= \_ -> case atom of
  Var v -> do
    env <- getSubst
    case env ! v of
      Rename v' -> inlineVar v'
      SubstVal (Var v') -> inlineVar v'
      SubstVal x -> return x
  _ -> simplifyAtom atom >>= \case
    Var v -> inlineVar v
    ans -> return ans
  where
    inlineVar :: AtomName CS o -> SimplifyM i o (Atom CS o)
    inlineVar v = do
      -- We simplify all applications, except those that have custom linearizations
      -- and are inside a linearization operation.
      ask >>= \case
        WillLinearize -> do
          doInline
          -- lookupCustomRules v >>= \case
          --   Just (CustomLinearize _ _ _) -> return $ Var v
          --   Nothing -> doInline
        NoLinearize -> doInline
      where
        doInline = do
          lookupAtomName v >>= \case
            LetBound (DeclBinding _ _ (Atom x)) -> dropSubst $ simplifyAtomAndInline x
            _ -> return $ Var v

determineSpecializationSpec
  :: EnvReader m => AtomName CS n -> [Atom CS n] -> m n (SpecializationSpec n, [Atom CS n])
determineSpecializationSpec fname staticArgs = do
  lookupAtomName fname >>= \case
    NoinlineFun _ (NaryPiType bs _ _) _ -> do
      (PairB staticArgBinders _) <- return $
        splitNestAt (length staticArgs) bs
      (ab, extraArgs) <- generalizeArgs staticArgBinders staticArgs
      return (AppSpecialization fname ab, extraArgs)
    _ -> error "should only be specializing top functions"

getSpecializedFunction :: EnvReader m => SpecializationSpec n -> m n (Abs TopEnvFrag TopFunName n)
getSpecializedFunction s = do
  querySpecializationCache s >>= \case
    Just name -> return $ Abs emptyOutFrag name
    _ -> liftTopBuilderHoisted $ emitSpecialization (sink s)

emitSpecialization :: (Mut n, TopBuilder m) => SpecializationSpec n -> m n (TopFunName n)
emitSpecialization s = do
  let hint = getNameHint s
  specializedTy <- liftSimplifyM $ specializedFunSimpType (sink s)
  let binding = TopFunBinding $ DexTopFun specializedTy s Waiting
  name <- emitBinding hint binding
  extendSpecializationCache s name
  return name

specializedFunCoreTypeTop
  :: (Mut n, TopBuilder m)
  => SpecializationSpec n -> m n (NaryPiType CoreIR n)
specializedFunCoreTypeTop spec = liftSimplifyM $ specializedFunCoreType $ sink spec

specializedFunCoreType :: SpecializationSpec n -> SimplifyM i n (NaryPiType CoreIR n)
specializedFunCoreType (AppSpecialization f ab) = do
  refreshAbs ab \extraArgBs (ListE staticArgs) -> do
    lookupAtomName (sink f) >>= \case
      NoinlineFun _ fTy _ -> do
        NaryPiType dynArgBs effs resultTy <- instantiateNaryPi fTy staticArgs
        let allBs = fmapNest plainPiBinder extraArgBs >>> dynArgBs
        return $ NaryPiType allBs effs resultTy
      _ -> error "should only be specializing top-level functions"

specializedFunSimpType :: SpecializationSpec n -> SimplifyM i n (NaryPiType SimpIR n)
specializedFunSimpType spec = do
  piTy <- specializedFunCoreType spec
  simplifiedPiType piTy

-- TODO: de-dup this and simplifyApp?
simplifyTabApp :: forall i o. Emits o
  => NameHint -> Atom CS i -> NE.NonEmpty (Atom CS o) -> SimplifyM i o (Atom CS o)
simplifyTabApp hint f xs =
  simplifyFuncAtom f >>= \case
    Left  lam  -> fast lam
    Right atom -> slow atom
  where
    fast :: TabLamExpr CS i' -> SimplifyM i' o (Atom CS o)
    fast lam = case fromNaryTabLam (NE.length xs) (TabLam lam) of
      Just (bsCount, LamExpr bs (Block _ decls atom)) -> do
          let (xsPref, xsRest) = NE.splitAt bsCount xs
          extendSubst (bs@@>(SubstVal <$> xsPref)) $ simplifyDecls decls $
            case NE.nonEmpty xsRest of
              Nothing    -> simplifyAtom atom
              Just rest' -> simplifyTabApp hint atom rest'
      Nothing -> error "should never happen"

    slow :: Atom CS o -> SimplifyM i o (Atom CS o)
    slow = \case
      TabLam lam -> dropSubst $ fast lam
      ACase e alts ty -> do
        -- TODO: Don't rebuild the alts here! Factor out Case simplification
        -- with lazy substitution and call it from here!
        resultTy <- getTabAppType ty $ toList xs
        alts' <- forM alts \(Abs b a) -> liftCSBuilder do
          buildAlt (binderType b) \v -> do
            a' <- applyRename (b@>v) a
            naryTabApp a' (map sink $ toList xs)
        caseExpr <- caseComputingEffs e alts' resultTy
        dropSubst $ simplifyExpr hint $ caseExpr
      atom -> do
        atom' <- toDataAtomIgnoreRecon atom
        xs' <- mapM toDataAtomIgnoreRecon (toList xs)
        resultTy <- getType $ TabApp atom xs
        liftSimpAtom (Just resultTy) =<< naryTabAppHinted hint atom' xs'

    simplifyFuncAtom :: Atom CS i -> SimplifyM i o (Either (TabLamExpr CS i) (Atom CS o))
    simplifyFuncAtom func = case func of
      TabLam lam -> return $ Left lam
      _ -> Right <$> simplifyAtom func

simplifyIxType :: IxType CS o -> SimplifyM i o (IxType SimpIR o)
simplifyIxType (IxType t ixDict) = do
  t' <- getRepType t
  IxType t' <$> case ixDict of
    IxDictAtom (DictCon (IxFin n)) -> do
      n' <- toDataAtomIgnoreReconAssumeNoDecls n
      return $ IxDictRawFin n'
    IxDictAtom d -> do
      (dictAbs, params) <- generalizeIxDict =<< cheapNormalize d
      params' <- mapM toDataAtomIgnoreReconAssumeNoDecls params
      sdName <- requireIxDictCache dictAbs
      return $ IxDictSpecialized t' sdName params'
    -- TODO: remove these two coercions once we disallow these cases in CS
    IxDictRawFin n            -> do
      n' <- toDataAtomIgnoreReconAssumeNoDecls n
      return $ IxDictRawFin n'
    IxDictSpecialized ty d xs ->
      return $ unsafeCoerceIRE $ IxDictSpecialized ty d xs

requireIxDictCache
  :: (HoistingTopBuilder TopEnvFrag m) => AbsDict n -> m n (Name SpecializedDictNameC n)
requireIxDictCache dictAbs = do
  queryIxDictCache dictAbs >>= \case
    Just name -> return name
    Nothing -> do
      ab <- liftTopBuilderHoisted do
        dName <- emitBinding "d" $ sink $ SpecializedDictBinding $ SpecializedDict dictAbs Nothing
        extendCache $ mempty { ixDictCache = eMapSingleton (sink dictAbs) dName }
        return dName
      maybeD <- emitHoistedEnv ab
      case maybeD of
        Just name -> return name
        Nothing -> error "Couldn't hoist specialized dictionary"
{-# INLINE requireIxDictCache #-}

liftCSBuilder :: EnvReader m => BuilderM CS n a -> m n a
liftCSBuilder = liftBuilder
{-# INLINE liftCSBuilder #-}

-- TODO: do we even need this, or is it just a glorified `SubstM`?
simplifyAtom :: Atom CS i -> SimplifyM i o (Atom CS o)
simplifyAtom atom = confuseGHC >>= \_ -> case atom of
  Var v -> simplifyVar v
  -- We'll simplify the body when we eventually call `toDataAtom`
  TabLam _ -> substM atom
  -- We don't simplify body of lam because we'll beta-reduce it soon.
  Lam _ _ _  -> substM atom
  Pi _ -> substM atom
  TabPi _ -> substM atom
  DepPairTy _ -> substM atom
  DepPair x y ty -> DepPair <$> simplifyAtom x <*> simplifyAtom y <*> substM ty
  Con con -> Con <$> (inline traversePrimCon) simplifyAtom con
  TC tc -> TC <$> (inline traversePrimTC) simplifyAtom tc
  Eff eff -> Eff <$> substM eff
  PtrVar v -> PtrVar <$> substM v
  DictCon d -> (DictCon <$> substM d) >>= cheapNormalize
  DictTy  d -> DictTy <$> substM d
  NewtypeCon _ _ -> substM atom
  NewtypeTyCon t -> NewtypeTyCon <$> substM t
  ACase e alts _   -> do
    e' <- simplifyAtom e
    case trySelectBranch e' of
      Just (i, arg) -> do
        Abs b body <- return $ alts !! i
        extendSubst (b @> SubstVal arg) $ simplifyAtom body
      Nothing -> substM atom
  ProjectElt i x -> normalizeProj i =<< simplifyAtom x
  SimpInCore _ _ -> substM atom

simplifyVar :: AtomName CS i -> SimplifyM i o (Atom CS o)
simplifyVar v = do
  env <- getSubst
  case env ! v of
    SubstVal x -> return x
    Rename v' -> do
      AtomNameBinding bindingInfo <- lookupEnv v'
      case bindingInfo of
        -- Functions get inlined only at application sites
        LetBound (DeclBinding _ (Pi _) _) -> return $ Var v'
        LetBound (DeclBinding _ _ (Atom x)) -> dropSubst $ simplifyAtom x
        _ -> return $ Var v'

-- Assumes first order (args/results are "data", allowing newtypes), monormophic
simplifyLam
  :: LamExpr CS i
  -> SimplifyM i o (LamExpr SimpIR o, Abs (Nest AtomNameBinder) (ReconstructAtom CS) o)
simplifyLam (LamExpr bsTop body) = case bsTop of
  Nest (b:>ty) bs -> do
    ty' <- substM ty
    tySimp <- getRepType ty'
    withFreshBinder (getNameHint b) tySimp \b' -> do
      x <- liftSimpAtom (Just $ sink ty') (Var $ binderName b')
      extendSubst (b@>SubstVal x) do
        (LamExpr bs' body', Abs bsRecon recon) <- simplifyLam $ LamExpr bs body
        return (LamExpr (Nest (b':>tySimp) bs') body', Abs (Nest b' bsRecon) recon)
  Empty -> do
    SimplifiedBlock body' recon <- buildSimplifiedBlock $ simplifyBlock body
    return (LamExpr Empty body', Abs Empty recon)

data SplitDataNonData n = SplitDataNonData
  { dataTy    :: Type SimpIR n
  , nonDataTy :: Type CS n
  , toSplit   :: forall i l . Atom CS l -> SimplifyM i l (SAtom l, Atom CS l)
  , fromSplit :: forall i l . DExt n l => SAtom l -> Atom CS l -> SimplifyM i l (Atom CS l) }

-- bijection between that type and a (data, non-data) pair type.
splitDataComponents :: Type CS n -> SimplifyM i n (SplitDataNonData n)
splitDataComponents = \case
  ProdTy tys -> do
    splits <- mapM splitDataComponents tys
    return $ SplitDataNonData
      { dataTy    = ProdTy $ map dataTy    splits
      , nonDataTy = ProdTy $ map nonDataTy splits
      , toSplit = \xProd -> do
          xs <- getUnpacked xProd
          (ys, zs) <- unzip <$> forM (zip xs splits) \(x, split) -> toSplit split x
          return (ProdVal ys, ProdVal zs)
      , fromSplit = \xsProd ysProd -> do
          xs <- getUnpacked xsProd
          ys <- getUnpacked ysProd
          zs <- forM (zip (zip xs ys) splits) \((x, y), split) -> fromSplit split x y
          return $ ProdVal zs }
  ty -> tryGetRepType ty >>= \case
    Just repTy -> return $ SplitDataNonData
      { dataTy = repTy
      , nonDataTy = UnitTy
      , toSplit = \x -> (,UnitVal) <$> toDataAtomIgnoreReconAssumeNoDecls x
      , fromSplit = \x _ -> liftSimpAtom (Just $ sink ty) x }
    Nothing -> return $ SplitDataNonData
      { dataTy = UnitTy
      , nonDataTy = ty
      , toSplit = \x -> return (UnitVal, x)
      , fromSplit = \_ x -> return x }

buildSimplifiedBlock
  :: (forall o'. (Emits o', DExt o o') => SimplifyM i o' (Atom CS o'))
  -> SimplifyM i o (SimplifiedBlock o)
buildSimplifiedBlock cont = do
  Abs decls eitherResult <- buildScoped do
    ans <- cont
    tryAsDataAtom ans >>= \case
      Nothing -> return $ LeftE ans
      Just (dataResult, _) -> do
        ansTy <- getType ans
        return $ RightE (dataResult `PairE` ansTy)
  case eitherResult of
    LeftE ans -> do
      (declsResult, recon) <- refreshAbs (Abs decls ans) \decls' ans' -> do
        (newResult, reconAbs) <- telescopicCapture (toScopeFrag decls') ans'
        return (Abs decls' newResult, LamRecon reconAbs)
      block <- makeBlockFromDecls declsResult
      return $ SimplifiedBlock block recon
    RightE (ans `PairE` ty) -> do
      block <- makeBlockFromDecls $ Abs decls ans
      let ty' = ignoreHoistFailure $ hoist (toScopeFrag decls) ty
      return $ SimplifiedBlock block (CoerceRecon ty')

simplifyRecordVariantOp :: Emits o => RecordVariantOp (Atom CS o) -> SimplifyM i o (Atom CS o)
simplifyRecordVariantOp op = case op of
  RecordCons left right -> getType left >>= \case
    StaticRecordTy leftTys -> getType right >>= \case
      StaticRecordTy rightTys -> do
        -- Unpack, then repack with new arguments (possibly in the middle).
        leftList <- getUnpacked $ unwrapNewtype left
        let leftItems = restructure leftList leftTys
        rightList <- getUnpacked $ unwrapNewtype right
        let rightItems = restructure rightList rightTys
        return $ Record (void (leftTys <> rightTys)) $ toList $ leftItems <> rightItems
      _ -> error "not a record"
    _ -> error "not a record"
  RecordConsDynamic ~(NewtypeTyCon (LabelCon l)) val rec -> do
    getType rec >>= \case
      StaticRecordTy itemTys -> do
        itemList <- getUnpacked $ unwrapNewtype rec
        let items = restructure itemList itemTys
        return $ Record (labeledSingleton l () <> void itemTys) $
          toList $ labeledSingleton l val <> items
      _ -> error "not a record"
  RecordSplit f full -> getType full >>= \case
    StaticRecordTy fullTys -> case f of
      LabeledRow f' | [StaticFields fields] <- fromFieldRowElems f' -> do
        -- Unpack, then repack into two pieces.
        fullList <- getUnpacked $ unwrapNewtype full
        let fullItems = restructure fullList fullTys
        let (_, remaining) = splitLabeledItems fields fullTys
        let (left, right) = splitLabeledItems fields fullItems
        return $ PairVal (Record (void fields)    (toList left ))
                         (Record (void remaining) (toList right))
      _ -> error "failed to simplifiy a field row"
    _ -> error "not a record"
  RecordSplitDynamic ~(NewtypeTyCon (LabelCon l)) rec ->
    getType rec >>= \case
      StaticRecordTy itemTys -> do
        itemList <- getUnpacked $ unwrapNewtype rec
        let items = restructure itemList itemTys
        let (val, rest) = splitLabeledItems (labeledSingleton l ()) items
        let (_, otherItemTys) = splitLabeledItems (labeledSingleton l ()) itemTys
        return $ PairVal (head $ toList val) $
          Record (void otherItemTys) $ toList rest
      _ -> error "not a record"
  VariantLift leftTys right -> do
    VariantTy (NoExt rightTys) <- getType right
    let fullTys = leftTys <> rightTys
    let fullLabels = toList $ reflectLabels fullTys
    let labels = toList $ reflectLabels rightTys
    -- Emit a case statement (ordered by the arg type) that lifts the type.
    rightSimp <- toDataAtomIgnoreRecon right
    resTy <- getResTy
    resTySimp <- getRepType resTy
    liftSimpAtom (Just resTy) =<< buildCase rightSimp resTySimp \caseIdx v -> do
      -- TODO: This is slow! Optimize this! We keep searching through lists all the time!
      let (label, i) = labels !! caseIdx
      let idx = fromJust $ elemIndex (label, i + length (lookupLabel leftTys label)) fullLabels
      SumTy resTys <- sinkM resTySimp
      return $ SumVal resTys idx v
  VariantSplit leftTysLabeled full' -> do
    VariantTy (NoExt fullTysLabeled) <- getType full'
    let rightTysLabeled = snd $ splitLabeledItems leftTysLabeled fullTysLabeled
    resTy <- getResTy
    leftTys <- forM (toList leftTysLabeled) \t -> getRepType t
    rightTys <- mapM getRepType $ toList rightTysLabeled
    full <- toDataAtomIgnoreRecon full'
    resTySimp <- getRepType resTy
    liftSimpAtom (Just resTy) =<< buildCase full resTySimp \caseIdx v -> do
      SumTy resTys <- sinkM resTySimp
      let (label, i) = toList (reflectLabels fullTysLabeled) !! caseIdx
      let labelIx labs li = fromJust $ elemIndex li (toList $ reflectLabels labs)
      case leftTysLabeled `lookupLabel` label of
        [] -> return $ SumVal resTys 1 $ SumVal (sinkList rightTys) (labelIx rightTysLabeled (label, i)) v
        tys -> if i < length tys
          then return $ SumVal resTys 0 $ SumVal (sinkList leftTys ) (labelIx leftTysLabeled (label, i)) v
          else return $ SumVal resTys 1 $ SumVal (sinkList rightTys) (labelIx rightTysLabeled (label, i - length tys)) v
  VariantMake ~(VariantTy (NoExt tys)) label i v -> do
    let ix = fromJust $ elemIndex (label, i) $ toList $ reflectLabels tys
    return $ NewtypeCon (VariantCon (void tys)) $ SumVal (toList tys) ix v
  SumToVariant c -> do
    SumTy cases <- getType c
    let labels = foldMap (const $ labeledSingleton "c" ()) cases
    return $ NewtypeCon (VariantCon labels) c
  where
    getResTy = getType (RecordVariantOp op)

simplifyOp :: Emits o => PrimOp (Atom CS o) -> SimplifyM i o (Atom CS o)
simplifyOp op = do
  ty <- getType $ PrimOp op
  case op of
    BinOp binop x' y' -> do
      x <- toDataAtomIgnoreRecon x'
      y <- toDataAtomIgnoreRecon y'
      liftSimpAtom (Just ty) =<< case binop of
        ISub -> isub x y
        IAdd -> iadd x y
        IMul -> imul x y
        IDiv -> idiv x y
        ICmp Less  -> ilt x y
        ICmp Equal -> ieq x y
        _ -> fallback
    MiscOp (Select c' x' y') -> do
      c <- toDataAtomIgnoreRecon c'
      x <- toDataAtomIgnoreRecon x'
      y <- toDataAtomIgnoreRecon y'
      liftSimpAtom (Just ty) =<< select c x y
    MiscOp (ShowAny x) -> dropSubst $ showAny x >>= simplifyBlock
    _ -> liftSimpAtom (Just ty) =<< fallback
    where
      fallback = do
        op' <- (inline traversePrimOp) toDataOrRepType op
        liftEnvReaderM (peepholeOp op') >>= \case
          Left  a   -> return a
          Right op'' -> emitOp op''

pattern CoerceReconAbs :: Abs (Nest b) (ReconstructAtom CS) n
pattern CoerceReconAbs <- Abs _ (CoerceRecon _)

projectDictMethod :: Emits o => Atom CS o -> Int -> SimplifyM i o (Atom CS o)
projectDictMethod d i = do
  cheapNormalize d >>= \case
    DictCon (InstanceDict instanceName args) -> dropSubst do
      args' <- mapM simplifyAtom args
      InstanceDef _ bs _ body <- lookupInstanceDef instanceName
      let InstanceBody _ methods = body
      let method = methods !! i
      extendSubst (bs@@>(SubstVal <$> args')) $
        simplifyBlock method
    DictCon (IxFin n) -> projectIxFinMethod (toEnum i) n
    d' -> error $ "Not a simplified dict: " ++ pprint d'

simplifyHof :: Emits o => NameHint -> Hof CS i -> SimplifyM i o (Atom CS o)
simplifyHof _hint hof = case hof of
  For d ixDict lam -> do
    (lam', Abs (UnaryNest b) recon) <- simplifyLam lam
    ixType <- ixTyFromDict =<< substM ixDict
    IxType _ ixDict' <- simplifyIxType ixType
    ans <- emitExpr $ Hof $ For d ixDict' lam'
    case recon of
      CoerceRecon _ -> do
        resultTy <- getTypeSubst $ Hof hof
        liftSimpAtom (Just resultTy) ans
      LamRecon reconAbs -> do
        liftCSBuilder $ buildTabLam noHint ixType \i' -> do
          ans' <- liftSimpAtom Nothing =<< sinkM ans
          elt <- tabApp ans' $ Var i'
          -- TODO Avoid substituting the body of `recon` twice (once
          -- for `applySubst` and once for `applyReconAbs`).  Maybe
          -- by making `applyReconAbs` run in a `SubstReader`?
          reconAbs' <- applyRename (b @> i') reconAbs  -- BUG: this mixes up IR variants!!
          applyReconAbs reconAbs' elt
  While body -> do
    SimplifiedBlock body' (CoerceRecon resultTy) <- buildSimplifiedBlock $ simplifyBlock body
    result <- emitExpr (Hof $ While body')
    liftSimpAtom (Just resultTy) result
  RunReader r lam -> do
    r' <- toDataAtomIgnoreRecon =<< simplifyAtom r
    (lam', Abs b recon) <- simplifyLam lam
    ans <- emitExpr $ Hof $ RunReader r' lam'
    let recon' = ignoreHoistFailure $ hoist b recon
    applyRecon recon' ans
  RunWriter Nothing (BaseMonoid e combine) lam -> do
    (e', wTy) <- toDataAtom =<< simplifyAtom e
    (combine', CoerceReconAbs) <- simplifyLam combine
    (lam', Abs b recon) <- simplifyLam lam
    let hof' = Hof $ RunWriter Nothing (BaseMonoid e' combine') lam'
    (ans, w) <- fromPair =<< emitExpr hof'
    let recon' = ignoreHoistFailure $ hoist b recon
    ans' <- applyRecon recon' ans
    w' <- liftSimpAtom wTy w
    return $ PairVal ans' w'
  RunWriter _ _ _ -> error "Shouldn't see a RunWriter with a dest in Simplify"
  RunState Nothing s lam -> do
    (s', sTy) <- toDataAtom =<< simplifyAtom s
    (lam', Abs b recon) <- simplifyLam lam
    resultPair <- emitExpr $ Hof $ RunState Nothing s' lam'
    (ans, sOut) <- fromPair resultPair
    let recon' = ignoreHoistFailure $ hoist b recon
    ans' <- applyRecon recon' ans
    sOut' <- liftSimpAtom sTy sOut
    return $ PairVal ans' sOut'
  RunState _ _ _ -> error "Shouldn't see a RunState with a dest in Simplify"
  RunIO body -> do
    SimplifiedBlock body' recon <- buildSimplifiedBlock $ simplifyBlock body
    ans <- emitExpr $ Hof $ RunIO body'
    applyRecon recon ans
  RunInit body -> do
    SimplifiedBlock body' recon <- buildSimplifiedBlock $ simplifyBlock body
    ans <- emitExpr $ Hof $ RunInit body'
    applyRecon recon ans
  Linearize lam -> do
    -- XXX: we're ignoring the result type here, which only makes sense if we're
    -- dealing with functions on simple types.
    (lam', CoerceReconAbs) <- local (const WillLinearize) $ simplifyLam lam
    linearize lam'
  Transpose lam -> do
    -- XXX: we're ignoring the result type here, which only makes sense if we're
    -- dealing with functions on simple types.
    (lam'@(UnaryLamExpr (b:>ty) _), CoerceReconAbs) <- simplifyLam lam
    lamTransposed <- transpose lam'
    -- XXX: this injection might be sketchy wrt free variables
    return $ Lam (injectIRE lamTransposed) LinArrow (Abs (b:>injectIRE ty) Pure)
  CatchException body-> do
    SimplifiedBlock body' (CoerceRecon ty) <- buildSimplifiedBlock $ simplifyBlock body
    block <- liftBuilder $ runSubstReaderT idSubst $
      buildBlock $ exceptToMaybeBlock $ body'
    result <- emitBlock block
    liftSimpAtom (Just ty) result

simplifyBlock :: Emits o => Block CS i -> SimplifyM i o (Atom CS o)
simplifyBlock (Block _ decls result) = simplifyDecls decls $ simplifyAtom result

-- === exception-handling pass ===

type HandlerM = SubstReaderT (AtomSubstVal SimpIR) (BuilderM SimpIR)

exceptToMaybeBlock :: Emits o => SBlock i -> HandlerM i o (SAtom o)
exceptToMaybeBlock (Block (BlockAnn ty _) decls result) = do
  ty' <- substM ty
  exceptToMaybeDecls ty' decls $ Atom result
exceptToMaybeBlock (Block NoBlockAnn Empty result) = exceptToMaybeExpr $ Atom result
exceptToMaybeBlock _ = error "impossible"

exceptToMaybeDecls :: Emits o => SType o -> Nest SDecl i i' -> SExpr i' -> HandlerM i o (SAtom o)
exceptToMaybeDecls _ Empty result = exceptToMaybeExpr result
exceptToMaybeDecls resultTy (Nest (Let b (DeclBinding _ _ rhs)) decls) finalResult = do
  maybeResult <- exceptToMaybeExpr rhs
  case maybeResult of
    -- This case is just an optimization (but an important one!)
    JustAtom _ x  ->
      extendSubst (b@> SubstVal x) $ exceptToMaybeDecls resultTy decls finalResult
    _ -> emitMaybeCase maybeResult (MaybeTy resultTy)
          (return $ NothingAtom $ sink resultTy)
          (\v -> extendSubst (b@> SubstVal v) $
                   exceptToMaybeDecls (sink resultTy) decls finalResult)

exceptToMaybeExpr :: Emits o => SExpr i -> HandlerM i o (SAtom o)
exceptToMaybeExpr expr = case expr of
  Case e alts resultTy _ -> do
    e' <- substM e
    resultTy' <- substM $ MaybeTy resultTy
    buildCase e' resultTy' \i v -> do
      Abs b body <- return $ alts !! i
      extendSubst (b @> SubstVal v) $ exceptToMaybeBlock body
  Atom x -> do
    x' <- substM x
    ty <- getType x'
    return $ JustAtom ty x'
  Hof (For ann d (UnaryLamExpr b body)) -> do
    ixTy <- ixTyFromDict =<< substM d
    maybes <- buildForAnn (getNameHint b) ann ixTy \i ->
      extendSubst (b@>Rename i) $ exceptToMaybeBlock body
    catMaybesE maybes
  Hof (RunState Nothing s lam) -> do
    s' <- substM s
    BinaryLamExpr h ref body <- return lam
    result  <- emitRunState noHint s' \h' ref' ->
      extendSubst (h @> Rename h' <.> ref @> Rename ref') do
        exceptToMaybeBlock body
    (maybeAns, newState) <- fromPair result
    a <- getTypeSubst expr
    emitMaybeCase maybeAns (MaybeTy a)
       (return $ NothingAtom $ sink a)
       (\ans -> return $ JustAtom (sink a) $ PairVal ans (sink newState))
  Hof (RunWriter Nothing monoid (BinaryLamExpr h ref body)) -> do
    monoid' <- substM monoid
    accumTy <- substM =<< (getReferentTy $ EmptyAbs $ PairB h ref)
    result <- emitRunWriter noHint accumTy monoid' \h' ref' ->
      extendSubst (h @> Rename h' <.> ref @> Rename ref') $
        exceptToMaybeBlock body
    (maybeAns, accumResult) <- fromPair result
    a <- getTypeSubst expr
    emitMaybeCase maybeAns (MaybeTy a)
      (return $ NothingAtom $ sink a)
      (\ans -> return $ JustAtom (sink a) $ PairVal ans (sink accumResult))
  Hof (While body) -> runMaybeWhile $ exceptToMaybeBlock body
  PrimOp (MiscOp (ThrowException _)) -> do
    ty <- getTypeSubst expr
    return $ NothingAtom ty
  _ -> do
    expr' <- substM expr
    hasExceptions expr' >>= \case
      True -> error $ "Unexpected exception-throwing expression: " ++ pprint expr
      False -> do
        v <- emit expr'
        ty <- getType v
        return $ JustAtom ty (Var v)

hasExceptions :: EnvReader m => SExpr n -> m n Bool
hasExceptions expr = getEffects expr >>= \case
  EffectRow effs NoTail -> return $ ExceptionEffect `eSetMember` effs

-- === instances ===

instance GenericE (ReconstructAtom r) where
  type RepE (ReconstructAtom r) = EitherE2 (Type r) (ReconAbs (Atom r))

  fromE = \case
    CoerceRecon ty -> Case0 ty
    LamRecon ab    -> Case1 ab
  {-# INLINE fromE #-}
  toE = \case
    Case0 ty -> CoerceRecon ty
    Case1 ab -> LamRecon ab
    _ -> error "impossible"
  {-# INLINE toE #-}

instance SinkableE   (ReconstructAtom r)
instance HoistableE  (ReconstructAtom r)
instance AlphaEqE    (ReconstructAtom r)
instance RenameE     (ReconstructAtom r)

instance Pretty (ReconstructAtom r n) where
  pretty (CoerceRecon ty) = "Coercion reconstruction: " <> pretty ty
  pretty (LamRecon ab) = "Reconstruction abs: " <> pretty ab

-- === GHC performance hacks ===

{-# SPECIALIZE
  buildNaryAbs
    :: (SinkableE e, RenameE e, SubstE (AtomSubstVal SimpIR) e, HoistableE e)
    => EmptyAbs (Nest (Binder SimpIR)) n
    -> (forall l. DExt n l => [AtomName SimpIR l] -> SimplifyM i l (e l))
    -> SimplifyM i n (Abs (Nest (Binder SimpIR)) e n) #-}

-- Note [Confuse GHC]
-- I can't explain this, but for some reason using this function in strategic
-- places makes GHC produce significantly better code. If we define
--
-- simplifyAtom = \case
--   ...
--   Con con -> traverse simplifyAtom con
--   ...
--
-- then GHC is reluctant to generate a fast-path worker function for simplifyAtom
-- that would return unboxed tuples, because (at least that's my guess) it's afraid
-- that it will have to allocate a reader closure for the traverse, which does not
-- get inlined. For some reason writing the `confuseGHC >>= \_ -> case atom of ...`
-- makes GHC do the right thing, i.e. generate unboxed worker + a tiny wrapper that
-- allocates -- a closure to be passed into traverse.
--
-- What's so special about this, I don't know. `return ()` is insufficient and doesn't
-- make the optimization go through. I'll just take the win for now...
--
-- NB: We should revise this whenever we upgrade to a newer GHC version.
confuseGHC :: SimplifyM i o (DistinctEvidence o)
confuseGHC = getDistinct
{-# INLINE confuseGHC #-}
