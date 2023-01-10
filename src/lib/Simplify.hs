-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module Simplify
  ( simplifyTopBlock, simplifyTopFunction, SimplifiedBlock (..)) where

import Control.Category ((>>>))
import Control.Monad
import Control.Monad.Reader
import Data.Maybe
import Data.List (elemIndex)
import Data.Foldable (toList)
import Data.Text.Prettyprint.Doc (Pretty (..), hardline)
import qualified Data.List.NonEmpty as NE
import qualified Data.Set as S
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
import Util (bindM2)
import Util (enumerate, foldMapM, restructure, splitAtExact)

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

-- Simplification happens after dictionary synthesis (`synthTopBlock`)
-- and before lowering.  Its input invariants are therefore
-- - PrimCon has no DictHole constructors
-- - PrimOp has no
--   - Low-level memory operations (part of Dex Abstract Machine).
--   - Destination operations (part of Dex Abstract Machine).
--   - Vector operations (incidental; simplification should handle
--     these as written, but the input IR happens not to have them due
--     to phase ordering).
-- - PrimHof has no Dex abstract machine ops (currently Seq or
--   RememberDest)

-- The output invariants of simplification are all of the input
-- invariants, and
-- - Lambdas are only allowed in
--   - the result of a top-level Block, or
--   - immediately as arguments to `PrimHof` constructors
-- - Non-table applications in decls can only refer to @noinline
--   functions
-- - PrimHof has no CatchException, Linearize, or Transpose constructors
-- - PrimOp has no
--   - ExplicitDict constructors
--   - ThrowException constructors
--   - RecordCons, RecordConsDynamic, RecordSplit, or
--     RecordSplitDynamic constructors
--   - VariantLift, VariantSplit, or VariantMake constructors

-- === Simplification monad ===

class (ScopableBuilder2 SimpIR m, SubstReader (AtomSubstVal CoreIR) m) => Simplifier m

data WillLinearize = WillLinearize | NoLinearize

-- Note that the substitution carried in this monad generally maps AtomName i to
-- simplified Atom o, but with one notable exception: top-level function names.
-- This is because top-level functions can have special (AD) rules associated with
-- them, and we try to preserve their identity for as long as we can. Since the only
-- elimination form for function is application, we do some extra handling in simplifyApp.
newtype SimplifyM (i::S) (o::S) (a:: *) = SimplifyM
  { runSimplifyM'
    :: SubstReaderT (AtomSubstVal CoreIR) (DoubleBuilderT SimpIR TopEnvFrag (ReaderT WillLinearize HardFailM)) i o a }
  deriving ( Functor, Applicative, Monad, ScopeReader, EnvExtender, Fallible
           , EnvReader, SubstReader (AtomSubstVal CoreIR), MonadFail
           , Builder SimpIR, HoistingTopBuilder TopEnvFrag)

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

data SimplifiedBlock n = SimplifiedBlock (SBlock n) (ReconstructAtom CoreIR n)

-- TODO: extend this to work on functions instead of blocks (with blocks still
-- accessible as nullary functions)
simplifyTopBlock :: (TopBuilder m, Mut n) => CBlock n -> m n (SimplifiedBlock n)
simplifyTopBlock block = liftSimplifyM $ buildSimplifiedBlock $ simplifyBlock block
{-# SCC simplifyTopBlock #-}

simplifyTopFunction :: (TopBuilder m, Mut n) => LamExpr CoreIR n -> m n (LamExpr SimpIR n)
simplifyTopFunction f = liftSimplifyM do
  (lam, IdentityReconAbs) <- simplifyLam f
  return lam
{-# SCC simplifyTopFunction #-}

instance GenericE SimplifiedBlock where
  type RepE SimplifiedBlock = PairE SBlock (ReconstructAtom CoreIR)
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

simplifyDecls :: Emits o => Nest CDecl i i' -> SimplifyM i' o a -> SimplifyM i o a
simplifyDecls topDecls cont = do
  s  <- getSubst
  s' <- simpDeclsSubst s topDecls
  withSubst s' cont
{-# INLINE simplifyDecls #-}

simpDeclsSubst
  :: Emits o => Subst (AtomSubstVal CoreIR) l o -> Nest CDecl l i'
  -> SimplifyM i o (Subst (AtomSubstVal CoreIR) i' o)
simpDeclsSubst !s = \case
  Empty -> return s
  Nest (Let b (DeclBinding _ _ expr)) rest -> do
    let hint = (getNameHint b)
    x <- withSubst s $ simplifyExpr hint expr
    simpDeclsSubst (s <>> (b@>SubstVal x)) rest

simplifyExpr :: Emits o => NameHint -> CExpr i -> SimplifyM i o (CAtom o)
simplifyExpr hint expr = confuseGHC >>= \_ -> case expr of
  App f xs -> do
    xs' <- mapM simplifyAtom xs
    simplifyApp hint f xs'
  TabApp f xs -> do
    xs' <- mapM simplifyAtom xs
    simplifyTabApp hint f xs'
  Atom x -> simplifyAtom x
  PrimOp  op  -> (inline traversePrimOp) simplifyAtom op >>= simplifyOp
  ProjMethod dict i -> bindM2 projectDictMethod (simplifyAtom dict) (pure i)
  RefOp ref eff -> do
    ref' <- coreToSimpAtom =<< simplifyAtom ref
    eff' <- simplifyRefOp eff
    liftM (injectCore . Var) $ emit $ RefOp ref' eff'
  Hof hof -> simplifyHof hint hof
  RecordVariantOp op -> simplifyRecordVariantOp  =<< mapM simplifyAtom op
  TabCon ty xs -> do
    ty' <- coreToSimpAtom =<< simplifyAtom ty
    xs' <- forM xs \x -> coreToSimpAtom =<< simplifyAtom x
    liftM injectCore $ emitExpr $ TabCon ty' xs'
  UserEffectOp _ -> error "not implemented"
  Case scrut alts resultTy eff -> do
    scrut' <- simplifyAtom scrut
    -- TODO: this can fail! We need to handle the case of a non-data scrutinee!
    scrutSimp <- coreToSimpAtom scrut'
    case trySelectBranch scrut' of
      Just (i, arg) -> do
        Abs b body <- return $ alts !! i
        extendSubst (b @> SubstVal arg) $ simplifyBlock body
      Nothing -> do
        resultTy' <- simplifyAtom resultTy
        isData resultTy' >>= \case
          True -> do
            -- TODO: this ought to come as a reward for passing the `isData` test
            resultTyData <- coreToSimpAtom resultTy'
            eff' <- substM eff
            alts' <- forM alts \(Abs b body) -> do
              bTy' <- coreToSimpAtom =<< substM (binderType b)
              buildAbs (getNameHint b) bTy' \x ->
                extendSubst (b @> Rename x) $
                  buildBlock do
                    -- This should succeed because of the `isData` test
                    coreToSimpAtom =<< simplifyBlock body
            liftM Var $ emitHinted hint $ Case scrutSimp alts' resultTyData eff'
          False -> defuncCase scrutSimp alts resultTy'

simplifyRefOp :: Emits o => RefOp CoreIR i -> SimplifyM i o (RefOp SimpIR o)
simplifyRefOp = \case
  MExtend (BaseMonoid em cb) x -> do
    em'  <- coreToSimpAtom =<< simplifyAtom em
    x'   <- coreToSimpAtom =<< simplifyAtom x
    (cb', IdentityReconAbs) <- simplifyLam cb
    return $ MExtend (BaseMonoid em' cb') x'
  MGet   -> return MGet
  MPut x -> MPut <$> (coreToSimpAtom =<< simplifyAtom x)
  MAsk   -> return MAsk
  IndexRef x -> IndexRef <$> (coreToSimpAtom =<< simplifyAtom x)
  ProjRef i -> return $ ProjRef i

caseComputingEffs
  :: forall m n r. (MonadFail1 m, EnvReader m)
  => Atom r n -> [Alt r n] -> Type r n -> m n (Expr r n)
caseComputingEffs scrut alts resultTy = do
  Case scrut alts resultTy <$> foldMapM getEffects alts
{-# INLINE caseComputingEffs #-}

defuncCase :: Emits o => SAtom o -> [Alt CoreIR i] -> CType o -> SimplifyM i o (CAtom o)
defuncCase scrut alts resultTy = do
  split <- splitDataComponents resultTy
  (alts', recons) <- unzip <$> mapM (simplifyAlt split) alts
  closureTys <- mapM getAltNonDataTy alts'
  let closureSumTy = SumTy closureTys
  let newNonDataTy = nonDataTy split
  alts'' <- forM (enumerate alts') \(i, alt) -> injectAltResult closureTys i alt
  caseExpr <- caseComputingEffs scrut alts'' (PairTy (dataTy split) closureSumTy)
  caseResult <- liftM Var $ emit $ caseExpr
  (dataVal, sumVal) <- fromPair caseResult
  reconAlts <- forM (zip closureTys recons) \(ty, recon) -> liftCoreBuilder do
    buildUnaryAtomAlt (injectCore ty) \v -> applyRecon (sink recon) (Var v)
  let nonDataVal = ACase (injectCore sumVal) reconAlts newNonDataTy
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
      :: SplitDataNonData n -> Abs (Binder CoreIR) CBlock i
      -> SimplifyM i o (Abs (Binder SimpIR) SBlock o, ReconstructAtom CoreIR o)
    simplifyAlt split (Abs (b:>bTy) body) = fromPairE <$> do
      -- TODO: this can fail! We need to handle the case of a non-data scrutinee!
      bTy' <- coreToSimpAtom =<< substM bTy
      withFreshBinder (getNameHint b) bTy' \b' -> extendSubst (b@>Rename (binderName b')) do
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
  => NameHint -> CAtom i -> NE.NonEmpty (CAtom o) -> SimplifyM i o (CAtom o)
simplifyApp hint f xs =
  simplifyFuncAtom f >>= \case
    Left  (lam, arr, eff)  -> fast lam arr eff
    Right atom -> slow atom
  where
    fast :: LamExpr CoreIR i' -> Arrow -> EffAbs CoreIR i' -> SimplifyM i' o (CAtom o)
    fast lam arr eff = case fromNaryLam (NE.length xs) (Lam lam arr eff) of
      Just (bsCount, LamExpr bs (Block _ decls atom)) -> do
          let (xsPref, xsRest) = NE.splitAt bsCount xs
          extendSubst (bs@@>(SubstVal <$> xsPref)) $ simplifyDecls decls $
            case NE.nonEmpty xsRest of
              Nothing    -> simplifyAtom atom
              Just rest' -> simplifyApp hint atom rest'
      Nothing -> error "should never happen"

    slow :: CAtom o -> SimplifyM i o (CAtom o)
    slow atom = case atom of
      Lam lam arr eff -> dropSubst $ fast lam arr eff
      ACase e alts ty -> do
        -- TODO: Don't rebuild the alts here! Factor out Case simplification
        -- with lazy substitution and call it from here!
        resultTy <- getAppType ty $ toList xs
        alts' <- forM alts \(Abs b a) -> liftCoreBuilder do
          buildAlt (binderType b) \v -> do
            a' <- applyRename (b@>v) a
            naryApp a' (map sink $ toList xs)
        caseExpr <- caseComputingEffs e alts' resultTy
        dropSubst $ simplifyExpr hint caseExpr
      Var v ->
        lookupAtomName v >>= \case
          TopFunBound _ (AwaitingSpecializationArgsTopFun numSpecializationArgs _) ->
            case splitAtExact numSpecializationArgs (toList xs) of
              Just (specializationArgs, runtimeArgs) -> do
                (spec, extraArgs) <- determineSpecializationSpec v specializationArgs
                ab <- getSpecializedFunction spec
                Just specializedFunction <- emitHoistedEnv ab
                runtimeArgs' <- mapM coreToSimpAtom runtimeArgs -- Runtime args should be "data"
                injectCore <$> naryAppHinted hint (Var specializedFunction)
                  (extraArgs ++ runtimeArgs')
              Nothing -> error $ "Specialization of " ++ pprint atom ++
                " requires saturated application of specialization args."
          _ -> do
            xs' <- mapM coreToSimpAtom xs
            injectCore <$> naryAppHinted hint (Var v) (toList xs')
      _ -> error $ "Unexpected function: " ++ pprint atom

    simplifyFuncAtom :: CAtom i -> SimplifyM i o (Either (LamExpr CoreIR i, Arrow, EffAbs CoreIR i) (CAtom o))
    simplifyFuncAtom func = case func of
      Lam lam arr eff -> return $ Left (lam, arr, eff)
      _ -> Right <$> simplifyAtomAndInline func

-- | Like `simplifyAtom`, but will try to inline function definitions found
-- in the environment. The only exception is when we're going to differentiate
-- and the function has a custom derivative rule defined.
simplifyAtomAndInline :: CAtom i -> SimplifyM i o (CAtom o)
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
    inlineVar :: SAtomName o -> SimplifyM i o (CAtom o)
    inlineVar v = do
      -- We simplify all applications, except those that have custom linearizations
      -- and are inside a linearization operation.
      ask >>= \case
        WillLinearize -> do
          lookupCustomRules v >>= \case
            Just (CustomLinearize _ _ _) -> return $ Var v
            Nothing -> doInline
        NoLinearize -> doInline
      where
        doInline = do
          lookupAtomName v >>= \case
            LetBound (DeclBinding _ _ (Atom x)) -> dropSubst $ simplifyAtomAndInline x
            _ -> return $ Var v

determineSpecializationSpec
  :: EnvReader m => SAtomName n -> [CAtom n] -> m n (SpecializationSpec n, [SAtom n])
determineSpecializationSpec fname staticArgs = do
  lookupAtomName fname >>= \case
    TopFunBound (NaryPiType bs _ _) _ -> do
      (PairB staticArgBinders _) <- return $
        splitNestAt (length staticArgs) bs
      (ab, extraArgs) <- generalizeArgs staticArgBinders staticArgs
      extraArgs' <- mapM coreToSimpAtom extraArgs -- Extra args should be "data"
      return (AppSpecialization fname ab, extraArgs')
    _ -> error "should only be specializing top functions"

getSpecializedFunction :: EnvReader m => SpecializationSpec n -> m n (Abs TopEnvFrag SAtomName n)
getSpecializedFunction s = do
  querySpecializationCache s >>= \case
    Just name -> return $ Abs emptyOutFrag name
    _ -> liftTopBuilderHoisted $ emitSpecialization (sink s)

emitIxDictSpecialization :: DictExpr CoreIR n -> SimplifyM i n (DictExpr CoreIR n)
emitIxDictSpecialization d@(ExplicitMethods _ _) = return d
emitIxDictSpecialization d@(IxFin _)             = return d -- `Ix (Fin n))` is built-in
emitIxDictSpecialization ixDict = do
  (dictAbs, params) <- generalizeIxDict (DictCon ixDict)
  sdName <- queryIxDictCache dictAbs >>= \case
    Just name -> return name
    Nothing -> do
      ab <- liftTopBuilderHoisted do
        dName <- emitBinding "d" $ sink $ SpecializedDictBinding $ SpecializedDict dictAbs Nothing
        extendIxDictCache (sink dictAbs) dName
        return dName
      maybeD <- emitHoistedEnv ab
      case maybeD of
        Just name -> return name
        Nothing -> error "Couldn't hoist specialized dictionary"
  return $ ExplicitMethods sdName params

-- TODO: de-dup this and simplifyApp?
simplifyTabApp :: forall i o. Emits o
  => NameHint -> CAtom i -> NE.NonEmpty (CAtom o) -> SimplifyM i o (CAtom o)
simplifyTabApp hint f xs =
  simplifyFuncAtom f >>= \case
    Left  lam  -> fast lam
    Right atom -> slow atom
  where
    fast :: TabLamExpr CoreIR i' -> SimplifyM i' o (Atom CoreIR o)
    fast lam = case fromNaryTabLam (NE.length xs) (TabLam lam) of
      Just (bsCount, LamExpr bs (Block _ decls atom)) -> do
          let (xsPref, xsRest) = NE.splitAt bsCount xs
          extendSubst (bs@@>(SubstVal <$> xsPref)) $ simplifyDecls decls $
            case NE.nonEmpty xsRest of
              Nothing    -> simplifyAtom atom
              Just rest' -> simplifyTabApp hint atom rest'
      Nothing -> error "should never happen"

    slow :: CAtom o -> SimplifyM i o (CAtom o)
    slow atom = case atom of
      TabLam   lam       -> dropSubst $ fast lam
      ACase e alts ty -> do
        -- TODO: Don't rebuild the alts here! Factor out Case simplification
        -- with lazy substitution and call it from here!
        resultTy <- getTabAppType ty $ toList xs
        alts' <- forM alts \(Abs b a) -> liftCoreBuilder do
          buildAlt (binderType b) \v -> do
            a' <- applyRename (b@>v) a
            naryTabApp a' (map sink $ toList xs)
        caseExpr <- caseComputingEffs e alts' resultTy
        dropSubst $ simplifyExpr hint $ caseExpr
      _ -> do
        atom' <- coreToSimpAtom atom
        xs' <- mapM coreToSimpAtom (toList xs)
        injectCore <$> naryTabAppHinted hint atom' xs'

    simplifyFuncAtom :: CAtom i -> SimplifyM i o (Either (TabLamExpr CoreIR i) (CAtom o))
    simplifyFuncAtom func = case func of
      TabLam lam -> return $ Left lam
      _ -> Right <$> simplifyAtom func

-- TODO: implement this using a safe traversal rather than just coercing after
-- performing the isData check.
testIfDataAtom :: EnvReader m => CAtom n -> m n (Maybe (SAtom n))
testIfDataAtom x = do
  ty <- getType x
  isData ty >>= \case
    True -> return $ Just $ unsafeCoerceIRE x
    False -> return Nothing

-- TODO: implement this using a safe traversal rather than just coercing after
-- performing the isData check.
coreToSimpAtom :: EnvReader m => CAtom n -> m n (SAtom n)
coreToSimpAtom x = do
  testIfDataAtom x >>= \case
    Just x' -> return x'
    Nothing -> do
      xTy <- getType x
      case xTy of
        TyKind -> isData x >>= \case
          True -> return $ unsafeCoerceIRE x
          False -> error $ "can't convert to simp: " ++ pprint x
        DictTy (DictType "Ix" _ _) -> return $ unsafeCoerceIRE x
        _ -> error $ "can't convert to simp: " ++
          pprint x ++ "    " ++ pprint xTy ++ "   " ++ show x

-- Keeping this distinct because we might want to distinguish types and atoms in
-- the simplified IR.
coreToSimpType :: EnvReader m => CAtom n -> m n (SAtom n)
coreToSimpType = coreToSimpAtom

simplifyIxType :: IxType CoreIR o -> SimplifyM i o (IxType SimpIR o)
simplifyIxType (IxType t d) = dropSubst do
  t' <- coreToSimpAtom =<< simplifyAtom t
  d' <- coreToSimpAtom =<< simplifyAtom d
  return $ IxType t' d'

injectCore :: CovariantInIR e => e SimpIR n -> e CoreIR n
injectCore = injectIRE

liftCoreBuilder :: EnvReader m => BuilderM CoreIR n a -> m n a
liftCoreBuilder = liftBuilder
{-# INLINE liftCoreBuilder #-}

simplifyAtom :: CAtom i -> SimplifyM i o (CAtom o)
simplifyAtom atom = confuseGHC >>= \_ -> case atom of
  Var v -> simplifyVar v
  -- Tables that only contain data aren't necessarily getting inlined,
  -- so this might be the last chance to simplify them.
  TabLam (TabLamExpr (b:>ixTy) body) -> do
    getTypeSubst atom >>= isData >>= \case
      True -> do
        ixTy' <- simplifyIxType =<< substM ixTy
        withFreshBinder (getNameHint b) ixTy' \b' ->
          extendSubst (b@>Rename (binderName b')) do
            SimplifiedBlock body' IdentityRecon <- buildSimplifiedBlock $ simplifyBlock body
            return $ injectCore $ TabLam (TabLamExpr (b':>ixTy') body')
      False -> substM atom
  -- We don't simplify body of lam because we'll beta-reduce it soon.
  Lam _ _ _  -> substM atom
  Pi (PiType (PiBinder b ty arr) eff resultTy) -> do
    ty' <- simplifyAtom ty
    withFreshBinder (getNameHint b) (PiBinding arr ty') \b' -> do
      extendRenamer (b@>binderName b') $
        Pi <$> (PiType (PiBinder b' ty' arr) <$> substM eff <*> simplifyAtom resultTy)
  TabPi (TabPiType (b:>IxType t d) resultTy) -> do
    t' <- simplifyAtom t
    d' <- simplifyAtom d
    withFreshBinder (getNameHint b) (IxType t' d') \b' -> do
      extendRenamer (b@>binderName b') $
        TabPi <$> (TabPiType (b':>IxType t' d') <$> simplifyAtom resultTy)
  DepPairTy _ -> substM atom
  DepPair x y ty -> DepPair <$> simplifyAtom x <*> simplifyAtom y <*> substM ty
  Con con -> Con <$> (inline traversePrimCon) simplifyAtom con
  TC tc -> TC <$> (inline traversePrimTC) simplifyAtom tc
  Eff eff -> Eff <$> substM eff
  PtrVar v -> PtrVar <$> substM v
  TypeCon sn dataDefName (DataDefParams arrParams) -> do
    dataDefName' <- substM dataDefName
    let (arrs, params) = unzip arrParams
    params' <- mapM simplifyAtom params
    return $ TypeCon sn dataDefName' (DataDefParams $ zip arrs params')
  DictCon d -> do
    d' <- substM d
    dTy <- getType d'
    DictCon <$> case dTy of
      DictTy (DictType "Ix" _ _) -> emitIxDictSpecialization d'
      _ -> return d'
  DictTy  t -> DictTy  <$> substM t
  RecordTy _ -> substM atom >>= cheapNormalize >>= \atom' -> case atom' of
    StaticRecordTy items -> StaticRecordTy <$> dropSubst (mapM simplifyAtom items)
    _ -> error $ "Failed to simplify a record with a dynamic label: " ++ pprint atom'
  VariantTy (Ext items ext) -> VariantTy <$> do
    items' <- mapM simplifyAtom items
    ext' <- liftM fromExtLabeledItemsE $ substM $ ExtLabeledItemsE $ Ext NoLabeledItems ext
    return $ prefixExtLabeledItems items' ext'
  LabeledRow elems -> substM elems >>= \elems' -> case fromFieldRowElems elems' of
    [StaticFields items] -> do
      items' <- dropSubst $ mapM simplifyAtom items
      return $ LabeledRow $ fieldRowElemsFromList [StaticFields items']
    []                   -> return $ LabeledRow $ fieldRowElemsFromList []
    _ -> error "Failed to simplify a labeled row"
  ACase e alts rTy   -> do
    e' <- simplifyAtom e
    case trySelectBranch e' of
      Just (i, arg) -> do
        Abs b body <- return $ alts !! i
        extendSubst (b @> SubstVal arg) $ simplifyAtom body
      Nothing -> do
        rTy' <- simplifyAtom rTy
        alts' <- forM alts \(Abs b body) -> do
          bTy' <- simplifyAtom $ binderType b
          buildAbs (getNameHint b) bTy' \xs ->
            extendSubst (b @> Rename xs) $
              simplifyAtom body
        return $ ACase e' alts' rTy'
  ProjectElt i x -> do
    x' <- simplifyAtom x
    liftEnvReaderM $ normalizeProj i x'

simplifyVar :: CAtomName i -> SimplifyM i o (CAtom o)
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

-- Assumes first order, monormophic
simplifyLam
  :: LamExpr CoreIR i
  -> SimplifyM i o (LamExpr SimpIR o, Abs (Nest AtomNameBinder) (ReconstructAtom CoreIR) o)
simplifyLam (LamExpr bsTop body) = case bsTop of
  Nest (b:>ty) bs -> do
    ty'<- coreToSimpType =<< simplifyAtom ty
    withFreshBinder (getNameHint b) ty' \b' -> do
      extendSubst (b@>Rename (binderName b')) do
        (LamExpr bs' body', Abs bsRecon recon) <- simplifyLam $ LamExpr bs body
        return (LamExpr (Nest (b':>ty') bs') body', Abs (Nest b' bsRecon) recon)
  Empty -> do
    SimplifiedBlock body' recon <- buildSimplifiedBlock $ simplifyBlock body
    return (LamExpr Empty body', Abs Empty recon)

data SplitDataNonData n = SplitDataNonData
  { dataTy    :: SType n
  , nonDataTy :: CType n
  , toSplit   :: forall m l . (Fallible1 m, EnvReader m) => CAtom l -> m l (SAtom l, CAtom l)
  , fromSplit :: forall m l . (Fallible1 m, EnvReader m) => SAtom l -> CAtom l -> m l (CAtom l) }

-- bijection between that type and a (data, non-data) pair type.
splitDataComponents :: EnvReader m => CType n -> m n (SplitDataNonData n)
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
  ty -> isData ty >>= \case
    True -> return $ SplitDataNonData
      { dataTy = unsafeCoerceIRE ty
      , nonDataTy = UnitTy
      , toSplit = \x -> return (unsafeCoerceIRE x, UnitVal)
      , fromSplit = \x _ -> return (unsafeCoerceIRE x) }
    False -> return $ SplitDataNonData
      { dataTy = UnitTy
      , nonDataTy = ty
      , toSplit = \x -> return (UnitVal, x)
      , fromSplit = \_ x -> return x }
{-# SPECIALIZE splitDataComponents :: CType o -> SimplifyM i o (SplitDataNonData o) #-}

buildSimplifiedBlock
  :: (forall o'. (Emits o', DExt o o') => SimplifyM i o' (CAtom o'))
  -> SimplifyM i o (SimplifiedBlock o)
buildSimplifiedBlock cont = do
  declsResult <- buildScoped cont
  (declsResult', recon) <- refreshAbs declsResult \decls result -> do
    testIfDataAtom result >>= \case
      Just dataResult -> return (Abs decls dataResult, IdentityRecon)
      Nothing -> do
        (newResult, reconAbs) <- telescopicCapture (toScopeFrag decls) result
        return (Abs decls newResult, LamRecon reconAbs)
  block <- makeBlockFromDecls declsResult'
  return $ SimplifiedBlock block recon

simplifyRecordVariantOp :: Emits o => RecordVariantOp (CAtom o) -> SimplifyM i o (CAtom o)
simplifyRecordVariantOp op = case op of
  RecordCons left right -> getType left >>= \case
    StaticRecordTy leftTys -> getType right >>= \case
      StaticRecordTy rightTys -> do
        -- Unpack, then repack with new arguments (possibly in the middle).
        leftList <- getUnpacked left
        let leftItems = restructure leftList leftTys
        rightList <- getUnpacked right
        let rightItems = restructure rightList rightTys
        return $ Record (leftTys <> rightTys) $ toList $ leftItems <> rightItems
      _ -> error "not a record"
    _ -> error "not a record"
  RecordConsDynamic ~(Con (LabelCon l)) val rec -> do
    valTy <- getType val
    getType rec >>= \case
      StaticRecordTy itemTys -> do
        itemList <- getUnpacked rec
        let items = restructure itemList itemTys
        return $ Record (labeledSingleton l valTy <> itemTys) $
          toList $ labeledSingleton l val <> items
      _ -> error "not a record"
  RecordSplit f full -> getType full >>= \case
    StaticRecordTy fullTys -> case f of
      LabeledRow f' | [StaticFields fields] <- fromFieldRowElems f' -> do
        -- Unpack, then repack into two pieces.
        fullList <- getUnpacked full
        let fullItems = restructure fullList fullTys
        let (_, remaining) = splitLabeledItems fields fullTys
        let (left, right) = splitLabeledItems fields fullItems
        return $ PairVal (Record fields    (toList left ))
                         (Record remaining (toList right))
      _ -> error "failed to simplifiy a field row"
    _ -> error "not a record"
  RecordSplitDynamic ~(Con (LabelCon l)) rec ->
    getType rec >>= \case
      StaticRecordTy itemTys -> do
        itemList <- getUnpacked rec
        let items = restructure itemList itemTys
        let (val, rest) = splitLabeledItems (labeledSingleton l ()) items
        let (_, otherItemTys) = splitLabeledItems (labeledSingleton l ()) itemTys
        return $ PairVal (head $ toList val) $
          Record otherItemTys $ toList rest
      _ -> error "not a record"
  VariantLift leftTys' right' -> injectCore <$> do
    leftTys <- mapM coreToSimpAtom leftTys'
    right <- coreToSimpAtom right'
    getType right >>= \case
      VariantTy (NoExt rightTys) -> do
        let fullTys = leftTys <> rightTys
        let fullRow = NoExt fullTys
        let fullLabels = toList $ reflectLabels fullTys
        let labels = toList $ reflectLabels rightTys
        -- Emit a case statement (ordered by the arg type) that lifts the type.
        buildCase right (VariantTy fullRow) \caseIdx v -> do
          -- TODO: This is slow! Optimize this! We keep searching through lists all the time!
          let (label, i) = labels !! caseIdx
          let idx = fromJust $ elemIndex (label, i + length (lookupLabel leftTys label)) fullLabels
          let fullRow'@(NoExt fullRowItems') = fromExtLabeledItemsE $ sink $ ExtLabeledItemsE fullRow
          return $ Con $ Newtype (VariantTy fullRow') $ SumVal (toList fullRowItems') idx v
      _ -> error "not a variant"
  VariantSplit leftTys' full' -> injectCore <$> do
    leftTys <- mapM coreToSimpAtom leftTys'
    full <- coreToSimpAtom full'
    getType full >>= \case
      VariantTy (NoExt fullTys) -> do
        -- TODO: This is slow! Optimize this! We keep searching through lists all the time!
        -- Emit a case statement (ordered by the arg type) that splits into the
        -- appropriate piece, changing indices as needed.
        resTy@(SumTy resTys) <- getType $ ComposeE $ VariantSplit leftTys full
        let (_, rightTys) = splitLabeledItems leftTys fullTys
        let fullLabels = toList $ reflectLabels fullTys
        let leftLabels = toList $ reflectLabels leftTys
        let rightLabels = toList $ reflectLabels rightTys
        buildCase full resTy \caseIdx v -> do
          let (label, i) = fullLabels !! caseIdx
          let labelIx labs li = fromJust $ elemIndex li labs
          let resTys' = sinkList resTys
          let lTy = sink $ VariantTy $ NoExt leftTys
          let rTy = sink $ VariantTy $ NoExt rightTys
          case leftTys `lookupLabel` label of
            [] -> return $ SumVal resTys' 1 $ Con $ Newtype rTy $
              SumVal (sinkList $ toList rightTys) (labelIx rightLabels (label, i)) v
            tys -> if i < length tys
              then return $ SumVal resTys' 0 $ Con $ Newtype lTy $
                SumVal (sinkList $ toList leftTys) (labelIx leftLabels (label, i)) v
              else return $ SumVal resTys' 1 $ Con $ Newtype rTy $
                SumVal (sinkList $ toList rightTys)
                       (labelIx rightLabels (label, i - length tys)) v
      _ -> error "Not a variant type"
  VariantMake ~ty@(VariantTy (NoExt tys)) label i v -> do
    let ix = fromJust $ elemIndex (label, i) $ toList $ reflectLabels tys
    return $ Con $ Newtype ty $ SumVal (toList tys) ix v
  SumToVariant c -> do
    resultTy <- getType $ ComposeE $ SumToVariant c
    return $ Con $ Newtype resultTy $ c

-- TODO: come up with a coherent strategy for ordering these various reductions
simplifyOp :: Emits o => PrimOp (CAtom o) -> SimplifyM i o (CAtom o)
simplifyOp op = case op of
  BinOp binop x' y' -> do
    x <- coreToSimpAtom x'
    y <- coreToSimpAtom y'
    injectCore <$> case binop of
      ISub -> isub x y
      IAdd -> iadd x y
      IMul -> imul x y
      IDiv -> idiv x y
      ICmp Less  -> ilt x y
      ICmp Equal -> ieq x y
      _ -> fallback
  MiscOp (Select c' x' y') -> do
    c <- coreToSimpAtom c'
    x <- coreToSimpAtom x'
    y <- coreToSimpAtom y'
    injectCore <$> select c x y
  MiscOp (ShowAny x) -> dropSubst $ showAny x >>= simplifyBlock
  _ -> injectCore <$> fallback
  where
    fallback = do
      op' <- (inline traversePrimOp) coreToSimpAtom op
      liftEnvReaderM (peepholeOp op') >>= \case
        Left  a   -> return a
        Right op'' -> emitOp op''

pattern IdentityReconAbs :: Abs binder (ReconstructAtom CoreIR) n
pattern IdentityReconAbs <- Abs _ IdentityRecon

projectDictMethod :: Emits o => CAtom o -> Int -> SimplifyM i o (CAtom o)
projectDictMethod d i = do
  cheapNormalize d >>= \case
    DictCon (InstanceDict instanceName args) -> dropSubst do
      args' <- mapM simplifyAtom args
      InstanceDef _ bs _ body <- lookupInstanceDef instanceName
      let InstanceBody _ methods = body
      let method = methods !! i
      extendSubst (bs@@>(SubstVal <$> args')) $
        simplifyBlock method
    Con (ExplicitDict _ method) -> do
      case i of
        0 -> return method
        _ -> error "ExplicitDict only supports single-method classes"
    DictCon (ExplicitMethods sd params) -> do
      -- We don't produce the specialized methods until after simplification. So
      -- during simplification we can't be sure that the second field of
      -- `SpecializedDict` will be non-Nothing. Thus, we use the explicit
      -- definition instead.
      SpecializedDictBinding (SpecializedDict (Abs bs dict) _) <- lookupEnv sd
      dict' <- applySubst (bs @@> map SubstVal params) dict
      projectDictMethod dict' i
    DictCon (IxFin n) -> projectIxFinMethod (toEnum i) n
    d' -> error $ "Not a simplified dict: " ++ pprint d'

simplifyHof :: Emits o => NameHint -> Hof CoreIR i -> SimplifyM i o (CAtom o)
simplifyHof hint hof = case hof of
  For d ixDict lam -> do
    ixTy@(IxType _ ixDict') <- simplifyIxType =<< ixTyFromDict =<< substM ixDict
    (lam', Abs (UnaryNest b) recon) <- simplifyLam lam
    ans <- liftM Var $ emitHinted hint $ Hof $ For d ixDict' lam'
    case recon of
      IdentityRecon -> return $ injectCore ans
      LamRecon reconAbs -> liftCoreBuilder $
        buildTabLam noHint (injectCore ixTy) \i' -> do
          elt <- tabApp (injectCore $ sink ans) $ Var i'
          -- TODO Avoid substituting the body of `recon` twice (once
          -- for `applySubst` and once for `applyReconAbs`).  Maybe
          -- by making `applyReconAbs` run in a `SubstReader`?
          reconAbs' <- applyRename (b @> i') reconAbs
          applyReconAbs reconAbs' elt
  While body -> do
    SimplifiedBlock body' IdentityRecon <- buildSimplifiedBlock $ simplifyBlock body
    liftM Var $ emitHinted hint $ Hof $ While body'
  RunReader r lam -> do
    r' <- coreToSimpAtom =<< simplifyAtom r
    (lam', Abs b recon) <- simplifyLam lam
    ans <- emitHinted hint $ Hof $ RunReader r' lam'
    let recon' = ignoreHoistFailure $ hoist b recon
    applyRecon recon' $ Var ans
  RunWriter Nothing (BaseMonoid e combine) lam -> do
    e' <- coreToSimpAtom =<< simplifyAtom e
    (combine', IdentityReconAbs) <- simplifyLam combine
    (lam', Abs b recon) <- simplifyLam lam
    let hof' = Hof $ RunWriter Nothing (BaseMonoid e' combine') lam'
    (ans, w) <- fromPair =<< liftM Var (emitHinted hint hof')
    let recon' = ignoreHoistFailure $ hoist b recon
    ans' <- applyRecon recon' (injectCore ans)
    return $ PairVal ans' (injectCore w)
  RunWriter _ _ _ -> error "Shouldn't see a RunWriter with a dest in Simplify"
  RunState Nothing s lam -> do
    s' <- coreToSimpAtom =<< simplifyAtom s
    (lam', Abs b recon) <- simplifyLam lam
    resultPair <- emitHinted hint $ Hof $ RunState Nothing s' lam'
    (ans, sOut) <- fromPair $ Var resultPair
    let recon' = ignoreHoistFailure $ hoist b recon
    ans' <- applyRecon recon' (injectCore ans)
    return $ PairVal ans' (injectCore sOut)
  RunState _ _ _ -> error "Shouldn't see a RunState with a dest in Simplify"
  RunIO body -> do
    SimplifiedBlock body' recon <- buildSimplifiedBlock $ simplifyBlock body
    ans <- emitHinted hint $ Hof $ RunIO body'
    applyRecon recon $ Var ans
  RunInit body -> do
    SimplifiedBlock body' recon <- buildSimplifiedBlock $ simplifyBlock body
    ans <- emitHinted hint $ Hof $ RunInit body'
    applyRecon recon $ Var ans
  Linearize lam -> do
    (lam', IdentityReconAbs) <- local (const WillLinearize) $ simplifyLam lam
    linearize lam'
  Transpose lam -> do
    (lam'@(UnaryLamExpr (b:>ty) _), IdentityReconAbs) <- simplifyLam lam
    lamTransposed <- transpose lam'
    return $ Lam (injectIRE lamTransposed) LinArrow (Abs (b:>injectIRE ty) Pure)
  CatchException body-> do
    SimplifiedBlock body' IdentityRecon <- buildSimplifiedBlock $ simplifyBlock body
    block <- liftBuilder $ runSubstReaderT idSubst $
      buildBlock $ exceptToMaybeBlock $ body'
    result <- emitBlock block
    return $ injectCore result

simplifyBlock :: Emits o => CBlock i -> SimplifyM i o (CAtom o)
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

hasExceptions :: (EnvReader m, MonadFail1 m) => SExpr n -> m n Bool
hasExceptions expr = do
  (EffectRow effs t) <- getEffects expr
  case t of
    Nothing -> return $ ExceptionEffect `S.member` effs
    Just _  -> error "Shouldn't have tail left"

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
