-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Inference
  ( inferTopUDecl, checkTopUType, inferTopUExpr , generalizeDict, asTopBlock
  , UDeclInferenceResult (..), asFFIFunType) where

import Prelude hiding ((.), id)
import Control.Category
import Control.Applicative
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Reader
import Data.Either (partitionEithers)
import Data.Foldable (toList, asum)
import Data.Functor ((<&>))
import Data.List (sortOn)
import Data.Maybe (fromJust, fromMaybe, catMaybes)
import Data.Word
import qualified Data.HashMap.Strict as HM
import qualified Data.Map.Strict as M
import GHC.Generics (Generic (..))

import Builder
import CheapReduction
import CheckType
import Core
import Err
import IRVariants
import MonadUtil
import MTL1
import Name
import Subst
import PPrint
import QueryType
import Types.Core
import Types.Imp
import Types.Primitives
import Types.Source
import Types.Top
import qualified Types.OpNames as P
import Util hiding (group)

-- === Top-level interface ===

checkTopUType :: (Fallible1 m, TopLogger1 m, EnvReader m) => UType n -> m n (CType n)
checkTopUType ty = liftInfererM $ checkUType ty
{-# SCC checkTopUType #-}

inferTopUExpr :: (Fallible1 m, TopLogger1 m, EnvReader m) => UExpr n -> m n (TopBlock CoreIR n)
inferTopUExpr e = fst <$> (asTopBlock =<< liftInfererM (buildBlock $ bottomUp e))
{-# SCC inferTopUExpr #-}

data UDeclInferenceResult e n =
   UDeclResultDone (e n)  -- used for UDataDefDecl, UInterface and UInstance
 | UDeclResultBindName LetAnn (TopBlock CoreIR n) (Abs (UBinder (AtomNameC CoreIR)) e n)
 | UDeclResultBindPattern NameHint (TopBlock CoreIR n) (ReconAbs CoreIR e n)

inferTopUDecl :: (Mut n, Fallible1 m, TopBuilder m, HasNamesE e, TopLogger1 m)
              => UTopDecl n l -> e l -> m n (UDeclInferenceResult e n)
inferTopUDecl (UStructDecl tc def) result = do
  tc' <- emitBinding (getNameHint tc) $ TyConBinding Nothing (DotMethods mempty)
  def' <- liftInfererM $ extendRenamer (tc@>tc') $ inferStructDef def
  updateTopEnv $ UpdateTyConDef tc' def'
  UStructDef _ paramBs _ methods <- return def
  forM_ methods \(letAnn, methodName, methodDef) -> do
    method <- liftInfererM $ extendRenamer (tc@>tc') $
      inferDotMethod tc' (Abs paramBs methodDef)
    method' <- emitTopLet (getNameHint methodName) letAnn (Atom $ toAtom $ Lam method)
    updateTopEnv $ UpdateFieldDef tc' methodName (atomVarName method')
  UDeclResultDone <$> applyRename (tc @> tc') result
inferTopUDecl (UDataDefDecl def tc dcs) result = do
  tcDef@(TyConDef _ _ _ (ADTCons dataCons)) <- liftInfererM $ inferTyConDef def
  tc' <- emitBinding (getNameHint tcDef) $ TyConBinding (Just tcDef) (DotMethods mempty)
  dcs' <- forM (enumerate dataCons) \(i, dcDef) ->
    emitBinding (getNameHint dcDef) $ DataConBinding tc' i
  let subst = tc @> tc' <.> dcs @@> dcs'
  UDeclResultDone <$> applyRename subst result
inferTopUDecl (UInterface paramBs methodTys className methodNames) result = do
  let sn = getSourceName className
  let methodSourceNames = nestToList getSourceName methodNames
  classDef <- liftInfererM $ inferClassDef sn methodSourceNames paramBs methodTys
  className' <- emitBinding (getNameHint sn) $ ClassBinding classDef
  methodNames' <- forM (enumerate methodSourceNames) \(i, prettyName) -> do
    emitBinding (getNameHint prettyName) $ MethodBinding className' i
  let subst = className @> className' <.> methodNames @@> methodNames'
  UDeclResultDone <$> applyRename subst result
inferTopUDecl (UInstance className bs params methods maybeName expl) result = do
  let (InternalName _ _ className') = className
  def <- liftInfererM $ withRoleUBinders bs \(ZipB roleExpls bs') -> do
    ClassDef _ _ _ _ _ paramBinders _ _ <- lookupClassDef (sink className')
    params' <- checkInstanceParams paramBinders params
    body <- checkInstanceBody (sink className') params' methods
    return $ InstanceDef className' roleExpls bs' params' body
  UDeclResultDone <$> case maybeName of
    RightB UnitB  -> do
      instanceName <- emitInstanceDef def
      ClassDef _ builtinName _ _ _ _ _ _ <- lookupClassDef className'
      addInstanceSynthCandidate className' builtinName instanceName
      return result
    JustB instanceName' -> do
      instanceName <- emitInstanceDef def
      lam <- instanceFun instanceName expl
      instanceAtomName <- emitTopLet (getNameHint instanceName') PlainLet $ Atom lam
      applyRename (instanceName' @> atomVarName instanceAtomName) result
    _ -> error "impossible"
inferTopUDecl (ULocalDecl (WithSrcB _ decl)) result = case decl of
  UPass -> return $ UDeclResultDone result
  UExprDecl _ -> error "Shouldn't have this at the top level (should have become a command instead)"
  ULet letAnn p tyAnn rhs -> case p of
    WithSrcB _ (UPatBinder b) -> do
      block <- liftInfererM $ buildBlock do
        checkMaybeAnnExpr tyAnn rhs
      (topBlock, resultTy) <- asTopBlock block
      let letAnn' = considerInlineAnn letAnn resultTy
      return $ UDeclResultBindName letAnn' topBlock (Abs b result)
    _ -> do
      PairE block recon <- liftInfererM $ buildBlockInfWithRecon do
        val <- checkMaybeAnnExpr tyAnn rhs
        v <- emitDecl (getNameHint p) PlainLet $ Atom val
        bindLetPat p v do
          renameM result
      (topBlock, _) <- asTopBlock block
      return $ UDeclResultBindPattern (getNameHint p) topBlock recon
{-# SCC inferTopUDecl #-}

asTopBlock :: EnvReader m => CExpr n -> m n (TopBlock CoreIR n, CType n)
asTopBlock block = do
  let effs = getEffects block
  let ty = getType block
  return (TopLam False (PiType Empty (EffTy effs ty)) (LamExpr Empty block), ty)

getInstanceType :: EnvReader m => InstanceDef n -> m n (CorePiType n)
getInstanceType (InstanceDef className roleExpls bs params _) = liftEnvReaderM do
  refreshAbs (Abs bs (ListE params)) \bs' (ListE params') -> do
    className' <- sinkM className
    dTy <- toType <$> dictType className' params'
    return $ CorePiType ImplicitApp (snd <$> roleExpls) bs' $ EffTy Pure dTy

-- === Inferer monad ===

newtype SolverSubst n = SolverSubst { fromSolverSubst :: M.Map (CAtomName n) (CAtom n) }

emptySolverSubst :: SolverSubst n
emptySolverSubst = SolverSubst mempty

data InfState (n::S) = InfState
  { givens         :: Givens n
  , infEffects     :: EffectRow CoreIR n }

newtype InfererM (i::S) (o::S) (a:: *) = InfererM
  { runInfererM' :: SubstReaderT Name (ReaderT1 InfState (BuilderT CoreIR (ExceptT (State TypingInfo)))) i o a }
  deriving (Functor, Applicative, Monad, MonadFail, Alternative, Builder CoreIR,
            EnvExtender, ScopableBuilder CoreIR,
            ScopeReader, EnvReader, Fallible, Catchable, SubstReader Name)

type InfererCPSB  b i    o a = (forall o'. DExt o o' => b o o' -> InfererM i  o' a) -> InfererM i o a
type InfererCPSB2 b i i' o a = (forall o'. DExt o o' => b o o' -> InfererM i' o' a) -> InfererM i o a

liftInfererM :: (EnvReader m, TopLogger1 m, Fallible1 m) => InfererM n n a -> m n a
liftInfererM cont = do
  (ansExcept, typeInfo) <- liftInfererMPure cont
  emitLog $ Outputs [SourceInfo $ SITypingInfo typeInfo]
  liftExcept ansExcept
{-# INLINE liftInfererM #-}

liftInfererMPure :: EnvReader m => InfererM n n a -> m n (Except a, TypingInfo)
liftInfererMPure cont = do
  ansM <- liftBuilderT $ runReaderT1 emptyInfState $ runSubstReaderT idSubst $ runInfererM' cont
  return $ runState (runExceptT ansM) mempty
 where
  emptyInfState :: InfState n
  emptyInfState = InfState (Givens HM.empty) Pure
{-# INLINE liftInfererMPure #-}

-- === Solver monad ===

type Solution = PairE CAtomName CAtom
newtype SolverDiff (n::S) = SolverDiff (RListE Solution n)
  deriving (MonoidE, SinkableE, HoistableE, RenameE)
type SolverM i o a = DiffStateT1 SolverSubst SolverDiff (InfererM i) o a

type Zonkable e = (HasNamesE e, SubstE AtomSubstVal e)

liftSolverM :: SolverM i o a -> InfererM i o a
liftSolverM cont = fst <$> runDiffStateT1 emptySolverSubst cont

solverFail :: SolverM i o a
solverFail = empty

zonk :: Zonkable e => e n -> SolverM i n (e n)
zonk e = do
  s <- getDiffState
  applySolverSubst s e
{-# INLINE zonk #-}

zonkStuck :: CStuck n -> SolverM i n (CAtom n)
zonkStuck stuck = do
  solverSubst <- getDiffState
  Distinct <- getDistinct
  env <- unsafeGetEnv
  let subst = newSubst (lookupSolverSubst solverSubst)
  return $ substStuck (env, subst) stuck

applySolverSubst :: (EnvReader m, Zonkable e) => SolverSubst n -> e n -> m n (e n)
applySolverSubst subst e = do
  Distinct <- getDistinct
  env <- unsafeGetEnv
  return $ fmapNames env (lookupSolverSubst subst) e
{-# INLINE applySolverSubst #-}

withFreshBinderInf :: NameHint -> Explicitness -> CType o -> InfererCPSB CBinder i o a
withFreshBinderInf hint expl ty cont =
  withFreshBinder hint ty \b -> do
    givens <- case expl of
      Inferred _ (Synth _) -> return [toAtom $ binderVar b]
      _ -> return []
    extendGivens givens $ cont b
{-# INLINE withFreshBinderInf #-}

withFreshBindersInf
  :: (SinkableE e, RenameE e)
  => [Explicitness] -> Abs (Nest CBinder) e o
  -> (forall o'. DExt o o' => Nest CBinder o o' -> e o' -> InfererM i  o' a)
  -> InfererM i o a
withFreshBindersInf explsTop (Abs bsTop e) contTop =
  runSubstReaderT idSubst $ go explsTop bsTop \bs' -> do
    e' <- renameM e
    liftSubstReaderT $ contTop bs' e'
 where
  go :: [Explicitness] -> Nest CBinder ii ii'
     -> (forall o'. DExt o o' => Nest CBinder o o' -> SubstReaderT Name (InfererM i) ii'  o' a)
     -> SubstReaderT Name (InfererM i) ii o a
  go [] Empty cont = withDistinct $ cont Empty
  go (expl:expls) (Nest b bs) cont = do
    ty <- renameM $ binderType b
    SubstReaderT \s -> withFreshBinderInf (getNameHint b) expl ty \b' -> do
      runSubstReaderT (sink s) $ extendSubst (b@>binderName b') do
        go expls bs \bs' -> cont (Nest b' bs')
  go _ _ _ = error "zip error"
{-# INLINE withFreshBindersInf #-}

withInferenceVar
  :: (Zonkable e, Emits o, ToBinding binding (AtomNameC CoreIR)) => NameHint -> binding o
  -> (forall o'. (Emits o', DExt o o') => CAtomName o' -> SolverM i o' (e o', CAtom o'))
  -> SolverM i o (e o)
withInferenceVar hint binding cont = diffStateT1 \s -> do
  declsAndAns <- withFreshBinder hint binding \(b:>_) -> do
    hardHoist b <$> buildScoped do
      v <- sinkM $ binderName b
      s' <- sinkM s
      (PairE ans soln, diff) <- runDiffStateT1 s' do
        toPairE <$> cont v
      let subst = SolverSubst $ M.singleton v soln
      ans' <- applySolverSubst subst ans
      diff' <- applySolutionToDiff subst v diff
      return $ PairE ans' diff'
  fromPairE <$> emitDecls declsAndAns
 where
  applySolutionToDiff :: SolverSubst n -> CAtomName n -> SolverDiff n -> InfererM i n (SolverDiff n)
  applySolutionToDiff subst vSoln (SolverDiff (RListE (ReversedList cs))) = do
    SolverDiff . RListE . ReversedList <$> forMFilter cs \(PairE v x) ->
      case v == vSoln of
        True -> return Nothing
        False -> Just . PairE v <$> applySolverSubst subst x
{-# INLINE withInferenceVar #-}

withFreshUnificationVar
  :: (Zonkable e, Emits o) => SrcId -> InfVarDesc -> Kind CoreIR o
  -> (forall o'. (Emits o', DExt o o') => CAtomVar o' -> SolverM i o' (e o'))
  -> SolverM i o (e o)
withFreshUnificationVar sid desc k cont = do
  withInferenceVar "_unif_" (InfVarBound k) \v -> do
    ans <- toAtomVar v >>= cont
    soln <- (M.lookup v <$> fromSolverSubst <$> getDiffState) >>= \case
      Just soln ->  return soln
      Nothing -> throw sid $ AmbiguousInferenceVar (pprint v) (pprint k) desc
    return (ans, soln)
{-# INLINE withFreshUnificationVar #-}

withFreshUnificationVarNoEmits
  :: (Zonkable e) => SrcId -> InfVarDesc -> Kind CoreIR o
  -> (forall o'. (DExt o o') => CAtomVar o' -> SolverM i o' (e o'))
  -> SolverM i o (e o)
withFreshUnificationVarNoEmits sid desc k cont = diffStateT1 \s -> do
  Abs Empty resultAndDiff <- buildScoped do
    liftM toPairE $ runDiffStateT1 (sink s) $
      withFreshUnificationVar sid desc (sink k) cont
  return $ fromPairE resultAndDiff

withFreshDictVar
  :: (Zonkable e, Emits o) => CType o
  -- This tells us how to synthesize the dict. The supplied CType won't contain inference vars.
  -> (forall o'. (          DExt o o') => CType o' -> SolverM i o' (CAtom o'))
  -> (forall o'. (Emits o', DExt o o') => CAtom o' -> SolverM i o' (e o'))
  -> SolverM i o (e o)
withFreshDictVar dictTy synthIt cont = hasInferenceVars dictTy >>= \case
  False -> withDistinct $ synthIt dictTy >>= cont
  True -> withInferenceVar "_dict_" (DictBound dictTy) \v -> do
    ans <- cont =<< (toAtom <$> toAtomVar v)
    dictTy' <- zonk $ sink dictTy
    dict <- synthIt dictTy'
    return (ans, dict)
{-# INLINE withFreshDictVar #-}

withFreshDictVarNoEmits
  :: (Zonkable e) => CType o
  -- This tells us how to synthesize the dict. The supplied CType won't contain inference vars.
  -> (forall o'. (DExt o o') => CType o' -> SolverM i o' (CAtom o'))
  -> (forall o'. (DExt o o') => CAtom o' -> SolverM i o' (e o'))
  -> SolverM i o (e o)
withFreshDictVarNoEmits dictTy synthIt cont = diffStateT1 \s -> do
  Abs Empty resultAndDiff <- buildScoped do
    liftM toPairE $ runDiffStateT1 (sink s) $
      withFreshDictVar (sink dictTy) synthIt cont
  return $ fromPairE resultAndDiff
{-# INLINE withFreshDictVarNoEmits #-}

withDict
  :: (Zonkable e, Emits o) => SrcId -> CType o
  -> (forall o'. (Emits o', DExt o o') => CAtom o' -> SolverM i o' (e o'))
  -> SolverM i o (e o)
withDict sid dictTy cont = withFreshDictVar dictTy
   (\dictTy' -> lift11 $ trySynthTerm sid dictTy' Full)
   cont
{-# INLINE withDict#-}

addConstraint :: CAtomName o -> CAtom o -> SolverM i o ()
addConstraint v ty = updateDiffStateM (SolverDiff $ RListE $ toSnocList [PairE v ty])
{-# INLINE addConstraint #-}

getInfState :: InfererM i o (InfState o)
getInfState = InfererM $ liftSubstReaderT ask
{-# INLINE getInfState #-}

withInfState :: (InfState o -> InfState o) -> InfererM i o a -> InfererM i o a
withInfState f cont = InfererM $ local f (runInfererM' cont)
{-# INLINE withInfState #-}

withAllowedEffects :: EffectRow CoreIR o -> InfererM i o a -> InfererM i o a
withAllowedEffects effs cont = withInfState (\(InfState g _) -> InfState g effs) cont
{-# INLINE withAllowedEffects #-}

getTypeAndEmit :: HasType CoreIR e => SrcId -> e o -> InfererM i o (e o)
getTypeAndEmit sid e = do
  emitExprType sid (getType e)
  return e

emitExprType :: SrcId -> CType any -> InfererM i o ()
emitExprType sid ty = emitTypeInfo sid $ ExprType $ pprint ty

emitTypeInfo :: SrcId -> TypeInfo -> InfererM i o ()
emitTypeInfo sid tyInfo =
  InfererM $ liftSubstReaderT $ lift11 $ lift1 $ lift $
    modify (<> TypingInfo (M.singleton sid tyInfo))

withReducibleEmissions
  :: (HasNamesE e, SubstE AtomSubstVal e, ToErr err)
  => SrcId -> err
  -> (forall o' . (Emits o', DExt o o') => InfererM i o' (e o'))
  -> InfererM i o (e o)
withReducibleEmissions sid msg cont = do
  withDecls <- buildScoped cont
  reduceWithDecls withDecls >>= \case
    Just t -> return t
    _ -> throw sid msg
{-# INLINE withReducibleEmissions #-}

-- === actual inference pass ===

data RequiredTy (n::S) =
   Check (CType n)
 | Infer
   deriving Show

data PartialPiType (n::S) where
  PartialPiType
    :: AppExplicitness -> [Explicitness]
    -> Nest CBinder n l
    ->   EffectRow CoreIR l
    ->   RequiredTy l
    -> PartialPiType n

data PartialType (n::S) =
   PartialType (PartialPiType n)
 | FullType (CType n)

checkOrInfer :: Emits o => RequiredTy o -> UExpr i -> InfererM i o (CAtom o)
checkOrInfer reqTy expr = case reqTy of
  Infer -> bottomUp expr
  Check t -> topDown t expr

topDown :: forall i o. Emits o => CType o -> UExpr i -> InfererM i o (CAtom o)
topDown ty uexpr = topDownPartial (typeAsPartialType ty) uexpr

topDownPartial :: Emits o => PartialType o -> UExpr i -> InfererM i o (CAtom o)
topDownPartial partialTy exprWithSrc@(WithSrcE sid expr) =
  case partialTy of
    PartialType partialPiTy -> case expr of
      ULam lam -> toAtom <$> Lam <$> checkULamPartial partialPiTy sid lam
      _ -> toAtom <$> Lam <$> etaExpandPartialPi partialPiTy \resultTy explicitArgs -> do
        expr' <- bottomUpExplicit exprWithSrc
        dropSubst $ checkOrInferApp sid sid expr' explicitArgs [] resultTy
    FullType ty -> topDownExplicit ty exprWithSrc

-- Creates a lambda for all args and returns (via CPA) the explicit args
etaExpandPartialPi
  :: PartialPiType o
  -> (forall o'. (Emits o', DExt o o') => RequiredTy o' -> [CAtom o'] -> InfererM i o' (CAtom o'))
  -> InfererM i o (CoreLamExpr o)
etaExpandPartialPi (PartialPiType appExpl expls bs effs reqTy) cont = do
  withFreshBindersInf expls (Abs bs (PairE effs reqTy)) \bs' (PairE effs' reqTy') -> do
    let args = zip expls (toAtom <$> bindersVars bs')
    explicits <- return $ catMaybes $ args <&> \case
      (Explicit, arg) -> Just arg
      _ -> Nothing
    withAllowedEffects effs' do
      body <- buildBlock $ cont (sink reqTy') (sink <$> explicits)
      let piTy = CorePiType appExpl expls bs' (EffTy effs' $ getType body)
      return $ CoreLamExpr piTy $ LamExpr bs' body

-- Doesn't introduce implicit pi binders or dependent pairs
topDownExplicit :: forall i o. Emits o => CType o -> UExpr i -> InfererM i o (CAtom o)
topDownExplicit reqTy exprWithSrc@(WithSrcE sid expr) = emitExprType sid reqTy >> case expr of
  ULam lamExpr -> case reqTy of
    TyCon (Pi piTy) -> toAtom <$> Lam <$> checkULam sid lamExpr piTy
    _       -> throw sid $ UnexpectedTerm "lambda" (pprint reqTy)
  UFor dir uFor@(UForExpr b _) -> case reqTy of
    TyCon (TabPi tabPiTy) -> do
      lam@(UnaryLamExpr b' _) <- checkUForExpr sid uFor tabPiTy
      ixTy <- asIxType (getSrcId b) $ binderType b'
      emitHof $ For dir ixTy lam
    _ -> throw sid $ UnexpectedTerm "`for` expression" (pprint reqTy)
  UApp f posArgs namedArgs -> do
    f' <- bottomUpExplicit f
    checkOrInferApp sid (getSrcId f) f' posArgs namedArgs (Check reqTy)
  UDepPair lhs rhs -> case reqTy of
    TyCon (DepPairTy ty@(DepPairType _ (_ :> lhsTy) _)) -> do
      lhs' <- checkSigmaDependent lhs (FullType lhsTy)
      rhsTy <- instantiate ty [lhs']
      rhs' <- topDown rhsTy rhs
      return $ toAtom $ DepPair lhs' rhs' ty
    _ -> throw sid $ UnexpectedTerm "dependent pair" (pprint reqTy)
  UCase scrut alts -> do
    scrut' <- bottomUp scrut
    let scrutTy = getType scrut'
    alts' <- mapM (checkCaseAlt (Check reqTy) scrutTy) alts
    buildSortedCase scrut' alts' reqTy
  UDo block -> withBlockDecls block \result -> topDownExplicit (sink reqTy) result
  UTabCon xs -> do
    case reqTy of
      TyCon (TabPi tabPiTy) -> checkTabCon tabPiTy sid xs
      _ -> throw sid $ UnexpectedTerm "table constructor" (pprint reqTy)
  UNatLit x -> fromNatLit sid x reqTy
  UIntLit x -> fromIntLit sid x reqTy
  UPrim UTuple xs -> case reqTy of
    TyKind -> toAtom . ProdType <$> mapM checkUType xs
    TyCon (ProdType reqTys) -> do
      when (length reqTys /= length xs) $ throw sid $ TupleLengthMismatch (length reqTys) (length xs)
      toAtom <$> ProdCon <$> forM (zip reqTys xs) \(reqTy', x) -> topDown reqTy' x
    _ -> throw sid $ UnexpectedTerm "tuple" (pprint reqTy)
  UFieldAccess _ _ -> infer
  UVar _           -> infer
  UTypeAnn _ _     -> infer
  UTabApp _ _      -> infer
  UFloatLit _      -> infer
  UPrim _ _        -> infer
  ULit _           -> infer
  UPi _            -> infer
  UTabPi _         -> infer
  UDepPairTy _     -> infer
  UHole -> throw sid InferHoleErr
  where
    infer :: InfererM i o (CAtom o)
    infer = do
      sigmaAtom <- maybeInterpretPunsAsTyCons (Check reqTy) =<< bottomUpExplicit exprWithSrc
      instantiateSigma sid (Check reqTy) sigmaAtom

bottomUp :: Emits o => UExpr i -> InfererM i o (CAtom o)
bottomUp expr = bottomUpExplicit expr >>= instantiateSigma (getSrcId expr) Infer

-- Doesn't instantiate implicit args
bottomUpExplicit :: Emits o => UExpr i -> InfererM i o (SigmaAtom o)
bottomUpExplicit (WithSrcE sid expr) = getTypeAndEmit sid =<< case expr of
  UVar ~(InternalName _ sn v) ->  do
    v' <- renameM v
    ty <- getUVarType v'
    return $ SigmaUVar sn ty v'
  ULit l -> return $ SigmaAtom Nothing $ Con $ Lit l
  UFieldAccess x (WithSrc _ field) -> do
    x' <- bottomUp x
    ty <- return $ getType x'
    fields <- getFieldDefs sid ty
    case M.lookup field fields of
      Just def -> case def of
        FieldProj i -> SigmaAtom Nothing <$> projectField i x'
        FieldDotMethod method (TyConParams _ params) -> do
          method' <- toAtomVar method
          resultTy <- partialAppType (getType method') (params ++ [x'])
          return $ SigmaPartialApp resultTy (toAtom method') (params ++ [x'])
      Nothing -> throw sid $ CantFindField (pprint field) (pprint ty) (map pprint $ M.keys fields)
  ULam lamExpr -> SigmaAtom Nothing <$> toAtom <$> inferULam lamExpr
  UFor dir uFor@(UForExpr b _) -> do
    lam@(UnaryLamExpr b' _) <- inferUForExpr uFor
    ixTy <- asIxType (getSrcId b) $ binderType b'
    liftM (SigmaAtom Nothing) $ emitHof $ For dir ixTy lam
  UApp f posArgs namedArgs -> do
    f' <- bottomUpExplicit f
    SigmaAtom Nothing <$> checkOrInferApp sid (getSrcId f) f' posArgs namedArgs Infer
  UTabApp tab args -> do
    tab' <- bottomUp tab
    SigmaAtom Nothing <$> inferTabApp (getSrcId tab) tab' args
  UPi (UPiExpr bs appExpl effs ty) -> do
    -- TODO: check explicitness constraints
    withUBinders bs \(ZipB expls bs') -> do
      effTy' <- EffTy <$> checkUEffRow effs <*> checkUType ty
      return $ SigmaAtom Nothing $ toAtom $
        Pi $ CorePiType appExpl expls bs' effTy'
  UTabPi (UTabPiExpr b ty) -> do
    Abs b' ty' <- withUBinder b \(WithAttrB _ b') ->
      liftM (Abs b') $ checkUType ty
    d <- getIxDict (getSrcId b) $ binderType b'
    let piTy = TabPiType d b' ty'
    return $ SigmaAtom Nothing $ toAtom $ TabPi piTy
  UDepPairTy (UDepPairType expl b rhs) -> do
    withUBinder b \(WithAttrB _ b') -> do
      rhs' <- checkUType rhs
      return $ SigmaAtom Nothing $ toAtom $ DepPairTy $ DepPairType expl b' rhs'
  UDepPair _ _ -> throw sid InferDepPairErr
  UCase scrut (alt:alts) -> do
    scrut' <- bottomUp scrut
    let scrutTy = getType scrut'
    alt'@(IndexedAlt _ altAbs) <- checkCaseAlt Infer scrutTy alt
    Abs b ty <- liftEnvReaderM $ refreshAbs altAbs \b body -> do
      return $ Abs b (getType body)
    resultTy <- liftHoistExcept sid $ hoist b ty
    alts' <- mapM (checkCaseAlt (Check resultTy) scrutTy) alts
    SigmaAtom Nothing <$> buildSortedCase scrut' (alt':alts') resultTy
  UCase _ [] -> throw sid InferEmptyCaseEff
  UDo block -> withBlockDecls block \result -> bottomUpExplicit result
  UTabCon xs -> liftM (SigmaAtom Nothing) $ inferTabCon sid xs
  UTypeAnn val ty -> do
    ty' <- checkUType ty
    liftM (SigmaAtom Nothing) $ topDown ty' val
  UPrim UTuple xs -> do
    xs' <- forM xs \x -> bottomUp x
    return $ SigmaAtom Nothing $ Con $ ProdCon xs'
  UPrim UMonoLiteral [WithSrcE _ l] -> case l of
    UIntLit x -> return $ SigmaAtom Nothing $ Con $ Lit $ Int32Lit $ fromIntegral x
    UNatLit x -> return $ SigmaAtom Nothing $ Con $ Lit $ Word32Lit $ fromIntegral x
    _ -> throwInternal "argument to %monoLit must be a literal"
  UPrim UExplicitApply (f:xs) -> do
    f' <- bottomUpExplicit f
    xs' <- mapM bottomUp xs
    SigmaAtom Nothing <$> applySigmaAtom sid f' xs'
  UPrim UProjNewtype [x] -> do
    x' <- bottomUp x >>= unwrapNewtype
    return $ SigmaAtom Nothing x'
  UPrim prim xs -> do
    xs' <- forM xs \x -> do
      inferPrimArg x >>= \case
        Stuck _ (Var v) -> lookupAtomName (atomVarName v) >>= \case
          LetBound (DeclBinding _ (Atom e)) -> return e
          _ -> return $ toAtom v
        x' -> return x'
    liftM (SigmaAtom Nothing) $ matchPrimApp prim xs'
  UNatLit l -> liftM (SigmaAtom Nothing) $ fromNatLit sid l NatTy
  UIntLit l -> liftM (SigmaAtom Nothing) $ fromIntLit sid l (BaseTy $ Scalar Int32Type)
  UFloatLit x -> return $ SigmaAtom Nothing $ Con $ Lit  $ Float32Lit $ realToFrac x
  UHole -> throw sid InferHoleErr

expectEq :: (PrettyE e, AlphaEqE e) => SrcId -> e o -> e o -> InfererM i o ()
expectEq sid reqTy actualTy = alphaEq reqTy actualTy >>= \case
  True -> return ()
  False -> throw sid $ TypeMismatch (pprint reqTy) (pprint actualTy)
{-# INLINE expectEq #-}

fromIntLit :: Emits o => SrcId -> Int -> CType o -> InfererM i o (CAtom o)
fromIntLit sid x ty = do
  let litVal = Con $ Lit $ Int64Lit $ fromIntegral x
  applyFromLiteralMethod sid ty "from_integer" litVal

fromNatLit :: Emits o => SrcId -> Word64 -> CType o -> InfererM i o (CAtom o)
fromNatLit sid x ty = do
  let litVal = Con $ Lit $ Word64Lit $ fromIntegral x
  applyFromLiteralMethod sid ty "from_unsigned_integer" litVal

instantiateSigma :: Emits o => SrcId -> RequiredTy o -> SigmaAtom o -> InfererM i o (CAtom o)
instantiateSigma sid reqTy sigmaAtom = case sigmaAtom of
  SigmaUVar _ _ _ -> case getType sigmaAtom of
    TyCon (Pi (CorePiType ImplicitApp expls bs (EffTy _ resultTy))) -> do
      bsConstrained <- buildConstraints (Abs bs resultTy) \_ resultTy' -> do
        case reqTy of
          Infer -> return []
          Check reqTy' -> return [TypeConstraint sid (sink reqTy') resultTy']
      args <- inferMixedArgs @UExpr sid fDesc expls bsConstrained ([], [])
      applySigmaAtom sid sigmaAtom args
    _ -> fallback
  _ -> fallback
  where
    fallback = forceSigmaAtom sid sigmaAtom >>= matchReq sid reqTy
    fDesc = getSourceName sigmaAtom

matchReq :: Ext o o' => SrcId -> RequiredTy o -> CAtom o' -> InfererM i o' (CAtom o')
matchReq sid (Check reqTy) x = do
  reqTy' <- sinkM reqTy
  return x <* expectEq sid reqTy' (getType x)
matchReq _ Infer x = return x
{-# INLINE matchReq #-}

forceSigmaAtom :: Emits o => SrcId -> SigmaAtom o -> InfererM i o (CAtom o)
forceSigmaAtom sid sigmaAtom = case sigmaAtom of
  SigmaAtom _ x -> return x
  SigmaUVar _ _ v -> case v of
    UAtomVar v' -> inlineTypeAliases v'
    _ -> applySigmaAtom sid sigmaAtom []
  SigmaPartialApp _ _ _ -> error "not implemented" -- better error message?

withBlockDecls
  :: (Emits o, Zonkable e)
  => UBlock i
  -> (forall i' o'. (Emits o', DExt o o') => UExpr i' -> InfererM i' o' (e o'))
  -> InfererM i o (e o)
withBlockDecls (WithSrcE _ (UBlock declsTop result)) contTop =
  go declsTop $ contTop result where
  go :: (Emits o, Zonkable e)
     => Nest UDecl i i'
     -> (forall o'. (Emits o', DExt o o') => InfererM i' o' (e o'))
     -> InfererM i  o (e o)
  go decls cont = case decls of
    Empty -> withDistinct cont
    Nest d ds -> withUDecl d $ go ds $ cont

withUDecl
  :: (Emits o, Zonkable e)
  => UDecl i i'
  -> (forall o'. (Emits o', DExt o o') => InfererM i' o' (e o'))
  -> InfererM i  o (e o)
withUDecl (WithSrcB _ d) cont = case d of
  UPass -> withDistinct cont
  UExprDecl e -> withDistinct $ bottomUp e >> cont
  ULet letAnn p ann rhs -> do
    val <- checkMaybeAnnExpr ann rhs
    let letAnn' = considerInlineAnn letAnn (getType val)
    var <- emitDecl (getNameHint p) letAnn' $ Atom val
    bindLetPat p var cont

considerInlineAnn :: LetAnn -> CType n -> LetAnn
considerInlineAnn PlainLet TyKind = InlineLet
considerInlineAnn PlainLet (TyCon (Pi (CorePiType _ _ _ (EffTy Pure TyKind)))) = InlineLet
considerInlineAnn ann _ = ann

applyFromLiteralMethod
  :: Emits n => SrcId -> CType n -> SourceName -> CAtom n -> InfererM i n (CAtom n)
applyFromLiteralMethod sid resultTy methodName litVal =
  lookupSourceMap methodName >>= \case
    Nothing -> error $ "prelude function not found: " ++ pprint methodName
    Just ~(UMethodVar methodName') -> do
      MethodBinding className _ <- lookupEnv methodName'
      dictTy <- toType <$> dictType className [toAtom resultTy]
      Just d <- toMaybeDict <$> trySynthTerm sid dictTy Full
      emit =<< mkApplyMethod d 0 [litVal]

-- atom that requires instantiation to become a rho type
data SigmaAtom n =
    SigmaAtom (Maybe SourceName) (CAtom n)
  | SigmaUVar SourceName (CType n) (UVar n)
  | SigmaPartialApp (CType n) (CAtom n) [CAtom n]
    deriving (Show)

-- XXX: this gives the type of the atom in the absence of other type information.
-- So it interprets struct names as data constructors rather than type constructors.
instance HasType CoreIR SigmaAtom where
  getType = \case
    SigmaAtom _ x -> getType x
    SigmaUVar _ ty _ -> ty
    SigmaPartialApp ty _ _ -> ty

instance HasSourceName (SigmaAtom n) where
  getSourceName = \case
    SigmaAtom sn _ -> case sn of
      Just sn' -> sn'
      Nothing  -> "<expr>"
    SigmaUVar sn _ _ -> sn
    SigmaPartialApp _ _ _ -> "<dot method>"

data FieldDef (n::S) =
   FieldProj Int
 | FieldDotMethod (CAtomName n) (TyConParams n)
   deriving (Show, Generic)

getFieldDefs :: SrcId -> CType n -> InfererM i n (M.Map FieldName' (FieldDef n))
getFieldDefs sid ty = case ty of
  StuckTy _ _ -> noFields
  TyCon con -> case con of
    NewtypeTyCon (UserADTType _ tyName params) -> do
      TyConBinding ~(Just tyDef) (DotMethods dotMethods) <- lookupEnv tyName
      instantiateTyConDef tyDef params >>= \case
        StructFields fields -> do
          let projFields = enumerate fields <&> \(i, (field, _)) ->
                [(FieldName field, FieldProj i), (FieldNum i, FieldProj i)]
          let methodFields = M.toList dotMethods <&> \(field, f) ->
                (FieldName field, FieldDotMethod f params)
          return $ M.fromList $ concat projFields ++ methodFields
        ADTCons _ -> noFields
    RefType _ valTy -> case valTy of
      RefTy _ _ -> noFields
      _ -> do
        valFields <- getFieldDefs sid valTy
        return $ M.filter isProj valFields
        where isProj = \case
                FieldProj _ -> True
                _ -> False
    ProdType ts -> return $ M.fromList $ enumerate ts <&> \(i, _) -> (FieldNum i, FieldProj i)
    TabPi _ -> noFields
    _ -> noFields
  where noFields = throw sid $ NoFields $ pprint ty

projectField :: Emits o => Int -> CAtom o -> InfererM i o (CAtom o)
projectField i x = case getType x of
  StuckTy _ _ -> bad
  TyCon con -> case con of
    ProdType _ -> proj i x
    NewtypeTyCon _ -> projectStruct i x
    RefType _ valTy -> case valTy of
      TyCon (ProdType _) -> getProjRef (ProjectProduct i) x
      TyCon (NewtypeTyCon _) -> projectStructRef i x
      _ -> bad
    _ -> bad
  where bad = error $ "bad projection: " ++ pprint (i, x)

class PrettyE e => ExplicitArg (e::E) where
  checkExplicitNonDependentArg :: Emits o => e i -> PartialType o -> InfererM i o (CAtom o)
  checkExplicitDependentArg    ::            e i -> PartialType o -> InfererM i o (CAtom o)
  inferExplicitArg :: Emits o => e i -> InfererM i o (CAtom o)
  isHole :: e n -> Bool
  explicitArgSrcId :: e n -> SrcId

instance ExplicitArg UExpr where
  checkExplicitDependentArg arg argTy = checkSigmaDependent arg argTy
  checkExplicitNonDependentArg arg argTy = topDownPartial argTy arg
  inferExplicitArg arg = bottomUp arg
  isHole = \case
    WithSrcE _ UHole -> True
    _ -> False
  explicitArgSrcId = getSrcId

instance ExplicitArg CAtom where
  checkExplicitDependentArg    = checkCAtom
  checkExplicitNonDependentArg = checkCAtom
  inferExplicitArg arg = renameM arg
  isHole _ = False
  explicitArgSrcId _ = rootSrcId

checkCAtom :: CAtom i -> PartialType o -> InfererM i o (CAtom o)
checkCAtom arg argTy = do
  arg' <- renameM arg
  case argTy of
    FullType argTy' -> expectEq rootSrcId argTy' (getType arg')
    PartialType _ -> return () -- TODO?
  return arg'

checkOrInferApp
  :: forall i o arg . (Emits o, ExplicitArg arg)
  => SrcId -> SrcId ->  SigmaAtom o -> [arg i] -> [(SourceName, arg i)]
  -> RequiredTy o -> InfererM i o (CAtom o)
checkOrInferApp appSrcId funSrcId f' posArgs namedArgs reqTy = do
  f <- maybeInterpretPunsAsTyCons reqTy f'
  case getType f of
    TyCon (Pi piTy@(CorePiType appExpl expls _ _)) -> case appExpl of
      ExplicitApp -> do
        checkExplicitArity appSrcId expls posArgs
        bsConstrained <- buildAppConstraints appSrcId reqTy piTy
        args <- inferMixedArgs appSrcId fDesc expls bsConstrained (posArgs, namedArgs)
        applySigmaAtom appSrcId f args
      ImplicitApp -> error "should already have handled this case"
    ty -> throw funSrcId $ EliminationErr "function type" (pprint ty)
 where
  fDesc :: SourceName
  fDesc = getSourceName f'

buildAppConstraints :: SrcId -> RequiredTy n -> CorePiType n -> InfererM i n (ConstrainedBinders n)
buildAppConstraints appSrcId reqTy (CorePiType _ _ bs effTy) = do
  effsAllowed <- infEffects <$> getInfState
  buildConstraints (Abs bs effTy) \_ (EffTy effs resultTy) -> do
    resultTyConstraints <- return case reqTy of
      Infer -> []
      Check reqTy' -> [TypeConstraint appSrcId (sink reqTy') resultTy]
    EffectRow _ t <- return effs
    effConstraints <- case t of
      NoTail -> return []
      EffectRowTail _ -> return [EffectConstraint appSrcId (sink effsAllowed) effs]
    return $ resultTyConstraints ++ effConstraints

maybeInterpretPunsAsTyCons :: RequiredTy n -> SigmaAtom n -> InfererM i n (SigmaAtom n)
maybeInterpretPunsAsTyCons (Check TyKind) (SigmaUVar sn _ (UPunVar v)) = do
  let v' = UTyConVar v
  ty <- getUVarType v'
  return $ SigmaUVar sn ty v'
maybeInterpretPunsAsTyCons _ x = return x

type IsDependent = Bool

inlineTypeAliases :: CAtomName n -> InfererM i n (CAtom n)
inlineTypeAliases v = do
 lookupAtomName v >>= \case
   LetBound (DeclBinding InlineLet (Atom e)) -> return e
   _ -> toAtom <$> toAtomVar v

applySigmaAtom :: Emits o => SrcId -> SigmaAtom o -> [CAtom o] -> InfererM i o (CAtom o)
applySigmaAtom appSrcId (SigmaAtom _ f) args = emitWithEffects appSrcId =<< mkApp f args
applySigmaAtom appSrcId (SigmaUVar _ _ f) args = case f of
  UAtomVar f' -> do
    f'' <- inlineTypeAliases f'
    emitWithEffects appSrcId =<< mkApp f'' args
  UTyConVar f' -> do
    TyConDef sn roleExpls _ _ <- lookupTyCon f'
    let expls = snd <$> roleExpls
    return $ toAtom $ UserADTType sn f' (TyConParams expls args)
  UDataConVar v -> do
    (tyCon, i) <- lookupDataCon v
    applyDataCon tyCon i args
  UPunVar tc -> do
    TyConDef sn _ _ _ <- lookupTyCon tc
    -- interpret as a data constructor by default
    (params, dataArgs) <- splitParamPrefix tc args
    repVal <- makeStructRepVal tc dataArgs
    return $ toAtom $ NewtypeCon (UserADTData sn tc params) repVal
  UClassVar f' -> do
    ClassDef sourceName builtinName _ _ _ _ _ _ <- lookupClassDef f'
    return $ toAtom case builtinName of
      Just Ix   -> IxDictType   singleTyParam
      Just Data -> DataDictType singleTyParam
      Nothing   -> DictType sourceName f' args
      where singleTyParam = case args of
              [p] -> fromJust $ toMaybeType p
              _ -> error "not a single type param"
  UMethodVar  f' -> do
    MethodBinding className methodIdx <- lookupEnv f'
    ClassDef _ _ _ _ _ paramBs _ _ <- lookupClassDef className
    let numParams = nestLength paramBs
    -- params aren't needed because they're already implied by the dict argument
    let (dictArg:args') = drop numParams args
    emitWithEffects appSrcId =<< mkApplyMethod (fromJust $ toMaybeDict dictArg) methodIdx args'
applySigmaAtom appSrcId (SigmaPartialApp _ f prevArgs) args =
  emitWithEffects appSrcId =<< mkApp f (prevArgs ++ args)

splitParamPrefix :: EnvReader m => TyConName n -> [CAtom n] -> m n (TyConParams n, [CAtom n])
splitParamPrefix tc args = do
  TyConDef _ _ paramBs _ <- lookupTyCon tc
  let (paramArgs, dataArgs) = splitAt (nestLength paramBs) args
  params <- makeTyConParams tc paramArgs
  return (params, dataArgs)

applyDataCon :: Emits o => TyConName o -> Int -> [CAtom o] -> InfererM i o (CAtom o)
applyDataCon tc conIx topArgs = do
  tyDef@(TyConDef sn _ _ _) <- lookupTyCon tc
  (params, dataArgs) <- splitParamPrefix tc topArgs
  ADTCons conDefs <- instantiateTyConDef tyDef params
  DataConDef _ _ repTy _ <- return $ conDefs !! conIx
  conProd <- wrap repTy dataArgs
  repVal <- return case conDefs of
    []  -> error "unreachable"
    [_] -> conProd
    _   -> Con $ SumCon conTys conIx conProd
      where conTys = conDefs <&> \(DataConDef _ _ rty _) -> rty
  return $ toAtom $ NewtypeCon (UserADTData sn tc params) repVal
  where
    wrap :: EnvReader m => CType n -> [CAtom n] -> m n (CAtom n)
    wrap _ [arg] = return $ arg
    wrap rty args = case rty of
      TyCon (ProdType tys)  ->
        if nargs == ntys
          then return $ Con $ ProdCon args
          else Con . ProdCon . (curArgs ++) . (:[]) <$> wrap (last tys) remArgs
        where
          nargs = length args; ntys = length tys
          (curArgs, remArgs) = splitAt (ntys - 1) args
      TyCon (DepPairTy dpt@(DepPairType _ b rty')) -> do
        rty'' <- applySubst (b@>SubstVal h) rty'
        ans <- wrap rty'' t
        return $ toAtom $ DepPair h ans dpt
        where h:t = args
      _ -> error $ "Unexpected data con representation type: " ++ pprint rty

emitWithEffects :: Emits o => SrcId -> CExpr o -> InfererM i o (CAtom o)
emitWithEffects sid expr = do
  addEffects sid $ getEffects expr
  emit expr

checkExplicitArity :: SrcId -> [Explicitness] -> [a] -> InfererM i o ()
checkExplicitArity sid expls args = do
  let arity = length [() | Explicit <- expls]
  let numArgs = length args
  when (numArgs /= arity) $ throw sid $ ArityErr arity numArgs

type MixedArgs arg = ([arg], [(SourceName, arg)])  -- positional args, named args
data Constraint (n::S) =
    TypeConstraint SrcId (CType n) (CType n)
  -- permitted effects (no inference vars), proposed effects
  | EffectConstraint SrcId (EffectRow CoreIR n) (EffectRow CoreIR n)

type Constraints = ListE Constraint
type ConstrainedBinders n = ([IsDependent], Abs (Nest CBinder) Constraints n)

buildConstraints
  :: HasNamesE e
  => Abs (Nest CBinder) e o
  -> (forall o'. DExt o o' => [CAtom o'] -> e o' -> EnvReaderM o' [Constraint o'])
  -> InfererM i o (ConstrainedBinders o)
buildConstraints ab cont = liftEnvReaderM do
  refreshAbs ab \bs e -> do
    cs <- cont (toAtom <$> bindersVars bs) e
    return (getDependence (Abs bs e), Abs bs $ ListE cs)
  where
    getDependence :: HasNamesE e => Abs (Nest CBinder) e n -> [IsDependent]
    getDependence (Abs Empty _) = []
    getDependence (Abs (Nest b bs) e) =
      (binderName b `isFreeIn` Abs bs e) : getDependence (Abs bs e)

-- TODO: check that there are no extra named args provided
inferMixedArgs
  :: forall arg i o . (Emits o, ExplicitArg arg)
  => SrcId -> SourceName
  -> [Explicitness] -> ConstrainedBinders o
  -> MixedArgs (arg i)
  -> InfererM i o [CAtom o]
inferMixedArgs appSrcId fSourceName explsTop (dependenceTop, bsAbs) argsTop@(_, namedArgsTop) = do
  checkNamedArgValidity appSrcId explsTop (map fst namedArgsTop)
  liftSolverM $ fromListE <$> go explsTop dependenceTop bsAbs argsTop
 where
  go :: Emits oo
     => [Explicitness] -> [IsDependent] -> Abs (Nest CBinder) Constraints oo -> MixedArgs (arg i)
     -> SolverM i oo (ListE CAtom oo)
  go expls dependence (Abs bs cs) args = do
    cs' <- eagerlyApplyConstraints bs cs
    case (expls, dependence, bs) of
      ([], [], Empty) -> return mempty
      (expl:explsRest, isDependent:dependenceRest, Nest b bsRest) -> do
        inferMixedArg isDependent (binderType b) expl args \arg restArgs -> do
          bs' <- applySubst (b @> SubstVal arg) (Abs bsRest cs')
          (ListE [arg] <>) <$> go explsRest dependenceRest bs' restArgs
      (_, _, _) -> error "zip error"

  eagerlyApplyConstraints
    :: Nest CBinder oo oo' -> Constraints oo'
    -> SolverM i oo (Constraints oo')
  eagerlyApplyConstraints Empty (ListE cs) = mapM_ applyConstraint cs >> return (ListE [])
  eagerlyApplyConstraints bs (ListE cs) = ListE <$> forMFilter cs \c -> do
    case hoist bs c of
      HoistSuccess c' -> case c' of
        TypeConstraint _ _ _ -> applyConstraint c' >> return Nothing
        EffectConstraint _ _ (EffectRow specificEffs _) ->
          hasInferenceVars specificEffs >>= \case
            False -> applyConstraint c' >> return Nothing
            -- we delay applying the constraint in this case because we might
            -- learn more about the specific effects after we've seen more
            -- arguments (like a `Ref h a` that tells us about the `h`)
            True -> return $ Just c
      HoistFailure _ -> return $ Just c

  inferMixedArg
    :: (Emits oo, Zonkable e) => IsDependent -> CType oo -> Explicitness -> MixedArgs (arg i)
    -> (forall o'. (Emits o', DExt oo o') => CAtom o' -> MixedArgs (arg i) -> SolverM i o' (e o'))
    -> SolverM i oo (e oo)
  inferMixedArg isDependent argTy' expl args cont = do
    argTy <- zonk argTy'
    case expl of
      Explicit -> do
        -- this should succeed because we've already done the arity check
        (arg:argsRest, namedArgs) <- return args
        if isHole arg
          then do
            let desc = (pprint fSourceName, "_")
            withFreshUnificationVar appSrcId (ImplicitArgInfVar desc) argTy \v ->
              cont (toAtom v) (argsRest, namedArgs)
          else do
            arg' <- checkOrInferExplicitArg isDependent arg argTy
            withDistinct $ cont arg' (argsRest, namedArgs)
      Inferred argName infMech -> do
        let desc = (pprint $ fSourceName, fromMaybe "_" (fmap pprint argName))
        case lookupNamedArg args argName of
          Just arg -> do
            arg' <- checkOrInferExplicitArg isDependent arg argTy
            withDistinct $ cont arg' args
          Nothing -> case infMech of
            Unify -> withFreshUnificationVar appSrcId (ImplicitArgInfVar desc) argTy \v -> cont (toAtom v) args
            Synth _ -> withDict appSrcId argTy \d -> cont d args

  checkOrInferExplicitArg :: Emits oo => Bool -> arg i -> CType oo -> SolverM i oo (CAtom oo)
  checkOrInferExplicitArg isDependent arg argTy = do
    arg' <- lift11 $ withoutInfVarsPartial argTy >>= \case
      Just partialTy  -> case isDependent of
        True  -> checkExplicitDependentArg   arg partialTy
        False -> checkExplicitNonDependentArg arg partialTy
      Nothing -> inferExplicitArg arg
    constrainEq (explicitArgSrcId arg) argTy (getType arg')
    return arg'

  lookupNamedArg :: MixedArgs x -> Maybe SourceName -> Maybe x
  lookupNamedArg _ Nothing = Nothing
  lookupNamedArg (_, namedArgs) (Just v) = lookup v namedArgs

  withoutInfVarsPartial :: CType n -> InfererM i n (Maybe (PartialType n))
  withoutInfVarsPartial = \case
    TyCon (Pi piTy) ->
      withoutInfVars piTy >>= \case
        Just piTy' -> return $ Just $ PartialType $ piAsPartialPi piTy'
        Nothing -> withoutInfVars $ PartialType $ piAsPartialPiDropResultTy piTy
    ty -> liftM (FullType <$>) $ withoutInfVars ty

  withoutInfVars :: HoistableE e => e n -> InfererM i n (Maybe (e n))
  withoutInfVars x = hasInferenceVars x >>= \case
    True -> return Nothing
    False -> return $ Just x

checkNamedArgValidity :: Fallible m => SrcId -> [Explicitness] -> [SourceName] -> m ()
checkNamedArgValidity sid expls offeredNames = do
  let explToMaybeName = \case
        Explicit -> Nothing
        Inferred v _ -> v
  let acceptedNames = catMaybes $ map explToMaybeName expls
  let duplicates = repeated offeredNames
  when (not $ null duplicates) $ throw sid $ RepeatedOptionalArgs $ map pprint duplicates
  let unrecognizedNames = filter (not . (`elem` acceptedNames)) offeredNames
  when (not $ null unrecognizedNames) do
    throw sid $ UnrecognizedOptionalArgs (map pprint unrecognizedNames) (map pprint acceptedNames)

inferPrimArg :: Emits o => UExpr i -> InfererM i o (CAtom o)
inferPrimArg x = do
  xBlock <- buildBlock $ bottomUp x
  case getType xBlock of
    TyKind -> reduceExpr xBlock >>= \case
      Just reduced -> return reduced
      _ -> throwInternal "Type args to primops must be reducible"
    _ -> emit xBlock

matchPrimApp :: Emits o => PrimName -> [CAtom o] -> InfererM i o (CAtom o)
matchPrimApp = \case
 UNat                -> \case ~[]  -> return $ toAtom $ NewtypeTyCon Nat
 UFin                -> \case ~[n] -> return $ toAtom $ NewtypeTyCon (Fin n)
 UEffectRowKind      -> \case ~[]  -> return $ toAtom $ NewtypeTyCon EffectRowKind
 UBaseType b         -> \case ~[]  -> return $ toAtomR $ BaseType b
 UNatCon             -> \case ~[x] -> return $ toAtom $ NewtypeCon NatCon x
 UPrimTC tc -> case tc of
   P.ProdType -> \ts -> return $ toAtom $ ProdType $ map (fromJust . toMaybeType) ts
   P.SumType  -> \ts -> return $ toAtom $ SumType  $ map (fromJust . toMaybeType) ts
   P.RefType  -> \case ~[h, a] -> return $ toAtom $ RefType h (fromJust $ toMaybeType a)
   P.TypeKind -> \case ~[] -> return $ Con $ TyConAtom $ TypeKind
   P.HeapType -> \case ~[] -> return $ Con $ TyConAtom $ HeapType
 UCon con -> case con of
   P.ProdCon -> \xs -> return $ toAtom $ ProdCon xs
   P.HeapVal -> \case ~[] -> return $ toAtom HeapVal
   P.SumCon _ -> error "not supported"
 UMiscOp op -> \x -> emit =<< MiscOp <$> matchGenericOp op x
 UMemOp  op -> \x -> emit =<< MemOp  <$> matchGenericOp op x
 UBinOp op -> \case ~[x, y] -> emit $ BinOp op x y
 UUnOp  op -> \case ~[x]    -> emit $ UnOp  op x
 UMAsk      -> \case ~[r]    -> emit $ RefOp r MAsk
 UMGet      -> \case ~[r]    -> emit $ RefOp r MGet
 UMPut      -> \case ~[r, x] -> emit $ RefOp r $ MPut x
 UIndexRef  -> \case ~[r, i] -> indexRef r i
 UApplyMethod i -> \case ~(d:args) -> emit =<< mkApplyMethod (fromJust $ toMaybeDict d) i args
 ULinearize -> \case ~[f, x]  -> do f' <- lam1 f; emitHof $ Linearize f' x
 UTranspose -> \case ~[f, x]  -> do f' <- lam1 f; emitHof $ Transpose f' x
 URunReader -> \case ~[x, f]  -> do f' <- lam2 f; emitHof $ RunReader x f'
 URunState  -> \case ~[x, f]  -> do f' <- lam2 f; emitHof $ RunState  Nothing x f'
 UWhile     -> \case ~[f]     -> do f' <- lam0 f; emitHof $ While f'
 URunIO     -> \case ~[f]     -> do f' <- lam0 f; emitHof $ RunIO f'
 UCatchException-> \case ~[f] -> do f' <- lam0 f; emitHof =<< mkCatchException f'
 UMExtend   -> \case ~[r, z, f, x] -> do f' <- lam2 f; emit $ RefOp r $ MExtend (BaseMonoid z f') x
 URunWriter -> \args -> do
   [idVal, combiner, f] <- return args
   combiner' <- lam2 combiner
   f' <- lam2 f
   emitHof $ RunWriter Nothing (BaseMonoid idVal combiner') f'
 p -> \case xs -> throwInternal $ "Bad primitive application: " ++ show (p, xs)
 where
   lam2 :: Fallible m => CAtom n -> m (LamExpr CoreIR n)
   lam2 x = do
     ExplicitCoreLam (BinaryNest b1 b2) body <- return x
     return $ BinaryLamExpr b1 b2 body

   lam1 :: Fallible m => CAtom n -> m (LamExpr CoreIR n)
   lam1 x = do
     ExplicitCoreLam (UnaryNest b) body <- return x
     return $ UnaryLamExpr b body

   lam0 :: Fallible m => CAtom n -> m (CExpr n)
   lam0 x = do
     ExplicitCoreLam Empty body <- return x
     return body

   matchGenericOp :: GenericOp op => OpConst op CoreIR -> [CAtom n] -> InfererM i n (op CoreIR n)
   matchGenericOp op xs = do
     (tyArgs, dataArgs) <- partitionEithers <$> forM xs \x -> do
       case getType x of
         TyKind -> do
           Just x' <- return $ toMaybeType x
           return $ Left x'
         _ -> return $ Right x
     return $ fromJust $ toOp $ GenericOpRep op tyArgs dataArgs []

pattern ExplicitCoreLam :: Nest CBinder n l -> CExpr l -> CAtom n
pattern ExplicitCoreLam bs body <- Con (Lam (CoreLamExpr _ (LamExpr bs body)))

-- === n-ary applications ===

inferTabApp :: Emits o => SrcId -> CAtom o -> [UExpr i] -> InfererM i o (CAtom o)
inferTabApp tabSrcId tab args = do
  tabTy <- return $ getType tab
  args' <- inferNaryTabAppArgs tabSrcId tabTy args
  naryTabApp tab args'

inferNaryTabAppArgs :: Emits o => SrcId -> CType o -> [UExpr i] -> InfererM i o [CAtom o]
inferNaryTabAppArgs _ _ [] = return []
inferNaryTabAppArgs tabSrcId tabTy (arg:rest) = case tabTy of
  TyCon (TabPi (TabPiType _ b resultTy)) -> do
    let ixTy = binderType b
    let isDependent = binderName b `isFreeIn` resultTy
    arg' <- if isDependent
      then checkSigmaDependent arg (FullType ixTy)
      else topDown ixTy arg
    resultTy' <- applySubst (b @> SubstVal arg') resultTy
    rest' <- inferNaryTabAppArgs tabSrcId resultTy' rest
    return $ arg':rest'
  _ -> throw tabSrcId $ EliminationErr "table type" (pprint tabTy)

checkSigmaDependent :: UExpr i -> PartialType o -> InfererM i o (CAtom o)
checkSigmaDependent e ty = withReducibleEmissions (getSrcId e) CantReduceDependentArg $
  topDownPartial (sink ty) e

-- === sorting case alternatives ===

data IndexedAlt n = IndexedAlt CaseAltIndex (Alt CoreIR n)

instance SinkableE IndexedAlt where
  sinkingProofE = todoSinkableProof

buildNthOrderedAlt :: (Emits n, Builder CoreIR m)
                   => [IndexedAlt n] -> CType n -> CType n -> Int -> CAtom n
                   -> m n (CAtom n)
buildNthOrderedAlt alts _ resultTy i v = do
  case lookup i [(idx, alt) | IndexedAlt idx alt <- alts] of
    Nothing -> do
      resultTy' <- sinkM resultTy
      emit $ ThrowError resultTy'
    Just alt -> applyAbs alt (SubstVal v) >>= emit

buildMonomorphicCase
  :: (Emits n, ScopableBuilder CoreIR m)
  => [IndexedAlt n] -> CAtom n -> CType n -> m n (CAtom n)
buildMonomorphicCase alts scrut resultTy = do
  scrutTy <- return $ getType scrut
  buildCase scrut resultTy \i v -> do
    ListE alts' <- sinkM $ ListE alts
    scrutTy'    <- sinkM scrutTy
    resultTy'   <- sinkM resultTy
    buildNthOrderedAlt alts' scrutTy' resultTy' i v

buildSortedCase :: (Fallible1 m, Builder CoreIR m, Emits n)
                 => CAtom n -> [IndexedAlt n] -> CType n
                 -> m n (CAtom n)
buildSortedCase scrut alts resultTy = do
  scrutTy <- return $ getType scrut
  case scrutTy of
    TyCon (NewtypeTyCon (UserADTType _ defName _)) -> do
      TyConDef _ _ _ (ADTCons cons) <- lookupTyCon defName
      case cons of
        [] -> error "case of void?"
        -- Single constructor ADTs are not sum types, so elide the case.
        [_] -> do
          let [IndexedAlt _ alt] = alts
          scrut' <- unwrapNewtype scrut
          emit =<< applyAbs alt (SubstVal scrut')
        _ -> do
          scrut' <- unwrapNewtype scrut
          liftEmitBuilder $ buildMonomorphicCase alts scrut' resultTy
    _ -> fail $ "Unexpected case expression type: " <> pprint scrutTy

-- TODO: cache this with the instance def (requires a recursive binding)
instanceFun :: EnvReader m => InstanceName n -> AppExplicitness -> m n (CAtom n)
instanceFun instanceName appExpl = do
  InstanceDef _ expls bs _ _ <- lookupInstanceDef instanceName
  liftEnvReaderM $ refreshAbs (Abs bs UnitE) \bs' UnitE -> do
    args <- mapM toAtomVar $ nestToNames bs'
    result <- toAtom <$> mkInstanceDict (sink instanceName) (toAtom <$> args)
    let effTy = EffTy Pure (getType result)
    let piTy = CorePiType appExpl (snd<$>expls) bs' effTy
    return $ toAtom $ CoreLamExpr piTy (LamExpr bs' $ Atom result)

checkMaybeAnnExpr :: Emits o => Maybe (UType i) -> UExpr i -> InfererM i o (CAtom o)
checkMaybeAnnExpr ty expr = confuseGHC >>= \_ -> case ty of
  Nothing -> bottomUp expr
  Just ty' -> do
    ty'' <- checkUType ty'
    topDown ty'' expr

inferTyConDef :: UDataDef i -> InfererM i o (TyConDef o)
inferTyConDef (UDataDef tyConName paramBs dataCons) = do
  withRoleUBinders paramBs \(ZipB roleExpls paramBs') -> do
    dataCons' <- ADTCons <$> mapM inferDataCon dataCons
    return (TyConDef tyConName roleExpls paramBs' dataCons')

inferStructDef :: UStructDef i -> InfererM i o (TyConDef o)
inferStructDef (UStructDef tyConName paramBs fields _) = do
  withRoleUBinders paramBs \(ZipB roleExpls paramBs') -> do
    let (fieldNames, fieldTys) = unzip fields
    tys <- mapM checkUType fieldTys
    let dataConDefs = StructFields $ zip (withoutSrc <$> fieldNames) tys
    return $ TyConDef tyConName roleExpls paramBs' dataConDefs

inferDotMethod
  :: TyConName o
  -> Abs (Nest UAnnBinder) (Abs UAtomBinder ULamExpr) i
  -> InfererM i o (CoreLamExpr o)
inferDotMethod tc (Abs uparamBs (Abs selfB lam)) = do
  TyConDef sn roleExpls paramBs _ <- lookupTyCon tc
  let expls = snd <$> roleExpls
  withFreshBindersInf expls (Abs paramBs UnitE) \paramBs' UnitE -> do
    let paramVs = bindersVars paramBs'
    extendRenamer (uparamBs @@> (atomVarName <$> paramVs)) do
      let selfTy = toType $ UserADTType sn (sink tc) (TyConParams expls (toAtom <$> paramVs))
      withFreshBinderInf "self" Explicit selfTy \selfB' -> do
        lam' <- extendRenamer (selfB @> binderName selfB') $ inferULam lam
        return $ prependCoreLamExpr (expls ++ [Explicit]) (paramBs' >>> UnaryNest selfB') lam'

  where
    prependCoreLamExpr :: [Explicitness] -> Nest CBinder n l -> CoreLamExpr l -> CoreLamExpr n
    prependCoreLamExpr expls bs e = case e of
      CoreLamExpr (CorePiType appExpl piExpls piBs effTy) (LamExpr lamBs body) -> do
        let piType  = CorePiType appExpl (expls <> piExpls) (bs >>> piBs) effTy
        let lamExpr = LamExpr (bs >>> lamBs) body
        CoreLamExpr piType lamExpr

inferDataCon :: (SourceName, UDataDefTrail i) -> InfererM i o (DataConDef o)
inferDataCon (sourceName, UDataDefTrail argBs) = do
  withUBinders argBs \(ZipB _ argBs') -> do
    let (repTy, projIdxs) = dataConRepTy $ EmptyAbs argBs'
    return $ DataConDef sourceName (EmptyAbs argBs') repTy projIdxs

dataConRepTy :: EmptyAbs (Nest CBinder) n -> (CType n, [[Projection]])
dataConRepTy (Abs topBs UnitE) = case topBs of
  Empty -> (UnitTy, [])
  _ -> go [] [UnwrapNewtype] topBs
  where
    go :: [CType l] -> [Projection] -> Nest (Binder CoreIR) l p -> (CType l, [[Projection]])
    go revAcc projIdxs = \case
      Empty -> case revAcc of
        []   -> error "should never happen"
        [ty] -> (ty, [projIdxs])
        _    -> ( toType $ ProdType $ reverse revAcc
                , iota (length revAcc) <&> \i -> ProjectProduct i:projIdxs )
      Nest b bs -> case hoist b (EmptyAbs bs) of
        HoistSuccess (Abs bs' UnitE) -> go (binderType b:revAcc) projIdxs bs'
        HoistFailure _ -> (fullTy, idxs)
          where
            accSize = length revAcc
            (fullTy, depTyIdxs) = case revAcc of
              [] -> (depTy, [])
              _  -> (toType $ ProdType $ reverse revAcc ++ [depTy], [ProjectProduct accSize])
            (tailTy, tailIdxs) = go [] (ProjectProduct 1 : (depTyIdxs ++ projIdxs)) bs
            idxs = (iota accSize <&> \i -> ProjectProduct i : projIdxs) ++
                   ((ProjectProduct 0 : (depTyIdxs ++ projIdxs)) : tailIdxs)
            depTy = toType $ DepPairTy $ DepPairType ExplicitDepPair b tailTy

inferClassDef
  :: SourceName -> [SourceName] -> Nest UAnnBinder i i' -> [UType i']
  -> InfererM i o (ClassDef o)
inferClassDef className methodNames paramBs methodTys = do
  withRoleUBinders paramBs \(ZipB roleExpls paramBs') -> do
    let paramNames = catMaybes $ nestToListFlip paramBs \(UAnnBinder expl b _ _) ->
          case expl of Inferred _ (Synth _) -> Nothing
                       _ -> Just $ Just $ getSourceName b
    methodTys' <- forM methodTys \m -> do
      checkUType m >>= \case
        TyCon (Pi t) -> return t
        t -> return $ CorePiType ImplicitApp [] Empty (EffTy Pure t)
    PairB paramBs'' superclassBs <- partitionBinders rootSrcId (zipAttrs roleExpls paramBs') $
      \b@(WithAttrB (_, expl) b') -> case expl of
        Explicit -> return $ LeftB b
        -- TODO: Add a proper SrcId here. We'll need to plumb it through from the original UBinders
        Inferred _ Unify -> throw rootSrcId InterfacesNoImplicitParams
        Inferred _ (Synth _) -> return $ RightB b'
    let (roleExpls', paramBs''') = unzipAttrs paramBs''
    builtinName <- case className of
      -- TODO: this is hacky. Let's just make the Ix class, including its
      -- methods, fully built-in instead of prelude-defined.
      "Ix"   -> return $ Just Ix
      "Data" -> return $ Just Data
      _      -> return Nothing
    return $ ClassDef className builtinName methodNames paramNames roleExpls' paramBs''' superclassBs methodTys'

withUBinder :: UAnnBinder i i' -> InfererCPSB2 (WithExpl CBinder) i i' o a
withUBinder (UAnnBinder expl (WithSrcB sid b) ann cs) cont = do
  ty <- inferAnn sid ann cs
  emitExprType sid ty
  withFreshBinderInf (getNameHint b) expl ty \b' ->
    extendSubst (b@>binderName b') $ cont (WithAttrB expl b')

withUBinders :: Nest UAnnBinder i i' -> InfererCPSB2 (Nest (WithExpl CBinder)) i i' o a
withUBinders bs cont = do
  Abs bs' UnitE <- inferUBinders bs \_ -> return UnitE
  let (expls, bs'') = unzipAttrs bs'
  withFreshBindersInf expls (Abs bs'' UnitE) \bs''' UnitE -> do
    extendSubst (bs@@> (atomVarName <$> bindersVars bs''')) $
      cont $ zipAttrs expls bs'''

inferUBinders
  :: Zonkable e => Nest UAnnBinder i i'
  -> (forall o'. DExt o o' => [CAtomName o'] -> InfererM i' o' (e o'))
  -> InfererM i o (Abs (Nest (WithExpl CBinder)) e o)
inferUBinders Empty cont = withDistinct $ Abs Empty <$> cont []
inferUBinders (Nest (UAnnBinder expl (WithSrcB sid b) ann cs) bs) cont = do
  -- TODO: factor out the common part of each case (requires an annotated
  -- `where` clause because of the rank-2 type)
  ty <- inferAnn sid ann cs
  emitExprType sid ty
  withFreshBinderInf (getNameHint b) expl ty \b' -> do
    extendSubst (b@>binderName b') do
      Abs bs' e <- inferUBinders bs \vs -> cont (sink (binderName b') : vs)
      return $ Abs (Nest (WithAttrB expl b') bs') e

withRoleUBinders :: Nest UAnnBinder i i' -> InfererCPSB2 (Nest (WithRoleExpl CBinder)) i i' o a
withRoleUBinders bs cont = do
  withUBinders bs \(ZipB expls bs') -> do
    let tys = getType <$> bindersVars bs'
    roleExpls <- forM (zip tys expls) \(ty, expl) -> do
      role <- inferRole ty expl
      return (role, expl)
    cont (zipAttrs roleExpls bs')
  where
    inferRole :: CType o -> Explicitness -> InfererM i o ParamRole
    inferRole ty = \case
      Inferred _ (Synth _) -> return DictParam
      _ -> case ty of
        TyKind -> return TypeParam
        _ -> isData ty >>= \case
          True -> return DataParam
          -- TODO(dougalm): the `False` branch should throw an error but that's
          -- currently too conservative. e.g. `data RangeFrom q:Type i:q = ...`
          -- fails because `q` isn't data. We should be able to fix it once we
          -- have a `Data a` class (see issue #680).
          False -> return DataParam
    {-# INLINE inferRole #-}

inferAnn :: SrcId -> UAnn i -> [UConstraint i] -> InfererM i o (CType o)
inferAnn binderSrcId ann cs = case ann of
  UAnn ty -> checkUType ty
  UNoAnn -> case cs of
    WithSrcE sid (UVar ~(InternalName _ _ v)):_ -> do
      renameM v >>= getUVarType >>= \case
        TyCon (Pi (CorePiType ExplicitApp [Explicit] (UnaryNest (_:>ty)) _)) -> return ty
        ty -> throw sid $ NotAUnaryConstraint $ pprint ty
    _ -> throw binderSrcId AnnotationRequired

checkULamPartial :: PartialPiType o -> SrcId -> ULamExpr i -> InfererM i o (CoreLamExpr o)
checkULamPartial partialPiTy sid lamExpr = do
  PartialPiType piAppExpl expls piBs piEffs piReqTy <- return partialPiTy
  ULamExpr lamBs lamAppExpl lamEffs lamResultTy body <- return lamExpr
  checkExplicitArity sid expls (nestToList (const ()) lamBs)
  when (piAppExpl /= lamAppExpl) $ throw sid $ WrongArrowErr (pprint piAppExpl) (pprint lamAppExpl)
  checkLamBinders expls piBs lamBs \lamBs' -> do
    PairE piEffs' piReqTy' <- applyRename (piBs @@> (atomVarName <$> bindersVars lamBs')) (PairE piEffs piReqTy)
    resultTy <- case (lamResultTy, piReqTy') of
      (Nothing, Infer  ) -> return Infer
      (Just t , Infer  ) -> Check <$> checkUType t
      (Nothing, Check t) -> Check <$> return t
      (Just t , Check t') -> checkUType t >>= expectEq (getSrcId t) t' >> return (Check t')
    forM_ lamEffs \lamEffs' -> do
      lamEffs'' <- checkUEffRow lamEffs'
      expectEq sid (Eff piEffs') (Eff lamEffs'') -- TODO: add source annotations to lambda effects too
    body' <- withAllowedEffects piEffs' do
      buildBlock $ withBlockDecls body \result -> checkOrInfer (sink resultTy) result
    resultTy' <- case resultTy of
      Infer -> return $ getType body'
      Check t -> return t
    let piTy = CorePiType piAppExpl expls lamBs' (EffTy piEffs' resultTy')
    return $ CoreLamExpr piTy (LamExpr lamBs' body')
  where
    checkLamBinders
      :: [Explicitness] -> Nest CBinder o any -> Nest UAnnBinder i i'
      -> InfererCPSB2 (Nest CBinder) i i' o a
    checkLamBinders [] Empty Empty cont = withDistinct $ cont Empty
    checkLamBinders (piExpl:piExpls) (Nest (piB:>piAnn) piBs) lamBs cont = do
      case piExpl of
        Inferred _ _ -> do
          withFreshBinderInf (getNameHint piB) piExpl piAnn \b -> do
            Abs piBs' UnitE <- applyRename (piB@>binderName b) (EmptyAbs piBs)
            checkLamBinders piExpls piBs' lamBs \bs -> cont (Nest b bs)
        Explicit -> case lamBs of
          Nest (UAnnBinder _ (WithSrcB bSid lamB) lamAnn _) lamBsRest -> emitExprType bSid piAnn >> do
            case lamAnn of
              UAnn lamAnn' -> checkUType lamAnn' >>= expectEq (getSrcId lamAnn') piAnn
              UNoAnn -> return ()
            withFreshBinderInf (getNameHint lamB) Explicit piAnn \b -> do
              Abs piBs' UnitE <- applyRename (piB@>binderName b) (EmptyAbs piBs)
              extendRenamer (lamB@>sink (binderName b)) $
                checkLamBinders piExpls piBs' lamBsRest \bs -> cont (Nest b bs)
          Empty -> error "zip error"
    checkLamBinders  _ _ _ _ = error "zip error"

inferUForExpr :: Emits o => UForExpr i -> InfererM i o (LamExpr CoreIR o)
inferUForExpr (UForExpr b body) = do
  withUBinder b \(WithAttrB _ b') -> do
    body' <- buildBlock $ withBlockDecls body \result -> bottomUp result
    return $ LamExpr (UnaryNest b') body'

checkUForExpr :: Emits o => SrcId -> UForExpr i -> TabPiType CoreIR o -> InfererM i o (LamExpr CoreIR o)
checkUForExpr sid (UForExpr bFor body) (TabPiType _ bPi resultTy) = do
  let uLamExpr = ULamExpr (UnaryNest bFor) ExplicitApp Nothing Nothing body
  effsAllowed <- infEffects <$> getInfState
  partialPi <- liftEnvReaderM $ refreshAbs (Abs bPi resultTy) \bPi' resultTy' -> do
    return $ PartialPiType ExplicitApp [Explicit] (UnaryNest bPi') (sink effsAllowed) (Check resultTy')
  CoreLamExpr _ lamExpr <- checkULamPartial partialPi sid uLamExpr
  return lamExpr

inferULam :: ULamExpr i -> InfererM i o (CoreLamExpr o)
inferULam (ULamExpr bs appExpl effs resultTy body) = do
  Abs (ZipB expls bs') (PairE effTy body') <- inferUBinders bs \_ -> do
    effs' <- fromMaybe Pure <$> mapM checkUEffRow effs
    resultTy' <- mapM checkUType resultTy
    body' <- buildBlock $ withAllowedEffects (sink effs') do
      withBlockDecls body \result ->
        case resultTy' of
          Nothing -> bottomUp result
          Just resultTy'' -> topDown (sink resultTy'') result
    let effTy = EffTy effs' (getType body')
    return $ PairE effTy body'
  return $ CoreLamExpr (CorePiType appExpl expls bs' effTy) (LamExpr bs' body')

checkULam :: SrcId -> ULamExpr i -> CorePiType o -> InfererM i o (CoreLamExpr o)
checkULam sid ulam piTy = checkULamPartial (piAsPartialPi piTy) sid ulam

piAsPartialPi :: CorePiType n -> PartialPiType n
piAsPartialPi (CorePiType appExpl expls bs (EffTy effs ty)) =
  PartialPiType appExpl expls bs effs (Check ty)

typeAsPartialType :: CType n -> PartialType n
typeAsPartialType (TyCon (Pi piTy)) = PartialType $ piAsPartialPi piTy
typeAsPartialType ty = FullType ty

piAsPartialPiDropResultTy :: CorePiType n -> PartialPiType n
piAsPartialPiDropResultTy (CorePiType appExpl expls bs (EffTy effs _)) =
  PartialPiType appExpl expls bs effs Infer

checkInstanceParams :: Nest CBinder o any -> [UExpr i] -> InfererM i o [CAtom o]
checkInstanceParams bsTop paramsTop = go bsTop paramsTop
 where
  go :: Nest CBinder o any -> [UExpr i] -> InfererM i o [CAtom o]
  go Empty [] = return []
  go (Nest (b:>ty) bs) (x:xs) = do
    x' <- checkUParam ty x
    Abs bs' UnitE <- applySubst (b@>SubstVal x') $ Abs bs UnitE
    (x':) <$> go bs' xs
  go _ _ = error "zip error"

checkInstanceBody
  :: ClassName o -> [CAtom o]
  -> [UMethodDef i] -> InfererM i o (InstanceBody o)
checkInstanceBody className params methods = do
  -- instances are top-level so it's ok to have imprecise root srcIds here
  let sid = rootSrcId
  ClassDef _ _ methodNames _ _ paramBs scBs methodTys <- lookupClassDef className
  Abs scBs' methodTys' <- applySubst (paramBs @@> (SubstVal <$> params)) $ Abs scBs $ ListE methodTys
  superclassTys <- superclassDictTys scBs'
  superclassDicts <- mapM (flip (trySynthTerm sid) Full) superclassTys
  ListE methodTys'' <- applySubst (scBs'@@>(SubstVal<$>superclassDicts)) methodTys'
  methodsChecked <- mapM (checkMethodDef className methodTys'') methods
  let (idxs, methods') = unzip $ sortOn fst $ methodsChecked
  forM_ (repeated idxs) \i ->
    throw sid $ DuplicateMethod $ pprint (methodNames!!i)
  forM_ ([0..(length methodTys''-1)] `listDiff` idxs) \i ->
    throw sid $ MissingMethod $ pprint (methodNames!!i)
  return $ InstanceBody superclassDicts methods'

superclassDictTys :: Nest CBinder o o' -> InfererM i o [CType o]
superclassDictTys Empty = return []
superclassDictTys (Nest b bs) = do
  Abs bs' UnitE <- liftHoistExcept rootSrcId $ hoist b $ Abs bs UnitE
  (binderType b:) <$> superclassDictTys bs'

checkMethodDef :: ClassName o -> [CorePiType o] -> UMethodDef i -> InfererM i o (Int, CAtom o)
checkMethodDef className methodTys (WithSrcE sid m) = do
  UMethodDef ~(InternalName _ sourceName v) rhs <- return m
  MethodBinding className' i <- renameM v >>= lookupEnv
  when (className /= className') do
    ClassBinding classDef <- lookupEnv className
    throw sid $ NotAMethod (pprint sourceName) (pprint $ getSourceName classDef)
  (i,) <$> toAtom <$> Lam <$> checkULam sid rhs (methodTys !! i)

checkUEffRow :: UEffectRow i -> InfererM i o (EffectRow CoreIR o)
checkUEffRow (UEffectRow effs t) = do
   effs' <- liftM eSetFromList $ mapM checkUEff $ toList effs
   t' <- case t of
     Nothing -> return NoTail
     Just (SourceOrInternalName ~(InternalName sid _ v)) -> do
       v' <- toAtomVar =<< renameM v
       expectEq sid EffKind (getType v')
       return $ EffectRowTail v'
   return $ EffectRow effs' t'

checkUEff :: UEffect i -> InfererM i o (Effect CoreIR o)
checkUEff eff = case eff of
  URWSEffect rws (SourceOrInternalName ~(InternalName sid _ region)) -> do
    region' <- renameM region >>= toAtomVar
    expectEq sid (TyCon HeapType) (getType region')
    return $ RWSEffect rws (toAtom region')
  UExceptionEffect -> return ExceptionEffect
  UIOEffect        -> return IOEffect

type CaseAltIndex = Int

checkCaseAlt :: Emits o => RequiredTy o -> CType o -> UAlt i -> InfererM i o (IndexedAlt o)
checkCaseAlt reqTy scrutineeTy (UAlt pat body) = do
  alt <- checkCasePat pat scrutineeTy do
    withBlockDecls body \result -> checkOrInfer (sink reqTy) result
  idx <- getCaseAltIndex pat
  return $ IndexedAlt idx alt

getCaseAltIndex :: UPat i i' -> InfererM i o CaseAltIndex
getCaseAltIndex (WithSrcB sid pat) = case pat of
  UPatCon ~(InternalName _ _ conName) _ -> do
    (_, con) <- renameM conName >>= lookupDataCon
    return con
  _ -> throw sid IllFormedCasePattern

checkCasePat
  :: Emits o
  => UPat i i' -> CType o
  -> (forall o'. (Emits o', Ext o o') => InfererM i' o' (CAtom o'))
  -> InfererM i o (Alt CoreIR o)
checkCasePat (WithSrcB sid pat) scrutineeTy cont = case pat of
  UPatCon ~(InternalName _ _ conName) ps -> do
    (dataDefName, con) <- renameM conName >>= lookupDataCon
    tyConDef <- lookupTyCon dataDefName
    params <- inferParams sid scrutineeTy dataDefName
    ADTCons cons <- instantiateTyConDef tyConDef params
    DataConDef _ _ repTy idxs <- return $ cons !! con
    when (length idxs /= nestLength ps) $ throw sid $ PatternArityErr (length idxs) (nestLength ps)
    withFreshBinderInf noHint Explicit repTy \b -> Abs b <$> do
      buildBlock do
        args <- forM idxs \projs -> do
          emitToVar =<< applyProjectionsReduced (init projs) (sink $ toAtom $ binderVar b)
        bindLetPats ps args $ cont
  _ -> throw sid IllFormedCasePattern

inferParams :: Emits o => SrcId -> CType o -> TyConName o -> InfererM i o (TyConParams o)
inferParams sid ty dataDefName = do
  TyConDef sourceName roleExpls paramBs _ <- lookupTyCon dataDefName
  let paramExpls = snd <$> roleExpls
  let inferenceExpls = paramExpls <&> \case
        Explicit -> Inferred Nothing Unify
        expl -> expl
  paramBsAbs <- buildConstraints (Abs paramBs UnitE) \params _ -> do
    let ty' = toType $ UserADTType sourceName (sink dataDefName) $ TyConParams paramExpls params
    return [TypeConstraint sid (sink ty) ty']
  args <- inferMixedArgs sid sourceName inferenceExpls paramBsAbs emptyMixedArgs
  return $ TyConParams paramExpls args

bindLetPats
  :: (Emits o, HasNamesE e)
  => Nest UPat i i' -> [CAtomVar o]
  -> (forall o'. (Emits o', DExt o o') => InfererM i' o' (e o'))
  -> InfererM i o (e o)
bindLetPats Empty [] cont = getDistinct >>= \Distinct -> cont
bindLetPats (Nest p ps) (x:xs) cont = bindLetPat p x $ bindLetPats ps (sink <$> xs) cont
bindLetPats _ _ _ = error "mismatched number of args"

bindLetPat
  :: (Emits o, HasNamesE e)
  => UPat i i' -> CAtomVar o
  -> (forall o'. (Emits o', DExt o o') => InfererM i' o' (e o'))
  -> InfererM i o (e o)
bindLetPat (WithSrcB sid pat) v cont = emitExprType sid (getType v) >> case pat of
  UPatBinder b -> getDistinct >>= \Distinct -> extendSubst (b @> atomVarName v) cont
  UPatProd ps -> do
    let n = nestLength ps
    case getType v of
      TyCon (ProdType ts) | length ts == n -> return ()
      ty -> throw sid $ PatTypeErr "product type" (pprint ty)
    xs <- forM (iota n) \i -> proj i (toAtom v) >>= emitInline
    bindLetPats ps xs cont
  UPatDepPair (PairB p1 p2) -> do
    case getType v of
      TyCon (DepPairTy _) -> return ()
      ty -> throw sid $ PatTypeErr "dependent pair" (pprint ty)
    -- XXX: we're careful here to reduce the projection because of the dependent
    -- types. We do the same in the `UPatCon` case.
    x1 <- reduceProj 0 (toAtom v) >>= emitInline
    bindLetPat p1 x1 do
      x2  <- getSnd (sink $ toAtom v) >>= emitInline
      bindLetPat p2 x2 do
        cont
  UPatCon ~(InternalName _ _ conName) ps -> do
    (dataDefName, _) <- lookupDataCon =<< renameM conName
    TyConDef _ _ _ cons <- lookupTyCon dataDefName
    case cons of
      ADTCons [DataConDef _ _ _ idxss] -> do
        when (length idxss /= nestLength ps) $
          throw sid $ PatternArityErr (length idxss) (nestLength ps)
        void $ inferParams sid (getType $ toAtom v) dataDefName
        xs <- forM idxss \idxs -> applyProjectionsReduced idxs (toAtom v) >>= emitInline
        bindLetPats ps xs cont
      _ -> throw sid SumTypeCantFail
  UPatTable ps -> do
    let n = fromIntegral (nestLength ps) :: Word32
    case getType v of
      TyCon (TabPi (TabPiType _ (_:>FinConst n') _)) | n == n' -> return ()
      ty -> throw sid $ PatTypeErr ("Fin " ++ show n ++ " table") (pprint ty)
    xs <- forM [0 .. n - 1] \i -> do
      emitToVar =<< mkTabApp (toAtom v) (toAtom $ NewtypeCon (FinCon (NatVal n)) (NatVal $ fromIntegral i))
    bindLetPats ps xs cont
  where
    emitInline :: Emits n => CAtom  n -> InfererM i n (AtomVar CoreIR n)
    emitInline atom = emitDecl noHint InlineLet $ Atom atom

checkUType :: UType i -> InfererM i o (CType o)
checkUType t = do
  Just t' <- toMaybeType <$> checkUParam TyKind t
  return t'

checkUParam :: Kind CoreIR o -> UType i -> InfererM i o (CAtom o)
checkUParam k uty =
  withReducibleEmissions (getSrcId uty) msg $ withAllowedEffects Pure $ topDownExplicit (sink k) uty
  where msg = CantReduceType $ pprint uty

inferTabCon :: forall i o. Emits o => SrcId -> [UExpr i] -> InfererM i o (CAtom o)
inferTabCon sid xs = do
  let n = fromIntegral (length xs) :: Word32
  let finTy = FinConst n
  elemTy <- case xs of
    []  -> throw sid InferEmptyTable
    x:_ -> getType <$> bottomUp x
  ixTy <- asIxType sid finTy
  let tabTy = ixTy ==> elemTy
  xs' <- forM xs \x -> topDown elemTy x
  let dTy = toType $ DataDictType elemTy
  Just dataDict <- toMaybeDict <$> trySynthTerm sid dTy Full
  emit $ TabCon (Just $ WhenIRE dataDict) tabTy xs'

checkTabCon :: forall i o. Emits o => TabPiType CoreIR o -> SrcId -> [UExpr i] -> InfererM i o (CAtom o)
checkTabCon tabTy@(TabPiType _ b elemTy) sid xs = do
  let n = fromIntegral (length xs) :: Word32
  let finTy = FinConst n
  expectEq sid (binderType b) finTy
  xs' <- forM (enumerate xs) \(i, x) -> do
    let i' = toAtom (NewtypeCon (FinCon (NatVal n)) (NatVal $ fromIntegral i)) :: CAtom o
    elemTy' <- applySubst (b@>SubstVal i') elemTy
    topDown elemTy' x
  dTy <- case hoist b elemTy of
    HoistSuccess elemTy' -> return $ toType $ DataDictType elemTy'
    HoistFailure _ -> ignoreExcept <$> liftEnvReaderT do
      withFreshBinder noHint finTy \b' ->  do
        elemTy' <- applyRename (b@>binderName b') elemTy
        let dTy = toType $ DataDictType elemTy'
        return $ toType $ CorePiType ImplicitApp [Inferred Nothing Unify] (UnaryNest b') (EffTy Pure dTy)
  Just dataDict <- toMaybeDict <$> trySynthTerm sid dTy Full
  emit $ TabCon (Just $ WhenIRE dataDict) (TyCon (TabPi tabTy)) xs'

addEffects :: SrcId -> EffectRow CoreIR o -> InfererM i o ()
addEffects _ Pure = return ()
addEffects sid eff = do
  effsAllowed <- infEffects <$> getInfState
  case checkExtends effsAllowed eff of
    Success () -> return ()
    Failure _  -> expectEq sid (Eff effsAllowed) (Eff eff)

getIxDict :: SrcId -> CType o -> InfererM i o (IxDict CoreIR o)
getIxDict sid t = fromJust <$> toMaybeDict <$> trySynthTerm sid (toType $ IxDictType t) Full

asIxType :: SrcId -> CType o -> InfererM i o (IxType CoreIR o)
asIxType sid ty = IxType ty <$> getIxDict sid ty

-- === Solver ===

-- TODO: put this pattern and friends in the Name library? Don't really want to
-- have to think about `eqNameColorRep` just to implement a partial map.
lookupSolverSubst :: forall c n. Color c => SolverSubst n -> Name c n -> AtomSubstVal c n
lookupSolverSubst (SolverSubst m) name =
  case eqColorRep of
    Nothing -> Rename name
    Just (ColorsEqual :: ColorsEqual c (AtomNameC CoreIR))-> case M.lookup name m of
      Nothing -> Rename name
      Just sol -> SubstVal sol

applyConstraint :: Constraint o -> SolverM i o ()
applyConstraint = \case
  TypeConstraint sid t1 t2 -> constrainEq sid t1 t2
  EffectConstraint sid r1 r2' -> do
    -- r1 shouldn't have inference variables. And we can't infer anything about
    -- any inference variables in r2's explicit effects because we don't know
    -- how they line up with r1's. So this is just about figuring out r2's tail.
    r2 <- zonk r2'
    let msg = DisallowedEffects (pprint r1) (pprint r2)
    case checkExtends r1 r2 of
      Success () -> return ()
      Failure _  -> searchFailureAsTypeErr sid msg do
        EffectRow effs1 t1 <- return r1
        EffectRow effs2 (EffectRowTail v2) <- return r2
        guard =<< isUnificationName (atomVarName v2)
        guard $ null (eSetToList $ effs2 `eSetDifference` effs1)
        let extras1 = effs1 `eSetDifference` effs2
        extendSolution v2 (toAtom $ EffectRow extras1 t1)

constrainEq :: ToAtom e CoreIR => SrcId -> e o -> e o -> SolverM i o ()
constrainEq sid t1 t2 = do
  t1' <- zonk $ toAtom t1
  t2' <- zonk $ toAtom t2
  msg <- liftEnvReaderM do
    ab <- renameForPrinting $ PairE t1' t2'
    return $ canonicalizeForPrinting ab \(Abs infVars (PairE t1Pretty t2Pretty)) ->
      UnificationFailure (pprint t1Pretty) (pprint t2Pretty) (nestToList pprint infVars)
  void $ searchFailureAsTypeErr sid msg $ unify t1' t2'

searchFailureAsTypeErr :: ToErr e => SrcId -> e -> SolverM i n a -> SolverM i n a
searchFailureAsTypeErr sid msg cont = cont <|> throw sid msg
{-# INLINE searchFailureAsTypeErr #-}

class AlphaEqE e => Unifiable (e::E) where
  unify :: e n -> e n -> SolverM i n ()

instance Unifiable (Stuck CoreIR) where
  unify s1 s2 = do
    x1 <- zonkStuck s1
    x2 <- zonkStuck s2
    case (x1, x2) of
      (Con c, Con c') -> unify c c'
      (Stuck _ s, Stuck _ s') -> unifyStuckZonked  s s'
      (Stuck _ s, Con c) -> unifyStuckConZonked s c
      (Con c, Stuck _ s) -> unifyStuckConZonked s c

-- assumes both `CStuck` args are zonked
unifyStuckZonked :: CStuck n -> CStuck n -> SolverM i n ()
unifyStuckZonked s1 s2 = do
  x1 <- mkStuck s1
  x2 <- mkStuck s2
  case (s1, s2) of
    (Var v1, Var v2) -> do
      if atomVarName v1 == atomVarName v2
        then return ()
        else extendSolution v2 x1 <|> extendSolution v1 x2
    (_, Var v2) -> extendSolution v2 x1
    (Var v1, _) -> extendSolution v1 x2
    (_, _) -> unifyEq s1 s2

unifyStuckConZonked :: CStuck n -> Con CoreIR n -> SolverM i n ()
unifyStuckConZonked s x = case s of
  Var v -> extendSolution v (Con x)
  _ -> empty

unifyStuckCon :: CStuck n -> Con CoreIR n -> SolverM i n ()
unifyStuckCon s con = do
  x <- zonkStuck s
  case x of
    Stuck _ s' -> unifyStuckConZonked s' con
    Con con' -> unify con' con

instance Unifiable (Atom CoreIR) where
  unify (Con c) (Con c') = unify c c'
  unify (Stuck _ s) (Stuck _ s') = unify  s s'
  unify (Stuck _ s) (Con c) = unifyStuckCon s c
  unify (Con c) (Stuck _ s) = unifyStuckCon s c

-- TODO: do this directly rather than going via `CAtom` using `Type`. We just
-- need to deal with `Stuck`.
instance Unifiable (Type CoreIR) where
  unify (TyCon c) (TyCon c') = unify c c'
  unify (StuckTy _ s) (StuckTy _ s') = unify  s s'
  unify (StuckTy _ s) (TyCon c) = unifyStuckCon s (TyConAtom c)
  unify (TyCon c) (StuckTy _ s) = unifyStuckCon s (TyConAtom c)

instance Unifiable (Con CoreIR) where
  unify e1 e2 = case e1 of
    ( Lit x ) -> do
    { Lit x' <- matchit; guard (x == x')}
    ( ProdCon xs ) -> do
    { ProdCon xs' <- matchit; unifyLists xs xs'}
    ( SumCon ts  i  x ) -> do
    { SumCon ts' i' x' <- matchit; unifyLists ts ts'; guard (i==i'); unify x x'}
    ( DepPair t  x  y ) -> do
    { DepPair t' x' y' <- matchit; unify t t'; unify x x'; unify y y'}
    ( HeapVal ) -> do
    { HeapVal <- matchit; return ()}
    ( Eff eff ) -> do
    { Eff eff' <- matchit; unify eff eff'}
    ( Lam lam ) -> do
    { Lam lam' <- matchit; unifyEq lam lam'}
    ( NewtypeCon con  x  ) -> do
    { NewtypeCon con' x' <- matchit; unifyEq con con'; unify x x'}
    ( TyConAtom t ) -> do
    { TyConAtom t' <- matchit; unify t t'}
    ( DictConAtom d ) -> do
    { DictConAtom d' <- matchit; unifyEq d d'}
    where matchit = return e2

instance Unifiable (TyCon CoreIR) where
  unify t1 t2 = case t1 of
    ( BaseType b ) -> do
    { BaseType b' <- matchit; guard $ b == b'}
    ( HeapType ) -> do
    { HeapType <- matchit; return () }
    ( TypeKind ) -> do
    { TypeKind <- matchit; return () }
    ( Pi piTy ) -> do
    { Pi piTy' <- matchit; unify piTy piTy'}
    ( TabPi piTy) -> do
    { TabPi piTy' <- matchit; unify piTy piTy'}
    ( DictTy d ) -> do
    { DictTy d' <- matchit; unify d d'}
    ( NewtypeTyCon con ) -> do
    { NewtypeTyCon con' <- matchit; unify con con'}
    ( SumType ts ) -> do
    { SumType ts' <- matchit; unifyLists ts ts'}
    ( ProdType ts ) -> do
    { ProdType ts' <- matchit; unifyLists ts ts'}
    ( RefType h  t ) -> do
    { RefType h' t' <- matchit; unify h h'; unify t t'}
    ( DepPairTy t ) -> do
    { DepPairTy t' <- matchit; unify t t'}
    where matchit = return t2

unifyLists :: Unifiable e => [e n] -> [e n] -> SolverM i n ()
unifyLists [] [] = return ()
unifyLists (x:xs) (y:ys) = unify x y >> unifyLists xs ys
unifyLists _ _ = empty

instance Unifiable DictType where
  unify d1 d2 = case d1 of
    ( DictType _ c  params )-> do
    { DictType _ c' params' <- matchit; guard (c == c'); unifyLists params params'}
    ( IxDictType t ) -> do
    { IxDictType t' <- matchit; unify t t'}
    ( DataDictType t ) -> do
    { DataDictType t' <- matchit; unify t t'}
    where matchit = return d2
  {-# INLINE unify #-}

instance Unifiable NewtypeTyCon where
  unify e1 e2 = case e1 of
    ( Nat ) -> do
    { Nat <- matchit; return ()}
    ( Fin n ) -> do
    { Fin n' <- matchit; unify n n'}
    ( EffectRowKind ) -> do
    { EffectRowKind <- matchit; return ()}
    ( UserADTType _ c  params ) -> do
    { UserADTType _ c' params' <- matchit; guard (c == c') >> unify params params' }
    where matchit = return e2

instance Unifiable (IxType CoreIR) where
  -- We ignore the dictionaries because we assume coherence
  unify (IxType t _) (IxType t' _) = unify t t'

instance Unifiable TyConParams where
  -- We ignore the dictionaries because we assume coherence
  unify ps ps' = zipWithM_ unify (ignoreSynthParams ps) (ignoreSynthParams ps')

instance Unifiable (EffectRow CoreIR) where
  unify x1 x2 =
        unifyDirect x1 x2
    <|> unifyDirect x2 x1
    <|> unifyZip x1 x2

   where
     unifyDirect :: EffectRow CoreIR n -> EffectRow CoreIR n -> SolverM i n ()
     unifyDirect r@(EffectRow effs' mv') (EffectRow effs (EffectRowTail v)) | null (eSetToList effs) =
       case mv' of
         EffectRowTail v' | v == v' -> guard $ null $ eSetToList effs'
         _ -> extendSolution v (Con $ Eff r)
     unifyDirect _ _ = empty
     {-# INLINE unifyDirect #-}

     unifyZip :: EffectRow CoreIR n -> EffectRow CoreIR n -> SolverM i n ()
     unifyZip r1 r2 = case (r1, r2) of
       (EffectRow effs1 t1, EffectRow effs2 t2) | not (eSetNull effs1 || eSetNull effs2) -> do
         let extras1 = effs1 `eSetDifference` effs2
         let extras2 = effs2 `eSetDifference` effs1
         void $ withFreshEff \newRow -> do
           unify (EffectRow mempty (sink t1)) (extendEffRow (sink extras2) newRow)
           unify (extendEffRow (sink extras1) newRow) (EffectRow mempty (sink t2))
           return UnitE
       _ -> unifyEq r1 r2

withFreshEff
  :: Zonkable e
  => (forall o'. DExt o o' => EffectRow CoreIR o' -> SolverM i o' (e o'))
  -> SolverM i o (e o)
withFreshEff cont =
  withFreshUnificationVarNoEmits rootSrcId MiscInfVar EffKind \v -> do
    cont $ EffectRow mempty $ EffectRowTail v
{-# INLINE withFreshEff #-}

unifyEq :: AlphaEqE e => e n -> e n -> SolverM i n ()
unifyEq e1 e2 = guard =<< alphaEq e1 e2
{-# INLINE unifyEq #-}

instance Unifiable CorePiType where
  unify (CorePiType appExpl1 expls1 bsTop1 effTy1)
              (CorePiType appExpl2 expls2 bsTop2 effTy2) = do
    unless (appExpl1 == appExpl2) empty
    unless (expls1 == expls2) empty
    go (Abs bsTop1 effTy1) (Abs bsTop2 effTy2)
   where
    go :: Abs (Nest CBinder) (EffTy CoreIR) n
       -> Abs (Nest CBinder) (EffTy CoreIR) n
       -> SolverM i n ()
    go (Abs Empty (EffTy e1 t1)) (Abs Empty (EffTy e2 t2)) = unify t1 t2 >> unify e1 e2
    go (Abs (Nest (b1:>t1) bs1) rest1)
       (Abs (Nest (b2:>t2) bs2) rest2) = do
      unify t1 t2
      void $ withFreshSkolemName t1 \v -> do
        ab1 <- zonk =<< applyRename (b1@>atomVarName v) (Abs bs1 rest1)
        ab2 <- zonk =<< applyRename (b2@>atomVarName v) (Abs bs2 rest2)
        go ab1 ab2
        return UnitE
    go _ _ = empty

instance Unifiable (TabPiType CoreIR) where
  unify (TabPiType _ b1 ty1) (TabPiType _ b2 ty2) =
    unify (Abs b1 ty1) (Abs b2 ty2)

instance Unifiable (DepPairType CoreIR) where
  unify (DepPairType expl1 b1 rhs1) (DepPairType expl2 b2 rhs2) = do
    guard $ expl1 == expl2
    unify (Abs b1 rhs1) (Abs b2 rhs2)

instance Unifiable (Abs CBinder CType) where
  unify (Abs b1 ty1) (Abs b2 ty2) = do
    let ann1 = binderType b1
    let ann2 = binderType b2
    unify ann1 ann2
    void $ withFreshSkolemName ann1 \v -> do
      ty1' <- applyRename (b1@>atomVarName v) ty1
      ty2' <- applyRename (b2@>atomVarName v) ty2
      unify ty1'  ty2'
      return UnitE

withFreshSkolemName
  :: Zonkable e => Kind CoreIR o
  -> (forall o'. DExt o o' => CAtomVar o' -> SolverM i o' (e o'))
  -> SolverM i o (e o)
withFreshSkolemName ty cont = diffStateT1 \s -> do
  withFreshBinder "skol" (SkolemBound ty) \b -> do
    (ans, diff) <- runDiffStateT1 (sink s) do
      v <- toAtomVar $ binderName b
      ans <- cont v >>= zonk
      case hoist b ans of
        HoistSuccess ans' -> return ans'
        HoistFailure _ -> empty
    case hoist b diff of
      HoistSuccess diff' -> return (ans, diff')
      HoistFailure _ -> empty
{-# INLINE withFreshSkolemName #-}

extendSolution :: CAtomVar n -> CAtom n -> SolverM i n ()
extendSolution (AtomVar v _) t =
  isUnificationName v >>= \case
    True -> do
      when (v `isFreeIn` t) solverFail -- occurs check
      -- When we unify under a pi binder we replace its occurrences with a
      -- skolem variable. We don't want to unify with terms containing these
      -- variables because that would mean inferring dependence, which is a can
      -- of worms.
      forM_ (freeAtomVarsList t) \fv ->
        whenM (isSkolemName fv) solverFail -- can't unify with skolems
      addConstraint v t
    False -> empty

isUnificationName :: EnvReader m => CAtomName n -> m n Bool
isUnificationName v = lookupEnv v >>= \case
  AtomNameBinding (SolverBound (InfVarBound _)) -> return True
  _ -> return False
{-# INLINE isUnificationName #-}

isSolverName :: EnvReader m => CAtomName n -> m n Bool
isSolverName v = lookupEnv v >>= \case
  AtomNameBinding (SolverBound _) -> return True
  _                               -> return False


isSkolemName :: EnvReader m => CAtomName n -> m n Bool
isSkolemName v = lookupEnv v >>= \case
  AtomNameBinding (SolverBound (SkolemBound _)) -> return True
  _ -> return False
{-# INLINE isSkolemName #-}

renameForPrinting :: EnvReader m
                   => (PairE CAtom CAtom n) -> m n (Abs (Nest (AtomNameBinder CoreIR)) (PairE CAtom CAtom) n)
renameForPrinting e = do
  infVars <- filterM isSolverName $ freeAtomVarsList e
  let ab = abstractFreeVarsNoAnn infVars e
  let hints = take (length infVars) $ map getNameHint $
                map (:[]) ['a'..'z'] ++ map show [(0::Int)..]
  Distinct <- getDistinct
  scope <- toScope <$> unsafeGetEnv  -- TODO: figure out how to do it safely
  return $ withManyFresh hints scope \bs' ->
    runScopeReaderM (scope `extendOutMap` toScopeFrag bs') do
      Abs bsAbs eAbs <- sinkM ab
      e' <- applyRename (bsAbs@@>nestToNames bs') eAbs
      return $ Abs bs' e'

-- === builder and type querying helpers ===

makeStructRepVal :: (Fallible1 m, EnvReader m) => TyConName n -> [CAtom n] -> m n (CAtom n)
makeStructRepVal tyConName args = do
  TyConDef _ _ _ (StructFields fields) <- lookupTyCon tyConName
  case fields of
    [_] -> case args of
      [arg] -> return arg
      _ -> error "wrong number of args"
    _ -> return $ Con $ ProdCon args

-- === dictionary synthesis ===

-- Given a simplified dict (an Atom of type `DictTy _` in the
-- post-simplification IR), and a requested, more general, dict type, generalize
-- the dict to match the more general type. This is only possible because we
-- require that instances are polymorphic in data-role parameters. It would be
-- valid to implement `generalizeDict` by re-synthesizing the whole dictionary,
-- but we know that the derivation tree has to be the same, so we take the
-- shortcut of just generalizing the data parameters.
generalizeDict :: EnvReader m => CType n -> CDict n -> m n (CDict n)
generalizeDict ty dict = do
  result <- liftEnvReaderM $ liftM fst $ liftInfererMPure $ generalizeDictRec ty dict
  case result of
    Failure e -> error $ "Failed to generalize " ++ pprint dict
      ++ " to " ++ show ty ++ " because " ++ pprint e
    Success ans -> return ans

generalizeDictRec :: CType n -> CDict n -> InfererM i n (CDict n)
generalizeDictRec targetTy (DictCon dict) = case dict of
  InstanceDict _ instanceName args -> do
    InstanceDef _ roleExpls bs _ _ <- lookupInstanceDef instanceName
    liftSolverM $ generalizeInstanceArgs roleExpls bs args \args' -> do
      d <- mkInstanceDict (sink instanceName) args'
      -- We use rootSrcId here because we only call this after type inference so
      -- precise source info isn't needed.
      constrainEq rootSrcId (sink $ toAtom targetTy) (toAtom $ getType d)
      return d
  IxFin _ -> do
    TyCon (DictTy (IxDictType (TyCon (NewtypeTyCon (Fin n))))) <- return targetTy
    return $ DictCon $ IxFin n
  DataData _ -> do
    TyCon (DictTy (DataDictType t')) <- return targetTy
    return $ DictCon $ DataData t'
  IxRawFin _ -> error "not a simplified dict"
generalizeDictRec _ _ = error "not a simplified dict"

generalizeInstanceArgs
  :: Zonkable e => [RoleExpl] -> Nest CBinder o any -> [CAtom o]
  -> (forall o'. DExt o o' => [CAtom o'] -> SolverM i o' (e o'))
  -> SolverM i o (e o)
generalizeInstanceArgs [] Empty [] cont = withDistinct $ cont []
generalizeInstanceArgs ((role,_):expls) (Nest (b:>ty) bs) (arg:args) cont = do
  generalizeInstanceArg role ty arg \arg' -> do
    Abs bs' UnitE <- applySubst (b@>SubstVal arg') (Abs bs UnitE)
    generalizeInstanceArgs expls bs' (sink <$> args) \args' ->
      cont $ sink arg' : args'
generalizeInstanceArgs _ _ _ _ = error "zip error"

generalizeInstanceArg
  :: Zonkable e => ParamRole -> CType o -> CAtom o
  -> (forall o'. DExt o o' => CAtom o' -> SolverM i o' (e o'))
  -> SolverM i o (e o)
generalizeInstanceArg role ty arg cont = case role of
  -- XXX: for `TypeParam` we can just emit a fresh inference name rather than
  -- traversing the whole type like we do in `Generalize.hs`. The reason is
  -- that it's valid to implement `generalizeDict` by synthesizing an entirely
  -- fresh dictionary, and if we were to do that, we would infer this type
  -- parameter exactly as we do here, using inference.
  TypeParam -> withFreshUnificationVarNoEmits rootSrcId MiscInfVar TyKind \v -> cont $ toAtom v
  DictParam -> withFreshDictVarNoEmits ty (
    \ty' -> case toMaybeDict (sink arg) of
              Just d -> liftM toAtom $ lift11 $ generalizeDictRec ty' d
              _ -> error "not a dict") cont
  DataParam -> withFreshUnificationVarNoEmits rootSrcId MiscInfVar ty \v -> cont $ toAtom v

emitInstanceDef :: (Mut n, TopBuilder m) => InstanceDef n -> m n (Name InstanceNameC n)
emitInstanceDef instanceDef@(InstanceDef className _ _ _ _) = do
  ty <- getInstanceType instanceDef
  emitBinding (getNameHint className) $ InstanceBinding instanceDef ty

-- main entrypoint to dictionary synthesizer
trySynthTerm :: SrcId -> CType n -> RequiredMethodAccess -> InfererM i n (SynthAtom n)
trySynthTerm sid ty reqMethodAccess = do
  hasInferenceVars ty >>= \case
    True -> throw sid $ CantSynthInfVars $ pprint ty
    False -> withVoidSubst do
      synthTy <- liftExcept $ typeAsSynthType sid ty
      synthTerm sid synthTy reqMethodAccess
        <|> (throw sid $ CantSynthDict $ pprint ty)
{-# SCC trySynthTerm #-}

hasInferenceVars :: (EnvReader m, HoistableE e) => e n -> m n Bool
hasInferenceVars e = liftEnvReaderM $ anyInferenceVars $ freeAtomVarsList e
{-# INLINE hasInferenceVars #-}

anyInferenceVars :: [CAtomName n] -> EnvReaderM n Bool
anyInferenceVars = \case
  [] -> return False
  (v:vs) -> isSolverName v >>= \case
    True  -> return True
    False -> anyInferenceVars vs

type SynthAtom = CAtom
type SynthPiType n = ([Explicitness], Abs (Nest CBinder) DictType n)
data SynthType n =
   SynthDictType (DictType n)
 | SynthPiType (SynthPiType n)
   deriving (Show, Generic)

data Givens n = Givens { fromGivens :: HM.HashMap (EKey SynthType n) (SynthAtom n) }

getGivens :: InfererM i o (Givens o)
getGivens = givens <$> getInfState

withGivens :: Givens o -> InfererM i o a -> InfererM i o a
withGivens givens cont = withInfState (\s -> s { givens = givens }) cont

extendGivens :: [SynthAtom o] -> InfererM i o a -> InfererM i o a
extendGivens newGivens cont = do
  prevGivens <- getGivens
  finalGivens <- getSuperclassClosure prevGivens newGivens
  withGivens finalGivens cont
{-# INLINE extendGivens #-}

getSynthType :: SynthAtom n -> SynthType n
getSynthType x = ignoreExcept $ typeAsSynthType rootSrcId (getType x)
{-# INLINE getSynthType #-}

typeAsSynthType :: SrcId -> CType n -> Except (SynthType n)
typeAsSynthType sid = \case
  TyCon (DictTy dictTy) -> return $ SynthDictType dictTy
  TyCon (Pi (CorePiType ImplicitApp expls bs (EffTy Pure (TyCon (DictTy d))))) ->
    return $ SynthPiType (expls, Abs bs d)
  ty -> Failure $ toErr sid $ NotASynthType $ pprint ty
{-# SCC typeAsSynthType #-}

getSuperclassClosure :: EnvReader m => Givens n -> [SynthAtom n] -> m n (Givens n)
getSuperclassClosure givens newGivens = do
  Distinct <- getDistinct
  env <- unsafeGetEnv
  return $ getSuperclassClosurePure env givens newGivens
{-# INLINE getSuperclassClosure #-}

getSuperclassClosurePure :: Distinct n => Env n -> Givens n -> [SynthAtom n] -> Givens n
getSuperclassClosurePure env givens newGivens =
  snd $ runState (runEnvReaderT env (mapM_ visitGiven newGivens)) givens
  where
    visitGiven :: SynthAtom n -> EnvReaderT (State (Givens n)) n ()
    visitGiven x = alreadyVisited x >>= \case
      True -> return ()
      False -> do
        markAsVisited x
        parents <- getDirectSuperclasses x
        mapM_ visitGiven parents

    alreadyVisited :: SynthAtom n -> EnvReaderT (State (Givens n)) n Bool
    alreadyVisited x = do
      Givens m <- get
      ty <- return $ getSynthType x
      return $ EKey ty `HM.member` m

    markAsVisited :: SynthAtom n -> EnvReaderT (State (Givens n)) n ()
    markAsVisited x = do
      ty <- return $ getSynthType x
      modify \(Givens m) -> Givens $ HM.insert (EKey ty) x m

    getDirectSuperclasses :: SynthAtom n -> EnvReaderT (State (Givens n)) n [SynthAtom n]
    getDirectSuperclasses synthExpr = do
      synthTy <- return $ getSynthType synthExpr
      superclasses <- case synthTy of
        SynthPiType _ -> return []
        SynthDictType dTy -> getSuperclassTys dTy
      forM (enumerate superclasses) \(i, _) -> do
        reduceSuperclassProj i $ fromJust (toMaybeDict synthExpr)

synthTerm :: SrcId -> SynthType n -> RequiredMethodAccess -> InfererM i n (SynthAtom n)
synthTerm sid targetTy reqMethodAccess = confuseGHC >>= \_ -> case targetTy of
  SynthPiType (expls, ab) -> do
    ab' <- withFreshBindersInf expls ab \bs' targetTy' -> do
      Abs bs' <$> synthTerm sid (SynthDictType targetTy') reqMethodAccess
    Abs bs' synthExpr <- return ab'
    let piTy = CorePiType ImplicitApp expls bs' (EffTy Pure (getType synthExpr))
    let lamExpr = LamExpr bs' (Atom synthExpr)
    return $ toAtom $ Lam $ CoreLamExpr piTy lamExpr
  SynthDictType dictTy -> case dictTy of
    IxDictType (TyCon (NewtypeTyCon (Fin n))) -> return $ toAtom $ IxFin n
    DataDictType t -> do
      void (synthDictForData sid dictTy <|> synthDictFromGiven sid dictTy)
      return $ toAtom $ DataData t
    _ -> do
      dict <- synthDictFromInstance sid dictTy <|> synthDictFromGiven sid dictTy
      case dict of
        Con (DictConAtom (InstanceDict _ instanceName _)) -> do
          isReqMethodAccessAllowed <- reqMethodAccess `isMethodAccessAllowedBy` instanceName
          if isReqMethodAccessAllowed
            then return dict
            else empty
        _ -> return dict
{-# SCC synthTerm #-}

isMethodAccessAllowedBy :: EnvReader m =>  RequiredMethodAccess -> InstanceName n -> m n Bool
isMethodAccessAllowedBy access instanceName = do
  InstanceDef className _ _ _ (InstanceBody _ methods) <- lookupInstanceDef instanceName
  let numInstanceMethods = length methods
  ClassDef _ _ _ _ _ _ _ methodTys <- lookupClassDef className
  let numClassMethods = length methodTys
  case access of
    Full                  -> return $ numClassMethods == numInstanceMethods
    Partial numReqMethods -> return $ numReqMethods   <= numInstanceMethods

synthDictFromGiven :: SrcId -> DictType n -> InfererM i n (SynthAtom n)
synthDictFromGiven sid targetTy = do
  givens <- ((HM.elems . fromGivens) <$> getGivens)
  asum $ givens <&> \given -> do
    case getSynthType given of
      SynthDictType givenDictTy -> do
        guard =<< alphaEq targetTy givenDictTy
        return given
      SynthPiType givenPiTy -> typeErrAsSearchFailure do
        args <- instantiateSynthArgs sid targetTy givenPiTy
        reduceInstantiateGiven given args

synthDictFromInstance :: SrcId -> DictType n -> InfererM i n (SynthAtom n)
synthDictFromInstance sid targetTy = do
  instances <- getInstanceDicts targetTy
  asum $ instances <&> \candidate -> typeErrAsSearchFailure do
    CorePiType _ expls bs (EffTy _ (TyCon (DictTy candidateTy))) <- lookupInstanceTy candidate
    args <- instantiateSynthArgs sid targetTy (expls, Abs bs candidateTy)
    return $ toAtom $ InstanceDict (toType targetTy) candidate args

getInstanceDicts :: EnvReader m => DictType n -> m n [InstanceName n]
getInstanceDicts dictTy = do
  env <- withEnv (envSynthCandidates . moduleEnv)
  case dictTy of
    DictType _ name _ -> return $ M.findWithDefault [] name $ instanceDicts env
    IxDictType _      -> return $ ixInstances env
    DataDictType _    -> return []

addInstanceSynthCandidate :: TopBuilder m => ClassName n -> Maybe BuiltinClassName -> InstanceName n  -> m n ()
addInstanceSynthCandidate className maybeBuiltin instanceName = do
  sc <- return case maybeBuiltin of
    Nothing   -> mempty {instanceDicts = M.singleton className [instanceName] }
    Just Ix   -> mempty {ixInstances   = [instanceName]}
    Just Data -> mempty
  emitLocalModuleEnv $ mempty {envSynthCandidates = sc}

instantiateSynthArgs :: SrcId -> DictType n -> SynthPiType n -> InfererM i n [CAtom n]
instantiateSynthArgs sid target (expls, synthPiTy) = do
  liftM fromListE $ withReducibleEmissions sid CantReduceDict do
    bsConstrained <- buildConstraints (sink synthPiTy) \_ resultTy -> do
      return [TypeConstraint sid (TyCon $ DictTy $ sink target) (TyCon $ DictTy resultTy)]
    ListE <$> inferMixedArgs sid "dict" expls bsConstrained emptyMixedArgs

emptyMixedArgs :: MixedArgs (CAtom n)
emptyMixedArgs = ([], [])

typeErrAsSearchFailure :: InfererM i n a -> InfererM i n a
typeErrAsSearchFailure cont = cont `catchErr` \case
  TypeErr _ _ -> empty
  e -> throwErr e

synthDictForData :: forall i n. SrcId -> DictType n -> InfererM i n (SynthAtom n)
synthDictForData sid dictTy@(DataDictType ty) = case ty of
  -- TODO Deduplicate vs CheckType.checkDataLike
  -- The "Stuck" case is different
  StuckTy _ _ -> synthDictFromGiven sid dictTy
  TyCon con -> case con of
    TabPi (TabPiType _ b eltTy) -> recurBinder (Abs b eltTy) >> success
    DepPairTy (DepPairType _ b@(_:>l) r) -> do
     recur l >> recurBinder (Abs b r) >> success
    NewtypeTyCon nt -> do
      (_, ty') <- unwrapNewtypeType nt
      recur ty' >> success
    BaseType _  -> success
    ProdType as -> mapM_ recur as >> success
    SumType  cs -> mapM_ recur cs >> success
    RefType _ _ -> success
    HeapType    -> success
    _   -> notData
  where
    recur ty' = synthDictForData sid $ DataDictType ty'
    recurBinder :: Abs CBinder CType n -> InfererM i n (SynthAtom n)
    recurBinder (Abs b body) =
      withFreshBinderInf noHint Explicit (binderType b) \b' -> do
        body' <- applyRename (b@>binderName b') body
        ans <- synthDictForData sid $ DataDictType (toType body')
        return $ ignoreHoistFailure $ hoist b' ans
    notData = empty
    success = return $ toAtom $ DataData ty
synthDictForData _ dictTy = error $ "Malformed Data dictTy " ++ pprint dictTy

instance GenericE Givens where
  type RepE Givens = HashMapE (EKey SynthType) SynthAtom
  fromE (Givens m) = HashMapE m
  {-# INLINE fromE #-}
  toE (HashMapE m) = Givens m
  {-# INLINE toE #-}

instance SinkableE Givens where

-- === Inference-specific builder patterns ===

type WithExpl     = WithAttrB Explicitness
type WithRoleExpl = WithAttrB RoleExpl

buildBlockInfWithRecon
  :: HasNamesE e
  => (forall l. (Emits l, DExt n l) => InfererM i l (e l))
  -> InfererM i n (PairE CExpr (ReconAbs CoreIR e) n)
buildBlockInfWithRecon cont = do
  ab <- buildScoped cont
  (block, recon) <- liftEnvReaderM $ refreshAbs ab \decls result -> do
    (newResult, recon) <- telescopicCapture decls result
    return (Abs decls newResult, recon)
  block' <- mkBlock block
  return $ PairE block' recon
{-# INLINE buildBlockInfWithRecon #-}

-- === IFunType ===

asFFIFunType :: EnvReader m => CType n -> m n (Maybe (IFunType, CorePiType n))
asFFIFunType ty = return do
  TyCon (Pi piTy) <- return ty
  impTy <- checkFFIFunTypeM piTy
  return (impTy, piTy)

checkFFIFunTypeM :: Fallible m => CorePiType n -> m IFunType
checkFFIFunTypeM (CorePiType appExpl (_:expls) (Nest b bs) effTy) = do
  argTy <- checkScalar $ binderType b
  case bs of
    Empty -> do
      resultTys <- checkScalarOrPairType (etTy effTy)
      let cc = case length resultTys of
                 0 -> error "Not implemented"
                 1 -> FFICC
                 _ -> FFIMultiResultCC
      return $ IFunType cc [argTy] resultTys
    Nest b' rest -> do
      let naryPiRest = CorePiType appExpl expls (Nest b' rest) effTy
      IFunType cc argTys resultTys <- checkFFIFunTypeM naryPiRest
      return $ IFunType cc (argTy:argTys) resultTys
checkFFIFunTypeM _ = error "expected at least one argument"

checkScalar :: (IRRep r, Fallible m) => Type r n -> m BaseType
checkScalar (BaseTy ty) = return ty
checkScalar ty = throw rootSrcId $ FFIArgTyNotScalar $ pprint ty

checkScalarOrPairType :: (IRRep r, Fallible m) => Type r n -> m [BaseType]
checkScalarOrPairType (PairTy a b) = do
  tys1 <- checkScalarOrPairType a
  tys2 <- checkScalarOrPairType b
  return $ tys1 ++ tys2
checkScalarOrPairType (BaseTy ty) = return [ty]
checkScalarOrPairType ty = throw rootSrcId $ FFIResultTyErr $ pprint ty

-- === instances ===

instance DiffStateE SolverSubst SolverDiff where
  updateDiffStateE :: forall n. Distinct n => Env n -> SolverSubst n -> SolverDiff n -> SolverSubst n
  updateDiffStateE _ initState (SolverDiff (RListE diffs)) = foldl update' initState (unsnoc diffs)
    where
     update' :: Distinct n => SolverSubst n -> Solution n -> SolverSubst n
     update' (SolverSubst subst) (PairE v x) = SolverSubst $ M.insert v x subst

instance SinkableE InfState where sinkingProofE _ = todoSinkableProof

instance GenericE SigmaAtom where
  type RepE SigmaAtom = EitherE3 (LiftE (Maybe SourceName) `PairE` CAtom)
                                 (LiftE SourceName `PairE` CType `PairE` UVar)
                                 (CType `PairE` CAtom `PairE` ListE CAtom)
  fromE = \case
    SigmaAtom x y         -> Case0 $ LiftE x `PairE` y
    SigmaUVar x y z       -> Case1 $ LiftE x `PairE` y `PairE` z
    SigmaPartialApp x y z -> Case2 $ x `PairE` y `PairE` ListE z
  {-# INLINE fromE #-}

  toE = \case
    Case0 (LiftE x `PairE` y)           -> SigmaAtom x y
    Case1 (LiftE x `PairE` y `PairE` z) -> SigmaUVar x y z
    Case2 (x `PairE` y `PairE` ListE z) -> SigmaPartialApp x y z
    _ -> error "impossible"
  {-# INLINE toE #-}

instance RenameE SigmaAtom
instance HoistableE SigmaAtom
instance SinkableE SigmaAtom

instance SubstE AtomSubstVal SigmaAtom where
  substE env (SigmaAtom sn x) = SigmaAtom sn $ substE env x
  substE env (SigmaUVar sn ty uvar) = case uvar of
    UAtomVar v -> substE env $ SigmaAtom (Just sn) $ toAtom (AtomVar v ty)
    UTyConVar   v -> SigmaUVar sn ty' $ UTyConVar   $ substE env v
    UDataConVar v -> SigmaUVar sn ty' $ UDataConVar $ substE env v
    UPunVar     v -> SigmaUVar sn ty' $ UPunVar     $ substE env v
    UClassVar   v -> SigmaUVar sn ty' $ UClassVar   $ substE env v
    UMethodVar  v -> SigmaUVar sn ty' $ UMethodVar  $ substE env v
    where ty' = substE env ty
  substE env (SigmaPartialApp ty f xs) =
    SigmaPartialApp (substE env ty) (substE env f) (map (substE env) xs)

instance PrettyE e => Pretty (UDeclInferenceResult e l) where
  pretty = \case
    UDeclResultDone e -> pretty e
    UDeclResultBindName _ block _ -> pretty block
    UDeclResultBindPattern _ block _ -> pretty block

instance SinkableE e => SinkableE (UDeclInferenceResult e) where
  sinkingProofE = todoSinkableProof

instance (RenameE e, CheckableE CoreIR e) => CheckableE CoreIR (UDeclInferenceResult e) where
  checkE = \case
    UDeclResultDone e -> UDeclResultDone <$> checkE e
    UDeclResultBindName ann block ab ->
      UDeclResultBindName ann <$> checkE block <*> renameM ab -- TODO: check result
    UDeclResultBindPattern hint block recon ->
      UDeclResultBindPattern hint <$> checkE block <*> renameM recon -- TODO: check recon

instance GenericE SynthType where
  type RepE SynthType = EitherE2 DictType (PairE (LiftE [Explicitness]) (Abs (Nest CBinder) DictType))
  fromE (SynthDictType d) = Case0 d
  fromE (SynthPiType   (expl, t)) = Case1 (PairE (LiftE expl) t)
  toE (Case0 d) = SynthDictType d
  toE (Case1 (PairE (LiftE expl) t)) = SynthPiType (expl, t)
  toE _ = error "impossible"

instance AlphaEqE       SynthType
instance AlphaHashableE SynthType
instance SinkableE      SynthType
instance HoistableE     SynthType
instance RenameE        SynthType
instance SubstE AtomSubstVal SynthType

instance GenericE Constraint where
  type RepE Constraint = PairE
                           (LiftE SrcId)
                           (EitherE
                             (PairE CType CType)
                             (PairE (EffectRow CoreIR) (EffectRow CoreIR)))
  fromE (TypeConstraint   sid t1 t2) = LiftE sid `PairE` LeftE  (PairE t1 t2)
  fromE (EffectConstraint sid e1 e2) = LiftE sid `PairE` RightE (PairE e1 e2)
  {-# INLINE fromE #-}
  toE (LiftE sid `PairE` LeftE  (PairE t1 t2)) = TypeConstraint   sid t1 t2
  toE (LiftE sid `PairE` RightE (PairE e1 e2)) = EffectConstraint sid e1 e2
  {-# INLINE toE #-}

instance SinkableE             Constraint
instance HoistableE            Constraint
instance (SubstE AtomSubstVal) Constraint

instance GenericE RequiredTy where
  type RepE RequiredTy = EitherE CType UnitE
  fromE (Check ty) = LeftE ty
  fromE Infer      = RightE UnitE
  {-# INLINE fromE #-}
  toE (LeftE ty)     = Check ty
  toE (RightE UnitE) = Infer
  {-# INLINE toE #-}

instance SinkableE      RequiredTy
instance HoistableE     RequiredTy
instance AlphaEqE       RequiredTy
instance RenameE        RequiredTy

instance GenericE PartialType where
  type RepE PartialType = EitherE PartialPiType CType
  fromE (PartialType ty) = LeftE  ty
  fromE (FullType    ty) = RightE ty
  {-# INLINE fromE #-}
  toE (LeftE  ty) = PartialType ty
  toE (RightE ty) = FullType    ty
  {-# INLINE toE #-}

instance SinkableE      PartialType
instance HoistableE     PartialType
instance AlphaEqE       PartialType
instance RenameE        PartialType

instance GenericE SolverSubst where
  -- XXX: this is a bit sketchy because it's not actually bijective...
  type RepE SolverSubst = ListE (PairE CAtomName CAtom)
  fromE (SolverSubst m) = ListE $ map (uncurry PairE) $ M.toList m
  {-# INLINE fromE #-}
  toE (ListE pairs) = SolverSubst $ M.fromList $ map fromPairE pairs
  {-# INLINE toE #-}

instance SinkableE SolverSubst where
instance RenameE SolverSubst where
instance HoistableE SolverSubst

instance GenericE PartialPiType where
  type RepE PartialPiType = LiftE (AppExplicitness, [Explicitness]) `PairE` Abs (Nest CBinder)
                              (EffectRow CoreIR `PairE` RequiredTy)
  fromE (PartialPiType ex exs b eff ty) = LiftE (ex, exs) `PairE` Abs b (PairE eff ty)
  {-# INLINE fromE #-}
  toE   (LiftE (ex, exs) `PairE` Abs b (PairE eff ty)) = PartialPiType ex exs b eff ty
  {-# INLINE toE #-}

instance SinkableE      PartialPiType
instance HoistableE     PartialPiType
instance AlphaEqE       PartialPiType
instance RenameE        PartialPiType

-- See Note [Confuse GHC] from Simplify.hs
confuseGHC :: EnvReader m => m n (DistinctEvidence n)
confuseGHC = getDistinct
{-# INLINE confuseGHC #-}
