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
import Data.Text.Prettyprint.Doc (Pretty (..))
import Data.Word
import qualified Data.HashMap.Strict as HM
import qualified Data.Map.Strict as M
import GHC.Generics (Generic (..))

import Builder
import CheckType
import Core
import Err
import IRVariants
import MTL1
import Name
import SourceInfo
import Subst
import QueryType
import Types.Core
import Types.Imp
import Types.Primitives
import Types.Source
import Util hiding (group)
import Visit

-- === Top-level interface ===

checkTopUType :: (Fallible1 m, EnvReader m) => UType n -> m n (CType n)
checkTopUType ty = liftInfererM $ checkUType ty
{-# SCC checkTopUType #-}

inferTopUExpr :: (Fallible1 m, EnvReader m) => UExpr n -> m n (TopBlock CoreIR n)
inferTopUExpr e = asTopBlock =<< liftInfererM (bottomUp e)
{-# SCC inferTopUExpr #-}

data UDeclInferenceResult e n =
   UDeclResultDone (e n)  -- used for UDataDefDecl, UInterface and UInstance
 | UDeclResultBindName LetAnn (TopBlock CoreIR n) (Abs (UBinder (AtomNameC CoreIR)) e n)
 | UDeclResultBindPattern NameHint (TopBlock CoreIR n) (ReconAbs CoreIR e n)

type WithExpl     = WithAttrB Explicitness
type WithRoleExpl = WithAttrB RoleExpl

inferTopUDecl :: (Mut n, Fallible1 m, TopBuilder m, HasNamesE e)
              => UTopDecl n l -> e l -> m n (UDeclInferenceResult e n)
inferTopUDecl (UStructDecl tc def) result = do
  tc' <- emitBinding (getNameHint tc) $ TyConBinding Nothing (DotMethods mempty)
  def' <- liftInfererM $ extendRenamer (tc@>tc') $ inferStructDef def
  updateTopEnv $ UpdateTyConDef tc' def'
  UStructDef _ paramBs _ methods <- return def
  forM_ methods \(letAnn, methodName, methodDef) -> do
    method <- liftInfererM $ extendRenamer (tc@>tc') $
      inferDotMethod tc' (Abs paramBs methodDef)
    method' <- emitTopLet (getNameHint methodName) letAnn (Con $ Lam method)
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
    ClassDef _ _ _ _ paramBinders _ _ <- lookupClassDef (sink className')
    params' <- checkInstanceParams paramBinders params
    body <- checkInstanceBody (sink className') params' methods
    return $ InstanceDef className' roleExpls bs' params' body
  UDeclResultDone <$> case maybeName of
    RightB UnitB  -> do
      instanceName <- emitInstanceDef def
      addInstanceSynthCandidate className' instanceName
      return result
    JustB instanceName' -> undefined
    -- JustB instanceName' -> do
    --   instanceName <- emitInstanceDef def
    --   lam <- instanceFun instanceName expl
    --   instanceAtomName <- emitTopLet (getNameHint instanceName') PlainLet $ Atom lam
    --   applyRename (instanceName' @> atomVarName instanceAtomName) result
    _ -> error "impossible"
inferTopUDecl (ULocalDecl (WithSrcB src decl)) result = addSrcContext src case decl of
  UPass -> return $ UDeclResultDone result
  UExprDecl _ -> error "Shouldn't have this at the top level (should have become a command instead)"
  ULet letAnn p tyAnn rhs -> case p of
    WithSrcB _ (UPatBinder b) -> do
      block <- liftInfererM $ checkMaybeAnnExpr tyAnn rhs
      topBlock <- asTopBlock block
      return $ UDeclResultBindName letAnn topBlock (Abs b result)
    _ -> undefined
      -- PairE block recon <- liftInfererM $ buildBlockInfWithRecon do
      --   val <- checkMaybeAnnExpr tyAnn rhs
      --   v <- emitHinted (getNameHint p) $ Atom val
      --   bindLetPat p v do
      --     renameM result
      -- topBlock <- asTopBlock block
      -- return $ UDeclResultBindPattern (getNameHint p) topBlock recon
{-# SCC inferTopUDecl #-}

asTopBlock :: EnvReader m => CExpr n -> m n (TopBlock CoreIR n)
asTopBlock body = do
  let effTy = EffTy (getEffects body) (getType body)
  return $ TopLam False (PiType Empty effTy) (LamExpr Empty body)

getInstanceType :: EnvReader m => InstanceDef n -> m n (CorePiType n)
getInstanceType (InstanceDef className roleExpls bs params _) = liftEnvReaderM do
  refreshAbs (Abs bs (ListE params)) \bs' (ListE params') -> do
    className' <- sinkM className
    ClassDef classSourceName _ _ _ _ _ _ <- lookupClassDef className'
    let dTy = DictTy $ DictType classSourceName className' params'
    return $ CorePiType ImplicitApp (snd <$> roleExpls) bs' $ EffTy Pure dTy

-- === Inferer monad ===

newtype SolverSubst n = SolverSubst { fromSolverSubst :: M.Map (CAtomName n) (CExpr n) }

emptySolverSubst :: SolverSubst n
emptySolverSubst = SolverSubst mempty

data InfState (n::S) = InfState
  { givens         :: Givens n
  , infEffects     :: EffectRow CoreIR n }

newtype InfererM (i::S) (o::S) (a:: *) = InfererM
  { runInfererM' :: SubstReaderT Name (ReaderT1 InfState (EnvReaderT FallibleM)) i o a }
  deriving (Functor, Applicative, Monad, MonadFail, Alternative,
            EnvExtender, ScopeReader, EnvReader, Fallible,
            Catchable, CtxReader, SubstReader Name)


type InfererCPSB  b i    o a = (forall o'. DExt o o' => b o o' -> InfererM i  o' a) -> InfererM i o a
type InfererCPSB2 b i i' o a = (forall o'. DExt o o' => b o o' -> InfererM i' o' a) -> InfererM i o a

liftInfererM :: (EnvReader m, Fallible1 m) => InfererM n n a -> m n a
liftInfererM cont = do
  ansM <- liftEnvReaderT $ runReaderT1 emptyInfState $ runSubstReaderT idSubst $ runInfererM' cont
  liftExcept $ runFallibleM ansM
 where
  emptyInfState :: InfState n
  emptyInfState = InfState (Givens HM.empty) Pure
{-# INLINE liftInfererM #-}

-- === Solver monad ===

type Solution = PairE CAtomName CExpr
newtype SolverDiff (n::S) = SolverDiff (RListE Solution n)
  deriving (MonoidE, SinkableE, HoistableE, RenameE)
type SolverM i o a = DiffStateT1 SolverSubst SolverDiff (InfererM i) o a

type Zonkable e = (HasNamesE e, SubstE ExprSubstVal e)

liftSolverM :: SolverM i o a -> InfererM i o a
liftSolverM cont = fst <$> runDiffStateT1 emptySolverSubst cont

zonk :: Zonkable e => e n -> SolverM i n (e n)
zonk e = do
  s <- getDiffState
  applySolverSubst s e
{-# INLINE zonk #-}

applySolverSubst :: (EnvReader m, Zonkable e) => SolverSubst n -> e n -> m n (e n)
applySolverSubst subst e = do
  Distinct <- getDistinct
  env <- unsafeGetEnv
  return $ fmapNames env (lookupSolverSubst subst) e
{-# INLINE applySolverSubst #-}

formatAmbiguousVarErr :: CAtomName n -> CType n' -> InfVarDesc -> String
formatAmbiguousVarErr infVar ty = \case
  AnnotationInfVar v ->
    "Couldn't infer type of unannotated binder " <> v
  ImplicitArgInfVar (f, argName) ->
    "Couldn't infer implicit argument `" <> argName <> "` of " <> f
  TypeInstantiationInfVar t ->
    "Couldn't infer instantiation of type " <> t
  MiscInfVar ->
    "Ambiguous type variable: " ++ pprint infVar ++ ": " ++ pprint ty

withFreshBinderInf :: NameHint -> Explicitness -> CType o -> InfererCPSB CBinder i o a
withFreshBinderInf hint expl ty cont =
  withFreshBinder hint ty \b -> do
    givens <- case expl of
      Inferred _ (Synth _) -> return [Var $ binderVar b]
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
  :: (Zonkable e, ToBinding binding (AtomNameC CoreIR)) => NameHint -> binding o
  -> (forall o'. DExt o o' => CAtomName o' -> SolverM i o' (e o', CExpr o'))
  -> SolverM i o (e o)
withInferenceVar hint binding cont = diffStateT1 \s -> do
  fromPairE <$> withFreshBinder hint binding \(b:>_) -> do
    hardHoist b <$> do
      let v = binderName b
      s' <- sinkM s
      (PairE ans soln, diff) <- runDiffStateT1 s' $ toPairE <$> cont v
      let subst = SolverSubst $ M.singleton v soln
      ans' <- applySolverSubst subst ans
      diff' <- applySolutionToDiff subst v diff
      return $ PairE ans' diff'
 where
  applySolutionToDiff :: SolverSubst n -> CAtomName n -> SolverDiff n -> InfererM i n (SolverDiff n)
  applySolutionToDiff subst vSoln (SolverDiff (RListE (ReversedList cs))) = do
    SolverDiff . RListE . ReversedList <$> forMFilter cs \(PairE v x) ->
      case v == vSoln of
        True -> return Nothing
        False -> Just . PairE v <$> applySolverSubst subst x
{-# INLINE withInferenceVar #-}

withFreshUnificationVar
  :: (Zonkable e) => InfVarDesc -> Kind CoreIR o
  -> (forall o'. DExt o o' => CAtomVar o' -> SolverM i o' (e o'))
  -> SolverM i o (e o)
withFreshUnificationVar desc k cont = undefined
  -- diffStateT1 \s -> do
  -- Abs Empty resultAndDiff <- buildScoped do
  --   liftM toPairE $ runDiffStateT1 (sink s) $
  --     withFreshUnificationVar desc (sink k) cont
  -- return $ fromPairE resultAndDiff

-- withFreshUnificationVar
--   :: Zonkable e => InfVarDesc -> Kind CoreIR o
--   -> (forall o'. DExt o o' => CAtomVar o' -> SolverM i o' (e o'))
--   -> SolverM i o (e o)
-- withFreshUnificationVar desc k cont = do
--   -- TODO: we shouldn't need the context stuff on `InfVarBound` anymore
--   ctx <- srcPosCtx <$> getErrCtx
--   withInferenceVar "_unif_" (InfVarBound k (ctx, desc)) \v -> do
--     ans <- toAtomVar v >>= cont
--     soln <- (M.lookup v <$> fromSolverSubst <$> getDiffState) >>= \case
--       Just soln ->  return soln
--       Nothing -> throw TypeErr $ formatAmbiguousVarErr v k desc
--     return (ans, soln)
-- {-# INLINE withFreshUnificationVar #-}

withFreshDictVar
  :: Zonkable e => CType o
  -- This tells us how to synthesize the dict. The supplied CType won't contain inference vars.
  -> (forall o'. DExt o o' => CType o'     -> SolverM i o' (SynthExpr o'))
  -> (forall o'. DExt o o' => SynthExpr o' -> SolverM i o' (e o'))
  -> SolverM i o (e o)
withFreshDictVar dictTy synthIt cont = hasInferenceVars dictTy >>= \case
  False -> withDistinct $ synthIt dictTy >>= cont
  True -> withInferenceVar "_dict_" (DictBound dictTy) \v -> do
    ans <- cont =<< (Var <$> toAtomVar v)
    dictTy' <- zonk $ sink dictTy
    dict <- synthIt dictTy'
    return (ans, dict)
{-# INLINE withFreshDictVar #-}

withDict
  :: Zonkable e => Kind CoreIR o
  -> (forall o'. DExt o o' => SynthExpr o' -> SolverM i o' (e o'))
  -> SolverM i o (e o)
withDict dictTy cont = withFreshDictVar dictTy
   (\dictTy' -> lift11 $ trySynthTerm dictTy' Full)
   cont
{-# INLINE withDict#-}

addConstraint :: CAtomName o -> CExpr o -> SolverM i o ()
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

checkOrInfer :: RequiredTy o -> UExpr i -> InfererM i o (CExpr o)
checkOrInfer reqTy expr = case reqTy of
  Infer -> bottomUp expr
  Check t -> topDown t expr

topDown :: forall i o. CType o -> UExpr i -> InfererM i o (CExpr o)
topDown ty uexpr = topDownPartial (typeAsPartialType ty) uexpr

topDownPartial :: PartialType o -> UExpr i -> InfererM i o (CExpr o)
topDownPartial partialTy exprWithSrc@(WithSrcE pos expr) = addSrcContext pos $
  case partialTy of
    PartialType partialPiTy -> case expr of
      ULam lam -> Con . Lam <$> checkULamPartial partialPiTy lam
      _ -> Con . Lam <$> etaExpandPartialPi partialPiTy \resultTy explicitArgs -> do
        expr' <- bottomUpExplicit exprWithSrc
        dropSubst $ checkOrInferApp expr' explicitArgs [] resultTy
    FullType ty -> topDownExplicit ty exprWithSrc

-- Creates a lambda for all args and returns (via CPA) the explicit args
etaExpandPartialPi
  :: PartialPiType o
  -> (forall o'. DExt o o' => RequiredTy o' -> [CExpr o'] -> InfererM i o' (CExpr o'))
  -> InfererM i o (CoreLamExpr o)
etaExpandPartialPi (PartialPiType appExpl expls bs effs reqTy) cont = do
  withFreshBindersInf expls (Abs bs (PairE effs reqTy)) \bs' (PairE effs' reqTy') -> do
    let args = zip expls (Var <$> bindersVars bs')
    explicits <- return $ catMaybes $ args <&> \case
      (Explicit, arg) -> Just arg
      _ -> Nothing
    withAllowedEffects effs' do
      body <- cont (sink reqTy') (sink <$> explicits)
      let piTy = CorePiType appExpl expls bs' (EffTy effs' $ getType body)
      return $ CoreLamExpr piTy $ LamExpr bs' body

-- Doesn't introduce implicit pi binders or dependent pairs
topDownExplicit :: forall i o. CType o -> UExpr i -> InfererM i o (CExpr o)
topDownExplicit reqTy exprWithSrc@(WithSrcE pos expr) = addSrcContext pos case expr of
  ULam lamExpr -> case reqTy of
    Pi piTy -> Con . Lam <$> checkULam lamExpr piTy
    _       -> throw TypeErr $ "Unexpected lambda. Expected: " ++ pprint reqTy
  UFor dir uFor -> case reqTy of
    TabPi tabPiTy -> do
      lam@(UnaryLamExpr b' _) <- checkUForExpr uFor tabPiTy
      ixTy <- asIxType $ binderType b'
      liftM toExpr $ mkTypedHof $ For dir ixTy lam
    _ -> throw TypeErr $ "Unexpected `for` expression. Expected: " ++ pprint reqTy
  UApp f posArgs namedArgs -> do
    f' <- bottomUpExplicit f
    checkOrInferApp f' posArgs namedArgs (Check reqTy)
  UDepPair lhs rhs -> case reqTy of
    DepPairTy ty@(DepPairType _ (_ :> lhsTy) _) -> do
      lhs' <- checkSigmaDependent lhs (FullType lhsTy)
      rhsTy <- instantiate ty [lhs']
      rhs' <- topDown rhsTy rhs
      return $ Con $ DepPair lhs' rhs' ty
    _ -> throw TypeErr $ "Unexpected dependent pair. Expected: " ++ pprint reqTy
  UCase scrut alts -> do
    scrut' <- bottomUp scrut
    let scrutTy = getType scrut'
    alts' <- mapM (checkCaseAlt (Check reqTy) scrutTy) alts
    buildSortedCase scrut' alts' reqTy
  UDo block -> withBlockDecls block \result -> topDownExplicit (sink reqTy) result
  UTabCon xs -> do
    case reqTy of
      TabPi tabPiTy -> checkTabCon tabPiTy xs
      _ -> throw TypeErr $ "Unexpected table constructor. Expected: " ++ pprint reqTy
  UNatLit x -> do
    let litVal = Con $ Lit $ Word64Lit $ fromIntegral x
    applyFromLiteralMethod reqTy "from_unsigned_integer" litVal
  UIntLit x  -> do
    let litVal = Con $ Lit $ Int64Lit $ fromIntegral x
    applyFromLiteralMethod reqTy "from_integer" litVal
  UPrim UTuple xs -> case reqTy of
    TyKind -> Con . TypeCon . ProdTy <$> mapM checkUType xs
    ProdTy reqTys -> do
      when (length reqTys /= length xs) $ throw TypeErr "Tuple length mismatch"
      Con . ProdCon <$> forM (zip reqTys xs) \(reqTy', x) -> topDown reqTy' x
    _ -> throw TypeErr $ "Unexpected tuple. Expected: " ++ pprint reqTy
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
  UHole -> throw TypeErr "Can't infer value of hole"
  where
    infer :: InfererM i o (CExpr o)
    infer = do
      sigmaAtom <- maybeInterpretPunsAsTyCons (Check reqTy) =<< bottomUpExplicit exprWithSrc
      instantiateSigma (Check reqTy) sigmaAtom

bottomUp :: UExpr i -> InfererM i o (CExpr o)
bottomUp expr = bottomUpExplicit expr >>= instantiateSigma Infer

-- Doesn't instantiate implicit args
bottomUpExplicit :: UExpr i -> InfererM i o (SigmaExpr o)
bottomUpExplicit (WithSrcE pos expr) = addSrcContext pos case expr of
  UVar ~(InternalName _ sn v) ->  do
    v' <- renameM v
    ty <- getUVarType v'
    return $ SigmaUVar sn ty v'
  ULit l -> return $ SigmaExpr Nothing $ Con $ Lit l
  UFieldAccess x (WithSrc pos' field) -> addSrcContext pos' do
    x' <- bottomUp x
    ty <- return $ getType x'
    fields <- getFieldDefs ty
    case M.lookup field fields of
      Just def -> case def of
        FieldProj i -> SigmaExpr Nothing <$> projectField i x'
        FieldDotMethod method (TyConParams _ params) -> do
          method' <- toAtomVar method
          resultTy <- partialAppType (getType method') (params ++ [x'])
          return $ SigmaPartialApp resultTy (Var method') (params ++ [x'])
      Nothing -> throw TypeErr $
        "Can't resolve field " ++ pprint field ++ " of type " ++ pprint ty ++
        "\nKnown fields are: " ++ pprint (M.keys fields)
  ULam lamExpr -> SigmaExpr Nothing . Con . Lam <$> inferULam lamExpr
  UFor dir uFor -> do
    lam@(UnaryLamExpr b' _) <- inferUForExpr uFor
    ixTy <- asIxType $ binderType b'
    liftM (SigmaExpr Nothing) $ liftM toExpr $ mkTypedHof $ For dir ixTy lam
  UApp f posArgs namedArgs -> do
    f' <- bottomUpExplicit f
    SigmaExpr Nothing <$> checkOrInferApp f' posArgs namedArgs Infer
  UTabApp tab args -> do
    tab' <- bottomUp tab
    SigmaExpr Nothing <$> inferTabApp (srcPos tab) tab' args
  UPi (UPiExpr bs appExpl effs ty) -> do
    -- TODO: check explicitness constraints
    withUBinders bs \(ZipB expls bs') -> do
      effTy' <- EffTy <$> checkUEffRow effs <*> checkUType ty
      return $ SigmaExpr Nothing $ Con $ TypeCon $
        Pi $ CorePiType appExpl expls bs' effTy'
  UTabPi (UTabPiExpr b ty) -> do
    Abs b' ty' <- withUBinder b \(WithAttrB _ b') ->
      liftM (Abs b') $ checkUType ty
    d <- getIxDict $ binderType b'
    let piTy = TabPiType d b' ty'
    return $ SigmaExpr Nothing $ Con $ TypeCon $ TabPi piTy
  UDepPairTy (UDepPairType expl b rhs) -> do
    withUBinder b \(WithAttrB _ b') -> do
      rhs' <- checkUType rhs
      return $ SigmaExpr Nothing $ Con $ TypeCon $ DepPairTy $ DepPairType expl b' rhs'
  UDepPair _ _ -> throw TypeErr $
    "Can't infer the type of a dependent pair; please annotate its type"
  UCase scrut (alt:alts) -> do
    scrut' <- bottomUp scrut
    let scrutTy = getType scrut'
    alt'@(IndexedAlt _ (Abs b body)) <- checkCaseAlt Infer scrutTy alt
    resultTy <- liftHoistExcept $ hoist b (getType body)
    alts' <- mapM (checkCaseAlt (Check resultTy) scrutTy) alts
    SigmaExpr Nothing <$> buildSortedCase scrut' (alt':alts') resultTy
  UCase _ [] -> throw TypeErr "Can't infer empty case expressions"
  UDo block -> undefined -- withBlockDecls block \result -> bottomUpExplicit result
  UTabCon xs -> liftM (SigmaExpr Nothing) $ inferTabCon xs
  UTypeAnn val ty -> do
    ty' <- checkUType ty
    liftM (SigmaExpr Nothing) $ topDown ty' val
  UPrim UTuple xs -> do
    xs' <- forM xs \x -> bottomUp x
    return $ SigmaExpr Nothing $ Con $ ProdCon xs'
  UPrim UMonoLiteral [WithSrcE _ l] -> case l of
    UIntLit x -> return $ SigmaExpr Nothing $ Con $ Lit $ Int32Lit $ fromIntegral x
    UNatLit x -> return $ SigmaExpr Nothing $ Con $ Lit $ Word32Lit $ fromIntegral x
    _ -> throw MiscErr "argument to %monoLit must be a literal"
  UPrim UExplicitApply (f:xs) -> do
    f' <- bottomUpExplicit f
    xs' <- mapM bottomUp xs
    SigmaExpr Nothing <$> applySigmaExpr f' xs'
  UPrim UProjNewtype [x] -> undefined
  -- UPrim UProjNewtype [x] -> do
  --   x' <- bottomUp x >>= unwrapNewtype
  --   return $ SigmaExpr Nothing x'
  UPrim prim xs -> do
    xs' <- forM xs bottomUp
    liftM (SigmaExpr Nothing) $ matchPrimApp prim xs'
  UNatLit _ -> throw TypeErr $ "Can't infer type of literal. Try an explicit annotation"
  UIntLit _ -> throw TypeErr $ "Can't infer type of literal. Try an explicit annotation"
  UFloatLit x -> return $ SigmaExpr Nothing $ Con $ Lit  $ Float32Lit $ realToFrac x
  UHole -> throw TypeErr "Can't infer value of hole"

expectEq :: (PrettyE e, AlphaEqE e) => e o -> e o -> InfererM i o ()
expectEq reqTy actualTy = alphaEq reqTy actualTy >>= \case
  True -> return ()
  False -> throw TypeErr $ "Expected: " ++ pprint reqTy ++
                         "\nActual:   " ++ pprint actualTy
{-# INLINE expectEq #-}

matchReq :: Ext o o' => RequiredTy o -> CExpr o' -> InfererM i o' (CExpr o')
matchReq (Check reqTy) x = do
  reqTy' <- sinkM reqTy
  return x <* expectEq reqTy' (getType x)
matchReq Infer x = return x
{-# INLINE matchReq #-}

instantiateSigma :: RequiredTy o -> SigmaExpr o -> InfererM i o (CExpr o)
instantiateSigma reqTy sigmaAtom = case sigmaAtom of
  SigmaUVar _ _ _ -> case getType sigmaAtom of
    Pi (CorePiType ImplicitApp expls bs (EffTy _ resultTy)) -> do
      bsConstrained <- buildConstraints (Abs bs resultTy) \_ resultTy' -> do
        case reqTy of
          Infer -> return []
          Check reqTy' -> return [TypeConstraint (sink reqTy') resultTy']
      args <- inferMixedArgs @UExpr fDesc expls bsConstrained ([], [])
      applySigmaExpr sigmaAtom args
    _ -> fallback
  _ -> fallback
  where
    fallback = forceSigmaExpr sigmaAtom >>= matchReq reqTy
    fDesc = getSourceName sigmaAtom

forceSigmaExpr :: SigmaExpr o -> InfererM i o (CExpr o)
forceSigmaExpr sigmaAtom = case sigmaAtom of
  SigmaExpr _ x -> return x
  SigmaUVar _ _ v -> case v of
    UAtomVar v' -> Var <$> toAtomVar v'
    _ -> applySigmaExpr sigmaAtom []
  SigmaPartialApp _ _ _ -> error "not implemented" -- better error message?

withBlockDecls
  :: UBlock i
  -> (forall i' o'. DExt o o' => UExpr i' -> InfererM i' o' (CExpr o'))
  -> InfererM i o (CExpr o)
withBlockDecls (WithSrcE src (UBlock declsTop result)) contTop =
  addSrcContext src $ go declsTop $ contTop result where
  go :: Nest UDecl i i'
     -> (forall o'. DExt o o' => InfererM i' o' (CExpr o'))
     -> InfererM i  o (CExpr o)
  go decls cont = case decls of
    Empty -> withDistinct cont
    Nest d ds -> withUDecl d $ go ds $ cont

withUDecl
  :: UDecl i i'
  -> (forall o'. DExt o o' => InfererM i' o' (CExpr o'))
  -> InfererM i  o (CExpr o)
withUDecl (WithSrcB src d) cont = addSrcContext src case d of
  UPass -> withDistinct cont
  UExprDecl e -> do
    e' <- bottomUp e
    withDecl "dead" e' \_ -> cont
  ULet letAnn p ann rhs -> do
    rhs' <- checkMaybeAnnExpr ann rhs
    withDecl (getNameHint p) rhs' \var -> do
      bindLetPat p var cont

applyFromLiteralMethod
  :: CType n -> SourceName -> CExpr n -> InfererM i n (CExpr n)
applyFromLiteralMethod resultTy methodName litVal =
  lookupSourceMap methodName >>= \case
    Nothing -> error $ "prelude function not found: " ++ methodName
    Just ~(UMethodVar methodName') -> do
      MethodBinding className _ <- lookupEnv methodName'
      dictTy <- DictTy <$> dictType className [Con $ TypeCon resultTy]
      d <- trySynthTerm dictTy Full
      mkApplyMethod d 0 [litVal]

-- atom that requires instantiation to become a rho type
data SigmaExpr n =
    SigmaExpr (Maybe SourceName) (CExpr n)
  | SigmaUVar SourceName (CType n) (UVar n)
  | SigmaPartialApp (CType n) (CExpr n) [CExpr n]
    deriving (Show)

-- XXX: this gives the type of the atom in the absence of other type information.
-- So it interprets struct names as data constructors rather than type constructors.
instance HasType CoreIR SigmaExpr where
  getType = \case
    SigmaExpr _ x -> getType x
    SigmaUVar _ ty _ -> ty
    SigmaPartialApp ty _ _ -> ty

instance HasSourceName (SigmaExpr n) where
  getSourceName = \case
    SigmaExpr sn _ -> case sn of
      Just sn' -> sn'
      Nothing  -> "<expr>"
    SigmaUVar sn _ _ -> sn
    SigmaPartialApp _ _ _ -> "<dot method>"

data FieldDef (n::S) =
   FieldProj Int
 | FieldDotMethod (CAtomName n) (TyConParams Expr n)
   deriving (Show, Generic)

getFieldDefs :: CType n -> InfererM i n (M.Map FieldName' (FieldDef n))
getFieldDefs ty = case ty of
  NewtypeTyCon (UserADTType _ tyName params) -> do
    TyConBinding ~(Just tyDef) (DotMethods dotMethods) <- lookupEnv tyName
    instantiateTyConDef tyDef params >>= \case
      StructFields fields -> do
        let projFields = enumerate fields <&> \(i, (field, _)) ->
              [(FieldName field, FieldProj i), (FieldNum i, FieldProj i)]
        let methodFields = M.toList dotMethods <&> \(field, f) ->
              (FieldName field, FieldDotMethod f params)
        return $ M.fromList $ concat projFields ++ methodFields
      ADTCons _ -> noFields ""
  RefTy _ valTy -> case valTy of
    RefTy _ _ -> noFields ""
    _ -> do
      valFields <- getFieldDefs valTy
      return $ M.filter isProj valFields
      where isProj = \case
              FieldProj _ -> True
              _ -> False
  ProdTy ts -> return $ M.fromList $ enumerate ts <&> \(i, _) -> (FieldNum i, FieldProj i)
  TabPi _ -> noFields "\nArray indexing uses [] now."
  _ -> noFields ""
  where
    noFields s = throw TypeErr $ "Can't get fields for type " ++ pprint ty ++ s

projectField :: Int -> CExpr o -> InfererM i o (CExpr o)
projectField i x = undefined
-- projectField i x = case getType x of -- TODO: normalize!
--   ProdTy _ -> projectTuple i x
--   NewtypeTyCon _ -> projectStruct i x
--   RefTy _ valTy -> case valTy of
--     ProdTy _ -> getProjRef (ProjectProduct i) x
--     NewtypeTyCon _ -> projectStructRef i x
--     _ -> bad
--   _ -> bad
--   where bad = error $ "bad projection: " ++ pprint (i, x)

class PrettyE e => ExplicitArg (e::E) where
  checkExplicitArg :: IsDependent -> e i -> PartialType o -> InfererM i o (CExpr o)
  inferExplicitArg :: e i -> InfererM i o (CExpr o)
  isHole :: e n -> Bool

instance ExplicitArg UExpr where
  checkExplicitArg isDependent arg argTy = do
    if isDependent
      then checkSigmaDependent arg argTy -- do we actually need this?
      else topDownPartial argTy arg

  inferExplicitArg arg = bottomUp arg
  isHole = \case
    WithSrcE _ UHole -> True
    _ -> False

instance ExplicitArg CExpr where
  checkExplicitArg _ arg argTy = do
    arg' <- renameM arg
    case argTy of
      FullType argTy' -> expectEq argTy' (getType arg')
      PartialType _ -> return () -- TODO?
    return arg'
  inferExplicitArg arg = renameM arg
  isHole _ = False

checkOrInferApp
  :: forall i o arg . ExplicitArg arg
  => SigmaExpr o -> [arg i] -> [(SourceName, arg i)]
  -> RequiredTy o -> InfererM i o (CExpr o)
checkOrInferApp f' posArgs namedArgs reqTy = do
  f <- maybeInterpretPunsAsTyCons reqTy f'
  case getType f of
    Pi piTy@(CorePiType appExpl expls _ _) -> case appExpl of
      ExplicitApp -> do
        checkExplicitArity expls posArgs
        bsConstrained <- buildAppConstraints reqTy piTy
        args <- inferMixedArgs fDesc expls bsConstrained (posArgs, namedArgs)
        applySigmaExpr f args
      ImplicitApp -> error "should already have handled this case"
    ty -> throw TypeErr $ "Expected a function type. Got: " ++ pprint ty
 where
  fDesc :: SourceName
  fDesc = getSourceName f'

buildAppConstraints :: RequiredTy n -> CorePiType n -> InfererM i n (Abs (Nest CBinder) Constraints n)
buildAppConstraints reqTy (CorePiType _ _ bs effTy) = do
  effsAllowed <- infEffects <$> getInfState
  buildConstraints (Abs bs effTy) \_ (EffTy effs resultTy) -> do
    resultTyConstraints <- return case reqTy of
      Infer -> []
      Check reqTy' -> [TypeConstraint (sink reqTy') resultTy]
    EffectRow _ t <- return effs
    effConstraints <- case t of
      NoTail -> return []
      EffectRowTail _ -> return [EffectConstraint (sink effsAllowed) effs]
    return $ resultTyConstraints ++ effConstraints

maybeInterpretPunsAsTyCons :: RequiredTy n -> SigmaExpr n -> InfererM i n (SigmaExpr n)
maybeInterpretPunsAsTyCons (Check TyKind) (SigmaUVar sn _ (UPunVar v)) = do
  let v' = UTyConVar v
  ty <- getUVarType v'
  return $ SigmaUVar sn ty v'
maybeInterpretPunsAsTyCons _ x = return x

type IsDependent = Bool

applySigmaExpr :: SigmaExpr o -> [CExpr o] -> InfererM i o (CExpr o)
applySigmaExpr (SigmaExpr _ f) args = emitExprWithEffects =<< mkApp f args
applySigmaExpr (SigmaUVar _ _ f) args = case f of
  UAtomVar f' -> do
    f'' <- toAtomVar f'
    emitExprWithEffects =<< mkApp (Var f'') args
  UTyConVar f' -> do
    TyConDef sn roleExpls _ _ <- lookupTyCon f'
    let expls = snd <$> roleExpls
    return $ Con $ TypeCon $ NewtypeTyCon $ UserADTType sn f' (TyConParams expls args)
  UDataConVar v -> do
    (tyCon, i) <- lookupDataCon v
    applyDataCon tyCon i args
  UPunVar tc -> undefined
  UPunVar tc -> do
    TyConDef sn _ _ _ <- lookupTyCon tc
    -- interpret as a data constructor by default
    (params, dataArgs) <- splitParamPrefix tc args
    repVal <- makeStructRepVal tc dataArgs
    return $ Con $ NewtypeCon (UserADTData sn tc params) repVal
  UClassVar   f' -> do
    ClassDef sourceName _ _ _ _ _ _ <- lookupClassDef f'
    return $ Con $ TypeCon $ DictTy $ DictType sourceName f' args
  UMethodVar  f' -> do
    MethodBinding className methodIdx <- lookupEnv f'
    ClassDef _ _ _ _ paramBs _ _ <- lookupClassDef className
    let numParams = nestLength paramBs
    -- params aren't needed because they're already implied by the dict argument
    let (dictArg:args') = drop numParams args
    emitExprWithEffects =<< mkApplyMethod dictArg methodIdx args'
applySigmaExpr (SigmaPartialApp _ f prevArgs) args =
  emitExprWithEffects =<< mkApp f (prevArgs ++ args)

splitParamPrefix :: EnvReader m => TyConName n -> [CExpr n] -> m n (TyConParams Expr n, [CExpr n])
splitParamPrefix tc args = do
  TyConDef _ _ paramBs _ <- lookupTyCon tc
  let (paramArgs, dataArgs) = splitAt (nestLength paramBs) args
  params <- makeTyConParams tc paramArgs
  return (params, dataArgs)

applyDataCon :: TyConName o -> Int -> [CExpr o] -> InfererM i o (CExpr o)
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
  return $ Con $ NewtypeCon (UserADTData sn tc params) repVal
  where
    wrap :: EnvReader m => CType n -> [CExpr n] -> m n (CExpr n)
    wrap _ [arg] = return $ arg
    wrap rty args = case rty of
      ProdTy tys  ->
        if nargs == ntys
          then return $ Con $ ProdCon args
          else Con . ProdCon . (curArgs ++) . (:[]) <$> wrap (last tys) remArgs
        where
          nargs = length args; ntys = length tys
          (curArgs, remArgs) = splitAt (ntys - 1) args
      DepPairTy dpt@(DepPairType _ b rty') -> do
        rty'' <- applySubst (b@>SubstVal h) rty'
        ans <- wrap rty'' t
        return $ Con $ DepPair h ans dpt
        where h:t = args
      _ -> error $ "Unexpected data con representation type: " ++ pprint rty

-- TODO: this now passes back the input unchanged so there's no need to actually
-- return it
emitExprWithEffects :: CExpr o -> InfererM i o (CExpr o)
emitExprWithEffects expr = do
  addEffects $ getEffects expr
  return expr

checkExplicitArity :: [Explicitness] -> [a] -> InfererM i o ()
checkExplicitArity expls args = do
  let arity = length [() | Explicit <- expls]
  let numArgs = length args
  when (numArgs /= arity) do
    throw TypeErr $ "Wrong number of positional arguments provided. Expected " ++
      pprint arity ++ " but got " ++ pprint numArgs

type MixedArgs arg = ([arg], [(SourceName, arg)])  -- positional args, named args
data Constraint (n::S) =
    TypeConstraint (CType n) (CType n)
  -- permitted effects (no inference vars), proposed effects
  | EffectConstraint (EffectRow CoreIR n) (EffectRow CoreIR n)
type Constraints = ListE Constraint

buildConstraints
  :: RenameE e
  => Abs (Nest CBinder) e o
  -> (forall o'. DExt o o' => [CExpr o'] -> e o' -> EnvReaderM o' [Constraint o'])
  -> InfererM i o (Abs (Nest CBinder) Constraints o)
buildConstraints ab cont = liftEnvReaderM do
  refreshAbs ab \bs e -> do
    cs <- cont (Var <$> bindersVars bs) e
    return $ Abs bs $ ListE cs

-- TODO: check that there are no extra named args provided
inferMixedArgs
  :: forall arg i o . ExplicitArg arg
  => SourceName
  -> [Explicitness] -> Abs (Nest CBinder) Constraints o
  -> MixedArgs (arg i)
  -> InfererM i o [CExpr o]
inferMixedArgs fSourceName explsTop bsAbs argsTop@(_, namedArgsTop) = do
  checkNamedArgValidity explsTop (map fst namedArgsTop)
  liftSolverM $ fromListE <$> go explsTop bsAbs argsTop
 where
  go :: [Explicitness] -> Abs (Nest CBinder) Constraints oo -> MixedArgs (arg i)
     -> SolverM i oo (ListE CExpr oo)
  go expls (Abs bs cs) args = do
    cs' <- eagerlyApplyConstraints bs cs
    case (expls, bs) of
      ([], Empty) -> return mempty
      (expl:explsRest, Nest b bsRest) -> do
        let isDependent = binderName b `isFreeIn` Abs bsRest cs'
        inferMixedArg isDependent (binderType b) expl args \arg restArgs -> do
          bs' <- applySubst (b @> SubstVal arg) (Abs bsRest cs')
          (ListE [arg] <>) <$> go explsRest bs' restArgs
      (_, _) -> error "zip error"

  eagerlyApplyConstraints
    :: Nest CBinder oo oo' -> Constraints oo'
    -> SolverM i oo (Constraints oo')
  eagerlyApplyConstraints Empty (ListE cs) = mapM_ applyConstraint cs >> return (ListE [])
  eagerlyApplyConstraints bs (ListE cs) = ListE <$> forMFilter cs \c -> do
    case hoist bs c of
      HoistSuccess c' -> case c' of
        TypeConstraint _ _ -> applyConstraint c' >> return Nothing
        EffectConstraint _ (EffectRow specificEffs _) ->
          hasInferenceVars specificEffs >>= \case
            False -> applyConstraint c' >> return Nothing
            -- we delay applying the constraint in this case because we might
            -- learn more about the specific effects after we've seen more
            -- arguments (like a `Ref h a` that tells us about the `h`)
            True -> return $ Just c
      HoistFailure _ -> return $ Just c

  inferMixedArg
    :: Zonkable e => IsDependent -> CType oo -> Explicitness -> MixedArgs (arg i)
    -> (forall o'. DExt oo o' => CExpr o' -> MixedArgs (arg i) -> SolverM i o' (e o'))
    -> SolverM i oo (e oo)
  inferMixedArg isDependent argTy' expl args cont = do
    argTy <- zonk argTy'
    case expl of
      Explicit -> do
        -- this should succeed because we've already done the arity check
        (arg:argsRest, namedArgs) <- return args
        if isHole arg
          then do
            let desc = (fSourceName, "_")
            withFreshUnificationVar (ImplicitArgInfVar desc) argTy \v ->
              cont (Var v) (argsRest, namedArgs)
          else do
            arg' <- checkOrInferExplicitArg isDependent arg argTy
            withDistinct $ cont arg' (argsRest, namedArgs)
      Inferred argName infMech -> do
        let desc = (fSourceName, fromMaybe "_" argName)
        case lookupNamedArg args argName of
          Just arg -> do
            arg' <- checkOrInferExplicitArg isDependent arg argTy
            withDistinct $ cont arg' args
          Nothing -> case infMech of
            Unify -> withFreshUnificationVar (ImplicitArgInfVar desc) argTy \v -> cont (Var v) args
            Synth _ -> withDict argTy \d -> cont d args

  checkOrInferExplicitArg :: Bool -> arg i -> CType oo -> SolverM i oo (CExpr oo)
  checkOrInferExplicitArg isDependent arg argTy = do
    arg' <- lift11 $ withoutInfVarsPartial argTy >>= \case
      Just partialTy  -> checkExplicitArg isDependent arg partialTy
      Nothing         -> inferExplicitArg arg
    constrainTypesEq argTy (getType arg')
    return arg'

  lookupNamedArg :: MixedArgs x -> Maybe SourceName -> Maybe x
  lookupNamedArg _ Nothing = Nothing
  lookupNamedArg (_, namedArgs) (Just v) = lookup v namedArgs

  withoutInfVarsPartial :: CType n -> InfererM i n (Maybe (PartialType n))
  withoutInfVarsPartial = \case
    Pi piTy ->
      withoutInfVars piTy >>= \case
        Just piTy' -> return $ Just $ PartialType $ piAsPartialPi piTy'
        Nothing -> withoutInfVars $ PartialType $ piAsPartialPiDropResultTy piTy
    ty -> liftM (FullType <$>) $ withoutInfVars ty

  withoutInfVars :: HoistableE e => e n -> InfererM i n (Maybe (e n))
  withoutInfVars x = hasInferenceVars x >>= \case
    True -> return Nothing
    False -> return $ Just x

checkNamedArgValidity :: Fallible m => [Explicitness] -> [SourceName] -> m ()
checkNamedArgValidity expls offeredNames = do
  let explToMaybeName = \case
        Explicit -> Nothing
        Inferred v _ -> v
  let acceptedNames = catMaybes $ map explToMaybeName expls
  let duplicates = repeated offeredNames
  when (not $ null duplicates) do
    throw TypeErr $ "Repeated names offered" ++ pprint duplicates
  let unrecognizedNames = filter (not . (`elem` acceptedNames)) offeredNames
  when (not $ null unrecognizedNames) do
    throw TypeErr $ "Unrecognized named arguments: " ++ pprint unrecognizedNames
      ++ "\nShould be one of: " ++ pprint acceptedNames

matchPrimApp :: PrimName -> [CExpr o] -> InfererM i o (CExpr o)
matchPrimApp = \case
 UNat                -> \case ~[]  -> return $ Con $ TypeCon $ NewtypeTyCon Nat
 UFin                -> \case ~[n] -> return $ Con $ TypeCon $ NewtypeTyCon (Fin n)
 UEffectRowKind      -> \case ~[]  -> return $ Con $ TypeCon $ NewtypeTyCon EffectRowKind
 UBaseType b         -> \case ~[]  -> return $ Con $ TypeCon $ TC $ BaseType b
 UNatCon             -> \case ~[x] -> return $ Con $ NewtypeCon NatCon x
 UPrimTC op -> \x -> Con . TypeCon . TC  <$> matchGenericOp (Right op) x
 UCon    op -> \x -> undefined -- Con <$> matchGenericOp (Right op) x
 UMiscOp op -> \x -> toExpr . MiscOp <$> matchGenericOp op x
 UMemOp  op -> \x -> toExpr . MemOp  <$> matchGenericOp op x
 UBinOp op -> \case ~[x, y] -> return $ toExpr $ BinOp op x y
 UUnOp  op -> \case ~[x]    -> return $ toExpr $ UnOp  op x
 UMAsk      -> \case ~[r]    -> return $ toExpr $ RefOp r MAsk
 UMGet      -> \case ~[r]    -> return $ toExpr $ RefOp r MGet
 UMPut      -> \case ~[r, x] -> return $ toExpr $ RefOp r $ MPut x
 UIndexRef  -> \case ~[r, i] -> undefined -- indexRef r i
 UApplyMethod i -> \case ~(d:args) -> undefined -- mkApplyMethod d i args
 ULinearize -> \case ~[f, x]  -> do f' <- lam1 f; liftM toExpr $ mkTypedHof $ Linearize f' x
 UTranspose -> \case ~[f, x]  -> do f' <- lam1 f; liftM toExpr $ mkTypedHof $ Transpose f' x
 URunReader -> \case ~[x, f]  -> do f' <- lam2 f; liftM toExpr $ mkTypedHof $ RunReader x f'
 URunState  -> \case ~[x, f]  -> do f' <- lam2 f; liftM toExpr $ mkTypedHof $ RunState  Nothing x f'
 UWhile     -> \case ~[f]     -> do f' <- lam0 f; liftM toExpr $ mkTypedHof $ While f'
 URunIO     -> \case ~[f]     -> do f' <- lam0 f; liftM toExpr $ mkTypedHof $ RunIO f'
 UCatchException-> \case ~[f] -> do f' <- lam0 f; liftM toExpr $ mkTypedHof =<< mkCatchException f'
 UMExtend   -> \case ~[r, z, f, x] -> do f' <- lam2 f; return $ toExpr $ RefOp r $ MExtend (BaseMonoid z f') x
 URunWriter -> \args -> do
   [idVal, combiner, f] <- return args
   combiner' <- lam2 combiner
   f' <- lam2 f
   liftM toExpr $ mkTypedHof $ RunWriter Nothing (BaseMonoid idVal combiner') f'
 p -> \case xs -> throw TypeErr $ "Bad primitive application: " ++ show (p, xs)
 where
   lam2 :: Fallible m => CExpr n -> m (LamExpr CoreIR n)
   lam2 x = do
     ExplicitCoreLam (BinaryNest b1 b2) body <- return x
     return $ BinaryLamExpr b1 b2 body

   lam1 :: Fallible m => CExpr n -> m (LamExpr CoreIR n)
   lam1 x = do
     ExplicitCoreLam (UnaryNest b) body <- return x
     return $ UnaryLamExpr b body

   lam0 :: Fallible m => CExpr n -> m (CExpr n)
   lam0 x = do
     ExplicitCoreLam Empty body <- return x
     return body

   matchGenericOp :: GenericOp op => OpConst op CoreIR -> [CExpr n] -> InfererM i n (op CoreIR n)
   matchGenericOp op xs = do
     (tyArgs, dataArgs) <- partitionEithers <$> forM xs \x -> do
       case getType x of
         TyKind -> do
           Con (TypeCon x') <- return x
           return $ Left x'
         _ -> return $ Right x
     return $ fromJust $ toOp $ GenericOpRep op tyArgs dataArgs []

pattern ExplicitCoreLam :: Nest CBinder n l -> CExpr l -> CExpr n
pattern ExplicitCoreLam bs body <- Con (Lam (CoreLamExpr _ (LamExpr bs body)))

-- === n-ary applications ===

inferTabApp :: SrcPosCtx -> CExpr o -> [UExpr i] -> InfererM i o (CExpr o)
inferTabApp tabCtx tab args = undefined
-- inferTabApp tabCtx tab args = addSrcContext tabCtx do
--   tabTy <- return $ getType tab
--   args' <- inferNaryTabAppArgs tabTy args
--   mkTabApp tab args'

inferNaryTabAppArgs :: CType o -> [UExpr i] -> InfererM i o [CExpr o]
inferNaryTabAppArgs _ [] = return []
inferNaryTabAppArgs tabTy (arg:rest) = case tabTy of
  TabPi (TabPiType _ b resultTy) -> do
    let ixTy = binderType b
    let isDependent = binderName b `isFreeIn` resultTy
    arg' <- if isDependent
      then checkSigmaDependent arg (FullType ixTy)
      else topDown ixTy arg
    resultTy' <- applySubst (b @> SubstVal arg') resultTy
    rest' <- inferNaryTabAppArgs resultTy' rest
    return $ arg':rest'
  _ -> throw TypeErr $ "Expected a table type but got: " ++ pprint tabTy

checkSigmaDependent :: UExpr i -> PartialType o -> InfererM i o (CExpr o)
checkSigmaDependent e@(WithSrcE ctx _) ty = addSrcContext ctx $
  withReducibleEmissions depFunErrMsg $ topDownPartial (sink ty) e
  where
    depFunErrMsg =
      "Dependent functions can only be applied to fully evaluated expressions. " ++
      "Bind the argument to a name before you apply the function."

withReducibleEmissions
  :: ( Zonkable e, SubstE ExprSubstVal e)
  => String
  -> (forall o' . DExt o o' => InfererM i o' (e o'))
  -> InfererM i o (e o)
withReducibleEmissions msg cont = undefined
-- withReducibleEmissions msg cont = do
--   Abs decls result <- buildScoped cont
--   cheapReduceWithDecls decls result >>= \case
--     Just t -> return t
--     _ -> throw TypeErr msg

-- === sorting case alternatives ===

data IndexedAlt n = IndexedAlt CaseAltIndex (Alt CoreIR n)

instance SinkableE IndexedAlt where
  sinkingProofE = todoSinkableProof

buildNthOrderedAlt :: EnvReader m
                   => [IndexedAlt n] -> CType n -> CType n -> Int -> CExpr n
                   -> m n (CExpr n)
buildNthOrderedAlt alts scrutTy resultTy i v = do
  case lookup i [(idx, alt) | IndexedAlt idx alt <- alts] of
    Nothing -> do
      resultTy' <- sinkM resultTy
      return $ PrimOp $ MiscOp $ ThrowError resultTy'
    Just alt -> applyAbs alt (SubstVal v)

buildMonomorphicCase
  :: EnvReader m => [IndexedAlt n] -> CExpr n -> CType n -> m n (CExpr n)
buildMonomorphicCase alts scrut resultTy = undefined
-- buildMonomorphicCase alts scrut resultTy = do
--   scrutTy <- return $ getType scrut
--   buildCase scrut resultTy \i v -> do
--     ListE alts' <- sinkM $ ListE alts
--     scrutTy'    <- sinkM scrutTy
--     resultTy'   <- sinkM resultTy
--     buildNthOrderedAlt alts' scrutTy' resultTy' i v

buildSortedCase
  :: (Fallible1 m, EnvReader m)
  => CExpr n -> [IndexedAlt n] -> CType n -> m n (CExpr n)
buildSortedCase scrut alts resultTy = undefined
-- buildSortedCase scrut alts resultTy = do
--   scrutTy <- return $ getType scrut
--   case scrutTy of
--     NewtypeTyCon (UserADTType _ defName _) -> do
--       TyConDef _ _ _ (ADTCons cons) <- lookupTyCon defName
--       case cons of
--         [] -> error "case of void?"
--         -- Single constructor ADTs are not sum types, so elide the case.
--         [_] -> do
--           let [IndexedAlt _ alt] = alts
--           scrut' <- unwrapNewtype scrut
--           applyAbs alt (SubstVal scrut')
--         _ -> liftEmitBuilder $ buildMonomorphicCase alts scrut resultTy
--     _ -> fail $ "Unexpected case expression type: " <> pprint scrutTy

-- TODO: cache this with the instance def (requires a recursive binding)
instanceFun :: EnvReader m => InstanceName n -> AppExplicitness -> m n (CExpr n)
instanceFun instanceName appExpl = do
  InstanceDef _ expls bs _ _ <- lookupInstanceDef instanceName
  liftEnvReaderM $ refreshAbs (Abs bs UnitE) \bs' UnitE -> do
    args <- mapM toAtomVar $ nestToNames bs'
    result <- mkDictExpr $ InstanceDict (sink instanceName) (Var <$> args)
    let effTy = EffTy Pure (getType result)
    let piTy = CorePiType appExpl (snd<$>expls) bs' effTy
    return $ Con $ Lam $ CoreLamExpr piTy (LamExpr bs' result)

checkMaybeAnnExpr :: Maybe (UType i) -> UExpr i -> InfererM i o (CExpr o)
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
    let dataConDefs = StructFields $ zip fieldNames tys
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
      let selfTy = NewtypeTyCon $ UserADTType sn (sink tc) (TyConParams expls (Var <$> paramVs))
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
        _    -> ( ProdTy $ reverse revAcc
                , iota (length revAcc) <&> \i -> ProjectProduct i:projIdxs )
      Nest b bs -> case hoist b (EmptyAbs bs) of
        HoistSuccess (Abs bs' UnitE) -> go (binderType b:revAcc) projIdxs bs'
        HoistFailure _ -> (fullTy, idxs)
          where
            accSize = length revAcc
            (fullTy, depTyIdxs) = case revAcc of
              [] -> (depTy, [])
              _  -> (ProdTy $ reverse revAcc ++ [depTy], [ProjectProduct accSize])
            (tailTy, tailIdxs) = go [] (ProjectProduct 1 : (depTyIdxs ++ projIdxs)) bs
            idxs = (iota accSize <&> \i -> ProjectProduct i : projIdxs) ++
                   ((ProjectProduct 0 : (depTyIdxs ++ projIdxs)) : tailIdxs)
            depTy = DepPairTy $ DepPairType ExplicitDepPair b tailTy

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
        Pi t -> return t
        t -> return $ CorePiType ImplicitApp [] Empty (EffTy Pure t)
    PairB paramBs'' superclassBs <- partitionBinders (zipAttrs roleExpls paramBs') $
      \b@(WithAttrB (_, expl) b') -> case expl of
        Explicit -> return $ LeftB b
        Inferred _ Unify -> throw TypeErr "Interfaces can't have implicit parameters"
        Inferred _ (Synth _) -> return $ RightB b'
    let (roleExpls', paramBs''') = unzipAttrs paramBs''
    return $ ClassDef className methodNames paramNames roleExpls' paramBs''' superclassBs methodTys'

withUBinder :: UAnnBinder i i' -> InfererCPSB2 (WithExpl CBinder) i i' o a
withUBinder (UAnnBinder expl b ann cs) cont = do
  ty <- inferAnn ann cs
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
inferUBinders (Nest (UAnnBinder expl b ann cs) bs) cont = do
  -- TODO: factor out the common part of each case (requires an annotated
  -- `where` clause because of the rank-2 type)
  ty <- inferAnn ann cs
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

inferAnn :: UAnn i -> [UConstraint i] -> InfererM i o (CType o)
inferAnn ann cs = case ann of
  UAnn ty -> checkUType ty
  UNoAnn -> case cs of
    WithSrcE _ (UVar ~(InternalName _ _ v)):_ -> do
      renameM v >>= getUVarType >>= \case
        Pi (CorePiType ExplicitApp [Explicit] (UnaryNest (_:>ty)) _) -> return ty
        ty -> throw TypeErr $ "Constraint should be a unary function. Got: " ++ pprint ty
    _ -> throw TypeErr "Type annotation or constraint required"

checkULamPartial :: PartialPiType o -> ULamExpr i -> InfererM i o (CoreLamExpr o)
checkULamPartial partialPiTy lamExpr = do
  PartialPiType piAppExpl expls piBs piEffs piReqTy <- return partialPiTy
  ULamExpr lamBs lamAppExpl lamEffs lamResultTy body <- return lamExpr
  checkExplicitArity expls (nestToList (const ()) lamBs)
  when (piAppExpl /= lamAppExpl) $ throw TypeErr $ "Wrong arrow. Expected "
     ++ pprint piAppExpl ++ " got " ++ pprint lamAppExpl
  checkLamBinders expls piBs lamBs \lamBs' -> do
    PairE piEffs' piReqTy' <- applyRename (piBs @@> (atomVarName <$> bindersVars lamBs')) (PairE piEffs piReqTy)
    resultTy <- case (lamResultTy, piReqTy') of
      (Nothing, Infer  ) -> return Infer
      (Just t , Infer  ) -> Check <$> checkUType t
      (Nothing, Check t) -> Check <$> return t
      (Just t , Check t') -> checkUType t >>= expectEq t' >> return (Check t')
    forM_ lamEffs \lamEffs' -> do
      lamEffs'' <- checkUEffRow lamEffs'
      expectEq (Con $ Eff piEffs') (Con $ Eff lamEffs'')
    body' <- withAllowedEffects piEffs' do
      withBlockDecls body \result -> checkOrInfer (sink resultTy) result
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
          Nest (UAnnBinder _ lamB lamAnn _) lamBsRest -> do
            case lamAnn of
              UAnn lamAnn' -> checkUType lamAnn' >>= expectEq piAnn
              UNoAnn -> return ()
            withFreshBinderInf (getNameHint lamB) Explicit piAnn \b -> do
              Abs piBs' UnitE <- applyRename (piB@>binderName b) (EmptyAbs piBs)
              extendRenamer (lamB@>sink (binderName b)) $
                checkLamBinders piExpls piBs' lamBsRest \bs -> cont (Nest b bs)
          Empty -> error "zip error"
    checkLamBinders  _ _ _ _ = error "zip error"

inferUForExpr :: UForExpr i -> InfererM i o (LamExpr CoreIR o)
inferUForExpr (UForExpr b body) = do
  withUBinder b \(WithAttrB _ b') -> do
    body' <- withBlockDecls body \result -> bottomUp result
    return $ LamExpr (UnaryNest b') body'

checkUForExpr :: UForExpr i -> TabPiType CoreIR o -> InfererM i o (LamExpr CoreIR o)
checkUForExpr (UForExpr bFor body) (TabPiType _ bPi resultTy) = do
  let uLamExpr = ULamExpr (UnaryNest bFor) ExplicitApp Nothing Nothing body
  effsAllowed <- infEffects <$> getInfState
  partialPi <- liftEnvReaderM $ refreshAbs (Abs bPi resultTy) \bPi' resultTy' -> do
    return $ PartialPiType ExplicitApp [Explicit] (UnaryNest bPi') (sink effsAllowed) (Check resultTy')
  CoreLamExpr _ lamExpr <- checkULamPartial partialPi uLamExpr
  return lamExpr

inferULam :: ULamExpr i -> InfererM i o (CoreLamExpr o)
inferULam (ULamExpr bs appExpl effs resultTy body) = do
  Abs (ZipB expls bs') (PairE effTy body') <- inferUBinders bs \_ -> do
    effs' <- fromMaybe Pure <$> mapM checkUEffRow effs
    resultTy' <- mapM checkUType resultTy
    body' <- withAllowedEffects (sink effs') do
      withBlockDecls body \result ->
        case resultTy' of
          Nothing -> bottomUp result
          Just resultTy'' -> topDown (sink resultTy'') result
    let effTy = EffTy effs' (getType body')
    return $ PairE effTy body'
  return $ CoreLamExpr (CorePiType appExpl expls bs' effTy) (LamExpr bs' body')

checkULam :: ULamExpr i -> CorePiType o -> InfererM i o (CoreLamExpr o)
checkULam ulam piTy = checkULamPartial (piAsPartialPi piTy) ulam

piAsPartialPi :: CorePiType n -> PartialPiType n
piAsPartialPi (CorePiType appExpl expls bs (EffTy effs ty)) =
  PartialPiType appExpl expls bs effs (Check ty)

typeAsPartialType :: CType n -> PartialType n
typeAsPartialType (Pi piTy) = PartialType $ piAsPartialPi piTy
typeAsPartialType ty = FullType ty

piAsPartialPiDropResultTy :: CorePiType n -> PartialPiType n
piAsPartialPiDropResultTy (CorePiType appExpl expls bs (EffTy effs _)) =
  PartialPiType appExpl expls bs effs Infer

checkInstanceParams :: Nest CBinder o any -> [UExpr i] -> InfererM i o [CExpr o]
checkInstanceParams bsTop paramsTop = go bsTop paramsTop
 where
  go :: Nest CBinder o any -> [UExpr i] -> InfererM i o [CExpr o]
  go Empty [] = return []
  go (Nest (b:>ty) bs) (x:xs) = do
    x' <- checkUParam ty x
    Abs bs' UnitE <- applySubst (b@>SubstVal x') $ Abs bs UnitE
    (x':) <$> go bs' xs
  go _ _ = error "zip error"

checkInstanceBody
  :: ClassName o -> [CExpr o]
  -> [UMethodDef i] -> InfererM i o (InstanceBody o)
checkInstanceBody className params methods = do
  ClassDef _ methodNames _ _ paramBs scBs methodTys <- lookupClassDef className
  Abs scBs' methodTys' <- applySubst (paramBs @@> (SubstVal <$> params)) $ Abs scBs $ ListE methodTys
  superclassTys <- superclassDictTys scBs'
  superclassDicts <- mapM (flip trySynthTerm Full) superclassTys
  ListE methodTys'' <- applySubst (scBs'@@>(SubstVal<$>superclassDicts)) methodTys'
  methodsChecked <- mapM (checkMethodDef className methodTys'') methods
  let (idxs, methods') = unzip $ sortOn fst $ methodsChecked
  forM_ (repeated idxs) \i ->
    throw TypeErr $ "Duplicate method: " ++ pprint (methodNames!!i)
  forM_ ([0..(length methodTys'' - 1)] `listDiff` idxs) \i ->
    throw TypeErr $ "Missing method: " ++ pprint (methodNames!!i)
  return $ InstanceBody superclassDicts methods'

superclassDictTys :: Nest CBinder o o' -> InfererM i o [CType o]
superclassDictTys Empty = return []
superclassDictTys (Nest b bs) = do
  Abs bs' UnitE <- liftHoistExcept $ hoist b $ Abs bs UnitE
  (binderType b:) <$> superclassDictTys bs'

checkMethodDef :: ClassName o -> [CorePiType o] -> UMethodDef i -> InfererM i o (Int, CExpr o)
checkMethodDef className methodTys (WithSrcE src m) = addSrcContext src do
  UMethodDef ~(InternalName _ sourceName v) rhs <- return m
  MethodBinding className' i <- renameM v >>= lookupEnv
  when (className /= className') do
    ClassBinding (ClassDef classSourceName _ _ _ _ _ _) <- lookupEnv className
    throw TypeErr $ pprint sourceName ++ " is not a method of " ++ pprint classSourceName
  (i,) <$> Con . Lam <$> checkULam rhs (methodTys !! i)

checkUEffRow :: UEffectRow i -> InfererM i o (EffectRow CoreIR o)
checkUEffRow (UEffectRow effs t) = do
   effs' <- liftM eSetFromList $ mapM checkUEff $ toList effs
   t' <- case t of
     Nothing -> return NoTail
     Just (~(SIInternalName _ v _ _)) -> do
       v' <- toAtomVar =<< renameM v
       expectEq EffKind (getType v')
       return $ EffectRowTail v'
   return $ EffectRow effs' t'

checkUEff :: UEffect i -> InfererM i o (Effect CoreIR o)
checkUEff eff = case eff of
  URWSEffect rws (~(SIInternalName _ region _ _)) -> do
    region' <- renameM region >>= toAtomVar
    expectEq (TC HeapType) (getType region')
    return $ RWSEffect rws (Var region')
  UExceptionEffect -> return ExceptionEffect
  UIOEffect        -> return IOEffect

type CaseAltIndex = Int

checkCaseAlt :: RequiredTy o -> CType o -> UAlt i -> InfererM i o (IndexedAlt o)
checkCaseAlt reqTy scrutineeTy (UAlt pat body) = do
  alt <- checkCasePat pat scrutineeTy do
    withBlockDecls body \result -> checkOrInfer (sink reqTy) result
  idx <- getCaseAltIndex pat
  return $ IndexedAlt idx alt

getCaseAltIndex :: UPat i i' -> InfererM i o CaseAltIndex
getCaseAltIndex (WithSrcB _ pat) = case pat of
  UPatCon ~(InternalName _ _ conName) _ -> do
    (_, con) <- renameM conName >>= lookupDataCon
    return con
  _ -> throw TypeErr $ "Case patterns must start with a data constructor or variant pattern"

checkCasePat
  :: UPat i i' -> CType o
  -> (forall o'. Ext o o' => InfererM i' o' (CExpr o'))
  -> InfererM i o (Alt CoreIR o)
checkCasePat (WithSrcB pos pat) scrutineeTy cont = addSrcContext pos $ case pat of
  UPatCon ~(InternalName _ _ conName) ps -> do
    (dataDefName, con) <- renameM conName >>= lookupDataCon
    tyConDef <- lookupTyCon dataDefName
    params <- inferParams scrutineeTy dataDefName
    ADTCons cons <- instantiateTyConDef tyConDef params
    DataConDef _ _ repTy idxs <- return $ cons !! con
    when (length idxs /= nestLength ps) $ throw TypeErr $
      "Unexpected number of pattern binders. Expected " ++ show (length idxs)
                                             ++ " got " ++ show (nestLength ps)
    withFreshBinderInf noHint Explicit repTy \b -> Abs b <$> do
      args <- forM idxs \projs -> undefined
        -- ans <- normalizeNaryProj (init projs) (sink $ Var $ binderVar b)
        -- emit $ Atom ans
      bindLetPats ps args $ cont
  _ -> throw TypeErr $ "Case patterns must start with a data constructor or variant pattern"

inferParams :: CType o -> TyConName o -> InfererM i o (TyConParams Expr o)
inferParams ty dataDefName = do
  TyConDef sourceName roleExpls paramBs _ <- lookupTyCon dataDefName
  let paramExpls = snd <$> roleExpls
  let inferenceExpls = paramExpls <&> \case
        Explicit -> Inferred Nothing Unify
        expl -> expl
  paramBsAbs <- buildConstraints (Abs paramBs UnitE) \params _ -> do
    let ty' = NewtypeTyCon (UserADTType sourceName (sink dataDefName) $ TyConParams paramExpls params)
    return [TypeConstraint (sink ty) ty']
  args <- inferMixedArgs sourceName inferenceExpls paramBsAbs emptyMixedArgs
  return $ TyConParams paramExpls args

bindLetPats
  :: HasNamesE e
  => Nest UPat i i' -> [CAtomVar o]
  -> (forall o'. DExt o o' => InfererM i' o' (e o'))
  -> InfererM i o (e o)
bindLetPats Empty [] cont = getDistinct >>= \Distinct -> cont
bindLetPats (Nest p ps) (x:xs) cont = bindLetPat p x $ bindLetPats ps (sink <$> xs) cont
bindLetPats _ _ _ = error "mismatched number of args"

bindLetPat
  :: HasNamesE e
  => UPat i i' -> CAtomVar o
  -> (forall o'. DExt o o' => InfererM i' o' (e o'))
  -> InfererM i o (e o)
bindLetPat (WithSrcB pos pat) v cont = addSrcContext pos $ case pat of
  UPatBinder b -> getDistinct >>= \Distinct -> extendSubst (b @> atomVarName v) cont
  -- UPatProd ps -> do
  --   let n = nestLength ps
  --   case getType v of
  --     ProdTy ts | length ts == n -> return ()
  --     ty -> throw TypeErr $ "Expected a product type but got: " ++ pprint ty
  --   xs <- forM (iota n) \i -> do
  --     normalizeProj (ProjectProduct i) (Var v) >>= emit . Atom
  --   bindLetPats ps xs cont
  -- UPatDepPair (PairB p1 p2) -> do
  --   case getType v of
  --     DepPairTy _ -> return ()
  --     ty -> throw TypeErr $ "Expected a dependent pair, but got: " ++ pprint ty
  --   x1 <- getFst (Var v) >>= emit . Atom
  --   bindLetPat p1 x1 do
  --     x2  <- getSnd (sink $ Var v) >>= emit . Atom
  --     bindLetPat p2 x2 do
  --       cont
  -- UPatCon ~(InternalName _ _ conName) ps -> do
  --   (dataDefName, _) <- lookupDataCon =<< renameM conName
  --   TyConDef _ _ _ cons <- lookupTyCon dataDefName
  --   case cons of
  --     ADTCons [DataConDef _ _ _ idxss] -> do
  --       when (length idxss /= nestLength ps) $ throw TypeErr $
  --         "Unexpected number of pattern binders. Expected " ++ show (length idxss)
  --                                                ++ " got " ++ show (nestLength ps)
  --       void $ inferParams (getType $ Var v) dataDefName
  --       x <- cheapNormalize $ Var v
  --       xs <- forM idxss \idxs -> normalizeNaryProj idxs x >>= emit . Atom
  --       bindLetPats ps xs cont
  --     _ -> throw TypeErr $ "sum type constructor in can't-fail pattern"
  UPatTable ps -> undefined
  -- UPatTable ps -> do
  --   let n = fromIntegral (nestLength ps) :: Word32
  --   cheapNormalize (getType v) >>= \case
  --     TabPi (TabPiType _ (_:>FinConst n') _) | n == n' -> return ()
  --     ty -> throw TypeErr $ "Expected a Fin " ++ show n ++ " table type but got: " ++ pprint ty
  --   xs <- forM [0 .. n - 1] \i -> do
  --     emit =<< mkTabApp (Var v) [NewtypeCon (FinCon (NatVal n)) (NatVal $ fromIntegral i)]
  --   bindLetPats ps xs cont

checkUType :: UType i -> InfererM i o (CType o)
checkUType t = undefined
-- checkUType t = do
--   Type t' <- checkUParam TyKind t
--   return t'

checkUParam :: Kind CoreIR o -> UType i -> InfererM i o (CExpr o)
checkUParam k uty@(WithSrcE pos _) = addSrcContext pos $
  withReducibleEmissions msg $ withAllowedEffects Pure $ topDownExplicit (sink k) uty
  where msg = "Can't reduce type expression: " ++ pprint uty

inferTabCon :: forall i o. [UExpr i] -> InfererM i o (CExpr o)
inferTabCon xs = do
  let n = fromIntegral (length xs) :: Word32
  let finTy = undefined -- FinConst n
  elemTy <- case xs of
    []  -> throw TypeErr "Can't infer type of empty table"
    x:_ -> getType <$> bottomUp x
  ixTy <- asIxType finTy
  let tabTy = ixTy ==> elemTy
  xs' <- forM xs \x -> topDown elemTy x
  dTy <- DictTy <$> dataDictType elemTy
  dataDict <- trySynthTerm dTy Full
  return $ TabCon (Just $ WhenIRE dataDict) tabTy xs'

checkTabCon :: forall i o. TabPiType CoreIR o -> [UExpr i] -> InfererM i o (CExpr o)
checkTabCon tabTy@(TabPiType _ b elemTy) xs = do
  let n = fromIntegral (length xs) :: Word32
  let finTy = undefined -- FinConst n
  expectEq (binderType b) finTy
  xs' <- forM (enumerate xs) \(i, x) -> do
    let i' = Con $ NewtypeCon (FinCon (toExpr $ NatVal n)) (toExpr $ NatVal $ fromIntegral i)
    elemTy' <- applySubst (b@>SubstVal i') elemTy
    topDown elemTy' x
  dTy <- case hoist b elemTy of
    HoistSuccess elemTy' -> DictTy <$> dataDictType elemTy'
    HoistFailure _ -> ignoreExcept <$> liftEnvReaderT do
      withFreshBinder noHint finTy \b' ->  do
        elemTy' <- applyRename (b@>binderName b') elemTy
        dTy <- DictTy <$> dataDictType elemTy'
        return $ Pi $ CorePiType ImplicitApp [Inferred Nothing Unify] (UnaryNest b') (EffTy Pure dTy)
  dataDict <- trySynthTerm dTy Full
  return $ TabCon (Just $ WhenIRE dataDict) (TabPi tabTy) xs'

addEffects :: EffectRow CoreIR o -> InfererM i o ()
addEffects Pure = return ()
addEffects eff = do
  effsAllowed <- infEffects <$> getInfState
  case checkExtends effsAllowed eff of
    Success () -> return ()
    Failure _  -> expectEq (Con $ Eff effsAllowed) (Con $ Eff eff)

getIxDict :: CType o -> InfererM i o (IxDict CoreIR o)
getIxDict t = do
  dictTy <- DictTy <$> ixDictType t
  IxDictAtom <$> trySynthTerm dictTy Full

asIxType :: CType o -> InfererM i o (IxType CoreIR o)
asIxType ty = IxType ty <$> getIxDict ty

-- === Solver ===

-- TODO: put this pattern and friends in the Name library? Don't really want to
-- have to think about `eqNameColorRep` just to implement a partial map.
lookupSolverSubst :: forall c n. Color c => SolverSubst n -> Name c n -> ExprSubstVal c n
lookupSolverSubst (SolverSubst m) name =
  case eqColorRep of
    Nothing -> Rename name
    Just (ColorsEqual :: ColorsEqual c (AtomNameC CoreIR))-> case M.lookup name m of
      Nothing -> Rename name
      Just sol -> SubstVal sol

applyConstraint :: Constraint o -> SolverM i o ()
applyConstraint = \case
  TypeConstraint t1 t2 -> constrainTypesEq t1 t2
  EffectConstraint r1 r2' -> do
    -- r1 shouldn't have inference variables. And we can't infer anything about
    -- any inference variables in r2's explicit effects because we don't know
    -- how they line up with r1's. So this is just about figuring out r2's tail.
    r2 <- zonk r2'
    let msg = "Allowed effects:   " ++ pprint r1 ++
            "\nRequested effects: " ++ pprint r2
    case checkExtends r1 r2 of
      Success () -> return ()
      Failure _  -> addContext msg $ searchFailureAsTypeErr do
        EffectRow effs1 t1 <- return r1
        EffectRow effs2 (EffectRowTail v2) <- return r2
        guard =<< isUnificationName (atomVarName v2)
        guard $ null (eSetToList $ effs2 `eSetDifference` effs1)
        let extras1 = effs1 `eSetDifference` effs2
        extendSolution (atomVarName v2) (Con $ Eff $ EffectRow extras1 t1)

constrainTypesEq :: CType o -> CType o -> SolverM i o ()
constrainTypesEq t1 t2 = constrainEq (Con (TypeCon t1)) (Con (TypeCon t2)) -- TODO: use a type class instead?

constrainEq :: CExpr o -> CExpr o -> SolverM i o ()
constrainEq t1 t2 = do
  t1' <- zonk t1
  t2' <- zonk t2
  msg <- liftEnvReaderM $ do
    ab <- renameForPrinting $ PairE t1' t2'
    return $ canonicalizeForPrinting ab \(Abs infVars (PairE t1Pretty t2Pretty)) ->
              "Expected: " ++ pprint t1Pretty
         ++ "\n  Actual: " ++ pprint t2Pretty
         ++ (case infVars of
               Empty -> ""
               _ -> "\n(Solving for: " ++ pprint (nestToList pprint infVars) ++ ")")
  void $ addContext msg $ unify t1' t2'

class (AlphaEqE e, Zonkable e) => Unifiable (e::E) where
  unifyZonked :: e n -> e n -> SolverM i n ()

unify :: Unifiable e => e n -> e n -> SolverM i n ()
unify e1 e2 = do
  e1' <- zonk e1
  e2' <- zonk e2
  searchFailureAsTypeErr $ unifyZonked e1' e2'
{-# INLINE unify #-}
{-# SCC unify #-}

searchFailureAsTypeErr :: SolverM i n a -> SolverM i n a
searchFailureAsTypeErr cont = cont <|> throw TypeErr ""
{-# INLINE searchFailureAsTypeErr #-}

instance Unifiable (Expr CoreIR) where
  unifyZonked e1 e2 = undefined

    -- confuseGHC >>= \_ -> case sameConstructor e1 e2 of
    -- False -> case (e1, e2) of
    --   (t, Var (AtomVar v _)) -> extendSolution v t
    --   (Var (AtomVar v _), t) -> extendSolution v t
    --   _ -> empty
    -- True -> case (e1, e2) of
    --   (Var (AtomVar v' _), Var (AtomVar v _)) ->
    --     if v == v' then return () else extendSolution v e1 <|> extendSolution v' e2
    --   (Eff eff, Eff eff') -> unify eff eff'
    --   (Type t, Type t') -> case (t, t') of
    --     (Pi piTy, Pi piTy') -> unify piTy piTy'
    --     (TabPi piTy, TabPi piTy') -> unifyTabPiType piTy piTy'
    --     (TC con, TC con') -> do
    --       GenericOpRep name  ts  xs  [] <- return $ fromEGenericOpRep con
    --       GenericOpRep name' ts' xs' [] <- return $ fromEGenericOpRep con'
    --       guard $ name == name' && length ts == length ts' && length xs == length xs'
    --       zipWithM_ unify (Type <$> ts) (Type <$> ts')
    --       zipWithM_ unify xs xs'
    --     (DictTy d, DictTy d') -> unify d d'
    --     (NewtypeTyCon con, NewtypeTyCon con') -> unify con con'
    --     _ -> unifyEq t t'
    --   _ -> unifyEq e1 e2

instance Unifiable DictType where
  unifyZonked (DictType _ c params) (DictType _ c' params') =
    guard (c == c') >> zipWithM_ unify params params'
  {-# INLINE unifyZonked #-}

instance Unifiable NewtypeTyCon where
  unifyZonked e1 e2 = case (e1, e2) of
    (Nat, Nat) -> return ()
    (Fin n, Fin n') -> unify n n'
    (EffectRowKind, EffectRowKind) -> return ()
    (UserADTType _ c params, UserADTType _ c' params') -> guard (c == c') >> unify params params'
    _ -> empty

instance Unifiable (IxType CoreIR) where
  -- We ignore the dictionaries because we assume coherence
  unifyZonked (IxType t _) (IxType t' _) = unifyZonked t t'

instance Unifiable (Type CoreIR) where
  unifyZonked t t' = undefined -- unifyZonked (Type t) (Type t')

instance Unifiable (TyConParams Expr) where
  -- We ignore the dictionaries because we assume coherence
  unifyZonked ps ps' = zipWithM_ unify (ignoreSynthParams ps) (ignoreSynthParams ps')

instance Unifiable (EffectRow CoreIR) where
  unifyZonked x1 x2 =
        unifyDirect x1 x2
    <|> unifyDirect x2 x1
    <|> unifyZip x1 x2

   where
     unifyDirect :: EffectRow CoreIR n -> EffectRow CoreIR n -> SolverM i n ()
     unifyDirect r@(EffectRow effs' mv') (EffectRow effs (EffectRowTail v)) | null (eSetToList effs) =
       case mv' of
         EffectRowTail v' | v == v' -> guard $ null $ eSetToList effs'
         _ -> extendSolution (atomVarName v) (Con $ Eff r)
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
  withFreshUnificationVar MiscInfVar EffKind \v -> do
    cont $ EffectRow mempty $ EffectRowTail v
{-# INLINE withFreshEff #-}

unifyEq :: AlphaEqE e => e n -> e n -> SolverM i n ()
unifyEq e1 e2 = guard =<< alphaEq e1 e2
{-# INLINE unifyEq #-}

instance Unifiable CorePiType where
  unifyZonked (CorePiType appExpl1 expls1 bsTop1 effTy1)
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

unifyTabPiType :: TabPiType CoreIR n -> TabPiType CoreIR n -> SolverM i n ()
unifyTabPiType (TabPiType _ b1 ty1) (TabPiType _ b2 ty2) = do
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
      liftHoistExcept $ hoist b ans
    diff' <- liftHoistExcept $ hoist b diff
    return (ans, diff')
{-# INLINE withFreshSkolemName #-}

extendSolution :: CAtomName n -> CExpr n -> SolverM i n ()
extendSolution v t =
  isUnificationName v >>= \case
    True -> do
      when (v `isFreeIn` t) $ throw TypeErr $ "Occurs check failure: " ++ pprint (v, t)
      -- When we unify under a pi binder we replace its occurrences with a
      -- skolem variable. We don't want to unify with terms containing these
      -- variables because that would mean inferring dependence, which is a can
      -- of worms.
      forM_ (freeAtomVarsList t) \fv ->
        whenM (isSkolemName fv) $ throw TypeErr $ "Can't unify with skolem vars"
      addConstraint v t
    False -> empty

isUnificationName :: EnvReader m => CAtomName n -> m n Bool
isUnificationName v = lookupEnv v >>= \case
  AtomNameBinding (SolverBound (InfVarBound _ _)) -> return True
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

renameForPrinting :: (EnvReader m, HasNamesE e)
                   => e n -> m n (Abs (Nest (AtomNameBinder CoreIR)) e n)
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

-- === dictionary synthesis ===

-- Given a simplified dict (an Atom of type `DictTy _` in the
-- post-simplification IR), and a requested, more general, dict type, generalize
-- the dict to match the more general type. This is only possible because we
-- require that instances are polymorphic in data-role parameters. It would be
-- valid to implement `generalizeDict` by re-synthesizing the whole dictionary,
-- but we know that the derivation tree has to be the same, so we take the
-- shortcut of just generalizing the data parameters.
generalizeDict :: EnvReader m => CType n -> Dict n -> m n (Dict n)
generalizeDict ty dict = do
  result <- liftEnvReaderT $ liftInfererM $ generalizeDictRec ty dict
  case result of
    Failure e -> error $ "Failed to generalize " ++ pprint dict
      ++ " to " ++ pprint ty ++ " because " ++ pprint e
    Success ans -> return ans

generalizeDictRec :: CType n -> Dict n -> InfererM i n (Dict n)
generalizeDictRec targetTy dict = do
  Con (DictCon _ dict') <- return dict -- TODO: normalize
  case dict' of
    InstanceDict instanceName args -> do
      InstanceDef _ roleExpls bs _ _ <- lookupInstanceDef instanceName
      liftSolverM $ generalizeInstanceArgs roleExpls bs args \args' -> do
        d <- mkDictExpr $ InstanceDict (sink instanceName) args'
        constrainEq (sink $ Con $ TypeCon targetTy) (Con $ TypeCon $ getType d)
        return d
    IxFin _ -> case targetTy of
      DictTy (DictType "Ix" _ [Con (TypeCon (NewtypeTyCon (Fin n)))]) -> mkDictExpr $ IxFin n
      _ -> error $ "not an Ix(Fin _) dict: " ++ pprint targetTy
    InstantiatedGiven _ _ -> notSimplifiedDict
    SuperclassProj _ _    -> notSimplifiedDict
    DataData _ -> case targetTy of
      DictTy (DictType "Data" _ [Con (TypeCon t)]) -> mkDictExpr $ DataData t
      _ -> error "not a data dict"
    where notSimplifiedDict = error $ "Not a simplified dict: " ++ pprint dict

mkDictExpr :: EnvReader m => DictExpr n -> m n (CExpr n)
mkDictExpr d = do
  ty <- typeOfDictExpr d
  return $ Con $ DictCon ty d

generalizeInstanceArgs
  :: Zonkable e => [RoleExpl] -> Nest CBinder o any -> [CExpr o]
  -> (forall o'. DExt o o' => [CExpr o'] -> SolverM i o' (e o'))
  -> SolverM i o (e o)
generalizeInstanceArgs [] Empty [] cont = withDistinct $ cont []
generalizeInstanceArgs ((role,_):expls) (Nest (b:>ty) bs) (arg:args) cont = do
  generalizeInstanceArg role ty arg \arg' -> do
    Abs bs' UnitE <- applySubst (b@>SubstVal arg') (Abs bs UnitE)
    generalizeInstanceArgs expls bs' (sink <$> args) \args' ->
      cont $ sink arg' : args'
generalizeInstanceArgs _ _ _ _ = error "zip error"

generalizeInstanceArg
  :: Zonkable e => ParamRole -> CType o -> CExpr o
  -> (forall o'. DExt o o' => CExpr o' -> SolverM i o' (e o'))
  -> SolverM i o (e o)
generalizeInstanceArg role ty arg cont = case role of
  -- XXX: for `TypeParam` we can just emit a fresh inference name rather than
  -- traversing the whole type like we do in `Generalize.hs`. The reason is
  -- that it's valid to implement `generalizeDict` by synthesizing an entirely
  -- fresh dictionary, and if we were to do that, we would infer this type
  -- parameter exactly as we do here, using inference.
  TypeParam -> withFreshUnificationVar  MiscInfVar TyKind \v -> cont $ Var v
  DictParam -> withFreshDictVar  ty (\ty' -> lift11 $ generalizeDictRec ty' (sink arg)) cont
  DataParam -> withFreshUnificationVar MiscInfVar ty \v -> cont $ Var v

emitInstanceDef :: (Mut n, TopBuilder m) => InstanceDef n -> m n (Name InstanceNameC n)
emitInstanceDef instanceDef@(InstanceDef className _ _ _ _) = do
  ty <- getInstanceType instanceDef
  emitBinding (getNameHint className) $ InstanceBinding instanceDef ty

-- main entrypoint to dictionary synthesizer
trySynthTerm :: CType n -> RequiredMethodAccess -> InfererM i n (SynthExpr n)
trySynthTerm ty reqMethodAccess = do
  hasInferenceVars ty >>= \case
    True -> throw TypeErr $ "Can't synthesize a dictionary for a type with inference vars: " ++ pprint ty
    False -> withVoidSubst do
      synthTy <- liftExcept $ typeAsSynthType ty
      synthTerm synthTy reqMethodAccess
        <|> throw TypeErr ("Couldn't synthesize a class dictionary for: " ++ pprint ty)
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

type SynthExpr = CExpr
type SynthPiType n = ([Explicitness], Abs (Nest CBinder) DictType n)
data SynthType n =
   SynthDictType (DictType n)
 | SynthPiType (SynthPiType n)
   deriving (Show, Generic)

data Givens n = Givens { fromGivens :: HM.HashMap (EKey SynthType n) (SynthExpr n) }

getGivens :: InfererM i o (Givens o)
getGivens = givens <$> getInfState

withGivens :: Givens o -> InfererM i o a -> InfererM i o a
withGivens givens cont = withInfState (\s -> s { givens = givens }) cont

extendGivens :: [SynthExpr o] -> InfererM i o a -> InfererM i o a
extendGivens newGivens cont = do
  prevGivens <- getGivens
  finalGivens <- getSuperclassClosure prevGivens newGivens
  withGivens finalGivens cont
{-# INLINE extendGivens #-}

getSynthType :: SynthExpr n -> SynthType n
getSynthType x = ignoreExcept $ typeAsSynthType (getType x)
{-# INLINE getSynthType #-}

typeAsSynthType :: CType n -> Except (SynthType n)
typeAsSynthType = \case
  DictTy dictTy -> return $ SynthDictType dictTy
  Pi (CorePiType ImplicitApp expls bs (EffTy Pure (DictTy d))) -> return $ SynthPiType (expls, Abs bs d)
  ty -> Failure $ Err TypeErr mempty $ "Can't synthesize terms of type: " ++ pprint ty
{-# SCC typeAsSynthType #-}

getSuperclassClosure :: EnvReader m => Givens n -> [SynthExpr n] -> m n (Givens n)
getSuperclassClosure givens newGivens = do
  Distinct <- getDistinct
  env <- unsafeGetEnv
  return $ getSuperclassClosurePure env givens newGivens
{-# INLINE getSuperclassClosure #-}

getSuperclassClosurePure :: Distinct n => Env n -> Givens n -> [SynthExpr n] -> Givens n
getSuperclassClosurePure env givens newGivens =
  snd $ runState (runEnvReaderT env (mapM_ visitGiven newGivens)) givens
  where
    visitGiven :: SynthExpr n -> EnvReaderT (State (Givens n)) n ()
    visitGiven x = alreadyVisited x >>= \case
      True -> return ()
      False -> do
        markAsVisited x
        parents <- getDirectSuperclasses x
        mapM_ visitGiven parents

    alreadyVisited :: SynthExpr n -> EnvReaderT (State (Givens n)) n Bool
    alreadyVisited x = do
      Givens m <- get
      ty <- return $ getSynthType x
      return $ EKey ty `HM.member` m

    markAsVisited :: SynthExpr n -> EnvReaderT (State (Givens n)) n ()
    markAsVisited x = do
      ty <- return $ getSynthType x
      modify \(Givens m) -> Givens $ HM.insert (EKey ty) x m

    getDirectSuperclasses :: SynthExpr n -> EnvReaderT (State (Givens n)) n [SynthExpr n]
    getDirectSuperclasses synthExpr = do
      synthTy <- return $ getSynthType synthExpr
      superclasses <- case synthTy of
        SynthPiType _ -> return []
        SynthDictType dTy -> getSuperclassTys dTy
      forM (enumerate superclasses) \(i, ty) -> do
        return $ Con $ DictCon ty $ SuperclassProj synthExpr i

synthTerm :: SynthType n -> RequiredMethodAccess -> InfererM i n (SynthExpr n)
synthTerm targetTy reqMethodAccess = confuseGHC >>= \_ -> case targetTy of
  SynthPiType (expls, ab) -> do
    ab' <- withFreshBindersInf expls ab \bs' targetTy' -> do
      Abs bs' <$> synthTerm (SynthDictType targetTy') reqMethodAccess
    Abs bs' synthExpr <- return ab'
    let piTy = CorePiType ImplicitApp expls bs' (EffTy Pure (getType synthExpr))
    return $ Con $ Lam $ CoreLamExpr piTy $ LamExpr bs' synthExpr
  SynthDictType dictTy -> case dictTy of
    DictType "Ix" _ [Con (TypeCon (NewtypeTyCon (Fin n)))] ->
      return $ Con $ DictCon (DictTy dictTy) $ IxFin n
    DictType "Data" _ [Con (TypeCon t)] -> do
      void (synthDictForData dictTy <|> synthDictFromGiven dictTy)
      return $ Con $ DictCon (DictTy dictTy) $ DataData t
    _ -> do
      dict <- synthDictFromInstance dictTy <|> synthDictFromGiven dictTy
      case dict of
        -- TODO: normalize first?
        Con (DictCon _ (InstanceDict instanceName _)) -> do
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
  ClassDef _ _ _ _ _ _ methodTys <- lookupClassDef className
  let numClassMethods = length methodTys
  case access of
    Full                  -> return $ numClassMethods == numInstanceMethods
    Partial numReqMethods -> return $ numReqMethods   <= numInstanceMethods

synthDictFromGiven :: DictType n -> InfererM i n (SynthExpr n)
synthDictFromGiven targetTy = do
  givens <- ((HM.elems . fromGivens) <$> getGivens)
  asum $ givens <&> \given -> do
    case getSynthType given of
      SynthDictType givenDictTy -> do
        guard =<< alphaEq targetTy givenDictTy
        return given
      SynthPiType givenPiTy -> do
        args <- instantiateSynthArgs targetTy givenPiTy
        return $ Con $ DictCon (DictTy targetTy) $ InstantiatedGiven given args

synthDictFromInstance :: DictType n -> InfererM i n (SynthExpr n)
synthDictFromInstance targetTy@(DictType _ targetClass _) = do
  instances <- getInstanceDicts targetClass
  asum $ instances <&> \candidate -> typeErrAsSearchFailure do
    CorePiType _ expls bs (EffTy _ (DictTy candidateTy)) <- lookupInstanceTy candidate
    args <- instantiateSynthArgs targetTy (expls, Abs bs candidateTy)
    return $ Con $ DictCon (DictTy targetTy) $ InstanceDict candidate args

getInstanceDicts :: EnvReader m => ClassName n -> m n [InstanceName n]
getInstanceDicts name = do
  env <- withEnv moduleEnv
  return $ M.findWithDefault [] name $ instanceDicts $ envSynthCandidates env
{-# INLINE getInstanceDicts #-}

instantiateSynthArgs :: DictType n -> SynthPiType n -> InfererM i n [CExpr n]
instantiateSynthArgs target (expls, synthPiTy) = do
  liftM fromListE $ withReducibleEmissions "dict args" do
    bsConstrained <- buildConstraints (sink synthPiTy) \_ resultTy -> do
      return [TypeConstraint (DictTy $ sink target) (DictTy resultTy)]
    ListE <$> inferMixedArgs "dict" expls bsConstrained emptyMixedArgs

emptyMixedArgs :: MixedArgs (CExpr n)
emptyMixedArgs = ([], [])

typeErrAsSearchFailure :: InfererM i n a -> InfererM i n a
typeErrAsSearchFailure cont = cont `catchErr` \err@(Err errTy _ _) -> do
  case errTy of
    TypeErr -> empty
    _ -> throwErr err

synthDictForData :: forall i n. DictType n -> InfererM i n (SynthExpr n)
synthDictForData dictTy@(DictType "Data" dName [Con (TypeCon ty)]) = undefined
-- synthDictForData dictTy@(DictType "Data" dName [Type ty]) = case ty of
--   -- TODO Deduplicate vs CheckType.checkDataLike
--   -- The "Var" case is different
--   TyVar _ -> synthDictFromGiven dictTy
--   TabPi (TabPiType _ b eltTy) -> recurBinder (Abs b eltTy) >> success
--   DepPairTy (DepPairType _ b@(_:>l) r) -> do
--     recur l >> recurBinder (Abs b r) >> success
--   NewtypeTyCon nt -> do
--     (_, ty') <- unwrapNewtypeType nt
--     recur ty' >> success
--   TC con -> case con of
--     BaseType _       -> success
--     ProdType as      -> mapM_ recur as >> success
--     SumType  cs      -> mapM_ recur cs >> success
--     RefType _ _      -> success
--     HeapType         -> success
--     _ -> notData
--   _   -> notData
--   where
--     recur ty' = synthDictForData $ DictType "Data" dName [Type ty']
--     recurBinder :: Abs CBinder CType n -> InfererM i n (SynthExpr n)
--     recurBinder (Abs b body) =
--       withFreshBinderInf noHint Explicit (binderType b) \b' -> do
--         body' <- applyRename (b@>binderName b') body
--         ans <- synthDictForData $ DictType "Data" (sink dName) [Type body']
--         return $ ignoreHoistFailure $ hoist b' ans
--     notData = empty
--     success = return $ DictCon (DictTy dictTy) $ DataData ty
-- synthDictForData dictTy = error $ "Malformed Data dictTy " ++ pprint dictTy

instance GenericE Givens where
  type RepE Givens = HashMapE (EKey SynthType) SynthExpr
  fromE (Givens m) = HashMapE m
  {-# INLINE fromE #-}
  toE (HashMapE m) = Givens m
  {-# INLINE toE #-}

instance SinkableE Givens where

-- === IFunType ===

asFFIFunType :: EnvReader m => CType n -> m n (Maybe (IFunType, CorePiType n))
asFFIFunType ty = return do
  Pi piTy <- return ty
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
checkScalar ty = throw TypeErr $ pprint ty

checkScalarOrPairType :: (IRRep r, Fallible m) => Type r n -> m [BaseType]
checkScalarOrPairType (PairTy a b) = do
  tys1 <- checkScalarOrPairType a
  tys2 <- checkScalarOrPairType b
  return $ tys1 ++ tys2
checkScalarOrPairType (BaseTy ty) = return [ty]
checkScalarOrPairType ty = throw TypeErr $ pprint ty

-- === instances ===

instance DiffStateE SolverSubst SolverDiff where
  updateDiffStateE :: forall n. Distinct n => Env n -> SolverSubst n -> SolverDiff n -> SolverSubst n
  updateDiffStateE _ initState (SolverDiff (RListE diffs)) = foldl update initState (unsnoc diffs)
    where
     update :: Distinct n => SolverSubst n -> Solution n -> SolverSubst n
     update (SolverSubst subst) (PairE v x) = SolverSubst $ M.insert v x subst

instance SinkableE InfState where sinkingProofE _ = todoSinkableProof

instance GenericE SigmaExpr where
  type RepE SigmaExpr = EitherE3 (LiftE (Maybe SourceName) `PairE` CExpr)
                                 (LiftE SourceName `PairE` CType `PairE` UVar)
                                 (CType `PairE` CExpr `PairE` ListE CExpr)
  fromE = \case
    SigmaExpr x y         -> Case0 $ LiftE x `PairE` y
    SigmaUVar x y z       -> Case1 $ LiftE x `PairE` y `PairE` z
    SigmaPartialApp x y z -> Case2 $ x `PairE` y `PairE` ListE z
  {-# INLINE fromE #-}

  toE = \case
    Case0 (LiftE x `PairE` y)           -> SigmaExpr x y
    Case1 (LiftE x `PairE` y `PairE` z) -> SigmaUVar x y z
    Case2 (x `PairE` y `PairE` ListE z) -> SigmaPartialApp x y z
    _ -> error "impossible"
  {-# INLINE toE #-}

instance RenameE SigmaExpr
instance HoistableE SigmaExpr
instance SinkableE SigmaExpr

-- instance SubstE ExprSubstVal SigmaExpr where
--   substE env (SigmaExpr sn x) = SigmaExpr sn $ substE env x
--   substE env (SigmaUVar sn ty uvar) = case uvar of
--     UAtomVar v -> substE env $ SigmaExpr (Just sn) $ Var (AtomVar v ty)
--     UTyConVar   v -> SigmaUVar sn ty' $ UTyConVar   $ substE env v
--     UDataConVar v -> SigmaUVar sn ty' $ UDataConVar $ substE env v
--     UPunVar     v -> SigmaUVar sn ty' $ UPunVar     $ substE env v
--     UClassVar   v -> SigmaUVar sn ty' $ UClassVar   $ substE env v
--     UMethodVar  v -> SigmaUVar sn ty' $ UMethodVar  $ substE env v
--     where ty' = substE env ty
--   substE env (SigmaPartialApp ty f xs) =
--     SigmaPartialApp (substE env ty) (substE env f) (map (substE env) xs)

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
instance SubstE ExprSubstVal SynthType

instance GenericE Constraint where
  type RepE Constraint = EitherE
                           (PairE CType CType)
                           (PairE (EffectRow CoreIR) (EffectRow CoreIR))
  fromE (TypeConstraint   t1 t2) = LeftE  (PairE t1 t2)
  fromE (EffectConstraint e1 e2) = RightE (PairE e1 e2)
  {-# INLINE fromE #-}
  toE (LeftE  (PairE t1 t2)) = TypeConstraint   t1 t2
  toE (RightE (PairE e1 e2)) = EffectConstraint e1 e2
  {-# INLINE toE #-}

instance SinkableE             Constraint
instance HoistableE            Constraint
instance (SubstE ExprSubstVal) Constraint

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
  type RepE SolverSubst = ListE (PairE CAtomName CExpr)
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
