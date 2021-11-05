-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module SaferNames.Inference (inferModule) where

import Prelude hiding ((.), id)
import Control.Category
import Control.Applicative
import Control.Monad
import Control.Monad.State (get, modify, runState)
import Control.Monad.Writer.Strict (execWriterT, tell)
import Control.Monad.Reader
import Data.Foldable (toList)
import Data.Functor ((<&>))
import Data.List (sortOn)
import Data.Maybe (fromJust)
import Data.String (fromString)
import Data.Text.Prettyprint.Doc (Pretty (..))
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import SaferNames.Name
import SaferNames.Builder
import SaferNames.Syntax
import SaferNames.Type
import SaferNames.PPrint ()
import SaferNames.CheapReduction

import LabeledItems
import Err
import Util

inferModule :: Distinct n => Bindings n -> UModule n -> Except (Module n)
inferModule bindings uModule@(UModule decl _) = do
  if isTopDecl decl
    then do
      DistinctAbs bindingsFrag sourceMap <- runTopInfererM bindings do
        UModule decl' sourceMap <- injectM uModule
        inferUDeclTop decl' $ substM sourceMap
      let scs = bindingsFragToSynthCandidates bindingsFrag
      return $ Module Core id $
        EvaluatedModule bindingsFrag scs sourceMap
    else do
      ab <- runInfererM bindings do
        UModule decl' sourceMap <- return uModule
        Abs decls (ZonkableSM sourceMap') <- buildScoped $
          inferUDeclLocal decl' do
            applyDefaults
            ZonkableSM <$> substM sourceMap
        return $ Abs decls sourceMap'
      DistinctAbs decls sourceMap <- return $ refreshAbs (toScope bindings) ab
      let scs = bindingsFragToSynthCandidates $ boundBindings decls
      return $ Module Core decls $
        EvaluatedModule emptyOutFrag scs sourceMap

isTopDecl :: UDecl n l -> Bool
isTopDecl decl = case decl of
  ULet         _ _ _     -> False
  UDataDefDecl _ _ _     -> True
  UInterface   _ _ _ _ _ -> True
  UInstance    _ _ _ _ _ -> False

-- === Top-level inferer ===

class ( MonadFail2 m, Fallible2 m, CtxReader2 m, TopBuilder2 m
      , EnvReader Name m) => TopInferer m where
  liftLocalInferer :: (SubstE AtomSubstVal e, InjectableE e)
                   => (forall o'. InfererM i o' (e o'))
                   -> m i o (e o)

newtype TopInfererM i o a = TopInfererM
  { runTopInfererM' :: EnvReaderT Name (TopBuilderT FallibleM) i o a }
  deriving ( Functor, Applicative, Monad, MonadFail, ScopeReader
           , Fallible, CtxReader, EnvReader Name, BindingsReader, TopBuilder)

instance TopInferer TopInfererM where
  liftLocalInferer cont = do
    env <- getEnv
    WithBindings bindings env' <- addBindings env
    result <- liftExcept $ runSubstInfererM bindings env' do
      ans <- cont
      applyDefaults
      zonk ans
    injectM result

runTopInfererM
  :: Distinct n
  => Bindings n
  -> (forall l. Ext n l => TopInfererM l l (e l))
  -> Except (DistinctAbs BindingsFrag e n)
runTopInfererM bindings cont =
  runFallibleM $ runTopBuilderT bindings $ runEnvReaderT idEnv $
    runTopInfererM' $ cont

applyDefaults :: Inferer m => m i o ()
applyDefaults = do
  Defaults defaults <- getDefaults
  forM_ defaults \(ty, ty') ->
    tryConstrainEq ty (injectFromTop ty')

-- === Inferer interface ===

class ( MonadFail2 m, Fallible2 m, Catchable2 m, CtxReader2 m, Builder2 m
      , EnvReader Name m, Solver2 m)
      => Inferer (m::MonadKind2) where
  liftSolverM :: SolverM o a -> m i o a

inferSuggestionStrength :: Type n -> SuggestionStrength
inferSuggestionStrength ty = case hoistToTop ty of
  Nothing -> Suggest
  Just _  -> Concrete

-- === Concrete Inferer monad ===

data InfOutMap (n::S) =
  InfOutMap
    (Bindings n)
    (SolverSubst n)
    (Defaults n)
    -- the subset of the names in the bindings whose definitions may contain
    -- inference vars (this is so we can avoid zonking everything in scope when
    -- we zonk bindings)
    (UnsolvedBindings n)
    (SynthesisVars n)

type SynthesisVars = ListE AtomName

newtype Defaults (n::S) = Defaults [(Atom n, Atom VoidS)]
        deriving (Semigroup, Monoid, Show)

instance GenericE Defaults where
  type RepE Defaults = ListE (PairE Atom (LiftE (Atom VoidS)))
  fromE (Defaults xys) = ListE [PairE x (LiftE y) | (x, y) <- xys]
  toE (ListE xys) = Defaults [(x, y) | PairE x (LiftE y) <- xys]

instance InjectableE         Defaults
instance SubstE Name         Defaults
instance SubstE AtomSubstVal Defaults
instance HoistableE          Defaults

data InfOutFrag (n::S) (l::S) = InfOutFrag (InfEmissions n l) (Defaults l) (SolverSubst l)

type InfEmission  = EitherE DeclBinding SolverBinding
type InfEmissions = Nest (BinderP AtomNameC InfEmission)

instance GenericB InfOutFrag where
  type RepB InfOutFrag = PairB InfEmissions (LiftB (PairE Defaults SolverSubst))
  fromB (InfOutFrag emissions defaults solverSubst) =
    PairB emissions (LiftB (PairE defaults solverSubst))
  toB (PairB emissions (LiftB (PairE defaults solverSubst))) =
    InfOutFrag emissions defaults solverSubst

instance ProvesExt   InfOutFrag
instance SubstB Name InfOutFrag
instance BindsNames  InfOutFrag
instance InjectableB InfOutFrag

instance OutFrag InfOutFrag where
  emptyOutFrag = InfOutFrag Empty mempty emptySolverSubst
  catOutFrags scope (InfOutFrag em ds ss) (InfOutFrag em' ds' ss') =
    withExtEvidence em' $
      InfOutFrag (em >>> em') (inject ds <> ds') (catSolverSubsts scope (inject ss) ss')

instance HasScope InfOutMap where
  toScope (InfOutMap bindings _ _ _ _) = toScope bindings

instance OutMap InfOutMap where
  emptyOutMap = InfOutMap emptyOutMap emptySolverSubst mempty mempty mempty

instance ExtOutMap InfOutMap BindingsFrag where
  extendOutMap (InfOutMap bindings ss dd oldUn svs) frag =
    withExtEvidence frag do
      let newUn = UnsolvedBindings $ getAtomNames frag
      -- as an optimization, only do the zonking for the new stuff
      let newBindings = bindings `extendOutMap` frag
      let (zonkedUn, zonkedBindings) = zonkUnsolvedBindings (inject ss) newUn newBindings
      InfOutMap zonkedBindings (inject ss) (inject dd) (inject oldUn <> zonkedUn) (inject svs)

newtype UnsolvedBindings (n::S) =
  UnsolvedBindings { fromUnsolvedBindings :: S.Set (AtomName n) }
  deriving (Semigroup, Monoid)

instance InjectableE UnsolvedBindings where
  injectionProofE = todoInjectableProof

getAtomNames :: Distinct l => BindingsFrag n l -> S.Set (AtomName l)
getAtomNames frag = S.fromList $ nameSetToList AtomNameRep $ toNameSet $ toScopeFrag frag

-- query each binding rhs for inference names and add it to the set if needed

extendInfOutMapSolver :: Distinct n => InfOutMap n -> SolverSubst n -> InfOutMap n
extendInfOutMapSolver (InfOutMap bindings ss dd un svs) ss' = do
  let (un', bindings') = zonkUnsolvedBindings ss' un bindings
  let ssFinal = catSolverSubsts (toScope bindings) ss ss'
  InfOutMap bindings' ssFinal dd un' svs

substIsEmpty :: SolverSubst n -> Bool
substIsEmpty (SolverSubst subst) = null subst

-- TODO: zonk the allowed effects and synth candidates in the bindings too
-- TODO: the reason we need this is that `getType` uses the bindings to obtain
-- type information, and we need this information when we emit decls. For
-- example, if we emit `f x` and we don't know that `f` has a type of the form
-- `a -> b` then `getType` will crash. But we control the inference-specific
-- implementation of `emitDecl`, so maybe we could instead do something like
-- emit a fresh inference variable in the case thea `getType` fails.
zonkUnsolvedBindings :: Distinct n => SolverSubst n -> UnsolvedBindings n -> Bindings n
                     -> (UnsolvedBindings n, Bindings n)
zonkUnsolvedBindings ss un bindings | substIsEmpty ss = (un, bindings)
zonkUnsolvedBindings ss unsolved bindings =
  flip runState bindings $ execWriterT do
    forM_ (S.toList $ fromUnsolvedBindings unsolved) \v -> do
      rhs <- flip lookupBindingsPure v <$> get
      let rhs' = zonkWithOutMap (InfOutMap bindings ss mempty mempty mempty) rhs
      modify $ updateBindings v rhs'
      when (hasInferenceVars bindings rhs') $
        tell $ UnsolvedBindings $ S.singleton v

hasInferenceVars :: HoistableE e => Bindings n -> e n -> Bool
hasInferenceVars bs e = any isInferenceVar $ freeVarsList AtomNameRep e
  where isInferenceVar v =
          case lookupBindingsPure bs v of
            AtomNameBinding (SolverBound _) -> True
            _                               -> False

instance ExtOutMap InfOutMap InfOutFrag where
  extendOutMap infOutMap (InfOutFrag em ds solverSubst) = do
    extendDefaults ds $
      flip extendInfOutMapSolver solverSubst $
        extendSynthVars em $
          flip extendOutMap (boundBindings em) $
            infOutMap

extendSynthVars :: Distinct l => InfEmissions n l -> InfOutMap l -> InfOutMap l
extendSynthVars Empty outMap = outMap
extendSynthVars (Nest (b :> RightE (DictVarBound _ _)) rest) outMap =
  InfOutMap bs ss ds un (ListE [inject (binderName b)] <> svs)
  where InfOutMap bs ss ds un svs = extendSynthVars rest outMap
extendSynthVars (Nest _ rest) outMap = extendSynthVars rest outMap

extendDefaults :: Defaults n -> InfOutMap n -> InfOutMap n
extendDefaults ds' (InfOutMap bindings ss ds un svs) =
  InfOutMap bindings ss (ds <> ds') un svs

newtype InfererM (i::S) (o::S) (a:: *) = InfererM
  { runInfererM' :: EnvReaderT Name (InplaceT InfOutMap InfOutFrag FallibleM) i o a }
  deriving (Functor, Applicative, Monad, MonadFail,
            ScopeReader, Fallible, Catchable, CtxReader, EnvReader Name)

runInfererM
  :: Distinct n
  => Bindings n
  -> (forall l. Ext n l => InfererM n l (e l))
  -> Except (e n)
runInfererM bindings cont = runSubstInfererM bindings idEnv cont

runSubstInfererM
  :: Distinct o
  => Bindings o -> Env Name i o
  -> (forall o'. Ext o o' => InfererM i o' (e o'))
  -> Except (e o)
runSubstInfererM bindings env cont = do
  DistinctAbs (InfOutFrag unsolvedInfNames _ _) result <-
    runFallibleM $
      runInplaceT (initInfOutMap bindings) $
        runEnvReaderT (inject env) $ runInfererM' $ cont
  case unsolvedInfNames of
    Empty -> return result
    Nest (_:>RightE (InfVarBound _ ctx)) _ ->
      addSrcContext ctx $
        throw TypeErr $ "Ambiguous type variable"
    _ -> error "not possible?"

initInfOutMap :: Bindings n -> InfOutMap n
initInfOutMap bindings =
  InfOutMap bindings emptySolverSubst mempty (UnsolvedBindings mempty) mempty

emitInfererM :: NameHint -> InfEmission o -> InfererM i o (AtomName o)
emitInfererM hint emission = InfererM $ EnvReaderT $ lift $
  emitInplace hint emission \b emission' ->
    InfOutFrag (Nest (b :> emission') Empty) mempty emptySolverSubst

instance Solver (InfererM i) where
  extendSolverSubst v ty = InfererM $ EnvReaderT $ lift $
    void $ doInplace (PairE v ty) \_ (PairE v' ty') ->
      DistinctAbs (InfOutFrag Empty mempty (singletonSolverSubst v' ty')) UnitE

  zonk e = InfererM $ EnvReaderT $ lift $
             withInplaceOutEnv e zonkWithOutMap

  emitSolver binding = emitInfererM "?" $ RightE binding

  addDefault t1 t2 = InfererM $ EnvReaderT $ lift $
    extendTrivialInplace $ InfOutFrag Empty defaults emptySolverSubst
    where defaults = Defaults [(t1, t2)]

  getDefaults = InfererM $ EnvReaderT $ lift $
    withInplaceOutEnv UnitE \(InfOutMap _ _ defaults _ _) UnitE ->
      inject defaults

  getSynthVars = InfererM $ EnvReaderT $ lift $
    withInplaceOutEnv UnitE \(InfOutMap _ _ _ _ svs) UnitE ->
      inject svs

instance Inferer InfererM where
  liftSolverM m = InfererM $ EnvReaderT $ lift $
    liftBetweenInplaceTs (liftExcept . liftM fromJust . runSearcherM) id liftSolverOutFrag $
      runSolverM' m

instance Builder (InfererM i) where
  emitDecl hint ann expr = do
    -- This zonking, and the zonking of the bindings elsewhere, is only to
    -- prevent `getType` from failing. But maybe we should just catch the
    -- failure if it occurs and generate a fresh inference name for the type in
    -- that case?
    expr' <- zonk expr
    ty <- getType expr'
    emitInfererM hint $ LeftE $ DeclBinding ann ty expr'

  buildScopedGeneral ab cont = InfererM $ EnvReaderT $ ReaderT \env -> do
    scopedResults <- scopedInplaceGeneral
      (\outMap b -> outMap `extendOutMap` boundBindings b)
      ab
      (\e -> flip runReaderT (inject env) $ runEnvReaderT' $ runInfererM' $
               withFabricatedEmitsEvidence $ do
                 result <- cont e
                 attemptSynthesis
                 return result)
    ScopedResult outMap bs result <- return scopedResults
    Abs outFrag resultAbs <- hoistInfState (toScope outMap) bs result
    DeferredInjection ExtW (DistinctAbs (PairB b decls) result') <-
        refreshAbsM =<< extendInplace =<< injectM (Abs outFrag resultAbs)
    injectM $ Abs b $ Abs decls result'

type InferenceNameBinders = Nest (BinderP AtomNameC SolverBinding)

-- When we finish building a block of decls we need to hoist the local solver
-- information into the outer scope. If the local solver state mentions local
-- variables which are about to go out of scope then we emit a "escaped scope"
-- error. To avoid false positives, we clean up as much dead (i.e. solved)
-- solver state as possible.
hoistInfState
  :: ( Fallible m, SubstE Name e, SubstE AtomSubstVal e
     , HoistableE e, Distinct n2, InjectableB b, BindsNames b)
  => Scope n1
  -> PairB b InfOutFrag n1 n2
  ->   e n2
  -> m (Abs InfOutFrag (Abs (PairB b (Nest Decl)) e) n1)
hoistInfState scope (PairB b (InfOutFrag emissions defaults subst)) result = do
  withSubscopeDistinct emissions do
    HoistedSolverState infVars defaults' subst' (DistinctAbs decls result') <-
      hoistInfStateRec (scope `extendOutMap` toScopeFrag b) emissions
                       defaults subst result
    case exchangeBs $ PairB b (PairB infVars (LiftB (PairE defaults' subst'))) of
      -- TODO: better error message
      Nothing -> throw TypeErr "Leaked local variable"
      Just (PairB (PairB infVars' (LiftB (PairE defaults'' subst''))) b') -> do
        -- TODO: do we need to zonk here so that any type annotations in b' get
        -- substituted? Or do we leave that up to the caller? Unlike with the
        -- decls, we don't need to do it for the sake of our local leak
        -- checking.
        return $ Abs (InfOutFrag (infNamesToEmissions infVars') defaults'' subst'') $
                   Abs (PairB b' decls) result'

data HoistedSolverState e n where
  HoistedSolverState
    :: (Distinct l1, Distinct n)
    => InferenceNameBinders n l1
    ->   Defaults l1
    ->   SolverSubst l1
    ->   DistinctAbs (Nest Decl) e l1
    -> HoistedSolverState e n

instance HoistableE e => HoistableE (HoistedSolverState e) where
  freeVarsE (HoistedSolverState infVars defaults subst ab) =
    freeVarsE (Abs infVars (PairE (PairE defaults subst) ab))

dceIfSolved :: (HoistableE e, SubstE AtomSubstVal e)
            => NameBinder AtomNameC n l -> HoistedSolverState e l -> Maybe (HoistedSolverState e n)
dceIfSolved b (HoistedSolverState infVars defaults subst result) =
  case deleteFromSubst subst (inject $ binderName b) of
    Just subst' ->
      -- do we need to zonk here? (if not, say why not)
      case hoist b (HoistedSolverState infVars defaults subst' result) of
        Just hoisted -> Just hoisted
        Nothing -> error "this shouldn't happen"
    Nothing -> Nothing

hoistInfStateRec :: ( Fallible m, Distinct n, Distinct l
                    , HoistableE e, SubstE AtomSubstVal e)
                 => Scope n
                 -> InfEmissions n l -> Defaults l -> SolverSubst l -> e l
                 -> m (HoistedSolverState e n)
hoistInfStateRec scope Empty defaults subst e = do
  let e'        = applySolverSubstE scope subst e
  let defaults' = applySolverSubstE scope subst defaults
  return $ HoistedSolverState Empty defaults' subst (DistinctAbs Empty e')
hoistInfStateRec scope (Nest (b :> infEmission) rest) defaults subst e = do
  withSubscopeDistinct rest do
    solverState@(HoistedSolverState infVars defaults' subst' result) <-
       hoistInfStateRec (extendOutMap scope (toScopeFrag b)) rest defaults subst e
    case infEmission of
      RightE binding@(InfVarBound _ _) ->
        case dceIfSolved b solverState of
          Just solverState' -> return solverState'
          Nothing -> return $ HoistedSolverState (Nest (b:>binding) infVars)
                                                 defaults' subst' result
      RightE (DictVarBound ty ctx) ->
        case dceIfSolved b solverState of
          Just solverState' -> return solverState'
          Nothing ->
            case hoist b solverState of
              Just hoisted -> return hoisted
              Nothing -> addSrcContext ctx $ do
                throw TypeErr $ "Couldn't synthesize dictionary: " ++ pprint ty
                     ++ "\n" ++ pprint subst
      RightE (SkolemBound _) ->
        case hoist b solverState of
          Just hoisted -> return hoisted
          Nothing -> error "probably shouldn't happen?"
      LeftE emission -> do
        -- TODO: avoid this repeated traversal here and in `tryHoistExpr`
        --       above by using `WithRestrictedScope` to cache free vars.
        PairB infVars' (b':>emission') <- liftMaybeErr TypeErr "Leaked local variable" $
                                            exchangeBs (PairB (b:>emission) infVars)
        subst'' <- liftMaybeErr TypeErr "Leaked local variable" $ hoist b' subst'
        let defaults'' = hoistDefaults b' defaults'
        withSubscopeDistinct b' $ do
            let scope' = scope `extendOutMap` toScopeFrag infVars'
            let emission'' = applySolverSubstE scope' subst'' emission'
            DistinctAbs rest' e' <- return result
            return $ HoistedSolverState infVars' defaults'' subst'' $
                        DistinctAbs (Nest (Let b' emission'') rest') e'

hoistDefaults :: BindsNames b => b n l -> Defaults l -> Defaults n
hoistDefaults b (Defaults defaults) =
  flip foldMap defaults \(t1, t2) ->
    case hoist b t1 of
      Nothing -> Defaults []
      Just t1' -> Defaults [(t1', t2)]


infNamesToEmissions :: InferenceNameBinders n l -> InfEmissions n l
infNamesToEmissions emissions =
  fmapNest (\(b:>binding) -> b :> RightE binding) emissions

instance BindingsReader (InfererM i) where
  addBindings e = InfererM $ EnvReaderT $ lift do
    withInplaceOutEnv e \(InfOutMap bindings _ _ _ _) e' ->
      WithBindings bindings e'

instance Scopable (InfererM i) where
  withBindings ab cont = do
    Abs b (Abs Empty result) <- buildScopedGeneral ab \x -> cont x
    return $ Abs b result

  extendNamelessBindings frag cont = InfererM $ EnvReaderT $ ReaderT \env -> do
    Distinct <- getDistinct
    liftBetweenInplaceTs id (\(InfOutMap bindings ss ds un svs) ->
                               InfOutMap (extendOutMap bindings frag) ss ds un svs) id $
       runEnvReaderT env $ runInfererM' $ cont

-- === actual inference pass ===

type SigmaType = Type  -- may     start with an implicit lambda
type RhoType   = Type  -- doesn't start with an implicit lambda
data SuggestionStrength = Suggest | Concrete  deriving Show
data RequiredTy (e::E) (n::S) = Check SuggestionStrength (e n)
                              | Infer
                                deriving Show

checkSigma :: (Emits o, Inferer m) => UExpr i
           -> SuggestionStrength
           -> SigmaType o -> m i o (Atom o)
checkSigma expr reqCon sTy = case sTy of
  Pi piTy@(PiType (PiBinder b _ arrow) _ _)
    | arrow `elem` [ImplicitArrow, ClassArrow] -> case expr of
        WithSrcE _ (ULam lam@(ULamExpr arrow' _ _))
          | arrow == arrow' ->
            -- is this even reachable? we don't have syntax for implicit/class lambda
            checkULam lam piTy
        -- we have to add the lambda argument corresponding to the implicit pi
        -- type argument
        _ -> do
          buildPureLam (getNameHint b)  arrow (piArgType piTy) \x -> do
            piTy' <- injectM piTy
            (Pure, bodyTy) <- instantiatePi piTy' (Var x)
            checkSigma expr reqCon bodyTy
  _ -> checkOrInferRho expr (Check reqCon sTy)

inferSigma :: (Emits o, Inferer m) => UExpr i -> m i o (Atom o)
inferSigma (WithSrcE pos expr) = case expr of
  ULam lam@(ULamExpr ImplicitArrow _ _) ->
    addSrcContext pos $ inferULam Pure lam
  _ -> inferRho (WithSrcE pos expr)

checkRho :: (Emits o, Inferer m) => UExpr i -> RhoType o -> m i o (Atom o)
checkRho expr ty = checkOrInferRho expr (Check Suggest ty)

inferRho :: (Emits o, Inferer m) => UExpr i -> m i o (Atom o)
inferRho expr = checkOrInferRho expr Infer

instantiateSigma :: (Emits o, Inferer m) => Atom o -> m i o (Atom o)
instantiateSigma f = do
  ty <- tryGetType f
  case ty of
    Pi (PiType (PiBinder _ argTy ImplicitArrow) _ _) -> do
      x <- freshType argTy
      ans <- emit $ App f x
      instantiateSigma $ Var ans
    Pi (PiType (PiBinder _ argTy ClassArrow) _ _) -> do
      dict <- trySynthDict argTy >>= \case
                Nothing -> do
                  Var <$> freshDictName argTy
                Just d -> return d
      ans <- emit $ App f dict
      instantiateSigma $ Var ans
    _ -> return f

checkOrInferRho :: forall m i o.
                   (Emits o, Inferer m)
                => UExpr i -> RequiredTy RhoType o -> m i o (Atom o)
checkOrInferRho (WithSrcE pos expr) reqTy = do
 addSrcContext pos $ case expr of
  UVar ~(InternalName v) -> do
    substM v >>= inferUVar >>= instantiateSigma >>= matchRequirement
  ULam (ULamExpr ImplicitArrow (UPatAnn p ann) body) -> do
    argTy <- checkAnn ann
    v <- freshInferenceName argTy
    bindLamPat p v $ checkOrInferRho body reqTy
  ULam lamExpr ->
    case reqTy of
      Check _ (Pi piTy) -> checkULam lamExpr piTy
      Check _ _ -> inferULam Pure lamExpr >>= matchRequirement
      Infer   -> inferULam Pure lamExpr
  UFor dir (UForExpr b body) -> do
    allowedEff <- getAllowedEffects
    let uLamExpr = ULamExpr PlainArrow b body
    lam <- case reqTy of
      Check _ (Pi tabPiTy) -> do
        lamPiTy <- buildForTypeFromTabType allowedEff tabPiTy
        checkULam uLamExpr lamPiTy
      Check _ _ -> inferULam allowedEff uLamExpr
      Infer   -> inferULam allowedEff uLamExpr
    result <- liftM Var $ emit $ Hof $ For (RegularFor dir) lam
    matchRequirement result
  UApp arr f x@(WithSrcE xPos _) -> do
    f' <- inferRho f
    -- NB: We never infer dependent function types, but we accept them, provided they
    --     come with annotations. So, unless we already know that the function is
    --     dependent here (i.e. the type of the zonk comes as a dependent Pi type),
    --     then nothing in the remainder of the program can convince us that the type
    --     is dependent. Also, the Pi binder is never considered to be in scope for
    --     inference variables, so they cannot get unified with it. Hence, this zonk
    --     is safe and doesn't make the type checking depend on the program order.
    infTy <- getType =<< zonk f'
    piTy  <- addSrcContext (srcPos f) $ fromPiType True arr infTy
    case considerNonDepPiType piTy of
      Just (_, argTy, effs, _) -> do
        x' <- checkSigma x Suggest argTy
        addEffects effs
        appVal <- emit $ App f' x'
        instantiateSigma (Var appVal) >>= matchRequirement
      Nothing -> do
        maybeX <- buildBlockReduced do
          argTy' <- injectM $ piArgType piTy
          checkSigma x Suggest argTy'
        case maybeX of
          Nothing -> addSrcContext xPos $ do
            throw TypeErr $ "Dependent functions can only be applied to fully " ++
                            "evaluated expressions. Bind the argument to a name " ++
                            "before you apply the function."
          Just x' -> do
            (effs, _) <- instantiatePi piTy x'
            addEffects effs
            appVal <- emit $ App f' x'
            instantiateSigma (Var appVal) >>= matchRequirement
  UPi (UPiExpr arr (UPatAnn (WithSrcB pos' pat) ann) effs ty) -> do
    -- TODO: make sure there's no effect if it's an implicit or table arrow
    ann' <- checkAnn ann
    piTy <- addSrcContext pos' case pat of
      UPatBinder UIgnore -> do
        effs' <- checkUEffRow effs
        ty' <- checkUType ty
        buildNonDepPi "_" arr ann' effs' ty'
      _ -> buildPi (getNameHint pat) arr ann' \v -> do
        PairE effs' ty' <- buildScopedReduceDecls do
          v' <- injectM v
          bindLamPat (WithSrcB pos' pat) v' do
            effs' <- checkUEffRow effs
            ty'   <- checkUType   ty
            return $ PairE effs' ty'
        return (effs', ty')
    matchRequirement $ Pi piTy
  UDecl (UDeclExpr decl body) -> do
    inferUDeclLocal decl $ checkOrInferRho body reqTy
  UCase scrut alts -> do
    scrut' <- inferRho scrut
    scrutTy <- getType scrut'
    reqTy' <- case reqTy of
      Infer -> freshType TyKind
      Check _ req -> return req
    alts' <- mapM (checkCaseAlt reqTy' scrutTy) alts
    scrut'' <- zonk scrut'
    buildSortedCase scrut'' alts' reqTy'
  UTabCon xs -> inferTabCon xs reqTy >>= matchRequirement
  UIndexRange low high -> do
    n <- freshType TyKind
    low'  <- mapM (flip checkRho n) low
    high' <- mapM (flip checkRho n) high
    matchRequirement $ TC $ IndexRange n low' high'
  UHole -> case reqTy of
    Infer -> throw MiscErr "Can't infer type of hole"
    Check _ ty -> freshType ty
  UTypeAnn val ty -> do
    ty' <- zonk =<< checkUType ty
    val' <- checkSigma val (inferSuggestionStrength ty') ty'
    matchRequirement val'
  UPrimExpr prim -> do
    prim' <- forM prim \x -> do
      x' <- inferRho x
      getType x' >>= \case
        TyKind -> cheapReduce x'
        _ -> return x'
    val <- case prim' of
      TCExpr  e -> return $ TC e
      ConExpr e -> return $ Con e
      OpExpr  e -> Var <$> emit (Op e)
      HofExpr e -> Var <$> emit (Hof e)
    matchRequirement val
  URecord (Ext items Nothing) -> do
    items' <- mapM inferRho items
    matchRequirement $ Record items'
  URecord (Ext items (Just ext)) -> do
    items' <- mapM inferRho items
    restTy <- freshInferenceName LabeledRowKind
    ext' <- zonk =<< (checkRho ext $ RecordTy $ Ext NoLabeledItems $ Just restTy)
    matchRequirement =<< emitOp (RecordCons items' ext')
  UVariant labels@(LabeledItems lmap) label value -> do
    value' <- inferRho value
    prevTys <- mapM (const $ freshType TyKind) labels
    rest <- freshInferenceName LabeledRowKind
    ty <- getType value'
    let items = prevTys <> labeledSingleton label ty
    let extItems = Ext items $ Just rest
    let i = case M.lookup label lmap of
              Just prev -> length prev
              Nothing -> 0
    matchRequirement $ Variant extItems label i value'
  URecordTy row -> matchRequirement =<< RecordTy <$> checkExtLabeledRow row
  UVariantTy row -> matchRequirement =<< VariantTy <$> checkExtLabeledRow row
  UVariantLift labels value -> do
    row <- freshInferenceName LabeledRowKind
    value' <- zonk =<< (checkRho value $ VariantTy $ Ext NoLabeledItems $ Just row)
    prev <- mapM (\() -> freshType TyKind) labels
    matchRequirement =<< emitOp (VariantLift prev value')
  UIntLit  x  -> matchRequirement $ Con $ Lit  $ Int32Lit $ fromIntegral x
  UFloatLit x -> matchRequirement $ Con $ Lit  $ Float32Lit $ realToFrac x
  -- TODO: Make sure that this conversion is not lossy!
  where
    matchRequirement :: Atom o -> m i o (Atom o)
    matchRequirement x = return x <*
      case reqTy of
        Infer -> return ()
        Check _ req -> do
          ty <- getType x
          constrainEq req ty

-- === sorting case alternatives ===

data IndexedAlt n = IndexedAlt CaseAltIndex (Alt n)

instance InjectableE IndexedAlt where
  injectionProofE = todoInjectableProof

buildNthOrderedAlt :: (Emits n, Builder m)
                   => [IndexedAlt n] -> Type n -> Type n -> Int -> [AtomName n]
                   -> m n (Atom n)
buildNthOrderedAlt alts scrutTy resultTy i vs = do
  case lookup (nthCaseAltIdx scrutTy i) [(idx, alt) | IndexedAlt idx alt <- alts] of
    Nothing -> do
      resultTy' <- injectM resultTy
      emitOp $ ThrowError resultTy'
    Just alt -> applyNaryAbs alt vs >>= emitBlock

-- converts from the ordinal index used in the core IR to the more complicated
-- `CaseAltIndex` used in the surface IR.
nthCaseAltIdx :: Type n -> Int -> CaseAltIndex
nthCaseAltIdx ty i = case ty of
  TypeCon _ _ -> ConAlt i
  VariantTy (NoExt types) -> case lookup i pairedIndices of
    Just idx -> idx
    Nothing -> error "alt index out of range"
    where
      pairedIndices :: [(Int, CaseAltIndex)]
      pairedIndices = enumerate $ [VariantAlt l idx | (l, idx, _) <- toList (withLabels types)]
  _ -> error $ "can't pattern-match on: " <> pprint ty

buildMonomorphicCase :: (Emits n, Builder m) => [IndexedAlt n] -> Atom n -> Type n -> m n (Atom n)
buildMonomorphicCase alts scrut resultTy = do
  scrutTy <- getType scrut
  buildCase scrut resultTy \i vs -> do
    ListE alts' <- injectM $ ListE alts
    scrutTy'    <- injectM scrutTy
    resultTy'   <- injectM resultTy
    buildNthOrderedAlt alts' scrutTy' resultTy' i vs

buildSortedCase :: (Fallible1 m, Builder m, Emits n)
                 => Atom n -> [IndexedAlt n] -> Type n
                 -> m n (Atom n)
buildSortedCase scrut alts resultTy = do
  scrutTy <- getType scrut
  case scrutTy of
    TypeCon _ _ -> buildMonomorphicCase alts scrut resultTy
    VariantTy (Ext types tailName) -> do
      case filter isVariantTailAlt alts of
        [] -> case tailName of
          Nothing ->
            -- We already know the type exactly, so just emit a case.
            buildMonomorphicCase alts scrut resultTy
          Just _ -> do
            -- Split off the types we don't know about, mapping them to a
            -- runtime error.
            buildSplitCase types scrut resultTy
              (\v -> do ListE alts' <- injectM $ ListE alts
                        resultTy'   <- injectM resultTy
                        buildMonomorphicCase alts' (Var v) resultTy')
              (\_ -> do resultTy' <- injectM resultTy
                        emitOp $ ThrowError resultTy')
        [IndexedAlt (VariantTailAlt (LabeledItems skippedItems)) tailAlt] -> do
            -- Split off the types skipped by the tail pattern.
            let splitLeft fvs ltys = NE.fromList $ NE.take (length ltys) fvs
            let left = LabeledItems $ M.intersectionWith splitLeft
                        (fromLabeledItems types) skippedItems
            checkNoTailOverlaps alts left
            buildSplitCase left scrut resultTy
              (\v -> do ListE alts' <- injectM $ ListE alts
                        resultTy'   <- injectM resultTy
                        buildMonomorphicCase alts' (Var v) resultTy')
              (\v -> do tailAlt' <- injectM tailAlt
                        applyNaryAbs tailAlt' [v] >>= emitBlock )
        _ -> throw TypeErr "Can't specify more than one variant tail pattern."
    _ -> fail $ "Unexpected case expression type: " <> pprint scrutTy

-- Make sure all of the alternatives are exclusive with the tail pattern (could
-- technically allow overlap but this is simpler). Split based on the tail
-- pattern's skipped types.
checkNoTailOverlaps :: Fallible1 m => [IndexedAlt n] -> LabeledItems (Type n) ->  m n ()
checkNoTailOverlaps alts (LabeledItems tys) = do
  forM_ alts \(IndexedAlt (VariantAlt label i) _) ->
    case M.lookup label tys of
      Just tys' | i <= length tys' -> return ()
      _ -> throw TypeErr "Variant explicit alternatives overlap with tail pattern."

isVariantTailAlt :: IndexedAlt n -> Bool
isVariantTailAlt (IndexedAlt (VariantTailAlt _) _) = True
isVariantTailAlt _ = False

-- ===

inferUVar :: Inferer m => UVar o -> m i o (Atom o)
inferUVar = \case
  UAtomVar v ->
    return $ Var v
  UTyConVar v -> do
    -- TODO: we shouldn't need these tildes because it's the only valid case
    ~(TyConBinding   dataDefName) <- lookupBindings v
    ~(DataDefBinding dataDef)     <- lookupBindings dataDefName
    return $ TypeCon (dataDefName, dataDef) []
  UDataConVar v -> do
   -- TODO: we shouldn't need these tildes because it's the only valid case
    ~(DataConBinding dataDefName idx) <- lookupBindings v
    ~(DataDefBinding dataDef)         <- lookupBindings dataDefName
    return $ DataCon (pprint v) (dataDefName, dataDef) [] idx []
  UClassVar v -> do
    ~(ClassBinding (ClassDef _ _ dataDef)) <- lookupBindings v
    return $ TypeCon dataDef []
  UMethodVar v -> do
    ~(MethodBinding _ _ getter) <- lookupBindings v
    return getter

buildForTypeFromTabType :: (Fallible1 m, Builder m)
                        => EffectRow n -> PiType n -> m n (PiType n)
buildForTypeFromTabType effs tabPiTy@(PiType (PiBinder bPi piArgTy arr) _ _) = do
  unless (arr == TabArrow) $ throw TypeErr $ "Not an table arrow type: " ++ pprint arr
  buildPi (getNameHint bPi) PlainArrow piArgTy \i -> do
    Distinct <- getDistinct
    (_, resultTy) <- instantiatePi (inject tabPiTy) $ Var i
    return (inject effs, resultTy)

inferUDeclLocal ::  (Emits o, Inferer m) => UDecl i i' -> m i' o a -> m i o a
inferUDeclLocal (ULet letAnn (UPatAnn p ann) rhs) cont = do
  val <- case ann of
    Nothing -> inferSigma rhs
    Just ty -> do
      ty' <- zonk =<< checkUType ty
      checkSigma rhs (inferSuggestionStrength ty') ty'
  expr <- zonk $ Atom val
  var <- emitDecl (getNameHint p) letAnn expr
  bindLamPat p var cont
inferUDeclLocal (UInstance ~(InternalName className) argBinders params methods maybeName) cont = do
  className' <- substM className
  instanceDict <- checkInstanceArgs argBinders do
                    className'' <- injectM className'
                    checkInstanceBody className'' params methods
  case maybeName of
    RightB UnitB  -> do
      void $ emitDecl "instance" InstanceLet $ Atom instanceDict
      cont
    JustB instanceName -> do
      instanceVal <- emitDecl (getNameHint instanceName) PlainLet (Atom instanceDict)
      extendEnv (instanceName @> instanceVal) cont
    _ -> error "impossible"
inferUDeclLocal _ _ = error "not a local decl"

inferUDeclTop :: TopInferer m => UDecl i i' -> m i' o a -> m i o a
inferUDeclTop (UDataDefDecl def tc dcs) cont = do
  def' <- liftLocalInferer (inferDataDef def) >>= emitDataDef
  tc' <- emitTyConName def'
  dcs' <- mapM (emitDataConName def') [0..(nestLength dcs - 1)]
  extendEnv (tc @> tc' <.> dcs @@> dcs') cont
inferUDeclTop (UInterface paramBs superclasses methodTys className methodNames) cont = do
  let classPrettyName   = fromString (pprint className) :: SourceName
  let methodPrettyNames = map fromString (nestToList pprint methodNames) :: [SourceName]
  classDef <- inferInterfaceDataDef classPrettyName methodPrettyNames
                paramBs superclasses methodTys
  className' <- emitClassDef classDef
  mapM_ (emitSuperclass className') [0..(length superclasses - 1)]
  methodNames' <- forM (enumerate $ zip methodPrettyNames methodTys) \(i, (prettyName, ty)) -> do
    let UMethodType (Right explicits) _ = ty
    emitMethodType (getNameHint prettyName) className' explicits i
  extendEnv (className @> className' <.> methodNames @@> methodNames') cont
inferUDeclTop _ _ = error "not a top decl"

inferDataDef :: Inferer m => UDataDef i -> m i o (DataDef o)
inferDataDef (UDataDef (tyConName, paramBs) dataCons) = do
  Abs paramBs' (ListE dataCons') <-
    withNestedUBinders paramBs \_ -> do
      dataCons' <- mapM inferDataCon dataCons
      return $ ListE dataCons'
  return $ DataDef tyConName paramBs' dataCons'

inferDataCon :: Inferer m => (SourceName, UDataDefTrail i) -> m i o (DataConDef o)
inferDataCon (sourceName, UDataDefTrail argBs) = do
  argBs' <- checkUBinders (EmptyAbs argBs)
  return $ DataConDef sourceName argBs'

inferInterfaceDataDef :: TopInferer m
                      => SourceName -> [SourceName]
                      -> Nest (UAnnBinder AtomNameC) i i'
                      -> [UType i'] -> [UMethodType i']
                      -> m i o (ClassDef o)
inferInterfaceDataDef className methodNames paramBs superclasses methods = do
  dictDef <- liftLocalInferer do
    paramBs' <- checkUBinders $ EmptyAbs paramBs
    buildNewtype className paramBs' \params -> do
      extendEnv (paramBs @@> params) do
        superclasses' <- mapM checkUType superclasses
        methodsTys'   <- mapM checkUType $ methods <&> \(UMethodType _ ty) -> ty
        return $ PairTy (ProdTy superclasses') (ProdTy methodsTys')
  defName <- emitDataDef dictDef
  return $ ClassDef className methodNames (defName, dictDef)

withNestedUBinders :: (Inferer m, HasNamesE e, SubstE AtomSubstVal e, InjectableE e)
                  => Nest (UAnnBinder AtomNameC) i i'
                  -> (forall o'. Ext o o' => [AtomName o'] -> m i' o' (e o'))
                  -> m i o (Abs (Nest Binder) e o)
withNestedUBinders bs cont = case bs of
  Empty -> Abs Empty <$> cont []
  Nest b rest -> do
    Abs b' (Abs rest' body) <- withUBinder b \name -> do
      withNestedUBinders rest \names -> do
        name' <- injectM name
        cont (name':names)
    return $ Abs (Nest b' rest') body

withUBinder :: (Inferer m, HasNamesE e, SubstE AtomSubstVal e, InjectableE e)
            => UAnnBinder AtomNameC i i'
            -> (forall o'. Ext o o' => AtomName o' -> m i' o' (e o'))
            -> m i o (Abs Binder e o)
withUBinder (UAnnBinder b ann) cont = do
  ann' <- checkUType ann
  buildAbs ann' \name -> extendEnv (b @> name) $ cont name

checkUBinders :: Inferer m
              => EmptyAbs (Nest (UAnnBinder AtomNameC)) i
              -> m i o (EmptyAbs (Nest Binder) o)
checkUBinders (EmptyAbs bs) = withNestedUBinders bs \_ -> return UnitE
checkUBinders _ = error "impossible"

inferULam :: (Emits o, Inferer m) => EffectRow o -> ULamExpr i -> m i o (Atom o)
inferULam effs (ULamExpr arrow (UPatAnn p ann) body) = do
  argTy <- checkAnn ann
  buildLam (getNameHint p) arrow argTy effs \v ->
    bindLamPat p v $ inferSigma body

checkULam :: (Emits o, Inferer m) => ULamExpr i -> PiType o -> m i o (Atom o)
checkULam (ULamExpr _ (UPatAnn p ann) body) piTy = do
  let argTy = piArgType piTy
  checkAnn ann >>= constrainEq argTy
  -- XXX: we're ignoring the ULam arrow here. Should we be checking that it's
  -- consistent with the arrow supplied by the pi type?
  buildDepEffLam (getNameHint p) (piArrow piTy) argTy
    (\v -> do
        piTy' <- injectM piTy
        fst <$> instantiatePi piTy' (Var v) )
     \v -> bindLamPat p v do
        piTy' <- injectM piTy
        (_, resultTy) <- instantiatePi piTy' (Var v)
        checkSigma body Suggest resultTy

checkInstanceArgs
  :: (Emits o, Inferer m)
  => Nest UPatAnnArrow i i'
  -> (forall o'. (Emits o', Ext o o') =>  m i' o' (Atom o'))
  -> m i o (Atom o)
checkInstanceArgs Empty cont = cont
checkInstanceArgs (Nest (UPatAnnArrow (UPatAnn p ann) arrow) rest) cont = do
  case arrow of
    ImplicitArrow -> return ()
    ClassArrow    -> return ()
    _ -> throw TypeErr $ "Not a valid arrow for an instance: " ++ pprint arrow
  argTy <- checkAnn ann
  buildLam (getNameHint p) arrow argTy Pure \v -> do
    bindLamPat p v $
      checkInstanceArgs rest do
        cont

checkInstanceBody :: (Emits o, Inferer m)
                  => ClassName o
                  -> [UType i]
                  -> [UMethodDef i]
                  -> m i o (Atom o)
checkInstanceBody className params methods = do
  ClassDef _ methodNames def@(_, DataDef tcNameHint _ _) <- getClassDef className
  params' <- mapM checkUType params
  Just dictTy <- fromNewtype <$> applyDataDefParams (snd def) params'
  PairTy (ProdTy superclassTys) (ProdTy methodTys) <- return dictTy
  superclassDicts <- forM superclassTys \ty -> trySynthDict ty >>= \case
    Nothing ->
      -- TODO: do we need to defer this failure and try again later?
      throw TypeErr $ "Couldn't construct superclass instance: " <> pprint ty
    Just d -> return d
  methodsChecked <- mapM (checkMethodDef className methodTys) methods
  let (idxs, methods') = unzip $ sortOn fst $ methodsChecked
  forM_ (repeated idxs) \i ->
    throw TypeErr $ "Duplicate method: " ++ pprint (methodNames!!i)
  forM_ ([0..(length methodTys - 1)] `listDiff` idxs) \i ->
    throw TypeErr $ "Missing method: " ++ pprint (methodNames!!i)
  let dataConNameHint = "Mk" <> tcNameHint
  return $ DataCon dataConNameHint def params' 0 [PairVal (ProdVal superclassDicts)
                                                          (ProdVal methods')]

checkMethodDef :: (Emits o, Inferer m)
               => ClassName o -> [Type o] -> UMethodDef i -> m i o (Int, Atom o)
checkMethodDef className methodTys (UMethodDef ~(InternalName v) rhs) = do
  MethodBinding className' i _ <- substM v >>= lookupBindings
  when (className /= className') $
    throw TypeErr $ pprint v ++ " is not a method of " ++ pprint className
  let methodTy = methodTys !! i
  rhs' <- checkSigma rhs Suggest methodTy
  return (i, rhs')

checkUEffRow :: (Emits o, Inferer m) => UEffectRow i -> m i o (EffectRow o)
checkUEffRow (EffectRow effs t) = do
   effs' <- liftM S.fromList $ mapM checkUEff $ toList effs
   t' <- forM t \(InternalName v) -> do
            v' <- substM v
            constrainVarTy v' EffKind
            return v'
   return $ EffectRow effs' t'

checkUEff :: (Emits o, Inferer m) => UEffect i -> m i o (Effect o)
checkUEff eff = case eff of
  RWSEffect rws ~(InternalName region) -> do
    region' <- substM region
    constrainVarTy region' TyKind
    return $ RWSEffect rws region'
  ExceptionEffect -> return ExceptionEffect
  IOEffect        -> return IOEffect

constrainVarTy :: (Emits o, Inferer m) => AtomName o -> Type o -> m i o ()
constrainVarTy v tyReq = do
  varTy <- getType $ Var v
  constrainEq tyReq varTy

data CaseAltIndex = ConAlt Int
                  | VariantAlt Label Int
                  | VariantTailAlt (LabeledItems ())
  deriving (Eq, Show)

checkCaseAlt :: (Emits o, Inferer m)
             => RhoType o -> Type o -> UAlt i -> m i o (IndexedAlt o)
checkCaseAlt reqTy scrutineeTy (UAlt pat body) = do
  alt <- checkCasePat pat scrutineeTy do
    reqTy' <- injectM reqTy
    checkRho body reqTy'
  idx <- getCaseAltIndex pat
  return $ IndexedAlt idx alt

getCaseAltIndex :: Inferer m => UPat i i' -> m i o CaseAltIndex
getCaseAltIndex (WithSrcB _ pat) = case pat of
  UPatCon ~(InternalName conName) _ -> do
    (_, con) <- substM conName >>= getDataCon
    return $ ConAlt con
  UPatVariant (LabeledItems lmap) label _ -> do
    let i = case M.lookup label lmap of
              Just prev -> length prev
              Nothing -> 0
    return (VariantAlt label i)
  UPatVariantLift labels _ -> do
    return (VariantTailAlt labels)
  _ -> throw TypeErr $ "Case patterns must start with a data constructor or variant pattern"

checkCasePat :: (Emits o, Inferer m)
             => UPat i i'
             -> Type o
             -> (forall o'. (Emits o', Ext o o') => m i' o' (Atom o'))
             -> m i o (Alt o)
checkCasePat (WithSrcB pos pat) scrutineeTy cont = addSrcContext pos $ case pat of
  UPatCon ~(InternalName conName) ps -> do
    (dataDefName, con) <- substM conName >>= getDataCon
    dataDef@(DataDef _ paramBs cons) <- getDataDef dataDefName
    DataConDef _ (EmptyAbs argBs) <- return $ cons !! con
    when (nestLength argBs /= nestLength ps) $ throw TypeErr $
      "Unexpected number of pattern binders. Expected " ++ show (nestLength argBs)
                                             ++ " got " ++ show (nestLength ps)
    (params, argBs') <- inferParams (Abs paramBs $ EmptyAbs argBs)
    constrainEq scrutineeTy $ TypeCon (dataDefName, dataDef) params
    buildAlt argBs' \args ->
      bindLamPats ps args $ cont
  UPatVariant labels label p -> do
    ty <- freshType TyKind
    prevTys <- mapM (const $ freshType TyKind) labels
    rest <- freshInferenceName LabeledRowKind
    let patTypes = prevTys <> labeledSingleton label ty
    let extPatTypes = Ext patTypes $ Just rest
    constrainEq scrutineeTy $ VariantTy extPatTypes
    buildUnaryAlt ty \x ->
      bindLamPat p x cont
  UPatVariantLift labels p -> do
    prevTys <- mapM (const $ freshType TyKind) labels
    rest <- freshInferenceName LabeledRowKind
    let extPatTypes = Ext prevTys $ Just rest
    constrainEq scrutineeTy $ VariantTy extPatTypes
    let ty = VariantTy $ Ext NoLabeledItems $ Just rest
    buildUnaryAlt ty \x ->
      bindLamPat p x cont
  _ -> throw TypeErr $ "Case patterns must start with a data constructor or variant pattern"

inferParams :: (Emits o, Inferer m, HasNamesE e, InjectableE e)
            => Abs (Nest Binder) e o -> m i o ([Type o], e o)
inferParams (Abs Empty body) = return ([], body)
inferParams (Abs (Nest (b:>ty) bs) body) = do
  x <- freshInferenceName ty
  rest <- applyAbs (Abs b (Abs bs body)) x
  (xs, body') <- inferParams rest
  return (Var x : xs, body')

bindLamPats :: (Emits o, Inferer m)
            => Nest UPat i i' -> [AtomName o] -> m i' o a -> m i o a
bindLamPats Empty [] cont = cont
bindLamPats (Nest p ps) (x:xs) cont = bindLamPat p x $ bindLamPats ps xs cont
bindLamPats _ _ _ = error "mismatched number of args"

bindLamPat :: (Emits o, Inferer m) => UPat i i' -> AtomName o -> m i' o a -> m i o a
bindLamPat (WithSrcB pos pat) v cont = addSrcContext pos $ case pat of
  UPatBinder b -> extendEnv (b @> v) cont
  UPatUnit UnitB -> do
    constrainVarTy v UnitTy
    cont
  UPatPair (PairB p1 p2) -> do
    let x = Var v
    ty <- getType x
    _  <- fromPairType ty
    x' <- zonk x  -- ensure it has a pair type before unpacking
    x1 <- getFst x' >>= zonk >>= emitAtomToName
    bindLamPat p1 x1 do
      x2  <- getSnd x' >>= zonk >>= emitAtomToName
      bindLamPat p2 x2 do
        cont
  UPatCon ~(InternalName conName) ps -> do
    (dataDefName, _) <- getDataCon =<< substM conName
    dataDef@(DataDef _ paramBs cons) <- getDataDef dataDefName
    case cons of
      [DataConDef _ (EmptyAbs argBs)] -> do
        when (nestLength argBs /= nestLength ps) $ throw TypeErr $
          "Unexpected number of pattern binders. Expected " ++ show (nestLength argBs)
                                                 ++ " got " ++ show (nestLength ps)
        (params, UnitE) <- inferParams (Abs paramBs UnitE)
        constrainVarTy v $ TypeCon (dataDefName, dataDef) params
        xs <- zonk (Var v) >>= emitUnpacked
        xs' <- forM xs \x -> zonk (Var x) >>= emitAtomToName
        bindLamPats ps xs' cont
      _ -> throw TypeErr $ "sum type constructor in can't-fail pattern"
  UPatRecord (Ext labels Nothing) (PairB pats (RightB UnitB)) -> do
    expectedTypes <- mapM (const $ freshType TyKind) labels
    constrainVarTy v (RecordTy (NoExt expectedTypes))
    xs <- zonk (Var v) >>= emitUnpacked
    xs' <- forM xs \x -> zonk (Var x) >>= emitAtomToName
    bindLamPats pats xs' cont
  UPatRecord (Ext labels (Just ())) (PairB pats (LeftB tailPat)) -> do
    wantedTypes <- mapM (const $ freshType TyKind) labels
    restType <- freshInferenceName LabeledRowKind
    constrainVarTy v (RecordTy $ Ext wantedTypes $ Just restType)
    -- Split the record.
    wantedTypes' <- mapM zonk wantedTypes
    v' <- zonk $ Var v
    split <- emit $ Op $ RecordSplit wantedTypes' v'
    [left, right] <- emitUnpacked $ Var split
    leftVals <- emitUnpacked $ Var left
    bindLamPats pats leftVals $
      bindLamPat tailPat right $
        cont
  UPatRecord _ _ -> error "mismatched labels and patterns (should be ruled out by the parser)"
  UPatVariant _ _ _   -> throw TypeErr "Variant not allowed in can't-fail pattern"
  UPatVariantLift _ _ -> throw TypeErr "Variant not allowed in can't-fail pattern"
  UPatTable ps -> do
    elemTy <- freshType TyKind
    let idxTy = FixedIntRange 0 (fromIntegral $ nestLength ps)
    ty <- getType $ Var v
    tabTy <- idxTy ==> elemTy
    constrainEq ty tabTy
    idxs <- indices idxTy
    unless (length idxs == nestLength ps) $
      throw TypeErr $ "Incorrect length of table pattern: table index set has "
                      <> pprint (length idxs) <> " elements but there are "
                      <> pprint (nestLength ps) <> " patterns."
    xs <- forM idxs \i -> emit $ App (Var v) i
    bindLamPats ps xs cont

checkAnn :: (Emits o, Inferer m) => Maybe (UType i) -> m i o (Type o)
checkAnn ann = case ann of
  Just ty -> checkUType ty
  Nothing -> freshType TyKind

checkUType :: Inferer m => UType i -> m i o (Type o)
checkUType ty = do
  reduced <- buildBlockReduced $ withAllowedEffects Pure $ checkRho ty TyKind
  case reduced of
    Just ty' -> return $ ty'
    Nothing  -> throw TypeErr $ "Can't reduce type expression: " ++ pprint ty

checkExtLabeledRow :: (Emits o, Inferer m)
                   => ExtLabeledItems (UExpr i) (UExpr i)
                   -> m i o (ExtLabeledItems (Type o) (AtomName o))
checkExtLabeledRow (Ext types Nothing) = do
  types' <- mapM checkUType types
  return $ Ext types' Nothing
checkExtLabeledRow (Ext types (Just ext)) = do
  types' <- mapM checkUType types
  -- Only variables can have kind LabeledRowKind at the moment.
  Var ext' <- checkRho ext LabeledRowKind
  return $ Ext types' $ Just ext'

inferTabCon :: (Emits o, Inferer m) => [UExpr i] -> RequiredTy RhoType o -> m i o (Atom o)
inferTabCon xs reqTy = do
  (tabTy, xs') <- case reqTy of
    Check Concrete tabTy@(TabTyAbs piTy) -> do
      idx <- indices $ piArgType piTy
      -- TODO: Check length!!
      unless (length idx == length xs) $
        throw TypeErr "Table type doesn't match annotation"
      xs' <- forM (zip xs idx) \(x, i) -> do
        (_, xTy) <- instantiatePi piTy i
        checkOrInferRho x $ Check Concrete xTy
      return (tabTy, xs')
    _ -> do
      elemTy <- case xs of
        []    -> freshType TyKind
        (x:_) -> getType =<< inferRho x
      tabTy <- FixedIntRange 0 (fromIntegral $ length xs) ==> elemTy
      case reqTy of
        Check Suggest sTy -> addContext context $ constrainEq sTy tabTy
          where context = "If attempting to construct a fixed-size table not " <>
                          "indexed by 'Fin n' for some n, this error may " <>
                          "indicate there was not enough information to infer " <>
                          "a concrete index set; try adding an explicit " <>
                          "annotation."
        Infer       -> return ()
        _           -> error "Missing case"
      xs' <- mapM (flip checkRho elemTy) xs
      return (tabTy, xs')
  liftM Var $ emit $ Op $ TabCon tabTy xs'

-- Bool flag is just to tweak the reported error message
fromPiType :: (Emits o, Inferer m) => Bool -> Arrow -> Type o -> m i o (PiType o)
fromPiType _ _ (Pi piTy) = return piTy -- TODO: check arrow
fromPiType expectPi arr ty = do
  a <- freshType TyKind
  b <- freshType TyKind
  piTy <- nonDepPiType arr a Pure b
  if expectPi then  constrainEq (Pi piTy) ty
              else  constrainEq ty (Pi piTy)
  return piTy

fromPairType :: (Emits o, Inferer m) => Type o -> m i o (Type o, Type o)
fromPairType (PairTy t1 t2) = return (t1, t2)
fromPairType ty = do
  a <- freshType TyKind
  b <- freshType TyKind
  constrainEq (PairTy a b) ty
  return (a, b)

addEffects :: (Emits o, Inferer m) => EffectRow o -> m i o ()
addEffects eff = do
  allowed <- checkAllowedUnconditionally eff
  unless allowed $ do
    allowedEffects <- getAllowedEffects
    eff' <- openEffectRow eff
    constrainEq (Eff allowedEffects) (Eff eff')

checkAllowedUnconditionally :: Inferer m => EffectRow o -> m i o Bool
checkAllowedUnconditionally Pure = return True
checkAllowedUnconditionally eff = do
  eff' <- zonk eff
  effAllowed <- getAllowedEffects >>= zonk
  return $ case checkExtends effAllowed eff' of
    Failure _  -> False
    Success () -> True

openEffectRow :: (Emits o, Inferer m) => EffectRow o -> m i o (EffectRow o)
openEffectRow (EffectRow effs Nothing) = extendEffRow effs <$> freshEff
openEffectRow effRow = return effRow

-- === Solver ===

newtype SolverSubst n = SolverSubst (M.Map (AtomName n) (Type n))

instance Pretty (SolverSubst n) where
  pretty (SolverSubst m) = pretty $ M.toList m

class (CtxReader1 m, BindingsReader m) => Solver (m::MonadKind1) where
  zonk :: (SubstE AtomSubstVal e, InjectableE e) => e n -> m n (e n)
  extendSolverSubst :: AtomName n -> Type n -> m n ()
  emitSolver :: SolverBinding n -> m n (AtomName n)
  addDefault :: Type n -> Type VoidS -> m n ()
  getDefaults :: m n (Defaults n)
  getSynthVars :: m n (SynthesisVars n)

type SolverOutMap = InfOutMap

data SolverOutFrag (n::S) (l::S) =
  SolverOutFrag (SolverEmissions n l) (Defaults l) (SolverSubst l)

type SolverEmissions = Nest (BinderP AtomNameC SolverBinding)

instance GenericB SolverOutFrag where
  type RepB SolverOutFrag = PairB SolverEmissions (LiftB (PairE Defaults SolverSubst))
  fromB (SolverOutFrag em ds subst) = PairB em (LiftB (PairE ds subst))
  toB   (PairB em (LiftB (PairE ds subst))) = SolverOutFrag em ds subst

instance ProvesExt   SolverOutFrag
instance SubstB Name SolverOutFrag
instance BindsNames  SolverOutFrag
instance InjectableB SolverOutFrag

instance OutFrag SolverOutFrag where
  emptyOutFrag = SolverOutFrag Empty mempty emptySolverSubst
  catOutFrags scope (SolverOutFrag em ds ss) (SolverOutFrag em' ds' ss') =
    withExtEvidence em' $
      SolverOutFrag (em >>> em')
                    (inject ds <> ds')
                    (catSolverSubsts scope (inject ss) ss')

instance ExtOutMap InfOutMap SolverOutFrag where
  extendOutMap infOutMap outFrag =
    extendOutMap infOutMap $ liftSolverOutFrag outFrag

newtype SolverM (n::S) (a:: *) =
  SolverM { runSolverM' :: InplaceT SolverOutMap SolverOutFrag SearcherM n a }
  deriving (Functor, Applicative, Monad, MonadFail, Alternative, Searcher,
            ScopeReader, Fallible, CtxReader)

runSolverM :: ( SubstE AtomSubstVal e, InjectableE e, HoistableE e
              , Distinct n)
           => Bindings n
           -> (forall l. Ext n l => SolverM l (e l))
           -> Except (e n)
runSolverM bindings cont = do
  maybeAbs <- runSearcherM $ runInplaceT (initInfOutMap bindings) $
                runSolverM' $ cont >>= zonk
  case maybeAbs of
    Nothing -> throw TypeErr "No solution"
    Just (DistinctAbs bs result) ->
      case hoist bs result of
        Nothing -> throw EscapedNameErr "Unsolved vars in runSolverM"
        Just result' -> return result'

instance BindingsReader SolverM where
  addBindings e = SolverM do
    withInplaceOutEnv e \(InfOutMap bindings _ _ _ _) e' ->
      WithBindings bindings e'

instance Solver SolverM where
  extendSolverSubst v ty = SolverM $
    void $ doInplace (PairE v ty) \_ (PairE v' ty') ->
      DistinctAbs (SolverOutFrag Empty mempty (singletonSolverSubst v' ty')) UnitE

  zonk e = SolverM $ withInplaceOutEnv e zonkWithOutMap

  emitSolver binding = SolverM $
    emitInplace "?" binding \b binding' ->
      SolverOutFrag (Nest (b:>binding') Empty) mempty emptySolverSubst

  addDefault t1 t2 = SolverM $
    extendTrivialInplace $ SolverOutFrag Empty defaults emptySolverSubst
    where defaults = Defaults [(t1, t2)]

  getDefaults = SolverM do
    withInplaceOutEnv UnitE \(InfOutMap _ _ defaults _ _) UnitE ->
      inject defaults

  getSynthVars = SolverM do
    withInplaceOutEnv UnitE \(InfOutMap _ _ _ _ svs) UnitE ->
      inject svs

instance Unifier SolverM

freshInferenceName :: Solver m => Kind n -> m n (AtomName n)
freshInferenceName k = do
  ctx <- srcPosCtx <$> getErrCtx
  emitSolver $ InfVarBound k ctx

freshDictName :: Solver m => Type n -> m n (AtomName n)
freshDictName ty = do
  ctx <- srcPosCtx <$> getErrCtx
  emitSolver $ DictVarBound ty ctx

-- TODO: clean up skolem vars!
freshSkolemName :: Solver m => Kind n -> m n (AtomName n)
freshSkolemName k = emitSolver $ SkolemBound k

type Solver2 (m::MonadKind2) = forall i. Solver (m i)
type Alternative1 (m::MonadKind1) = forall n. Alternative (m n)

emptySolverSubst :: SolverSubst n
emptySolverSubst = SolverSubst mempty

singletonSolverSubst :: AtomName n -> Type n -> SolverSubst n
singletonSolverSubst v ty = SolverSubst $ M.singleton v ty

-- We apply the rhs subst over the full lhs subst. We could try tracking
-- metadata about which name->type mappings contain no inference variables and
-- can be skipped.
catSolverSubsts :: Distinct n => Scope n -> SolverSubst n -> SolverSubst n -> SolverSubst n
catSolverSubsts scope (SolverSubst s1) (SolverSubst s2) = SolverSubst $ s1' <> s2
  where s1' = fmap (applySolverSubstE scope (SolverSubst s2)) s1

-- TODO: put this pattern and friends in the Name library? Don't really want to
-- have to think about `eqNameColorRep` just to implement a partial map.
lookupSolverSubst :: forall c n. SolverSubst n -> Name c n -> AtomSubstVal c n
lookupSolverSubst (SolverSubst m) name =
  case eqNameColorRep AtomNameRep (getNameColor name) of
    Nothing -> Rename name
    Just ColorsEqual -> case M.lookup name m of
      Nothing -> Rename name
      Just ty -> SubstVal ty

applySolverSubstE :: (SubstE (SubstVal AtomNameC Atom) e, Distinct n)
                  => Scope n -> SolverSubst n -> e n -> e n
applySolverSubstE scope solverSubst e =
  fmapNames scope (lookupSolverSubst solverSubst) e

zonkWithOutMap :: (SubstE AtomSubstVal e, Distinct n)
               => InfOutMap n -> e n -> e n
zonkWithOutMap (InfOutMap bindings solverSubst _ _ _) e =
  applySolverSubstE (toScope bindings) solverSubst e

_applySolverSubstB :: (SubstB (SubstVal AtomNameC Atom) b, Distinct l)
                   => Scope n -> SolverSubst n -> b n l -> b n l
_applySolverSubstB scope solverSubst e = substBDistinct (scope, env) e
  where env = newEnv $ lookupSolverSubst solverSubst

deleteFromSubst :: SolverSubst n -> AtomName n -> Maybe (SolverSubst n)
deleteFromSubst (SolverSubst m) v
  | M.member v m = Just $ SolverSubst $ M.delete v m
  | otherwise    = Nothing

liftSolverOutFrag :: Distinct l => SolverOutFrag n l -> InfOutFrag n l
liftSolverOutFrag (SolverOutFrag emissions defaults subst) =
  InfOutFrag (liftSolverEmissions emissions) defaults subst

liftSolverEmissions :: Distinct l => SolverEmissions n l -> InfEmissions n l
liftSolverEmissions emissions =
  fmapNest (\(b:>emission) -> (b:>RightE emission)) emissions

instance GenericE SolverSubst where
  -- XXX: this is a bit sketchy because it's not actually bijective...
  type RepE SolverSubst = ListE (PairE AtomName Type)
  fromE (SolverSubst m) = ListE $ map (uncurry PairE) $ M.toList m
  toE (ListE pairs) = SolverSubst $ M.fromList $ map fromPairE pairs

instance InjectableE SolverSubst where
instance SubstE Name SolverSubst where
instance HoistableE SolverSubst

constrainEq :: Inferer m => Type o -> Type o -> m i o ()
constrainEq t1 t2 = do
  t1' <- zonk t1
  t2' <- zonk t2
  let ((t1Pretty, t2Pretty), infVars) = renameForPrinting (t1', t2')
  let msg =   "Expected: " ++ pprint t1Pretty
         ++ "\n  Actual: " ++ pprint t2Pretty
         ++ (if null infVars then "" else
               "\n(Solving for: " ++ pprint infVars ++ ")")
  void $ addContext msg $ liftSolverM $ unify t1' t2'

class (Alternative1 m, Searcher1 m, Fallible1 m, Solver m) => Unifier m

class (AlphaEqE e, InjectableE e, SubstE AtomSubstVal e) => Unifiable (e::E) where
  unifyZonked :: Unifier m => e n -> e n -> m n ()

tryConstrainEq :: Inferer m => Type o -> Type o -> m i o ()
tryConstrainEq t1 t2 = do
  constrainEq t1 t2 `catchErr` \errs -> case errs of
    Errs [Err TypeErr _ _] -> return ()
    _ -> throwErrs errs

unify :: (Unifier m, Unifiable e) => e n -> e n -> m n ()
unify e1 e2 = do
  e1' <- zonk e1
  e2' <- zonk e2
  (     unifyEq e1' e2'
    <|> unifyZonked e1' e2'
    <!> throw TypeErr "")

instance Unifiable Atom where
  unifyZonked e1 e2 =
        unifyDirect e2 e1
    <|> unifyDirect e1 e2
    <|> unifyZip e1 e2
   where
     unifyDirect :: Unifier m => Type n -> Type n -> m n ()
     unifyDirect (Var v) t = extendSolution v t
     unifyDirect _ _ = empty

     unifyZip :: Unifier m => Type n -> Type n -> m n ()
     unifyZip t1 t2 = case (t1, t2) of
       (Pi piTy, Pi piTy') -> unifyPiType piTy piTy'
       (RecordTy  xs, RecordTy  xs') -> unify (ExtLabeledItemsE xs) (ExtLabeledItemsE xs')
       (VariantTy xs, VariantTy xs') -> unify (ExtLabeledItemsE xs) (ExtLabeledItemsE xs')
       (TypeCon (c,_) xs, TypeCon (c',_) xs') ->
         unless (c == c') empty >> unifyFoldable xs xs'
       (TC con, TC con') -> unifyFoldable con con'
       (Eff eff, Eff eff') -> unify eff eff'
       _ -> empty

instance Unifiable (EffectRowP AtomName) where
  unifyZonked x1 x2 =
        unifyDirect x1 x2
    <|> unifyDirect x2 x1
    <|> unifyZip x1 x2

   where
     unifyDirect :: Unifier m => EffectRow n -> EffectRow n -> m n ()
     unifyDirect r (EffectRow effs (Just v)) | S.null effs = extendSolution v (Eff r)
     unifyDirect _ _ = empty

     unifyZip :: Unifier m => EffectRow n -> EffectRow n -> m n ()
     unifyZip r1 r2 = case (r1, r2) of
      (EffectRow effs1 t1, EffectRow effs2 t2) | not (S.null effs1 || S.null effs2) -> do
        let extras1 = effs1 `S.difference` effs2
        let extras2 = effs2 `S.difference` effs1
        newRow <- freshEff
        unify (EffectRow mempty t1) (extendEffRow extras2 newRow)
        unify (extendEffRow extras1 newRow) (EffectRow mempty t2)
      _ -> empty

instance Unifiable (ExtLabeledItemsE Type AtomName) where
  unifyZonked x1 x2 =
        unifyDirect x1 x2
    <|> unifyDirect x2 x1
    <|> unifyZip x1 x2

   where
     unifyDirect :: Unifier m
                 => ExtLabeledItemsE Type AtomName n
                 -> ExtLabeledItemsE Type AtomName n -> m n ()
     unifyDirect (ExtLabeledItemsE r) (ExtLabeledItemsE (Ext NoLabeledItems (Just v))) =
       extendSolution v (LabeledRow r)
     unifyDirect _ _ = empty

     unifyZip :: Unifier m
              => ExtLabeledItemsE Type AtomName n
              -> ExtLabeledItemsE Type AtomName n -> m n ()
     unifyZip (ExtLabeledItemsE r1) (ExtLabeledItemsE r2) = case (r1, r2) of
       (_, Ext NoLabeledItems _) -> empty
       (Ext NoLabeledItems _, _) -> empty
       (Ext (LabeledItems items1) t1, Ext (LabeledItems items2) t2) -> do
         let unifyPrefixes tys1 tys2 = mapM (uncurry unify) $ NE.zip tys1 tys2
         sequence_ $ M.intersectionWith unifyPrefixes items1 items2
         let diffDrop xs ys = NE.nonEmpty $ NE.drop (length ys) xs
         let extras1 = M.differenceWith diffDrop items1 items2
         let extras2 = M.differenceWith diffDrop items2 items1
         newTail <- freshInferenceName LabeledRowKind
         unify (ExtLabeledItemsE (Ext NoLabeledItems t1))
               (ExtLabeledItemsE (Ext (LabeledItems extras2) (Just newTail)))
         unify (ExtLabeledItemsE (Ext NoLabeledItems t2))
               (ExtLabeledItemsE (Ext (LabeledItems extras1) (Just newTail)))

unifyFoldable :: (Eq (f ()), Functor f, Foldable f, Unifiable e, Unifier m)
              => f (e n) -> f (e n) -> m n ()
unifyFoldable xs ys = do
  unless (void xs == void ys) empty
  zipWithM_ unify (toList xs) (toList ys)

unifyEq :: (AlphaEqE e, Unifier m) => e n -> e n -> m n ()
unifyEq e1 e2 = do
  eq <- alphaEq e1 e2
  unless eq empty

unifyPiType :: Unifier m => PiType n -> PiType n -> m n ()
unifyPiType (PiType (PiBinder b1 ann1 arr1) eff1 ty1)
            (PiType (PiBinder b2 ann2 arr2) eff2 ty2) = do
  unless (arr1 == arr2) empty
  unify ann1 ann2
  v <- freshSkolemName ann1
  PairE eff1' ty1' <- applyAbs (Abs b1 (PairE eff1 ty1)) v
  PairE eff2' ty2' <- applyAbs (Abs b2 (PairE eff2 ty2)) v
  unify ty1'  ty2'
  unify eff1' eff2'

extendSolution :: Unifier m => AtomName n -> Type n -> m n ()
extendSolution v t =
  isInferenceName v >>= \case
    True -> do
      when (v `isFreeIn` t) $ throw TypeErr $ "Occurs check failure: " ++ pprint (v, t)
      -- When we unify under a pi binder we replace its occurrences with a
      -- skolem variable. We don't want to unify with terms containing these
      -- variables because that would mean inferring dependence, which is a can
      -- of worms.
      forM_ (freeVarsList AtomNameRep t) \fv ->
        whenM (isSkolemName fv) $ throw TypeErr $ "Can't unify with skolem vars"
      extendSolverSubst v t
    False -> empty

isInferenceName :: BindingsReader m => AtomName n -> m n Bool
isInferenceName v = lookupBindings v >>= \case
  AtomNameBinding (SolverBound (InfVarBound _ _)) -> return True
  _ -> return False

isSkolemName :: BindingsReader m => AtomName n -> m n Bool
isSkolemName v = lookupBindings v >>= \case
  AtomNameBinding (SolverBound (SkolemBound _)) -> return True
  _ -> return False

freshType :: Solver m => Kind n -> m n (Type n)
freshType k = Var <$> freshInferenceName k

freshEff :: Solver m => m n (EffectRow n)
freshEff = EffectRow mempty . Just <$> freshInferenceName EffKind

renameForPrinting :: (Type n, Type n) -> ((Type n, Type n), [AtomName n])
renameForPrinting (t1, t2) = ((t1, t2), []) -- TODO!

-- === dictionary synthesis ===

attemptSynthesis :: (Emits o, Inferer m) => m i o ()
attemptSynthesis = do
  ListE svs <- getSynthVars
  forM_ svs \sv -> do
    ~(AtomNameBinding (SolverBound (DictVarBound ty _))) <- lookupBindings sv
    trySynthDict ty >>= \case
      Nothing -> return ()
      Just d -> extendSolverSubst sv d

-- main entrypoint to dictionary synthesizer
trySynthDict :: (Emits n, Builder m, Scopable m, BindingsReader m)
             => Type n -> m n (Maybe (Atom n))
trySynthDict ty = do
  WithBindings bindings ty' <- addBindings ty
  if hasInferenceVars bindings ty'
    then return Nothing
    else do
      let dicts = runSyntherM bindings $ buildBlock do
                      ty'' <- injectM ty'
                      synthDict ty''
      case dicts of
        [d] -> do
          d' <- injectM d
          Just <$> emitBlock d'
        _ -> return Nothing

class (Alternative1 m, Searcher1 m, Builder m)
      => Synther m where
  tryEachCandidate :: [a] -> m n a
  -- TODO: just expose `unsafeGetBindings` etc to avoid this silly rank-2 dance
  liftSolverSynth
    :: (SubstE AtomSubstVal e', HoistableE e', InjectableE e, InjectableE e')
    => e n
    -> (forall l. e l -> SolverM l (e' l))
    -> m n (e' n)

newtype SyntherM (n::S) (a:: *) = SyntherM
  { runSyntherM' :: BuilderT [] n a }
  deriving ( Functor, Applicative, Monad, BindingsReader
           , Scopable, ScopeReader, MonadFail
           , Alternative, Searcher)

instance Synther SyntherM where
  tryEachCandidate xs = SyntherM $ BuilderT $ liftInplace xs
  liftSolverSynth e cont = do
    WithBindings bindings e' <- addBindings e
    let result = runSolverM bindings do
                   e'' <- injectM e'
                   cont e''
    case result of
      Success result' -> injectM result'
      Failure _ -> empty

instance Builder SyntherM where
  emitDecl hint ann expr = SyntherM $ emitDecl hint ann expr
  buildScopedGeneral ab f = SyntherM $
    buildScopedGeneral ab \e ->
      runSyntherM' $ f e

runSyntherM :: Distinct n
            => Bindings n
            -> (forall l. (Distinct l, Ext n l) => SyntherM l (e l))
            -> [e n]
runSyntherM bindings cont = runBuilderT bindings $ runSyntherM' cont

synthDict :: (Emits n, Synther m) => Type n -> m n (Atom n)
synthDict ty = do
  polyDict <- getGiven <|> getInstance
  ty' <- injectM ty
  polyTy <- getType polyDict
  (params, reqDictTys) <- instantiateDictParams ty' polyTy
  reqDicts <- mapM synthDict reqDictTys
  naryApp polyDict $ params ++ reqDicts

instantiateDictParams :: Synther m => Type n -> Type n -> m n ([Atom n], [Type n])
instantiateDictParams monoTy polyTy = do
  PairE (ListE params) (ListE tys) <-
    liftSolverSynth (PairE monoTy polyTy) \(PairE monoTy' polyTy') -> do
      (params, tys) <- instantiateDictParamsRec monoTy' polyTy'
      return $ PairE (ListE params) (ListE tys)
  return (params, tys)

instantiateDictParamsRec :: Unifier m => Type n -> Type n -> m n ([Atom n], [Type n])
instantiateDictParamsRec monoTy polyTy = case polyTy of
  Pi (PiType (PiBinder b argTy ImplicitArrow) _ resultTy) -> do
    param <- freshInferenceName argTy
    resultTy' <- applyAbs (Abs b resultTy) param
    (params, dictTys) <- instantiateDictParamsRec monoTy resultTy'
    return (Var param : params, dictTys)
  Pi (PiType (PiBinder b dictTy ClassArrow) _ resultTy) -> do
    case fromConstAbs (Abs b resultTy) of
      Just resultTy' -> do
        (params, dictTys) <- instantiateDictParamsRec monoTy resultTy'
        case params of
          [] -> return ([], dictTy:dictTys)
          _ -> error "Not implemented: interleaved params and class constraints"
      Nothing -> error "shouldn't have dependent class arrow"
  _ -> do
    unify monoTy polyTy
    return ([], [])

getGiven :: Synther m => m n (Atom n)
getGiven = (lambdaDicts <$> getSynthCandidatesM) >>= tryEachCandidate

getInstance :: Synther m => m n (Atom n)
getInstance = (instanceDicts <$> getSynthCandidatesM) >>= tryEachCandidate

-- === Zonkable source map hack ===

-- This is a hack to give a dummy `SubstE Atom` instance to SourceMap. We need
-- one because the inference machinery wants to zonk everything before
-- returning, but we can't give it a real one because it's just a name-to-name
-- mapping. We might be able to avoid this hack if we make inference names a
-- distinct name color.

newtype ZonkableSourceMap (n::S) =
  ZonkableSM (SourceMap n)
  deriving (HoistableE, InjectableE)

instance SubstE Name ZonkableSourceMap where
  substE env (ZonkableSM e) = ZonkableSM $ substE env e

instance SubstE AtomSubstVal ZonkableSourceMap where
  substE (scope, env) e = substE (scope, env') e
    where env' = newEnv \v -> case env ! v of
                   SubstVal (Var v') -> v'
                   SubstVal _ -> error "shouldn't happen"
                   Rename v' -> v'
