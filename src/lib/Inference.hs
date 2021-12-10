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

module Inference (inferModule, synthModule, trySynthDict, trySynthDictBlock) where

import Prelude hiding ((.), id)
import Control.Category
import Control.Applicative
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Writer.Strict hiding (Alt)
import Control.Monad.Reader
import Data.Foldable (toList, asum)
import Data.Function ((&))
import Data.Functor ((<&>), ($>))
import Data.List (sortOn, intercalate)
import Data.Maybe (fromJust)
import Data.String (fromString)
import Data.Text.Prettyprint.Doc (Pretty (..))
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Unsafe.Coerce as TrulyUnsafe

import Name
import Builder
import Syntax hiding (State)
import Type
import PPrint ()
import CheapReduction
import GenericTraversal
import MTL1

import LabeledItems
import Err
import Util

inferModule :: Distinct n => Env n -> UModule n -> Except (Module n)
inferModule bindings uModule@(UModule decl _) = do
  if isTopDecl decl
    then do
      DistinctAbs bs UnitE <- runTopInfererM bindings do
        Immut <- return $ toImmutEvidence bindings
        localTopBuilder do
          UModule decl' sourceMap <- return uModule
          inferUDeclTop decl' $
            substM sourceMap >>= emitSourceMap
          return UnitE
      return $ Module Typed Empty $ Abs bs UnitE
    else do
      ab <- runInfererM bindings do
        UModule decl' sourceMap <- return uModule
        Immut <- return $ toImmutEvidence bindings
        solveLocal $
          buildDeclsInfUnzonked $
            inferUDeclLocal decl' do
              applyDefaults
              substM sourceMap
      DistinctAbs decls sm <- return $ refreshAbs (toScope bindings) ab
      let scs = bindingsFragToSynthCandidates $ toEnvFrag decls
      return $ Module Typed decls $ Abs (TopEnvFrag emptyOutFrag scs sm) UnitE

isTopDecl :: UDecl n l -> Bool
isTopDecl decl = case decl of
  ULet         _ _ _     -> False
  UDataDefDecl _ _ _     -> True
  UInterface   _ _ _ _ _ -> True
  UInstance    _ _ _ _ _ -> False

-- === Top-level inferer ===

class ( MonadFail2 m, Fallible2 m, CtxReader2 m, TopBuilder2 m
      , SubstReader Name m) => TopInferer m where

newtype TopInfererM i o a = TopInfererM
  { runTopInfererM' :: SubstReaderT Name (TopBuilderT FallibleM) i o a }
  deriving ( Functor, Applicative, Monad, MonadFail, ScopeReader
           , Fallible, CtxReader, SubstReader Name, EnvReader, TopBuilder)

instance TopInferer TopInfererM where

runTopInfererM
  :: Distinct n
  => Env n
  -> TopInfererM n n a
  -> Except a
runTopInfererM bindings cont =
  runFallibleM $ runTopBuilderT bindings $ runSubstReaderT idSubst $
    runTopInfererM' $ cont

applyDefaults :: (EmitsInf o, Inferer m) => m i o ()
applyDefaults = do
  Defaults defaults <- getDefaults
  forM_ defaults \(ty, ty') ->
    tryConstrainEq ty (sinkFromTop ty')

-- === Inferer interface ===

class ( MonadFail1 m, Fallible1 m, Catchable1 m, CtxReader1 m
      , Builder m)
      => InfBuilder (m::MonadKind1) where

  -- XXX: we should almost always used the zonking `buildDeclsInf` and variant,
  -- except where it's not possible because the result isn't atom-substitutable,
  -- such as the source map at the top level.
  buildDeclsInfUnzonked
    :: (SinkableE e, HoistableE e)
    => EmitsInf n
    => (forall l. (EmitsBoth l, DExt n l) => m l (e l))
    -> m n (Abs (Nest Decl) e n)

  buildAbsInf
    :: (SinkableE e, HoistableE e, NameColor c, ToBinding binding c)
    => EmitsInf n
    => NameHint -> binding n
    -> (forall l. (EmitsInf l, DExt n l) => Name c l -> m l (e l))
    -> m n (Abs (BinderP c binding) e n)

buildDeclsInf
  :: (SubstE AtomSubstVal e, Solver m, InfBuilder m)
  => (SinkableE e, HoistableE e)
  => EmitsInf n
  => (forall l. (EmitsBoth l, DExt n l) => m l (e l))
  -> m n (Abs (Nest Decl) e n)
buildDeclsInf cont = buildDeclsInfUnzonked $ cont >>= zonk

type InfBuilder2 (m::MonadKind2) = forall i. InfBuilder (m i)

type IfaceType = Type
class (SubstReader Name m, InfBuilder2 m, Solver2 m)
      => Inferer (m::MonadKind2) where
  liftSolverM :: EmitsInf o => SolverM o a -> m i o a
  gatherUnsolvedInterfaces :: m i o a -> m i o (a, [IfaceType o])
  reportUnsolvedInterface  :: Type o  -> m i o ()

-- === Concrete Inferer monad ===

data InfOutMap (n::S) =
  InfOutMap
    (Env n)
    (SolverSubst n)
    (Defaults n)
    -- the subset of the names in the bindings whose definitions may contain
    -- inference vars (this is so we can avoid zonking everything in scope when
    -- we zonk bindings)
    (UnsolvedEnv n)

newtype Defaults (n::S) = Defaults [(Atom n, Atom VoidS)]
        deriving (Semigroup, Monoid, Show)

instance GenericE Defaults where
  type RepE Defaults = ListE (PairE Atom (LiftE (Atom VoidS)))
  fromE (Defaults xys) = ListE [PairE x (LiftE y) | (x, y) <- xys]
  toE (ListE xys) = Defaults [(x, y) | PairE x (LiftE y) <- xys]

instance SinkableE         Defaults
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
instance SinkableB InfOutFrag
instance HoistableB  InfOutFrag

instance OutFrag InfOutFrag where
  emptyOutFrag = InfOutFrag Empty mempty emptySolverSubst
  catOutFrags scope (InfOutFrag em ds ss) (InfOutFrag em' ds' ss') =
    withExtEvidence em' $
      InfOutFrag (em >>> em') (sink ds <> ds') (catSolverSubsts scope (sink ss) ss')

instance HasScope InfOutMap where
  toScope (InfOutMap bindings _ _ _) = toScope bindings

instance OutMap InfOutMap where
  emptyOutMap = InfOutMap emptyOutMap emptySolverSubst mempty mempty

instance ExtOutMap InfOutMap EnvFrag where
  extendOutMap (InfOutMap bindings ss dd oldUn) frag =
    withExtEvidence frag do
      let newUn = UnsolvedEnv $ getAtomNames frag
      -- as an optimization, only do the zonking for the new stuff
      let newEnv = bindings `extendOutMap` frag
      let (zonkedUn, zonkedEnv) = zonkUnsolvedEnv (sink ss) newUn newEnv
      InfOutMap zonkedEnv (sink ss) (sink dd) (sink oldUn <> zonkedUn)

newtype UnsolvedEnv (n::S) =
  UnsolvedEnv { fromUnsolvedEnv :: S.Set (AtomName n) }
  deriving (Semigroup, Monoid)

instance SinkableE UnsolvedEnv where
  sinkingProofE = todoSinkableProof

getAtomNames :: Distinct l => EnvFrag n l -> S.Set (AtomName l)
getAtomNames frag = S.fromList $ nameSetToList AtomNameRep $ toNameSet $ toScopeFrag frag

-- query each binding rhs for inference names and add it to the set if needed

extendInfOutMapSolver :: Distinct n => InfOutMap n -> SolverSubst n -> InfOutMap n
extendInfOutMapSolver (InfOutMap bindings ss dd un) ss' = do
  let (un', bindings') = zonkUnsolvedEnv ss' un bindings
  let ssFinal = catSolverSubsts (toScope bindings) ss ss'
  InfOutMap bindings' ssFinal dd un'

substIsEmpty :: SolverSubst n -> Bool
substIsEmpty (SolverSubst subst) = null subst

-- TODO: zonk the allowed effects and synth candidates in the bindings too
-- TODO: the reason we need this is that `getType` uses the bindings to obtain
-- type information, and we need this information when we emit decls. For
-- example, if we emit `f x` and we don't know that `f` has a type of the form
-- `a -> b` then `getType` will crash. But we control the inference-specific
-- implementation of `emitDecl`, so maybe we could instead do something like
-- emit a fresh inference variable in the case thea `getType` fails.
zonkUnsolvedEnv :: Distinct n => SolverSubst n -> UnsolvedEnv n -> Env n
                     -> (UnsolvedEnv n, Env n)
zonkUnsolvedEnv ss un bindings | substIsEmpty ss = (un, bindings)
zonkUnsolvedEnv ss unsolved bindings =
  flip runState bindings $ execWriterT do
    forM_ (S.toList $ fromUnsolvedEnv unsolved) \v -> do
      rhs <- flip lookupEnvPure v <$> get
      let rhs' = zonkWithOutMap (InfOutMap bindings ss mempty mempty) rhs
      modify $ updateEnv v rhs'
      when (hasInferenceVars bindings rhs') $
        tell $ UnsolvedEnv $ S.singleton v

hasInferenceVars :: HoistableE e => Env n -> e n -> Bool
hasInferenceVars bs e = any (isInferenceVar bs) $ freeVarsList AtomNameRep e

isInferenceVar :: Env n -> AtomName n -> Bool
isInferenceVar bs v = case lookupEnvPure bs v of
  AtomNameBinding (SolverBound _) -> True
  _                               -> False

instance ExtOutMap InfOutMap InfOutFrag where
  extendOutMap infOutMap (InfOutFrag em ds solverSubst) = do
    extendDefaults ds $
      flip extendInfOutMapSolver solverSubst $
        flip extendOutMap (toEnvFrag em) $
          infOutMap

extendDefaults :: Defaults n -> InfOutMap n -> InfOutMap n
extendDefaults ds' (InfOutMap bindings ss ds un) =
  InfOutMap bindings ss (ds <> ds') un

-- TODO: Make GatherRequired hold a set
data RequiredIfaces (n::S) = FailIfRequired | GatherRequired [IfaceType n]
instance GenericE RequiredIfaces where
  type RepE RequiredIfaces = MaybeE (ListE IfaceType)
  fromE = \case
    FailIfRequired    -> NothingE
    GatherRequired ds -> JustE (ListE ds)
  toE = \case
    NothingE         -> FailIfRequired
    JustE (ListE ds) -> GatherRequired ds
    _ -> error "unreachable"
instance SinkableE RequiredIfaces
instance HoistableE  RequiredIfaces

newtype InfererM (i::S) (o::S) (a:: *) = InfererM
  { runInfererM' :: SubstReaderT Name (StateT1 RequiredIfaces (InplaceT InfOutMap InfOutFrag FallibleM)) i o a }
  deriving (Functor, Applicative, Monad, MonadFail, MonadState (RequiredIfaces o),
            ScopeReader, Fallible, Catchable, CtxReader, SubstReader Name)

runInfererM :: Distinct n => Env n -> InfererM n n a -> Except a
runInfererM bindings cont = runSubstInfererM bindings idSubst cont

liftInfererM :: (Fallible2 m, CtxReader2 m, SubstReader Name m, EnvReader2 m)
             => Immut o
             => InfererM i o a -> m i o a
liftInfererM cont = do
  DB bindings <- getDB
  env <- getSubst
  liftExcept $ runSubstInfererM bindings env cont

runLocalInfererM
  :: (Immut n, SinkableE e)
  => (forall l. (EmitsInf l, DExt n l) => InfererM i l (e l))
  -> InfererM i n (DistinctAbs InfOutFrag e n)
runLocalInfererM cont = InfererM $ SubstReaderT $ ReaderT \env -> StateT1 \s -> do
  DistinctAbs fg (PairE ans s') <- locallyMutableInplaceT do
    Distinct <- getDistinct
    EmitsInf <- fabricateEmitsInfEvidenceM
    toPairE <$> (runStateT1 (runSubstReaderT (sink env) $ runInfererM' cont) (sink s))
  return (DistinctAbs fg ans, hoistRequiredIfaces fg s')

runSubstInfererM :: Distinct o => Env o -> Subst Name i o -> InfererM i o a -> Except a
runSubstInfererM bindings env cont = do
  (InfOutFrag Empty _ _, (result, _)) <-
    runFallibleM do
      Immut <- return $ toImmutEvidence bindings
      runInplaceT (initInfOutMap bindings) $
        runStateT1 (runSubstReaderT env $ runInfererM' $ cont) FailIfRequired
  return result

initInfOutMap :: Env n -> InfOutMap n
initInfOutMap bindings =
  InfOutMap bindings emptySolverSubst mempty (UnsolvedEnv mempty)

emitInfererM :: Mut o => NameHint -> InfEmission o -> InfererM i o (AtomName o)
emitInfererM hint emission = InfererM $ SubstReaderT $ lift $ lift11 $
  emitInplaceT hint emission \b emission' ->
    InfOutFrag (Nest (b :> emission') Empty) mempty emptySolverSubst

instance Solver (InfererM i) where
  extendSolverSubst v ty = InfererM $ SubstReaderT $ lift $ lift11 $
    void $ extendTrivialInplaceT $
      InfOutFrag Empty mempty (singletonSolverSubst v ty)

  zonk e = InfererM $ SubstReaderT $ lift $ lift11 $ liftImmut do
    Distinct <- getDistinct
    solverOutMap <- getOutMapInplaceT
    return $ zonkWithOutMap solverOutMap e

  emitSolver binding = emitInfererM "?" $ RightE binding

  addDefault t1 t2 = InfererM $ SubstReaderT $ lift $ lift11 $
    extendTrivialInplaceT $ InfOutFrag Empty defaults emptySolverSubst
    where defaults = Defaults [(t1, t2)]

  getDefaults = InfererM $ SubstReaderT $ lift $ lift11 $ liftImmut do
    InfOutMap _ _ defaults _ <- getOutMapInplaceT
    return defaults

  solveLocal cont = do
    DistinctAbs (InfOutFrag unsolvedInfNames _ _) result <- runLocalInfererM cont
    case unsolvedInfNames of
      Empty -> return result
      Nest (_:>RightE (InfVarBound _ ctx)) _ ->
        addSrcContext ctx $ throw TypeErr $ "Ambiguous type variable"
      _ -> error "not possible?"

instance InfBuilder (InfererM i) where
  buildDeclsInfUnzonked cont = do
    InfererM $ SubstReaderT $ ReaderT \env -> StateT1 \s -> do
      Abs decls (PairE result s') <- extendInplaceT do
        DistinctAbs frag resultWithState <- locallyMutableInplaceT do
          Emits    <- fabricateEmitsEvidenceM
          EmitsInf <- fabricateEmitsInfEvidenceM
          toPairE <$> runStateT1 (runSubstReaderT (sink env) $ runInfererM' cont) (sink s)
        scope <- getScope
        hoistThroughDecls scope frag resultWithState
      return (Abs decls result, hoistRequiredIfaces decls s')

  buildAbsInf hint binding cont = do
    InfererM $ SubstReaderT $ ReaderT \env -> StateT1 \s -> do
      Abs b (PairE result s') <- extendInplaceT do
        scope <- getScope
        withFresh hint nameColorRep scope \b -> do
          let b' = b :> sink binding
          let bExt = toEnvFrag b'
          extendInplaceTLocal (\bindings -> extendOutMap bindings bExt) do
            DistinctAbs infFrag resultWithState <- locallyMutableInplaceT do
              EmitsInf <- fabricateEmitsInfEvidenceM
              toPairE <$> runStateT1 (
                runSubstReaderT (sink env) (runInfererM' $ cont $ sink $ binderName b)) (sink s)
            PairB infFrag' b'' <- liftHoistExcept $ exchangeBs $ PairB b' infFrag
            return $ withSubscopeDistinct b'' $ DistinctAbs infFrag' $ Abs b'' resultWithState
      return (Abs b result, hoistRequiredIfaces b s')

instance Inferer InfererM where
  liftSolverM m = InfererM $ SubstReaderT $ lift $ lift11 $
    liftBetweenInplaceTs (liftExcept . liftM fromJust . runSearcherM) id liftSolverOutFrag $
      runSolverM' m

  gatherUnsolvedInterfaces m = do
    s' <- get
    put $ GatherRequired []
    ans <- m
    ds <- get
    put s'
    case ds of
      FailIfRequired     -> throw CompilerErr "Unexpected FailIfRequired?"
      GatherRequired ds' -> return (ans, ds')

  reportUnsolvedInterface iface = do
    UnitE <- liftImmut do
      DB bindings <- getDB
      when (hasInferenceVars bindings (sink iface)) $ throw NotImplementedErr $
        "Inference requires delayed interface resolution"
      return UnitE
    get >>= \case
      FailIfRequired    -> throw TypeErr $ "Couldn't synthesize a class dictionary for: " ++ pprint iface
      GatherRequired ds -> put $ GatherRequired $ iface:ds

instance Builder (InfererM i) where
  emitDecl hint ann expr = do
    -- This zonking, and the zonking of the bindings elsewhere, is only to
    -- prevent `getType` from failing. But maybe we should just catch the
    -- failure if it occurs and generate a fresh inference name for the type in
    -- that case?
    expr' <- zonk expr
    ty <- getType expr'
    emitInfererM hint $ LeftE $ DeclBinding ann ty expr'

  buildScoped cont = do
    InfererM $ SubstReaderT $ ReaderT \env -> StateT1 \s -> do
      resultWithEmissions <- locallyMutableInplaceT do
        Emits <- fabricateEmitsEvidenceM
        toPairE <$> runStateT1 (runSubstReaderT (sink env) $ runInfererM' cont) (sink s)
      DistinctAbs frag@(InfOutFrag emissions _ _) (PairE result s') <- return resultWithEmissions
      let decls = fmapNest (\(b:>LeftE rhs) -> Let b rhs) emissions
      return (DistinctAbs decls result, hoistRequiredIfaces frag s')

type InferenceNameBinders = Nest (BinderP AtomNameC SolverBinding)

-- When we finish building a block of decls we need to hoist the local solver
-- information into the outer scope. If the local solver state mentions local
-- variables which are about to go out of scope then we emit a "escaped scope"
-- error. To avoid false positives, we clean up as much dead (i.e. solved)
-- solver state as possible.
hoistThroughDecls
  :: (Fallible m, HoistableE e, Distinct l)
  => Scope n
  -> InfOutFrag n l
  ->   e l
  -> m (DistinctAbs InfOutFrag (Abs (Nest Decl) e) n)
hoistThroughDecls scope (InfOutFrag emissions defaults subst) result = do
  withSubscopeDistinct emissions do
    HoistedSolverState infVars defaults' subst' (DistinctAbs decls result') <-
      hoistInfStateRec scope emissions defaults subst result
    let hoistedInfFrag = InfOutFrag (infNamesToEmissions infVars) defaults' subst'
    return $ DistinctAbs hoistedInfFrag $ Abs decls result'

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

dceIfSolved :: HoistableE e
            => NameBinder AtomNameC n l -> HoistedSolverState e l
            -> Maybe (HoistedSolverState e n)
dceIfSolved b (HoistedSolverState infVars defaults subst result) = do
  let v = withExtEvidence infVars $ sink $ binderName b
  case deleteFromSubst subst v of
    Just subst' ->
      -- do we need to zonk here? (if not, say why not)
      case hoist b (HoistedSolverState infVars defaults subst' result) of
        HoistSuccess hoisted -> Just hoisted
        HoistFailure err -> error $ "this shouldn't happen. Leaked var: " ++ pprint err
    Nothing -> Nothing

hoistInfStateRec :: (Fallible m, Distinct n, Distinct l, HoistableE e)
                 => Scope n
                 -> InfEmissions n l -> Defaults l -> SolverSubst l -> e l
                 -> m (HoistedSolverState e n)
hoistInfStateRec scope Empty defaults subst e = do
  let defaults' = applySolverSubstE scope subst defaults
  return $ HoistedSolverState Empty defaults' subst (DistinctAbs Empty e)
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
      RightE (SkolemBound _) ->
        case hoist b solverState of
          HoistSuccess hoisted -> return hoisted
          HoistFailure _ -> error "probably shouldn't happen?"
      LeftE emission -> do
        -- TODO: avoid this repeated traversal here and in `tryHoistExpr`
        --       above by using `WithRestrictedScope` to cache free vars.
        PairB infVars' (b':>emission') <- liftHoistExcept $
                                            exchangeBs (PairB (b:>emission) infVars)
        subst'' <- liftHoistExcept $ hoist b' subst'
        let defaults'' = hoistDefaults b' defaults'
        withSubscopeDistinct b' $ do
            let scope' = scope `extendOutMap` toScopeFrag infVars'
            let emission'' = applySolverSubstE scope' subst'' emission'
            DistinctAbs rest' e' <- return result
            return $ HoistedSolverState infVars' defaults'' subst'' $
                        DistinctAbs (Nest (Let b' emission'') rest') e'

hoistRequiredIfaces :: BindsNames b => b n l -> RequiredIfaces l -> RequiredIfaces n
hoistRequiredIfaces bs = \case
  FailIfRequired    -> FailIfRequired
  GatherRequired ds -> GatherRequired $ ds & mapMaybe \d -> case hoist bs d of
    HoistSuccess d' -> Just d'
    HoistFailure _  -> Nothing

hoistDefaults :: BindsNames b => b n l -> Defaults l -> Defaults n
hoistDefaults b (Defaults defaults) =
  Defaults $ defaults & mapMaybe \(t1, t2) -> case hoist b t1 of
      HoistSuccess t1' -> Just (t1', t2)
      HoistFailure _   -> Nothing

infNamesToEmissions :: InferenceNameBinders n l -> InfEmissions n l
infNamesToEmissions emissions =
  fmapNest (\(b:>binding) -> b :> RightE binding) emissions

instance EnvReader (InfererM i) where
  getEnv = do
    InfOutMap bindings _ _ _ <- InfererM $ SubstReaderT $ lift $ lift11 $ getOutMapInplaceT
    return bindings

instance EnvExtender (InfererM i) where
  extendEnv frag cont = InfererM $ SubstReaderT $ ReaderT \env -> StateT1 \s -> do
    (ans, s') <- extendInplaceTLocal (\bindings -> extendOutMap bindings frag) $
      withExtEvidence (toExtEvidence frag) $
        runStateT1 (runSubstReaderT (sink env) (runInfererM' cont)) (sink s)
    return (ans, hoistRequiredIfaces frag s')

-- === actual inference pass ===

type SigmaType = Type  -- may     start with an implicit lambda
type RhoType   = Type  -- doesn't start with an implicit lambda
data RequiredTy (e::E) (n::S) = Check (e n)
                              | Infer
                                deriving Show

checkSigma :: (EmitsBoth o, Inferer m) => UExpr i
           -> SigmaType o -> m i o (Atom o)
checkSigma expr sTy = case sTy of
  Pi piTy@(PiType (PiBinder b _ arrow) _ _)
    | arrow `elem` [ImplicitArrow, ClassArrow] -> case expr of
        WithSrcE _ (ULam lam@(ULamExpr arrow' _ _))
          | arrow == arrow' ->
            -- is this even reachable? we don't have syntax for implicit/class lambda
            checkULam lam piTy
        -- we have to add the lambda argument corresponding to the implicit pi
        -- type argument
        _ -> do
          buildLamInf (getNameHint b) arrow (piArgType piTy) (\_-> return Pure)
            \x -> do
              piTy' <- sinkM piTy
              (Pure, bodyTy) <- instantiatePi piTy' (Var x)
              checkSigma expr bodyTy
  _ -> checkOrInferRho expr (Check sTy)

inferSigma :: (EmitsBoth o, Inferer m) => UExpr i -> m i o (Atom o)
inferSigma (WithSrcE pos expr) = case expr of
  ULam lam@(ULamExpr ImplicitArrow _ _) ->
    addSrcContext pos $ inferULam Pure lam
  _ -> inferRho (WithSrcE pos expr)

checkRho :: (EmitsBoth o, Inferer m) => UExpr i -> RhoType o -> m i o (Atom o)
checkRho expr ty = checkOrInferRho expr (Check ty)

inferRho :: (EmitsBoth o, Inferer m) => UExpr i -> m i o (Atom o)
inferRho expr = checkOrInferRho expr Infer

instantiateSigma :: (EmitsBoth o, Inferer m) => Atom o -> m i o (Atom o)
instantiateSigma f = do
  ty <- tryGetType f
  case ty of
    Pi (PiType (PiBinder _ argTy ImplicitArrow) _ _) -> do
      x <- freshType argTy
      ans <- emit $ App f x
      instantiateSigma $ Var ans
    Pi (PiType (PiBinder _ argTy ClassArrow) _ _) -> do
      ctx <- srcPosCtx <$> getErrCtx
      dict <- emit $ Op $ SynthesizeDict ctx argTy
      ans <- emit $ App f $ Var dict
      instantiateSigma $ Var ans
    _ -> return f

checkOrInferRho :: forall m i o.
                   (EmitsBoth o, Inferer m)
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
      Check (Pi piTy) -> checkULam lamExpr piTy
      Check _ -> inferULam Pure lamExpr >>= matchRequirement
      Infer   -> inferULam Pure lamExpr
  UFor dir (UForExpr b body) -> do
    allowedEff <- getAllowedEffects
    let uLamExpr = ULamExpr PlainArrow b body
    lam <- case reqTy of
      Check (Pi tabPiTy) -> do
        lamPiTy <- buildForTypeFromTabType allowedEff tabPiTy
        checkULam uLamExpr lamPiTy
      Check _ -> inferULam allowedEff uLamExpr
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
        x' <- checkSigma x argTy
        addEffects effs
        appVal <- emit $ App f' x'
        instantiateSigma (Var appVal) >>= matchRequirement
      Nothing -> do
        Abs decls result <- buildDeclsInf do
          argTy' <- sinkM $ piArgType piTy
          checkSigma x argTy'
        cheapReduceWithDecls decls result >>= \case
          (Just x', Just ds) -> do
            forM_ ds reportUnsolvedInterface
            (effs, _) <- instantiatePi piTy x'
            addEffects effs
            appVal <- emit $ App f' x'
            instantiateSigma (Var appVal) >>= matchRequirement
          _ -> addSrcContext xPos $ do
            throw TypeErr $ "Dependent functions can only be applied to fully " ++
                            "evaluated expressions. Bind the argument to a name " ++
                            "before you apply the function."
  UPi (UPiExpr arr (UPatAnn (WithSrcB pos' pat) ann) effs ty) -> do
    -- TODO: make sure there's no effect if it's an implicit or table arrow
    matchRequirement . Pi =<< checkAnnWithMissingDicts ann \missingDs getAnnType -> do
      -- Note that we can't automatically quantify class Pis, because the class dict
      -- might have been bound on the rhs of a let and it would get bound to the
      -- inserted arguments instead of the desired dict. It's not a fundemental
      -- limitation of our automatic quantification, but it's simpler not to deal with
      -- that for now.
      let checkNoMissing = addSrcContext pos' $ unless (null missingDs) $ throw TypeErr $
            "Couldn't synthesize a class dictionary for: " ++ pprint (head missingDs)
      autoDs <- case arr of
        TabArrow   -> checkNoMissing $> mempty
        ClassArrow -> checkNoMissing $> mempty
        _          -> return $ missingDs
      introDictTys autoDs $ do
        ann' <- getAnnType
        addSrcContext pos' case pat of
          UPatBinder UIgnore ->
            buildPiInf "_ign" arr ann' \_ -> (,) <$> checkUEffRow effs <*> checkUType ty
          _ -> buildPiInf (getNameHint pat) arr ann' \v -> do
            Abs decls piResult <- buildDeclsInf do
              v' <- sinkM v
              bindLamPat (WithSrcB pos' pat) v' do
                effs' <- checkUEffRow effs
                ty'   <- checkUType   ty
                return $ PairE effs' ty'
            cheapReduceWithDecls decls piResult >>= \case
              (Just (PairE effs' ty'), Just []) -> return $ (effs', ty')
              _ -> throw TypeErr $ "Can't reduce type expression: " ++
                     pprint (Block (BlockAnn TyKind) decls $ Atom $ snd $ fromPairE piResult)
  UDecl (UDeclExpr decl body) -> do
    inferUDeclLocal decl $ checkOrInferRho body reqTy
  UCase scrut alts -> do
    scrut' <- inferRho scrut
    scrutTy <- getType scrut'
    reqTy' <- case reqTy of
      Infer -> freshType TyKind
      Check req -> return req
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
    Check ty -> freshType ty
  UTypeAnn val ty -> do
    ty' <- zonk =<< checkUType ty
    val' <- checkSigma val ty'
    matchRequirement val'
  UPrimExpr prim -> do
    prim' <- forM prim \x -> do
      xBlock <- buildBlockInf $ inferRho x
      getType xBlock >>= \case
        TyKind -> cheapReduceToAtom xBlock >>= \case
          (Just reduced, Just []) -> return reduced
          _ -> throw CompilerErr "Type args to primops must be reducible"
        _ -> emitBlock xBlock
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
  UIntLit x  -> do
    lookupSourceMap MethodNameRep "fromInteger" >>= \case
      Nothing ->
        -- fallback for missing protolude
        matchRequirement $ Con $ Lit $ Int32Lit $ fromIntegral x
      Just fromIntMethod -> do
        ~(MethodBinding _ _ fromInt) <- lookupEnv fromIntMethod
        fromInt' <- instantiateSigma fromInt
        let i64Atom = Con $ Lit $ Int64Lit $ fromIntegral x
        result <- matchRequirement =<< app fromInt' i64Atom
        resultTy <- getType result
        addDefault resultTy $ BaseTy (Scalar Int32Type)
        return result
  UFloatLit x -> matchRequirement $ Con $ Lit  $ Float32Lit $ realToFrac x
  -- TODO: Make sure that this conversion is not lossy!
  where
    matchRequirement :: Atom o -> m i o (Atom o)
    matchRequirement x = return x <*
      case reqTy of
        Infer -> return ()
        Check req -> do
          ty <- getType x
          constrainEq req ty

-- === sorting case alternatives ===

data IndexedAlt n = IndexedAlt CaseAltIndex (Alt n)

instance SinkableE IndexedAlt where
  sinkingProofE = todoSinkableProof

buildNthOrderedAlt :: (Emits n, Builder m)
                   => [IndexedAlt n] -> Type n -> Type n -> Int -> [AtomName n]
                   -> m n (Atom n)
buildNthOrderedAlt alts scrutTy resultTy i vs = do
  case lookup (nthCaseAltIdx scrutTy i) [(idx, alt) | IndexedAlt idx alt <- alts] of
    Nothing -> do
      resultTy' <- sinkM resultTy
      emitOp $ ThrowError resultTy'
    Just alt -> applyNaryAbs alt vs >>= emitBlock

-- converts from the ordinal index used in the core IR to the more complicated
-- `CaseAltIndex` used in the surface IR.
nthCaseAltIdx :: Type n -> Int -> CaseAltIndex
nthCaseAltIdx ty i = case ty of
  TypeCon _ _ _ -> ConAlt i
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
    ListE alts' <- sinkM $ ListE alts
    scrutTy'    <- sinkM scrutTy
    resultTy'   <- sinkM resultTy
    buildNthOrderedAlt alts' scrutTy' resultTy' i vs

buildSortedCase :: (Fallible1 m, Builder m, Emits n)
                 => Atom n -> [IndexedAlt n] -> Type n
                 -> m n (Atom n)
buildSortedCase scrut alts resultTy = do
  scrutTy <- getType scrut
  case scrutTy of
    TypeCon _ _ _ -> buildMonomorphicCase alts scrut resultTy
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
              (\v -> do ListE alts' <- sinkM $ ListE alts
                        resultTy'   <- sinkM resultTy
                        buildMonomorphicCase alts' (Var v) resultTy')
              (\_ -> do resultTy' <- sinkM resultTy
                        emitOp $ ThrowError resultTy')
        [IndexedAlt (VariantTailAlt (LabeledItems skippedItems)) tailAlt] -> do
            -- Split off the types skipped by the tail pattern.
            let splitLeft fvs ltys = NE.fromList $ NE.take (length ltys) fvs
            let left = LabeledItems $ M.intersectionWith splitLeft
                        (fromLabeledItems types) skippedItems
            checkNoTailOverlaps alts left
            buildSplitCase left scrut resultTy
              (\v -> do ListE alts' <- sinkM $ ListE alts
                        resultTy'   <- sinkM resultTy
                        buildMonomorphicCase alts' (Var v) resultTy')
              (\v -> do tailAlt' <- sinkM tailAlt
                        applyNaryAbs tailAlt' [v] >>= emitBlock )
        _ -> throw TypeErr "Can't specify more than one variant tail pattern."
    _ -> fail $ "Unexpected case expression type: " <> pprint scrutTy

-- Make sure all of the alternatives are exclusive with the tail pattern (could
-- technically allow overlap but this is simpler). Split based on the tail
-- pattern's skipped types.
checkNoTailOverlaps :: Fallible1 m => [IndexedAlt n] -> LabeledItems (Type n) ->  m n ()
checkNoTailOverlaps alts (LabeledItems tys) = do
  forM_ alts \case
    (IndexedAlt (VariantAlt label i) _) ->
      case M.lookup label tys of
        Just tys' | i <= length tys' -> return ()
        _ -> throw TypeErr "Variant explicit alternatives overlap with tail pattern."
    _ -> return ()

isVariantTailAlt :: IndexedAlt n -> Bool
isVariantTailAlt (IndexedAlt (VariantTailAlt _) _) = True
isVariantTailAlt _ = False

-- ===

inferUVar :: Inferer m => UVar o -> m i o (Atom o)
inferUVar = \case
  UAtomVar v ->
    return $ Var v
  UTyConVar v -> do
    TyConBinding   _ tyConAtom <- lookupEnv v
    return tyConAtom
  UDataConVar v -> do
    DataConBinding _ _ conAtom <- lookupEnv v
    return conAtom
  UClassVar v -> do
    ClassBinding _ dictTyAtom <- lookupEnv v
    return dictTyAtom
  UMethodVar v -> do
    MethodBinding _ _ getter <- lookupEnv v
    return getter

buildForTypeFromTabType :: (Fallible1 m, Builder m)
                        => EffectRow n -> PiType n -> m n (PiType n)
buildForTypeFromTabType effs tabPiTy@(PiType (PiBinder bPi piArgTy arr) _ _) = do
  unless (arr == TabArrow) $ throw TypeErr $ "Not an table arrow type: " ++ pprint arr
  buildPi (getNameHint bPi) PlainArrow piArgTy \i -> do
    Distinct <- getDistinct
    (_, resultTy) <- instantiatePi (sink tabPiTy) $ Var i
    return (sink effs, resultTy)

inferUDeclLocal ::  (EmitsBoth o, Inferer m) => UDecl i i' -> m i' o a -> m i o a
inferUDeclLocal (ULet letAnn (UPatAnn p ann) rhs) cont = do
  val <- case ann of
    Nothing -> inferSigma rhs
    Just ty -> do
      ty' <- zonk =<< checkUType ty
      checkSigma rhs ty'
  var <- emitDecl (getNameHint p) letAnn $ Atom val
  bindLamPat p var cont
inferUDeclLocal (UInstance ~(InternalName className) argBinders params methods maybeName) cont = do
  className' <- substM className
  instanceDict <- checkInstanceArgs argBinders do
                    checkInstanceParams params \params' -> do
                      className'' <- sinkM className'
                      checkInstanceBody className'' params' methods
  case maybeName of
    RightB UnitB  -> do
      void $ emitDecl "instance" InstanceLet $ Atom instanceDict
      cont
    JustB instanceName -> do
      instanceVal <- emitDecl (getNameHint instanceName) PlainLet (Atom instanceDict)
      extendSubst (instanceName @> instanceVal) cont
    _ -> error "impossible"
inferUDeclLocal _ _ = error "not a local decl"

inferUDeclTop :: (Mut o, TopInferer m) => UDecl i i' -> m i' o a -> m i o a
inferUDeclTop (UDataDefDecl def tc dcs) cont = do
  def' <- liftImmut $ liftInfererM $ solveLocal $ inferDataDef def
  defName <- emitDataDef def'
  tc' <- emitTyConName defName =<< tyConDefAsAtom defName
  dcs' <- forM [0..(nestLength dcs - 1)] \i ->
    emitDataConName defName i =<< dataConDefAsAtom defName i
  extendSubst (tc @> tc' <.> dcs @@> dcs') cont
inferUDeclTop (UInterface paramBs superclasses methodTys className methodNames) cont = do
  let classPrettyName   = fromString (pprint className) :: SourceName
  let methodPrettyNames = map fromString (nestToList pprint methodNames) :: [SourceName]
  classDef@(ClassDef _ _ dictDataDef) <-
    inferInterfaceDataDef classPrettyName methodPrettyNames paramBs superclasses methodTys
  className' <- emitClassDef classDef =<< tyConDefAsAtom dictDataDef
  mapM_ (emitSuperclass className') [0..(length superclasses - 1)]
  methodNames' <-
    forM (enumerate $ zip methodPrettyNames methodTys) \(i, (prettyName, ty)) -> do
      let UMethodType (Right explicits) _ = ty
      emitMethodType (getNameHint prettyName) className' explicits i
  extendSubst (className @> className' <.> methodNames @@> methodNames') cont
inferUDeclTop _ _ = error "not a top decl"

tyConDefAsAtom :: TopInferer m => DataDefName o -> m i o (Atom o)
tyConDefAsAtom defName = liftBuilder do
  defName' <- sinkM defName
  DataDef sourceName params _ <- lookupDataDef defName'
  buildPureNaryLam (EmptyAbs $ binderNestAsPiNest PlainArrow params) \params' -> do
    defName'' <- sinkM defName'
    return $ TypeCon sourceName defName'' $ Var <$> params'

dataConDefAsAtom :: TopInferer m => DataDefName o -> Int -> m i o (Atom o)
dataConDefAsAtom defName conIx = liftBuilder do
  DataDef _ tyParams conDefs <- lookupDataDef =<< sinkM defName
  let conDef = conDefs !! conIx
  buildPureNaryLam (EmptyAbs $ binderNestAsPiNest ImplicitArrow tyParams) \tyArgs -> do
    ab <- sinkM $ Abs tyParams conDef
    DataConDef conName (EmptyAbs conParams) <- applyNaryAbs ab tyArgs
    buildPureNaryLam (EmptyAbs $ binderNestAsPiNest PlainArrow conParams) \conArgs -> do
      ListE tyArgs' <- sinkM $ ListE tyArgs
      defName' <- sinkM defName
      return $ DataCon conName defName' (Var <$> tyArgs') conIx (Var <$> conArgs)

binderNestAsPiNest :: Arrow -> Nest Binder n l -> Nest PiBinder n l
binderNestAsPiNest arr = \case
  Empty             -> Empty
  Nest (b:>ty) rest -> Nest (PiBinder b ty arr) $ binderNestAsPiNest arr rest

inferDataDef :: (EmitsInf o, Inferer m) => UDataDef i -> m i o (DataDef o)
inferDataDef (UDataDef (tyConName, paramBs) dataCons) = do
  Abs paramBs' (ListE dataCons') <-
    withNestedUBinders paramBs \_ -> do
      dataCons' <- mapM inferDataCon dataCons
      return $ ListE dataCons'
  return $ DataDef tyConName paramBs' dataCons'

inferDataCon :: (EmitsInf o, Inferer m)
             => (SourceName, UDataDefTrail i) -> m i o (DataConDef o)
inferDataCon (sourceName, UDataDefTrail argBs) = do
  argBs' <- checkUBinders (EmptyAbs argBs)
  return $ DataConDef sourceName argBs'

inferInterfaceDataDef :: (Mut o, TopInferer m)
                      => SourceName -> [SourceName]
                      -> Nest (UAnnBinder AtomNameC) i i'
                      -> [UType i'] -> [UMethodType i']
                      -> m i o (ClassDef o)
inferInterfaceDataDef className methodNames paramBs superclasses methods = do
  dictDef <- liftImmut $ liftInfererM do
    paramBs' <- solveLocal $ checkUBinders $ EmptyAbs paramBs
    buildNewtype className paramBs' \params -> solveLocal do
      params' <- mapM sinkM params
      extendSubst (paramBs @@> params') do
        superclasses' <- mapM checkUType superclasses
        methodsTys'   <- mapM checkUType $ methods <&> \(UMethodType _ ty) -> ty
        return $ PairTy (ProdTy superclasses') (ProdTy methodsTys')
  defName <- emitDataDef dictDef
  return $ ClassDef className methodNames defName

withNestedUBinders
  :: (EmitsInf o, Inferer m, HasNamesE e, SubstE AtomSubstVal e, SinkableE e)
  => Nest (UAnnBinder AtomNameC) i i'
  -> (forall o'. (EmitsInf o', Ext o o') => [AtomName o'] -> m i' o' (e o'))
  -> m i o (Abs (Nest Binder) e o)
withNestedUBinders bs cont = case bs of
  Empty -> Abs Empty <$> cont []
  Nest b rest -> do
    Abs b' (Abs rest' body) <- withUBinder b \name -> do
      withNestedUBinders rest \names -> do
        name' <- sinkM name
        cont (name':names)
    return $ Abs (Nest b' rest') body

withUBinder :: (EmitsInf o, Inferer m, HasNamesE e, SubstE AtomSubstVal e, SinkableE e)
            => UAnnBinder AtomNameC i i'
            -> (forall o'. (EmitsInf o', Ext o o') => AtomName o' -> m i' o' (e o'))
            -> m i o (Abs Binder e o)
withUBinder (UAnnBinder b ann) cont = do
  ann' <- checkUType ann
  buildAbsInf (getNameHint b) ann' \name ->
    extendSubst (b @> name) $ cont name

checkUBinders :: (EmitsInf o, Inferer m)
              => EmptyAbs (Nest (UAnnBinder AtomNameC)) i
              -> m i o (EmptyAbs (Nest Binder) o)
checkUBinders (EmptyAbs bs) = withNestedUBinders bs \_ -> return UnitE
checkUBinders _ = error "impossible"

inferULam :: (EmitsBoth o, Inferer m) => EffectRow o -> ULamExpr i -> m i o (Atom o)
inferULam effs (ULamExpr arrow (UPatAnn p ann) body) = do
  argTy <- checkAnn ann
  buildLamInf (getNameHint p) arrow argTy (\_ -> sinkM effs) \v ->
    bindLamPat p v $ inferSigma body

checkULam :: (EmitsBoth o, Inferer m) => ULamExpr i -> PiType o -> m i o (Atom o)
checkULam (ULamExpr _ (UPatAnn p ann) body) piTy = do
  let argTy = piArgType piTy
  checkAnn ann >>= constrainEq argTy
  -- XXX: we're ignoring the ULam arrow here. Should we be checking that it's
  -- consistent with the arrow supplied by the pi type?
  buildLamInf (getNameHint p) (piArrow piTy) argTy
    (\v -> do
        piTy' <- sinkM piTy
        fst <$> instantiatePi piTy' (Var v) )
     \v -> bindLamPat p v do
        piTy' <- sinkM piTy
        (_, resultTy) <- instantiatePi piTy' (Var v)
        checkSigma body resultTy

checkInstanceArgs
  :: (EmitsBoth o, Inferer m)
  => Nest UPatAnnArrow i i'
  -> (forall o'. (EmitsBoth o', Ext o o') =>  m i' o' (Atom o'))
  -> m i o (Atom o)
checkInstanceArgs Empty cont = cont
checkInstanceArgs (Nest (UPatAnnArrow (UPatAnn p ann) arrow) rest) cont = do
  case arrow of
    ImplicitArrow -> return ()
    ClassArrow    -> return ()
    _ -> throw TypeErr $ "Not a valid arrow for an instance: " ++ pprint arrow
  checkAnnWithMissingDicts ann \ds getArgTy -> do
    introDicts ds $ do
      argTy <- getArgTy
      buildLamInf (getNameHint p) arrow argTy (const $ return Pure) \v -> do
        bindLamPat p v $
          checkInstanceArgs rest do
            cont

checkInstanceParams :: forall m i o. (EmitsBoth o, Inferer m)
                    => [UType i]
                    -> (forall o'. (EmitsBoth o', Ext o o') => [Type o'] -> m i o' (Atom o'))
                    -> m i o (Atom o)
checkInstanceParams params cont = go params []
  where
    go :: forall o'. (EmitsBoth o', Inferer m, Ext o o') => [UType i] -> [Type o'] -> m i o' (Atom o')
    go []    ptys = cont $ reverse ptys
    go (p:t) ptys = checkUTypeWithMissingDicts p \ds getParamType -> do
      introDicts ds do
        pty <- getParamType
        ListE ptys' <- sinkM $ ListE ptys
        go t (pty:ptys')

checkInstanceBody :: (EmitsBoth o, Inferer m)
                  => ClassName o
                  -> [Type o]
                  -> [UMethodDef i]
                  -> m i o (Atom o)
checkInstanceBody className params methods = do
  ClassDef _ methodNames defName <- getClassDef className
  def@(DataDef tcNameHint _ _) <- lookupDataDef defName
  Just dictTy <- fromNewtype <$> checkedApplyDataDefParams def params
  PairTy (ProdTy superclassTys) (ProdTy methodTys) <- return dictTy
  superclassDicts <- mapM trySynthDict superclassTys
  methodsChecked <- mapM (checkMethodDef className methodTys) methods
  let (idxs, methods') = unzip $ sortOn fst $ methodsChecked
  forM_ (repeated idxs) \i ->
    throw TypeErr $ "Duplicate method: " ++ pprint (methodNames!!i)
  forM_ ([0..(length methodTys - 1)] `listDiff` idxs) \i ->
    throw TypeErr $ "Missing method: " ++ pprint (methodNames!!i)
  let dataConNameHint = "Mk" <> tcNameHint
  return $ DataCon dataConNameHint defName params 0 [PairVal (ProdVal superclassDicts)
                                                          (ProdVal methods')]

introDicts :: forall m o. (EmitsBoth o, Solver m, InfBuilder m)
           => [Type o]
           -> (forall l. (EmitsBoth l, Ext o l) => m l (Atom l))
           -> m o (Atom o)
introDicts []    m = m
introDicts (h:t) m = buildLamInf "_autoq" ClassArrow h (const $ return Pure) \_ -> do
  ListE t' <- sinkM $ ListE t
  introDicts t' m

introDictTys :: forall m o. (EmitsInf o, Solver m, InfBuilder m)
             => [Type o]
             -> (forall l. (EmitsInf l, Ext o l) => m l (PiType l))
             -> m o (PiType o)
introDictTys []    m = m
introDictTys (h:t) m = buildPiInf "_autoq" ClassArrow h \_ -> do
  ListE t' <- sinkM $ ListE t
  (Pure,) . Pi <$> (introDictTys t' m)

checkMethodDef :: (EmitsBoth o, Inferer m)
               => ClassName o -> [Type o] -> UMethodDef i -> m i o (Int, Atom o)
checkMethodDef className methodTys (UMethodDef ~(InternalName v) rhs) = do
  MethodBinding className' i _ <- substM v >>= lookupEnv
  when (className /= className') $
    throw TypeErr $ pprint v ++ " is not a method of " ++ pprint className
  let methodTy = methodTys !! i
  rhs' <- checkSigma rhs methodTy
  return (i, rhs')

checkUEffRow :: (EmitsInf o, Inferer m) => UEffectRow i -> m i o (EffectRow o)
checkUEffRow (EffectRow effs t) = do
   effs' <- liftM S.fromList $ mapM checkUEff $ toList effs
   t' <- forM t \(InternalName v) -> do
            v' <- substM v
            constrainVarTy v' EffKind
            return v'
   return $ EffectRow effs' t'

checkUEff :: (EmitsInf o, Inferer m) => UEffect i -> m i o (Effect o)
checkUEff eff = case eff of
  RWSEffect rws (Just ~(InternalName region)) -> do
    region' <- substM region
    constrainVarTy region' TyKind
    return $ RWSEffect rws $ Just region'
  RWSEffect rws Nothing -> return $ RWSEffect rws Nothing
  ExceptionEffect -> return ExceptionEffect
  IOEffect        -> return IOEffect

constrainVarTy :: (EmitsInf o, Inferer m) => AtomName o -> Type o -> m i o ()
constrainVarTy v tyReq = do
  varTy <- getType $ Var v
  constrainEq tyReq varTy

data CaseAltIndex = ConAlt Int
                  | VariantAlt Label Int
                  | VariantTailAlt (LabeledItems ())
  deriving (Eq, Show)

checkCaseAlt :: (EmitsBoth o, Inferer m)
             => RhoType o -> Type o -> UAlt i -> m i o (IndexedAlt o)
checkCaseAlt reqTy scrutineeTy (UAlt pat body) = do
  alt <- checkCasePat pat scrutineeTy do
    reqTy' <- sinkM reqTy
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

checkCasePat :: (EmitsBoth o, Inferer m)
             => UPat i i'
             -> Type o
             -> (forall o'. (EmitsBoth o', Ext o o') => m i' o' (Atom o'))
             -> m i o (Alt o)
checkCasePat (WithSrcB pos pat) scrutineeTy cont = addSrcContext pos $ case pat of
  UPatCon ~(InternalName conName) ps -> do
    (dataDefName, con) <- substM conName >>= getDataCon
    DataDef sourceName paramBs cons <- lookupDataDef dataDefName
    DataConDef _ (EmptyAbs argBs) <- return $ cons !! con
    when (nestLength argBs /= nestLength ps) $ throw TypeErr $
      "Unexpected number of pattern binders. Expected " ++ show (nestLength argBs)
                                             ++ " got " ++ show (nestLength ps)
    (params, argBs') <- inferParams (Abs paramBs $ EmptyAbs argBs)
    constrainEq scrutineeTy $ TypeCon sourceName dataDefName params
    buildAltInf argBs' \args ->
      bindLamPats ps args $ cont
  UPatVariant labels label p -> do
    ty <- freshType TyKind
    prevTys <- mapM (const $ freshType TyKind) labels
    rest <- freshInferenceName LabeledRowKind
    let patTypes = prevTys <> labeledSingleton label ty
    let extPatTypes = Ext patTypes $ Just rest
    constrainEq scrutineeTy $ VariantTy extPatTypes
    buildUnaryAltInf ty \x ->
      bindLamPat p x cont
  UPatVariantLift labels p -> do
    prevTys <- mapM (const $ freshType TyKind) labels
    rest <- freshInferenceName LabeledRowKind
    let extPatTypes = Ext prevTys $ Just rest
    constrainEq scrutineeTy $ VariantTy extPatTypes
    let ty = VariantTy $ Ext NoLabeledItems $ Just rest
    buildUnaryAltInf ty \x ->
      bindLamPat p x cont
  _ -> throw TypeErr $ "Case patterns must start with a data constructor or variant pattern"

inferParams :: (EmitsBoth o, Inferer m, HasNamesE e, SinkableE e)
            => Abs (Nest Binder) e o -> m i o ([Type o], e o)
inferParams (Abs Empty body) = return ([], body)
inferParams (Abs (Nest (b:>ty) bs) body) = do
  x <- freshInferenceName ty
  rest <- applyAbs (Abs b (Abs bs body)) x
  (xs, body') <- inferParams rest
  return (Var x : xs, body')

bindLamPats :: (EmitsBoth o, Inferer m)
            => Nest UPat i i' -> [AtomName o] -> m i' o a -> m i o a
bindLamPats Empty [] cont = cont
bindLamPats (Nest p ps) (x:xs) cont = bindLamPat p x $ bindLamPats ps xs cont
bindLamPats _ _ _ = error "mismatched number of args"

bindLamPat :: (EmitsBoth o, Inferer m) => UPat i i' -> AtomName o -> m i' o a -> m i o a
bindLamPat (WithSrcB pos pat) v cont = addSrcContext pos $ case pat of
  UPatBinder b -> extendSubst (b @> v) cont
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
    (DataDef sourceName paramBs cons) <- lookupDataDef dataDefName
    case cons of
      [DataConDef _ (EmptyAbs argBs)] -> do
        when (nestLength argBs /= nestLength ps) $ throw TypeErr $
          "Unexpected number of pattern binders. Expected " ++ show (nestLength argBs)
                                                 ++ " got " ++ show (nestLength ps)
        (params, UnitE) <- inferParams (Abs paramBs UnitE)
        constrainVarTy v $ TypeCon sourceName dataDefName params
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

checkAnn :: (EmitsInf o, Inferer m) => Maybe (UType i) -> m i o (Type o)
checkAnn ann = case ann of
  Just ty -> checkUType ty
  Nothing -> freshType TyKind

checkAnnWithMissingDicts :: (EmitsInf o, Inferer m)
                         => Maybe (UType i)
                         -> ([IfaceType o] -> (forall o'. (EmitsInf o', Ext o o') => m i o' (Type o')) -> m i o a)
                         -> m i o a
checkAnnWithMissingDicts ann cont = case ann of
  Just ty -> checkUTypeWithMissingDicts ty cont
  Nothing -> cont [] (freshType TyKind)  -- Unannotated binders are never auto-quantified

checkUTypeWithMissingDicts :: (EmitsInf o, Inferer m)
                           => UType i
                           -> ([IfaceType o] -> (forall o'. (EmitsInf o', Ext o o') => m i o' (Type o')) -> m i o a)
                           -> m i o a
checkUTypeWithMissingDicts uty@(WithSrcE pos _) cont = do
  ListE unsolvedSubset <- liftImmut $ do
    -- We have to be careful not to emit inference vars out of the initial solve.
    -- The resulting type will never be used in downstream inference, so we can easily
    -- end up with fake ambiguous variables if they leak out.
    DistinctAbs frag unsolvedSubset' <- liftInfererM $ runLocalInfererM do
      (Abs decls result, unsolvedSubset) <- gatherUnsolvedInterfaces $
        buildDeclsInf $ withAllowedEffects Pure $ checkRho uty TyKind
      -- Note that even if the normalization succeeds here, we can't short-circuit
      -- rechecking the UType, because unsolvedSubset is only an approximation to
      -- the set of all constraints. We have to reverify it again!
      -- We could probably add a flag to RequiredIfaces that would indicate whether
      -- pruning has happened.
      --
      -- TODO: When we're gathering the constraints, we shouldn't treat the existence of
      -- unhoistable dicts as an irrecoverable failure. They might be derivable from the
      -- hoistable dicts (e.g. as in i:n=>(..i)=>Float). The failures are only irrecoverable
      -- when we stop doing auto quantification.
      (_, maybeUnsolved) <- cheapReduceWithDecls decls result
      case maybeUnsolved of
        Nothing       -> addSrcContext pos $ throw NotImplementedErr $
          "A type expression has interface constraints that depend on values " ++
          "local to the expression"
        Just unsolved -> ListE <$> nubAlphaEq (unsolvedSubset ++ unsolved)
    return $ case hoistRequiredIfaces frag (GatherRequired $ fromListE unsolvedSubset') of
      GatherRequired unsolvedSubset -> ListE unsolvedSubset
      FailIfRequired                -> error "Unreachable"
  cont unsolvedSubset $ checkUType uty

checkUType :: (EmitsInf o, Inferer m) => UType i -> m i o (Type o)
checkUType uty@(WithSrcE pos _) = do
  Abs decls result <- buildDeclsInf $ withAllowedEffects Pure $ checkRho uty TyKind
  (ans, unsolved)  <- cheapReduceWithDecls decls result
  case (ans, unsolved) of
    (_       , Nothing) -> addSrcContext pos $ throw NotImplementedErr $
      "A type expression has interface constraints that depend on values local to the expression"
    (Just ty , Just ds) -> addSrcContext pos (forM_ ds reportUnsolvedInterface) $> ty
    (Nothing , Just []) -> addSrcContext pos $ throw TypeErr $
      "Can't reduce type expression: " ++ pprint uty
    (Nothing , Just ds) -> do
      uniqDs <- nubAlphaEq ds
      throw TypeErr $
        "Can't reduce type expression: " ++ pprint uty ++ "\n" ++
        "This might be due to a failure to find a viable interface implementation " ++
        "for: " ++ intercalate ", " (pprint <$> uniqDs)

checkExtLabeledRow :: (EmitsBoth o, Inferer m)
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

inferTabCon :: (EmitsBoth o, Inferer m) => [UExpr i] -> RequiredTy RhoType o -> m i o (Atom o)
inferTabCon xs reqTy = do
  (tabTy, xs') <- case reqTy of
    Check tabTy@(TabTyAbs piTy) | null $ freeVarsE (piArgType piTy) -> do
      idx <- indices $ piArgType piTy
      -- TODO: Check length!!
      unless (length idx == length xs) $
        throw TypeErr "Table type doesn't match annotation"
      xs' <- forM (zip xs idx) \(x, i) -> do
        (_, xTy) <- instantiatePi piTy i
        checkOrInferRho x $ Check xTy
      return (tabTy, xs')
    _ -> do
      elemTy <- case xs of
        []    -> freshType TyKind
        (x:_) -> getType =<< inferRho x
      tabTy <- FixedIntRange 0 (fromIntegral $ length xs) ==> elemTy
      case reqTy of
        Check sTy -> addContext context $ constrainEq sTy tabTy
          where context = "If attempting to construct a fixed-size table not " <>
                          "indexed by 'Fin n' for some n, this error may " <>
                          "indicate there was not enough information to infer " <>
                          "a concrete index set; try adding an explicit " <>
                          "annotation."
        Infer       -> return ()
      xs' <- mapM (flip checkRho elemTy) xs
      return (tabTy, xs')
  liftM Var $ emit $ Op $ TabCon tabTy xs'

-- Bool flag is just to tweak the reported error message
fromPiType :: (EmitsBoth o, Inferer m) => Bool -> Arrow -> Type o -> m i o (PiType o)
fromPiType _ _ (Pi piTy) = return piTy -- TODO: check arrow
fromPiType expectPi arr ty = do
  a <- freshType TyKind
  b <- freshType TyKind
  piTy <- nonDepPiType arr a Pure b
  if expectPi then  constrainEq (Pi piTy) ty
              else  constrainEq ty (Pi piTy)
  return piTy

fromPairType :: (EmitsBoth o, Inferer m) => Type o -> m i o (Type o, Type o)
fromPairType (PairTy t1 t2) = return (t1, t2)
fromPairType ty = do
  a <- freshType TyKind
  b <- freshType TyKind
  constrainEq (PairTy a b) ty
  return (a, b)

addEffects :: (EmitsBoth o, Inferer m) => EffectRow o -> m i o ()
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

openEffectRow :: (EmitsBoth o, Inferer m) => EffectRow o -> m i o (EffectRow o)
openEffectRow (EffectRow effs Nothing) = extendEffRow effs <$> freshEff
openEffectRow effRow = return effRow

-- === Solver ===

newtype SolverSubst n = SolverSubst (M.Map (AtomName n) (Type n))

instance Pretty (SolverSubst n) where
  pretty (SolverSubst m) = pretty $ M.toList m

class (CtxReader1 m, EnvReader m) => Solver (m::MonadKind1) where
  zonk :: (SubstE AtomSubstVal e, SinkableE e) => e n -> m n (e n)
  extendSolverSubst :: AtomName n -> Type n -> m n ()
  emitSolver :: EmitsInf n => SolverBinding n -> m n (AtomName n)
  addDefault :: Type n -> Type VoidS -> m n ()
  getDefaults :: m n (Defaults n)
  solveLocal :: (Immut n, SinkableE e, HoistableE e)
             => (forall l. (EmitsInf l, Ext n l, Distinct l) => m l (e l))
             -> m n (e n)

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
instance SinkableB SolverOutFrag

instance OutFrag SolverOutFrag where
  emptyOutFrag = SolverOutFrag Empty mempty emptySolverSubst
  catOutFrags scope (SolverOutFrag em ds ss) (SolverOutFrag em' ds' ss') =
    withExtEvidence em' $
      SolverOutFrag (em >>> em')
                    (sink ds <> ds')
                    (catSolverSubsts scope (sink ss) ss')

instance ExtOutMap InfOutMap SolverOutFrag where
  extendOutMap infOutMap outFrag =
    extendOutMap infOutMap $ liftSolverOutFrag outFrag

newtype SolverM (n::S) (a:: *) =
  SolverM { runSolverM' :: InplaceT SolverOutMap SolverOutFrag SearcherM n a }
  deriving (Functor, Applicative, Monad, MonadFail, Alternative, Searcher,
            ScopeReader, Fallible, CtxReader)

runSolverM :: Distinct n => Env n -> SolverM n a -> Except a
runSolverM bindings cont = do
  Immut <- return $ toImmutEvidence bindings
  maybeResult <- runSearcherM $ runInplaceT (initInfOutMap bindings) $
                   runSolverM' $ cont
  case maybeResult of
    Nothing -> throw TypeErr "No solution"
    Just (_, result) -> return result

instance EnvReader SolverM where
  getEnv = SolverM do
    InfOutMap bindings _ _ _ <- getOutMapInplaceT
    return bindings

instance Solver SolverM where
  extendSolverSubst v ty = SolverM $
    void $ extendTrivialInplaceT $
      SolverOutFrag Empty mempty (singletonSolverSubst v ty)

  zonk e = SolverM $ liftImmut do
    Distinct <- getDistinct
    solverOutMap <- getOutMapInplaceT
    return $ zonkWithOutMap solverOutMap $ sink e

  emitSolver binding = SolverM $
    emitInplaceT "?" binding \b binding' ->
      SolverOutFrag (Nest (b:>binding') Empty) mempty emptySolverSubst

  addDefault t1 t2 = SolverM $
    extendTrivialInplaceT $ SolverOutFrag Empty defaults emptySolverSubst
    where defaults = Defaults [(t1, t2)]

  getDefaults = SolverM $ liftImmut do
    (InfOutMap _ _ defaults _) <- getOutMapInplaceT
    return defaults

  solveLocal cont = SolverM do
    results <- locallyMutableInplaceT do
      Distinct <- getDistinct
      EmitsInf <- fabricateEmitsInfEvidenceM
      runSolverM' cont
    DistinctAbs (SolverOutFrag unsolvedInfNames _ _) result <- return results
    case hoist unsolvedInfNames result of
      HoistSuccess result' -> return result'
      HoistFailure vs -> throw TypeErr $ "Ambiguous type variables: " ++ pprint vs

instance Unifier SolverM

freshInferenceName :: (EmitsInf n, Solver m) => Kind n -> m n (AtomName n)
freshInferenceName k = do
  ctx <- srcPosCtx <$> getErrCtx
  emitSolver $ InfVarBound k ctx

freshSkolemName :: (EmitsInf n, Solver m) => Kind n -> m n (AtomName n)
freshSkolemName k = emitSolver $ SkolemBound k

type Solver2 (m::MonadKind2) = forall i. Solver (m i)

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
zonkWithOutMap (InfOutMap bindings solverSubst _ _) e =
  applySolverSubstE (toScope bindings) solverSubst e

_applySolverSubstB :: (SubstB (SubstVal AtomNameC Atom) b, Distinct l)
                   => Scope n -> SolverSubst n -> b n l -> b n l
_applySolverSubstB scope solverSubst e = substBDistinct (scope, env) e
  where env = newSubst $ lookupSolverSubst solverSubst

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

instance SinkableE SolverSubst where
instance SubstE Name SolverSubst where
instance HoistableE SolverSubst

constrainEq :: (EmitsInf o, Inferer m) => Type o -> Type o -> m i o ()
constrainEq t1 t2 = do
  t1' <- zonk t1
  t2' <- zonk t2
  Abs infVars (PairE t1Pretty t2Pretty) <- renameForPrinting $ PairE t1' t2'
  let msg =   "Expected: " ++ pprint t1Pretty
         ++ "\n  Actual: " ++ pprint t2Pretty
         ++ (case infVars of
               Empty -> ""
               _ -> "\n(Solving for: " ++ pprint (nestToList pprint infVars) ++ ")")
  void $ addContext msg $ liftSolverM $ unify t1' t2'

class (Alternative1 m, Searcher1 m, Fallible1 m, Solver m) => Unifier m

class (AlphaEqE e, SinkableE e, SubstE AtomSubstVal e) => Unifiable (e::E) where
  unifyZonked :: (EmitsInf n, Unifier m) => e n -> e n -> m n ()

tryConstrainEq :: (EmitsInf o, Inferer m) => Type o -> Type o -> m i o ()
tryConstrainEq t1 t2 = do
  constrainEq t1 t2 `catchErr` \errs -> case errs of
    Errs [Err TypeErr _ _] -> return ()
    _ -> throwErrs errs

unify :: (EmitsInf n, Unifier m, Unifiable e) => e n -> e n -> m n ()
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

     unifyZip :: (EmitsInf n, Unifier m) => Type n -> Type n -> m n ()
     unifyZip t1 t2 = case (t1, t2) of
       (Pi piTy, Pi piTy') -> unifyPiType piTy piTy'
       (RecordTy  xs, RecordTy  xs') -> unify (ExtLabeledItemsE xs) (ExtLabeledItemsE xs')
       (VariantTy xs, VariantTy xs') -> unify (ExtLabeledItemsE xs) (ExtLabeledItemsE xs')
       (TypeCon _ c xs, TypeCon _ c' xs') ->
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
     unifyDirect :: (EmitsInf n, Unifier m) => EffectRow n -> EffectRow n -> m n ()
     unifyDirect r (EffectRow effs (Just v)) | S.null effs = extendSolution v (Eff r)
     unifyDirect _ _ = empty

     unifyZip :: (EmitsInf n, Unifier m) => EffectRow n -> EffectRow n -> m n ()
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
     unifyDirect :: (EmitsInf n, Unifier m)
                 => ExtLabeledItemsE Type AtomName n
                 -> ExtLabeledItemsE Type AtomName n -> m n ()
     unifyDirect (ExtLabeledItemsE r) (ExtLabeledItemsE (Ext NoLabeledItems (Just v))) =
       extendSolution v (LabeledRow r)
     unifyDirect _ _ = empty

     unifyZip :: (EmitsInf n, Unifier m)
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

unifyFoldable
  :: (Eq (f ()), Functor f, Foldable f, Unifiable e, Unifier m, EmitsInf n)
  => f (e n) -> f (e n) -> m n ()
unifyFoldable xs ys = do
  unless (void xs == void ys) empty
  zipWithM_ unify (toList xs) (toList ys)

unifyEq :: (AlphaEqE e, Unifier m) => e n -> e n -> m n ()
unifyEq e1 e2 = do
  eq <- alphaEq e1 e2
  unless eq empty

unifyPiType :: (EmitsInf n, Unifier m) => PiType n -> PiType n -> m n ()
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

isInferenceName :: EnvReader m => AtomName n -> m n Bool
isInferenceName v = lookupEnv v >>= \case
  AtomNameBinding (SolverBound (InfVarBound _ _)) -> return True
  _ -> return False

isSkolemName :: EnvReader m => AtomName n -> m n Bool
isSkolemName v = lookupEnv v >>= \case
  AtomNameBinding (SolverBound (SkolemBound _)) -> return True
  _ -> return False

freshType :: (EmitsInf n, Solver m) => Kind n -> m n (Type n)
freshType k = Var <$> freshInferenceName k

freshEff :: (EmitsInf n, Solver m) => m n (EffectRow n)
freshEff = EffectRow mempty . Just <$> freshInferenceName EffKind

renameForPrinting :: (EnvReader m, HoistableE e, SinkableE e, SubstE Name e)
                  => e n -> m n (Abs (Nest (NameBinder AtomNameC)) e n)
renameForPrinting e = liftImmut do
  e' <- sinkM e
  DB bindings <- getDB
  return $ renameForPrinting' bindings e'

renameForPrinting' :: (Distinct n, HoistableE e, SinkableE e, SubstE Name e)
                   => Env n -> e n -> Abs (Nest (NameBinder AtomNameC)) e n
renameForPrinting' bindings e = do
  let infVars = filter (isInferenceVar bindings) $ freeVarsList AtomNameRep e
  let ab = abstractFreeVarsNoAnn infVars e
  let scope = toScope bindings
  let hints = take (length infVars) $ map fromString $
                map (:[]) ['a'..'z'] ++ map show [(0::Int)..]
  withManyFresh hints AtomNameRep scope \bs' ->
    runScopeReaderM (scope `extendOutMap` toScopeFrag bs') do
      ab' <- sinkM ab
      e' <- applyNaryAbs ab' $ nestToList (sink . nameBinderName) bs'
      return $ Abs bs' e'

-- === dictionary synthesis ===

-- main entrypoint to dictionary synthesizer
trySynthDict :: (Emits n, Builder m, Fallible1 m, EnvExtender m, EnvReader m)
             => Type n -> m n (Atom n)
trySynthDict ty = trySynthDictBlock ty >>= emitBlock

trySynthDictBlock :: (Fallible1 m, EnvReader m) => Type n -> m n (Block n)
trySynthDictBlock ty = liftImmut do
  DB bindings <- getDB
  ty' <- sinkM ty
  if hasInferenceVars bindings ty'
    then
      throw TypeErr "Can't synthesize a dictionary for a type with inference vars"
    else do
      let solutions = runSyntherM bindings $ buildBlock do
                        ty'' <- sinkM ty'
                        synthDict ty''
      let solutionsInstance = filter ((== UsedInstance) . snd) solutions
      unless (length solutionsInstance <= 1) $
        throw TypeErr $ "Multiple candidate class dictionaries for: " ++ pprint ty
      case solutions of
        [] -> throw TypeErr $ "Couldn't synthesize a class dictionary for: " ++ pprint ty
        (d, _):_ -> return d

-- TODO: we'd rather have something like this:
--   data Givens n = Givens (M.Map (Type n) (Given n))
-- but we need an Ord or Hashable instance on types
data Givens n = Givens [Type n] [Given n]

type Given = Block

data DerivationKind = OnlyGivens | UsedInstance deriving Eq

instance Semigroup DerivationKind where
  OnlyGivens <> OnlyGivens = OnlyGivens
  _          <> _          = UsedInstance
instance Monoid DerivationKind where
  mempty = OnlyGivens

class (Alternative1 m, Searcher1 m, Builder m)
      => Synther m where
  getGivens :: m n (Givens n)
  withGivens :: Givens n -> m n a -> m n a
  declareUsedInstance :: m n ()

newtype SyntherM (n::S) (a:: *) = SyntherM
  { runSyntherM' :: OutReaderT Givens (BuilderT (WriterT DerivationKind [])) n a }
  deriving ( Functor, Applicative, Monad, EnvReader, EnvExtender
           , ScopeReader, MonadFail, Fallible
           , Alternative, Searcher, OutReader Givens)

instance Synther SyntherM where
  getGivens = askOutReader

  declareUsedInstance = SyntherM $ tell UsedInstance

  withGivens givens cont = do
    localOutReader givens cont

instance Builder SyntherM where
  emitDecl hint ann expr = SyntherM $ emitDecl hint ann expr
  buildScoped cont = SyntherM $ buildScoped $ runSyntherM' cont

runSyntherM :: Distinct n
            => Env n
            -> SyntherM n a
            -> [(a, DerivationKind)]
runSyntherM bindings cont = do
  runWriterT $ runBuilderT bindings do
    initGivens <- givensFromEnv
    runOutReaderT initGivens $ runSyntherM' cont

givensFromEnv :: EnvReader m => m n (Givens n)
givensFromEnv = liftImmut do
  DB bindings <- getDB
  let (SynthCandidates givens projs _) = getSynthCandidates bindings
  let givensBlocks = map AtomicBlock givens
  return $ getSuperclassClosure bindings projs (Givens [] []) givensBlocks

extendGivens :: Synther m => [Given n] -> m n a -> m n a
extendGivens newGivens cont = do
  prevGivens <- getGivens
  projs <- superclassGetters <$> getSynthCandidatesM
  finalGivens <- getSuperclassClosureM projs prevGivens newGivens
  withGivens finalGivens cont

getSuperclassClosureM
  :: EnvReader m
  => [Atom n] -> Givens n -> [Given n] -> m n (Givens n)
getSuperclassClosureM projs givens newGivens =  liftImmut do
  DB bindings <- getDB
  givens' <- sinkM givens
  ListE projs'     <- sinkM $ ListE projs
  ListE newGivens' <- sinkM $ ListE newGivens
  return $ getSuperclassClosure bindings projs' givens' newGivens'

getSuperclassClosure
  :: forall n. Distinct n
  => Env n -> [Atom n] -> Givens n -> [Given n] -> Givens n
getSuperclassClosure bindings projs givens newGivens =
  execState (mapM_ visitGiven newGivens) givens
  where
    visitGiven :: Given n -> State (Givens n) ()
    visitGiven x = alreadyVisited x >>= \case
      True -> return ()
      False -> do
        markAsVisited x
        forM_ projs \proj ->
          case tryApply bindings proj x of
            Just parent -> visitGiven parent
            Nothing -> return ()

    alreadyVisited :: Given n -> State (Givens n) Bool
    alreadyVisited x = do
      Givens tys _ <- get
      return $ runEnvReaderM bindings do
        ty <- getType x
        ty `alphaElem` tys

    markAsVisited :: Given n -> State (Givens n) ()
    markAsVisited x = do
      let ty = runEnvReaderM bindings $ getType x
      modify \(Givens tys xs) -> Givens (ty:tys) (x:xs)

tryApply :: Distinct n => Env n -> Atom n -> Given n -> Maybe (Given n)
tryApply bindings proj dict = do
  runBuilderT bindings do
    Distinct <- getDistinct
    tryApplyM (sink proj) (sink dict)

tryApplyM :: (MonadFail1 m, Builder m)
          => Atom n -> Given n -> m n (Given n)
tryApplyM proj dict = do
  dictTy <- getType dict
  projTy <- getType proj
  instantiateProjParams projTy dictTy >>= \case
    NothingE -> fail "couldn't instantiate params"
    JustE (ListE params) -> buildBlock do
      Distinct <- getDistinct
      instantiated <- naryApp (sink proj) (map sink params)
      dictAtom <- emitBlock $ sink dict
      app instantiated dictAtom
    _ -> error "impossible"

instantiateProjParams :: EnvReader m => Type n -> Type n
                      -> m n (MaybeE (ListE Atom) n)
instantiateProjParams projTy dictTy = liftImmut do
  DB bindings <- getDB
  PairE projTy' dictTy' <- sinkM $ PairE projTy dictTy
  let result = runSolverM bindings $ solveLocal do
                 params <- instantiateProjParamsM (sink projTy') (sink dictTy')
                 zonk $ ListE params
  case result of
    Success params -> return $ JustE $ params
    Failure _ -> return NothingE

instantiateProjParamsM :: (EmitsInf n, Unifier m) => Type n -> Type n -> m n [Atom n]
instantiateProjParamsM projTy dictTy = case projTy of
  Pi (PiType (PiBinder b argTy ImplicitArrow) _ resultTy) -> do
    param <- freshInferenceName argTy
    resultTy' <- applyAbs (Abs b resultTy) param
    params <- instantiateProjParamsM resultTy' dictTy
    return $ Var param : params
  Pi (PiType (PiBinder _ argTy PlainArrow) _ _) -> do
    unify dictTy argTy
    return []
  _ -> error $ "unexpected projection type: " ++ pprint projTy

getGiven :: (Synther m, Emits n) => m n (Atom n)
getGiven = do
  Givens _ givens <- getGivens
  asum $ map emitBlock givens

getInstance :: DataDefName n -> Synther m => m n (Atom n)
getInstance target = do
  instances <- instanceDicts <$> getSynthCandidatesM
  case M.lookup target instances of
    Just relevantInstances -> do
      declareUsedInstance
      asum $ map pure relevantInstances
    Nothing -> empty

synthDict :: (Emits n, Synther m) => Type n -> m n (Atom n)
synthDict (Pi piTy@(PiType (PiBinder b argTy arr) Pure _)) =
  buildPureLam (getNameHint b) arr argTy \v -> do
    piTy' <- sinkM piTy
    (_, resultTy) <- instantiatePi piTy' $ Var v
    newGivens <- case arr of
      ClassArrow -> return [AtomicBlock $ Var v]
      _ -> return []
    extendGivens newGivens $ synthDict resultTy
synthDict ty@(TypeCon _ dataDef _) = do
  polyDict <- getGiven <|> getInstance dataDef
  ty' <- sinkM ty
  polyTy <- getType polyDict
  PairE (ListE params) (ListE reqDictTys) <- instantiateDictParams ty' polyTy
  reqDicts <- mapM synthDict reqDictTys
  naryApp polyDict $ params ++ reqDicts
synthDict ty = error $ "Not a valid dictionary type: " ++ pprint ty

instantiateDictParams :: (Fallible1 m, EnvReader m)
                      => Type n -> Type n -> m n (PairE (ListE Atom) (ListE Type) n)
instantiateDictParams monoTy polyTy = liftImmut do
  DB bindings <- getDB
  liftExcept $ runSolverM bindings $ solveLocal do
    monoTy' <- sinkM monoTy
    polyTy' <- sinkM polyTy
    (params, tys) <- instantiateDictParamsRec monoTy' polyTy'
    zonk $ PairE (ListE params) (ListE tys)

instantiateDictParamsRec :: (EmitsInf n, Unifier m)
                         => Type n -> Type n -> m n ([Atom n], [Type n])
instantiateDictParamsRec monoTy polyTy = case polyTy of
  Pi (PiType (PiBinder b argTy ImplicitArrow) _ resultTy) -> do
    param <- freshInferenceName argTy
    resultTy' <- applyAbs (Abs b resultTy) param
    (params, dictTys) <- instantiateDictParamsRec monoTy resultTy'
    return (Var param : params, dictTys)
  Pi (PiType (PiBinder b dictTy ClassArrow) _ resultTy) -> do
    case fromConstAbs (Abs b resultTy) of
      HoistSuccess resultTy' -> do
        (params, dictTys) <- instantiateDictParamsRec monoTy resultTy'
        case params of
          [] -> return ([], dictTy:dictTys)
          _ -> error "Not implemented: interleaved params and class constraints"
      HoistFailure _ -> error "shouldn't have dependent class arrow"
  _ -> do
    unify monoTy polyTy
    return ([], [])

instance GenericE Givens where
  type RepE Givens = PairE (ListE Type) (ListE Given)
  fromE (Givens tys givens) = PairE (ListE tys) (ListE givens)
  toE   (PairE (ListE tys) (ListE givens)) = Givens tys givens

instance SinkableE Givens where

-- === Dictionary synthesis traversal ===

synthModule :: Distinct n => Env n -> Module n -> Except (Module n)
synthModule bindings m = do
  Immut <- return $ toImmutEvidence bindings
  Module _ decls result <- runDictSynthTraverserM bindings $
                             traverseGenericE m
  return $ Module Core decls result

runDictSynthTraverserM
  :: Distinct n => Env n
  -> DictSynthTraverserM n n a
  -> Except a
runDictSynthTraverserM bindings m =
   runFallibleM $ runBuilderT bindings do
     runSubstReaderT idSubst $ runDictSynthTraverserM' m

newtype DictSynthTraverserM (i::S) (o::S) (a:: *) =
  DictSynthTraverserM
    { runDictSynthTraverserM' :: SubstReaderT Name (BuilderT FallibleM) i o a }
    deriving ( Functor, Applicative, Monad, SubstReader Name
             , EnvReader, ScopeReader, EnvExtender, MonadFail, Fallible)

instance GenericTraverser DictSynthTraverserM where
  traverseExpr (Op (SynthesizeDict ctx ty)) = do
    ty' <- substM ty
    addSrcContext ctx $ Atom <$> trySynthDict ty'
  traverseExpr expr = traverseExprDefault expr

-- TODO: need to figure out why this one isn't derivable
instance Builder (DictSynthTraverserM i) where
  emitDecl hint ann expr =
    DictSynthTraverserM $ emitDecl hint ann expr

  buildScoped cont =
    DictSynthTraverserM $ buildScoped $ runDictSynthTraverserM' cont

-- === Inference-specific builder patterns ===

-- The higher-order functions in Builder, like `buildLam` can't be easily used
-- in inference because they don't allow for the emission of inference
-- variables, which must be handled each time we leave a scope. In an earlier
-- version we tried to put this logic in the implementation of InfererM's
-- instance of Builder, but it forced us to overfit the Builder API to satisfy
-- the needs of inference, like adding `SubstE AtomSubstVal e` constraints in
-- various places.

buildBlockInf
  :: (EmitsInf n, Solver m, InfBuilder m)
  => (forall l. (EmitsBoth l, Ext n l) => m l (Atom l))
  -> m n (Block n)
buildBlockInf cont = do
  Abs decls (PairE result ty) <- buildDeclsInf do
    result <- cont
    ty <- getType result
    return $ result `PairE` ty
  ty' <- liftHoistExcept $ hoist decls ty
  return $ Block (BlockAnn ty') decls $ Atom result

buildLamInf
  :: (EmitsInf n, Solver m, InfBuilder m)
  => NameHint -> Arrow -> Type n
  -> (forall l. (EmitsInf  l, Ext n l) => AtomName l -> m l (EffectRow l))
  -> (forall l. (EmitsBoth l, Ext n l) => AtomName l -> m l (Atom l))
  -> m n (Atom n)
buildLamInf hint arr ty fEff fBody = do
  Abs (b:>_) (PairE effs body) <-
    buildAbsInf hint (LamBinding arr ty) \v -> do
      effs <- fEff v
      body <- withAllowedEffects effs $ buildBlockInf $ sinkM v >>= fBody
      return $ PairE effs body
  return $ Lam $ LamExpr (LamBinder b ty arr effs) body

buildPiInf
  :: (EmitsInf n, Solver m, InfBuilder m)
  => NameHint -> Arrow -> Type n
  -> (forall l. (EmitsInf l, Ext n l) => AtomName l -> m l (EffectRow l, Type l))
  -> m n (PiType n)
buildPiInf hint arr ty body = do
  Abs (b:>_) (PairE effs resultTy) <-
    buildAbsInf hint (PiBinding arr ty) \v ->
      withAllowedEffects Pure do
        (effs, resultTy) <- body v
        return $ PairE effs resultTy
  return $ PiType (PiBinder b ty arr) effs resultTy

buildUnaryAltInf
  :: (EmitsInf n, Solver m, InfBuilder m)
  => Type n
  -> (forall l. (EmitsBoth l, Ext n l) => AtomName l -> m l (Atom l))
  -> m n (Alt n)
buildUnaryAltInf ty body = do
  bs <- liftBuilder $ singletonBinderNest NoHint $ sink ty
  buildAltInf bs \[v] -> body v

buildAltInf
  :: (EmitsInf n, Solver m, InfBuilder m)
  => EmptyAbs (Nest Binder) n
  -> (forall l. (EmitsBoth l, Ext n l) => [AtomName l] -> m l (Atom l))
  -> m n (Alt n)
buildAltInf (Abs Empty UnitE) body =
  Abs Empty <$> buildBlockInf (body [])
buildAltInf (Abs (Nest (b:>ty) bs) UnitE) body = do
  Abs b' (Abs bs' body') <-
    buildAbsInf (getNameHint b) ty \v -> do
      ab <- sinkM $ Abs b (EmptyAbs bs)
      bs' <- applyAbs ab v
      buildAltInf bs' \vs -> do
        v' <- sinkM v
        body $ v' : vs
  return $ Abs (Nest b' bs') body'

-- === EmitsInf predicate ===

type EmitsBoth n = (EmitsInf n, Emits n)

class Mut n => EmitsInf (n::S)
data EmitsInfEvidence (n::S) where
  EmitsInf :: EmitsInf n => EmitsInfEvidence n
instance EmitsInf UnsafeS

fabricateEmitsInfEvidence :: forall n. EmitsInfEvidence n
fabricateEmitsInfEvidence =
  withEmitsInfEvidence (error "pure fabrication" :: EmitsInfEvidence n) EmitsInf

fabricateEmitsInfEvidenceM :: forall m n. Monad1 m => m n (EmitsInfEvidence n)
fabricateEmitsInfEvidenceM = return fabricateEmitsInfEvidence

withEmitsInfEvidence :: forall n a. EmitsInfEvidence n -> (EmitsInf n => a) -> a
withEmitsInfEvidence _ cont = fromWrapWithEmitsInf
 ( TrulyUnsafe.unsafeCoerce ( WrapWithEmitsInf cont :: WrapWithEmitsInf n       a
                                                  ) :: WrapWithEmitsInf UnsafeS a)
newtype WrapWithEmitsInf n r =
  WrapWithEmitsInf { fromWrapWithEmitsInf :: EmitsInf n => r }
