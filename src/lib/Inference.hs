-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module Inference
  ( inferTopUDecl, checkTopUType, inferTopUExpr, applyUDeclAbs
  , trySynthTerm
  , synthTopBlock, UDeclInferenceResult (..), synthIx ) where

import Prelude hiding ((.), id)
import Control.Category
import Control.Applicative
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Writer.Strict hiding (Alt)
import Control.Monad.Reader
import Data.Foldable (toList, asum)
import Data.Function ((&))
import Data.Functor (($>), (<&>))
import Data.List (sortOn, intercalate)
import Data.Maybe (fromJust)
import Data.Text.Prettyprint.Doc (Pretty (..))
import qualified Data.HashMap.Strict as HM
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Unsafe.Coerce as TrulyUnsafe
import GHC.Generics (Generic (..))

import Name
import Builder
import Syntax hiding (State)
import Type
import PPrint (pprintCanonicalized, prettyBlock)
import CheapReduction
import GenericTraversal
import MTL1
import Interpreter

import LabeledItems
import Err
import Util
import Core

-- === Top-level interface ===

checkTopUType :: (Fallible1 m, EnvReader m) => UType n -> m n (Type n)
checkTopUType ty = liftInfererM $ solveLocal $ withApplyDefaults $ checkUType ty
{-# SCC checkTopUType #-}

inferTopUExpr :: (Fallible1 m, EnvReader m) => UExpr n -> m n (Block n)
inferTopUExpr e = liftInfererM do
  solveLocal $ buildBlockInf $ withApplyDefaults $ inferSigma e
{-# SCC inferTopUExpr #-}

data UDeclInferenceResult e n =
   UDeclResultDone (e n)  -- used for UDataDefDecl, UInterface and UInstance
 | UDeclResultWorkRemaining (Block n) (Abs UDecl e n) -- used for ULet

inferTopUDecl :: (Mut n, Fallible1 m, TopBuilder m, SinkableE e, SubstE Name e)
              => UDecl n l -> e l -> m n (UDeclInferenceResult e n)
inferTopUDecl (UDataDefDecl def tc dcs) result = do
  PairE def' clsAbs <- liftInfererM $ solveLocal $ inferDataDef def
  defName <- emitDataDef def'
  tc' <- emitTyConName defName =<< tyConDefAsAtom defName (Just clsAbs)
  dcs' <- forM [0..(nestLength dcs - 1)] \i ->
    emitDataConName defName i =<< dataConDefAsAtom defName clsAbs i
  let subst = tc @> tc' <.> dcs @@> dcs'
  UDeclResultDone <$> applySubst subst result
inferTopUDecl (UInterface paramBs superclasses methodTys className methodNames) result = do
  let classSourceName = uBinderSourceName className
  let methodSourceNames = nestToList uBinderSourceName methodNames
  classDef <- liftInfererM $ inferClassDef classSourceName methodSourceNames
                                           paramBs superclasses methodTys
  className' <- emitClassDef classDef
  methodNames' <-
    forM (enumerate $ zip methodSourceNames methodTys) \(i, (prettyName, ty)) -> do
      let UMethodType (Right explicits) _ = ty
      emitMethod (getNameHint prettyName) className' explicits i
  let subst = className @> className' <.> methodNames @@> methodNames'
  UDeclResultDone <$> applySubst subst result
inferTopUDecl (UInstance className bs params methods maybeName) result = do
  let (InternalName _ className') = className
  -- XXX: we use `buildDeclsInf` even though we don't actually emit any decls
  -- here. The reason is that it does some DCE of inference vars for us. If we
  -- don't use it, we get spurious "Ambiguous type variable" errors. TODO: Fix
  -- this.
  Abs Empty ab <- liftInfererM $ solveLocal $ buildDeclsInf do
    checkInstanceArgs bs do
      checkInstanceParams params \params' -> do
        className'' <- sinkM className'
        body <- checkInstanceBody className'' params' methods
        return (ListE params' `PairE` body)
  Abs bs' (Abs dictBinders (ListE params' `PairE` body)) <- return ab
  let def = InstanceDef className' (bs' >>> dictBinders) params' body
  def' <- synthInstanceDef def
  instanceName <- emitInstanceDef def'
  UDeclResultDone <$> case maybeName of
    RightB UnitB  -> do
      -- only nameless instances become synthesis candidates
      addInstanceSynthCandidate className' instanceName
      return result
    JustB instanceName' -> do
      lam <- instanceFun instanceName
      instanceAtomName <- emitTopLet (getNameHint instanceName') PlainLet $ Atom lam
      applySubst (instanceName' @> instanceAtomName) result
    _ -> error "impossible"
inferTopUDecl decl@(ULet _ (UPatAnn p ann) rhs) result = do
  block <- liftInfererM $ solveLocal $ buildBlockInf do
    val <- checkMaybeAnnExpr ann rhs
    -- This is just for type checking. We don't actually generate
    -- pattern-matching code at the top level
    _ <- buildBlockInf do
      val' <- sinkM val
      v <- emitDecl noHint PlainLet $ Atom val'
      bindLamPat p v $ return UnitVal
    applyDefaults
    return val
  return $ UDeclResultWorkRemaining block $ Abs decl result
{-# SCC inferTopUDecl #-}

-- We use this to finish the processing the decl after we've completely
-- evaluated the right-hand side
applyUDeclAbs :: (Mut n, TopBuilder m, SinkableE e, SubstE Name e, MonadIO1 m)
              => Abs UDecl e n -> Atom n -> m n (e n)
applyUDeclAbs (Abs decl result) x = case decl of
  ULet letAnn (UPatAnn pat _) _ -> do
    v <- emitTopLet (getNameHint pat) letAnn (Atom x)
    case pat of
      WithSrcB _ (UPatBinder b) -> applySubst (b@>v) result
      _ -> do
        atomSubst <- liftInterpM do
          x' <- evalAtom (Var v)
          matchUPat pat x'
        nameSubst <- emitAtomSubstFrag atomSubst
        applySubst nameSubst result
  _ -> error "other top-level decls don't require any computation so we shouldn't get here"


emitAtomSubstFrag :: (Mut o, TopBuilder m)
                  => SubstFrag AtomSubstVal i i' o -> m o (SubstFrag Name i i' o)
emitAtomSubstFrag frag = go $ toSubstPairs frag
  where
    go :: (Mut o, TopBuilder m)
       => Nest (SubstPair AtomSubstVal o) i i' -> m o (SubstFrag Name i i' o)
    go Empty = return emptyInFrag
    go (Nest (SubstPair b val) rest) = do
      v <- case val of
        SubstVal x -> emitTopLet (getNameHint b) PlainLet (Atom x)
        Rename v -> return v
      (b@>v <.>) <$> go rest

-- === Inferer interface ===

class ( MonadFail1 m, Fallible1 m, Catchable1 m, CtxReader1 m
      , Builder m, ScopableBuilder m )
      => InfBuilder (m::MonadKind1) where

  -- XXX: we should almost always used the zonking `buildDeclsInf` and variant,
  -- except where it's not possible because the result isn't atom-substitutable,
  -- such as the source map at the top level.
  buildDeclsInfUnzonked
    :: (SinkableE e, HoistableE e, SubstE Name e)
    => EmitsInf n
    => (forall l. (EmitsBoth l, DExt n l) => m l (e l))
    -> m n (Abs (Nest Decl) e n)

  buildAbsInf
    :: (SinkableE e, HoistableE e, SubstE Name e, Color c, ToBinding binding c)
    => EmitsInf n
    => NameHint -> binding n
    -> (forall l. (EmitsInf l, DExt n l) => Name c l -> m l (e l))
    -> m n (Abs (BinderP c binding) e n)

buildDeclsInf
  :: (SubstE AtomSubstVal e, SubstE Name e, Solver m, InfBuilder m)
  => (SinkableE e, HoistableE e)
  => EmitsInf n
  => (forall l. (EmitsBoth l, DExt n l) => m l (e l))
  -> m n (Abs (Nest Decl) e n)
buildDeclsInf cont = buildDeclsInfUnzonked $ cont >>= zonk

type InfBuilder2 (m::MonadKind2) = forall i. InfBuilder (m i)

type IfaceTypeSet = ESet Type

class (SubstReader Name m, InfBuilder2 m, Solver2 m)
      => Inferer (m::MonadKind2) where
  liftSolverMInf :: EmitsInf o => SolverM o a -> m i o a
  gatherUnsolvedInterfaces :: m i o a -> m i o (a, IfaceTypeSet o)
  reportUnsolvedInterface  :: Type o  -> m i o ()
  addDefault :: Type o -> Type VoidS -> m i o ()
  getDefaults :: m i o (Defaults o)

applyDefaults :: EmitsInf o => InfererM i o ()
applyDefaults = do
  Defaults defaults <- getDefaults
  forM_ defaults \(ty, ty') ->
    tryConstrainEq ty (sinkFromTop ty')

withApplyDefaults :: EmitsInf o => InfererM i o a -> InfererM i o a
withApplyDefaults cont = cont <* applyDefaults
{-# INLINE withApplyDefaults #-}

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
  {-# INLINE fromE #-}
  toE (ListE xys) = Defaults [(x, y) | PairE x (LiftE y) <- xys]
  {-# INLINE toE #-}

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
getAtomNames frag = S.fromList $ nameSetToList $ toNameSet $ toScopeFrag frag

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
zonkUnsolvedEnv ss un env | substIsEmpty ss = (un, env)
zonkUnsolvedEnv ss unsolved env =
  flip runState env $ execWriterT do
    forM_ (S.toList $ fromUnsolvedEnv unsolved) \v -> do
      flip lookupEnvPure v <$> get >>= \case
        AtomNameBinding rhs -> do
          let rhs' = zonkWithOutMap (InfOutMap env ss mempty mempty) rhs
          modify $ updateEnv v $ AtomNameBinding rhs'
          let rhsHasInfVars = runEnvReaderM env $ hasInferenceVars rhs'
          when rhsHasInfVars $ tell $ UnsolvedEnv $ S.singleton v

hasInferenceVars :: (EnvReader m, HoistableE e) => e n -> m n Bool
hasInferenceVars e = anyM isInferenceVar $ freeAtomVarsList e

isInferenceVar :: EnvReader m => AtomName n -> m n Bool
isInferenceVar v = lookupEnv v >>= \case
  AtomNameBinding (SolverBound _) -> return True
  _                               -> return False

instance ExtOutMap InfOutMap InfOutFrag where
  extendOutMap infOutMap (InfOutFrag em ds solverSubst) =
    extendDefaults ds $
      flip extendInfOutMapSolver solverSubst $
        flip extendOutMap (toEnvFrag em) $
          infOutMap

extendDefaults :: Defaults n -> InfOutMap n -> InfOutMap n
extendDefaults ds' (InfOutMap bindings ss ds un) =
  InfOutMap bindings ss (ds <> ds') un

-- TODO: Make GatherRequired hold a set
data RequiredIfaces (n::S) = FailIfRequired | GatherRequired (IfaceTypeSet n)
instance GenericE RequiredIfaces where
  type RepE RequiredIfaces = MaybeE IfaceTypeSet
  fromE = \case
    FailIfRequired    -> NothingE
    GatherRequired ds -> JustE ds
  {-# INLINE fromE #-}
  toE = \case
    NothingE  -> FailIfRequired
    JustE ds  -> GatherRequired ds
    _ -> error "unreachable"
  {-# INLINE toE #-}
instance SinkableE RequiredIfaces
instance SubstE Name RequiredIfaces
instance HoistableE  RequiredIfaces

newtype InfererM (i::S) (o::S) (a:: *) = InfererM
  { runInfererM' :: SubstReaderT Name (StateT1 RequiredIfaces (InplaceT InfOutMap InfOutFrag FallibleM)) i o a }
  deriving (Functor, Applicative, Monad, MonadFail, MonadState (RequiredIfaces o),
            ScopeReader, Fallible, Catchable, CtxReader, SubstReader Name)

liftInfererMSubst :: (Fallible2 m, SubstReader Name m, EnvReader2 m)
                  => InfererM i o a -> m i o a
liftInfererMSubst cont = do
  env <- unsafeGetEnv
  subst <- getSubst
  Distinct <- getDistinct
  (InfOutFrag Empty _ _, (result, _)) <-
    liftExcept $ runFallibleM $ runInplaceT (initInfOutMap env) $
      runStateT1 (runSubstReaderT subst $ runInfererM' $ cont) FailIfRequired
  return result

liftInfererM :: (EnvReader m, Fallible1 m)
             => InfererM n n a -> m n a
liftInfererM cont = runSubstReaderT idSubst $ liftInfererMSubst $ cont
{-# INLINE liftInfererM #-}

runLocalInfererM
  :: SinkableE e
  => (forall l. (EmitsInf l, DExt n l) => InfererM i l (e l))
  -> InfererM i n (Abs InfOutFrag e n)
runLocalInfererM cont = InfererM $ SubstReaderT $ ReaderT \env -> StateT1 \s -> do
  Abs fg (PairE ans s') <- locallyMutableInplaceT do
    Distinct <- getDistinct
    EmitsInf <- fabricateEmitsInfEvidenceM
    toPairE <$> (runStateT1 (runSubstReaderT (sink env) $ runInfererM' cont) (sink s))
  return (Abs fg ans, hoistRequiredIfaces fg s')
{-# INLINE runLocalInfererM #-}

initInfOutMap :: Env n -> InfOutMap n
initInfOutMap bindings =
  InfOutMap bindings emptySolverSubst mempty (UnsolvedEnv mempty)

emitInfererM :: Mut o => NameHint -> InfEmission o -> InfererM i o (AtomName o)
emitInfererM hint emission = do
  Abs b v <- freshNameM hint
  let frag = InfOutFrag (Nest (b :> emission) Empty) mempty emptySolverSubst
  InfererM $ SubstReaderT $ lift $ lift11 $ extendInplaceT $ Abs frag v
{-# INLINE emitInfererM #-}

instance Solver (InfererM i) where
  extendSolverSubst v ty = do
   InfererM $ SubstReaderT $ lift $ lift11 $
    void $ extendTrivialInplaceT $
      InfOutFrag Empty mempty (singletonSolverSubst v ty)
  {-# INLINE extendSolverSubst #-}

  zonk e = InfererM $ SubstReaderT $ lift $ lift11 do
    Distinct <- getDistinct
    solverOutMap <- getOutMapInplaceT
    return $ zonkWithOutMap solverOutMap e
  {-# INLINE zonk #-}

  emitSolver binding = emitInfererM (getNameHint @String "?") $ RightE binding
  {-# INLINE emitSolver #-}

  solveLocal cont = do
    Abs (InfOutFrag unsolvedInfNames _ _) result <- runLocalInfererM cont
    case unsolvedInfNames of
      Empty -> return result
      Nest (_:>RightE (InfVarBound _ ctx)) _ -> do
        addSrcContext ctx $ throw TypeErr $ "Ambiguous type variable"
      _ -> error "not possible?"

instance InfBuilder (InfererM i) where
  buildDeclsInfUnzonked cont = do
    InfererM $ SubstReaderT $ ReaderT \env -> StateT1 \s -> do
      Abs frag resultWithState <- locallyMutableInplaceT do
        Emits    <- fabricateEmitsEvidenceM
        EmitsInf <- fabricateEmitsInfEvidenceM
        toPairE <$> runStateT1 (runSubstReaderT (sink env) $ runInfererM' cont) (sink s)
      ab <- hoistThroughDecls frag resultWithState
      Abs decls (PairE result s') <- extendInplaceT ab
      return (Abs decls result, hoistRequiredIfaces decls s')

  buildAbsInf hint binding cont = do
    InfererM $ SubstReaderT $ ReaderT \env -> StateT1 \s -> do
      ab <- withFreshBinder hint binding \b -> do
        ab <- locallyMutableInplaceT do
          EmitsInf <- fabricateEmitsInfEvidenceM
          toPairE <$> runStateT1 (
            runSubstReaderT (sink env) (runInfererM' $ cont $ sink $ binderName b)) (sink s)
        refreshAbs ab \infFrag resultWithState -> do
          PairB infFrag' b' <- liftHoistExcept $ exchangeBs $ PairB b infFrag
          return $ withSubscopeDistinct b' $ Abs infFrag' $ Abs b' resultWithState
      Abs b (PairE result s') <- extendInplaceT ab
      return (Abs (b:>binding) result, hoistRequiredIfaces b s')

instance Inferer InfererM where
  liftSolverMInf m = InfererM $ SubstReaderT $ lift $ lift11 $
    liftBetweenInplaceTs (liftExcept . liftM fromJust . runSearcherM) id liftSolverOutFrag $
      runSolverM' m
  {-# INLINE liftSolverMInf #-}

  addDefault t1 t2 = InfererM $ SubstReaderT $ lift $ lift11 $
    extendTrivialInplaceT $ InfOutFrag Empty defaults emptySolverSubst
    where defaults = Defaults [(t1, t2)]

  getDefaults = InfererM $ SubstReaderT $ lift $ lift11 do
    InfOutMap _ _ defaults _ <- getOutMapInplaceT
    return defaults

  gatherUnsolvedInterfaces m = do
    s' <- get
    put $ GatherRequired mempty
    ans <- m
    ds <- get
    put s'
    case ds of
      FailIfRequired     -> throw CompilerErr "Unexpected FailIfRequired?"
      GatherRequired ds' -> return (ans, ds')

  reportUnsolvedInterface iface = do
    UnitE <- do
      iface' <- sinkM iface
      ifaceHasInfVars <- hasInferenceVars iface'
      when ifaceHasInfVars $ throw NotImplementedErr $
        "Type inference of this program requires delayed interface resolution"
      return UnitE
    get >>= \case
      FailIfRequired    -> throw TypeErr $ "Couldn't synthesize a class dictionary for: "
                             ++ pprintCanonicalized iface
      GatherRequired ds -> put $ GatherRequired $ eSetSingleton iface <> ds

instance Builder (InfererM i) where
  emitDecl hint ann expr = do
    -- This zonking, and the zonking of the bindings elsewhere, is only to
    -- prevent `getType` from failing. But maybe we should just catch the
    -- failure if it occurs and generate a fresh inference name for the type in
    -- that case?
    expr' <- zonk expr
    ty <- getType expr'
    emitInfererM hint $ LeftE $ DeclBinding ann ty expr'
  {-# INLINE emitDecl #-}

instance ScopableBuilder (InfererM i) where
  buildScoped cont = do
    InfererM $ SubstReaderT $ ReaderT \env -> StateT1 \s -> do
      resultWithEmissions <- locallyMutableInplaceT do
        Emits <- fabricateEmitsEvidenceM
        toPairE <$> runStateT1 (runSubstReaderT (sink env) $ runInfererM' cont) (sink s)
      Abs frag@(InfOutFrag emissions _ _) (PairE result s') <- return resultWithEmissions
      let decls = fmapNest (\(b:>LeftE rhs) -> Let b rhs) emissions
      return (Abs decls result, hoistRequiredIfaces frag s')

type InferenceNameBinders = Nest (BinderP AtomNameC SolverBinding)

-- When we finish building a block of decls we need to hoist the local solver
-- information into the outer scope. If the local solver state mentions local
-- variables which are about to go out of scope then we emit a "escaped scope"
-- error. To avoid false positives, we clean up as much dead (i.e. solved)
-- solver state as possible.
hoistThroughDecls
  :: ( SubstE Name e, HoistableE e
     , Fallible1 m, ScopeReader m, EnvExtender m, HoistableE e)
  => InfOutFrag n l
  ->   e l
  -> m n (Abs InfOutFrag (Abs (Nest Decl) e) n)
hoistThroughDecls outFrag result = do
  scope <- unsafeGetScope
  refreshAbs (Abs outFrag result) \outFrag' result' -> do
    hoistThroughDecls' scope outFrag' result'

hoistThroughDecls'
  :: (Fallible m, HoistableE e, Distinct l)
  => Scope n
  -> InfOutFrag n l
  ->   e l
  -> m (Abs InfOutFrag (Abs (Nest Decl) e) n)
hoistThroughDecls' scope (InfOutFrag emissions defaults subst) result = do
  withSubscopeDistinct emissions do
    HoistedSolverState infVars defaults' subst' decls result' <-
      hoistInfStateRec scope emissions defaults subst result
    let hoistedInfFrag = InfOutFrag (infNamesToEmissions infVars) defaults' subst'
    return $ Abs hoistedInfFrag $ Abs decls result'

data HoistedSolverState e n where
  HoistedSolverState
    :: (Distinct l1, Distinct l2, Distinct n)
    => InferenceNameBinders n l1
    ->   Defaults l1
    ->   SolverSubst l1
    ->   Nest Decl l1 l2
    ->     e l2
    -> HoistedSolverState e n

instance HoistableE e => HoistableE (HoistedSolverState e) where
  freeVarsE (HoistedSolverState infVars defaults subst decls result) =
    freeVarsE (Abs infVars (PairE (PairE defaults subst) (Abs decls result)))

dceIfSolved :: HoistableE e
            => NameBinder AtomNameC n l -> HoistedSolverState e l
            -> Maybe (HoistedSolverState e n)
dceIfSolved b (HoistedSolverState infVars defaults subst decls result) = do
  let v = withExtEvidence infVars $ sink $ binderName b
  case deleteFromSubst subst v of
    Just subst' ->
      -- do we need to zonk here? (if not, say why not)
      case hoist b (HoistedSolverState infVars defaults subst' decls result) of
        HoistSuccess hoisted -> Just hoisted
        HoistFailure err -> error $ "this shouldn't happen. Leaked var: " ++ pprint err
    Nothing -> Nothing

hoistInfStateRec :: (Fallible m, Distinct n, Distinct l, HoistableE e)
                 => Scope n
                 -> InfEmissions n l -> Defaults l -> SolverSubst l -> e l
                 -> m (HoistedSolverState e n)
hoistInfStateRec scope Empty defaults subst e = do
  let defaults' = applySolverSubstE scope subst defaults
  return $ HoistedSolverState Empty defaults' subst Empty e
hoistInfStateRec scope (Nest (b :> infEmission) rest) defaults subst e = do
  withSubscopeDistinct rest do
    solverState@(HoistedSolverState infVars defaults' subst' decls result) <-
       hoistInfStateRec (extendOutMap scope (toScopeFrag b)) rest defaults subst e
    case infEmission of
      RightE binding@(InfVarBound _ _) ->
        case dceIfSolved b solverState of
          Just solverState' -> return solverState'
          Nothing -> return $ HoistedSolverState (Nest (b:>binding) infVars)
                                                 defaults' subst' decls result
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
            return $ HoistedSolverState infVars' defaults'' subst''
                        (Nest (Let b' emission'') decls) result

hoistRequiredIfaces :: BindsNames b => b n l -> RequiredIfaces l -> RequiredIfaces n
hoistRequiredIfaces bs = \case
  FailIfRequired    -> FailIfRequired
  GatherRequired ds -> GatherRequired $ eSetFromList $ eSetToList ds & mapMaybe \d -> case hoist bs d of
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
  unsafeGetEnv = do
    InfOutMap bindings _ _ _ <- InfererM $ SubstReaderT $ lift $ lift11 $ getOutMapInplaceT
    return bindings
  {-# INLINE unsafeGetEnv #-}

instance EnvExtender (InfererM i) where
  refreshAbs ab cont = InfererM $ SubstReaderT $ ReaderT \env -> StateT1 \s -> do
    refreshAbs ab \b e -> do
      (ans, s') <- flip runStateT1 (sink s) $ runSubstReaderT (sink env) $
                     runInfererM' $ cont b e
      return (ans, hoistRequiredIfaces b s')
  {-# INLINE refreshAbs #-}

-- === actual inference pass ===

type SigmaType = Type  -- may     start with an implicit lambda
type RhoType   = Type  -- doesn't start with an implicit lambda
data RequiredTy (e::E) (n::S) = Check (e n)
                              | Infer
                                deriving Show

checkSigma :: EmitsBoth o
           => UExpr i -> SigmaType o -> InfererM i o (Atom o)
checkSigma expr sTy = confuseGHC >>= \_ -> case sTy of
  Pi piTy@(PiType (PiBinder b _ arrow) _ _)
    | arrow `elem` [ImplicitArrow, ClassArrow] -> case expr of
        WithSrcE _ (ULam lam@(ULamExpr arrow' _ _)) | arrow == arrow' -> checkULam lam piTy
        -- we have to add the lambda argument corresponding to the implicit pi
        -- type argument
        _ -> do
          buildLamInf (getNameHint b) arrow (argType piTy) (\_-> return Pure)
            \x -> do
              piTy' <- sinkM piTy
              (Pure, bodyTy) <- instantiatePi piTy' (Var x)
              checkSigma expr bodyTy
  _ -> checkOrInferRho expr (Check sTy)

inferSigma :: EmitsBoth o => UExpr i -> InfererM i o (Atom o)
inferSigma (WithSrcE pos expr) = case expr of
  ULam lam@(ULamExpr ImplicitArrow _ _) ->
    addSrcContext pos $ inferULam Pure lam
  -- TODO: Should we be handling class arrows here?
  _ -> inferRho (WithSrcE pos expr)

checkRho :: EmitsBoth o => UExpr i -> RhoType o -> InfererM i o (Atom o)
checkRho expr ty = checkOrInferRho expr (Check ty)
{-# INLINE checkRho #-}

inferRho :: EmitsBoth o => UExpr i -> InfererM i o (Atom o)
inferRho expr = checkOrInferRho expr Infer
{-# INLINE inferRho #-}

instantiateSigma :: EmitsBoth o => Atom o -> InfererM i o (Atom o)
instantiateSigma f = do
  ty <- tryGetType f
  args <- getImplicitArgs ty
  naryApp f args

getImplicitArgs :: EmitsInf o => Type o -> InfererM i o [Atom o]
getImplicitArgs ty = case ty of
  Pi (PiType b _ _) ->
    getImplicitArg b >>= \case
      Nothing -> return []
      Just arg -> do
        appTy <- getAppType ty [arg]
        (arg:) <$> getImplicitArgs appTy
  _ -> return []

getImplicitArg :: EmitsInf o => PiBinder o o' -> InfererM i o (Maybe (Atom o))
getImplicitArg (PiBinder _ argTy arr) = case arr of
  ImplicitArrow -> Just <$> freshType argTy
  ClassArrow -> do
    ctx <- srcPosCtx <$> getErrCtx
    return $ Just $ Con $ DictHole ctx argTy
  _ -> return Nothing

checkOrInferRho :: forall i o. EmitsBoth o
                => UExpr i -> RequiredTy RhoType o -> InfererM i o (Atom o)
checkOrInferRho (WithSrcE pos expr) reqTy = do
 addSrcContext pos $ confuseGHC >>= \_ -> case expr of
  UVar ~(InternalName _ v) -> do
    substM v >>= inferUVar >>= instantiateSigma >>= matchRequirement
  ULam (ULamExpr ImplicitArrow (UPatAnn p ann) body) -> do
    argTy <- checkAnn ann
    v <- freshInferenceName argTy
    bindLamPat p v $ checkOrInferRho body reqTy
  ULam lamExpr -> do
    case reqTy of
      Check (Pi piTy) -> checkULam lamExpr piTy
      Check _ -> inferULam Pure lamExpr >>= matchRequirement
      Infer   -> inferULam Pure lamExpr
  UTabLam (UTabLamExpr b body) -> do
    let uLamExpr = ULamExpr PlainArrow b body
    Lam (LamExpr (LamBinder b' ty' _ _) body') <- case reqTy of
      Check (TabPi tabPiTy) -> do
        lamPiTy <- buildForTypeFromTabType Pure tabPiTy
        checkULam uLamExpr lamPiTy
      Check _ -> inferULam Pure uLamExpr
      Infer   -> inferULam Pure uLamExpr
    checkIx (annTypePos b) ty'
    matchRequirement $ TabLam $ TabLamExpr (b':>ty') body'
  UFor dir (UForExpr b body) -> do
    allowedEff <- getAllowedEffects
    let uLamExpr = ULamExpr PlainArrow b body
    lam@(Lam (LamExpr b' _)) <- case reqTy of
      Check (TabPi tabPiTy) -> do
        lamPiTy <- buildForTypeFromTabType allowedEff tabPiTy
        checkULam uLamExpr lamPiTy
      Check _ -> inferULam allowedEff uLamExpr
      Infer   -> inferULam allowedEff uLamExpr
    result <- liftM Var $ emit $ Hof $ For (RegularFor dir) lam
    checkIx (annTypePos b) $ binderType b'
    matchRequirement result
  UApp _ _ -> do
    let (f, args) = asNaryApp $ WithSrcE pos expr
    f' <- inferFunNoInstantiation f >>= zonk
    inferNaryApp (srcPos f) f' (NE.fromList args) >>= matchRequirement
  UTabApp _ _ -> do
    let (tab, args) = asNaryTabApp $ WithSrcE pos expr
    tab' <- inferRho tab >>= zonk
    inferNaryTabApp (srcPos tab) tab' (NE.fromList args) >>= matchRequirement
  UPi (UPiExpr arr (UPatAnn (WithSrcB pos' pat) ann) effs ty) -> do
    -- TODO: make sure there's no effect if it's an implicit or table arrow
    piTy <- checkAnnWithMissingDicts ann \missingDs getAnnType -> do
      -- Note that we can't automatically quantify class Pis, because the class dict
      -- might have been bound on the rhs of a let and it would get bound to the
      -- inserted arguments instead of the desired dict. It's not a fundemental
      -- limitation of our automatic quantification, but it's simpler not to deal with
      -- that for now.
      let checkNoMissing = addSrcContext pos' $ unless (null $ eSetToList missingDs) $ throw TypeErr $
            "Couldn't synthesize a class dictionary for: " ++ pprint (head $ eSetToList missingDs)
      autoDs <- case arr of
        ClassArrow -> checkNoMissing $> mempty
        _          -> return $ missingDs
      introDictTys (eSetToList autoDs) $ do
        ann' <- getAnnType
        addSrcContext pos' case pat of
          UPatBinder UIgnore ->
            buildPiInf noHint arr ann' \_ -> (,) <$> checkUEffRow effs <*> checkUType ty
          _ -> buildPiInf (getNameHint pat) arr ann' \v -> do
            Abs decls result <- buildDeclsInf do
              v' <- sinkM v
              bindLamPat (WithSrcB pos' pat) v' do
                effs' <- checkUEffRow effs
                ty'   <- checkUType   ty
                return $ PairE effs' ty'
            cheapReduceWithDecls decls result >>= \case
              (Just (PairE effs' ty'), DictTypeHoistSuccess, []) -> return $ (effs', ty')
              _ -> throw TypeErr $ "Can't reduce type expression: " ++
                     docAsStr (prettyBlock decls $ snd $ fromPairE result)
    matchRequirement $ Pi piTy
  UTabPi (UTabPiExpr (UPatAnn (WithSrcB pos' pat) ann) ty) -> do
    ann' <- checkAnn ann
    piTy <- addSrcContext pos' case pat of
      UPatBinder UIgnore ->
        buildTabPiInf noHint ann' \_ -> checkUType ty
      _ -> buildTabPiInf (getNameHint pat) ann' \v -> do
        Abs decls piResult <- buildDeclsInf do
          v' <- sinkM v
          bindLamPat (WithSrcB pos' pat) v' $ checkUType ty
        cheapReduceWithDecls decls piResult >>= \case
          (Just ty', DictTypeHoistSuccess, []) -> return ty'
          _ -> throw TypeErr $ "Can't reduce type expression: " ++
                 docAsStr (prettyBlock decls piResult)
    checkIx pos' $ argType piTy
    matchRequirement $ TabPi piTy
  UDecl (UDeclExpr (ULet letAnn (UPatAnn p ann) rhs) body) -> do
    val <- checkMaybeAnnExpr ann rhs
    var <- emitDecl (getNameHint p) letAnn $ Atom val
    bindLamPat p var $ checkOrInferRho body reqTy
  UDecl _ -> throw CompilerErr "not a local decl"
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
  UPrimExpr (OpExpr (ExplicitApply f x)) -> do
    f' <- inferFunNoInstantiation f
    x' <- inferRho x
    (liftM Var $ emit $ App f' (x':|[])) >>= matchRequirement
  UPrimExpr prim -> do
    prim' <- forM prim \x -> do
      xBlock <- buildBlockInf $ inferRho x
      getType xBlock >>= \case
        TyKind -> cheapReduce xBlock >>= \case
          (Just reduced, DictTypeHoistSuccess, []) -> return reduced
          _ -> throw CompilerErr "Type args to primops must be reducible"
        _ -> emitBlock xBlock
    val <- case prim' of
      TCExpr  e -> return $ TC e
      ConExpr e -> return $ Con e
      OpExpr  e -> Var <$> emit (Op e)
      HofExpr e -> Var <$> emit (Hof e)
    matchRequirement val
  ULabel name -> matchRequirement $ Con $ LabelCon name
  URecord elems ->
    matchRequirement =<< resolveDelay =<< foldM go (Nothing, mempty) (reverse elems)
    where
      go :: EmitsInf o
         => (Maybe (Atom o), LabeledItems (Atom o)) -> UFieldRowElem i
         -> InfererM i o (Maybe (Atom o), LabeledItems (Atom o))
      go delayedRec = \case
        UStaticField l e -> do
          e' <- inferRho e
          return (rec, labeledSingleton l e' <> delayItems)
          where (rec, delayItems) = delayedRec
        UDynField    v e -> do
          v' <- checkRho (WithSrcE Nothing $ UVar v) (TC LabelType)
          e' <- inferRho e
          rec' <- emitOp . RecordConsDynamic v' e' =<< resolveDelay delayedRec
          return (Just rec', mempty)
        UDynFields   v -> do
          anyFields <- freshInferenceName LabeledRowKind
          v' <- checkRho v $ RecordTyWithElems [DynFields anyFields]
          case delayedRec of
            (Nothing, delayItems) | null delayItems -> return (Just v', mempty)
            _ -> do
              rec' <- emitOp . RecordCons v' =<< resolveDelay delayedRec
              return (Just rec', mempty)

      resolveDelay :: EmitsInf o
                   => (Maybe (Atom o), LabeledItems (Atom o)) -> InfererM i o (Atom o)
      resolveDelay = \case
        (Nothing , delayedItems) -> return $ Record delayedItems
        (Just rec, delayedItems) -> case null delayedItems of
          True  -> return rec
          False -> emitOp $ RecordCons (Record delayedItems) rec
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
  URecordTy   elems -> matchRequirement =<< RecordTyWithElems . concat <$> mapM inferFieldRowElem elems
  ULabeledRow elems -> matchRequirement =<< LabeledRow . fieldRowElemsFromList . concat <$> mapM inferFieldRowElem elems
  UVariantTy row -> matchRequirement =<< VariantTy <$> checkExtLabeledRow row
  UVariantLift labels value -> do
    row <- freshInferenceName LabeledRowKind
    value' <- zonk =<< (checkRho value $ VariantTy $ Ext NoLabeledItems $ Just row)
    prev <- mapM (\() -> freshType TyKind) labels
    matchRequirement =<< emitOp (VariantLift prev value')
  UIntLit x  -> do
    lookupSourceMap "from_integer" >>= \case
      Nothing ->
        -- fallback for missing protolude
        matchRequirement $ Con $ Lit $ Int32Lit $ fromIntegral x
      Just (UMethodVar fromIntMethod) -> do
        ~(MethodBinding _ _ fromInt) <- lookupEnv fromIntMethod
        fromInt' <- instantiateSigma fromInt
        let i64Atom = Con $ Lit $ Int64Lit $ fromIntegral x
        result <- matchRequirement =<< app fromInt' i64Atom
        resultTy <- getType result
        addDefault resultTy $ BaseTy (Scalar Int32Type)
        return result
      Just _ -> error "not a method"
  UFloatLit x -> matchRequirement $ Con $ Lit  $ Float32Lit $ realToFrac x
  -- TODO: Make sure that this conversion is not lossy!
  where
    matchRequirement :: Atom o -> InfererM i o (Atom o)
    matchRequirement x = return x <*
      case reqTy of
        Infer -> return ()
        Check req -> do
          ty <- getType x
          constrainEq req ty
    {-# INLINE matchRequirement #-}

    annTypePos :: UPatAnn n l -> SrcPosCtx
    annTypePos = \case
      UPatAnn _ (Just (WithSrcE annpos _)) -> annpos
      UPatAnn (WithSrcB bpos _) _ -> bpos
    {-# INLINE annTypePos #-}

inferFieldRowElem :: EmitsBoth o => UFieldRowElem i -> InfererM i o [FieldRowElem o]
inferFieldRowElem = \case
  UStaticField l ty -> do
    ty' <- checkUType ty
    return [StaticFields $ labeledSingleton l ty']
  UDynField    v ty -> do
    ty' <- checkUType ty
    checkRho (WithSrcE Nothing $ UVar v) (TC LabelType) >>= \case
      Con (LabelCon l) -> return [StaticFields $ labeledSingleton l ty']
      Var v'           -> return [DynField v' ty']
      _                -> error "Unexpected Label atom"
  UDynFields   v    -> checkRho v LabeledRowKind >>= \case
    LabeledRow row -> return $ fromFieldRowElems row
    Var v'         -> return [DynFields v']
    _              -> error "Unexpected Fields atom"

-- === n-ary applications ===

-- The reason to infer n-ary applications rather than just handling nested
-- applications one by one is that we want to target the n-ary form of
-- application. This keeps our IR smaller and therefore faster and more
-- readable. But it's a bit delicate. Nary applications may only have effects at
-- their last argument, and they must only have as many arguments as implied by
-- the type of the function before it gets further instantiated. (For example,
-- `id (Float->Float) sin 1.0` is not allowed.)

-- This allows us to make the instantiated params/dicts part of an n-ary
-- application along with the ordinary explicit args
inferFunNoInstantiation :: EmitsBoth o => UExpr i -> InfererM i o (Atom o)
inferFunNoInstantiation expr@(WithSrcE pos expr') = do
 addSrcContext pos $ case expr' of
  UVar ~(InternalName _ v) -> do
    -- XXX: deliberately no instantiation!
    substM v >>= inferUVar
  _ -> inferRho expr

type UExprArg n = (SrcPosCtx, UExpr n)
asNaryApp :: UExpr n -> (UExpr n, [UExprArg n])
asNaryApp (WithSrcE appCtx (UApp f x)) =
  (f', xs ++ [(appCtx, x)])
  where (f', xs) = asNaryApp f
asNaryApp e = (e, [])

asNaryTabApp :: UExpr n -> (UExpr n, [UExprArg n])
asNaryTabApp (WithSrcE appCtx (UTabApp f x)) =
  (f', xs ++ [(appCtx, x)])
  where (f', xs) = asNaryTabApp f
asNaryTabApp e = (e, [])

inferNaryTabApp :: EmitsBoth o => SrcPosCtx -> Atom o -> NonEmpty (UExprArg i) -> InfererM i o (Atom o)
inferNaryTabApp tabCtx tab args = addSrcContext tabCtx do
  tabTy <- getType tab
  (arg':args') <- inferNaryTabAppArgs tabTy $ toList args
  liftM Var $ emit $ TabApp tab $ arg' :| args'

inferNaryTabAppArgs
  :: EmitsBoth o
  => Type o -> [UExprArg i] -> InfererM i o [Atom o]
inferNaryTabAppArgs _ [] = return []
inferNaryTabAppArgs tabTy ((appCtx, arg):rest) = do
  TabPiType (b:>argTy) resultTy <- fromTabPiType True tabTy
  checkIx Nothing argTy
  let isDependent = binderName b `isFreeIn` resultTy
  arg' <- addSrcContext appCtx $
    if isDependent
      then checkSigmaDependent arg argTy
      else checkSigma arg argTy
  arg'' <- zonk arg'
  resultTy' <- applySubst (b @> SubstVal arg'') resultTy
  rest' <- inferNaryTabAppArgs resultTy' rest
  return $ arg'':rest'

inferNaryApp :: EmitsBoth o => SrcPosCtx -> Atom o -> NonEmpty (UExprArg i) -> InfererM i o (Atom o)
inferNaryApp fCtx f args = addSrcContext fCtx do
  fTy <- getType f
  Just naryPi <- asNaryPiType <$> Pi <$> fromPiType True PlainArrow fTy
  (inferredArgs, remaining) <- inferNaryAppArgs naryPi args
  let appExpr = App f inferredArgs
  addEffects =<< exprEffects appExpr
  partiallyApplied <- Var <$> emit appExpr
  case nonEmpty remaining of
    Nothing ->
      -- we already instantiate before applying each explicit arg, but we still
      -- need to try once more after they've all been applied.
      instantiateSigma partiallyApplied
    Just remaining' -> inferNaryApp fCtx partiallyApplied remaining'

-- Returns the inferred args, along with any remaining args that couldn't be
-- applied.
-- XXX: we also instantiate args here, so the resulting inferred args list
-- includes instantiated params and dicts.
inferNaryAppArgs
  :: EmitsBoth o
  => NaryPiType o -> NonEmpty (UExprArg i) -> InfererM i o (NonEmpty (Atom o), [UExprArg i])
inferNaryAppArgs (NaryPiType (NonEmptyNest b Empty) effs resultTy) uArgs = do
  let isDependent = binderName b `isFreeIn` PairE effs resultTy
  (x, remaining) <- inferAppArg isDependent b uArgs
  return (x:|[], remaining)
inferNaryAppArgs (NaryPiType (NonEmptyNest b1 (Nest b2 rest)) effs resultTy) uArgs = do
  let restNaryPi = NaryPiType (NonEmptyNest b2 rest) effs resultTy
  let isDependent = binderName b1 `isFreeIn` restNaryPi
  (x, uArgs') <- inferAppArg isDependent b1 uArgs
  x' <- zonk x
  restNaryPi' <- applySubst (b1 @> SubstVal x') restNaryPi
  case nonEmpty uArgs' of
    Nothing -> return (x':|[], [])
    Just uArgs'' -> do
      (xs, remaining) <- inferNaryAppArgs restNaryPi' uArgs''
      return (NE.cons x' xs, remaining)

inferAppArg
  :: EmitsBoth o
  => Bool -> PiBinder o o' -> NonEmpty (UExprArg i) -> InfererM i o (Atom o, [UExprArg i])
inferAppArg isDependent b@(PiBinder _ argTy _) uArgs = getImplicitArg b >>= \case
  Just x -> return $ (x, toList uArgs)
  Nothing -> do
    let (appCtx, arg) :| restUArgs = uArgs
    liftM (,restUArgs) $ addSrcContext appCtx $
      if isDependent
        then checkSigmaDependent arg argTy
        else checkSigma arg argTy

checkSigmaDependent :: EmitsBoth o
                    => UExpr i -> SigmaType o -> InfererM i o (Atom o)
checkSigmaDependent e@(WithSrcE ctx _) ty = do
  Abs decls result <- buildDeclsInf $ checkSigma e (sink ty)
  cheapReduceWithDecls decls result >>= \case
    (Just x', DictTypeHoistSuccess, ds) ->
      forM_ ds reportUnsolvedInterface >> return x'
    _ -> addSrcContext ctx $ throw TypeErr $ depFunErrMsg
  where
    depFunErrMsg =
      "Dependent functions can only be applied to fully evaluated expressions. " ++
      "Bind the argument to a name before you apply the function."

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

buildMonomorphicCase
  :: (Emits n, ScopableBuilder m)
  => [IndexedAlt n] -> Atom n -> Type n -> m n (Atom n)
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
    TypeCon _ _ _ -> liftEmitBuilder $ buildMonomorphicCase alts scrut resultTy
    VariantTy (Ext types tailName) -> do
      case filter isVariantTailAlt alts of
        [] -> case tailName of
          Nothing ->
            -- We already know the type exactly, so just emit a case.
            liftEmitBuilder $ buildMonomorphicCase alts scrut resultTy
          Just _ -> do
            -- Split off the types we don't know about, mapping them to a
            -- runtime error.
            liftEmitBuilder $ buildSplitCase types scrut resultTy
              (\v -> do ListE alts' <- sinkM $ ListE alts
                        resultTy'   <- sinkM resultTy
                        liftEmitBuilder $ buildMonomorphicCase alts' (Var v) resultTy')
              (\_ -> do resultTy' <- sinkM resultTy
                        emitOp $ ThrowError resultTy')
        [IndexedAlt (VariantTailAlt (LabeledItems skippedItems)) tailAlt] -> do
            -- Split off the types skipped by the tail pattern.
            let splitLeft fvs ltys = NE.fromList $ NE.take (length ltys) fvs
            let left = LabeledItems $ M.intersectionWith splitLeft
                        (fromLabeledItems types) skippedItems
            checkNoTailOverlaps alts left
            liftEmitBuilder $ buildSplitCase left scrut resultTy
              (\v -> do ListE alts' <- sinkM $ ListE alts
                        resultTy'   <- sinkM resultTy
                        liftEmitBuilder $ buildMonomorphicCase alts' (Var v) resultTy')
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

inferUVar :: EmitsBoth o => UVar o -> InfererM i o (Atom o)
inferUVar = \case
  UAtomVar v ->
    return $ Var v
  UTyConVar v -> do
    TyConBinding   _ tyConAtom <- lookupEnv v
    return tyConAtom
  UDataConVar v -> do
    DataConBinding _ _ conAtom <- lookupEnv v
    return conAtom
  UClassVar v -> dictTypeFun v
  UMethodVar v -> do
    MethodBinding _ _ f <- lookupEnv v
    return f

buildForTypeFromTabType :: EffectRow n -> TabPiType n -> InfererM i n (PiType n)
buildForTypeFromTabType effs tabPiTy@(TabPiType (b:>ixTy) _) = do
  buildPi (getNameHint b) PlainArrow ixTy \i -> do
    Distinct <- getDistinct
    resultTy <- instantiateTabPi (sink tabPiTy) $ Var i
    return (sink effs, resultTy)

checkMaybeAnnExpr :: EmitsBoth o => Maybe (UType i) -> UExpr i -> InfererM i o (Atom o)
checkMaybeAnnExpr ty expr = confuseGHC >>= \_ -> case ty of
  Nothing -> inferSigma expr
  Just ty' -> checkSigma expr =<< zonk =<< checkUType ty'

tyConDefAsAtom :: EnvReader m => DataDefName n -> Maybe (DataIfaceReq n) -> m n (Atom n)
tyConDefAsAtom defName maybeIfaceReq = liftBuilder do
  DataDef sourceName params _ <- lookupDataDef =<< sinkM defName
  buildPureNaryLam (EmptyAbs $ binderNestAsPiNest PlainArrow params) \params' -> do
    EmptyAbs clsBs' <- case maybeIfaceReq of
      Just clsAbs -> sinkM clsAbs >>= (`applyNaryAbs` params')
      Nothing     -> return $ EmptyAbs Empty
    buildPureNaryLam (EmptyAbs $ binderNestAsPiNest ClassArrow clsBs') \_ -> do
      ListE params'' <- sinkM $ ListE params'
      defName'' <- sinkM defName
      return $ TypeCon sourceName defName'' $ Var <$> params''

dictTypeFun :: EnvReader m => ClassName n -> m n (Atom n)
dictTypeFun v = do
  -- TODO: we should cache this in the ClassDef
  ClassDef classSourceName _ paramBinders _ _ <- lookupClassDef v
  liftEnvReaderM $ refreshAbs (Abs paramBinders UnitE) \bs' UnitE -> do
    v' <- sinkM v
    return $ go classSourceName bs' v' $ nestToNames bs'
  where
    go :: SourceName -> Nest Binder n l -> ClassName l -> [AtomName l] -> Atom n
    go classSourceName bs className params = case bs of
      Empty -> DictTy $ DictType classSourceName className $ map Var params
      Nest (b:>ty) rest ->
        Lam $ LamExpr (LamBinder b ty PlainArrow Pure) $
          AtomicBlock $ go classSourceName rest className params

-- TODO: cache this with the instance def (requires a recursive binding)
instanceFun :: EnvReader m => InstanceName n -> m n (Atom n)
instanceFun instanceName = do
  InstanceDef _ bs _ _ <- lookupInstanceDef instanceName
  liftEnvReaderM $ refreshAbs (Abs bs UnitE) \bs' UnitE -> do
    let args = map Var $ nestToNames bs'
    instanceName' <- sinkM instanceName
    return $ go bs' instanceName' args
  where
    go :: Nest PiBinder n l -> InstanceName l -> [Atom l] -> Atom n
    go bs name args = case bs of
      Empty -> DictCon $ InstanceDict name args
      Nest (PiBinder b ty arr) rest -> do
        let restAtom = go rest name args
        Lam $ LamExpr (LamBinder b ty arr Pure) (AtomicBlock restAtom)

dataConDefAsAtom :: EnvReader m => DataDefName n -> DataIfaceReq n -> Int -> m n (Atom n)
dataConDefAsAtom defName ifaceReq conIx = liftBuilder do
  DataDef _ tyParams conDefs <- lookupDataDef =<< sinkM defName
  let conDef = conDefs !! conIx
  buildPureNaryLam (EmptyAbs $ binderNestAsPiNest ImplicitArrow tyParams) \tyArgs' -> do
    EmptyAbs clsParams' <- sinkM ifaceReq >>= (`applyNaryAbs` tyArgs')
    buildPureNaryLam (EmptyAbs $ binderNestAsPiNest ClassArrow clsParams') \_ -> do
      ab'' <- sinkM $ Abs tyParams conDef
      ListE tyArgs'' <- sinkM $ ListE tyArgs'
      DataConDef conName (EmptyAbs conParams'') <- applyNaryAbs ab'' tyArgs''
      buildPureNaryLam (EmptyAbs $ binderNestAsPiNest PlainArrow conParams'') \conArgs''' -> do
        ListE tyArgs''' <- sinkM $ ListE tyArgs'
        defName''' <- sinkM defName
        return $ DataCon conName defName''' (Var <$> tyArgs''') conIx (Var <$> conArgs''')

binderNestAsPiNest :: Arrow -> Nest Binder n l -> Nest PiBinder n l
binderNestAsPiNest arr = \case
  Empty             -> Empty
  Nest (b:>ty) rest -> Nest (PiBinder b ty arr) $ binderNestAsPiNest arr rest

type DataIfaceReq =
  Abs (Nest Binder)  -- Type parameters
    (EmptyAbs (Nest Binder))  -- Interface binders

inferDataDef :: EmitsInf o => UDataDef i -> InfererM i o (PairE DataDef DataIfaceReq o)
inferDataDef (UDataDef (tyConName, paramBs) clsBs dataCons) = do
  Abs paramBs' (PairE clsBs' (ListE dataCons')) <-
    withNestedUBinders paramBs id \_ -> do
      -- TODO: Don't masquerade as a class lambda
      Abs clsBs' dataCons'' <-
        withNestedUBinders clsBs (LamBound . LamBinding ClassArrow) \_ -> do
          dataCons' <- mapM inferDataCon dataCons
          return $ ListE dataCons'
      case hoist clsBs' dataCons'' of
        HoistFailure _ -> throw NotImplementedErr $ "Non-phantom type constraints in data?"
        HoistSuccess dataCons' -> return (PairE (EmptyAbs clsBs') dataCons')
  return $ PairE (DataDef tyConName paramBs' dataCons') (Abs paramBs' clsBs')

inferDataCon :: EmitsInf o
             => (SourceName, UDataDefTrail i) -> InfererM i o (DataConDef o)
inferDataCon (sourceName, UDataDefTrail argBs) = do
  argBs' <- checkUBinders (EmptyAbs argBs)
  return $ DataConDef sourceName argBs'

inferClassDef
  :: SourceName -> [SourceName] -> Nest (UAnnBinder AtomNameC) i i'
  -> [UType i'] -> [UMethodType i']
  -> InfererM i o (ClassDef o)
inferClassDef className methodNames paramBs superclasses methods = solveLocal do
  ab <- withNestedUBinders paramBs id \_ -> do
    superclasses' <- mapM checkUType superclasses
    methodsTys'   <- forM methods \(UMethodType (Right explicits) ty) -> do
      ty' <- checkUType ty
      return $ MethodType explicits ty'
    return $ PairE (ListE superclasses') (ListE methodsTys')
  Abs bs (PairE (ListE scs) (ListE mtys)) <- return ab
  return $ ClassDef className methodNames bs scs mtys

withNestedUBinders
  :: (EmitsInf o, HasNamesE e, SubstE AtomSubstVal e, SinkableE e, ToBinding binding AtomNameC)
  => Nest (UAnnBinder AtomNameC) i i'
  -> (forall l. Type l -> binding l)
  -> (forall o'. (EmitsInf o', Ext o o') => [AtomName o'] -> InfererM i' o' (e o'))
  -> InfererM i o (Abs (Nest Binder) e o)
withNestedUBinders bs asBinding cont = case bs of
  Empty -> Abs Empty <$> cont []
  Nest b rest -> do
    Abs b' (Abs rest' body) <- withUBinder b asBinding \name -> do
      withNestedUBinders rest asBinding \names -> do
        name' <- sinkM name
        cont (name':names)
    return $ Abs (Nest b' rest') body

withUBinder :: (EmitsInf o, HasNamesE e, SubstE AtomSubstVal e, SinkableE e, ToBinding binding AtomNameC)
            => UAnnBinder AtomNameC i i'
            -> (Type o -> binding o)
            -> (forall o'. (EmitsInf o', Ext o o') => AtomName o' -> InfererM i' o' (e o'))
            -> InfererM i o (Abs Binder e o)
withUBinder (UAnnBinder b ann) asBinding cont = do
  ann' <- checkUType ann
  Abs (n :> _) ans <- buildAbsInf (getNameHint b) (asBinding ann') \name ->
    extendSubst (b @> name) $ cont name
  return $ Abs (n :> ann') ans

checkUBinders :: EmitsInf o
              => EmptyAbs (Nest (UAnnBinder AtomNameC)) i
              -> InfererM i o (EmptyAbs (Nest Binder) o)
checkUBinders (EmptyAbs bs) = withNestedUBinders bs id \_ -> return UnitE
checkUBinders _ = error "impossible"

inferULam :: EmitsBoth o => EffectRow o -> ULamExpr i -> InfererM i o (Atom o)
inferULam effs (ULamExpr arrow (UPatAnn p ann) body) = do
  argTy <- checkAnn ann
  buildLamInf (getNameHint p) arrow argTy (\_ -> sinkM effs) \v ->
    bindLamPat p v $ inferSigma body

checkULam :: EmitsBoth o => ULamExpr i -> PiType o -> InfererM i o (Atom o)
checkULam (ULamExpr _ (UPatAnn p ann) body) piTy@(PiType (PiBinder _ argTy arr) _ _) = do
  case ann of
    Nothing    -> return ()
    Just annTy -> constrainEq argTy =<< checkUType annTy
  -- XXX: we're ignoring the ULam arrow here. Should we be checking that it's
  -- consistent with the arrow supplied by the pi type?
  buildLamInf (getNameHint p) arr argTy
    (\v -> do
        piTy' <- sinkM piTy
        fst <$> instantiatePi piTy' (Var v) )
     \v -> bindLamPat p v do
        piTy' <- sinkM piTy
        (_, resultTy) <- instantiatePi piTy' (Var v)
        checkSigma body resultTy

checkInstanceArgs
  :: (EmitsInf o, SinkableE e, SubstE Name e, HoistableE e)
  => Nest UPatAnnArrow i i'
  -> (forall o'. (EmitsInf o', Ext o o') => InfererM i' o' (e o'))
  -> InfererM i o (Abs (Nest PiBinder) e o)
checkInstanceArgs Empty cont = Abs Empty <$> cont
checkInstanceArgs (Nest (UPatAnnArrow (UPatAnn p ann) arrow) rest) cont = do
  case arrow of
    ImplicitArrow -> return ()
    ClassArrow    -> return ()
    PlainArrow    -> return ()
    _ -> throw TypeErr $ "Not a valid arrow for an instance: " ++ pprint arrow
  ab <- checkAnnWithMissingDicts ann \ds getArgTy -> do
    introDicts (eSetToList ds) $ do
      argTy <- getArgTy
      buildPiAbsInf (getNameHint p) arrow argTy \v -> do
        WithSrcB pos (UPatBinder b) <- return p  -- TODO: enforce this syntactically
        addSrcContext pos $ extendSubst (b@>v) $
          checkInstanceArgs rest do
            cont
  Abs bs (Abs b (Abs bs' e)) <- return ab
  return $ Abs (bs >>> Nest b Empty >>> bs') e

checkInstanceParams
  :: forall i o e.
     (EmitsInf o, SinkableE e, HoistableE e, SubstE Name e)
  => [UType i]
  -> (forall o'. (EmitsInf o', Ext o o') => [Type o'] -> InfererM i o' (e o'))
  -> InfererM i o (Abs (Nest PiBinder) e o)
checkInstanceParams params cont = go params []
  where
    go :: forall o'. (EmitsInf o', Ext o o') => [UType i] -> [Type o']
       -> InfererM i o' (Abs (Nest PiBinder) e o')
    go []    ptys = Abs Empty <$> cont (reverse ptys)
    go (p:t) ptys = checkUTypeWithMissingDicts p \ds getParamType -> do
      mergeAbs <$> introDicts (eSetToList ds) do
        pty <- getParamType
        ListE ptys' <- sinkM $ ListE ptys
        go t (pty:ptys')

mergeAbs :: Abs (Nest b) (Abs (Nest b) e) n -> Abs (Nest b) e n
mergeAbs (Abs bs (Abs bs' e)) = Abs (bs >>> bs') e

checkInstanceBody :: EmitsInf o
                  => ClassName o
                  -> [Type o]
                  -> [UMethodDef i]
                  -> InfererM i o (InstanceBody o)
checkInstanceBody className params methods = do
  def@(ClassDef _ methodNames _ _ _ ) <- getClassDef className
  (superclassTys, methodTys) <- checkedApplyClassParams def params
  superclassDicts <- mapM trySynthTerm superclassTys
  methodsChecked <- mapM (checkMethodDef className methodTys) methods
  let (idxs, methods') = unzip $ sortOn fst $ methodsChecked
  forM_ (repeated idxs) \i ->
    throw TypeErr $ "Duplicate method: " ++ pprint (methodNames!!i)
  forM_ ([0..(length methodTys - 1)] `listDiff` idxs) \i ->
    throw TypeErr $ "Missing method: " ++ pprint (methodNames!!i)
  return $ InstanceBody superclassDicts methods'

introDicts
  :: forall i o e.
     (EmitsInf o, SinkableE e, HoistableE e, SubstE Name e)
  => [Type o]
  -> (forall l. (EmitsInf l, Ext o l) => InfererM i l (e l))
  -> InfererM i o (Abs (Nest PiBinder) e o)
introDicts []    m = Abs Empty <$> m
introDicts (h:t) m = do
  ab <- buildPiAbsInf (getNameHint @String "_autoq") ClassArrow h \_ -> do
    ListE t' <- sinkM $ ListE t
    introDicts t' m
  Abs b (Abs bs e) <- return ab
  return $ Abs (Nest b bs) e

introDictTys :: forall i o. EmitsInf o
             => [Type o]
             -> (forall l. (EmitsInf l, Ext o l) => InfererM i l (PiType l))
             -> InfererM i o (PiType o)
introDictTys []    m = m
introDictTys (h:t) m = buildPiInf (getNameHint @String "_autoq") ClassArrow h \_ -> do
  ListE t' <- sinkM $ ListE t
  (Pure,) . Pi <$> (introDictTys t' m)

checkMethodDef :: EmitsInf o
               => ClassName o -> [MethodType o] -> UMethodDef i -> InfererM i o (Int, Block o)
checkMethodDef className methodTys (UMethodDef ~(InternalName sourceName v) rhs) = do
  MethodBinding className' i _ <- substM v >>= lookupEnv
  when (className /= className') do
    ClassBinding (ClassDef classSourceName _ _ _ _) <- lookupEnv className
    throw TypeErr $ pprint sourceName ++ " is not a method of "
                 ++ pprint classSourceName
  let MethodType _ methodTy = methodTys !! i
  rhs' <- buildBlockInf do
    methodTy' <- sinkM methodTy
    checkSigma rhs methodTy'
  return (i, rhs')

checkUEffRow :: EmitsInf o => UEffectRow i -> InfererM i o (EffectRow o)
checkUEffRow (EffectRow effs t) = do
   effs' <- liftM S.fromList $ mapM checkUEff $ toList effs
   t' <- forM t \(InternalName _ v) -> do
            v' <- substM v
            constrainVarTy v' EffKind
            return v'
   return $ EffectRow effs' t'

checkUEff :: EmitsInf o => UEffect i -> InfererM i o (Effect o)
checkUEff eff = case eff of
  RWSEffect rws (Just ~(InternalName _ region)) -> do
    region' <- substM region
    constrainVarTy region' TyKind
    return $ RWSEffect rws $ Just region'
  RWSEffect rws Nothing -> return $ RWSEffect rws Nothing
  ExceptionEffect -> return ExceptionEffect
  IOEffect        -> return IOEffect

constrainVarTy :: EmitsInf o => AtomName o -> Type o -> InfererM i o ()
constrainVarTy v tyReq = do
  varTy <- getType $ Var v
  constrainEq tyReq varTy

data CaseAltIndex = ConAlt Int
                  | VariantAlt Label Int
                  | VariantTailAlt (LabeledItems ())
  deriving (Eq, Show)

checkCaseAlt :: EmitsBoth o
             => RhoType o -> Type o -> UAlt i -> InfererM i o (IndexedAlt o)
checkCaseAlt reqTy scrutineeTy (UAlt pat body) = do
  alt <- checkCasePat pat scrutineeTy do
    reqTy' <- sinkM reqTy
    checkRho body reqTy'
  idx <- getCaseAltIndex pat
  return $ IndexedAlt idx alt

getCaseAltIndex :: UPat i i' -> InfererM i o CaseAltIndex
getCaseAltIndex (WithSrcB _ pat) = case pat of
  UPatCon ~(InternalName _ conName) _ -> do
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

checkCasePat :: EmitsBoth o
             => UPat i i'
             -> Type o
             -> (forall o'. (EmitsBoth o', Ext o o') => InfererM i' o' (Atom o'))
             -> InfererM i o (Alt o)
checkCasePat (WithSrcB pos pat) scrutineeTy cont = addSrcContext pos $ case pat of
  UPatCon ~(InternalName _ conName) ps -> do
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

inferParams :: (EmitsBoth o, HasNamesE e, SinkableE e)
            => Abs (Nest Binder) e o -> InfererM i o ([Type o], e o)
inferParams (Abs Empty body) = return ([], body)
inferParams (Abs (Nest (b:>ty) bs) body) = do
  x <- freshInferenceName ty
  rest <- applyAbs (Abs b (Abs bs body)) x
  (xs, body') <- inferParams rest
  return (Var x : xs, body')

bindLamPats :: EmitsBoth o
            => Nest UPat i i' -> [AtomName o] -> InfererM i' o a -> InfererM i o a
bindLamPats Empty [] cont = cont
bindLamPats (Nest p ps) (x:xs) cont = bindLamPat p x $ bindLamPats ps xs cont
bindLamPats _ _ _ = error "mismatched number of args"

bindLamPat :: EmitsBoth o => UPat i i' -> AtomName o -> InfererM i' o a -> InfererM i o a
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
  UPatCon ~(InternalName _ conName) ps -> do
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
  UPatRecord rowPat -> do
    bindPats cont ([], Empty, v) rowPat
    where
      bindPats :: EmitsBoth o
               => InfererM i' o a -> ([Label], Nest UPat i l, AtomName o) -> UFieldRowPat l i' -> InfererM i o a
      bindPats c rv = \case
        UEmptyRowPat -> case rv of
          (_ , Empty, _) -> c
          (ls, ps   , r) -> do
            labelTypeVars <- mapM (const $ freshType TyKind) $ foldMap (`labeledSingleton` ()) ls
            constrainVarTy r $ StaticRecordTy labelTypeVars
            itemsNestOrdered <- unpackInLabelOrder (Var r) ls
            bindLamPats ps itemsNestOrdered c
        URemFieldsPat b ->
          resolveDelay rv \rv' -> do
            tailVar <- freshInferenceName LabeledRowKind
            constrainVarTy rv' $ RecordTyWithElems [DynFields tailVar]
            bindLamPat (WithSrcB Nothing $ UPatBinder b) rv' c
        UStaticFieldPat l p rest -> do
          -- Note that the type constraint will be added when the delay is resolved
          let (ls, ps, rvn) = rv
          bindPats c (ls ++ [l], joinNest ps (Nest p Empty), rvn) rest
        UDynFieldsPat fv p rest -> do
          resolveDelay rv \rv' -> do
            fv' <- emitAtomToName =<< checkRho (WithSrcE Nothing $ UVar fv) LabeledRowKind
            tailVar <- freshInferenceName LabeledRowKind
            constrainVarTy rv' $ RecordTyWithElems [DynFields fv', DynFields tailVar]
            [subr, rv''] <- emitUnpacked =<< emitOp (RecordSplit (Var fv') (Var rv'))
            bindLamPat p subr $ bindPats c (mempty, Empty, rv'') rest
        UDynFieldPat lv p rest ->
          resolveDelay rv \rv' -> do
            lv' <- emitAtomToName =<< checkRho (WithSrcE Nothing $ UVar lv) (TC LabelType)
            fieldTy <- freshType TyKind
            tailVar <- freshInferenceName LabeledRowKind
            constrainVarTy rv' $ RecordTyWithElems [DynField lv' fieldTy, DynFields tailVar]
            [val, rv''] <- emitUnpacked =<< emitOp (RecordSplitDynamic (Var lv') (Var rv'))
            bindLamPat p val $ bindPats c (mempty, Empty, rv'') rest

      -- Unpacks the record and returns the components in order, as if they
      -- were looked up by consecutive labels. Note that the number of labels
      -- should match the total number of record fields, and the record should
      -- have no dynamic extensions!
      unpackInLabelOrder :: EmitsBoth o => Atom o -> [Label] -> InfererM i o [AtomName o]
      unpackInLabelOrder r ls = do
        itemsNatural <- emitUnpacked =<< zonk r
        let labelOrder = toList $ foldMap (\(i, l) -> labeledSingleton l i) $ enumerate ls
        let itemsMap = M.fromList $ zip labelOrder itemsNatural
        return $ (itemsMap M.!) <$> [0..M.size itemsMap - 1]

      resolveDelay :: EmitsBoth o => ([Label], Nest UPat i l, AtomName o) -> (AtomName o -> InfererM l o a) -> InfererM i o a
      resolveDelay (ls, ps, r) f = case ps of
        Empty -> f r
        _     -> do
          labelTypeVars <- mapM (const $ freshType TyKind) $ foldMap (`labeledSingleton` ()) ls
          tailVar <- freshInferenceName LabeledRowKind
          constrainVarTy r $ RecordTyWithElems [StaticFields labelTypeVars, DynFields tailVar]
          [itemsRecord, restRecord] <- getUnpacked =<<
            emitOp (RecordSplit
              (LabeledRow $ fieldRowElemsFromList [StaticFields labelTypeVars])
              (Var r))
          itemsNestOrdered <- unpackInLabelOrder itemsRecord ls
          restRecordName <- emitAtomToName restRecord
          bindLamPats ps itemsNestOrdered $ f restRecordName
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
    xs <- forM idxs \i -> emit $ TabApp (Var v) (i:|[])
    bindLamPats ps xs cont

checkAnn :: EmitsInf o => Maybe (UType i) -> InfererM i o (Type o)
checkAnn ann = case ann of
  Just ty -> checkUType ty
  Nothing -> freshType TyKind

checkAnnWithMissingDicts :: EmitsInf o
                         => Maybe (UType i)
                         -> (IfaceTypeSet o -> (forall o'. (EmitsInf o', Ext o o') => InfererM i o' (Type o')) -> InfererM i o a)
                         -> InfererM i o a
checkAnnWithMissingDicts ann cont = case ann of
  Just ty -> checkUTypeWithMissingDicts ty cont
  Nothing ->
    cont mempty (freshType TyKind)  -- Unannotated binders are never auto-quantified

checkUTypeWithMissingDicts :: EmitsInf o
                           => UType i
                           -> (IfaceTypeSet o -> (forall o'. (EmitsInf o', Ext o o') => InfererM i o' (Type o')) -> InfererM i o a)
                           -> InfererM i o a
checkUTypeWithMissingDicts uty@(WithSrcE pos _) cont = do
  unsolvedSubset <- do
    -- We have to be careful not to emit inference vars out of the initial solve.
    -- The resulting type will never be used in downstream inference, so we can easily
    -- end up with fake ambiguous variables if they leak out.
    Abs frag unsolvedSubset' <- liftInfererMSubst $ runLocalInfererM do
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
      (_, hoistErr, unsolved) <- cheapReduceWithDecls @Atom decls result
      case hoistErr of
        DictTypeHoistFailure -> addSrcContext pos $ throw NotImplementedErr $
          "A type expression has interface constraints that depend on values " ++
          "local to the expression"
        DictTypeHoistSuccess ->
          return $ unsolvedSubset <> eSetFromList unsolved
    return $ case hoistRequiredIfaces frag (GatherRequired unsolvedSubset') of
      GatherRequired unsolvedSubset -> unsolvedSubset
      FailIfRequired                -> error "Unreachable"
  cont unsolvedSubset $ checkUType uty

checkUType :: EmitsInf o => UType i -> InfererM i o (Type o)
checkUType uty@(WithSrcE pos _) = do
  Abs decls result <- buildDeclsInf $ withAllowedEffects Pure $ checkRho uty TyKind
  (ans, hoistStatus, ds) <- cheapReduceWithDecls decls result
  case hoistStatus of
    DictTypeHoistFailure -> addSrcContext pos $ throw NotImplementedErr $
      "A type expression has interface constraints that depend on values local to the expression"
    DictTypeHoistSuccess -> case ans of
      Just ty -> addSrcContext pos (forM_ ds reportUnsolvedInterface) $> ty
      Nothing -> case ds of
        [] -> addSrcContext pos $ throw TypeErr $
                "Can't reduce type expression: " ++ pprint uty
        ds' -> throw TypeErr $
          "Can't reduce type expression: " ++ pprint uty ++ "\n" ++
          "This might be due to a failure to find a viable interface implementation " ++
          "for: " ++ intercalate ", " (pprint <$> ds')

checkExtLabeledRow :: EmitsBoth o
                   => ExtLabeledItems (UExpr i) (UExpr i)
                   -> InfererM i o (ExtLabeledItems (Type o) (AtomName o))
checkExtLabeledRow (Ext types Nothing) = do
  types' <- mapM checkUType types
  return $ Ext types' Nothing
checkExtLabeledRow (Ext types (Just ext)) = do
  types' <- mapM checkUType types
  -- Only variables can have kind LabeledRowKind at the moment.
  Var ext' <- checkRho ext LabeledRowKind
  return $ Ext types' $ Just ext'

inferTabCon :: EmitsBoth o => [UExpr i] -> RequiredTy RhoType o -> InfererM i o (Atom o)
inferTabCon xs reqTy = do
  (tabTy, xs') <- case reqTy of
    Check tabTy@(TabPi piTy) | null $ freeVarsE (argType piTy) -> do
      idx <- indices $ argType piTy
      -- TODO: Check length!!
      unless (length idx == length xs) $
        throw TypeErr "Table type doesn't match annotation"
      xs' <- forM (zip xs idx) \(x, i) -> do
        xTy <- instantiateTabPi piTy i
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
fromTabPiType :: EmitsBoth o => Bool -> Type o -> InfererM i o (TabPiType o)
fromTabPiType _ (TabPi piTy) = return piTy
fromTabPiType expectPi ty = do
  a <- freshType TyKind
  b <- freshType TyKind
  piTy <- nonDepTabPiType a b
  if expectPi then  constrainEq (TabPi piTy) ty
              else  constrainEq ty (TabPi piTy)
  return piTy

-- Bool flag is just to tweak the reported error message
fromPiType :: EmitsBoth o => Bool -> Arrow -> Type o -> InfererM i o (PiType o)
fromPiType _ _ (Pi piTy) = return piTy -- TODO: check arrow
fromPiType expectPi arr ty = do
  a <- freshType TyKind
  b <- freshType TyKind
  piTy <- nonDepPiType arr a Pure b
  if expectPi then  constrainEq (Pi piTy) ty
              else  constrainEq ty (Pi piTy)
  return piTy

fromPairType :: EmitsBoth o => Type o -> InfererM i o (Type o, Type o)
fromPairType (PairTy t1 t2) = return (t1, t2)
fromPairType ty = do
  a <- freshType TyKind
  b <- freshType TyKind
  constrainEq (PairTy a b) ty
  return (a, b)

addEffects :: EmitsBoth o => EffectRow o -> InfererM i o ()
addEffects eff = do
  allowed <- checkAllowedUnconditionally eff
  unless allowed $ do
    effsAllowed <- getAllowedEffects
    eff' <- openEffectRow eff
    constrainEq (Eff effsAllowed) (Eff eff')

checkAllowedUnconditionally :: EffectRow o -> InfererM i o Bool
checkAllowedUnconditionally Pure = return True
checkAllowedUnconditionally eff = do
  eff' <- zonk eff
  effAllowed <- getAllowedEffects >>= zonk
  return $ case checkExtends effAllowed eff' of
    Failure _  -> False
    Success () -> True

openEffectRow :: EmitsBoth o => EffectRow o -> InfererM i o (EffectRow o)
openEffectRow (EffectRow effs Nothing) = extendEffRow effs <$> freshEff
openEffectRow effRow = return effRow

getIxClassName :: (Fallible1 m, EnvReader m) => m n (ClassName n)
getIxClassName = lookupSourceMap "Ix" >>= \case
  Nothing -> throw CompilerErr $ "Ix interface needed but not defined!"
  Just (UClassVar v) -> return v
  Just _ -> error "not a class var"

ixDictType :: (Fallible1 m, EnvReader m) => Type n -> m n (Type n)
ixDictType ty = do
  ixClassName <- getIxClassName
  return $ DictTy $ DictType "Ix" ixClassName [ty]

checkIx :: EmitsBoth o => SrcPosCtx -> Type o -> InfererM i o ()
checkIx ctx ty = do
  dictTy <- ixDictType ty
  void $ emit $ Atom $ Con $ DictHole ctx dictTy
{-# SCC checkIx #-}

synthIx :: (Fallible1 m, EnvReader m) => Type n -> m n (Atom n)
synthIx ty = ixDictType ty >>= trySynthTerm
{-# SCC synthIx #-}

-- === Solver ===

newtype SolverSubst n = SolverSubst (M.Map (AtomName n) (Type n))

instance Pretty (SolverSubst n) where
  pretty (SolverSubst m) = pretty $ M.toList m

class (CtxReader1 m, EnvReader m) => Solver (m::MonadKind1) where
  zonk :: (SubstE AtomSubstVal e, SinkableE e) => e n -> m n (e n)
  extendSolverSubst :: AtomName n -> Type n -> m n ()
  emitSolver :: EmitsInf n => SolverBinding n -> m n (AtomName n)
  solveLocal :: (SinkableE e, HoistableE e)
             => (forall l. (EmitsInf l, Ext n l, Distinct l) => m l (e l))
             -> m n (e n)

type SolverOutMap = InfOutMap

data SolverOutFrag (n::S) (l::S) =
  SolverOutFrag (SolverEmissions n l) (SolverSubst l)

type SolverEmissions = RNest (BinderP AtomNameC SolverBinding)

instance GenericB SolverOutFrag where
  type RepB SolverOutFrag = PairB SolverEmissions (LiftB SolverSubst)
  fromB (SolverOutFrag em subst) = PairB em (LiftB subst)
  toB   (PairB em (LiftB subst)) = SolverOutFrag em subst

instance ProvesExt   SolverOutFrag
instance SubstB Name SolverOutFrag
instance BindsNames  SolverOutFrag
instance SinkableB SolverOutFrag

instance OutFrag SolverOutFrag where
  emptyOutFrag = SolverOutFrag REmpty emptySolverSubst
  catOutFrags scope (SolverOutFrag em ss) (SolverOutFrag em' ss') =
    withExtEvidence em' $
      SolverOutFrag (em >>> em') (catSolverSubsts scope (sink ss) ss')

instance ExtOutMap InfOutMap SolverOutFrag where
  extendOutMap infOutMap outFrag =
    extendOutMap infOutMap $ liftSolverOutFrag outFrag

newtype SolverM (n::S) (a:: *) =
  SolverM { runSolverM' :: InplaceT SolverOutMap SolverOutFrag SearcherM n a }
  deriving (Functor, Applicative, Monad, MonadFail, Alternative, Searcher,
            ScopeReader, Fallible, CtxReader)

liftSolverM :: EnvReader m => SolverM n a -> m n (Except a)
liftSolverM cont = do
  env <- unsafeGetEnv
  Distinct <- getDistinct
  return do
    maybeResult <- runSearcherM $ runInplaceT (initInfOutMap env) $
                   runSolverM' $ cont
    case maybeResult of
      Nothing -> throw TypeErr "No solution"
      Just (_, result) -> return result
{-# INLINE liftSolverM #-}

instance EnvReader SolverM where
  unsafeGetEnv = SolverM do
    InfOutMap env _ _ _ <- getOutMapInplaceT
    return env
  {-# INLINE unsafeGetEnv #-}

newtype SolverEmission (n::S) (l::S) = SolverEmission (BinderP AtomNameC SolverBinding n l)
instance ExtOutMap SolverOutMap SolverEmission where
  extendOutMap env (SolverEmission e) = env `extendOutMap` toEnvFrag e
instance ExtOutFrag SolverOutFrag SolverEmission where
  extendOutFrag (SolverOutFrag es substs) (SolverEmission e) =
    withSubscopeDistinct e $ SolverOutFrag (RNest es e) (sink substs)

instance Solver SolverM where
  extendSolverSubst v ty = SolverM $
    void $ extendTrivialInplaceT $
      SolverOutFrag REmpty (singletonSolverSubst v ty)
  {-# INLINE extendSolverSubst #-}

  zonk e = SolverM do
    Distinct <- getDistinct
    solverOutMap <- getOutMapInplaceT
    return $ zonkWithOutMap solverOutMap $ sink e
  {-# INLINE zonk #-}

  emitSolver binding =
    SolverM $ freshExtendSubInplaceT (getNameHint @String "?") \b ->
      (SolverEmission (b:>binding), binderName b)
  {-# INLINE emitSolver #-}

  solveLocal cont = SolverM do
    results <- locallyMutableInplaceT do
      Distinct <- getDistinct
      EmitsInf <- fabricateEmitsInfEvidenceM
      runSolverM' cont
    Abs (SolverOutFrag unsolvedInfNames _) result <- return results
    case unsolvedInfNames of
      REmpty -> return result
      _      -> case hoist unsolvedInfNames result of
        HoistSuccess result' -> return result'
        HoistFailure vs -> throw TypeErr $ "Ambiguous type variables: " ++ pprint vs
  {-# INLINE solveLocal #-}

instance Unifier SolverM

freshInferenceName :: (EmitsInf n, Solver m) => Kind n -> m n (AtomName n)
freshInferenceName k = do
  ctx <- srcPosCtx <$> getErrCtx
  emitSolver $ InfVarBound k ctx
{-# INLINE freshInferenceName #-}

freshSkolemName :: (EmitsInf n, Solver m) => Kind n -> m n (AtomName n)
freshSkolemName k = emitSolver $ SkolemBound k
{-# INLINE freshSkolemName #-}

type Solver2 (m::MonadKind2) = forall i. Solver (m i)

emptySolverSubst :: SolverSubst n
emptySolverSubst = SolverSubst mempty

singletonSolverSubst :: AtomName n -> Type n -> SolverSubst n
singletonSolverSubst v ty = SolverSubst $ M.singleton v ty

-- We apply the rhs subst over the full lhs subst. We could try tracking
-- metadata about which name->type mappings contain no inference variables and
-- can be skipped.
catSolverSubsts :: Distinct n => Scope n -> SolverSubst n -> SolverSubst n -> SolverSubst n
catSolverSubsts scope (SolverSubst s1) (SolverSubst s2) =
  if M.null s2 then SolverSubst s1 else SolverSubst $ s1' <> s2
  where s1' = fmap (applySolverSubstE scope (SolverSubst s2)) s1

-- TODO: put this pattern and friends in the Name library? Don't really want to
-- have to think about `eqNameColorRep` just to implement a partial map.
lookupSolverSubst :: forall c n. Color c => SolverSubst n -> Name c n -> AtomSubstVal c n
lookupSolverSubst (SolverSubst m) name =
  case eqColorRep of
    Nothing -> Rename name
    Just (ColorsEqual :: ColorsEqual c AtomNameC)-> case M.lookup name m of
      Nothing -> Rename name
      Just ty -> SubstVal ty

applySolverSubstE :: (SubstE (SubstVal AtomNameC Atom) e, Distinct n)
                  => Scope n -> SolverSubst n -> e n -> e n
applySolverSubstE scope solverSubst@(SolverSubst m) e =
  if M.null m then e else fmapNames scope (lookupSolverSubst solverSubst) e

zonkWithOutMap :: (SubstE AtomSubstVal e, Distinct n)
               => InfOutMap n -> e n -> e n
zonkWithOutMap (InfOutMap bindings solverSubst _ _) e =
  applySolverSubstE (toScope bindings) solverSubst e

deleteFromSubst :: SolverSubst n -> AtomName n -> Maybe (SolverSubst n)
deleteFromSubst (SolverSubst m) v
  | M.member v m = Just $ SolverSubst $ M.delete v m
  | otherwise    = Nothing

liftSolverOutFrag :: Distinct l => SolverOutFrag n l -> InfOutFrag n l
liftSolverOutFrag (SolverOutFrag emissions subst) =
  InfOutFrag (liftSolverEmissions emissions) mempty subst

liftSolverEmissions :: Distinct l => SolverEmissions n l -> InfEmissions n l
liftSolverEmissions emissions =
  fmapNest (\(b:>emission) -> (b:>RightE emission)) $ unRNest emissions

instance GenericE SolverSubst where
  -- XXX: this is a bit sketchy because it's not actually bijective...
  type RepE SolverSubst = ListE (PairE AtomName Type)
  fromE (SolverSubst m) = ListE $ map (uncurry PairE) $ M.toList m
  {-# INLINE fromE #-}
  toE (ListE pairs) = SolverSubst $ M.fromList $ map fromPairE pairs
  {-# INLINE toE #-}

instance SinkableE SolverSubst where
instance SubstE Name SolverSubst where
instance HoistableE SolverSubst

constrainEq :: EmitsInf o => Type o -> Type o -> InfererM i o ()
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
  void $ addContext msg $ liftSolverMInf $ unify t1' t2'

class (Alternative1 m, Searcher1 m, Fallible1 m, Solver m) => Unifier m

class (AlphaEqE e, SinkableE e, SubstE AtomSubstVal e) => Unifiable (e::E) where
  unifyZonked :: EmitsInf n => e n -> e n -> SolverM n ()

tryConstrainEq :: EmitsInf o => Type o -> Type o -> InfererM i o ()
tryConstrainEq t1 t2 = do
  constrainEq t1 t2 `catchErr` \errs -> case errs of
    Errs [Err TypeErr _ _] -> return ()
    _ -> throwErrs errs

unify :: (EmitsInf n, Unifiable e) => e n -> e n -> SolverM n ()
unify e1 e2 = do
  e1' <- zonk e1
  e2' <- zonk e2
  (unifyZonked e1' e2' <!> throw TypeErr "")
{-# INLINE unify #-}
{-# SCC unify #-}

instance Unifiable Atom where
  unifyZonked e1 e2 = confuseGHC >>= \_ -> case sameConstructor e1 e2 of
    False -> case (e1, e2) of
      (t, Var v) -> extendSolution v t
      (Var v, t) -> extendSolution v t
      _ -> empty
    True -> case (e1, e2) of
      (Var v', Var v) -> if v == v' then return () else extendSolution v e1 <|> extendSolution v' e2
      (Pi piTy, Pi piTy') -> unifyPiType piTy piTy'
      (TabPi piTy, TabPi piTy') -> unifyTabPiType piTy piTy'
      (RecordTy els, RecordTy els') -> bindM2 unifyZonked (cheapNormalize els) (cheapNormalize els')
      (VariantTy xs, VariantTy xs') -> unify (ExtLabeledItemsE xs) (ExtLabeledItemsE xs')
      (TypeCon _ c xs, TypeCon _ c' xs') -> guard (c == c') >> zipWithM_ unify xs xs'
      (TC con, TC con') -> do
        guard $ sameConstructor con con'
        -- TODO: Optimize this!
        guard $ void con == void con'
        zipWithM_ unify (toList con) (toList con')
      (Eff eff, Eff eff') -> unify eff eff'
      (DictTy d, DictTy d') -> unify d d'
      _ -> unifyEq e1 e2

instance Unifiable DictType where
  unifyZonked (DictType _ c params) (DictType _ c' params') =
    guard (c == c') >> zipWithM_ unify params params'
  {-# INLINE unifyZonked #-}

instance Unifiable (EffectRowP AtomName) where
  unifyZonked x1 x2 =
        unifyDirect x1 x2
    <|> unifyDirect x2 x1
    <|> unifyZip x1 x2

   where
     unifyDirect :: EmitsInf n => EffectRow n -> EffectRow n -> SolverM n ()
     unifyDirect r@(EffectRow effs' mv') (EffectRow effs (Just v)) | S.null effs =
       case mv' of
         Just v' | v == v' -> guard $ S.null effs'
         _ -> extendSolution v (Eff r)
     unifyDirect _ _ = empty
     {-# INLINE unifyDirect #-}

     unifyZip :: EmitsInf n => EffectRow n -> EffectRow n -> SolverM n ()
     unifyZip r1 r2 = case (r1, r2) of
      (EffectRow effs1 t1, EffectRow effs2 t2) | not (S.null effs1 || S.null effs2) -> do
        let extras1 = effs1 `S.difference` effs2
        let extras2 = effs2 `S.difference` effs1
        newRow <- freshEff
        unify (EffectRow mempty t1) (extendEffRow extras2 newRow)
        unify (extendEffRow extras1 newRow) (EffectRow mempty t2)
      _ -> unifyEq r1 r2

-- TODO: This unification procedure is incomplete! There are types that we might
-- want to treat as equivalent, but for now they would be rejected conservatively!
-- One example would is the unification of {a: ty} and {@infVar: ty}.
instance Unifiable FieldRowElems where
  unifyZonked e1 e2 = go (fromFieldRowElems e1) (fromFieldRowElems e2)
    where
      go = curry \case
        ([]           , []           ) -> return ()
        ([DynFields f], [DynFields g]) | f == g -> return ()
        ([DynFields f], r            ) -> extendSolution f $ LabeledRow $ fieldRowElemsFromList r
        (l            , [DynFields f]) -> extendSolution f $ LabeledRow $ fieldRowElemsFromList l
        (l@(h:t)      , r@(h':t')    ) -> (unifyElem h h' >> go t t') <|> unifyAsExtLabledItems l r
        (l            , r            ) -> unifyAsExtLabledItems l r

      unifyElem :: EmitsInf n => FieldRowElem n -> FieldRowElem n -> SolverM n ()
      unifyElem f1 f2 = case (f1, f2) of
        (DynField v ty     , DynField v' ty'    ) -> unify (Var v) (Var v') >> unify ty ty'
        (DynFields r       , DynFields r'       ) -> unify (Var r) (Var r')
        (StaticFields items, StaticFields items') -> do
          guard $ reflectLabels items == reflectLabels items'
          zipWithM_ unify (toList items) (toList items')
        _ -> unifyEq f1 f2

      unifyAsExtLabledItems l r = bindM2 unify (asExtLabeledItems l) (asExtLabeledItems r)

      asExtLabeledItems x = ExtLabeledItemsE <$> fieldRowElemsAsExtRow (fieldRowElemsFromList x)

instance Unifiable (ExtLabeledItemsE Type AtomName) where
  unifyZonked x1 x2 =
        unifyDirect x1 x2
    <|> unifyDirect x2 x1
    <|> unifyZip x1 x2

   where
     unifyDirect :: EmitsInf n
                 => ExtLabeledItemsE Type AtomName n
                 -> ExtLabeledItemsE Type AtomName n -> SolverM n ()
     unifyDirect (ExtLabeledItemsE (Ext NoLabeledItems (Just v))) (ExtLabeledItemsE r@(Ext items mv)) =
       case mv of
         Just v' | v == v' -> guard $ null items
         _ -> extendSolution v $ LabeledRow $ extRowAsFieldRowElems r
     unifyDirect _ _ = empty
     {-# INLINE unifyDirect #-}

     unifyZip :: EmitsInf n
              => ExtLabeledItemsE Type AtomName n
              -> ExtLabeledItemsE Type AtomName n -> SolverM n ()
     unifyZip (ExtLabeledItemsE r1) (ExtLabeledItemsE r2) = case (r1, r2) of
       (Ext NoLabeledItems Nothing, Ext NoLabeledItems Nothing) -> return ()
       (_, Ext NoLabeledItems _) -> empty
       (Ext NoLabeledItems _, _) -> empty
       (Ext (LabeledItems items1) t1, Ext (LabeledItems items2) t2) -> do
         let unifyPrefixes tys1 tys2 = mapM (uncurry unify) $ NE.zip tys1 tys2
         sequence_ $ M.intersectionWith unifyPrefixes items1 items2
         let diffDrop xs ys = NE.nonEmpty $ NE.drop (length ys) xs
         let extras1 = M.differenceWith diffDrop items1 items2
         let extras2 = M.differenceWith diffDrop items2 items1
         if t1 /= t2 then do
           newTail <- freshInferenceName LabeledRowKind
           unify (ExtLabeledItemsE (Ext NoLabeledItems t1))
                 (ExtLabeledItemsE (Ext (LabeledItems extras2) (Just newTail)))
           unify (ExtLabeledItemsE (Ext NoLabeledItems t2))
                 (ExtLabeledItemsE (Ext (LabeledItems extras1) (Just newTail)))
         else if M.null extras1 && M.null extras2 then
           -- Redundant equation t1 == t1
           return ()
         else
           -- There is no substituion that equates two records with
           -- different fields but the same tail.
           -- Catching this fixes the infinite loop described in
           -- Issue #818.
           empty

unifyEq :: AlphaEqE e => e n -> e n -> SolverM n ()
unifyEq e1 e2 = guard =<< alphaEq e1 e2
{-# INLINE unifyEq #-}

unifyPiType :: EmitsInf n => PiType n -> PiType n -> SolverM n ()
unifyPiType (PiType (PiBinder b1 ann1 arr1) eff1 ty1)
            (PiType (PiBinder b2 ann2 arr2) eff2 ty2) = do
  unless (arr1 == arr2) empty
  unify ann1 ann2
  v <- freshSkolemName ann1
  PairE eff1' ty1' <- applyAbs (Abs b1 (PairE eff1 ty1)) v
  PairE eff2' ty2' <- applyAbs (Abs b2 (PairE eff2 ty2)) v
  unify ty1'  ty2'
  unify eff1' eff2'

unifyTabPiType :: EmitsInf n => TabPiType n -> TabPiType n -> SolverM n ()
unifyTabPiType (TabPiType (b1:>ann1) ty1) (TabPiType (b2:>ann2) ty2) = do
  unify ann1 ann2
  v <- freshSkolemName ann1
  ty1' <- applyAbs (Abs b1 ty1) v
  ty2' <- applyAbs (Abs b2 ty2) v
  unify ty1'  ty2'

extendSolution :: AtomName n -> Type n -> SolverM n ()
extendSolution v t =
  isInferenceName v >>= \case
    True -> do
      when (v `isFreeIn` t) $ throw TypeErr $ "Occurs check failure: " ++ pprint (v, t)
      -- When we unify under a pi binder we replace its occurrences with a
      -- skolem variable. We don't want to unify with terms containing these
      -- variables because that would mean inferring dependence, which is a can
      -- of worms.
      forM_ (freeAtomVarsList t) \fv ->
        whenM (isSkolemName fv) $ throw TypeErr $ "Can't unify with skolem vars"
      extendSolverSubst v t
    False -> empty

isInferenceName :: EnvReader m => AtomName n -> m n Bool
isInferenceName v = lookupEnv v >>= \case
  AtomNameBinding (SolverBound (InfVarBound _ _)) -> return True
  _ -> return False
{-# INLINE isInferenceName #-}

isSkolemName :: EnvReader m => AtomName n -> m n Bool
isSkolemName v = lookupEnv v >>= \case
  AtomNameBinding (SolverBound (SkolemBound _)) -> return True
  _ -> return False
{-# INLINE isSkolemName #-}

freshType :: (EmitsInf n, Solver m) => Kind n -> m n (Type n)
freshType k = Var <$> freshInferenceName k
{-# INLINE freshType #-}

freshEff :: (EmitsInf n, Solver m) => m n (EffectRow n)
freshEff = EffectRow mempty . Just <$> freshInferenceName EffKind
{-# INLINE freshEff #-}

renameForPrinting :: (EnvReader m, HoistableE e, SinkableE e, SubstE Name e)
                   => e n -> m n (Abs (Nest (NameBinder AtomNameC)) e n)
renameForPrinting e = do
  infVars <- filterM isInferenceVar $ freeAtomVarsList e
  let ab = abstractFreeVarsNoAnn infVars e
  let hints = take (length infVars) $ map getNameHint $
                map (:[]) ['a'..'z'] ++ map show [(0::Int)..]
  Distinct <- getDistinct
  scope <- toScope <$> unsafeGetEnv  -- TODO: figure out how to do it safely
  return $ withManyFresh hints scope \bs' ->
    runScopeReaderM (scope `extendOutMap` toScopeFrag bs') do
      ab' <- sinkM ab
      e' <- applyNaryAbs ab' $ nestToNames bs'
      return $ Abs bs' e'

-- === dictionary synthesis ===

synthTopBlock :: (EnvReader m, Fallible1 m) => Block n -> m n (Block n)
synthTopBlock block = do
  (liftExcept =<<) $ liftDictSynthTraverserM $ traverseGenericE block
{-# SCC synthTopBlock #-}

synthInstanceDef
  :: (EnvReader m, Fallible1 m) => InstanceDef n -> m n (InstanceDef n)
synthInstanceDef (InstanceDef className bs params body) = do
  liftExceptEnvReaderM $ refreshAbs (Abs bs (ListE params `PairE` body))
    \bs' (ListE params' `PairE` InstanceBody superclasses methods) -> do
      methods' <- mapM synthTopBlock methods
      return $ InstanceDef className bs' params' $ InstanceBody superclasses methods'

-- main entrypoint to dictionary synthesizer
trySynthTerm :: (Fallible1 m, EnvReader m) => Type n -> m n (SynthAtom n)
trySynthTerm ty = do
  hasInferenceVars ty >>= \case
    True -> throw TypeErr "Can't synthesize a dictionary for a type with inference vars"
    False -> do
      synthTy <- liftExcept $ typeAsSynthType ty
      solutions <- liftSyntherM $ synthTerm synthTy
      case solutions of
        [] -> throw TypeErr $ "Couldn't synthesize a class dictionary for: " ++ pprint ty
        [d] -> cheapNormalize d -- normalize to reduce code size
        _ -> throw TypeErr $ "Multiple candidate class dictionaries for: " ++ pprint ty
{-# SCC trySynthTerm #-}

-- The type of a `SynthAtom` atom must be `DictTy _` or `Pi _`. If it's `Pi _`,
-- then the atom itself is either a variable or a trivial lambda whose body
-- is also a `SynthAtom`.
type SynthAtom = Atom

data SynthType n =
   SynthDictType (DictType n)
 | SynthPiType (Abs PiBinder SynthType n)
   deriving (Show, Generic)

data Givens n = Givens { fromGivens :: HM.HashMap (EKey SynthType n) (SynthAtom n) }

class (Alternative1 m, Searcher1 m, EnvReader m, EnvExtender m)
    => Synther m where
  getGivens :: m n (Givens n)
  withGivens :: Givens n -> m n a -> m n a

newtype SyntherM (n::S) (a:: *) = SyntherM
  { runSyntherM' :: OutReaderT Givens (EnvReaderT []) n a }
  deriving ( Functor, Applicative, Monad, EnvReader, EnvExtender
           , ScopeReader, MonadFail
           , Alternative, Searcher, OutReader Givens)

instance Synther SyntherM where
  getGivens = askOutReader
  {-# INLINE getGivens #-}
  withGivens givens cont = localOutReader givens cont
  {-# INLINE withGivens #-}

liftSyntherM :: EnvReader m => SyntherM n a -> m n [a]
liftSyntherM cont =
  liftEnvReaderT do
    initGivens <- givensFromEnv
    runOutReaderT initGivens $ runSyntherM' cont
{-# INLINE liftSyntherM #-}

givensFromEnv :: EnvReader m => m n (Givens n)
givensFromEnv = do
  givens <- getLambdaDicts
  let givens' = map Var givens
  getSuperclassClosure (Givens HM.empty) givens'
{-# SCC givensFromEnv #-}

extendGivens :: Synther m => [SynthAtom n] -> m n a -> m n a
extendGivens newGivens cont = do
  prevGivens <- getGivens
  finalGivens <- getSuperclassClosure prevGivens newGivens
  withGivens finalGivens cont
{-# INLINE extendGivens #-}

getSynthType :: EnvReader m => SynthAtom n -> m n (SynthType n)
getSynthType x = do
  ty <- getType x
  return $ case typeAsSynthType ty of
    Failure errs -> error $ pprint errs
    Success ty'  -> ty'
{-# INLINE getSynthType #-}

typeAsSynthType :: Type n -> Except (SynthType n)
typeAsSynthType (DictTy dictTy) = return $ SynthDictType dictTy
typeAsSynthType (Pi (PiType b@(PiBinder _ _ arrow) Pure resultTy))
  | arrow == ImplicitArrow || arrow == ClassArrow = do
     resultTy' <- typeAsSynthType resultTy
     return $ SynthPiType $ Abs b resultTy'
typeAsSynthType ty = Failure $ Errs [Err TypeErr mempty $ "Can't synthesize terms of type: " ++ pprint ty]
{-# SCC typeAsSynthType #-}

getSuperclassClosure :: EnvReader m => Givens n -> [SynthAtom n] -> m n (Givens n)
getSuperclassClosure givens newGivens = do
  Distinct <- getDistinct
  env <- unsafeGetEnv
  return $ getSuperclassClosurePure env givens newGivens
{-# INLINE getSuperclassClosure #-}

getSuperclassClosurePure
  :: Distinct n => Env n -> Givens n -> [SynthAtom n] -> Givens n
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
      ty <- getSynthType x
      return $ EKey ty `HM.member` m

    markAsVisited :: SynthAtom n -> EnvReaderT (State (Givens n)) n ()
    markAsVisited x = do
      ty <- getSynthType x
      modify \(Givens m) -> Givens $ HM.insert (EKey ty) x m

    getDirectSuperclasses :: SynthAtom n -> EnvReaderT (State (Givens n)) n [SynthAtom n]
    getDirectSuperclasses synthExpr = do
      synthTy <- getSynthType synthExpr
      -- TODO: Does this really create a full translation only to inspect the top?
      superclasses <- case synthTy of
        SynthPiType _ -> return []
        SynthDictType (DictType _ className _) -> do
          ClassDef _ _ _ superclasses _ <- lookupClassDef className
          return $ void superclasses
      return $ enumerate superclasses <&> \(i, _) -> DictCon $ SuperclassProj synthExpr i

synthTerm :: SynthType n -> SyntherM n (SynthAtom n)
synthTerm ty = confuseGHC >>= \_ -> case ty of
  SynthPiType (Abs (PiBinder b argTy arr) resultTy) ->
    withFreshBinder (getNameHint b) argTy \b' -> do
      let v = binderName b'
      resultTy' <- applySubst (b@>v) resultTy
      newGivens <- case arr of
        ClassArrow -> return [Var v]
        _ -> return []
      synthExpr <- extendGivens newGivens $ synthTerm resultTy'
      return $ Lam $ LamExpr (LamBinder b' argTy arr Pure) (AtomicBlock synthExpr)
  SynthDictType dictTy -> synthDictFromInstance dictTy <!> synthDictFromGiven dictTy
{-# SCC synthTerm #-}

synthDictFromGiven :: DictType n -> SyntherM n (SynthAtom n)
synthDictFromGiven dictTy = do
  givens <- ((HM.elems . fromGivens) <$> getGivens)
  asum $ givens <&> \given -> do
    synthTy <- getSynthType given
    args <- instantiateSynthArgs dictTy synthTy
    case nonEmpty args of
      Nothing -> return given
      Just args' -> return $ DictCon $ InstantiatedGiven given args'

synthDictFromInstance :: DictType n -> SyntherM n (SynthAtom n)
synthDictFromInstance dictTy@(DictType _ targetClass _) = do
  instances <- getInstanceDicts targetClass
  asum $ instances <&> \candidate -> do
    synthTy <- getInstanceType candidate
    args <- instantiateSynthArgs dictTy synthTy
    return $ DictCon $ InstanceDict candidate args

-- TODO: This seems... excessively expensive?
getInstanceType :: InstanceName n -> SyntherM n (SynthType n)
getInstanceType instanceName = do
  InstanceDef className bs params _ <- lookupInstanceDef instanceName
  ClassDef classSourceName _ _ _ _ <- lookupClassDef className
  liftEnvReaderM $ refreshAbs (Abs bs (ListE params)) \bs' (ListE params') -> do
    className' <- sinkM className
    return $ go bs' classSourceName className' params'
  where
    go :: Nest PiBinder n l -> SourceName -> ClassName l -> [Atom l] -> SynthType n
    go bs classSourceName className params = case bs of
      Empty -> SynthDictType $ DictType classSourceName className params
      Nest b rest ->
        let restTy = go rest classSourceName className params
        in SynthPiType $ Abs b restTy
{-# SCC getInstanceType #-}

instantiateSynthArgs :: DictType n -> SynthType n -> SyntherM n [Atom n]
instantiateSynthArgs target synthTy = do
  ListE args <- {-# SCC argSolving #-} (liftExceptAlt =<<) $ liftSolverM $ solveLocal do
    target' <- sinkM target
    synthTy' <- sinkM synthTy
    args <- {-# SCC argInstantiation #-} instantiateSynthArgsRec [] target' emptyInFrag synthTy'
    zonk $ ListE args
  forM args \case
    Con (DictHole _ argTy) -> liftExceptAlt (typeAsSynthType argTy) >>= synthTerm
    arg -> return arg

instantiateSynthArgsRec
  :: EmitsInf n
  => [Atom n] -> DictType n -> SubstFrag AtomSubstVal n l n -> SynthType l -> SolverM n [Atom n]
instantiateSynthArgsRec prevArgsRec dictTy subst synthTy = case synthTy of
  SynthPiType (Abs (PiBinder b argTy arrow) resultTy) -> do
    argTy' <- applySubst subst argTy
    param <- case arrow of
      ImplicitArrow -> Var <$> freshInferenceName argTy'
      ClassArrow -> return $ Con $ DictHole Nothing argTy'
      _ -> error $ "Not a valid arrow type for synthesis: " ++ pprint arrow
    instantiateSynthArgsRec (param:prevArgsRec) dictTy (subst <.> b @> SubstVal param) resultTy
  SynthDictType dictTy' -> do
    unify dictTy =<< applySubst subst dictTy'
    return $ reverse prevArgsRec

instance GenericE Givens where
  type RepE Givens = HashMapE (EKey SynthType) SynthAtom
  fromE (Givens m) = HashMapE m
  {-# INLINE fromE #-}
  toE (HashMapE m) = Givens m
  {-# INLINE toE #-}

instance SinkableE Givens where

-- === Dictionary synthesis traversal ===

liftDictSynthTraverserM
  :: EnvReader m
  => DictSynthTraverserM n n a
  -> m n (Except a)
liftDictSynthTraverserM m =
  liftM runFallibleM $ liftBuilderT do
    runSubstReaderT idSubst $ runDictSynthTraverserM' m

newtype DictSynthTraverserM (i::S) (o::S) (a:: *) =
  DictSynthTraverserM
    { runDictSynthTraverserM' :: SubstReaderT Name (BuilderT FallibleM) i o a }
    deriving ( Functor, Applicative, Monad, SubstReader Name, Builder
             , EnvReader, ScopeReader, EnvExtender, MonadFail, Fallible)

instance GenericTraverser DictSynthTraverserM where
  traverseAtom (Con (DictHole ctx ty)) = do
    ty' <- cheapNormalize =<< substM ty
    addSrcContext ctx $ trySynthTerm ty'
  traverseAtom atom = traverseAtomDefault atom

instance ScopableBuilder (DictSynthTraverserM i) where
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
  :: EmitsInf n
  => (forall l. (EmitsBoth l, Ext n l) => InfererM i l (Atom l))
  -> InfererM i n (Block n)
buildBlockInf cont = buildDeclsInf (cont >>= withType) >>= computeAbsEffects >>= absToBlock
{-# INLINE buildBlockInf #-}

buildLamInf
  :: EmitsInf n
  => NameHint -> Arrow -> Type n
  -> (forall l. (EmitsInf  l, Ext n l) => AtomName l -> InfererM i l (EffectRow l))
  -> (forall l. (EmitsBoth l, Ext n l) => AtomName l -> InfererM i l (Atom l))
  -> InfererM i n (Atom n)
buildLamInf hint arr ty fEff fBody = do
  Abs (b:>_) (PairE effs body) <-
    buildAbsInf hint (LamBinding arr ty) \v -> do
      effs <- fEff v
      body <- withAllowedEffects effs $ buildBlockInf $ sinkM v >>= fBody
      return $ PairE effs body
  return $ Lam $ LamExpr (LamBinder b ty arr effs) body

buildPiAbsInf
  :: (EmitsInf n, SinkableE e, SubstE Name e, HoistableE e)
  => NameHint -> Arrow -> Type n
  -> (forall l. (EmitsInf l, Ext n l) => AtomName l -> InfererM i l (e l))
  -> InfererM i n (Abs PiBinder e n)
buildPiAbsInf hint arr ty body = do
  Abs (b:>_) resultTy <-
    buildAbsInf hint (PiBinding arr ty) \v ->
      withAllowedEffects Pure $ body v
  return $ Abs (PiBinder b ty arr) resultTy

buildPiInf
  :: EmitsInf n
  => NameHint -> Arrow -> Type n
  -> (forall l. (EmitsInf l, Ext n l) => AtomName l -> InfererM i l (EffectRow l, Type l))
  -> InfererM i n (PiType n)
buildPiInf hint arr ty body = do
  Abs (b:>_) (PairE effs resultTy) <-
    buildAbsInf hint (PiBinding arr ty) \v ->
      withAllowedEffects Pure do
        (effs, resultTy) <- body v
        return $ PairE effs resultTy
  return $ PiType (PiBinder b ty arr) effs resultTy

buildTabPiInf
  :: EmitsInf n
  => NameHint -> Type n
  -> (forall l. (EmitsInf l, Ext n l) => AtomName l -> InfererM i l (Type l))
  -> InfererM i n (TabPiType n)
buildTabPiInf hint ty body = do
  Abs (b:>_) resultTy <-
    buildAbsInf hint ty \v ->
      withAllowedEffects Pure $ body v
  return $ TabPiType (b:>ty) resultTy

buildUnaryAltInf
  :: EmitsInf n
  => Type n
  -> (forall l. (EmitsBoth l, Ext n l) => AtomName l -> InfererM i l (Atom l))
  -> InfererM i n (Alt n)
buildUnaryAltInf ty body = do
  bs <- liftBuilder $ singletonBinderNest noHint ty
  buildAltInf bs \[v] -> body v

buildAltInf
  :: EmitsInf n
  => EmptyAbs (Nest Binder) n
  -> (forall l. (EmitsBoth l, Ext n l) => [AtomName l] -> InfererM i l (Atom l))
  -> InfererM i n (Alt n)
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

-- === instances ===

instance PrettyE e => Pretty (UDeclInferenceResult e l) where
  pretty (UDeclResultDone e) = pretty e
  pretty (UDeclResultWorkRemaining block _) = pretty block

instance SinkableE e => SinkableE (UDeclInferenceResult e) where
  sinkingProofE = todoSinkableProof

instance (SubstE Name e, CheckableE e) => CheckableE (UDeclInferenceResult e) where
  checkE (UDeclResultDone e) = UDeclResultDone <$> substM e
  checkE (UDeclResultWorkRemaining block _) = do
    block' <- checkE block
    return $ UDeclResultWorkRemaining block'
                (error "TODO: implement substitution for UDecl")

instance (Monad m, ExtOutMap InfOutMap decls, OutFrag decls)
        => EnvReader (InplaceT InfOutMap decls m) where
  unsafeGetEnv = do
    InfOutMap env _ _ _ <- getOutMapInplaceT
    return env

instance (Monad m, ExtOutMap InfOutMap decls, OutFrag decls)
         => EnvExtender (InplaceT InfOutMap decls m) where
  refreshAbs ab cont = UnsafeMakeInplaceT \env decls ->
    refreshAbsPure (toScope env) ab \_ b e -> do
      let subenv = extendOutMap env $ toEnvFrag b
      (ans, d, _) <- unsafeRunInplaceT (cont b e) subenv emptyOutFrag
      case fabricateDistinctEvidence @UnsafeS of
        Distinct -> do
          let env' = extendOutMap (unsafeCoerceE env) d
          return (ans, catOutFrags (toScope env') decls d, env')
  {-# INLINE refreshAbs #-}

instance BindsEnv InfOutFrag where
  toEnvFrag (InfOutFrag frag _ _) = toEnvFrag frag

instance GenericE SynthType where
  type RepE SynthType = EitherE2 DictType (Abs PiBinder SynthType)
  fromE (SynthDictType d) = Case0 d
  fromE (SynthPiType   t) = Case1 t
  toE (Case0 d) = SynthDictType d
  toE (Case1 t) = SynthPiType t
  toE _ = error "impossible"

instance AlphaEqE       SynthType
instance AlphaHashableE SynthType
instance SinkableE      SynthType
instance HoistableE     SynthType
instance SubstE Name         SynthType
instance SubstE AtomSubstVal SynthType

-- See Note [Confuse GHC] from Simplify.hs
confuseGHC :: EnvReader m => m n (DistinctEvidence n)
confuseGHC = getDistinct
{-# INLINE confuseGHC #-}
