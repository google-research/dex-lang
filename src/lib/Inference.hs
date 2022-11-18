-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module Inference
  ( inferTopUDecl, checkTopUType, inferTopUExpr, applyUDeclAbs
  , trySynthTerm, generalizeDict
  , synthTopBlock, UDeclInferenceResult (..)) where

import Prelude hiding ((.), id)
import Control.Category
import Control.Applicative
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Writer.Strict hiding (Alt)
import Control.Monad.Reader
import Data.Coerce
import Data.Foldable (toList, asum)
import Data.Function ((&))
import Data.Functor (($>), (<&>))
import Data.List (sortOn, intercalate, partition)
import Data.Maybe (fromJust)
import Data.Text.Prettyprint.Doc (Pretty (..))
import Data.Word
import qualified Data.HashMap.Strict as HM
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Unsafe.Coerce as TrulyUnsafe
import GHC.Generics (Generic (..))

import Name
import Builder
import Syntax hiding (State)
import Types.Core
import CheckType (CheckableE (..), checkExtends, checkedApplyClassParams, tryGetType, asNaryPiType, isData)
import QueryType
import PPrint (pprintCanonicalized, prettyBlock)
import CheapReduction
import GenericTraversal
import MTL1
import Interpreter

import LabeledItems
import Err
import Util

-- === Top-level interface ===

checkTopUType :: (Fallible1 m, EnvReader m) => UType n -> m n (CType n)
checkTopUType ty = liftInfererM $ solveLocal $ withApplyDefaults $ checkUType ty
{-# SCC checkTopUType #-}

inferTopUExpr :: (Fallible1 m, EnvReader m) => UExpr n -> m n (CBlock n)
inferTopUExpr e = liftInfererM do
  solveLocal $ buildBlockInf $ withApplyDefaults $ inferSigma noHint e
{-# SCC inferTopUExpr #-}

data UDeclInferenceResult e n =
   UDeclResultDone (e n)  -- used for UDataDefDecl, UInterface and UInstance
 | UDeclResultWorkRemaining (CBlock n) (Abs UDecl e n) -- used for ULet

inferTopUDecl :: (Mut n, Fallible1 m, TopBuilder m, SinkableE e, SubstE Name e)
              => UDecl n l -> e l -> m n (UDeclInferenceResult e n)
inferTopUDecl (UDataDefDecl def tc dcs) result = do
  PairE def' (Abs ddbs' (ListE cbs')) <- liftInfererM $ solveLocal $ inferDataDef def
  defName <- emitDataDef def'
  tc' <- emitTyConName defName =<< tyConDefAsAtom defName
  dcs' <- forM (enumerate cbs') \(i, cbs'') ->
    emitDataConName defName i =<< dataConDefAsAtom (Abs ddbs' cbs'') defName i
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
    val <- checkMaybeAnnExpr (getNameHint p) ann rhs
    -- This is just for type checking. We don't actually generate
    -- pattern-matching code at the top level
    _ <- buildBlockInf do
      val' <- sinkM val
      v <- emitDecl (getNameHint p) PlainLet $ Atom val'
      bindLamPat p v $ return UnitVal
    applyDefaults
    return val
  return $ UDeclResultWorkRemaining block $ Abs decl result
inferTopUDecl (UEffectDecl opTys effName opNames) result = do
  opTys' <- forM opTys $ \opTy -> liftInfererM $ solveLocal $ inferEffOpType opTy
  let effSourceName = uBinderSourceName effName
  let effOpSourceNames = nestToList uBinderSourceName opNames
  let effDef = EffectDef effSourceName (zip effOpSourceNames opTys')
  effName' <- emitEffectDef effDef
  opNames' <-
    forM (enumerate effOpSourceNames) \(i, opName) -> do
      emitEffectOpDef effName' i opName
  let subst = effName @> effName' <.> opNames @@> opNames'
  UDeclResultDone <$> applySubst subst result
-- TODO(alex): handle retEff
inferTopUDecl (UHandlerDecl effName bodyTyArg tyArgs _retEff retTy opDefs handlerName) result =
  do let (InternalName _ effName') = effName
     let handlerSourceName = uBinderSourceName handlerName
     Abs Empty (Abs bodyTyArg' (Abs tyArgs' (retTy' `PairE` retOp' `PairE` ListE ops'))) <-
      liftInfererM $ solveLocal $ buildDeclsInf do
        checkHandlerBodyTyArg bodyTyArg \r -> do
          checkHandlerArgs tyArgs do
            effName'' <- sinkM effName'
            retTy' <- checkUType retTy
            (retOp, ops') <- checkHandlerBody effName'' (sink r) retTy' opDefs
            return (retTy' `PairE` retOp `PairE` ListE ops')
     -- TODO(alex): replace Pure with actual effects
     let handler = HandlerDef effName' bodyTyArg' tyArgs' Pure retTy' ops' retOp'
     handlerName' <- emitHandlerDef handlerSourceName handler
     let subst = handlerName @> handlerName'
     UDeclResultDone <$> applySubst subst result
{-# SCC inferTopUDecl #-}

checkHandlerBody :: EmitsInf o
                 => EffectName o
                 -> CAtomName o
                 -> CType o
                 -> [UEffectOpDef i]
                 -> InfererM i o (CBlock o, [CBlock o])
checkHandlerBody effName r retTy opDefs = do
  EffectDef _ effBody <- lookupEffectDef effName
  let (rets, ops) = partition isReturnOpDef opDefs
  retOp <- case rets of
    [UReturnOpDef retOp] -> do
      retOpTy <- mkRetOpTy r retTy
      buildBlockInf $ checkSigma noHint retOp (sink retOpTy)
    [] -> throw TypeErr "missing return"
    _ -> throw TypeErr "multiple returns"

  ops' <- forM ops (checkHandlerOp effName retTy)
  let (idxs, ops'') = unzip $ sortOn fst ops'
  let opNames = fst $ unzip effBody
  forM_ (repeated idxs) \i ->
    throw TypeErr $ "Duplicate operation: " ++ pprint (opNames!!i)
  forM_ ([0..(length effBody - 1)] `listDiff` idxs) \i ->
    throw TypeErr $ "Missing operation: " ++ pprint (opNames!!i)

  return (retOp, ops'')

checkHandlerOp :: EmitsInf o
               => EffectName o
               -> CType o
               -> UEffectOpDef i
               -> InfererM i o (Int, CBlock o)
checkHandlerOp effName retTy ~(UEffectOpDef pol (InternalName _ opName) opBody) = do
  EffectOpDef effName' (OpIdx opIdx) <- substM opName >>= lookupEffectOpDef
  EffectDef _ ops <- lookupEffectDef effName'
  let (_, EffectOpType pol' opTy) = ops !! opIdx
  when (effName /= effName') $ throw TypeErr
    ("operation " ++ pprint opName ++ " does not belong to effect " ++ pprint effName)
  when (pol /= pol') $ throw TypeErr
    ("operation " ++ pprint opName ++ " was declared with " ++ pprint pol ++ " but defined with " ++ pprint pol')
  -- need expected type of lambda
  Just (NaryPiType bs _ _) <- return $ asNaryPiType opTy
  internalOpTy <- refreshAbs (Abs bs UnitE) \bs' UnitE ->
    -- TODO(alex): Pure is wrong... handle effects from handler def
    return $ naryPiTypeAsType (NaryPiType bs' Pure (sink retTy))
  -- TODO(alex): introduce resume into scope (with correct type)
  -- TODO(alex): handle pol
  opBody' <- buildBlockInf $ checkSigma noHint opBody (sink internalOpTy)
  return (opIdx, opBody')

mkRetOpTy :: (EnvReader m, Fallible1 m) => CAtomName n -> CType n -> m n (CType n)
mkRetOpTy r retTy =
  Pi <$> (liftBuilder $ buildPi noHint PlainArrow (Var r) \_ -> do
    retTy' <- sinkM retTy
    return (Pure, retTy'))

isReturnOpDef :: UEffectOpDef n -> Bool
isReturnOpDef (UReturnOpDef _) = True
isReturnOpDef _ = False

inferEffOpType
  :: EmitsInf o
  => UEffectOpType i
  -> InfererM i o (EffectOpType o)
inferEffOpType (UEffectOpType policy ty) = do
  EffectOpType policy <$> checkUType ty

-- We use this to finish the processing the decl after we've completely
-- evaluated the right-hand side
applyUDeclAbs :: (Mut n, TopBuilder m, SinkableE e, SubstE Name e, MonadIO1 m)
              => Abs UDecl e n -> CAtom n -> m n (e n)
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
                  => SubstFrag (AtomSubstVal CoreIR) i i' o -> m o (SubstFrag Name i i' o)
emitAtomSubstFrag frag = go $ toSubstPairs frag
  where
    go :: (Mut o, TopBuilder m)
       => Nest (SubstPair (AtomSubstVal CoreIR) o) i i' -> m o (SubstFrag Name i i' o)
    go Empty = return emptyInFrag
    go (Nest (SubstPair b val) rest) = do
      v <- case val of
        SubstVal x -> emitTopLet (getNameHint b) PlainLet (Atom x)
        Rename v -> return v
      (b@>v <.>) <$> go rest

-- === Inferer interface ===

class ( MonadFail1 m, Fallible1 m, Catchable1 m, CtxReader1 m, Builder CoreIR m )
      => InfBuilder (m::MonadKind1) where

  -- XXX: we should almost always used the zonking `buildDeclsInf` and variant,
  -- except where it's not possible because the result isn't atom-substitutable,
  -- such as the source map at the top level.
  buildDeclsInfUnzonked
    :: (SinkableE e, HoistableE e, SubstE Name e)
    => EmitsInf n
    => (forall l. (EmitsBoth l, DExt n l) => m l (e l))
    -> m n (Abs (Nest CDecl) e n)

  buildAbsInf
    :: (SinkableE e, HoistableE e, SubstE Name e, Color c, ToBinding binding c)
    => EmitsInf n
    => NameHint -> binding n
    -> (forall l. (EmitsInf l, DExt n l) => Name c l -> m l (e l))
    -> m n (Abs (BinderP c binding) e n)

buildDeclsInf
  :: (SubstE (AtomSubstVal CoreIR) e, SubstE Name e, Solver m, InfBuilder m)
  => (SinkableE e, HoistableE e)
  => EmitsInf n
  => (forall l. (EmitsBoth l, DExt n l) => m l (e l))
  -> m n (Abs (Nest CDecl) e n)
buildDeclsInf cont = buildDeclsInfUnzonked $ cont >>= zonk

type InfBuilder2 (m::MonadKind2) = forall i. InfBuilder (m i)

type IfaceTypeSet = ESet CType

class (SubstReader Name m, InfBuilder2 m, Solver2 m)
      => Inferer (m::MonadKind2) where
  liftSolverMInf :: EmitsInf o => SolverM o a -> m i o a
  gatherUnsolvedInterfaces :: m i o a -> m i o (a, IfaceTypeSet o)
  reportUnsolvedInterface  :: CType o  -> m i o ()
  addDefault :: CAtomName o -> DefaultType -> m i o ()
  getDefaults :: m i o (Defaults o)

applyDefaults :: EmitsInf o => InfererM i o ()
applyDefaults = do
  defaults <- getDefaults
  applyDefault (intDefaults defaults) (BaseTy $ Scalar Int32Type)
  applyDefault (natDefaults defaults) NatTy
  where
    applyDefault ds ty =
      forM_ (nameSetToList ds) \v -> tryConstrainEq (Var v) ty

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

data DefaultType = IntDefault | NatDefault

data Defaults (n::S) = Defaults
  { intDefaults :: NameSet n   -- Set of names that should be defaulted to Int32
  , natDefaults :: NameSet n } -- Set of names that should be defaulted to Nat32

instance Semigroup (Defaults n) where
  Defaults d1 d2 <> Defaults d1' d2' = Defaults (d1 <> d1') (d2 <> d2')

instance Monoid (Defaults n) where
  mempty = Defaults mempty mempty

instance SinkableE Defaults where
  sinkingProofE _ _ = todoSinkableProof
instance HoistableE Defaults where
  freeVarsE (Defaults d1 d2) = d1 <> d2
instance SubstE Name Defaults where
  substE env (Defaults d1 d2) = Defaults (substDefaultSet d1) (substDefaultSet d2)
    where
      substDefaultSet d = freeVarsE $ substE env $ ListE $ nameSetToList @AtomNameC d

zonkDefaults :: SolverSubst n -> Defaults n -> Defaults n
zonkDefaults s (Defaults d1 d2) =
  Defaults (zonkDefaultSet d1) (zonkDefaultSet d2)
  where
    zonkDefaultSet d = flip foldMap (nameSetToList @AtomNameC d) \v ->
      case lookupSolverSubst s v of
        Rename   v'       -> freeVarsE v'
        SubstVal (Var v') -> freeVarsE v'
        _ -> mempty

data InfOutFrag (n::S) (l::S) = InfOutFrag (InfEmissions n l) (Defaults l) (SolverSubst l)

type InfEmission  = EitherE (DeclBinding CoreIR) (SolverBinding CoreIR)
type InfEmissions = RNest (BinderP AtomNameC InfEmission)

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
  emptyOutFrag = InfOutFrag REmpty mempty emptySolverSubst
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
      let newEnv = bindings `extendOutMap` frag
      -- As an optimization, only do the zonking for the new stuff.
      let (zonkedUn, zonkedEnv) = zonkUnsolvedEnv (sink ss) newUn newEnv
      InfOutMap zonkedEnv (sink ss) (sink dd) (sink oldUn <> zonkedUn)

newtype UnsolvedEnv (n::S) =
  UnsolvedEnv { fromUnsolvedEnv :: S.Set (CAtomName n) }
  deriving (Semigroup, Monoid)

instance SinkableE UnsolvedEnv where
  sinkingProofE = todoSinkableProof

getAtomNames :: Distinct l => EnvFrag n l -> S.Set (CAtomName l)
getAtomNames frag = S.fromList $ nameSetToList $ toNameSet $ toScopeFrag frag

-- TODO: zonk the allowed effects and synth candidates in the bindings too
-- TODO: the reason we need this is that `getType` uses the bindings to obtain
-- type information, and we need this information when we emit decls. For
-- example, if we emit `f x` and we don't know that `f` has a type of the form
-- `a -> b` then `getType` will crash. But we control the inference-specific
-- implementation of `emitDecl`, so maybe we could instead do something like
-- emit a fresh inference variable in the case thea `getType` fails.
-- XXX: It might be tempting to add a check for empty solver substs here,
-- but please don't do that! We use this function to filter overestimates of
-- UnsolvedEnv, and for performance reasons we should do that even when the
-- SolverSubst is empty.
zonkUnsolvedEnv :: Distinct n => SolverSubst n -> UnsolvedEnv n -> Env n
                -> (UnsolvedEnv n, Env n)
zonkUnsolvedEnv ss unsolved env =
  flip runState env $ execWriterT do
    forM_ (S.toList $ fromUnsolvedEnv unsolved) \v -> do
      flip lookupEnvPure v <$> get >>= \case
        AtomNameBinding rhs -> do
          let rhs' = zonkWithOutMap (InfOutMap env ss mempty mempty) rhs
          modify $ updateEnv v $ AtomNameBinding rhs'
          let rhsHasInfVars = runEnvReaderM env $ hasInferenceVars rhs'
          when rhsHasInfVars $ tell $ UnsolvedEnv $ S.singleton v

-- TODO: Wouldn't it be faster to carry the set of inference-emitted names in the out map?
hasInferenceVars :: (EnvReader m, HoistableE e) => e n -> m n Bool
hasInferenceVars e = liftEnvReaderM $ anyInferenceVars $ freeAtomVarsList e
{-# INLINE hasInferenceVars #-}

anyInferenceVars :: [CAtomName n] -> EnvReaderM n Bool
anyInferenceVars = \case
  [] -> return False
  (v:vs) -> isInferenceVar v >>= \case
    True  -> return True
    False -> anyInferenceVars vs

isInferenceVar :: EnvReader m => CAtomName n -> m n Bool
isInferenceVar v = lookupEnv v >>= \case
  AtomNameBinding (SolverBound _) -> return True
  _                               -> return False

instance ExtOutMap InfOutMap InfOutFrag where
  extendOutMap m (InfOutFrag em ds' ss') =
    -- There's no point in extending the subst or zonking unsolved when
    -- there are no new solutions.
    case substIsEmpty ss' of
      True  -> InfOutMap env   ss   ds'' us
      False -> InfOutMap env'' ss'' ds'' us''
        where
          (us'', env'') = zonkUnsolvedEnv ss' us env
          ss'' = catSolverSubsts (toScope env) ss ss'
    where
      InfOutMap env ss ds us = m `extendOutMap` toEnvFrag em
      ds'' = sink ds <> ds'

substIsEmpty :: SolverSubst n -> Bool
substIsEmpty (SolverSubst subst) = M.null subst

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
  (InfOutFrag REmpty _ _, (result, _)) <-
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

newtype InfDeclEmission (n::S) (l::S) = InfDeclEmission (BinderP AtomNameC InfEmission n l)
instance ExtOutMap InfOutMap InfDeclEmission where
  extendOutMap env (InfDeclEmission d) = env `extendOutMap` toEnvFrag d
  {-# INLINE extendOutMap #-}
instance ExtOutFrag InfOutFrag InfDeclEmission where
  extendOutFrag (InfOutFrag ems ds ss) (InfDeclEmission em) =
    withSubscopeDistinct em $ InfOutFrag (RNest ems em) (sink ds) (sink ss)
  {-# INLINE extendOutFrag #-}

emitInfererM :: Mut o => NameHint -> InfEmission o -> InfererM i o (CAtomName o)
emitInfererM hint emission = do
  InfererM $ SubstReaderT $ lift $ lift11 $ freshExtendSubInplaceT hint \b ->
    (InfDeclEmission (b :> emission), binderName b)
{-# INLINE emitInfererM #-}

instance Solver (InfererM i) where
  extendSolverSubst v ty = do
   InfererM $ SubstReaderT $ lift $ lift11 $
    void $ extendTrivialInplaceT $
      InfOutFrag REmpty mempty (singletonSolverSubst v ty)
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
      REmpty -> return result
      RNest _ (_:>RightE (InfVarBound _ ctx)) -> do
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

  addDefault v defaultType =
    InfererM $ SubstReaderT $ lift $ lift11 $
      extendTrivialInplaceT $ InfOutFrag REmpty defaults emptySolverSubst
    where
      defaults = case defaultType of
        IntDefault -> Defaults (freeVarsE v) mempty
        NatDefault -> Defaults mempty (freeVarsE v)

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
      FailIfRequired -> do
        givensStr <- do
          givens <- (HM.elems . fromGivens) <$> givensFromEnv
          mapM getType givens >>= \case
            [] -> return ""
            givensTys -> return $ "\nGiven: " ++ pprint givensTys
        throw TypeErr $ "Couldn't synthesize a class dictionary for: "
          ++ pprintCanonicalized iface ++ givensStr
      GatherRequired ds -> put $ GatherRequired $ eSetSingleton iface <> ds

instance Builder CoreIR (InfererM i) where
  emitDecl hint ann expr = do
    -- This zonking, and the zonking of the bindings elsewhere, is only to
    -- prevent `getType` from failing. But maybe we should just catch the
    -- failure if it occurs and generate a fresh inference name for the type in
    -- that case?
    expr' <- zonk expr
    ty <- getType expr'
    emitInfererM hint $ LeftE $ DeclBinding ann ty expr'
  {-# INLINE emitDecl #-}

type InferenceNameBinders = Nest (BinderP AtomNameC (SolverBinding CoreIR))

-- When we finish building a block of decls we need to hoist the local solver
-- information into the outer scope. If the local solver state mentions local
-- variables which are about to go out of scope then we emit a "escaped scope"
-- error. To avoid false positives, we clean up as much dead (i.e. solved)
-- solver state as possible.
hoistThroughDecls
  :: ( SubstE Name e, HoistableE e, Fallible1 m, ScopeReader m, EnvExtender m)
  => InfOutFrag n l
  ->   e l
  -> m n (Abs InfOutFrag (Abs (Nest CDecl) e) n)
hoistThroughDecls outFrag result = do
  scope <- unsafeGetScope
  refreshAbs (Abs outFrag result) \outFrag' result' -> do
    liftExcept $ hoistThroughDecls' scope outFrag' result'
{-# INLINE hoistThroughDecls #-}

hoistThroughDecls'
  :: (HoistableE e, Distinct l)
  => Scope n
  -> InfOutFrag n l
  ->   e l
  -> Except (Abs InfOutFrag (Abs (Nest CDecl) e) n)
hoistThroughDecls' scope (InfOutFrag emissions defaults subst) result = do
  withSubscopeDistinct emissions do
    HoistedSolverState infVars defaults' subst' decls result' <-
      hoistInfStateRec scope emissions emptyInferenceNameBindersFV
        (zonkDefaults subst defaults) (UnhoistedSolverSubst emptyOutFrag subst) Empty result
    let hoistedInfFrag = InfOutFrag (infNamesToEmissions infVars) defaults' subst'
    return $ Abs hoistedInfFrag $ Abs decls result'

data HoistedSolverState e n where
  HoistedSolverState
    :: InferenceNameBinders n l1
    ->   Defaults l1
    ->   SolverSubst l1
    ->   Nest CDecl l1 l2
    ->     e l2
    -> HoistedSolverState e n

-- XXX: Be careful how you construct DelayedSolveNests! When the substitution is
-- applied, the pieces are concatenated through regular map concatenation, not
-- through recursive substitutions as in catSolverSubsts! This is safe to do when
-- the individual SolverSubsts come from a projection of a larger SolverSubst,
-- which is how we use them in `hoistInfStateRec`.
type DelayedSolveNest (b::B) (n::S) (l::S) = Nest (EitherB b (LiftB SolverSubst)) n l

resolveDelayedSolve :: Distinct l => Scope n -> SolverSubst n -> DelayedSolveNest CDecl n l -> Nest CDecl n l
resolveDelayedSolve scope subst = \case
  Empty -> Empty
  Nest (RightB (LiftB sfrag)) rest -> resolveDelayedSolve scope (subst `unsafeCatSolverSubst` sfrag) rest
  Nest (LeftB  (Let b rhs)  ) rest ->
    withSubscopeDistinct rest $ withSubscopeDistinct b $
      Nest (Let b (applySolverSubstE scope subst rhs)) $
        resolveDelayedSolve (scope `extendOutMap` toScopeFrag b) (sink subst) rest
  where
    unsafeCatSolverSubst :: SolverSubst n -> SolverSubst n -> SolverSubst n
    unsafeCatSolverSubst (SolverSubst a) (SolverSubst b) = SolverSubst $ a <> b

data InferenceNameBindersFV (n::S) (l::S) = InferenceNameBindersFV (NameSet n) (InferenceNameBinders n l)
instance BindsNames InferenceNameBindersFV where
  toScopeFrag = toScopeFrag . dropInferenceNameBindersFV
instance ProvesExt InferenceNameBindersFV where
  toExtEvidence = toExtEvidence . dropInferenceNameBindersFV
instance HoistableB InferenceNameBindersFV where
  freeVarsB (InferenceNameBindersFV fvs _) = fvs

emptyInferenceNameBindersFV :: InferenceNameBindersFV n n
emptyInferenceNameBindersFV = InferenceNameBindersFV mempty Empty

dropInferenceNameBindersFV :: InferenceNameBindersFV n l -> InferenceNameBinders n l
dropInferenceNameBindersFV (InferenceNameBindersFV _ bs) = bs

prependNameBinder
  :: BinderP AtomNameC (SolverBinding CoreIR) n q
  -> InferenceNameBindersFV q l -> InferenceNameBindersFV n l
prependNameBinder b (InferenceNameBindersFV fvs bs) =
  InferenceNameBindersFV (freeVarsB b <> hoistFilterNameSet b fvs) (Nest b bs)

-- XXX: Stashing Distinct here is a little naughty, since that's generally not allowed.
-- Here it should be ok, because it's only used in hoistInfStateRec, which doesn't emit.
data UnhoistedSolverSubst (n::S) where
  UnhoistedSolverSubst :: Distinct l => ScopeFrag n l -> SolverSubst l -> UnhoistedSolverSubst n

delayedHoistSolverSubst :: BindsNames b => b n l -> UnhoistedSolverSubst l -> UnhoistedSolverSubst n
delayedHoistSolverSubst b (UnhoistedSolverSubst frag s) = UnhoistedSolverSubst (toScopeFrag b >>> frag) s

hoistSolverSubst :: UnhoistedSolverSubst n -> HoistExcept (SolverSubst n)
hoistSolverSubst (UnhoistedSolverSubst frag s) = hoist frag s

-- TODO: Instead of delaying the solve, compute the most-nested scope once
-- and then use it for all _eager_ substitutions while hoisting! Using a super-scope
-- for substitution shouldn't be a problem!
hoistInfStateRec
  :: forall n l l1 l2 e. (Distinct n, Distinct l2, HoistableE e)
  => Scope n -> InfEmissions n l
  -> InferenceNameBindersFV l l1 -> Defaults l1 -> UnhoistedSolverSubst l1
  -> DelayedSolveNest CDecl l1 l2 -> e l2
  -> Except (HoistedSolverState e n)
hoistInfStateRec scope emissions !infVars defaults !subst decls e = case emissions of
 REmpty -> do
  subst' <- liftHoistExcept $ hoistSolverSubst subst
  let decls' = withSubscopeDistinct decls $
                 resolveDelayedSolve (scope `extendOutMap` toScopeFrag infVars) subst' decls
  return $ HoistedSolverState (dropInferenceNameBindersFV infVars) defaults subst' decls' e
 RNest rest (b :> infEmission) -> do
  withSubscopeDistinct decls do
    case infEmission of
      RightE binding@(InfVarBound _ _) -> do
        UnhoistedSolverSubst frag (SolverSubst substMap) <- return subst
        let vHoist :: CAtomName l1 = withSubscopeDistinct infVars $ sink $ binderName b  -- binder name at l1
        let vUnhoist = withExtEvidence frag $ sink vHoist                               -- binder name below frag
        case M.lookup vUnhoist substMap of
          -- Unsolved inference variables are just gathered as they are.
          Nothing ->
            hoistInfStateRec scope rest (prependNameBinder (b:>binding) infVars)
                             defaults subst decls e
          -- If a variable is solved, we eliminate it.
          Just bSolutionUnhoisted -> do
            bSolution <- liftHoistExcept $ hoist frag bSolutionUnhoisted
            case exchangeBs $ PairB b infVars of
              -- This used to be accepted by the code at some point (and handled the same way
              -- as the Nothing) branch above, but I don't understand why. We don't even seem
              -- to be exercising it anyway, so throw a not implemented error for now.
              HoistFailure _ -> throw NotImplementedErr "Unzonked unsolved variables"
              HoistSuccess (PairB infVars' b') -> do
                let defaults' = hoistDefaults b' defaults
                let bZonkedDecls = Nest (RightB (LiftB $ SolverSubst $ M.singleton vHoist bSolution)) decls
#ifdef DEX_DEBUG
                -- Hoist the subst eagerly, unlike the unsafe implementation.
                hoistedSubst@(SolverSubst hoistMap) <- liftHoistExcept $ hoistSolverSubst subst
                let subst' = withSubscopeDistinct b' $ UnhoistedSolverSubst (toScopeFrag b') $
                               SolverSubst $ M.delete vHoist hoistMap
                -- Zonk the decls with `v @> bSolution` to make sure hoisting will succeed.
                -- This is quadratic, which is why we don't do this in the fast implementation!
                let allEmissions = RNest rest (b :> infEmission)
                let declsScope = withSubscopeDistinct infVars $
                      (scope `extendOutMap` toScopeFrag allEmissions) `extendOutMap` toScopeFrag infVars
                let resolvedDecls = resolveDelayedSolve declsScope hoistedSubst bZonkedDecls
                PairB resolvedDecls' b'' <- liftHoistExcept $ exchangeBs $ PairB b' resolvedDecls
                let decls' = fmapNest LeftB resolvedDecls'
                -- NB: We assume that e is hoistable above e! This has to be taken
                -- care of by zonking the result before this function is entered.
                e' <- liftHoistExcept $ hoist b'' e
                withSubscopeDistinct b'' $
                  hoistInfStateRec scope rest infVars' defaults' subst' decls' e'
#else
                -- SolverSubst should be recursively zonked, so any v that's a member
                -- should never appear in an rhs. Hence, deleting the entry corresponding to
                -- v should hoist the substitution above b'.
                let subst' = unsafeCoerceE $ UnhoistedSolverSubst frag $ SolverSubst $ M.delete vUnhoist substMap
                -- Applying the substitution `v @> bSolution` would eliminate `b` from decls, so this
                -- is equivalent to hoisting above b'. This is of course not reflected in the type
                -- system, which is why we use unsafe coercions.
                let decls' = unsafeCoerceB bZonkedDecls
                -- This is much more sketchy, but it reflects the e-hoistability assumption
                -- that our safe implementation makes as well. Except here it's obviously unchecked.
                let e' :: e UnsafeS = unsafeCoerceE e
                Distinct <- return $ fabricateDistinctEvidence @UnsafeS
                hoistInfStateRec scope rest infVars' defaults' subst' decls' e'
#endif
      RightE (SkolemBound _) -> do
#ifdef DEX_DEBUG
        PairB infVars' b' <- liftHoistExcept' "Skolem leak?" $ exchangeBs $ PairB b infVars
        defaults' <- liftHoistExcept' "Skolem leak?" $ hoist b' defaults
        let subst' = delayedHoistSolverSubst b' subst
        PairB decls' b'' <- liftHoistExcept' "Skolem leak?" $ exchangeBs $ PairB b' decls
        e' <- liftHoistExcept' "Skolem leak?" $ hoist b'' e
        withSubscopeDistinct b'' $ hoistInfStateRec scope rest infVars' defaults' subst' decls' e'
#else
        -- Skolem vars are only instantiated in unification, and we're very careful to
        -- never let them leak into the types of inference vars emitted while unifying
        -- and into the solver subst.
        Distinct <- return $ fabricateDistinctEvidence @UnsafeS
        hoistInfStateRec @n @UnsafeS @UnsafeS @UnsafeS
          scope
          (unsafeCoerceB rest) (unsafeCoerceB infVars)
          (unsafeCoerceE defaults) (unsafeCoerceE subst)
          (unsafeCoerceB decls) (unsafeCoerceE e)
#endif
      LeftE emission -> do
        -- Move the binder below all unsolved inference vars. Failure to do so is
        -- an inference error --- a variable cannot be solved once we exist the scope
        -- of all variables it mentions in its type.
        -- TODO: Shouldn't this be an ambiguous type error?
        PairB infVars' (b':>emission') <- liftHoistExcept $ exchangeBs (PairB (b:>emission) infVars)
        -- Now, those are real leakage errors. We never want to leak this var through a solution!
        -- But since we delay hoisting, they will only be raised later.
        let subst' = delayedHoistSolverSubst b' subst
        let defaults' = hoistDefaults b' defaults
        let decls' = Nest (LeftB (Let b' emission')) decls
        hoistInfStateRec scope rest infVars' defaults' subst' decls' e

hoistRequiredIfaces :: BindsNames b => b n l -> RequiredIfaces l -> RequiredIfaces n
hoistRequiredIfaces bs = \case
  FailIfRequired    -> FailIfRequired
  GatherRequired ds -> GatherRequired $ eSetFromList $ eSetToList ds & mapMaybe \d -> case hoist bs d of
    HoistSuccess d' -> Just d'
    HoistFailure _  -> Nothing

hoistDefaults :: BindsNames b => b n l -> Defaults l -> Defaults n
hoistDefaults b (Defaults d1 d2) = Defaults (hoistFilterNameSet b d1)
                                            (hoistFilterNameSet b d2)

infNamesToEmissions :: InferenceNameBinders n l -> InfEmissions n l
infNamesToEmissions = go REmpty
 where
   go :: InfEmissions n q -> InferenceNameBinders q l -> InfEmissions n l
   go acc = \case
     Empty -> acc
     Nest (b:>binding) rest -> go (RNest acc (b:>RightE binding)) rest

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

type SigmaType = CType  -- may     start with an implicit lambda
type RhoType   = CType  -- doesn't start with an implicit lambda
data RequiredTy (e::E) (n::S) = Check (e n)
                              | Infer
                                deriving Show

checkSigma :: EmitsBoth o
           => NameHint -> UExpr i -> SigmaType o -> InfererM i o (CAtom o)
checkSigma hint expr sTy = confuseGHC >>= \_ -> case sTy of
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
              checkSigma hint expr bodyTy
  _ -> checkOrInferRho hint expr (Check sTy)

inferSigma :: EmitsBoth o => NameHint -> UExpr i -> InfererM i o (CAtom o)
inferSigma hint (WithSrcE pos expr) = case expr of
  ULam lam@(ULamExpr ImplicitArrow _ _) ->
    addSrcContext pos $ inferULam Pure lam
  -- TODO: Should we be handling class arrows here?
  _ -> inferRho hint (WithSrcE pos expr)

checkRho :: EmitsBoth o =>
  NameHint -> UExpr i -> RhoType o -> InfererM i o (CAtom o)
checkRho hint expr ty = checkOrInferRho hint expr (Check ty)
{-# INLINE checkRho #-}

inferRho :: EmitsBoth o =>
  NameHint -> UExpr i -> InfererM i o (CAtom o)
inferRho hint expr = checkOrInferRho hint expr Infer
{-# INLINE inferRho #-}

instantiateSigma :: EmitsBoth o => CAtom o -> InfererM i o (CAtom o)
instantiateSigma f = fst <$> instantiateSigmaWithArgs f

instantiateSigmaWithArgs :: EmitsBoth o => CAtom o -> InfererM i o (CAtom o, [CAtom o])
instantiateSigmaWithArgs f = do
  ty <- tryGetType f
  args <- getImplicitArgs ty
  (,args) <$> naryApp f args

getImplicitArgs :: EmitsInf o => CType o -> InfererM i o [CAtom o]
getImplicitArgs ty = case ty of
  Pi (PiType b _ _) ->
    getImplicitArg b >>= \case
      Nothing -> return []
      Just arg -> do
        appTy <- getAppType ty [arg]
        (arg:) <$> getImplicitArgs appTy
  _ -> return []

getImplicitArg :: EmitsInf o => PiBinder CoreIR o o' -> InfererM i o (Maybe (CAtom o))
getImplicitArg (PiBinder _ argTy arr) = case arr of
  ImplicitArrow -> Just <$> freshType argTy
  ClassArrow -> do
    ctx <- srcPosCtx <$> getErrCtx
    return $ Just $ Con $ DictHole (AlwaysEqual ctx) argTy
  _ -> return Nothing

-- The name hint names the object being computed
checkOrInferRho :: forall i o. EmitsBoth o
                => NameHint -> UExpr i
                -> RequiredTy RhoType o -> InfererM i o (CAtom o)
checkOrInferRho hint (WithSrcE pos expr) reqTy = do
 addSrcContext pos $ confuseGHC >>= \_ -> case expr of
  UVar ~(InternalName _ v) -> do
    substM v >>= inferUVar >>= instantiateSigma >>= matchRequirement
  ULam (ULamExpr ImplicitArrow (UPatAnn p ann) body) -> do
    argTy <- checkAnn ann
    v <- freshInferenceName argTy
    bindLamPat p v $ checkOrInferRho hint body reqTy
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
    ixTy <- asIxType ty'
    matchRequirement $ TabLam $ TabLamExpr (b':>ixTy) body'
  UFor dir (UForExpr b body) -> do
    allowedEff <- getAllowedEffects
    let uLamExpr = ULamExpr PlainArrow b body
    lam@(Lam (LamExpr b' _)) <- case reqTy of
      Check (TabPi tabPiTy) -> do
        lamPiTy <- buildForTypeFromTabType allowedEff tabPiTy
        checkULam uLamExpr lamPiTy
      Check _ -> inferULam allowedEff uLamExpr
      Infer   -> inferULam allowedEff uLamExpr
    IxType _ ixDict <- asIxType $ binderType b'
    result <- liftM Var $ emitHinted hint $ Hof $ For dir ixDict lam
    matchRequirement result
  UApp _ _ -> do
    let (f, args) = asNaryApp $ WithSrcE pos expr
    f' <- inferFunNoInstantiation f >>= zonk
    inferNaryApp (srcPos f) f' (NE.fromList args) >>= matchRequirement
  UTabApp _ _ -> do
    let (tab, args) = asNaryTabApp $ WithSrcE pos expr
    tab' <- inferRho noHint tab >>= zonk
    inferNaryTabApp (srcPos tab) tab' (NE.fromList args) >>= matchRequirement
  UPi (UPiExpr arr (UPatAnn (WithSrcB pos' pat) ann) effs ty) -> do
    -- TODO: make sure there's no effect if it's an implicit or table
    -- arrow
    piTy <- checkAnnWithMissingDicts ann \missingDs getAnnType -> do
      -- Note that we can't automatically quantify class Pis, because
      -- the class dict might have been bound on the rhs of a let and
      -- it would get bound to the inserted arguments instead of the
      -- desired dict. It's not a fundemental limitation of our
      -- automatic quantification, but it's simpler not to deal with
      -- that for now.
      let checkNoMissing = (addSrcContext pos'
           $ unless (null $ eSetToList missingDs) $ throw TypeErr
           $ "Couldn't synthesize a class dictionary for: "
             ++ pprint (head $ eSetToList missingDs))
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
                return $ PairE (Eff effs') ty'
            cheapReduceWithDecls decls result >>= \case
              (Just (PairE (Eff effs') ty'), DictTypeHoistSuccess, []) -> return $ (effs', ty')
              _ -> throw TypeErr $ "Can't reduce type expression: " ++
                     docAsStr (prettyBlock decls $ snd $ fromPairE result)
    matchRequirement $ Pi piTy
  UTabPi (UTabPiExpr (UPatAnn (WithSrcB pos' pat) ann) ty) -> do
    ann' <- asIxType =<< checkAnn ann
    piTy <- addSrcContext pos' case pat of
      UPatBinder UIgnore ->
        buildTabPiInf noHint ann' \_ -> checkUType ty
      _ -> buildTabPiInf (getNameHint pat) ann' \v -> do
        Abs decls piResult <- buildDeclsInf do
          v' <- sinkM v
          bindLamPat (WithSrcB pos' pat) v' $ checkUType ty
        cheapReduceWithDecls decls piResult >>= \case
          (Just ty', _, _) -> return ty'
          -- TODO: handle phantom constraints!
          _ -> throw TypeErr $ "Can't reduce type expression: " ++
                 docAsStr (prettyBlock decls piResult)
    matchRequirement $ TabPi piTy
  UDepPairTy (UDepPairType (UPatAnn (WithSrcB pos' pat) ann) rhs) -> do
    ann' <- checkAnn ann
    depPairTy <- addSrcContext pos' do
      buildDepPairTyInf (getNameHint pat) ann' \v -> do
        Abs decls result <- buildDeclsInf do
          v' <- sinkM v
          bindLamPat (WithSrcB pos' pat) v' (checkUType rhs)
        cheapReduceWithDecls decls result >>= \case
          (Just rhs', DictTypeHoistSuccess, []) -> return rhs'
          _ -> throw TypeErr $ "Can't reduce type expression: " ++
                 docAsStr (prettyBlock decls result)
    matchRequirement $ DepPairTy depPairTy
  UDepPair lhs rhs -> do
    case reqTy of
      Check (DepPairTy ty@(DepPairType (_ :> lhsTy) _)) -> do
        lhs' <- checkSigmaDependent noHint lhs lhsTy
        rhsTy <- instantiateDepPairTy ty lhs'
        rhs' <- checkSigma noHint rhs rhsTy
        return $ DepPair lhs' rhs' ty
      _ -> throw TypeErr $ "Can't infer the type of a dependent pair; please annotate it"
  UDecl (UDeclExpr (ULet letAnn (UPatAnn p ann) rhs) body) -> do
    val <- checkMaybeAnnExpr (getNameHint p) ann rhs
    var <- emitDecl (getNameHint p) letAnn $ Atom val
    bindLamPat p var $ checkOrInferRho hint body reqTy
  UDecl _ -> throw CompilerErr "not a local decl"
  UCase scrut alts -> do
    scrut' <- inferRho noHint scrut
    scrutTy <- getType scrut'
    reqTy' <- case reqTy of
      Infer -> freshType TyKind
      Check req -> return req
    alts' <- mapM (checkCaseAlt reqTy' scrutTy) alts
    scrut'' <- zonk scrut'
    buildSortedCase scrut'' alts' reqTy'
  UTabCon xs -> inferTabCon hint xs reqTy >>= matchRequirement
  UHole -> case reqTy of
    Infer -> throw MiscErr "Can't infer type of hole"
    Check ty -> freshType ty
  UTypeAnn val ty -> do
    ty' <- zonk =<< checkUType ty
    val' <- checkSigma hint val ty'
    matchRequirement val'
  UPrimExpr (OpExpr (MonoLiteral (WithSrcE _ l))) -> case l of
    UIntLit x -> matchRequirement $ Con $ Lit $ Int32Lit $ fromIntegral x
    UNatLit x -> matchRequirement $ Con $ Lit $ Word32Lit $ fromIntegral x
    _ -> throw MiscErr "argument to %monoLit must be a literal"
  UPrimExpr (OpExpr (ExplicitApply f x)) -> do
    f' <- inferFunNoInstantiation f
    x' <- inferRho noHint x
    (liftM Var $ emitHinted hint $ App f' (x':|[])) >>= matchRequirement
  UPrimExpr (OpExpr (ProjBaseNewtype x)) -> do
    x' <- inferRho hint x >>= emitAtomToName hint
    return $ unwrapBaseNewtype $ Var x'
  UPrimExpr prim -> do
    prim' <- forM prim \x -> do
      xBlock <- buildBlockInf $ inferRho noHint x
      getType xBlock >>= \case
        TyKind -> cheapReduce xBlock >>= \case
          (Just reduced, DictTypeHoistSuccess, []) -> return reduced
          _ -> throw CompilerErr "Type args to primops must be reducible"
        _ -> emitBlock xBlock
    val <- case prim' of
      TCExpr  e -> return $ TC e
      ConExpr e -> return $ Con e
      OpExpr  e -> Var <$> emitHinted hint (Op e)
      HofExpr e -> Var <$> emitHinted hint (Hof e)
    matchRequirement val
  ULabel name -> matchRequirement $ Con $ LabelCon name
  URecord elems ->
    matchRequirement =<< resolveDelay =<< foldM go (Nothing, mempty) (reverse elems)
    where
      go :: EmitsInf o
         => (Maybe (CAtom o), LabeledItems (CAtom o)) -> UFieldRowElem i
         -> InfererM i o (Maybe (CAtom o), LabeledItems (CAtom o))
      go delayedRec = \case
        UStaticField l e -> do
          e' <- inferRho noHint e
          return (rec, labeledSingleton l e' <> delayItems)
          where (rec, delayItems) = delayedRec
        UDynField    v e -> do
          v' <- checkRho noHint (WithSrcE Nothing $ UVar v) (TC LabelType)
          e' <- inferRho noHint e
          rec' <- emitOp . RecordConsDynamic v' e' =<< resolveDelay delayedRec
          return (Just rec', mempty)
        UDynFields   v -> do
          anyFields <- freshInferenceName LabeledRowKind
          v' <- checkRho noHint v $ RecordTyWithElems [DynFields anyFields]
          case delayedRec of
            (Nothing, delayItems) | null delayItems -> return (Just v', mempty)
            _ -> do
              rec' <- emitOp . RecordCons v' =<< resolveDelay delayedRec
              return (Just rec', mempty)

      resolveDelay :: EmitsInf o
                   => (Maybe (CAtom o), LabeledItems (CAtom o)) -> InfererM i o (CAtom o)
      resolveDelay = \case
        (Nothing , delayedItems) -> getRecord delayedItems
        (Just rec, delayedItems) -> case null delayedItems of
          True  -> return rec
          False -> do
            dr <- getRecord delayedItems
            emitOp $ RecordCons dr rec
        where
          getRecord delayedItems = do
            tys <- traverse getType delayedItems
            return $ Record tys $ toList delayedItems
  UVariant labels@(LabeledItems lmap) label value -> do
    value' <- inferRho noHint value
    ty <- getType value'
    unless (M.size lmap == 0 || M.size lmap == 1) $ throw TypeErr
      "All labels in a variant literal should use the same field name."
    prevTys <- mapM (const $ freshType TyKind) labels
    rest <- freshInferenceName LabeledRowKind
    let items = prevTys <> labeledSingleton label ty
    let extItems = Ext items $ Just rest
    let i = length $ lookupLabel labels label
    matchRequirement =<< emitOp (VariantMake (VariantTy extItems) label i value')
  URecordTy   elems -> matchRequirement =<< RecordTyWithElems . concat <$> mapM inferFieldRowElem elems
  ULabeledRow elems -> matchRequirement =<< LabeledRow . fieldRowElemsFromList . concat <$> mapM inferFieldRowElem elems
  UVariantTy row -> matchRequirement =<< VariantTy <$> checkExtLabeledRow row
  UVariantLift labels value -> do
    row <- freshInferenceName LabeledRowKind
    value' <- zonk =<< (checkRho noHint value $ VariantTy $ Ext NoLabeledItems $ Just row)
    prev <- mapM (\() -> freshType TyKind) labels
    matchRequirement =<< emitOp (VariantLift prev value')
  UNatLit x -> do
    lookupSourceMap "from_unsigned_integer" >>= \case
      Nothing ->
        -- fallback for missing protolude
        matchRequirement $ Con $ Lit $ Word32Lit $ fromIntegral x
      Just (UMethodVar fromNatMethod) -> do
        ~(MethodBinding _ _ fromNat) <- lookupEnv fromNatMethod
        (fromNatInst, (Var resTyVar:_)) <- instantiateSigmaWithArgs fromNat
        addDefault resTyVar NatDefault
        let n64Atom = Con $ Lit $ Word64Lit $ fromIntegral x
        result <- matchRequirement =<< app fromNatInst n64Atom
        return result
      Just _ -> error "not a method"
  UIntLit x  -> do
    lookupSourceMap "from_integer" >>= \case
      Nothing ->
        -- fallback for missing protolude
        matchRequirement $ Con $ Lit $ Int32Lit $ fromIntegral x
      Just (UMethodVar fromIntMethod) -> do
        ~(MethodBinding _ _ fromInt) <- lookupEnv fromIntMethod
        (fromIntInst, (Var resTyVar:_)) <- instantiateSigmaWithArgs fromInt
        addDefault resTyVar IntDefault
        let i64Atom = Con $ Lit $ Int64Lit $ fromIntegral x
        result <- matchRequirement =<< app fromIntInst i64Atom
        return result
      Just _ -> error "not a method"
  UFloatLit x -> matchRequirement $ Con $ Lit  $ Float32Lit $ realToFrac x
  -- TODO: Make sure that this conversion is not lossy!
  where
    matchRequirement :: CAtom o -> InfererM i o (CAtom o)
    matchRequirement x = return x <*
      case reqTy of
        Infer -> return ()
        Check req -> do
          ty <- getType x
          constrainEq req ty
    {-# INLINE matchRequirement #-}

inferFieldRowElem :: EmitsBoth o => UFieldRowElem i -> InfererM i o [FieldRowElem CoreIR o]
inferFieldRowElem = \case
  UStaticField l ty -> do
    ty' <- checkUType ty
    return [StaticFields $ labeledSingleton l ty']
  UDynField    v ty -> do
    ty' <- checkUType ty
    checkRho noHint (WithSrcE Nothing $ UVar v) (TC LabelType) >>= \case
      Con (LabelCon l) -> return [StaticFields $ labeledSingleton l ty']
      Var v'           -> return [DynField v' ty']
      _                -> error "Unexpected Label atom"
  UDynFields   v    -> checkRho noHint v LabeledRowKind >>= \case
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
inferFunNoInstantiation :: EmitsBoth o => UExpr i -> InfererM i o (CAtom o)
inferFunNoInstantiation expr@(WithSrcE pos expr') = do
 addSrcContext pos $ case expr' of
  UVar ~(InternalName _ v) -> do
    -- XXX: deliberately no instantiation!
    substM v >>= inferUVar
  _ -> inferRho noHint expr

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

inferNaryTabApp :: EmitsBoth o => SrcPosCtx -> CAtom o -> NonEmpty (UExprArg i) -> InfererM i o (CAtom o)
inferNaryTabApp tabCtx tab args = addSrcContext tabCtx do
  tabTy <- getType tab
  (arg':args') <- inferNaryTabAppArgs tabTy $ toList args
  liftM Var $ emit $ TabApp tab $ arg' :| args'

inferNaryTabAppArgs
  :: EmitsBoth o
  => CType o -> [UExprArg i] -> InfererM i o [CAtom o]
inferNaryTabAppArgs _ [] = return []
inferNaryTabAppArgs tabTy ((appCtx, arg):rest) = do
  TabPiType b resultTy <- fromTabPiType True tabTy
  let ixTy = binderType b
  let isDependent = binderName b `isFreeIn` resultTy
  arg' <- addSrcContext appCtx $
    if isDependent
      then checkSigmaDependent (getNameHint b) arg ixTy
      else checkSigma (getNameHint b) arg ixTy
  arg'' <- zonk arg'
  resultTy' <- applySubst (b @> SubstVal arg'') resultTy
  rest' <- inferNaryTabAppArgs resultTy' rest
  return $ arg'':rest'

inferNaryApp :: EmitsBoth o => SrcPosCtx -> CAtom o -> NonEmpty (UExprArg i) -> InfererM i o (CAtom o)
inferNaryApp fCtx f args = addSrcContext fCtx do
  fTy <- getType f
  Just naryPi <- asNaryPiType <$> Pi <$> fromPiType True PlainArrow fTy
  (inferredArgs, remaining) <- inferNaryAppArgs naryPi args
  let appExpr = App f inferredArgs
  addEffects =<< getEffects appExpr
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
  => NaryPiType CoreIR o -> NonEmpty (UExprArg i) -> InfererM i o (NonEmpty (CAtom o), [UExprArg i])
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
  => Bool -> PiBinder CoreIR o o' -> NonEmpty (UExprArg i) -> InfererM i o (CAtom o, [UExprArg i])
inferAppArg isDependent b@(PiBinder _ argTy _) uArgs = getImplicitArg b >>= \case
  Just x -> return $ (x, toList uArgs)
  Nothing -> do
    let (appCtx, arg) :| restUArgs = uArgs
    liftM (,restUArgs) $ addSrcContext appCtx $
      if isDependent
        then checkSigmaDependent (getNameHint b) arg argTy
        else checkSigma (getNameHint b) arg argTy

checkSigmaDependent :: EmitsBoth o
                    => NameHint -> UExpr i -> SigmaType o -> InfererM i o (CAtom o)
checkSigmaDependent hint e@(WithSrcE ctx _) ty = do
  Abs decls result <- buildDeclsInf $ checkSigma hint e (sink ty)
  cheapReduceWithDecls decls result >>= \case
    (Just x', DictTypeHoistSuccess, ds) ->
      forM_ ds reportUnsolvedInterface >> return x'
    _ -> addSrcContext ctx $ throw TypeErr $ depFunErrMsg
  where
    depFunErrMsg =
      "Dependent functions can only be applied to fully evaluated expressions. " ++
      "Bind the argument to a name before you apply the function."

-- === sorting case alternatives ===

data IndexedAlt n = IndexedAlt CaseAltIndex (Alt CoreIR n)

instance SinkableE IndexedAlt where
  sinkingProofE = todoSinkableProof

buildNthOrderedAlt :: (Emits n, Builder CoreIR m)
                   => [IndexedAlt n] -> CType n -> CType n -> Int -> CAtom n
                   -> m n (CAtom n)
buildNthOrderedAlt alts scrutTy resultTy i v = do
  case lookup (nthCaseAltIdx scrutTy i) [(idx, alt) | IndexedAlt idx alt <- alts] of
    Nothing -> do
      resultTy' <- sinkM resultTy
      emitOp $ ThrowError resultTy'
    Just alt -> applyAbs alt (SubstVal v) >>= emitBlock

-- converts from the ordinal index used in the core IR to the more complicated
-- `CaseAltIndex` used in the surface IR.
nthCaseAltIdx :: CType n -> Int -> CaseAltIndex
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
  :: (Emits n, ScopableBuilder CoreIR m)
  => [IndexedAlt n] -> CAtom n -> CType n -> m n (CAtom n)
buildMonomorphicCase alts scrut resultTy = do
  scrutTy <- getType scrut
  buildCase scrut resultTy \i v -> do
    ListE alts' <- sinkM $ ListE alts
    scrutTy'    <- sinkM scrutTy
    resultTy'   <- sinkM resultTy
    buildNthOrderedAlt alts' scrutTy' resultTy' i v

buildSortedCase :: (Fallible1 m, Builder CoreIR m, Emits n)
                 => CAtom n -> [IndexedAlt n] -> CType n
                 -> m n (CAtom n)
buildSortedCase scrut alts resultTy = do
  scrutTy <- getType scrut
  case scrutTy of
    TypeCon _ defName _ -> do
      DataDef _ _ cons <- lookupDataDef defName
      case cons of
        [] -> error "case of void?"
        -- Single constructor ADTs are not sum types, so elide the case.
        [_] -> do
          let [IndexedAlt _ alt] = alts
          emitBlock =<< applyAbs alt (SubstVal $ unwrapCompoundNewtype scrut)
        _ -> liftEmitBuilder $ buildMonomorphicCase alts scrut resultTy
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
                        liftEmitBuilder $ buildMonomorphicCase alts' v resultTy')
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
                        liftEmitBuilder $ buildMonomorphicCase alts' v resultTy')
              (\v -> do tailAlt' <- sinkM tailAlt
                        applyAbs tailAlt' (SubstVal v) >>= emitBlock )
        _ -> throw TypeErr "Can't specify more than one variant tail pattern."
    _ -> fail $ "Unexpected case expression type: " <> pprint scrutTy

-- Make sure all of the alternatives are exclusive with the tail pattern (could
-- technically allow overlap but this is simpler). Split based on the tail
-- pattern's skipped types.
checkNoTailOverlaps :: Fallible1 m => [IndexedAlt n] -> LabeledItems (CType n) ->  m n ()
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

inferUVar :: EmitsBoth o => UVar o -> InfererM i o (CAtom o)
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
  UEffectVar _ -> do
    throw NotImplementedErr "inferUVar::UEffectVar"  -- TODO(alex): implement
  UEffectOpVar v -> do
    EffectOpBinding (EffectOpDef effName (OpIdx i)) <- lookupEnv v
    Var <$> (emit $ Op (Perform (Eff (OneEffect (UserEffect effName))) i))
  UHandlerVar v -> liftBuilder $ buildHandlerLam v

buildHandlerLam :: EmitsBoth n => HandlerName n -> BuilderM CoreIR n (CAtom n)
buildHandlerLam v = do
  HandlerBinding (HandlerDef effName _r _ns _hndEff _retTy _ _) <- lookupEnv v
  buildLam "r" ImplicitArrow TyKind Pure $ \r ->
    buildLam "eff" ImplicitArrow (TC EffectRowKind) Pure $ \eff -> do
      let bodyEff = EffectRow (S.singleton (UserEffect (sink effName))) (Just eff)
      bodyTy <- buildNonDepPi noHint PlainArrow UnitTy bodyEff (Var (sink r))
      let effRow = EffectRow (S.empty) (Just eff)
      buildLam "body" PlainArrow (Pi bodyTy) effRow $ \body -> do
        -- TODO(alex): deal with handler args below
        block <- buildBlock $ app (Var (sink body)) UnitVal
        Var <$> (emit $ Handle (sink v) [] block)

buildForTypeFromTabType :: EffectRow n -> TabPiType CoreIR n -> InfererM i n (PiType CoreIR n)
buildForTypeFromTabType effs tabPiTy@(TabPiType (b:>ixTy) _) = do
  let IxType ty _ = ixTy
  buildPi (getNameHint b) PlainArrow ty \i -> do
    Distinct <- getDistinct
    resultTy <- instantiateTabPi (sink tabPiTy) $ Var i
    return (sink effs, resultTy)

checkMaybeAnnExpr :: EmitsBoth o
  => NameHint -> Maybe (UType i) -> UExpr i -> InfererM i o (CAtom o)
checkMaybeAnnExpr hint ty expr = confuseGHC >>= \_ -> case ty of
  Nothing -> inferSigma hint expr
  Just ty' -> checkSigma hint expr =<< zonk =<< checkUType ty'

dictTypeFun :: EnvReader m => ClassName n -> m n (CAtom n)
dictTypeFun v = do
  -- TODO: we should cache this in the ClassDef
  ClassDef classSourceName _ paramBinders _ _ <- lookupClassDef v
  liftEnvReaderM $ refreshAbs (Abs paramBinders UnitE) \bs' UnitE -> do
    v' <- sinkM v
    return $ go classSourceName bs' v' $ nestToNames bs'
  where
    go :: SourceName -> Nest (RolePiBinder CoreIR) n l -> ClassName l -> [CAtomName l] -> CAtom n
    go classSourceName bs className params = case bs of
      Empty -> DictTy $ DictType classSourceName className $ map Var params
      Nest (RolePiBinder b ty _ _) rest ->
        Lam $ LamExpr (LamBinder b ty PlainArrow Pure) $
          AtomicBlock $ go classSourceName rest className params

-- TODO: cache this with the instance def (requires a recursive binding)
instanceFun :: EnvReader m => InstanceName n -> m n (CAtom n)
instanceFun instanceName = do
  InstanceDef _ bs _ _ <- lookupInstanceDef instanceName
  liftEnvReaderM $ refreshAbs (Abs bs UnitE) \bs' UnitE -> do
    let args = map Var $ nestToNames bs'
    instanceName' <- sinkM instanceName
    return $ go bs' instanceName' args
  where
    go :: Nest (RolePiBinder CoreIR) n l -> InstanceName l -> [CAtom l] -> CAtom n
    go bs name args = case bs of
      Empty -> DictCon $ InstanceDict name args
      Nest (RolePiBinder b ty arr _) rest -> do
        let restAtom = go rest name args
        Lam $ LamExpr (LamBinder b ty arr Pure) (AtomicBlock restAtom)

buildTyConLam
  :: ScopableBuilder CoreIR m
  => DataDefName n
  -> Arrow
  -> (forall l. DExt n l => SourceName -> DataDefParams CoreIR l -> m l (CAtom l))
  -> m n (CAtom n)
buildTyConLam defName arr cont = do
  DataDef sourceName paramBs _ <- lookupDataDef =<< sinkM defName
  buildPureNaryLam (EmptyAbs $ fmapNest replacePlain paramBs) \params -> do
    cont sourceName $ DataDefParams (attachArrows paramBs params)
  where
    replacePlain :: RolePiBinder CoreIR n l -> PiBinder CoreIR n l
    replacePlain (RolePiBinder b ty binderArr _) = PiBinder b ty arr'
      where arr' = case binderArr of
                     PlainArrow -> arr
                     _          -> binderArr

    attachArrows :: Nest (RolePiBinder CoreIR) n l
                  -> [CAtomName l2] -> [(Arrow, CAtom l2)]
    attachArrows Empty []     = []
    attachArrows (Nest (RolePiBinder _ _ arr' _) bs) (x:xs)
      = (arr', Var x):attachArrows bs xs
    attachArrows _ _ = error "zip error"

tyConDefAsAtom :: EnvReader m => DataDefName n -> m n (CAtom n)
tyConDefAsAtom defName = liftBuilder do
  buildTyConLam defName PlainArrow \sourceName params ->
    return $ TypeCon sourceName (sink defName) params

dataConDefAsAtom :: EnvReader m
                 => Abs (Nest (RolePiBinder CoreIR)) (EmptyAbs (Nest (Binder CoreIR))) n
                 -> DataDefName n -> Int -> m n (CAtom n)
dataConDefAsAtom bsAbs defName conIx = liftBuilder do
  buildTyConLam defName ImplicitArrow \_ params -> do
    defName' <- sinkM defName
    def@(DataDef sourceName _ _) <- lookupDataDef defName'
    conDefs <- instantiateDataDef def params
    let DataConDef _ conRep _ = conDefs !! conIx
    Abs conArgBinders UnitE <- applyDataConAbs (sink bsAbs) params
    buildPureNaryLam (EmptyAbs $ binderNestAsPiNest PlainArrow conArgBinders) \conArgs -> do
      conProd <- buildDataCon (sink conRep) $ Var <$> conArgs
      return $ Con $ Newtype (sink $ TypeCon sourceName defName' params) $
        case conDefs of
          []  -> error "unreachable"
          [_] -> conProd
          _   -> SumVal conTys conIx conProd
            where conTys = sinkList $ conDefs <&> \(DataConDef _ rty _) -> rty

buildDataCon :: EnvReader m => CType n -> [CAtom n] -> m n (CAtom n)
buildDataCon repTy topArgs = wrap repTy topArgs
  where
    wrap :: EnvReader m => CType n -> [CAtom n] -> m n (CAtom n)
    wrap _ [arg] = return $ arg
    wrap rty args = case rty of
      ProdTy tys  ->
        if nargs == ntys
          then return $ ProdVal args
          else ProdVal . (curArgs ++) . (:[]) <$> wrap (last tys) remArgs
        where
          nargs = length args; ntys = length tys
          (curArgs, remArgs) = splitAt (ntys - 1) args
      DepPairTy dpt@(DepPairType b rty') -> do
        rty'' <- applySubst (b@>SubstVal h) rty'
        ans <- wrap rty'' t
        return $ DepPair h ans dpt
        where h:t = args
      _ -> error $ "Unexpected data con representation type: " ++ pprint repTy

binderNestAsPiNest :: Arrow -> Nest (Binder CoreIR) n l -> Nest (PiBinder CoreIR) n l
binderNestAsPiNest arr = \case
  Empty             -> Empty
  Nest (b:>ty) rest -> Nest (PiBinder b ty arr) $ binderNestAsPiNest arr rest

inferRole :: CType o -> Arrow -> InfererM i o ParamRole
inferRole ty arr = case arr of
  ClassArrow -> return DictParam
  _ -> do
    zonk ty >>= \case
      TyKind -> return TypeParam
      ty' -> isData ty' >>= \case
        True -> return DataParam
        -- TODO(dougalm): the `False` branch should throw an error but that's
        -- currently too conservative. e.g. `data RangeFrom q:Type i:q = ...`
        -- fails because `q` isn't data. We should be able to fix it once we
        -- have a `Data a` class (see issue #680).
        False -> return DataParam
{-# INLINE inferRole #-}

inferDataDef
  :: EmitsInf o => UDataDef i
  -> InfererM i o (PairE DataDef
                         (Abs (Nest (RolePiBinder CoreIR)) (ListE (EmptyAbs (Nest (Binder CoreIR))))) o)
inferDataDef (UDataDef tyConName paramBs dataCons) = do
  Abs paramBs' (ListE dataConsWithBs') <-
    withNestedUBindersTyCon paramBs \_ -> do
      ListE <$> mapM inferDataCon dataCons
  let (dataCons', bs') = unzip $ fromPairE <$> dataConsWithBs'
  return $ PairE (DataDef tyConName paramBs' dataCons')
                 (Abs paramBs' $ ListE bs')

withNestedUBindersTyCon
  :: forall i i' o e. (EmitsInf o, HasNamesE e, SubstE (AtomSubstVal CoreIR) e, SinkableE e)
  => Nest (UAnnBinderArrow AtomNameC) i i'
  -> (forall o'. (EmitsInf o', Ext o o') => [CAtomName o'] -> InfererM i' o' (e o'))
  -> InfererM i o (Abs (Nest (RolePiBinder CoreIR)) e o)
withNestedUBindersTyCon bs cont = case bs of
  Empty -> Abs Empty <$> cont []
  Nest (UAnnBinderArrow b ty arr) rest -> do
    Abs b' (Abs rest' body) <-
      withRoleUBinder (UAnnBinder b ty) arr \name ->
        withNestedUBindersTyCon rest \names -> do
          name' <- sinkM name
          cont (name':names)
    return $ Abs (Nest b' rest') body

inferDataCon :: EmitsInf o
             => (SourceName, UDataDefTrail i)
             -> InfererM i o (PairE DataConDef (EmptyAbs (Nest (Binder CoreIR))) o)
inferDataCon (sourceName, UDataDefTrail argBs) = do
  argBs' <- checkUBinders (EmptyAbs argBs)
  let (repTy, projIdxs) = dataConRepTy argBs'
  return $ PairE (DataConDef sourceName repTy projIdxs) argBs'

dataConRepTy :: EmptyAbs (Nest (Binder CoreIR)) n -> (CType n, [[Projection]])
dataConRepTy (Abs topBs UnitE) = case topBs of
  Empty -> (UnitTy, [])
  _ -> go [] [UnwrapCompoundNewtype] topBs
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
            depTy = DepPairTy $ DepPairType b tailTy

inferClassDef
  :: SourceName -> [SourceName] -> Nest (UAnnBinder AtomNameC) i i'
  -> [UType i'] -> [UMethodType i']
  -> InfererM i o (ClassDef o)
inferClassDef className methodNames paramBs superclassTys methods = solveLocal do
  ab <- withClassDefBinders paramBs \_ -> do
    superclassTys' <- mapM checkUType superclassTys
    withSuperclassBinders superclassTys' do
      ListE <$> forM methods \(UMethodType (Right explicits) ty) -> do
        ty' <- checkUType ty
        return $ MethodType explicits ty'
  Abs bs (Abs scs (ListE mtys)) <- return ab
  return $ ClassDef className methodNames bs scs mtys

withClassDefBinders
  :: (EmitsInf o, HasNamesE e, SubstE (AtomSubstVal CoreIR) e, SinkableE e)
  => Nest (UAnnBinder AtomNameC) i i'
  -> (forall o'. (EmitsInf o', Ext o o') => [CAtomName o'] -> InfererM i' o' (e o'))
  -> InfererM i o (Abs (Nest (RolePiBinder CoreIR)) e o)
withClassDefBinders bs cont = case bs of
  Empty -> Abs Empty <$> cont []
  Nest b rest -> do
    Abs b' (Abs rest' body) <- withRoleUBinder b PlainArrow \name -> do
      withClassDefBinders rest \names -> do
        name' <- sinkM name
        cont (name':names)
    return $ Abs (Nest b' rest') body

withSuperclassBinders
  :: (SinkableE e, SubstE Name e, HoistableE e, EmitsInf o)
  => [CType o]
  -> (forall o'. (EmitsInf o', DExt o o') => InfererM i o' (e o'))
  -> InfererM i o (Abs SuperclassBinders e o)
withSuperclassBinders tys cont = do
  Abs bs e <- withSuperclassBindersRec tys cont
  return $ Abs (SuperclassBinders bs tys) e

withSuperclassBindersRec
  :: (SinkableE e, SubstE Name e, HoistableE e, EmitsInf o)
  => [CType o]
  -> (forall o'. (EmitsInf o', DExt o o') => InfererM i o' (e o'))
  -> InfererM i o (Abs (Nest AtomNameBinder) e o)
withSuperclassBindersRec [] cont = do
  Distinct <- getDistinct
  result <- cont
  return $ Abs Empty result
withSuperclassBindersRec (ty:rest) cont = do
  let binding = PiBinding ClassArrow ty
  Abs (b:>_) (Abs bs e) <- buildAbsInf noHint binding \_ -> do
    ListE rest' <- sinkM $ ListE rest
    withSuperclassBindersRec rest' cont
  return $ Abs (Nest b bs) e

withNestedUBinders
  :: (EmitsInf o, HasNamesE e, SubstE (AtomSubstVal CoreIR) e, SinkableE e, ToBinding binding AtomNameC)
  => Nest (UAnnBinder AtomNameC) i i'
  -> (forall l. CType l -> binding l)
  -> (forall o'. (EmitsInf o', Ext o o') => [CAtomName o'] -> InfererM i' o' (e o'))
  -> InfererM i o (Abs (Nest (Binder CoreIR)) e o)
withNestedUBinders bs asBinding cont = case bs of
  Empty -> Abs Empty <$> cont []
  Nest b rest -> do
    Abs b' (Abs rest' body) <- withUBinder b asBinding \name -> do
      withNestedUBinders rest asBinding \names -> do
        name' <- sinkM name
        cont (name':names)
    return $ Abs (Nest b' rest') body

withRoleUBinder
  :: (EmitsInf o, HasNamesE e, SubstE (AtomSubstVal CoreIR) e, SinkableE e)
  => UAnnBinder AtomNameC i i' -> Arrow
  -> (forall o'. (EmitsInf o', Ext o o') => CAtomName o' -> InfererM i' o' (e o'))
  -> InfererM i o (Abs (RolePiBinder CoreIR) e o)
withRoleUBinder (UAnnBinder b ann) arr cont = do
  ty <- checkUType ann
  role <- inferRole ty arr
  let binding = toBinding $ LamBinding arr ty
  Abs (b' :> _) ans <- buildAbsInf (getNameHint b) binding \name ->
    extendSubst (b @> name) $ cont name
  return $ Abs (RolePiBinder b' ty arr role) ans

withUBinder :: (EmitsInf o, HasNamesE e, SubstE (AtomSubstVal CoreIR) e, SinkableE e, ToBinding binding AtomNameC)
            => UAnnBinder AtomNameC i i'
            -> (CType o -> binding o)
            -> (forall o'. (EmitsInf o', Ext o o') => CAtomName o' -> InfererM i' o' (e o'))
            -> InfererM i o (Abs (Binder CoreIR) e o)
withUBinder (UAnnBinder b ann) asBinding cont = do
  ann' <- checkUType ann
  Abs (n :> _) ans <- buildAbsInf (getNameHint b) (asBinding ann') \name ->
    extendSubst (b @> name) $ cont name
  return $ Abs (n :> ann') ans

checkUBinders :: EmitsInf o
              => EmptyAbs (Nest (UAnnBinder AtomNameC)) i
              -> InfererM i o (EmptyAbs (Nest (Binder CoreIR)) o)
checkUBinders (EmptyAbs bs) = withNestedUBinders bs id \_ -> return UnitE
checkUBinders _ = error "impossible"

inferULam :: EmitsBoth o => EffectRow o -> ULamExpr i -> InfererM i o (CAtom o)
inferULam effs (ULamExpr arrow (UPatAnn p ann) body) = do
  argTy <- checkAnn ann
  buildLamInf (getNameHint p) arrow argTy (\_ -> sinkM effs) \v ->
    bindLamPat p v $ inferSigma noHint body

checkULam :: EmitsBoth o => ULamExpr i -> PiType CoreIR o -> InfererM i o (CAtom o)
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
        checkSigma noHint body resultTy

checkInstanceArgs
  :: (EmitsInf o, SinkableE e, SubstE Name e, HoistableE e)
  => Nest UPatAnnArrow i i'
  -> (forall o'. (EmitsInf o', DExt o o') => InfererM i' o' (e o'))
  -> InfererM i o (Abs (Nest (RolePiBinder CoreIR)) e o)
checkInstanceArgs Empty cont = do
  Distinct <- getDistinct
  Abs Empty <$> cont
checkInstanceArgs (Nest (UPatAnnArrow (UPatAnn p ann) arrow) rest) cont = do
  case arrow of
    ImplicitArrow -> return ()
    ClassArrow    -> return ()
    PlainArrow    -> return ()
    _ -> throw TypeErr $ "Not a valid arrow for an instance: " ++ pprint arrow
  ab <- checkAnnWithMissingDicts ann \ds getArgTy -> do
    introDicts (eSetToList ds) $ do
      argTy <- getArgTy
      ab <- buildPiAbsInf (getNameHint p) arrow argTy \v -> do
        WithSrcB pos (UPatBinder b) <- return p  -- TODO: enforce this syntactically
        addSrcContext pos $ extendSubst (b@>v) $
          checkInstanceArgs rest do
            cont
      Abs (PiBinder b ty _) e <- return ab
      -- it's important to do role inference after we finish everything else
      -- because we don't know what the parameter's type is until then.
      role <- inferRole argTy arrow
      return $ Abs (RolePiBinder b ty arrow role) e
  Abs bs (Abs b (Abs bs' e)) <- return ab
  return $ Abs (bs >>> Nest b Empty >>> bs') e

-- Nothing about the implementation was instance-specific. This seems
-- right. If not, at least we only need to change this definition.
checkHandlerArgs
  :: (EmitsInf o, SinkableE e, SubstE Name e, HoistableE e)
  => Nest UPatAnnArrow i i'
  -> (forall o'. (EmitsInf o', DExt o o') => InfererM i' o' (e o'))
  -> InfererM i o (Abs (Nest (PiBinder CoreIR)) e o)
checkHandlerArgs bs cont = do
  Abs bs' result <- checkInstanceArgs bs cont
  let bs'' = fmapNest (\(RolePiBinder b ty arr _) -> PiBinder b ty arr) bs'
  return $ Abs bs'' result

checkHandlerBodyTyArg
  :: (EmitsInf o, SinkableE e, SubstE Name e, HoistableE e)
  => UBinder AtomNameC i i'
  -> (forall o'. (EmitsInf o', Ext o o') => CAtomName o' -> InfererM i' o' (e o'))
  -> InfererM i o (Abs (PiBinder CoreIR) e o)
checkHandlerBodyTyArg b cont = do
  argTy <- freshType TyKind
  buildPiAbsInf (getNameHint b) ImplicitArrow argTy \v -> do
    extendSubst (b@>v) $
      cont v

checkInstanceParams
  :: forall i o e.
     (EmitsInf o, SinkableE e, HoistableE e, SubstE Name e)
  => [UType i]
  -> (forall o'. (EmitsInf o', Ext o o') => [CType o'] -> InfererM i o' (e o'))
  -> InfererM i o (Abs (Nest (RolePiBinder CoreIR)) e o)
checkInstanceParams params cont = go params []
  where
    go :: forall o'. (EmitsInf o', Ext o o') => [UType i] -> [CType o']
       -> InfererM i o' (Abs (Nest (RolePiBinder CoreIR)) e o')
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
                  -> [CType o]
                  -> [UMethodDef i]
                  -> InfererM i o (InstanceBody o)
checkInstanceBody className params methods = do
  def@(ClassDef _ methodNames _ _ _ ) <- getClassDef className
  Abs superclassBs methodTys <- checkedApplyClassParams def params
  SuperclassBinders bs superclassTys <- return superclassBs
  superclassDicts <- mapM trySynthTerm superclassTys
  ListE methodTys' <- applySubst (bs @@> map SubstVal superclassDicts) methodTys
  methodsChecked <- mapM (checkMethodDef className methodTys') methods
  let (idxs, methods') = unzip $ sortOn fst $ methodsChecked
  forM_ (repeated idxs) \i ->
    throw TypeErr $ "Duplicate method: " ++ pprint (methodNames!!i)
  forM_ ([0..(length methodTys' - 1)] `listDiff` idxs) \i ->
    throw TypeErr $ "Missing method: " ++ pprint (methodNames!!i)
  return $ InstanceBody superclassDicts methods'

introDicts
  :: forall i o e.
     (EmitsInf o, SinkableE e, HoistableE e, SubstE Name e)
  => [CType o]
  -> (forall l. (EmitsInf l, Ext o l) => InfererM i l (e l))
  -> InfererM i o (Abs (Nest (RolePiBinder CoreIR)) e o)
introDicts []    m = Abs Empty <$> m
introDicts (h:t) m = do
  ab <- buildPiAbsInf (getNameHint @String "_autoq") ClassArrow h \_ -> do
    ListE t' <- sinkM $ ListE t
    introDicts t' m
  Abs (PiBinder b ty arr) (Abs bs e) <- return ab
  return $ Abs (Nest (RolePiBinder b ty arr DictParam) bs) e

introDictTys :: forall i o. EmitsInf o
             => [CType o]
             -> (forall l. (EmitsInf l, Ext o l) => InfererM i l (PiType CoreIR l))
             -> InfererM i o (PiType CoreIR o)
introDictTys []    m = m
introDictTys (h:t) m = buildPiInf (getNameHint @String "_autoq") ClassArrow h \_ -> do
  ListE t' <- sinkM $ ListE t
  (Pure,) . Pi <$> (introDictTys t' m)

checkMethodDef :: EmitsInf o
               => ClassName o -> [MethodType o] -> UMethodDef i -> InfererM i o (Int, CBlock o)
checkMethodDef className methodTys (UMethodDef ~(InternalName sourceName v) rhs) = do
  MethodBinding className' i _ <- substM v >>= lookupEnv
  when (className /= className') do
    ClassBinding (ClassDef classSourceName _ _ _ _) <- lookupEnv className
    throw TypeErr $ pprint sourceName ++ " is not a method of "
                 ++ pprint classSourceName
  let MethodType _ methodTy = methodTys !! i
  rhs' <- buildBlockInf do
    methodTy' <- sinkM methodTy
    checkSigma noHint rhs methodTy'
  return (i, rhs')

checkUEffRow :: EmitsInf o => UEffectRow i -> InfererM i o (EffectRow o)
checkUEffRow (EffectRow effs t) = do
   effs' <- liftM S.fromList $ mapM checkUEff $ toList effs
   t' <- forM t \(SIInternalName _ v) -> do
            v' <- substM v
            constrainVarTy v' EffKind
            return v'
   return $ EffectRow effs' t'

checkUEff :: EmitsInf o => UEffect i -> InfererM i o (Effect o)
checkUEff eff = case eff of
  RWSEffect rws (Just ~(SIInternalName _ region)) -> do
    region' <- substM region
    constrainVarTy region' TyKind
    return $ RWSEffect rws $ Just region'
  RWSEffect rws Nothing -> return $ RWSEffect rws Nothing
  ExceptionEffect -> return ExceptionEffect
  IOEffect        -> return IOEffect
  UserEffect ~(SIInternalName _ name) -> UserEffect <$> substM name
  InitEffect -> return InitEffect

constrainVarTy :: EmitsInf o => CAtomName o -> CType o -> InfererM i o ()
constrainVarTy v tyReq = do
  varTy <- getType $ Var v
  constrainEq tyReq varTy

data CaseAltIndex = ConAlt Int
                  | VariantAlt Label Int
                  | VariantTailAlt (LabeledItems ())
  deriving (Eq, Show)

checkCaseAlt :: EmitsBoth o
             => RhoType o -> CType o -> UAlt i -> InfererM i o (IndexedAlt o)
checkCaseAlt reqTy scrutineeTy (UAlt pat body) = do
  alt <- checkCasePat pat scrutineeTy do
    reqTy' <- sinkM reqTy
    checkRho noHint body reqTy'
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
             -> CType o
             -> (forall o'. (EmitsBoth o', Ext o o') => InfererM i' o' (CAtom o'))
             -> InfererM i o (Alt CoreIR o)
checkCasePat (WithSrcB pos pat) scrutineeTy cont = addSrcContext pos $ case pat of
  UPatCon ~(InternalName _ conName) ps -> do
    (dataDefName, con) <- substM conName >>= getDataCon
    DataDef sourceName paramBs cons <- lookupDataDef dataDefName
    DataConDef _ repTy idxs <- return $ cons !! con
    when (length idxs /= nestLength ps) $ throw TypeErr $
      "Unexpected number of pattern binders. Expected " ++ show (length idxs)
                                             ++ " got " ++ show (nestLength ps)
    (params, repTy') <- inferParams (Abs paramBs repTy)
    constrainEq scrutineeTy $ TypeCon sourceName dataDefName params
    buildAltInf repTy' \arg -> do
      args <- forM idxs $ init |> NE.nonEmpty |> \case
        Nothing    -> return arg
        Just idxs' -> emit $ Atom $ ProjectElt idxs' arg
      bindLamPats ps args $ cont
      where (|>) = flip (.)
  UPatVariant labels label p -> do
    ty <- freshType TyKind
    prevTys <- mapM (const $ freshType TyKind) labels
    rest <- freshInferenceName LabeledRowKind
    let patTypes = prevTys <> labeledSingleton label ty
    let extPatTypes = Ext patTypes $ Just rest
    constrainEq scrutineeTy $ VariantTy extPatTypes
    buildAltInf ty \x ->
      bindLamPat p x cont
  UPatVariantLift labels p -> do
    prevTys <- mapM (const $ freshType TyKind) labels
    rest <- freshInferenceName LabeledRowKind
    let extPatTypes = Ext prevTys $ Just rest
    constrainEq scrutineeTy $ VariantTy extPatTypes
    let ty = VariantTy $ Ext NoLabeledItems $ Just rest
    buildAltInf ty \x ->
      bindLamPat p x cont
  _ -> throw TypeErr $ "Case patterns must start with a data constructor or variant pattern"

inferParams :: (EmitsBoth o, HasNamesE e, SinkableE e, SubstE (AtomSubstVal CoreIR) e)
            => Abs (Nest (RolePiBinder CoreIR)) e o -> InfererM i o (DataDefParams CoreIR o, e o)
inferParams (Abs paramBs body) = case paramBs of
  Empty -> return (DataDefParams [], body)
  Nest (RolePiBinder b ty PlainArrow _) bs -> do
    x <- freshInferenceName ty
    rest <- applySubst (b@>x) $ Abs bs body
    (DataDefParams params, body') <- inferParams rest
    return (DataDefParams ((PlainArrow, (Var x)) : params), body')
  Nest (RolePiBinder b ty ClassArrow _) bs -> do
    ctx <- srcPosCtx <$> getErrCtx
    let d = Con $ DictHole (AlwaysEqual ctx) ty
    rest <- applySubst (b@>SubstVal d) $ Abs bs body
    (DataDefParams params, body') <- inferParams rest
    return (DataDefParams ((ClassArrow, d):params), body')
  Nest (RolePiBinder _ _ _ _) _ -> do
    error "TODO Handle implicit or linear parameters for data constructors"

bindLamPats :: EmitsBoth o
            => Nest UPat i i' -> [CAtomName o] -> InfererM i' o a -> InfererM i o a
bindLamPats Empty [] cont = cont
bindLamPats (Nest p ps) (x:xs) cont = bindLamPat p x $ bindLamPats ps xs cont
bindLamPats _ _ _ = error "mismatched number of args"

bindLamPat :: EmitsBoth o => UPat i i' -> CAtomName o -> InfererM i' o a -> InfererM i o a
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
    x1 <- getFst x' >>= zonk >>= emitAtomToName noHint
    bindLamPat p1 x1 do
      x2  <- getSnd x' >>= zonk >>= emitAtomToName noHint
      bindLamPat p2 x2 do
        cont
  UPatDepPair (PairB p1 p2) -> do
    let x = Var v
    ty <- getType x
    _  <- fromDepPairType ty
    x' <- zonk x  -- ensure it has a dependent pair type before unpacking
    x1 <- getFst x' >>= zonk >>= emitAtomToName noHint
    bindLamPat p1 x1 do
      x2  <- getSnd x' >>= zonk >>= emitAtomToName noHint
      bindLamPat p2 x2 do
        cont
  UPatCon ~(InternalName _ conName) ps -> do
    (dataDefName, _) <- getDataCon =<< substM conName
    DataDef sourceName paramBs cons <- lookupDataDef dataDefName
    case cons of
      [DataConDef _ _ idxs] -> do
        when (length idxs /= nestLength ps) $ throw TypeErr $
          "Unexpected number of pattern binders. Expected " ++ show (length idxs)
                                                 ++ " got " ++ show (nestLength ps)
        (params, UnitE) <- inferParams (Abs paramBs UnitE)
        constrainVarTy v $ TypeCon sourceName dataDefName params
        xs <- mapM (emitAtomToName noHint) =<< getUnpacked =<< zonk (Var v)
        bindLamPats ps xs cont
      _ -> throw TypeErr $ "sum type constructor in can't-fail pattern"
  UPatRecord rowPat -> do
    bindPats cont ([], Empty, v) rowPat
    where
      bindPats :: EmitsBoth o
               => InfererM i' o a -> ([Label], Nest UPat i l, CAtomName o) -> UFieldRowPat l i' -> InfererM i o a
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
            fv' <- emitAtomToName noHint =<< checkRho noHint
              (WithSrcE Nothing $ UVar fv) LabeledRowKind
            tailVar <- freshInferenceName LabeledRowKind
            constrainVarTy rv' $ RecordTyWithElems [DynFields fv', DynFields tailVar]
            [subr, rv''] <- emitUnpacked =<< emitOp (RecordSplit (Var fv') (Var rv'))
            bindLamPat p subr $ bindPats c (mempty, Empty, rv'') rest
        UDynFieldPat lv p rest ->
          resolveDelay rv \rv' -> do
            lv' <- emitAtomToName noHint =<< checkRho noHint
              (WithSrcE Nothing $ UVar lv) (TC LabelType)
            fieldTy <- freshType TyKind
            tailVar <- freshInferenceName LabeledRowKind
            constrainVarTy rv' $ RecordTyWithElems [DynField lv' fieldTy, DynFields tailVar]
            [val, rv''] <- emitUnpacked =<< emitOp (RecordSplitDynamic (Var lv') (Var rv'))
            bindLamPat p val $ bindPats c (mempty, Empty, rv'') rest

      -- Unpacks the record and returns the components in order, as if they
      -- were looked up by consecutive labels. Note that the number of labels
      -- should match the total number of record fields, and the record should
      -- have no dynamic extensions!
      unpackInLabelOrder :: EmitsBoth o => CAtom o -> [Label] -> InfererM i o [CAtomName o]
      unpackInLabelOrder r ls = do
        itemsNatural <- emitUnpacked =<< zonk r
        let labelOrder = toList $ foldMap (\(i, l) -> labeledSingleton l i) $ enumerate ls
        let itemsMap = M.fromList $ zip labelOrder itemsNatural
        return $ (itemsMap M.!) <$> [0..M.size itemsMap - 1]

      resolveDelay :: EmitsBoth o => ([Label], Nest UPat i l, CAtomName o) -> (CAtomName o -> InfererM l o a) -> InfererM i o a
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
          restRecordName <- emitAtomToName noHint restRecord
          bindLamPats ps itemsNestOrdered $ f restRecordName
  UPatVariant _ _ _   -> throw TypeErr "Variant not allowed in can't-fail pattern"
  UPatVariantLift _ _ -> throw TypeErr "Variant not allowed in can't-fail pattern"
  UPatTable ps -> do
    elemTy <- freshType TyKind
    idxTy <- asIxType $ FinConst $ fromIntegral $ nestLength ps
    ty <- getType $ Var v
    tabTy <- idxTy ==> elemTy
    constrainEq ty tabTy
    maybeIdxs <- indicesLimit (nestLength ps) idxTy
    case maybeIdxs of
      (Right idxs) -> do
        xs <- forM idxs \i -> emit $ TabApp (Var v) (i:|[])
        bindLamPats ps xs cont
      (Left trueSize) ->
        throw TypeErr $ "Incorrect length of table pattern: table index set has "
                        <> pprint trueSize <> " elements but there are "
                        <> pprint (nestLength ps) <> " patterns."

checkAnn :: EmitsInf o => Maybe (UType i) -> InfererM i o (CType o)
checkAnn ann = case ann of
  Just ty -> checkUType ty
  Nothing -> freshType TyKind

checkAnnWithMissingDicts
  :: EmitsInf o
  => Maybe (UType i)
  -> (IfaceTypeSet o -> (forall o'. (EmitsInf o', Ext o o') => InfererM i o' (CType o')) -> InfererM i o a)
  -> InfererM i o a
checkAnnWithMissingDicts ann cont = case ann of
  Just ty -> checkUTypeWithMissingDicts ty cont
  Nothing ->
    cont mempty (freshType TyKind)  -- Unannotated binders are never auto-quantified

checkUTypeWithMissingDicts
  :: EmitsInf o
  => UType i
  -> (IfaceTypeSet o -> (forall o'. (EmitsInf o', Ext o o') => InfererM i o' (CType o')) -> InfererM i o a)
  -> InfererM i o a
checkUTypeWithMissingDicts uty@(WithSrcE _ _) cont = do
  unsolvedSubset <- do
    -- We have to be careful not to emit inference vars out of the initial solve.
    -- The resulting type will never be used in downstream inference, so we can easily
    -- end up with fake ambiguous variables if they leak out.
    Abs frag unsolvedSubset' <- liftInfererMSubst $ runLocalInfererM do
      (Abs decls result, unsolvedSubset) <- gatherUnsolvedInterfaces $
        buildDeclsInf $ withAllowedEffects Pure $ checkRho noHint uty TyKind
      -- Note that even if the normalization succeeds here, we can't short-circuit
      -- rechecking the UType, because unsolvedSubset is only an approximation to
      -- the set of all constraints. We have to reverify it again!
      -- We could probably add a flag to RequiredIfaces that would indicate whether
      -- pruning has happened.
      -- Note that we ignore the hoist success/failure bit because we're just
      -- collecting required dictionaries on a best-effort basis here. Failure
      -- to hoist only becomes an error later.
      (_, _, unsolved) <- cheapReduceWithDecls @CoreIR @CAtom decls result
      return $ unsolvedSubset <> eSetFromList unsolved
    return $ case hoistRequiredIfaces frag (GatherRequired unsolvedSubset') of
      GatherRequired unsolvedSubset -> unsolvedSubset
      FailIfRequired                -> error "Unreachable"
  cont unsolvedSubset $ checkUType uty

checkUType :: EmitsInf o => UType i -> InfererM i o (CType o)
checkUType uty@(WithSrcE pos _) = do
  Abs decls result <- buildDeclsInf $ withAllowedEffects Pure $ checkRho noHint uty TyKind
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
                   -> InfererM i o (ExtLabeledItems (CType o) (CAtomName o))
checkExtLabeledRow (Ext types Nothing) = do
  types' <- mapM checkUType types
  return $ Ext types' Nothing
checkExtLabeledRow (Ext types (Just ext)) = do
  types' <- mapM checkUType types
  -- Only variables can have kind LabeledRowKind at the moment.
  Var ext' <- checkRho noHint ext LabeledRowKind
  return $ Ext types' $ Just ext'

inferTabCon :: EmitsBoth o
  => NameHint -> [UExpr i] -> RequiredTy RhoType o -> InfererM i o (CAtom o)
inferTabCon hint xs reqTy = do
  (tabTy, xs') <- case reqTy of
    Check tabTy@(TabPi piTy) -> do
      (TabPiType b restTy) <- return piTy
      liftBuilderT (buildScoped $ indexSetSize $ sink $ binderAnn b) >>= \case
        (Just szMethod) ->
          staticallyKnownIdx szMethod >>= \case
            (Just size) | size == fromIntegral (length xs) -> do
              -- Size matches.  Try to hoist the result type past the
              -- type binder to avoid synthesizing the indices, if
              -- possible.
              case hoist b restTy of
                HoistSuccess elTy -> do
                  xs' <- mapM (\x -> checkRho noHint x elTy) xs
                  return (tabTy, xs')
                HoistFailure _    -> do
                  idx <- indices $ binderAnn b
                  xs' <- forM (zip xs idx) \(x, i) -> do
                    xTy <- instantiateTabPi piTy i
                    checkOrInferRho noHint x $ Check xTy
                  return (tabTy, xs')
            (Just size) -> throw TypeErr $ "Literal has " ++ count (length xs) "element"
                             ++ ", but required type has " ++ show size ++ "."
              where count :: Int -> String -> String
                    count 1 singular = "1 " ++ singular
                    count n singular = show n ++ " " ++ singular ++ "s"
            -- Size of index set not statically known
            Nothing -> inferFin
        -- Couldn't synthesize the Ix dictionary; inference variable
        -- present in (argType piTy)?
        Nothing -> inferFin
    -- Requested type is not a `Check (TabPi _)`
    _ -> inferFin
  liftM Var $ emitHinted hint $ Op $ TabCon tabTy xs'
    where
      inferFin = do
        elemTy <- case xs of
          []    -> freshType TyKind
          (x:_) -> getType =<< inferRho noHint x
        ixTy <- asIxType $ FinConst (fromIntegral $ length xs)
        tabTy <- ixTy ==> elemTy
        case reqTy of
          Check sTy -> addContext context $ constrainEq sTy tabTy
          Infer     -> return ()
        xs' <- mapM (\x -> checkRho noHint x elemTy) xs
        return (tabTy, xs')

      staticallyKnownIdx :: (EnvReader m) => Abs (Nest CDecl) CAtom n -> m n (Maybe Word32)
      staticallyKnownIdx (Abs decls res) = unsafeLiftInterpMCatch (evalDecls decls $ evalExpr $ Atom res) >>= \case
        (Success (IdxRepVal ix)) -> return $ Just ix
        _ -> return Nothing
      {-# INLINE staticallyKnownIdx #-}

      context = "If attempting to construct a fixed-size table not\n" <>
                "indexed by 'Fin n' for some static n, this error may\n" <>
                "indicate there was not enough information to infer\n" <>
                "a concrete index set; try adding an explicit\n" <>
                "annotation."

-- Bool flag is just to tweak the reported error message
fromTabPiType :: EmitsBoth o => Bool -> CType o -> InfererM i o (TabPiType CoreIR o)
fromTabPiType _ (TabPi piTy) = return piTy
fromTabPiType expectPi ty = do
  a <- freshType TyKind
  b <- freshType TyKind
  a' <- asIxType a
  piTy <- nonDepTabPiType a' b
  if expectPi then  constrainEq (TabPi piTy) ty
              else  constrainEq ty (TabPi piTy)
  return piTy

-- Bool flag is just to tweak the reported error message
fromPiType :: EmitsBoth o => Bool -> Arrow -> CType o -> InfererM i o (PiType CoreIR o)
fromPiType _ _ (Pi piTy) = return piTy -- TODO: check arrow
fromPiType expectPi arr ty = do
  a <- freshType TyKind
  b <- freshType TyKind
  piTy <- nonDepPiType arr a Pure b
  if expectPi then  constrainEq (Pi piTy) ty
              else  constrainEq ty (Pi piTy)
  return piTy

fromPairType :: EmitsBoth o => CType o -> InfererM i o (CType o, CType o)
fromPairType (PairTy t1 t2) = return (t1, t2)
fromPairType ty = do
  a <- freshType TyKind
  b <- freshType TyKind
  constrainEq (PairTy a b) ty
  return (a, b)

fromDepPairType :: EmitsBoth o => CType o -> InfererM i o (DepPairType CoreIR o)
fromDepPairType (DepPairTy t) = return t
fromDepPairType ty = throw TypeErr $ "Expected a dependent pair, but got: " ++ pprint ty

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

asIxType :: CType o -> InfererM i o (IxType CoreIR o)
asIxType ty = do
  dictTy <- DictTy <$> ixDictType ty
  ctx <- srcPosCtx <$> getErrCtx
  return $ IxType ty $ Con $ DictHole (AlwaysEqual ctx) dictTy
{-# SCC asIxType #-}

-- === Solver ===

newtype SolverSubst n = SolverSubst (M.Map (CAtomName n) (CType n))

instance Pretty (SolverSubst n) where
  pretty (SolverSubst m) = pretty $ M.toList m

class (CtxReader1 m, EnvReader m) => Solver (m::MonadKind1) where
  zonk :: (SubstE (AtomSubstVal CoreIR) e, SinkableE e) => e n -> m n (e n)
  extendSolverSubst :: CAtomName n -> CType n -> m n ()
  emitSolver :: EmitsInf n => SolverBinding CoreIR n -> m n (CAtomName n)
  solveLocal :: (SinkableE e, HoistableE e)
             => (forall l. (EmitsInf l, Ext n l, Distinct l) => m l (e l))
             -> m n (e n)

type SolverOutMap = InfOutMap

data SolverOutFrag (n::S) (l::S) =
  SolverOutFrag (SolverEmissions n l) (SolverSubst l)

type SolverEmissions = RNest (BinderP AtomNameC (SolverBinding CoreIR))

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

newtype SolverEmission (n::S) (l::S) = SolverEmission (BinderP AtomNameC (SolverBinding CoreIR) n l)
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

freshInferenceName :: (EmitsInf n, Solver m) => Kind CoreIR n -> m n (CAtomName n)
freshInferenceName k = do
  ctx <- srcPosCtx <$> getErrCtx
  emitSolver $ InfVarBound k ctx
{-# INLINE freshInferenceName #-}

freshSkolemName :: (EmitsInf n, Solver m) => Kind CoreIR n -> m n (CAtomName n)
freshSkolemName k = emitSolver $ SkolemBound k
{-# INLINE freshSkolemName #-}

type Solver2 (m::MonadKind2) = forall i. Solver (m i)

emptySolverSubst :: SolverSubst n
emptySolverSubst = SolverSubst mempty

singletonSolverSubst :: CAtomName n -> CType n -> SolverSubst n
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
lookupSolverSubst :: forall c n. Color c => SolverSubst n -> Name c n -> AtomSubstVal CoreIR c n
lookupSolverSubst (SolverSubst m) name =
  case eqColorRep of
    Nothing -> Rename name
    Just (ColorsEqual :: ColorsEqual c AtomNameC)-> case M.lookup name m of
      Nothing -> Rename name
      Just ty -> SubstVal ty

applySolverSubstE :: (SubstE (SubstVal AtomNameC CAtom) e, Distinct n)
                  => Scope n -> SolverSubst n -> e n -> e n
applySolverSubstE scope solverSubst@(SolverSubst m) e =
  if M.null m then e else fmapNames scope (lookupSolverSubst solverSubst) e

zonkWithOutMap :: (SubstE (AtomSubstVal CoreIR) e, Distinct n)
               => InfOutMap n -> e n -> e n
zonkWithOutMap (InfOutMap bindings solverSubst _ _) e =
  applySolverSubstE (toScope bindings) solverSubst e

liftSolverOutFrag :: Distinct l => SolverOutFrag n l -> InfOutFrag n l
liftSolverOutFrag (SolverOutFrag emissions subst) =
  InfOutFrag (liftSolverEmissions emissions) mempty subst

liftSolverEmissions :: Distinct l => SolverEmissions n l -> InfEmissions n l
liftSolverEmissions emissions =
  fmapRNest (\(b:>emission) -> (b:>RightE emission)) emissions

fmapRNest :: (forall ii ii'. b ii ii' -> b' ii ii')
          -> RNest b  i i'
          -> RNest b' i i'
fmapRNest _ REmpty = REmpty
fmapRNest f (RNest rest b) = RNest (fmapRNest f rest) (f b)

instance GenericE SolverSubst where
  -- XXX: this is a bit sketchy because it's not actually bijective...
  type RepE SolverSubst = ListE (PairE CAtomName CType)
  fromE (SolverSubst m) = ListE $ map (uncurry PairE) $ M.toList m
  {-# INLINE fromE #-}
  toE (ListE pairs) = SolverSubst $ M.fromList $ map fromPairE pairs
  {-# INLINE toE #-}

instance SinkableE SolverSubst where
instance SubstE Name SolverSubst where
instance HoistableE SolverSubst

constrainEq :: EmitsInf o => CType o -> CType o -> InfererM i o ()
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

class (AlphaEqE e, SinkableE e, SubstE (AtomSubstVal CoreIR) e) => Unifiable (e::E) where
  unifyZonked :: EmitsInf n => e n -> e n -> SolverM n ()

tryConstrainEq :: EmitsInf o => CType o -> CType o -> InfererM i o ()
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

instance Unifiable (Atom CoreIR) where
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
      (TypeCon _ c params, TypeCon _ c' params') -> guard (c == c') >> unify params params'
      (TC con, TC con') -> do
        guard $ sameConstructor con con'
        -- TODO: Optimize this!
        guard $ void con == void con'
        zipWithM_ unify (toList con) (toList con')
      (Eff eff, Eff eff') -> unify eff eff'
      (DictTy d, DictTy d') -> unify d d'
      _ -> unifyEq e1 e2

instance Unifiable (DictType CoreIR) where
  unifyZonked (DictType _ c params) (DictType _ c' params') =
    guard (c == c') >> zipWithM_ unify params params'
  {-# INLINE unifyZonked #-}

instance Unifiable (IxType CoreIR) where
  -- We ignore the dictionaries because we assume coherence
  unifyZonked (IxType t _) (IxType t' _) = unifyZonked t t'

instance Unifiable (DataDefParams CoreIR) where
  -- We ignore the dictionaries because we assume coherence
  unifyZonked (DataDefParams xs) (DataDefParams xs')
    = zipWithM_ unify (plainArrows xs) (plainArrows xs')

instance Unifiable (EffectRowP Name) where
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
instance Unifiable (FieldRowElems CoreIR) where
  unifyZonked e1 e2 = go (fromFieldRowElems e1) (fromFieldRowElems e2)
    where
      go = curry \case
        ([]           , []           ) -> return ()
        ([DynFields f], [DynFields g]) | f == g -> return ()
        ([DynFields f], r            ) -> extendSolution f $ LabeledRow $ fieldRowElemsFromList r
        (l            , [DynFields f]) -> extendSolution f $ LabeledRow $ fieldRowElemsFromList l
        (l@(h:t)      , r@(h':t')    ) -> (unifyElem h h' >> go t t') <|> unifyAsExtLabledItems l r
        (l            , r            ) -> unifyAsExtLabledItems l r

      unifyElem :: forall n. EmitsInf n => FieldRowElem CoreIR n -> FieldRowElem CoreIR n -> SolverM n ()
      unifyElem f1 f2 = case (f1, f2) of
        (DynField v ty     , DynField v' ty'    ) -> unify (Var v :: CAtom n) (Var v') >> unify ty ty'
        (DynFields r       , DynFields r'       ) -> unify (Var r :: CAtom n) (Var r')
        (StaticFields items, StaticFields items') -> do
          guard $ reflectLabels items == reflectLabels items'
          zipWithM_ unify (toList items) (toList items')
        _ -> unifyEq f1 f2

      unifyAsExtLabledItems l r = bindM2 unify (asExtLabeledItems l) (asExtLabeledItems r)

      asExtLabeledItems x = ExtLabeledItemsE <$> fieldRowElemsAsExtRow (fieldRowElemsFromList x)

instance Unifiable (ExtLabeledItemsE CType CAtomName) where
  unifyZonked x1 x2 =
        unifyDirect x1 x2
    <|> unifyDirect x2 x1
    <|> unifyZip x1 x2

   where
     unifyDirect :: EmitsInf n
                 => ExtLabeledItemsE CType CAtomName n
                 -> ExtLabeledItemsE CType CAtomName n -> SolverM n ()
     unifyDirect (ExtLabeledItemsE (Ext NoLabeledItems (Just v))) (ExtLabeledItemsE r@(Ext items mv)) =
       case mv of
         Just v' | v == v' -> guard $ null items
         _ -> extendSolution v $ LabeledRow $ extRowAsFieldRowElems r
     unifyDirect _ _ = empty
     {-# INLINE unifyDirect #-}

     unifyZip :: EmitsInf n
              => ExtLabeledItemsE CType CAtomName n
              -> ExtLabeledItemsE CType CAtomName n -> SolverM n ()
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

unifyPiType :: EmitsInf n => PiType CoreIR n -> PiType CoreIR n -> SolverM n ()
unifyPiType (PiType (PiBinder b1 ann1 arr1) eff1 ty1)
            (PiType (PiBinder b2 ann2 arr2) eff2 ty2) = do
  unless (arr1 == arr2) empty
  unify ann1 ann2
  v <- freshSkolemName ann1
  PairE eff1' ty1' <- applyAbs (Abs b1 (PairE eff1 ty1)) v
  PairE eff2' ty2' <- applyAbs (Abs b2 (PairE eff2 ty2)) v
  unify ty1'  ty2'
  unify eff1' eff2'

unifyTabPiType :: EmitsInf n => TabPiType CoreIR n -> TabPiType CoreIR n -> SolverM n ()
unifyTabPiType (TabPiType b1 ty1) (TabPiType b2 ty2) = do
  let ann1 = binderType b1
  let ann2 = binderType b2
  unify ann1 ann2
  v <- freshSkolemName ann1
  ty1' <- applyAbs (Abs b1 ty1) v
  ty2' <- applyAbs (Abs b2 ty2) v
  unify ty1'  ty2'

extendSolution :: CAtomName n -> CType n -> SolverM n ()
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

isInferenceName :: EnvReader m => CAtomName n -> m n Bool
isInferenceName v = lookupEnv v >>= \case
  AtomNameBinding (SolverBound (InfVarBound _ _)) -> return True
  _ -> return False
{-# INLINE isInferenceName #-}

isSkolemName :: EnvReader m => CAtomName n -> m n Bool
isSkolemName v = lookupEnv v >>= \case
  AtomNameBinding (SolverBound (SkolemBound _)) -> return True
  _ -> return False
{-# INLINE isSkolemName #-}

freshType :: (EmitsInf n, Solver m) => Kind CoreIR n -> m n (CType n)
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

synthTopBlock :: (EnvReader m, Fallible1 m) => CBlock n -> m n (CBlock n)
synthTopBlock block = do
  (liftExcept =<<) $ liftDictSynthTraverserM $ traverseGenericE block
{-# SCC synthTopBlock #-}

-- Given a simplified dict (an Atom of type `DictTy _` in the
-- post-simplification IR), and a requested, more general, dict type, generalize
-- the dict to match the more general type. This is only possible because we
-- require that instances are polymorphic in data-role parameters. It would be
-- valid to implement `generalizeDict` by re-synthesizing the whole dictionary,
-- but we know that the derivation tree has to be the same, so we take the
-- shortcut of just generalizing the data parameters.
generalizeDict :: (EnvReader m) => CType n -> Dict CoreIR n-> m n (Dict CoreIR n)
generalizeDict ty dict = do
  result <- liftSolverM $ solveLocal $ generalizeDictAndUnify (sink ty) (sink dict)
  case result of
    Failure e -> error $ pprint e
    Success ans -> return ans

generalizeDictAndUnify :: EmitsInf n => CType n -> Dict CoreIR n -> SolverM n (Dict CoreIR n)
generalizeDictAndUnify ty dict = do
  dict' <- generalizeDictRec dict
  dictTy <- getType dict'
  unify ty dictTy
  zonk dict'

generalizeDictRec :: EmitsInf n => Dict CoreIR n -> SolverM n (Dict CoreIR n)
generalizeDictRec dict = do
  -- TODO: we should be able to avoid the normalization here . We only need it
  -- because we sometimes end up with superclass projections. But they shouldn't
  -- really be allowed to occur in the post-simplification IR.
  DictCon dict' <- cheapNormalize dict
  DictCon <$> case dict' of
    InstanceDict instanceName args -> do
      InstanceDef _ bs _ _ <- lookupInstanceDef instanceName
      args' <- generalizeInstanceArgs bs args
      return $ InstanceDict instanceName args'
    IxFin _ -> IxFin <$> Var <$> freshInferenceName NatTy
    ExplicitMethods d params -> do
       SpecializedDictBinding (SpecializedDict (Abs bs _) _) <- lookupEnv d
       let bs' = fmapNest (\(b:>ty) -> RolePiBinder b ty PlainArrow DataParam) bs
       params' <- generalizeInstanceArgs bs' params
       return $ ExplicitMethods d params'
    InstantiatedGiven _ _ -> notSimplifiedDict
    SuperclassProj _ _    -> notSimplifiedDict
    where notSimplifiedDict = error $ "Not a simplified dict: " ++ pprint dict

generalizeInstanceArgs :: EmitsInf n => Nest (RolePiBinder CoreIR) n l -> [CAtom n] -> SolverM n [CAtom n]
generalizeInstanceArgs Empty [] = return []
generalizeInstanceArgs (Nest (RolePiBinder b ty _ role) bs) (arg:args) = do
  arg' <- case role of
    -- XXX: for `TypeParam` we can just emit a fresh inference name rather than
    -- traversing the whole type like we do in `Generalize.hs`. The reason is
    -- that it's valid to implement `generalizeDict` by synthesizing an entirely
    -- fresh dictionary, and if we were to do that, we would infer this type
    -- parameter exactly as we do here, using inference.
    TypeParam -> Var <$> freshInferenceName TyKind
    DictParam -> generalizeDictAndUnify ty arg
    DataParam -> Var <$> freshInferenceName ty
  Abs bs' UnitE <- applySubst (b@>SubstVal arg') (Abs bs UnitE)
  args' <- generalizeInstanceArgs bs' args
  return $ arg':args'
generalizeInstanceArgs _ _ = error "zip error"

synthInstanceDef
  :: (EnvReader m, Fallible1 m) => InstanceDef n -> m n (InstanceDef n)
synthInstanceDef (InstanceDef className bs params body) = do
  liftExceptEnvReaderM $ refreshAbs (Abs bs (ListE params `PairE` body))
    \bs' (ListE params' `PairE` InstanceBody superclasses methods) -> do
      methods' <- mapM synthTopBlock methods
      return $ InstanceDef className bs' params' $ InstanceBody superclasses methods'

-- main entrypoint to dictionary synthesizer
trySynthTerm :: (Fallible1 m, EnvReader m) => CType n -> m n (SynthAtom n)
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
type SynthAtom = CAtom

data SynthType n =
   SynthDictType (DictType CoreIR n)
 | SynthPiType (Abs (PiBinder CoreIR) SynthType n)
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

typeAsSynthType :: CType n -> Except (SynthType n)
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
          ClassDef _ _ _ (SuperclassBinders _ superclasses) _ <- lookupClassDef className
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
  SynthDictType dictTy -> case dictTy of
    DictType "Ix" _ [TC (Fin n)] -> return $ DictCon $ IxFin n
    _ -> synthDictFromInstance dictTy <!> synthDictFromGiven dictTy
{-# SCC synthTerm #-}

synthDictFromGiven :: DictType CoreIR n -> SyntherM n (SynthAtom n)
synthDictFromGiven dictTy = do
  givens <- ((HM.elems . fromGivens) <$> getGivens)
  asum $ givens <&> \given -> do
    synthTy <- getSynthType given
    args <- instantiateSynthArgs dictTy synthTy
    case nonEmpty args of
      Nothing -> return given
      Just args' -> return $ DictCon $ InstantiatedGiven given args'

synthDictFromInstance :: DictType CoreIR n -> SyntherM n (SynthAtom n)
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
    go :: Nest (RolePiBinder CoreIR) n l -> SourceName -> ClassName l -> [CAtom l] -> SynthType n
    go bs classSourceName className params = case bs of
      Empty -> SynthDictType $ DictType classSourceName className params
      Nest (RolePiBinder b ty arr _) rest ->
        let restTy = go rest classSourceName className params
        in SynthPiType $ Abs (PiBinder b ty arr) restTy
{-# SCC getInstanceType #-}

instantiateSynthArgs :: DictType CoreIR n -> SynthType n -> SyntherM n [CAtom n]
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
  => [Atom CoreIR n] -> DictType CoreIR n -> SubstFrag (AtomSubstVal CoreIR) n l n
  -> SynthType l -> SolverM n [CAtom n]
instantiateSynthArgsRec prevArgsRec dictTy subst synthTy = case synthTy of
  SynthPiType (Abs (PiBinder b argTy arrow) resultTy) -> do
    argTy' <- applySubst subst argTy
    param <- case arrow of
      ImplicitArrow -> Var <$> freshInferenceName argTy'
      ClassArrow -> return $ Con $ DictHole (AlwaysEqual Nothing) argTy'
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
liftDictSynthTraverserM m = do
  (ans, errs) <- liftGenericTraverserM (coerce $ Errs []) m
  return $ case coerce errs of
    Errs [] -> Success ans
    _       -> Failure $ coerce errs

type DictSynthTraverserM = GenericTraverserM CoreIR UnitB DictSynthTraverserS

newtype DictSynthTraverserS (n::S) = DictSynthTraverserS Errs
instance GenericE DictSynthTraverserS where
  type RepE DictSynthTraverserS = LiftE Errs
  fromE = LiftE . coerce
  toE = coerce . fromLiftE
instance SinkableE DictSynthTraverserS
instance HoistableState DictSynthTraverserS where
  hoistState _ _ (DictSynthTraverserS errs) = DictSynthTraverserS errs

instance GenericTraverser CoreIR UnitB DictSynthTraverserS where
  traverseAtom a@(Con (DictHole (AlwaysEqual ctx) ty)) = do
    ty' <- cheapNormalize =<< substM ty
    ans <- liftEnvReaderT $ addSrcContext ctx $ trySynthTerm ty'
    case ans of
      Failure errs -> put (DictSynthTraverserS errs) >> substM a
      Success d    -> return d
  traverseAtom atom = traverseAtomDefault atom

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
  => (forall l. (EmitsBoth l, DExt n l) => InfererM i l (CAtom l))
  -> InfererM i n (CBlock n)
buildBlockInf cont = buildDeclsInf (cont >>= withType) >>= computeAbsEffects >>= absToBlock
{-# INLINE buildBlockInf #-}

buildLamInf
  :: EmitsInf n
  => NameHint -> Arrow -> CType n
  -> (forall l. (EmitsInf  l, Ext n l) => CAtomName l -> InfererM i l (EffectRow l))
  -> (forall l. (EmitsBoth l, Ext n l) => CAtomName l -> InfererM i l (CAtom l))
  -> InfererM i n (CAtom n)
buildLamInf hint arr ty fEff fBody = do
  Abs (b:>_) (PairE effs body) <-
    buildAbsInf hint (LamBinding arr ty) \v -> do
      effs <- fEff v
      body <- withAllowedEffects effs $ buildBlockInf $ sinkM v >>= fBody
      return $ PairE effs body
  return $ Lam $ LamExpr (LamBinder b ty arr effs) body

buildPiAbsInf
  :: (EmitsInf n, SinkableE e, SubstE Name e, HoistableE e)
  => NameHint -> Arrow -> CType n
  -> (forall l. (EmitsInf l, Ext n l) => CAtomName l -> InfererM i l (e l))
  -> InfererM i n (Abs (PiBinder CoreIR) e n)
buildPiAbsInf hint arr ty body = do
  Abs (b:>_) resultTy <-
    buildAbsInf hint (PiBinding arr ty) \v ->
      withAllowedEffects Pure $ body v
  return $ Abs (PiBinder b ty arr) resultTy

buildPiInf
  :: EmitsInf n
  => NameHint -> Arrow -> CType n
  -> (forall l. (EmitsInf l, Ext n l) => CAtomName l -> InfererM i l (EffectRow l, CType l))
  -> InfererM i n (PiType CoreIR n)
buildPiInf hint arr ty body = do
  Abs (b:>_) (PairE effs resultTy) <-
    buildAbsInf hint (PiBinding arr ty) \v ->
      withAllowedEffects Pure do
        (effs, resultTy) <- body v
        return $ PairE effs resultTy
  return $ PiType (PiBinder b ty arr) effs resultTy

buildTabPiInf
  :: EmitsInf n
  => NameHint -> IxType CoreIR n
  -> (forall l. (EmitsInf l, Ext n l) => CAtomName l -> InfererM i l (CType l))
  -> InfererM i n (TabPiType CoreIR n)
buildTabPiInf hint ty body = do
  Abs (b:>_) resultTy <-
    buildAbsInf hint ty \v ->
      withAllowedEffects Pure $ body v
  return $ TabPiType (b:>ty) resultTy

buildDepPairTyInf
  :: EmitsInf n
  => NameHint -> CType n
  -> (forall l. (EmitsInf l, Ext n l) => CAtomName l -> InfererM i l (CType l))
  -> InfererM i n (DepPairType CoreIR n)
buildDepPairTyInf hint ty body = do
  Abs (b:>_) resultTy <- buildAbsInf hint ty body
  return $ DepPairType (b :> ty) resultTy

buildAltInf
  :: EmitsInf n
  => CType n
  -> (forall l. (EmitsBoth l, Ext n l) => CAtomName l -> InfererM i l (CAtom l))
  -> InfererM i n (Alt CoreIR n)
buildAltInf ty body = do
  buildAbsInf noHint ty \v ->
    buildBlockInf do
      Distinct <- getDistinct
      body $ sink v

-- === EmitsInf predicate ===

type EmitsBoth n = (EmitsInf n, Emits n)

class Mut n => EmitsInf (n::S)
data EmitsInfEvidence (n::S) where
  EmitsInf :: EmitsInf n => EmitsInfEvidence n
instance EmitsInf UnsafeS

fabricateEmitsInfEvidence :: forall n. EmitsInfEvidence n
fabricateEmitsInfEvidence = withFabricatedEmitsInf @n EmitsInf

fabricateEmitsInfEvidenceM :: forall m n. Monad1 m => m n (EmitsInfEvidence n)
fabricateEmitsInfEvidenceM = return fabricateEmitsInfEvidence

withFabricatedEmitsInf :: forall n a. (EmitsInf n => a) -> a
withFabricatedEmitsInf cont = fromWrapWithEmitsInf
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
  type RepE SynthType = EitherE2 (DictType CoreIR) (Abs (PiBinder CoreIR) SynthType)
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
instance SubstE (AtomSubstVal CoreIR) SynthType

-- See Note [Confuse GHC] from Simplify.hs
confuseGHC :: EnvReader m => m n (DistinctEvidence n)
confuseGHC = getDistinct
{-# INLINE confuseGHC #-}
