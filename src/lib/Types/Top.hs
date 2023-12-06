-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StrictData #-}

-- Top-level data types

module Types.Top where

import Data.Functor ((<&>))
import Data.Hashable
import Data.Text.Prettyprint.Doc
import qualified Data.Map.Strict       as M
import qualified Data.Set              as S

import GHC.Generics (Generic (..))
import Data.Store (Store (..))
import Foreign.Ptr

import Name
import Util (FileHash, SnocList (..))
import IRVariants
import PPrint

import Types.Primitives
import Types.Core
import Types.Source
import Types.Imp

type TopBlock = TopLam -- used for nullary lambda
type IsDestLam = Bool
data TopLam (r::IR) (n::S) = TopLam IsDestLam (PiType r n) (LamExpr r n)
     deriving (Show, Generic)
type STopLam = TopLam SimpIR
type CTopLam = TopLam CoreIR

data EvalStatus a = Waiting | Running | Finished a
     deriving (Show, Eq, Ord, Generic, Functor, Foldable, Traversable)
type TopFunEvalStatus n = EvalStatus (TopFunLowerings n)

data TopFun (n::S) =
   DexTopFun (TopFunDef n) (TopLam SimpIR n) (TopFunEvalStatus n)
 | FFITopFun String IFunType
   deriving (Show, Generic)

data TopFunDef (n::S) =
   Specialization       (SpecializationSpec n)
 | LinearizationPrimal  (LinearizationSpec n)
   -- Tangent functions all take some number of nonlinear args, then a *single*
   -- linear arg. This is so that transposition can be an involution - you apply
   -- it twice and you get back to the original function.
 | LinearizationTangent (LinearizationSpec n)
   deriving (Show, Generic)

newtype TopFunLowerings (n::S) = TopFunLowerings
  { topFunObjCode :: FunObjCodeName n } -- TODO: add optimized, imp etc. as needed
  deriving (Show, Generic, SinkableE, HoistableE, RenameE, AlphaEqE, AlphaHashableE, Pretty)

data AtomBinding (r::IR) (n::S) where
 LetBound     :: DeclBinding r  n  -> AtomBinding r n
 MiscBound    :: Type        r  n  -> AtomBinding r n
 TopDataBound :: RepVal n          -> AtomBinding SimpIR n
 SolverBound  :: SolverBinding n   -> AtomBinding CoreIR n
 NoinlineFun  :: CType n -> CAtom n -> AtomBinding CoreIR n
 FFIFunBound  :: CorePiType n -> TopFunName n -> AtomBinding CoreIR n

deriving instance IRRep r => Show (AtomBinding r n)
deriving via WrapE (AtomBinding r) n instance IRRep r => Generic (AtomBinding r n)

data SolverBinding (n::S) =
   InfVarBound (CType n)
 | SkolemBound (CType n)
 | DictBound   (CType n)
   deriving (Show, Generic)

-- TODO: Use an IntMap
newtype CustomRules (n::S) =
  CustomRules { customRulesMap :: M.Map (AtomName CoreIR n) (AtomRules n) }
  deriving (Semigroup, Monoid, Store)
data AtomRules (n::S) =
  -- number of implicit args, number of explicit args, linearization function
  CustomLinearize Int Int SymbolicZeros (CAtom n)
  deriving (Generic)

-- === envs and modules ===

-- `ModuleEnv` contains data that only makes sense in the context of evaluating
-- a particular module. `TopEnv` contains everything that makes sense "between"
-- evaluating modules.
data Env n = Env
  { topEnv    :: {-# UNPACK #-} TopEnv n
  , moduleEnv :: {-# UNPACK #-} ModuleEnv n }
  deriving (Generic)

newtype EnvFrag (n::S) (l::S) = EnvFrag (RecSubstFrag Binding n l)
        deriving (OutFrag)

data TopEnv (n::S) = TopEnv
  { envDefs          :: RecSubst Binding n
  , envCustomRules   :: CustomRules n
  , envCache         :: Cache n
  , envLoadedModules :: LoadedModules n
  , envLoadedObjects :: LoadedObjects n }
  deriving (Generic)

data SerializedEnv n = SerializedEnv
  { serializedEnvDefs        :: RecSubst Binding n
  , serializedEnvCustomRules :: CustomRules n
  , serializedEnvCache       :: Cache n }
  deriving (Generic)

-- TODO: consider splitting this further into `ModuleEnv` (the env that's
-- relevant between top-level decls) and `LocalEnv` (the additional parts of the
-- env that's relevant under a lambda binder). Unlike the Top/Module
-- distinction, there's some overlap. For example, instances can be defined at
-- both the module-level and local level. Similarly, if we start allowing
-- top-level effects in `Main` then we'll have module-level effects and local
-- effects.
data ModuleEnv (n::S) = ModuleEnv
  { envImportStatus    :: ImportStatus n
  , envSourceMap       :: SourceMap n
  , envSynthCandidates :: SynthCandidates n }
  deriving (Generic)

data Module (n::S) = Module
  { moduleSourceName :: ModuleSourceName
  , moduleDirectDeps :: S.Set (ModuleName n)
  , moduleTransDeps  :: S.Set (ModuleName n)  -- XXX: doesn't include the module itself
  , moduleExports    :: SourceMap n
    -- these are just the synth candidates required by this
    -- module by itself. We'll usually also need those required by the module's
    -- (transitive) dependencies, which must be looked up separately.
  , moduleSynthCandidates :: SynthCandidates n }
  deriving (Show, Generic)

data LoadedModules (n::S) = LoadedModules
  { fromLoadedModules   :: M.Map ModuleSourceName (ModuleName n)}
  deriving (Show, Generic)

emptyModuleEnv :: ModuleEnv n
emptyModuleEnv = ModuleEnv emptyImportStatus (SourceMap mempty) mempty

emptyLoadedModules :: LoadedModules n
emptyLoadedModules = LoadedModules mempty

data LoadedObjects (n::S) = LoadedObjects
  -- the pointer points to the actual runtime function
  { fromLoadedObjects :: M.Map (FunObjCodeName n) NativeFunction}
  deriving (Show, Generic)

emptyLoadedObjects :: LoadedObjects n
emptyLoadedObjects = LoadedObjects mempty

data ImportStatus (n::S) = ImportStatus
  { directImports :: S.Set (ModuleName n)
    -- XXX: This are cached for efficiency. It's derivable from `directImports`.
  , transImports           :: S.Set (ModuleName n) }
  deriving (Show, Generic)

data TopEnvFrag n l = TopEnvFrag (EnvFrag n l) (ModuleEnv l) (SnocList (TopEnvUpdate l))

data TopEnvUpdate n =
   ExtendCache              (Cache n)
 | AddCustomRule            (CAtomName n) (AtomRules n)
 | UpdateLoadedModules      ModuleSourceName (ModuleName n)
 | UpdateLoadedObjects      (FunObjCodeName n) NativeFunction
 | FinishDictSpecialization (SpecDictName n) [TopLam SimpIR n]
 | LowerDictSpecialization  (SpecDictName n) [TopLam SimpIR n]
 | UpdateTopFunEvalStatus   (TopFunName n) (TopFunEvalStatus n)
 | UpdateInstanceDef        (InstanceName n) (InstanceDef n)
 | UpdateTyConDef           (TyConName n) (TyConDef n)
 | UpdateFieldDef           (TyConName n) SourceName (CAtomName n)

-- TODO: we could add a lot more structure for querying by dict type, caching, etc.
data SynthCandidates n = SynthCandidates
  { instanceDicts     :: M.Map (ClassName n) [InstanceName n]
  , ixInstances       :: [InstanceName n] }
  deriving (Show, Generic)

emptyImportStatus :: ImportStatus n
emptyImportStatus = ImportStatus mempty mempty

-- TODO: figure out the additional top-level context we need -- backend, other
-- compiler flags etc. We can have a map from those to this.

data Cache (n::S) = Cache
  { specializationCache :: EMap SpecializationSpec TopFunName n
  , ixDictCache :: EMap AbsDict SpecDictName n
  , linearizationCache :: EMap LinearizationSpec (PairE TopFunName TopFunName) n
  , transpositionCache :: EMap TopFunName TopFunName n
    -- This is memoizing `parseAndGetDeps :: Text -> [ModuleSourceName]`. But we
    -- only want to store one entry per module name as a simple cache eviction
    -- policy, so we store it keyed on the module name, with the text hash for
    -- the validity check.
  , parsedDeps :: M.Map ModuleSourceName (FileHash, [ModuleSourceName])
  , moduleEvaluations :: M.Map ModuleSourceName ((FileHash, [ModuleName n]), ModuleName n)
  } deriving (Show, Generic)

-- === runtime function and variable representations ===

type RuntimeEnv = DynamicVarKeyPtrs

type DexDestructor = FunPtr (IO ())

data NativeFunction = NativeFunction
  { nativeFunPtr      :: FunPtr ()
  , nativeFunTeardown :: IO () }

instance Show NativeFunction where
  show _ = "<native function>"

-- Holds pointers to thread-local storage used to simulate dynamically scoped
-- variables, such as the output stream file descriptor.
type DynamicVarKeyPtrs = [(DynamicVar, Ptr ())]

data DynamicVar = OutStreamDyvar -- TODO: add others as needed
                  deriving (Enum, Bounded)

dynamicVarCName :: DynamicVar -> String
dynamicVarCName OutStreamDyvar = "dex_out_stream_dyvar"

dynamicVarLinkMap :: DynamicVarKeyPtrs -> [(String, Ptr ())]
dynamicVarLinkMap dyvars = dyvars <&> \(v, ptr) -> (dynamicVarCName v, ptr)

-- === Specialization and generalization ===

type Generalized (r::IR) (e::E) (n::S) = (Abstracted r e n, [Atom r n])
type Abstracted (r::IR) (e::E) = Abs (Nest (Binder r)) e
type AbsDict = Abstracted CoreIR (Dict CoreIR)

data SpecializedDictDef n =
   SpecializedDict
     (AbsDict n)
     -- Methods (thunked if nullary), if they're available.
     -- We create specialized dict names during simplification, but we don't
     -- actually simplify/lower them until we return to TopLevel
     (Maybe [TopLam SimpIR n])
   deriving (Show, Generic)

-- TODO: extend with AD-oriented specializations, backend-specific specializations etc.
data SpecializationSpec (n::S) =
   AppSpecialization (AtomVar CoreIR n) (Abstracted CoreIR (ListE CAtom) n)
   deriving (Show, Generic)

type Active = Bool
data LinearizationSpec (n::S) = LinearizationSpec (TopFunName n) [Active]
     deriving (Show, Generic)

-- === bindings - static information we carry about a lexical scope ===

-- TODO: consider making this an open union via a typeable-like class
data Binding (c::C) (n::S) where
  AtomNameBinding   :: AtomBinding r n                -> Binding (AtomNameC r)   n
  TyConBinding      :: Maybe (TyConDef n) -> DotMethods n -> Binding TyConNameC      n
  DataConBinding    :: TyConName n -> Int             -> Binding DataConNameC    n
  ClassBinding      :: ClassDef n                     -> Binding ClassNameC      n
  InstanceBinding   :: InstanceDef n -> CorePiType n  -> Binding InstanceNameC   n
  MethodBinding     :: ClassName n   -> Int           -> Binding MethodNameC     n
  TopFunBinding     :: TopFun n                       -> Binding TopFunNameC     n
  FunObjCodeBinding :: CFunction n                    -> Binding FunObjCodeNameC n
  ModuleBinding     :: Module n                       -> Binding ModuleNameC     n
  -- TODO: add a case for abstracted pointers, as used in `ClosedImpFunction`
  PtrBinding        :: PtrType -> PtrLitVal           -> Binding PtrNameC        n
  SpecializedDictBinding :: SpecializedDictDef n      -> Binding SpecializedDictNameC n
  ImpNameBinding    :: BaseType                       -> Binding ImpNameC n

-- === ToBinding ===

atomBindingToBinding :: AtomBinding r n -> Binding (AtomNameC r) n
atomBindingToBinding b = AtomNameBinding b

bindingToAtomBinding :: Binding (AtomNameC r) n -> AtomBinding r n
bindingToAtomBinding (AtomNameBinding b) = b

class (RenameE     e, SinkableE e) => ToBinding (e::E) (c::C) | e -> c where
  toBinding :: e n -> Binding c n

instance Color c => ToBinding (Binding c) c where
  toBinding = id

instance IRRep r => ToBinding (AtomBinding r) (AtomNameC r) where
  toBinding = atomBindingToBinding

instance IRRep r => ToBinding (DeclBinding r) (AtomNameC r) where
  toBinding = toBinding . LetBound

instance IRRep r => ToBinding (Type r) (AtomNameC r) where
  toBinding = toBinding . MiscBound

instance ToBinding SolverBinding (AtomNameC CoreIR) where
  toBinding = toBinding . SolverBound

instance IRRep r => ToBinding (IxType r) (AtomNameC r) where
  toBinding (IxType t _) = toBinding t

instance (ToBinding e1 c, ToBinding e2 c) => ToBinding (EitherE e1 e2) c where
  toBinding (LeftE  e) = toBinding e
  toBinding (RightE e) = toBinding e

instance ToBindersAbs (TopLam r) (Expr r) r where
  toAbs (TopLam _ _ lam) = toAbs lam

-- === GenericE, GenericB ===

instance GenericE SpecializedDictDef where
  type RepE SpecializedDictDef = AbsDict `PairE` MaybeE (ListE (TopLam SimpIR))
  fromE (SpecializedDict ab methods) = ab `PairE` methods'
    where methods' = case methods of Just xs -> LeftE (ListE xs)
                                     Nothing -> RightE UnitE
  {-# INLINE fromE #-}
  toE   (ab `PairE` methods) = SpecializedDict ab methods'
    where methods' = case methods of LeftE (ListE xs) -> Just xs
                                     RightE UnitE     -> Nothing
  {-# INLINE toE #-}

instance SinkableE      SpecializedDictDef
instance HoistableE     SpecializedDictDef
instance AlphaEqE       SpecializedDictDef
instance AlphaHashableE SpecializedDictDef
instance RenameE        SpecializedDictDef

instance HasScope Env where
  toScope = toScope . envDefs . topEnv

instance OutMap Env where
  emptyOutMap =
    Env (TopEnv (RecSubst emptyInFrag) mempty mempty emptyLoadedModules emptyLoadedObjects)
        emptyModuleEnv
  {-# INLINE emptyOutMap #-}

instance ExtOutMap Env (RecSubstFrag Binding)  where
  -- TODO: We might want to reorganize this struct to make this
  -- do less explicit sinking etc. It's a hot operation!
  extendOutMap (Env (TopEnv defs rules cache loadedM loadedO) moduleEnv) frag =
    withExtEvidence frag $ Env
      (TopEnv
        (defs  `extendRecSubst` frag)
        (sink rules)
        (sink cache)
        (sink loadedM)
        (sink loadedO))
      (sink moduleEnv)
  {-# INLINE extendOutMap #-}

instance ExtOutMap Env EnvFrag where
  extendOutMap = extendEnv
  {-# INLINE extendOutMap #-}

extendEnv :: Distinct l => Env n -> EnvFrag n l -> Env l
extendEnv env (EnvFrag newEnv) = do
  case extendOutMap env newEnv of
    Env envTop (ModuleEnv imports sm scs) -> do
      Env envTop (ModuleEnv imports sm scs)
{-# NOINLINE [1] extendEnv #-}


instance GenericE AtomRules where
  type RepE AtomRules = (LiftE (Int, Int, SymbolicZeros)) `PairE` CAtom
  fromE (CustomLinearize ni ne sz a) = LiftE (ni, ne, sz) `PairE` a
  toE (LiftE (ni, ne, sz) `PairE` a) = CustomLinearize ni ne sz a
instance SinkableE AtomRules
instance HoistableE AtomRules
instance AlphaEqE AtomRules
instance RenameE     AtomRules

instance GenericE CustomRules where
  type RepE CustomRules = ListE (PairE (AtomName CoreIR) AtomRules)
  fromE (CustomRules m) = ListE $ toPairE <$> M.toList m
  toE (ListE l) = CustomRules $ M.fromList $ fromPairE <$> l
instance SinkableE CustomRules
instance HoistableE CustomRules
instance AlphaEqE CustomRules
instance RenameE     CustomRules

instance GenericE Cache where
  type RepE Cache =
            EMap SpecializationSpec TopFunName
    `PairE` EMap AbsDict SpecDictName
    `PairE` EMap LinearizationSpec (PairE TopFunName TopFunName)
    `PairE` EMap TopFunName TopFunName
    `PairE` LiftE (M.Map ModuleSourceName (FileHash, [ModuleSourceName]))
    `PairE` ListE (        LiftE ModuleSourceName
                   `PairE` LiftE FileHash
                   `PairE` ListE ModuleName
                   `PairE` ModuleName)
  fromE (Cache x y z w parseCache evalCache) =
    x `PairE` y `PairE` z `PairE` w `PairE` LiftE parseCache `PairE`
      ListE [LiftE sourceName `PairE` LiftE hashVal `PairE` ListE deps `PairE` result
             | (sourceName, ((hashVal, deps), result)) <- M.toList evalCache ]
  {-# INLINE fromE #-}
  toE   (x `PairE` y `PairE` z `PairE` w `PairE` LiftE parseCache `PairE` ListE evalCache) =
    Cache x y z w parseCache
      (M.fromList
       [(sourceName, ((hashVal, deps), result))
       | LiftE sourceName `PairE` LiftE hashVal `PairE` ListE deps `PairE` result
          <- evalCache])
  {-# INLINE toE #-}

instance SinkableE  Cache
instance HoistableE Cache
instance AlphaEqE   Cache
instance RenameE     Cache
instance Store (Cache n)

instance Monoid (Cache n) where
  mempty = Cache mempty mempty mempty mempty mempty mempty
  mappend = (<>)

instance Semigroup (Cache n) where
  -- right-biased instead of left-biased
  Cache x1 x2 x3 x4 x5 x6 <> Cache y1 y2 y3 y4 y5 y6 =
    Cache (y1<>x1) (y2<>x2) (y3<>x3) (y4<>x4) (x5<>y5) (x6<>y6)


instance GenericE SynthCandidates where
  type RepE SynthCandidates = ListE (PairE ClassName (ListE InstanceName))
                      `PairE` ListE InstanceName
  fromE (SynthCandidates xs ys) = ListE xs' `PairE` ListE ys
    where xs' = map (\(k,vs) -> PairE k (ListE vs)) (M.toList xs)
  {-# INLINE fromE #-}
  toE (ListE xs `PairE` ListE ys) = SynthCandidates xs' ys
    where xs' = M.fromList $ map (\(PairE k (ListE vs)) -> (k,vs)) xs
  {-# INLINE toE #-}

instance SinkableE      SynthCandidates
instance HoistableE     SynthCandidates
instance AlphaEqE       SynthCandidates
instance AlphaHashableE SynthCandidates
instance RenameE        SynthCandidates

instance IRRep r => GenericE (AtomBinding r) where
  type RepE (AtomBinding r) =
     EitherE2 (EitherE3
      (DeclBinding   r)              -- LetBound
      (Type          r)              -- MiscBound
      (WhenCore r SolverBinding)     -- SolverBound
     ) (EitherE3
      (WhenCore r (PairE CType CAtom))               -- NoinlineFun
      (WhenSimp r RepVal)                            -- TopDataBound
      (WhenCore r (CorePiType `PairE` TopFunName))   -- FFIFunBound
     )

  fromE = \case
    LetBound    x -> Case0 $ Case0 x
    MiscBound   x -> Case0 $ Case1 x
    SolverBound x -> Case0 $ Case2 $ WhenIRE x
    NoinlineFun t x -> Case1 $ Case0 $ WhenIRE $ PairE t x
    TopDataBound repVal -> Case1 $ Case1 $ WhenIRE repVal
    FFIFunBound ty v    -> Case1 $ Case2 $ WhenIRE $ ty `PairE` v
  {-# INLINE fromE #-}

  toE = \case
    Case0 x' -> case x' of
      Case0 x         -> LetBound x
      Case1 x           -> MiscBound x
      Case2 (WhenIRE x) -> SolverBound x
      _ -> error "impossible"
    Case1 x' -> case x' of
      Case0 (WhenIRE (PairE t x)) -> NoinlineFun t x
      Case1 (WhenIRE repVal)                         -> TopDataBound repVal
      Case2 (WhenIRE (ty `PairE` v))                 -> FFIFunBound ty v
      _ -> error "impossible"
    _ -> error "impossible"
  {-# INLINE toE #-}


instance IRRep r => SinkableE   (AtomBinding r)
instance IRRep r => HoistableE  (AtomBinding r)
instance IRRep r => RenameE     (AtomBinding r)
instance IRRep r => AlphaEqE       (AtomBinding r)
instance IRRep r => AlphaHashableE (AtomBinding r)

instance GenericE TopFunDef where
  type RepE TopFunDef = EitherE3 SpecializationSpec LinearizationSpec LinearizationSpec
  fromE = \case
    Specialization       s -> Case0 s
    LinearizationPrimal  s -> Case1 s
    LinearizationTangent s -> Case2 s
  {-# INLINE fromE #-}
  toE = \case
    Case0 s ->   Specialization       s
    Case1 s ->   LinearizationPrimal  s
    Case2 s ->   LinearizationTangent s
    _ -> error "impossible"
  {-# INLINE toE #-}

instance SinkableE      TopFunDef
instance HoistableE     TopFunDef
instance RenameE        TopFunDef
instance AlphaEqE       TopFunDef
instance AlphaHashableE TopFunDef

instance IRRep r => GenericE (TopLam r) where
  type RepE (TopLam r) = LiftE Bool `PairE` PiType r `PairE` LamExpr r
  fromE (TopLam d x y) = LiftE d `PairE` x `PairE` y
  {-# INLINE fromE #-}
  toE (LiftE d `PairE` x `PairE` y) = TopLam d x y
  {-# INLINE toE #-}

instance IRRep r => SinkableE      (TopLam r)
instance IRRep r => HoistableE     (TopLam r)
instance IRRep r => RenameE        (TopLam r)
instance IRRep r => AlphaEqE       (TopLam r)
instance IRRep r => AlphaHashableE (TopLam r)

instance GenericE TopFun where
  type RepE TopFun = EitherE
        (TopFunDef `PairE` TopLam SimpIR `PairE` ComposeE EvalStatus TopFunLowerings)
        (LiftE (String, IFunType))
  fromE = \case
    DexTopFun def lam status -> LeftE (def `PairE` lam `PairE` ComposeE status)
    FFITopFun name ty    -> RightE (LiftE (name, ty))
  {-# INLINE fromE #-}
  toE = \case
    LeftE  (def `PairE` lam `PairE` ComposeE status) -> DexTopFun def lam status
    RightE (LiftE (name, ty))            -> FFITopFun name ty
  {-# INLINE toE #-}

instance SinkableE      TopFun
instance HoistableE     TopFun
instance RenameE        TopFun
instance AlphaEqE       TopFun
instance AlphaHashableE TopFun

instance GenericE SpecializationSpec where
  type RepE SpecializationSpec =
         PairE (AtomVar CoreIR) (Abs (Nest (Binder CoreIR)) (ListE CAtom))
  fromE (AppSpecialization fname (Abs bs args)) = PairE fname (Abs bs args)
  {-# INLINE fromE #-}
  toE   (PairE fname (Abs bs args)) = AppSpecialization fname (Abs bs args)
  {-# INLINE toE #-}

instance HasNameHint (SpecializationSpec n) where
  getNameHint (AppSpecialization f _) = getNameHint f

instance SinkableE      SpecializationSpec
instance HoistableE     SpecializationSpec
instance RenameE        SpecializationSpec
instance AlphaEqE       SpecializationSpec
instance AlphaHashableE SpecializationSpec

instance GenericE LinearizationSpec where
  type RepE LinearizationSpec = PairE TopFunName (LiftE [Active])
  fromE (LinearizationSpec fname actives) = PairE fname (LiftE actives)
  {-# INLINE fromE #-}
  toE   (PairE fname (LiftE actives)) = LinearizationSpec fname actives
  {-# INLINE toE #-}

instance SinkableE      LinearizationSpec
instance HoistableE     LinearizationSpec
instance RenameE        LinearizationSpec
instance AlphaEqE       LinearizationSpec
instance AlphaHashableE LinearizationSpec

instance GenericE SolverBinding where
  type RepE SolverBinding = EitherE3
                                  CType
                                  CType
                                  CType
  fromE = \case
    InfVarBound ty -> Case0 ty
    SkolemBound ty -> Case1 ty
    DictBound   ty -> Case2 ty
  {-# INLINE fromE #-}

  toE = \case
    Case0 ty -> InfVarBound ty
    Case1 ty -> SkolemBound ty
    Case2 ty -> DictBound   ty
    _ -> error "impossible"
  {-# INLINE toE #-}

instance SinkableE   SolverBinding
instance HoistableE  SolverBinding
instance RenameE     SolverBinding
instance AlphaEqE       SolverBinding
instance AlphaHashableE SolverBinding

instance GenericE (Binding c) where
  type RepE (Binding c) =
    EitherE3
      (EitherE6
          (WhenAtomName        c AtomBinding)
          (WhenC TyConNameC    c (MaybeE TyConDef `PairE` DotMethods))
          (WhenC DataConNameC  c (TyConName `PairE` LiftE Int))
          (WhenC ClassNameC    c (ClassDef))
          (WhenC InstanceNameC c (InstanceDef `PairE` CorePiType))
          (WhenC MethodNameC   c (ClassName `PairE` LiftE Int)))
      (EitherE4
          (WhenC TopFunNameC     c (TopFun))
          (WhenC FunObjCodeNameC c (CFunction))
          (WhenC ModuleNameC     c (Module))
          (WhenC PtrNameC        c (LiftE (PtrType, PtrLitVal))))
      (EitherE2
          (WhenC SpecializedDictNameC c (SpecializedDictDef))
          (WhenC ImpNameC             c (LiftE BaseType)))

  fromE = \case
    AtomNameBinding   binding           -> Case0 $ Case0 $ WhenAtomName binding
    TyConBinding      dataDef methods   -> Case0 $ Case1 $ WhenC $ toMaybeE dataDef `PairE` methods
    DataConBinding    dataDefName idx   -> Case0 $ Case2 $ WhenC $ dataDefName `PairE` LiftE idx
    ClassBinding      classDef          -> Case0 $ Case3 $ WhenC $ classDef
    InstanceBinding   instanceDef ty    -> Case0 $ Case4 $ WhenC $ instanceDef `PairE` ty
    MethodBinding     className idx     -> Case0 $ Case5 $ WhenC $ className `PairE` LiftE idx
    TopFunBinding     fun               -> Case1 $ Case0 $ WhenC $ fun
    FunObjCodeBinding cFun              -> Case1 $ Case1 $ WhenC $ cFun
    ModuleBinding m                     -> Case1 $ Case2 $ WhenC $ m
    PtrBinding ty p                     -> Case1 $ Case3 $ WhenC $ LiftE (ty,p)
    SpecializedDictBinding def          -> Case2 $ Case0 $ WhenC $ def
    ImpNameBinding ty                   -> Case2 $ Case1 $ WhenC $ LiftE ty
  {-# INLINE fromE #-}

  toE = \case
    Case0 (Case0 (WhenAtomName binding))           -> AtomNameBinding   binding
    Case0 (Case1 (WhenC (def `PairE` methods)))    -> TyConBinding      (fromMaybeE def) methods
    Case0 (Case2 (WhenC (n `PairE` LiftE idx)))    -> DataConBinding    n idx
    Case0 (Case3 (WhenC (classDef)))               -> ClassBinding      classDef
    Case0 (Case4 (WhenC (instanceDef `PairE` ty))) -> InstanceBinding   instanceDef ty
    Case0 (Case5 (WhenC ((n `PairE` LiftE i))))    -> MethodBinding     n i
    Case1 (Case0 (WhenC (fun)))                    -> TopFunBinding     fun
    Case1 (Case1 (WhenC (f)))                      -> FunObjCodeBinding f
    Case1 (Case2 (WhenC (m)))                      -> ModuleBinding     m
    Case1 (Case3 (WhenC ((LiftE (ty,p)))))         -> PtrBinding        ty p
    Case2 (Case0 (WhenC (def)))                    -> SpecializedDictBinding def
    Case2 (Case1 (WhenC ((LiftE ty))))             -> ImpNameBinding    ty
    _ -> error "impossible"
  {-# INLINE toE #-}

deriving via WrapE (Binding c) n instance Generic (Binding c n)
instance SinkableV         Binding
instance HoistableV        Binding
instance RenameV           Binding
instance Color c => SinkableE   (Binding c)
instance Color c => HoistableE  (Binding c)
instance Color c => RenameE     (Binding c)

instance Semigroup (SynthCandidates n) where
  SynthCandidates xs ys <> SynthCandidates xs' ys' =
    SynthCandidates (M.unionWith (<>) xs xs') (ys <> ys')

instance Monoid (SynthCandidates n) where
  mempty = SynthCandidates mempty mempty

instance GenericB EnvFrag where
  type RepB EnvFrag = RecSubstFrag Binding
  fromB (EnvFrag frag) = frag
  toB   frag = EnvFrag frag

instance SinkableB   EnvFrag
instance HoistableB  EnvFrag
instance ProvesExt   EnvFrag
instance BindsNames  EnvFrag
instance RenameB     EnvFrag

instance GenericE TopEnvUpdate where
  type RepE TopEnvUpdate = EitherE2 (
      EitherE4
    {- ExtendCache -}              Cache
    {- AddCustomRule -}            (CAtomName `PairE` AtomRules)
    {- UpdateLoadedModules -}      (LiftE ModuleSourceName `PairE` ModuleName)
    {- UpdateLoadedObjects -}      (FunObjCodeName `PairE` LiftE NativeFunction)
      ) ( EitherE6
    {- FinishDictSpecialization -} (SpecDictName `PairE` ListE (TopLam SimpIR))
    {- LowerDictSpecialization -}  (SpecDictName `PairE` ListE (TopLam SimpIR))
    {- UpdateTopFunEvalStatus -}   (TopFunName `PairE` ComposeE EvalStatus TopFunLowerings)
    {- UpdateInstanceDef -}        (InstanceName `PairE` InstanceDef)
    {- UpdateTyConDef -}           (TyConName `PairE` TyConDef)
    {- UpdateFieldDef -}           (TyConName `PairE` LiftE SourceName `PairE` CAtomName)
        )
  fromE = \case
    ExtendCache x                -> Case0 $ Case0 x
    AddCustomRule x y            -> Case0 $ Case1 (x `PairE` y)
    UpdateLoadedModules x y      -> Case0 $ Case2 (LiftE x `PairE` y)
    UpdateLoadedObjects x y      -> Case0 $ Case3 (x `PairE` LiftE y)
    FinishDictSpecialization x y -> Case1 $ Case0 (x `PairE` ListE y)
    LowerDictSpecialization x y  -> Case1 $ Case1 (x `PairE` ListE y)
    UpdateTopFunEvalStatus x y   -> Case1 $ Case2 (x `PairE` ComposeE y)
    UpdateInstanceDef x y        -> Case1 $ Case3 (x `PairE` y)
    UpdateTyConDef x y           -> Case1 $ Case4 (x `PairE` y)
    UpdateFieldDef x y z         -> Case1 $ Case5 (x `PairE` LiftE y `PairE` z)

  toE = \case
    Case0 e -> case e of
      Case0 x                   -> ExtendCache x
      Case1 (x `PairE` y)       -> AddCustomRule x y
      Case2 (LiftE x `PairE` y) -> UpdateLoadedModules x y
      Case3 (x `PairE` LiftE y) -> UpdateLoadedObjects x y
      _ -> error "impossible"
    Case1 e -> case e of
      Case0 (x `PairE` ListE y)           -> FinishDictSpecialization x y
      Case1 (x `PairE` ListE y)           -> LowerDictSpecialization x y
      Case2 (x `PairE` ComposeE y)        -> UpdateTopFunEvalStatus x y
      Case3 (x `PairE` y)                 -> UpdateInstanceDef x y
      Case4 (x `PairE` y)                 -> UpdateTyConDef x y
      Case5 (x `PairE` LiftE y `PairE` z) -> UpdateFieldDef x y z
      _ -> error "impossible"
    _ -> error "impossible"

instance SinkableE   TopEnvUpdate
instance HoistableE  TopEnvUpdate
instance RenameE     TopEnvUpdate

instance GenericB TopEnvFrag where
  type RepB TopEnvFrag = PairB EnvFrag (LiftB (ModuleEnv `PairE` ListE TopEnvUpdate))
  fromB (TopEnvFrag x y (ReversedList z)) = PairB x (LiftB (y `PairE` ListE z))
  toB   (PairB x (LiftB (y `PairE` ListE z))) = TopEnvFrag x y (ReversedList z)

instance RenameB     TopEnvFrag
instance HoistableB  TopEnvFrag
instance SinkableB TopEnvFrag
instance ProvesExt   TopEnvFrag
instance BindsNames  TopEnvFrag

instance OutFrag TopEnvFrag where
  emptyOutFrag = TopEnvFrag emptyOutFrag mempty mempty
  {-# INLINE emptyOutFrag #-}
  catOutFrags (TopEnvFrag frag1 env1 partial1)
              (TopEnvFrag frag2 env2 partial2) =
    withExtEvidence frag2 $
      TopEnvFrag
        (catOutFrags frag1 frag2)
        (sink env1 <> env2)
        (sinkSnocList partial1 <> partial2)
  {-# INLINE catOutFrags #-}

-- XXX: unlike `ExtOutMap Env EnvFrag` instance, this once doesn't
-- extend the synthesis candidates based on the annotated let-bound names. It
-- only extends synth candidates when they're supplied explicitly.
instance ExtOutMap Env TopEnvFrag where
  extendOutMap env (TopEnvFrag (EnvFrag frag) mEnv' otherUpdates) = do
    let newerTopEnv = foldl applyUpdate newTopEnv otherUpdates
    Env newerTopEnv newModuleEnv
    where
      Env (TopEnv defs rules cache loadedM loadedO) mEnv = env

      newTopEnv = withExtEvidence frag $ TopEnv
        (defs `extendRecSubst` frag)
        (sink rules) (sink cache) (sink loadedM) (sink loadedO)

      newModuleEnv =
        ModuleEnv
          (imports <> imports')
          (sm   <> sm'   <> newImportedSM)
          (scs  <> scs'  <> newImportedSC)
        where
          ModuleEnv imports sm scs = withExtEvidence frag $ sink mEnv
          ModuleEnv imports' sm' scs' = mEnv'
          newDirectImports = S.difference (directImports imports') (directImports imports)
          newTransImports  = S.difference (transImports  imports') (transImports  imports)
          newImportedSM  = flip foldMap newDirectImports $ moduleExports         . lookupModulePure
          newImportedSC  = flip foldMap newTransImports  $ moduleSynthCandidates . lookupModulePure

      lookupModulePure v = case lookupEnvPure newTopEnv v of ModuleBinding m -> m

applyUpdate :: TopEnv n -> TopEnvUpdate n -> TopEnv n
applyUpdate e = \case
  ExtendCache cache -> e { envCache = envCache e <> cache}
  AddCustomRule x y       -> e { envCustomRules   = envCustomRules   e <> CustomRules   (M.singleton x y)}
  UpdateLoadedModules x y -> e { envLoadedModules = envLoadedModules e <> LoadedModules (M.singleton x y)}
  UpdateLoadedObjects x y -> e { envLoadedObjects = envLoadedObjects e <> LoadedObjects (M.singleton x y)}
  FinishDictSpecialization dName methods -> do
    let SpecializedDictBinding (SpecializedDict dAbs oldMethods) = lookupEnvPure e dName
    case oldMethods of
      Nothing -> do
        let newBinding = SpecializedDictBinding $ SpecializedDict dAbs (Just methods)
        updateEnv dName newBinding e
      Just _ -> error "shouldn't be adding methods if we already have them"
  LowerDictSpecialization dName methods -> do
    let SpecializedDictBinding (SpecializedDict dAbs _) = lookupEnvPure e dName
    let newBinding = SpecializedDictBinding $ SpecializedDict dAbs (Just methods)
    updateEnv dName newBinding e
  UpdateTopFunEvalStatus f s -> do
    case lookupEnvPure e f of
      TopFunBinding (DexTopFun def lam _) ->
        updateEnv f (TopFunBinding $ DexTopFun def lam s) e
      _ -> error "can't update ffi function impl"
  UpdateInstanceDef name def -> do
    case lookupEnvPure e name of
      InstanceBinding _ ty -> updateEnv name (InstanceBinding def ty) e
  UpdateTyConDef name def -> do
    let TyConBinding _ methods = lookupEnvPure e name
    updateEnv name (TyConBinding (Just def) methods) e
  UpdateFieldDef name sn x -> do
    let TyConBinding def methods = lookupEnvPure e name
    updateEnv name (TyConBinding def (methods <> DotMethods (M.singleton sn x))) e

updateEnv :: Color c => Name c n -> Binding c n -> TopEnv n -> TopEnv n
updateEnv v rhs env =
  env { envDefs = RecSubst $ updateSubstFrag v rhs bs }
  where (RecSubst bs) = envDefs env

lookupEnvPure :: Color c => TopEnv n -> Name c n -> Binding c n
lookupEnvPure env v = lookupTerminalSubstFrag (fromRecSubst $ envDefs $ env) v

instance GenericE Module where
  type RepE Module =       LiftE ModuleSourceName
                   `PairE` ListE ModuleName
                   `PairE` ListE ModuleName
                   `PairE` SourceMap
                   `PairE` SynthCandidates

  fromE (Module name deps transDeps sm sc) =
    LiftE name `PairE` ListE (S.toList deps) `PairE` ListE (S.toList transDeps)
      `PairE` sm `PairE` sc
  {-# INLINE fromE #-}

  toE (LiftE name `PairE` ListE deps `PairE` ListE transDeps
         `PairE` sm `PairE` sc) =
    Module name (S.fromList deps) (S.fromList transDeps) sm sc
  {-# INLINE toE #-}

instance SinkableE      Module
instance HoistableE     Module
instance AlphaEqE       Module
instance AlphaHashableE Module
instance RenameE        Module

instance GenericE ImportStatus where
  type RepE ImportStatus = ListE ModuleName `PairE` ListE ModuleName
  fromE (ImportStatus direct trans) = ListE (S.toList direct)
                              `PairE` ListE (S.toList trans)
  {-# INLINE fromE #-}
  toE (ListE direct `PairE` ListE trans) =
    ImportStatus (S.fromList direct) (S.fromList trans)
  {-# INLINE toE #-}

instance SinkableE      ImportStatus
instance HoistableE     ImportStatus
instance AlphaEqE       ImportStatus
instance AlphaHashableE ImportStatus
instance RenameE        ImportStatus

instance Semigroup (ImportStatus n) where
  ImportStatus direct trans <> ImportStatus direct' trans' =
    ImportStatus (direct <> direct') (trans <> trans')

instance Monoid (ImportStatus n) where
  mappend = (<>)
  mempty = ImportStatus mempty mempty

instance GenericE LoadedModules where
  type RepE LoadedModules = ListE (PairE (LiftE ModuleSourceName) ModuleName)
  fromE (LoadedModules m) =
    ListE $ M.toList m <&> \(v,md) -> PairE (LiftE v) md
  {-# INLINE fromE #-}
  toE (ListE pairs) =
    LoadedModules $ M.fromList $ pairs <&> \(PairE (LiftE v) md) -> (v, md)
  {-# INLINE toE #-}

instance SinkableE      LoadedModules
instance HoistableE     LoadedModules
instance AlphaEqE       LoadedModules
instance AlphaHashableE LoadedModules
instance RenameE        LoadedModules

instance GenericE LoadedObjects where
  type RepE LoadedObjects = ListE (PairE FunObjCodeName (LiftE NativeFunction))
  fromE (LoadedObjects m) =
    ListE $ M.toList m <&> \(v,p) -> PairE v (LiftE p)
  {-# INLINE fromE #-}
  toE (ListE pairs) =
    LoadedObjects $ M.fromList $ pairs <&> \(PairE v (LiftE p)) -> (v, p)
  {-# INLINE toE #-}

instance SinkableE      LoadedObjects
instance HoistableE     LoadedObjects
instance RenameE        LoadedObjects

instance GenericE ModuleEnv where
  type RepE ModuleEnv = ImportStatus
                `PairE` SourceMap
                `PairE` SynthCandidates
  fromE (ModuleEnv imports sm sc) = imports `PairE` sm `PairE` sc
  {-# INLINE fromE #-}
  toE   (imports `PairE` sm `PairE` sc) = ModuleEnv imports sm sc
  {-# INLINE toE #-}

instance SinkableE      ModuleEnv
instance HoistableE     ModuleEnv
instance AlphaEqE       ModuleEnv
instance AlphaHashableE ModuleEnv
instance RenameE        ModuleEnv

instance Semigroup (ModuleEnv n) where
  ModuleEnv x1 x2 x3 <> ModuleEnv y1 y2 y3 =
    ModuleEnv (x1<>y1) (x2<>y2) (x3<>y3)

instance Monoid (ModuleEnv n) where
  mempty = ModuleEnv mempty mempty mempty

instance Semigroup (LoadedModules n) where
  LoadedModules m1 <> LoadedModules m2 = LoadedModules (m2 <> m1)

instance Monoid (LoadedModules n) where
  mempty = LoadedModules mempty

instance Semigroup (LoadedObjects n) where
  LoadedObjects m1 <> LoadedObjects m2 = LoadedObjects (m2 <> m1)

instance Monoid (LoadedObjects n) where
  mempty = LoadedObjects mempty


-- === instance ===

prettyRecord :: [(String, Doc ann)] -> Doc ann
prettyRecord xs = foldMap (\(name, val) -> pretty name <> indented val) xs

instance Pretty (TopEnv n) where
  pretty (TopEnv defs rules cache _ _) =
    prettyRecord [ ("Defs"          , pretty defs)
                 , ("Rules"         , pretty rules)
                 , ("Cache"         , pretty cache) ]

instance Pretty (CustomRules n) where
  pretty _ = "TODO: Rule printing"

instance Pretty (ImportStatus n) where
  pretty imports = pretty $ S.toList $ directImports imports

instance Pretty (ModuleEnv n) where
  pretty (ModuleEnv imports sm sc) =
    prettyRecord [ ("Imports"         , pretty imports)
                 , ("Source map"      , pretty sm)
                 , ("Synth candidates", pretty sc) ]

instance Pretty (Env n) where
  pretty (Env env1 env2) =
    prettyRecord [ ("Top env"   , pretty env1)
                 , ("Module env", pretty env2)]

instance Pretty (SolverBinding n) where
  pretty (InfVarBound  ty) = "Inference variable of type:"   <+> pretty ty
  pretty (SkolemBound  ty) = "Skolem variable of type:"      <+> pretty ty
  pretty (DictBound    ty) = "Dictionary variable of type:"  <+> pretty ty

instance Pretty (Binding c n) where
  pretty b = case b of
    -- using `unsafeCoerceIRE` here because otherwise we don't have `IRRep`
    -- TODO: can we avoid printing needing IRRep? Presumably it's related to
    -- manipulating sets or something, which relies on Eq/Ord, which relies on renaming.
    AtomNameBinding   info -> "Atom name:" <+> pretty (unsafeCoerceIRE @CoreIR info)
    TyConBinding dataDef _ -> "Type constructor: " <+> pretty dataDef
    DataConBinding tyConName idx -> "Data constructor:" <+>
      pretty tyConName <+> "Constructor index:" <+> pretty idx
    ClassBinding    classDef -> pretty classDef
    InstanceBinding instanceDef _ -> pretty instanceDef
    MethodBinding className idx -> "Method" <+> pretty idx <+> "of" <+> pretty className
    TopFunBinding f -> pretty f
    FunObjCodeBinding _ -> "<object file>"
    ModuleBinding  _ -> "<module>"
    PtrBinding   _ _ -> "<ptr>"
    SpecializedDictBinding _ -> "<specialized-dict-binding>"
    ImpNameBinding ty -> "Imp name of type: " <+> pretty ty

instance Pretty (Module n) where
  pretty m = prettyRecord
    [ ("moduleSourceName"     , pretty $ moduleSourceName m)
    , ("moduleDirectDeps"     , pretty $ S.toList $ moduleDirectDeps m)
    , ("moduleTransDeps"      , pretty $ S.toList $ moduleTransDeps m)
    , ("moduleExports"        , pretty $ moduleExports m)
    , ("moduleSynthCandidates", pretty $ moduleSynthCandidates m) ]

instance Pretty a => Pretty (EvalStatus a) where
  pretty = \case
    Waiting    -> "<waiting>"
    Running    -> "<running>"
    Finished a -> pretty a

instance Pretty (EnvFrag n l) where
  pretty (EnvFrag bindings) = pretty bindings

instance Pretty (Cache n) where
  pretty (Cache _ _ _ _ _ _) = "<cache>" -- TODO

instance Pretty (SynthCandidates n) where
  pretty scs = "instance dicts:" <+> pretty (M.toList $ instanceDicts scs)

instance Pretty (LoadedModules n) where
  pretty _ = "<loaded modules>"

instance Pretty (TopFunDef n) where
  pretty = \case
    Specialization       s -> pretty s
    LinearizationPrimal  _ -> "<linearization primal>"
    LinearizationTangent _ -> "<linearization tangent>"

instance Pretty (TopFun n) where
  pretty = \case
    DexTopFun def lam lowering ->
      "Top-level Function"
         <> hardline <+> "definition:" <+> pretty def
         <> hardline <+> "lambda:" <+> pretty lam
         <> hardline <+> "lowering:" <+> pretty lowering
    FFITopFun f _ -> pretty f

instance IRRep r => Pretty (TopLam r n) where
  pretty (TopLam _ _ lam) = pretty lam

instance IRRep r => Pretty (AtomBinding r n) where
  pretty binding = case binding of
    LetBound    b -> pretty b
    MiscBound   t -> pretty t
    SolverBound b -> pretty b
    FFIFunBound s _ -> pretty s
    NoinlineFun ty _ -> "Top function with type: " <+> pretty ty
    TopDataBound (RepVal ty _) -> "Top data with type: " <+> pretty ty

instance Pretty (SpecializationSpec n) where
  pretty (AppSpecialization f (Abs bs (ListE args))) =
    "Specialization" <+> pretty f <+> pretty bs <+> pretty args

instance Hashable a => Hashable (EvalStatus a)

instance Store (SolverBinding n)
instance IRRep r => Store (AtomBinding r n)
instance IRRep r => Store (TopLam r n)
instance Store (SynthCandidates n)
instance Store (Module n)
instance Store (ImportStatus n)
instance Store (TopFunLowerings n)
instance Store a => Store (EvalStatus a)
instance Store (TopFun n)
instance Store (TopFunDef n)
instance Color c => Store (Binding c n)
instance Store (ModuleEnv n)
instance Store (SerializedEnv n)
instance Store (AtomRules n)
instance Store (LinearizationSpec n)
instance Store (SpecializedDictDef n)
instance Store (SpecializationSpec n)
