-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ConstraintKinds #-}

-- Core data types for CoreIR and its variations.

module Types.Core (module Types.Core, SymbolicZeros (..)) where

import Data.Word
import Data.Maybe (fromJust)
import Data.Functor
import Data.Hashable
import Data.Text.Prettyprint.Doc  hiding (nest)
import qualified Data.Map.Strict       as M
import qualified Data.Set              as S

import GHC.Generics (Generic (..))
import Data.Store (Store (..))
import Foreign.Ptr

import Name
import Err
import Util (FileHash, SnocList (..), Tree (..))
import IRVariants

import qualified Types.OpNames as P
import Types.Primitives
import Types.Source
import Types.Imp

-- === core IR ===

data Atom (r::IR) (n::S) where
 Var        :: AtomName r n    -> Atom r n
 Con        :: Con r n         -> Atom r n
 PtrVar     :: PtrName n       -> Atom r n
 ProjectElt :: Projection -> Atom r n                   -> Atom r n
 DepPair    :: Atom r n -> Atom r n -> DepPairType r n  -> Atom r n
 -- === CoreIR only ===
 Lam          :: CoreLamExpr n                 -> Atom CoreIR n
 Eff          :: EffectRow CoreIR n            -> Atom CoreIR n
 DictCon      :: DictExpr n                    -> Atom CoreIR n
 NewtypeCon   :: NewtypeCon n -> Atom CoreIR n -> Atom CoreIR n
 DictHole     :: AlwaysEqual SrcPosCtx -> Type CoreIR n -> RequiredMethodAccess
              -> Atom CoreIR n
 TypeAsAtom   :: Type CoreIR n                 -> Atom CoreIR n
 -- === Shims between IRs ===
 SimpInCore   :: SimpInCore n    -> Atom CoreIR n
 RepValAtom   :: RepVal SimpIR n -> Atom SimpIR n

data Type (r::IR) (n::S) where
 TC           :: TC  r n         -> Type r n
 TabPi        :: TabPiType r n   -> Type r n
 DepPairTy    :: DepPairType r n -> Type r n
 TyVar        :: AtomName CoreIR n -> Type CoreIR n
 DictTy       :: DictType n      -> Type CoreIR n
 Pi           :: CorePiType  n   -> Type CoreIR n
 NewtypeTyCon :: NewtypeTyCon n  -> Type CoreIR n
 -- It was bad enough having this in `Atom`, but it's even worse now that it's
 -- replicated in `Type` too. We should be able to remove both once
 -- we represent types as normalized blocks.
 ProjectEltTy :: Projection -> CAtom n -> Type CoreIR n

type TabLamExpr = Abs (IxBinder SimpIR) (Abs (Nest SDecl) CAtom)
data SimpInCore (n::S) =
   LiftSimp (CType n) (SAtom n)
 | LiftSimpFun (CorePiType n) (LamExpr SimpIR n)
 | TabLam (TabPiType CoreIR n) (TabLamExpr n)
 | ACase (SAtom n) [Abs SBinder CAtom n] (CType n)
 deriving (Show, Generic)

deriving instance IRRep r => Show (Atom r n)
deriving instance IRRep r => Show (Type r n)
deriving via WrapE (Atom r) n instance IRRep r => Generic (Atom r n)
deriving via WrapE (Type r) n instance IRRep r => Generic (Type r n)

data Expr r n where
 TopApp :: TopFunName n -> [SAtom n]         -> Expr SimpIR n
 TabApp :: Atom r n -> [Atom r n]            -> Expr r n
 Case   :: Atom r n -> [Alt r n] -> Type r n -> EffectRow r n -> Expr r n
 Atom   :: Atom r n                          -> Expr r n
 TabCon :: Maybe (WhenCore r Dict n) -> Type r n -> [Atom r n] -> Expr r n
 PrimOp :: PrimOp r n                           -> Expr r n
 App             :: CAtom n -> [CAtom n]        -> Expr CoreIR n
 ApplyMethod     :: CAtom n -> Int -> [CAtom n] -> Expr CoreIR n

deriving instance IRRep r => Show (Expr r n)
deriving via WrapE (Expr r) n instance IRRep r => Generic (Expr r n)

data BaseMonoid r n =
  BaseMonoid { baseEmpty   :: Atom r n
             , baseCombine :: LamExpr r n }
  deriving (Show, Generic)

type EffAbs = Abs (Binder CoreIR) (EffectRow CoreIR)

data DeclBinding r n = DeclBinding LetAnn (Type r n) (Expr r n)
     deriving (Show, Generic)
data Decl (r::IR) (n::S) (l::S) = Let (AtomNameBinder r n l) (DeclBinding r n)
     deriving (Show, Generic)
type Decls r = Nest (Decl r)

-- TODO: make this a newtype with an unsafe constructor The idea is that the `r`
-- parameter will play a role a bit like the `c` parameter in names: if you have
-- an `AtomName r n` and you look up its definition in the `Env`, you're sure to
-- get an `AtomBinding r n`.
type AtomName       (r::IR) = Name (AtomNameC r)
type AtomNameBinder (r::IR) = NameBinder (AtomNameC r)

type ClassName    = Name ClassNameC
type TyConName    = Name TyConNameC
type DataConName  = Name DataConNameC
type EffectName   = Name EffectNameC
type EffectOpName = Name EffectOpNameC
type HandlerName  = Name HandlerNameC
type InstanceName = Name InstanceNameC
type MethodName   = Name MethodNameC
type ModuleName   = Name ModuleNameC
type PtrName      = Name PtrNameC
type SpecDictName = Name SpecializedDictNameC
type TopFunName   = Name TopFunNameC
type FunObjCodeName = Name FunObjCodeNameC

type AtomBinderP (r::IR) = BinderP (AtomNameC r)
type Binder r = AtomBinderP r (Type r) :: B
type Alt r = Abs (Binder r) (Block r) :: E

newtype DotMethods n = DotMethods (M.Map SourceName (CAtomName n))
        deriving (Show, Generic, Monoid, Semigroup)

data TyConDef n where
  -- The `SourceName` is just for pretty-printing. The actual alpha-renamable
  -- binder name is in UExpr and Env
  TyConDef
    :: SourceName
    -> RolePiBinders n l
    ->   DataConDefs l
    -> TyConDef n

data DataConDefs n =
   ADTCons [DataConDef n]
 | StructFields [(SourceName, CType n)]
   deriving (Show, Generic)

data DataConDef n =
  -- Name for pretty printing, constructor elements, representation type,
  -- list of projection indices that recovers elements from the representation.
  DataConDef SourceName (EmptyAbs (Nest CBinder) n) (CType n) [[Projection]]
  deriving (Show, Generic)

data ParamRole = TypeParam | DictParam | DataParam deriving (Show, Generic, Eq)

-- We track the explicitness information because we need it for the equality
-- check since we skip equality checking on dicts.
data TyConParams n = TyConParams [Explicitness] [Atom CoreIR n]
     deriving (Show, Generic)

-- The Type is the type of the result expression (and thus the type of the
-- block). It's given by querying the result expression's type, and checking
-- that it doesn't have any free names bound by the decls in the block. We store
-- it separately as an optimization, to avoid having to traverse the block.
-- If the decls are empty we can skip the type annotation, because then we can
-- cheaply query the result, and, more importantly, there's no risk of having a
-- type that mentions local variables.
data Block (r::IR) (n::S) where
  Block :: BlockAnn r n l -> Nest (Decl r) n l -> Atom r l -> Block r n

data BlockAnn r n l where
  BlockAnn :: Type r n -> EffectRow r n -> BlockAnn r n l
  NoBlockAnn :: BlockAnn r n n

data LamExpr (r::IR) (n::S) where
  LamExpr :: Nest (Binder r) n l -> Block r l -> LamExpr r n

data CoreLamExpr (n::S) = CoreLamExpr (CorePiType n) (LamExpr CoreIR n)

-- TODO(dougalm): let's get rid of this and just use a `LamExpr` with an extra argument.
data DestBlock (r::IR) (n::S) where
  -- The binder is for the destination that holds the result of the Block.
  -- The Block itself should not return anything -- it communicates results
  -- entirely through the destination.
  DestBlock :: forall r n l. Binder r n l -> Block r l -> DestBlock r n

data DestLamExpr (r::IR) (n::S) where
  DestLamExpr :: Nest (Binder r) n l -> DestBlock r l -> DestLamExpr r n

data IxDict r n where
  IxDictAtom        :: Atom CoreIR n         -> IxDict CoreIR n
  -- TODO: make these two only available in SimpIR (currently we can't do that
  -- because we need CoreIR to be a superset of SimpIR)
  -- IxDictRawFin is used post-simplification. It behaves like `Fin`, but
  -- it's parameterized by a newtyped-stripped `IxRepVal` instead of `Nat`, and
  -- it describes indices of type `IxRepVal`.
  IxDictRawFin      :: Atom r n                                 -> IxDict r n
  IxDictSpecialized :: SType n -> SpecDictName n -> [SAtom n] -> IxDict SimpIR n

deriving instance IRRep r => Show (IxDict r n)
deriving via WrapE (IxDict r) n instance IRRep r => Generic (IxDict r n)

data IxMethod = Size | Ordinal | UnsafeFromOrdinal
     deriving (Show, Generic, Enum, Bounded, Eq)

data IxType (r::IR) (n::S) =
  IxType { ixTypeType :: Type r n
         , ixTypeDict :: IxDict r n }
  deriving (Show, Generic)

type IxBinder r = BinderP (AtomNameC r) (IxType r)

data TabPiType (r::IR) (n::S) where
  TabPiType :: IxBinder r n l -> Type r l -> TabPiType r n

data PiType (r::IR) (n::S) where
  PiType :: Nest (Binder r) n l -> EffectRow r l -> Type r l -> PiType r n

type CoreBinders = Nest (WithExpl CBinder)

data CorePiType (n::S) where
  CorePiType :: AppExplicitness -> CoreBinders n l -> EffectRow CoreIR l -> Type CoreIR l -> CorePiType n

data DepPairType (r::IR) (n::S) where
  DepPairType :: DepPairExplicitness -> Binder r n l -> Type r l -> DepPairType r n

type Val  = Atom
type Kind = Type
type Dict = Atom CoreIR

-- A nest where the annotation of a binder cannot depend on the binders
-- introduced before it. You can think of it as introducing a bunch of
-- names into the scope in parallel, but since safer names only reasons
-- about sequential scope extensions, we encode it differently.
data NonDepNest r ann n l = NonDepNest (Nest (AtomNameBinder r) n l) [ann n]
                            deriving (Generic)

-- === GenericOp class ===

class IsPrimOp (e::IR->E) where
  toPrimOp :: e r n -> PrimOp r n

instance IsPrimOp PrimOp where
  toPrimOp x = x

class GenericOp (e::IR->E) where
  type OpConst e (r::IR) :: *
  fromOp :: e r n -> GenericOpRep (OpConst e r) r n
  toOp   :: GenericOpRep (OpConst e r) r n -> Maybe (e r n)

data GenericOpRep (const :: *) (r::IR) (n::S) =
  GenericOpRep const [Type r n] [Atom r n] [LamExpr r n]
  deriving (Show, Generic)

instance GenericE (GenericOpRep const r) where
  type RepE (GenericOpRep const r) = LiftE const `PairE` ListE (Type r) `PairE` ListE (Atom r) `PairE` ListE (LamExpr r)
  fromE (GenericOpRep c ts xs lams) = LiftE c `PairE` ListE ts `PairE` ListE xs `PairE` ListE lams
  {-# INLINE fromE #-}
  toE   (LiftE c `PairE` ListE ts `PairE` ListE xs `PairE` ListE lams) = GenericOpRep c ts xs lams
  {-# INLINE toE #-}

instance IRRep r => SinkableE (GenericOpRep const r) where
instance IRRep r => HoistableE (GenericOpRep const r) where
instance (Eq const, IRRep r) => AlphaEqE (GenericOpRep const r)
instance (Hashable const, IRRep r) => AlphaHashableE (GenericOpRep const r)
instance IRRep r => RenameE (GenericOpRep const r) where
  renameE env (GenericOpRep c ts xs ys) =
    GenericOpRep c (map (renameE env) ts) (map (renameE env) xs) (map (renameE env) ys)

fromEGenericOpRep :: GenericOp e => e r n -> GenericOpRep (OpConst e r) r n
fromEGenericOpRep = fromOp

toEGenericOpRep :: GenericOp e => GenericOpRep (OpConst e r) r n -> e r n
toEGenericOpRep = fromJust . toOp

traverseOp
  :: (GenericOp e, Monad m, OpConst e r ~ OpConst e r')
  => e r i
  -> (Type r i -> m (Type r' o))
  -> (Atom r i -> m (Atom r' o))
  -> (LamExpr r i -> m (LamExpr r' o))
  -> m (e r' o)
traverseOp op fType fAtom fLam = do
  let GenericOpRep c tys atoms lams = fromOp op
  tys'   <- mapM fType tys
  atoms' <- mapM fAtom atoms
  lams'  <- mapM fLam  lams
  return $ fromJust $ toOp $ GenericOpRep c tys' atoms' lams'

-- === Various ops ===

data TC (r::IR) (n::S) where
  BaseType :: BaseType             -> TC r n
  ProdType :: [Type r n]           -> TC r n
  SumType  :: [Type r n]           -> TC r n
  RefType  :: Atom r n -> Type r n -> TC r n
  TypeKind ::                         TC r n   -- TODO: `HasCore r` constraint
  HeapType ::                         TC r n
  deriving (Show, Generic)

data Con (r::IR) (n::S) where
  Lit     :: LitVal                        -> Con r n
  ProdCon :: [Atom r n]                    -> Con r n
  SumCon  :: [Type r n] -> Int -> Atom r n -> Con r n -- type, tag, payload
  HeapVal ::                                  Con r n
  deriving (Show, Generic)

data PrimOp (r::IR) (n::S) where
 UnOp     :: P.UnOp  -> Atom r n             -> PrimOp r n
 BinOp    :: P.BinOp -> Atom r n -> Atom r n -> PrimOp r n
 MemOp    :: MemOp r n                       -> PrimOp r n
 VectorOp :: VectorOp r n                    -> PrimOp r n
 MiscOp   :: MiscOp r n                      -> PrimOp r n
 Hof      :: Hof r n                         -> PrimOp r n
 RefOp    :: Atom r n -> RefOp r n           -> PrimOp r n
 DAMOp        :: DAMOp SimpIR n              -> PrimOp SimpIR n
 UserEffectOp :: UserEffectOp n              -> PrimOp CoreIR n

deriving instance IRRep r => Show (PrimOp r n)
deriving via WrapE (PrimOp r) n instance IRRep r => Generic (PrimOp r n)

data MemOp (r::IR) (n::S) =
   IOAlloc (Atom r n)
 | IOFree (Atom r n)
 | PtrOffset (Atom r n) (Atom r n)
 | PtrLoad (Atom r n)
 | PtrStore (Atom r n) (Atom r n)
   deriving (Show, Generic)

data MiscOp (r::IR) (n::S) =
   Select (Atom r n) (Atom r n) (Atom r n)        -- (3) predicate, val-if-true, val-if-false
 | CastOp (Type r n) (Atom r n)                   -- (2) Type, then value. See CheckType.hs for valid coercions.
 | BitcastOp (Type r n) (Atom r n)                -- (2) Type, then value. See CheckType.hs for valid coercions.
 | UnsafeCoerce (Type r n) (Atom r n)             -- type, then value. Assumes runtime representation is the same.
 | GarbageVal (Type r n)                 -- type of value (assume `Data` constraint)
 -- Effects
 | ThrowError (Type r n)                 -- (1) Hard error (parameterized by result type)
 | ThrowException (Type r n)             -- (1) Catchable exceptions (unlike `ThrowError`)
 -- Tag of a sum type
 | SumTag (Atom r n)
 -- Create an enum (payload-free ADT) from a Word8
 | ToEnum (Type r n) (Atom r n)
 -- printing
 | OutputStream
 | ShowAny (Atom r n)    -- implemented in Simplify
 | ShowScalar (Atom r n) -- Implemented in Imp. Result is a pair of an `IdxRepValTy`
                -- giving the logical size of the result and a fixed-size table,
                -- `Fin showStringBufferSize => Char`, assumed to have sufficient space.
   deriving (Show, Generic)

showStringBufferSize :: Word32
showStringBufferSize = 32

data VectorOp r n =
   VectorBroadcast (Atom r n) (Type r n)         -- value, vector type
 | VectorIota (Type r n)                         -- vector type
 | VectorSubref (Atom r n) (Atom r n) (Type r n) -- ref, base ix, vector type
   deriving (Show, Generic)

data Hof r n where
 For       :: ForAnn -> IxDict r n -> LamExpr r n -> Hof r n
 While     :: Block r n -> Hof r n
 RunReader :: Atom r n -> LamExpr r n -> Hof r n
 RunWriter :: Maybe (Atom r n) -> BaseMonoid r n -> LamExpr r n -> Hof r n
 RunState  :: Maybe (Atom r n) -> Atom r n -> LamExpr r n -> Hof r n  -- dest, initial value, body lambda
 RunIO     :: Block r n -> Hof r n
 RunInit   :: Block r n -> Hof r n
 CatchException :: Block   CoreIR n -> Hof CoreIR n
 Linearize      :: LamExpr CoreIR n -> Atom CoreIR n -> Hof CoreIR n
 Transpose      :: LamExpr CoreIR n -> Atom CoreIR n -> Hof CoreIR n

deriving instance IRRep r => Show (Hof r n)
deriving via WrapE (Hof r) n instance IRRep r => Generic (Hof r n)

-- Ops for "Dex Abstract Machine"
data DAMOp r n =
   Seq Direction (IxDict r n) (Atom r n) (LamExpr r n)   -- ix dict, carry dests, body lambda
 | RememberDest (Atom r n) (LamExpr r n)
 | AllocDest (Type r n)        -- type
 | Place (Atom r n) (Atom r n) -- reference, value
 | Freeze (Atom r n)           -- reference
   deriving (Show, Generic)

data RefOp r n =
   MAsk
 | MExtend (BaseMonoid r n) (Atom r n)
 | MGet
 | MPut (Atom r n)
 | IndexRef (Atom r n)
 | ProjRef Projection
  deriving (Show, Generic)

data UserEffectOp n =
   Handle (HandlerName n) [CAtom n] (CBlock n)
 | Resume (CType n) (CAtom n) -- Resume from effect handler (type, arg)
 | Perform (CAtom n) Int      -- Call an effect operation (effect name) (op #)
   deriving (Show, Generic)

-- === IR variants ===

type CAtom  = Atom CoreIR
type CType  = Type CoreIR
type CBinder = Binder CoreIR
type CExpr  = Expr CoreIR
type CBlock = Block CoreIR
type CDecl  = Decl  CoreIR
type CDecls = Decls CoreIR
type CAtomName  = AtomName CoreIR

type SAtom  = Atom SimpIR
type SType  = Type SimpIR
type SExpr  = Expr SimpIR
type SBlock = Block SimpIR
type SDecl  = Decl  SimpIR
type SDecls = Decls SimpIR
type SAtomName  = AtomName SimpIR
type SBinder = Binder SimpIR
type SRepVal = RepVal SimpIR
type SLam    = LamExpr SimpIR

-- === newtypes ===

-- Describes how to lift the "shallow" representation type to the newtype.
data NewtypeCon (n::S) =
   UserADTData (TyConName n) (TyConParams n)
 | NatCon
 | FinCon (Atom CoreIR n)
   deriving (Show, Generic)

data NewtypeTyCon (n::S) =
   Nat
 | Fin (Atom CoreIR n)
 | EffectRowKind
 | UserADTType SourceName (TyConName n) (TyConParams n)
   deriving (Show, Generic)

pattern TypeCon :: SourceName -> TyConName n -> TyConParams n -> CType n
pattern TypeCon s d xs = NewtypeTyCon (UserADTType s d xs)

isSumCon :: NewtypeCon n -> Bool
isSumCon = \case
 UserADTData _ _ -> True
 _ -> False

-- === type classes ===

data RolePiBinder (n::S) (l::S) = RolePiBinder ParamRole (WithExpl CBinder n l)
     deriving (Show, Generic)
type RolePiBinders = Nest RolePiBinder

data ClassDef (n::S) where
  ClassDef
    :: SourceName            -- name of class
    -> [SourceName]          -- method source names
    -> [Maybe SourceName]    -- parameter source names
    -> RolePiBinders n1 n2   -- parameters
    ->   Nest CBinder n2 n3  -- superclasses
    ->   [CorePiType n3]     -- method types
    -> ClassDef n1

data InstanceDef (n::S) where
  InstanceDef
    :: ClassName n1
    -> RolePiBinders n1 n2   -- parameters (types and dictionaries)
    ->   [CAtom n2]          -- class parameters
    ->   InstanceBody n2
    -> InstanceDef n1

data InstanceBody (n::S) =
  InstanceBody
    [CAtom n]  -- superclasses dicts
    [CAtom n]  -- method definitions
  deriving (Show, Generic)

data DictType (n::S) = DictType SourceName (ClassName n) [CAtom n]
     deriving (Show, Generic)

data DictExpr (n::S) =
   InstantiatedGiven (CAtom n) [CAtom n]
 | SuperclassProj (CAtom n) Int  -- (could instantiate here too, but we don't need it for now)
   -- We use NonEmpty because givens without args can be represented using `Var`.
 | InstanceDict (InstanceName n) [CAtom n]
   -- Special case for `Ix (Fin n)`  (TODO: a more general mechanism for built-in classes and instances)
 | IxFin (CAtom n)
   -- Special case for `Data <something that is actually data>`
 | DataData (CType n)
   deriving (Show, Generic)

-- TODO: Use an IntMap
newtype CustomRules (n::S) =
  CustomRules { customRulesMap :: M.Map (AtomName CoreIR n) (AtomRules n) }
  deriving (Semigroup, Monoid, Store)
data AtomRules (n::S) =
  -- number of implicit args, number of explicit args, linearization function
  CustomLinearize Int Int SymbolicZeros (CAtom n)
  deriving (Generic)

-- === Runtime representations ===

data RepVal (r::IR) (n::S) = RepVal (Type r n) (Tree (IExpr n))
     deriving (Show, Generic)

-- === envs and modules ===

-- `ModuleEnv` contains data that only makes sense in the context of evaluating
-- a particular module. `TopEnv` contains everything that makes sense "between"
-- evaluating modules.
data Env n = Env
  { topEnv    :: {-# UNPACK #-} TopEnv n
  , moduleEnv :: {-# UNPACK #-} ModuleEnv n }
  deriving (Generic)

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
 | FinishDictSpecialization (SpecDictName n) [LamExpr SimpIR n]
 | LowerDictSpecialization  (SpecDictName n) [LamExpr SimpIR n]
 | UpdateTopFunEvalStatus   (TopFunName n) (TopFunEvalStatus n)
 | UpdateInstanceDef        (InstanceName n) (InstanceDef n)
 | UpdateTyConDef           (TyConName n) (TyConDef n)
 | UpdateFieldDef           (TyConName n) SourceName (CAtomName n)

-- TODO: we could add a lot more structure for querying by dict type, caching, etc.
-- TODO: make these `Name n` instead of `Atom n` so they're usable as cache keys.
data SynthCandidates n = SynthCandidates
  { lambdaDicts       :: [AtomName CoreIR n]
  , instanceDicts     :: M.Map (ClassName n) [InstanceName n] }
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

-- === bindings - static information we carry about a lexical scope ===

-- TODO: consider making this an open union via a typeable-like class
data Binding (c::C) (n::S) where
  AtomNameBinding   :: AtomBinding r n                -> Binding (AtomNameC r)   n
  TyConBinding      :: Maybe (TyConDef n) -> DotMethods n -> Binding TyConNameC      n
  DataConBinding    :: TyConName n -> Int             -> Binding DataConNameC    n
  ClassBinding      :: ClassDef n                     -> Binding ClassNameC      n
  InstanceBinding   :: InstanceDef n -> CorePiType n  -> Binding InstanceNameC   n
  MethodBinding     :: ClassName n   -> Int           -> Binding MethodNameC     n
  EffectBinding     :: EffectDef n                    -> Binding EffectNameC     n
  HandlerBinding    :: HandlerDef n                   -> Binding HandlerNameC    n
  EffectOpBinding   :: EffectOpDef n                  -> Binding EffectOpNameC   n
  TopFunBinding     :: TopFun n                       -> Binding TopFunNameC     n
  FunObjCodeBinding :: CFunction n                    -> Binding FunObjCodeNameC n
  ModuleBinding     :: Module n                       -> Binding ModuleNameC     n
  -- TODO: add a case for abstracted pointers, as used in `ClosedImpFunction`
  PtrBinding        :: PtrType -> PtrLitVal           -> Binding PtrNameC        n
  SpecializedDictBinding :: SpecializedDictDef n      -> Binding SpecializedDictNameC n
  ImpNameBinding    :: BaseType                       -> Binding ImpNameC n

data EffectOpDef (n::S) where
  EffectOpDef :: EffectName n  -- name of associated effect
              -> EffectOpIdx   -- index in effect definition
              -> EffectOpDef n
  deriving (Show, Generic)

instance GenericE EffectOpDef where
  type RepE EffectOpDef =
    EffectName `PairE` LiftE EffectOpIdx
  fromE (EffectOpDef name idx) = name `PairE` LiftE idx
  toE (name `PairE` LiftE idx) = EffectOpDef name idx

instance SinkableE   EffectOpDef
instance HoistableE  EffectOpDef
instance RenameE     EffectOpDef

data EffectOpIdx = ReturnOp | OpIdx Int
  deriving (Show, Eq, Generic)

data EffectDef (n::S) where
  EffectDef :: SourceName
            -> [(SourceName, EffectOpType n)]
            -> EffectDef n

instance GenericE EffectDef where
  type RepE EffectDef =
    LiftE SourceName `PairE` ListE (LiftE SourceName `PairE` EffectOpType)
  fromE (EffectDef name ops) =
    LiftE name `PairE` ListE (map (\(x, y) -> LiftE x `PairE` y) ops)
  toE (LiftE name `PairE` ListE ops) =
    EffectDef name (map (\(LiftE x `PairE` y)->(x,y)) ops)

instance SinkableE EffectDef
instance HoistableE  EffectDef
instance AlphaEqE EffectDef
instance AlphaHashableE EffectDef
instance RenameE     EffectDef
deriving instance Show (EffectDef n)
deriving via WrapE EffectDef n instance Generic (EffectDef n)

data HandlerDef (n::S) where
  HandlerDef :: EffectName n
             -> CBinder n r -- body type arg
             -> RolePiBinders r l
               -> EffectRow CoreIR l
               -> CType l          -- return type
               -> [Block CoreIR l] -- effect operations
               -> Block CoreIR l   -- return body
             -> HandlerDef n

instance GenericE HandlerDef where
  type RepE HandlerDef =
    EffectName `PairE` Abs (CBinder `PairB` RolePiBinders)
      (EffectRow CoreIR `PairE` CType `PairE` ListE (Block CoreIR) `PairE` Block CoreIR)
  fromE (HandlerDef name bodyTyArg bs effs ty ops ret) =
    name `PairE` Abs (bodyTyArg `PairB` bs) (effs `PairE` ty `PairE` ListE ops `PairE` ret)
  toE (name `PairE` Abs (bodyTyArg `PairB` bs) (effs `PairE` ty `PairE` ListE ops `PairE` ret)) =
    HandlerDef name bodyTyArg bs effs ty ops ret

instance SinkableE HandlerDef
instance HoistableE  HandlerDef
instance AlphaEqE HandlerDef
instance AlphaHashableE HandlerDef
instance RenameE     HandlerDef
deriving instance Show (HandlerDef n)
deriving via WrapE HandlerDef n instance Generic (HandlerDef n)

data EffectOpType (n::S) where
  EffectOpType :: UResumePolicy -> CType n -> EffectOpType n

instance GenericE EffectOpType where
  type RepE EffectOpType =
    LiftE UResumePolicy `PairE` CType
  fromE (EffectOpType pol ty) = LiftE pol `PairE` ty
  toE (LiftE pol `PairE` ty) = EffectOpType pol ty

instance SinkableE EffectOpType
instance HoistableE  EffectOpType
instance AlphaEqE EffectOpType
instance AlphaHashableE EffectOpType
instance RenameE     EffectOpType
deriving instance Show (EffectOpType n)
deriving via WrapE EffectOpType n instance Generic (EffectOpType n)

instance GenericE SpecializedDictDef where
  type RepE SpecializedDictDef = AbsDict `PairE` MaybeE (ListE (LamExpr SimpIR))
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

data EvalStatus a = Waiting | Running | Finished a
     deriving (Show, Eq, Ord, Generic, Functor, Foldable, Traversable)
type TopFunEvalStatus n = EvalStatus (TopFunLowerings n)

data TopFun (n::S) =
   DexTopFun (TopFunDef n) (PiType SimpIR n) (LamExpr SimpIR n) (TopFunEvalStatus n)
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
 TopDataBound :: RepVal SimpIR n   -> AtomBinding SimpIR n
 SolverBound  :: SolverBinding n   -> AtomBinding CoreIR n
 NoinlineFun  :: CType n -> CAtom n -> AtomBinding CoreIR n
 FFIFunBound  :: CorePiType n -> TopFunName n -> AtomBinding CoreIR n

deriving instance IRRep r => Show (AtomBinding r n)
deriving via WrapE (AtomBinding r) n instance IRRep r => Generic (AtomBinding r n)

atomBindingType :: AtomBinding r n -> Type r n
atomBindingType b = case b of
  LetBound    (DeclBinding _ ty _) -> ty
  MiscBound   ty                   -> ty
  SolverBound (InfVarBound ty _)   -> ty
  SolverBound (SkolemBound ty)     -> ty
  NoinlineFun ty _                 -> ty
  TopDataBound (RepVal ty _) -> ty
  FFIFunBound piTy _ -> Pi piTy

-- name of function, name of arg
type InferenceArgDesc = (String, String)
data InfVarDesc =
   ImplicitArgInfVar InferenceArgDesc
 | AnnotationInfVar String -- name of binder
 | TypeInstantiationInfVar String -- name of type
 | MiscInfVar
   deriving (Show, Generic, Eq, Ord)

data SolverBinding (n::S) =
   InfVarBound (CType n) InfVarCtx
 | SkolemBound (CType n)
   deriving (Show, Generic)

-- Context for why we created an inference variable.
-- This helps us give better "ambiguous variable" errors.
type InfVarCtx = (SrcPosCtx, InfVarDesc)

newtype EnvFrag (n::S) (l::S) = EnvFrag (RecSubstFrag Binding n l)
        deriving (OutFrag)

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

-- === effects ===

data Effect (r::IR) (n::S) =
   RWSEffect RWS (Atom r n)
 | ExceptionEffect
 | IOEffect
 | UserEffect (Name EffectNameC n)
 | InitEffect  -- Internal effect modeling writing to a destination.
 deriving (Generic, Show)

data EffectRow (r::IR) (n::S) =
  EffectRow (ESet (Effect r) n) (EffectRowTail r n)
  deriving (Generic)

data EffectRowTail (r::IR) (n::S) where
  EffectRowTail :: AtomName CoreIR n -> EffectRowTail CoreIR n
  NoTail        ::                      EffectRowTail r n
deriving instance IRRep r => Show (EffectRowTail r n)
deriving instance IRRep r => Eq   (EffectRowTail r n)
deriving via WrapE (EffectRowTail r) n instance IRRep r => Generic (EffectRowTail r n)

data EffectAndType (r::IR) (n::S) = EffectAndType (EffectRow r n) (Type r n)
     deriving (Generic, Show)

deriving instance IRRep r => Show (EffectRow r n)

pattern Pure :: IRRep r => EffectRow r n
pattern Pure <- ((\(EffectRow effs t) -> (eSetToList effs, t)) -> ([], NoTail))
  where Pure = EffectRow mempty NoTail

pattern OneEffect :: IRRep r => Effect r n -> EffectRow r n
pattern OneEffect eff <- ((\(EffectRow effs t) -> (eSetToList effs, t)) -> ([eff], NoTail))
  where OneEffect eff = EffectRow (eSetSingleton eff) NoTail

instance IRRep r => Semigroup (EffectRow r n) where
  EffectRow effs t <> EffectRow effs' t' =
    EffectRow (effs <> effs') newTail
    where
      newTail = case (t, t') of
        (NoTail, effTail) -> effTail
        (effTail, NoTail) -> effTail
        _ | t == t' -> t
          | otherwise -> error "Can't combine effect rows with mismatched tails"

instance IRRep r => Monoid (EffectRow r n) where
  mempty = EffectRow mempty NoTail

extendEffRow :: IRRep r => ESet (Effect r) n -> EffectRow r n -> EffectRow r n
extendEffRow effs (EffectRow effs' t) = EffectRow (effs <> effs') t
{-# INLINE extendEffRow #-}

instance IRRep r => Store (EffectRowTail r n)
instance IRRep r => Store (EffectRow     r n)
instance IRRep r => Store (Effect        r n)

-- === Specialization and generalization ===

type Generalized (r::IR) (e::E) (n::S) = (Abstracted r e n, [Atom r n])
type Abstracted (r::IR) (e::E) = Abs (Nest (Binder r)) e
type AbsDict = Abstracted CoreIR Dict

data SpecializedDictDef n =
   SpecializedDict
     (AbsDict n)
     -- Methods (thunked if nullary), if they're available.
     -- We create specialized dict names during simplification, but we don't
     -- actually simplify/lower them until we return to TopLevel
     (Maybe [LamExpr SimpIR n])
   deriving (Show, Generic)

-- TODO: extend with AD-oriented specializations, backend-specific specializations etc.
data SpecializationSpec (n::S) =
   AppSpecialization (AtomName CoreIR n) (Abstracted CoreIR (ListE CAtom) n)
   deriving (Show, Generic)

type Active = Bool
data LinearizationSpec (n::S) =
  LinearizationSpec (TopFunName n) [Active]
  deriving (Show, Generic)

-- === BindsOneAtomName ===

class BindsOneName b (AtomNameC r) => BindsOneAtomName (r::IR) (b::B) | b -> r where
  binderType :: b n l -> Type r n
  -- binderAtomName :: b n l -> AtomName r l

bindersTypes :: (IRRep r, Distinct l, ProvesExt b, BindsNames b, BindsOneAtomName r b)
             => Nest b n l -> [Type r l]
bindersTypes Empty = []
bindersTypes n@(Nest b bs) = ty : bindersTypes bs
  where ty = withExtEvidence n $ sink (binderType b)

instance IRRep r => BindsOneAtomName r (BinderP (AtomNameC r) (Type r)) where
  binderType (_ :> ty) = ty

instance IRRep r => BindsOneAtomName r (IxBinder r) where
  binderType (_ :> IxType ty _) = ty

instance BindsOneAtomName CoreIR b => BindsOneAtomName CoreIR (WithExpl b) where
  binderType (WithExpl _ b) = binderType b

toBinderNest :: BindsOneAtomName r b => Nest b n l -> Nest (Binder r) n l
toBinderNest Empty = Empty
toBinderNest (Nest b bs) = Nest (asNameBinder b :> binderType b) (toBinderNest bs)

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

-- === HasArgType ===

class HasArgType (e::E) (r::IR) | e -> r where
  argType :: e n -> Type r n

instance HasArgType (TabPiType r) r where
  argType (TabPiType (_:>IxType ty _) _) = ty

-- === Pattern synonyms ===

-- XXX: only use this pattern when you're actually expecting a type. If it's
-- a Var, it doesn't check whether it's a type.
pattern Type :: CType n -> CAtom n
pattern Type t <- ((\case Var v          -> Just (TyVar v)
                          ProjectElt i x -> Just $ ProjectEltTy i x
                          TypeAsAtom t   -> Just t
                          _            -> Nothing) -> Just t)
  where Type (TyVar v) = Var v
        Type (ProjectEltTy i x) = ProjectElt i x
        Type t         = TypeAsAtom t

pattern IdxRepScalarBaseTy :: ScalarBaseType
pattern IdxRepScalarBaseTy = Word32Type

-- Type used to represent indices and sizes at run-time
pattern IdxRepTy :: Type r n
pattern IdxRepTy = TC (BaseType (Scalar Word32Type))

pattern IdxRepVal :: Word32 -> Atom r n
pattern IdxRepVal x = Con (Lit (Word32Lit x))

pattern IIdxRepVal :: Word32 -> IExpr n
pattern IIdxRepVal x = ILit (Word32Lit x)

pattern IIdxRepTy :: IType
pattern IIdxRepTy = Scalar Word32Type

-- Type used to represent sum type tags at run-time
pattern TagRepTy :: Type r n
pattern TagRepTy = TC (BaseType (Scalar Word8Type))

pattern TagRepVal :: Word8 -> Atom r n
pattern TagRepVal x = Con (Lit (Word8Lit x))

pattern CharRepTy :: Type r n
pattern CharRepTy = Word8Ty

charRepVal :: Char -> Atom r n
charRepVal c = Con (Lit (Word8Lit (fromIntegral $ fromEnum c)))

pattern Word8Ty :: Type r n
pattern Word8Ty = TC (BaseType (Scalar Word8Type))

pattern ProdTy :: [Type r n] -> Type r n
pattern ProdTy tys = TC (ProdType tys)

pattern ProdVal :: [Atom r n] -> Atom r n
pattern ProdVal xs = Con (ProdCon xs)

pattern SumTy :: [Type r n] -> Type r n
pattern SumTy cs = TC (SumType cs)

pattern SumVal :: [Type r n] -> Int -> Atom r n -> Atom r n
pattern SumVal tys tag payload = Con (SumCon tys tag payload)

pattern PairVal :: Atom r n -> Atom r n -> Atom r n
pattern PairVal x y = Con (ProdCon [x, y])

pattern PairTy :: Type r n -> Type r n -> Type r n
pattern PairTy x y = TC (ProdType [x, y])

pattern UnitVal :: Atom r n
pattern UnitVal = Con (ProdCon [])

pattern UnitTy :: Type r n
pattern UnitTy = TC (ProdType [])

pattern BaseTy :: BaseType -> Type r n
pattern BaseTy b = TC (BaseType b)

pattern PtrTy :: PtrType -> Type r n
pattern PtrTy ty = BaseTy (PtrType ty)

pattern RefTy :: Atom r n -> Type r n -> Type r n
pattern RefTy r a = TC (RefType r a)

pattern RawRefTy :: Type r n -> Type r n
pattern RawRefTy a = TC (RefType (Con HeapVal) a)

pattern TabTy :: IxBinder r n l -> Type r l -> Type r n
pattern TabTy b body = TabPi (TabPiType b body)

pattern FinTy :: Atom CoreIR n -> Type CoreIR n
pattern FinTy n = NewtypeTyCon (Fin n)

pattern NatTy :: Type CoreIR n
pattern NatTy = NewtypeTyCon Nat

pattern NatVal :: Word32 -> Atom CoreIR n
pattern NatVal n = NewtypeCon NatCon (IdxRepVal n)

pattern TyKind :: Kind r n
pattern TyKind = TC TypeKind

pattern EffKind :: Kind CoreIR n
pattern EffKind = NewtypeTyCon EffectRowKind

pattern FinConst :: Word32 -> Type CoreIR n
pattern FinConst n = NewtypeTyCon (Fin (NatVal n))

pattern NullaryLamExpr :: Block r n -> LamExpr r n
pattern NullaryLamExpr body = LamExpr Empty body

pattern UnaryLamExpr :: Binder r n l -> Block r l -> LamExpr r n
pattern UnaryLamExpr b body = LamExpr (UnaryNest b) body

pattern BinaryLamExpr :: Binder r n l1 -> Binder r l1 l2 -> Block r l2 -> LamExpr r n
pattern BinaryLamExpr b1 b2 body = LamExpr (BinaryNest b1 b2) body

pattern NullaryDestLamExpr :: DestBlock r n -> DestLamExpr r n
pattern NullaryDestLamExpr body = DestLamExpr Empty body

pattern AtomicBlock :: Atom r n -> Block r n
pattern AtomicBlock atom <- Block _ Empty atom
  where AtomicBlock atom = Block NoBlockAnn Empty atom

exprBlock :: IRRep r => Block r n -> Maybe (Expr r n)
exprBlock (Block _ (Nest (Let b (DeclBinding _ _ expr)) Empty) (Var n))
  | n == binderName b = Just expr
exprBlock _ = Nothing
{-# INLINE exprBlock #-}

pattern MaybeTy :: Type r n -> Type r n
pattern MaybeTy a = SumTy [UnitTy, a]

pattern NothingAtom :: Type r n -> Atom r n
pattern NothingAtom a = SumVal [UnitTy, a] 0 UnitVal

pattern JustAtom :: Type r n -> Atom r n -> Atom r n
pattern JustAtom a x = SumVal [UnitTy, a] 1 x

pattern BoolTy :: Type r n
pattern BoolTy = Word8Ty

pattern FalseAtom :: Atom r n
pattern FalseAtom = Con (Lit (Word8Lit 0))

pattern TrueAtom :: Atom r n
pattern TrueAtom = Con (Lit (Word8Lit 1))

-- === Typeclass instances for Name and other Haskell libraries ===

instance GenericE AtomRules where
  type RepE AtomRules = (LiftE (Int, Int, SymbolicZeros)) `PairE` CAtom
  fromE (CustomLinearize ni ne sz a) = LiftE (ni, ne, sz) `PairE` a
  toE (LiftE (ni, ne, sz) `PairE` a) = CustomLinearize ni ne sz a
instance SinkableE AtomRules
instance HoistableE AtomRules
instance AlphaEqE AtomRules
instance RenameE     AtomRules

instance IRRep r => GenericE (RepVal r) where
  type RepE (RepVal r) = PairE (Type r) (ComposeE Tree IExpr)
  fromE (RepVal ty tree) = ty `PairE` ComposeE tree
  toE   (ty `PairE` ComposeE tree) = RepVal ty tree

instance IRRep r => SinkableE      (RepVal r)
instance IRRep r => RenameE        (RepVal r)
instance IRRep r => HoistableE     (RepVal r)
instance IRRep r => AlphaHashableE (RepVal r)
instance IRRep r => AlphaEqE       (RepVal r)

instance GenericE CustomRules where
  type RepE CustomRules = ListE (PairE (AtomName CoreIR) AtomRules)
  fromE (CustomRules m) = ListE $ toPairE <$> M.toList m
  toE (ListE l) = CustomRules $ M.fromList $ fromPairE <$> l
instance SinkableE CustomRules
instance HoistableE CustomRules
instance AlphaEqE CustomRules
instance RenameE     CustomRules

instance GenericE TyConParams where
  type RepE TyConParams = PairE (LiftE [Explicitness]) (ListE CAtom)
  fromE (TyConParams infs xs) = PairE (LiftE infs) (ListE xs)
  {-# INLINE fromE #-}
  toE (PairE (LiftE infs) (ListE xs)) = TyConParams infs xs
  {-# INLINE toE #-}

-- We ignore the dictionary parameters because we assume coherence
instance AlphaEqE TyConParams where
  alphaEqE params params' =
    alphaEqE (ListE $ ignoreSynthParams params) (ListE $ ignoreSynthParams params')

instance AlphaHashableE TyConParams where
  hashWithSaltE env salt params =
    hashWithSaltE env salt $ ListE $ ignoreSynthParams params

ignoreSynthParams :: TyConParams n -> [CAtom n]
ignoreSynthParams (TyConParams infs xs) = [x | (inf, x) <- zip infs xs, notSynth inf]
  where notSynth = \case
          Inferred _ (Synth _) -> False
          _ -> True

instance SinkableE           TyConParams
instance HoistableE          TyConParams
instance RenameE             TyConParams

instance GenericE DataConDefs where
  type RepE DataConDefs = EitherE (ListE DataConDef) (ListE (PairE (LiftE SourceName) CType))
  fromE = \case
    ADTCons cons -> LeftE $ ListE cons
    StructFields fields -> RightE $ ListE [PairE (LiftE name) ty | (name, ty) <- fields]
  {-# INLINE fromE #-}
  toE = \case
    LeftE (ListE cons) -> ADTCons cons
    RightE (ListE fields) -> StructFields [(name, ty) | PairE (LiftE name) ty <- fields]
  {-# INLINE toE #-}

instance SinkableE      DataConDefs
instance HoistableE     DataConDefs
instance RenameE        DataConDefs
instance AlphaEqE       DataConDefs
instance AlphaHashableE DataConDefs

instance GenericE TyConDef where
  type RepE TyConDef = PairE (LiftE SourceName) (Abs RolePiBinders DataConDefs)
  fromE (TyConDef sourceName bs cons) = PairE (LiftE sourceName) (Abs bs cons)
  {-# INLINE fromE #-}
  toE   (PairE (LiftE sourceName) (Abs bs cons)) = TyConDef sourceName bs cons
  {-# INLINE toE #-}

deriving instance Show (TyConDef n)
deriving via WrapE TyConDef n instance Generic (TyConDef n)
instance SinkableE TyConDef
instance HoistableE  TyConDef
instance RenameE     TyConDef
instance AlphaEqE TyConDef
instance AlphaHashableE TyConDef

instance HasNameHint (TyConDef n) where
  getNameHint (TyConDef v _ _) = getNameHint v

instance GenericE DataConDef where
  type RepE DataConDef = (LiftE (SourceName, [[Projection]]))
    `PairE` EmptyAbs (Nest CBinder) `PairE` Type CoreIR
  fromE (DataConDef name bs repTy idxs) = (LiftE (name, idxs)) `PairE` bs `PairE` repTy
  {-# INLINE fromE #-}
  toE   ((LiftE (name, idxs)) `PairE` bs `PairE` repTy) = DataConDef name bs repTy idxs
  {-# INLINE toE #-}
instance SinkableE      DataConDef
instance HoistableE     DataConDef
instance RenameE        DataConDef
instance AlphaEqE       DataConDef
instance AlphaHashableE DataConDef

instance HasNameHint (DataConDef n) where
  getNameHint (DataConDef v _ _ _) = getNameHint v

instance GenericE NewtypeCon where
  type RepE NewtypeCon = EitherE3
   {- UserADTData -}  (TyConName `PairE` TyConParams)
   {- NatCon -}       UnitE
   {- FinCon -}       CAtom
  fromE = \case
    UserADTData d p -> Case0 $ d `PairE` p
    NatCon          -> Case1 UnitE
    FinCon n        -> Case2 n
  {-# INLINE fromE #-}
  toE = \case
    Case0 (d `PairE` p) -> UserADTData d p
    Case1 UnitE         -> NatCon
    Case2 n             -> FinCon n
    _ -> error "impossible"
  {-# INLINE toE #-}

instance SinkableE      NewtypeCon
instance HoistableE     NewtypeCon
instance AlphaEqE       NewtypeCon
instance AlphaHashableE NewtypeCon
instance RenameE        NewtypeCon

instance GenericE NewtypeTyCon where
  type RepE NewtypeTyCon = EitherE4
    {- Nat -}              UnitE
    {- Fin -}              CAtom
    {- EffectRowKind -}    UnitE
    {- UserADTType -}      (LiftE SourceName `PairE` TyConName `PairE` TyConParams)
  fromE = \case
    Nat               -> Case0 UnitE
    Fin n             -> Case1 n
    EffectRowKind     -> Case2 UnitE
    UserADTType s d p -> Case3 (LiftE s `PairE` d `PairE` p)
  {-# INLINE fromE #-}

  toE = \case
    Case0 UnitE -> Nat
    Case1 n     -> Fin n
    Case2 UnitE -> EffectRowKind
    Case3 (LiftE s `PairE` d `PairE` p) -> UserADTType s d p
    _ -> error "impossible"
  {-# INLINE toE #-}

instance SinkableE      NewtypeTyCon
instance HoistableE     NewtypeTyCon
instance AlphaEqE       NewtypeTyCon
instance AlphaHashableE NewtypeTyCon
instance RenameE        NewtypeTyCon

instance IRRep r => GenericE (BaseMonoid r) where
  type RepE (BaseMonoid r) = PairE (Atom r) (LamExpr r)
  fromE (BaseMonoid x f) = PairE x f
  {-# INLINE fromE #-}
  toE   (PairE x f) = BaseMonoid x f
  {-# INLINE toE #-}

instance IRRep r => SinkableE      (BaseMonoid r)
instance IRRep r => HoistableE     (BaseMonoid r)
instance IRRep r => RenameE        (BaseMonoid r)
instance IRRep r => AlphaEqE       (BaseMonoid r)
instance IRRep r => AlphaHashableE (BaseMonoid r)

instance GenericE UserEffectOp where
  type RepE UserEffectOp = EitherE3
 {- Handle -}  (HandlerName `PairE` ListE CAtom `PairE` CBlock)
 {- Resume -}  (CType `PairE` CAtom)
 {- Perform -} (CAtom `PairE` LiftE Int)
  fromE = \case
    Handle name args body -> Case0 $ name `PairE` ListE args `PairE` body
    Resume x y            -> Case1 $ x `PairE` y
    Perform x i           -> Case2 $ x `PairE` LiftE i
  {-# INLINE fromE #-}
  toE = \case
    Case0 (name `PairE` ListE args `PairE` body) -> Handle name args body
    Case1 (x `PairE` y)                          -> Resume x y
    Case2 (x `PairE` LiftE i)                    -> Perform x i
    _ -> error "impossible"
  {-# INLINE toE #-}

instance SinkableE      UserEffectOp
instance HoistableE     UserEffectOp
instance RenameE        UserEffectOp
instance AlphaEqE       UserEffectOp
instance AlphaHashableE UserEffectOp

instance IRRep r => GenericE (DAMOp r) where
  type RepE (DAMOp r) = EitherE5
  {- Seq -}            (LiftE Direction `PairE` IxDict r `PairE` Atom r `PairE` LamExpr r)
  {- RememberDest -}   (Atom r `PairE` LamExpr r)
  {- AllocDest -}      (Type r)
  {- Place -}          (Atom r `PairE` Atom r)
  {- Freeze -}         (Atom r)
  fromE = \case
    Seq d x y z      -> Case0 $ LiftE d `PairE` x `PairE` y `PairE` z
    RememberDest x y -> Case1 (x `PairE` y)
    AllocDest x      -> Case2 x
    Place x y        -> Case3 (x `PairE` y)
    Freeze x         -> Case4 x
  {-# INLINE fromE #-}
  toE = \case
    Case0 (LiftE d `PairE` x `PairE` y `PairE` z) -> Seq d x y z
    Case1 (x `PairE` y)                           -> RememberDest x y
    Case2 x                                       -> AllocDest x
    Case3 (x `PairE` y)                           -> Place x y
    Case4 x                                       -> Freeze x
    _ -> error "impossible"
  {-# INLINE toE #-}

instance IRRep r => SinkableE      (DAMOp r)
instance IRRep r => HoistableE     (DAMOp r)
instance IRRep r => RenameE        (DAMOp r)
instance IRRep r => AlphaEqE       (DAMOp r)
instance IRRep r => AlphaHashableE (DAMOp r)

instance IsPrimOp Hof where toPrimOp = Hof
instance IRRep r => GenericE (Hof r) where
  type RepE (Hof r) = EitherE2
    (EitherE6
  {- For -}       (LiftE ForAnn `PairE` IxDict r `PairE` LamExpr r)
  {- While -}     (Block r)
  {- RunReader -} (Atom r `PairE` LamExpr r)
  {- RunWriter -} (MaybeE (Atom r) `PairE` BaseMonoid r `PairE` LamExpr r)
  {- RunState -}  (MaybeE (Atom r) `PairE` Atom r `PairE` LamExpr r)
  {- RunIO -}     (Block r)
    ) (EitherE4
  {- RunInit -}        (Block r)
  {- CatchException -} (WhenCore r (Block r))
  {- Linearize -}      (WhenCore r (LamExpr r `PairE` Atom r))
  {- Transpose -}      (WhenCore r (LamExpr r `PairE` Atom r)))

  fromE = \case
    For ann d body      -> Case0 (Case0 (LiftE ann `PairE` d `PairE` body))
    While body          -> Case0 (Case1 body)
    RunReader x body    -> Case0 (Case2 (x `PairE` body))
    RunWriter d bm body -> Case0 (Case3 (toMaybeE d `PairE` bm `PairE` body))
    RunState  d x body  -> Case0 (Case4 (toMaybeE d `PairE` x `PairE` body))
    RunIO body          -> Case0 (Case5 body)
    RunInit body        -> Case1 (Case0 body)
    CatchException body -> Case1 (Case1 (WhenIRE body))
    Linearize body x    -> Case1 (Case2 (WhenIRE (PairE body x)))
    Transpose body x    -> Case1 (Case3 (WhenIRE (PairE body x)))
  {-# INLINE fromE #-}
  toE = \case
    Case0 hof -> case hof of
      Case0 (LiftE ann `PairE` d `PairE` body) -> For ann d body
      Case1 body                        -> While body
      Case2 (x `PairE` body)            -> RunReader x body
      Case3 (d `PairE` bm `PairE` body) -> RunWriter (fromMaybeE d) bm body
      Case4 (d `PairE` x `PairE` body)  -> RunState  (fromMaybeE d) x body
      Case5 body                        -> RunIO     body
      _ -> error "impossible"
    Case1 hof -> case hof of
      Case0 body -> RunInit body
      Case1 (WhenIRE body) -> CatchException body
      Case2 (WhenIRE (PairE body x)) -> Linearize body x
      Case3 (WhenIRE (PairE body x)) -> Transpose body x
      _ -> error "impossible"
    _ -> error "impossible"
  {-# INLINE toE #-}

instance IRRep r => SinkableE (Hof r)
instance IRRep r => HoistableE  (Hof r)
instance IRRep r => RenameE     (Hof r)
instance IRRep r => AlphaEqE (Hof r)
instance IRRep r => AlphaHashableE (Hof r)

instance GenericOp RefOp where
  type OpConst RefOp r = P.RefOp
  fromOp = \case
    MAsk                       -> GenericOpRep P.MAsk        [] [] []
    MExtend (BaseMonoid z f) x -> GenericOpRep P.MExtend     [] [z, x] [f]
    MGet                       -> GenericOpRep P.MGet        [] []  []
    MPut x                     -> GenericOpRep P.MPut        [] [x] []
    IndexRef x                 -> GenericOpRep P.IndexRef    [] [x] []
    ProjRef p                  -> GenericOpRep (P.ProjRef p) [] []  []
  {-# INLINE fromOp #-}
  toOp = \case
    GenericOpRep P.MAsk        [] []     []  -> Just $ MAsk
    GenericOpRep P.MExtend     [] [z, x] [f] -> Just $ MExtend (BaseMonoid z f) x
    GenericOpRep P.MGet        [] []     []  -> Just $ MGet
    GenericOpRep P.MPut        [] [x]    []  -> Just $ MPut x
    GenericOpRep P.IndexRef    [] [x]    []  -> Just $ IndexRef x
    GenericOpRep (P.ProjRef p) [] []     []  -> Just $ ProjRef p
    _ -> Nothing
  {-# INLINE toOp #-}

instance IRRep r => GenericE (RefOp r) where
  type RepE (RefOp r) = GenericOpRep (OpConst RefOp r) r
  fromE = fromEGenericOpRep
  toE   = toEGenericOpRep

instance IRRep r => SinkableE      (RefOp r)
instance IRRep r => HoistableE     (RefOp r)
instance IRRep r => RenameE        (RefOp r)
instance IRRep r => AlphaEqE       (RefOp r)
instance IRRep r => AlphaHashableE (RefOp r)

instance GenericE SimpInCore where
  type RepE SimpInCore = EitherE4
   {- LiftSimp -} (CType `PairE` SAtom)
   {- LiftSimpFun -} (CorePiType `PairE` LamExpr SimpIR)
   {- TabLam -}   (TabPiType CoreIR `PairE` TabLamExpr)
   {- ACase -}    (SAtom `PairE` ListE (Abs SBinder CAtom) `PairE` CType)
  fromE = \case
    LiftSimp ty x             -> Case0 $ ty `PairE` x
    LiftSimpFun ty x          -> Case1 $ ty `PairE` x
    TabLam ty lam             -> Case2 $ ty `PairE` lam
    ACase scrut alts resultTy -> Case3 $ scrut `PairE` ListE alts `PairE` resultTy
  {-# INLINE fromE #-}

  toE = \case
    Case0 (ty `PairE` x)                    -> LiftSimp ty x
    Case1 (ty `PairE` x)                    -> LiftSimpFun ty x
    Case2 (ty `PairE` lam)                  -> TabLam ty lam
    Case3 (x `PairE` ListE alts `PairE` ty) -> ACase x alts ty
    _ -> error "impossible"
  {-# INLINE toE #-}

instance SinkableE      SimpInCore
instance HoistableE     SimpInCore
instance RenameE        SimpInCore
instance AlphaEqE       SimpInCore
instance AlphaHashableE SimpInCore

instance IRRep r => GenericE (Atom r) where
  -- As tempting as it might be to reorder cases here, the current permutation
  -- was chosen as to make GHC inliner confident enough to simplify through
  -- toE/fromE entirely. If you wish to modify the order, please consult the
  -- GHC Core dump to make sure you haven't regressed this optimization.
  type RepE (Atom r) = EitherE3
         (EitherE4
  {- Var -}        (AtomName r)
  {- ProjectElt -} (LiftE Projection `PairE` Atom r)
  {- Lam -}        (WhenCore r CoreLamExpr)
  {- DepPair -}    ( Atom r `PairE` Atom r `PairE` DepPairType r)
         ) (EitherE4
  {- DictCon  -}   (WhenCore r DictExpr)
  {- NewtypeCon -}     (WhenCore r (NewtypeCon `PairE` Atom r))
  {- DictHole -}       (WhenCore r (LiftE (AlwaysEqual SrcPosCtx) `PairE`
                                    (Type CoreIR) `PairE`
                                    (LiftE RequiredMethodAccess)))
  {- Con -}        (Con r)
         ) (EitherE5
  {- Eff -}        ( WhenCore r (EffectRow r))
  {- PtrVar -}     PtrName
  {- RepValAtom -} ( WhenSimp r (RepVal r))
  {- SimpInCore -} ( WhenCore r SimpInCore)
  {- TypeAsAtom -} ( WhenCore r (Type CoreIR))
           )

  fromE atom = case atom of
    Var v             -> Case0 (Case0 v)
    ProjectElt idxs x -> Case0 (Case1 (PairE (LiftE idxs) x))
    Lam lamExpr       -> Case0 (Case2 (WhenIRE lamExpr))
    DepPair l r ty    -> Case0 (Case3 $ l `PairE` r `PairE` ty)
    DictCon d           -> Case1 $ Case0 $ WhenIRE d
    NewtypeCon c x      -> Case1 $ Case1 $ WhenIRE (c `PairE` x)
    DictHole s t access -> Case1 $ Case2 $ WhenIRE (LiftE s `PairE` t `PairE` LiftE access)
    Con con             -> Case1 $ Case3 con
    Eff effs      -> Case2 $ Case0 $ WhenIRE effs
    PtrVar v      -> Case2 $ Case1 $ v
    RepValAtom rv -> Case2 $ Case2 $ WhenIRE $ rv
    SimpInCore x  -> Case2 $ Case3 $ WhenIRE x
    TypeAsAtom t  -> Case2 $ Case4 $ WhenIRE t
  {-# INLINE fromE #-}

  toE atom = case atom of
    Case0 val -> case val of
      Case0 v -> Var v
      Case1 (PairE (LiftE idxs) x) -> ProjectElt idxs x
      Case2 (WhenIRE (lamExpr)) -> Lam lamExpr
      Case3 (l `PairE` r `PairE` ty) -> DepPair l r ty
      _ -> error "impossible"
    Case1 val -> case val of
      Case0 (WhenIRE d) -> DictCon d
      Case1 (WhenIRE (c `PairE` x)) -> NewtypeCon c x
      Case2 (WhenIRE (LiftE s `PairE` t `PairE` LiftE access)) -> DictHole s t access
      Case3 con -> Con con
      _ -> error "impossible"
    Case2 val -> case val of
      Case0 (WhenIRE effs) -> Eff effs
      Case1 v -> PtrVar v
      Case2 (WhenIRE rv) -> RepValAtom rv
      Case3 (WhenIRE x)  -> SimpInCore x
      Case4 (WhenIRE t)  -> TypeAsAtom t
      _ -> error "impossible"
    _ -> error "impossible"
  {-# INLINE toE #-}

instance IRRep r => SinkableE      (Atom r)
instance IRRep r => HoistableE     (Atom r)
instance IRRep r => AlphaEqE       (Atom r)
instance IRRep r => AlphaHashableE (Atom r)
instance IRRep r => RenameE        (Atom r)

instance IRRep r => GenericE (Type r) where
  type RepE (Type r) = EitherE8
  {- TyVar -}        (WhenCore r CAtomName)
  {- Pi -}           (WhenCore r CorePiType)
  {- TabPi -}        (TabPiType r)
  {- DepPairTy -}    (DepPairType r)
  {- DictTy  -}      (WhenCore r DictType)
  {- NewtypeTyCon -} (WhenCore r NewtypeTyCon)
  {- TC -}           (TC  r)
  {- ProjectEltTy -} (WhenCore r (LiftE Projection `PairE` Atom r))

  fromE = \case
    TyVar v        -> Case0 $ WhenIRE v
    Pi t           -> Case1 $ WhenIRE t
    TabPi t        -> Case2 t
    DepPairTy t    -> Case3 t
    DictTy  d      -> Case4 $ WhenIRE d
    NewtypeTyCon t -> Case5 $ WhenIRE t
    TC  con        -> Case6 $ con
    ProjectEltTy idxs x -> Case7 (WhenIRE (PairE (LiftE idxs) x))
  {-# INLINE fromE #-}

  toE = \case
    Case0 (WhenIRE v) -> TyVar v
    Case1 (WhenIRE t) -> Pi t
    Case2 t           -> TabPi  t
    Case3 t           -> DepPairTy t
    Case4 (WhenIRE d) -> DictTy d
    Case5 (WhenIRE t) -> NewtypeTyCon t
    Case6 con         -> TC con
    Case7 (WhenIRE (PairE (LiftE idxs) x)) -> ProjectEltTy idxs x
  {-# INLINE toE #-}

instance IRRep r => SinkableE      (Type r)
instance IRRep r => HoistableE     (Type r)
instance IRRep r => AlphaEqE       (Type r)
instance IRRep r => AlphaHashableE (Type r)
instance IRRep r => RenameE        (Type r)

instance IRRep r => GenericE (Expr r) where
  type RepE (Expr r) = EitherE2
    ( EitherE5
 {- App -}    (WhenCore r (Atom r `PairE` ListE (Atom r)))
 {- TabApp -} (Atom r `PairE` ListE (Atom r))
 {- Case -}   (Atom r `PairE` ListE (Alt r) `PairE` Type r `PairE` EffectRow r)
 {- Atom -}   (Atom r)
 {- TopApp -} (WhenSimp r (TopFunName `PairE` ListE (Atom r)))
    )
    ( EitherE3
 {- TabCon -}          (MaybeE (WhenCore r Dict) `PairE` Type r `PairE` ListE (Atom r))
 {- PrimOp -}          (PrimOp r)
 {- ApplyMethod -}     (WhenCore r (Atom r `PairE` LiftE Int `PairE` ListE (Atom r))))

  fromE = \case
    App    f xs        -> Case0 $ Case0 (WhenIRE (f `PairE` ListE xs))
    TabApp f xs        -> Case0 $ Case1 (f `PairE` ListE xs)
    Case e alts ty eff -> Case0 $ Case2 (e `PairE` ListE alts `PairE` ty `PairE` eff)
    Atom x             -> Case0 $ Case3 (x)
    TopApp f xs        -> Case0 $ Case4 (WhenIRE (f `PairE` ListE xs))
    TabCon d ty xs     -> Case1 $ Case0 (toMaybeE d `PairE` ty `PairE` ListE xs)
    PrimOp op          -> Case1 $ Case1 op
    ApplyMethod d i xs -> Case1 $ Case2 (WhenIRE (d `PairE` LiftE i `PairE` ListE xs))
  {-# INLINE fromE #-}
  toE = \case
    Case0 case0 -> case case0 of
      Case0 (WhenIRE (f `PairE` ListE xs))                -> App    f xs
      Case1 (f `PairE` ListE xs)                          -> TabApp f xs
      Case2 (e `PairE` ListE alts `PairE` ty `PairE` eff) -> Case e alts ty eff
      Case3 (x)                                           -> Atom x
      Case4 (WhenIRE (f `PairE` ListE xs))                -> TopApp f xs
      _ -> error "impossible"
    Case1 case1 -> case case1 of
      Case0 (d `PairE` ty `PairE` ListE xs) -> TabCon (fromMaybeE d) ty xs
      Case1 op -> PrimOp op
      Case2 (WhenIRE (d `PairE` LiftE i `PairE` ListE xs)) -> ApplyMethod d i xs
      _ -> error "impossible"
    _ -> error "impossible"
  {-# INLINE toE #-}

instance IRRep r => SinkableE      (Expr r)
instance IRRep r => HoistableE     (Expr r)
instance IRRep r => AlphaEqE       (Expr r)
instance IRRep r => AlphaHashableE (Expr r)
instance IRRep r => RenameE        (Expr r)

instance IRRep r => GenericE (PrimOp r) where
  type RepE (PrimOp r) = EitherE2
   ( EitherE5
 {- UnOp -}  (LiftE P.UnOp `PairE` Atom r)
 {- BinOp -} (LiftE P.BinOp `PairE` Atom r `PairE` Atom r)
 {- MemOp -} (MemOp r)
 {- VectorOp -} (VectorOp r)
 {- MiscOp -}   (MiscOp r)
   ) (EitherE4
 {- Hof -}           (Hof r)
 {- RefOp -}         (Atom r `PairE` RefOp r)
 {- DAMOp -}         (WhenSimp r (DAMOp SimpIR))
 {- UserEffectOp -}  (WhenCore r UserEffectOp)
             )
  fromE = \case
    UnOp  op x   -> Case0 $ Case0 $ LiftE op `PairE` x
    BinOp op x y -> Case0 $ Case1 $ LiftE op `PairE` x `PairE` y
    MemOp op     -> Case0 $ Case2 op
    VectorOp op  -> Case0 $ Case3 op
    MiscOp op    -> Case0 $ Case4 op
    Hof op          -> Case1 $ Case0 op
    RefOp r op      -> Case1 $ Case1 $ r `PairE` op
    DAMOp op        -> Case1 $ Case2 $ WhenIRE op
    UserEffectOp op -> Case1 $ Case3 $ WhenIRE op
  {-# INLINE fromE #-}

  toE = \case
    Case0 rep -> case rep of
      Case0 (LiftE op `PairE` x          ) -> UnOp  op x
      Case1 (LiftE op `PairE` x `PairE` y) -> BinOp op x y
      Case2 op -> MemOp op
      Case3 op -> VectorOp op
      Case4 op -> MiscOp op
      _ -> error "impossible"
    Case1 rep -> case rep of
      Case0 op -> Hof op
      Case1 (r `PairE` op) -> RefOp r op
      Case2 (WhenIRE op)   -> DAMOp op
      Case3 (WhenIRE op)   -> UserEffectOp op
      _ -> error "impossible"
    _ -> error "impossible"
  {-# INLINE toE #-}

instance IRRep r => SinkableE      (PrimOp r)
instance IRRep r => HoistableE     (PrimOp r)
instance IRRep r => AlphaEqE       (PrimOp r)
instance IRRep r => AlphaHashableE (PrimOp r)
instance IRRep r => RenameE        (PrimOp r)

instance GenericOp VectorOp where
  type OpConst VectorOp r = P.VectorOp
  fromOp = \case
    VectorBroadcast x t -> GenericOpRep P.VectorBroadcast [t] [x]    []
    VectorIota t        -> GenericOpRep P.VectorIota      [t] []     []
    VectorSubref x y t  -> GenericOpRep P.VectorSubref    [t] [x, y] []
  {-# INLINE fromOp #-}

  toOp = \case
    GenericOpRep P.VectorBroadcast [t] [x]    [] -> Just $ VectorBroadcast x t
    GenericOpRep P.VectorIota      [t] []     [] -> Just $ VectorIota t
    GenericOpRep P.VectorSubref    [t] [x, y] [] -> Just $ VectorSubref x y t
    _ -> Nothing
  {-# INLINE toOp #-}

instance IsPrimOp VectorOp where toPrimOp = VectorOp
instance IRRep r => GenericE (VectorOp r) where
  type RepE (VectorOp r) = GenericOpRep (OpConst VectorOp r) r
  fromE = fromEGenericOpRep
  toE   = toEGenericOpRep
instance IRRep r => SinkableE      (VectorOp r)
instance IRRep r => HoistableE     (VectorOp r)
instance IRRep r => AlphaEqE       (VectorOp r)
instance IRRep r => AlphaHashableE (VectorOp r)
instance IRRep r => RenameE        (VectorOp r)

instance GenericOp MemOp where
  type OpConst MemOp r = P.MemOp
  fromOp = \case
    IOAlloc x     -> GenericOpRep P.IOAlloc   [] [x]    []
    IOFree x      -> GenericOpRep P.IOFree    [] [x]    []
    PtrOffset x y -> GenericOpRep P.PtrOffset [] [x, y] []
    PtrLoad x     -> GenericOpRep P.PtrLoad   [] [x]    []
    PtrStore x y  -> GenericOpRep P.PtrStore  [] [x, y] []
  {-# INLINE fromOp #-}
  toOp = \case
    GenericOpRep P.IOAlloc   [] [x]    [] -> Just $ IOAlloc x
    GenericOpRep P.IOFree    [] [x]    [] -> Just $ IOFree x
    GenericOpRep P.PtrOffset [] [x, y] [] -> Just $ PtrOffset x y
    GenericOpRep P.PtrLoad   [] [x]    [] -> Just $ PtrLoad x
    GenericOpRep P.PtrStore  [] [x, y] [] -> Just $ PtrStore x y
    _ -> Nothing
  {-# INLINE toOp #-}

instance IsPrimOp MemOp where toPrimOp = MemOp
instance IRRep r => GenericE (MemOp r) where
  type RepE (MemOp r) = GenericOpRep (OpConst MemOp r) r
  fromE = fromEGenericOpRep
  toE   = toEGenericOpRep
instance IRRep r => SinkableE      (MemOp r)
instance IRRep r => HoistableE     (MemOp r)
instance IRRep r => AlphaEqE       (MemOp r)
instance IRRep r => AlphaHashableE (MemOp r)
instance IRRep r => RenameE        (MemOp r)

instance GenericOp MiscOp where
  type OpConst MiscOp r = P.MiscOp
  fromOp = \case
    Select p x y     -> GenericOpRep P.Select         []  [p,x,y] []
    CastOp t x       -> GenericOpRep P.CastOp         [t] [x]     []
    BitcastOp t x    -> GenericOpRep P.BitcastOp      [t] [x]     []
    UnsafeCoerce t x -> GenericOpRep P.UnsafeCoerce   [t] [x]     []
    GarbageVal t     -> GenericOpRep P.GarbageVal     [t] []      []
    ThrowError t     -> GenericOpRep P.ThrowError     [t] []      []
    ThrowException t -> GenericOpRep P.ThrowException [t] []      []
    SumTag x         -> GenericOpRep P.SumTag         []  [x]     []
    ToEnum t x       -> GenericOpRep P.ToEnum         [t] [x]     []
    OutputStream     -> GenericOpRep P.OutputStream   []  []      []
    ShowAny x        -> GenericOpRep P.ShowAny        []  [x]     []
    ShowScalar x     -> GenericOpRep P.ShowScalar     []  [x]     []
  {-# INLINE fromOp #-}
  toOp = \case
    GenericOpRep P.Select         []  [p,x,y] [] -> Just $ Select p x y
    GenericOpRep P.CastOp         [t] [x]     [] -> Just $ CastOp t x
    GenericOpRep P.BitcastOp      [t] [x]     [] -> Just $ BitcastOp t x
    GenericOpRep P.UnsafeCoerce   [t] [x]     [] -> Just $ UnsafeCoerce t x
    GenericOpRep P.GarbageVal     [t] []      [] -> Just $ GarbageVal t
    GenericOpRep P.ThrowError     [t] []      [] -> Just $ ThrowError t
    GenericOpRep P.ThrowException [t] []      [] -> Just $ ThrowException t
    GenericOpRep P.SumTag         []  [x]     [] -> Just $ SumTag x
    GenericOpRep P.ToEnum         [t] [x]     [] -> Just $ ToEnum t x
    GenericOpRep P.OutputStream   []  []      [] -> Just $ OutputStream
    GenericOpRep P.ShowAny        []  [x]     [] -> Just $ ShowAny x
    GenericOpRep P.ShowScalar     []  [x]     [] -> Just $ ShowScalar x
    _ -> Nothing
  {-# INLINE toOp #-}

instance IsPrimOp MiscOp where toPrimOp = MiscOp
instance IRRep r => GenericE (MiscOp r) where
  type RepE (MiscOp r) = GenericOpRep (OpConst MiscOp r) r
  fromE = fromEGenericOpRep
  toE   = toEGenericOpRep
instance IRRep r => SinkableE      (MiscOp r)
instance IRRep r => HoistableE     (MiscOp r)
instance IRRep r => AlphaEqE       (MiscOp r)
instance IRRep r => AlphaHashableE (MiscOp r)
instance IRRep r => RenameE        (MiscOp r)

instance GenericOp Con where
  type OpConst Con r = Either LitVal P.Con
  fromOp = \case
    Lit     l       -> GenericOpRep (Left l)             []  []  []
    ProdCon xs      -> GenericOpRep (Right P.ProdCon)    []  xs  []
    SumCon  tys i x -> GenericOpRep (Right (P.SumCon i)) tys [x] []
    HeapVal         -> GenericOpRep (Right P.HeapVal)    []  []  []
  {-# INLINE fromOp #-}

  toOp = \case
    GenericOpRep (Left l)             []  []  [] -> Just $ Lit     l
    GenericOpRep (Right P.ProdCon)    []  xs  [] -> Just $ ProdCon xs
    GenericOpRep (Right (P.SumCon i)) tys [x] [] -> Just $ SumCon  tys i x
    GenericOpRep (Right P.HeapVal)    []  []  [] -> Just $ HeapVal
    _ -> Nothing
  {-# INLINE toOp #-}

instance IRRep r => GenericE (Con r) where
  type RepE (Con r) = GenericOpRep (OpConst Con r) r
  fromE = fromEGenericOpRep
  toE   = toEGenericOpRep

instance IRRep r => SinkableE      (Con r)
instance IRRep r => HoistableE     (Con r)
instance IRRep r => AlphaEqE       (Con r)
instance IRRep r => AlphaHashableE (Con r)
instance IRRep r => RenameE        (Con r)

instance GenericOp TC where
  type OpConst TC r = Either BaseType P.TC
  fromOp = \case
    BaseType b  -> GenericOpRep (Left b) [] [] []
    ProdType ts -> GenericOpRep (Right P.ProdType) ts [] []
    SumType  ts -> GenericOpRep (Right P.SumType)  ts [] []
    RefType  h t -> GenericOpRep (Right P.RefType) [t] [h] []
    TypeKind -> GenericOpRep (Right P.TypeKind) [] [] []
    HeapType -> GenericOpRep (Right P.HeapType) [] [] []
  {-# INLINE fromOp #-}

  toOp = \case
    GenericOpRep (Left b) [] [] []              -> Just (BaseType b)
    GenericOpRep (Right P.ProdType) ts [] []    -> Just (ProdType ts)
    GenericOpRep (Right P.SumType)  ts [] []    -> Just (SumType  ts)
    GenericOpRep (Right P.RefType)  [t] [h] []  -> Just (RefType h t)
    GenericOpRep (Right P.TypeKind) [] [] []    -> Just TypeKind
    GenericOpRep (Right P.HeapType) [] [] []    -> Just HeapType
    GenericOpRep _ _ _ _ -> Nothing
  {-# INLINE toOp #-}

instance IRRep r => GenericE (TC r) where
  type RepE (TC r) = GenericOpRep (OpConst TC r) r
  fromE = fromEGenericOpRep
  toE   = toEGenericOpRep
instance IRRep r => SinkableE      (TC r)
instance IRRep r => HoistableE     (TC r)
instance IRRep r => AlphaEqE       (TC r)
instance IRRep r => AlphaHashableE (TC r)
instance IRRep r => RenameE        (TC r)

instance IRRep r => GenericE (Block r) where
  type RepE (Block r) = PairE (MaybeE (PairE (Type r) (EffectRow r))) (Abs (Nest (Decl r)) (Atom r))
  fromE (Block (BlockAnn ty effs) decls result) = PairE (JustE (PairE ty effs)) (Abs decls result)
  fromE (Block NoBlockAnn Empty result) = PairE NothingE (Abs Empty result)
  fromE _ = error "impossible"
  {-# INLINE fromE #-}
  toE   (PairE (JustE (PairE ty effs)) (Abs decls result)) = Block (BlockAnn ty effs) decls result
  toE   (PairE NothingE (Abs Empty result)) = Block NoBlockAnn Empty result
  toE   _ = error "impossible"
  {-# INLINE toE #-}

deriving instance IRRep r => Show (BlockAnn r n l)

instance IRRep r => SinkableE      (Block r)
instance IRRep r => HoistableE     (Block r)
instance IRRep r => AlphaEqE       (Block r)
instance IRRep r => AlphaHashableE (Block r)
instance IRRep r => RenameE        (Block r)
deriving instance IRRep r => Show (Block r n)
deriving via WrapE (Block r) n instance IRRep r => Generic (Block r n)

instance IRRep r => GenericB (NonDepNest r ann) where
  type RepB (NonDepNest r ann) = (LiftB (ListE ann)) `PairB` Nest (AtomNameBinder r)
  fromB (NonDepNest bs anns) = LiftB (ListE anns) `PairB` bs
  {-# INLINE fromB #-}
  toB (LiftB (ListE anns) `PairB` bs) = NonDepNest bs anns
  {-# INLINE toB #-}
instance IRRep r => ProvesExt (NonDepNest r ann)
instance IRRep r => BindsNames (NonDepNest r ann)
instance (IRRep r, SinkableE  ann) => SinkableB  (NonDepNest r ann)
instance (IRRep r, HoistableE ann) => HoistableB (NonDepNest r ann)
instance (IRRep r, RenameE ann, SinkableE ann) => RenameB (NonDepNest r ann)
instance (IRRep r, AlphaEqE       ann) => AlphaEqB       (NonDepNest r ann)
instance (IRRep r, AlphaHashableE ann) => AlphaHashableB (NonDepNest r ann)
deriving instance (Show (ann n)) => IRRep r => Show (NonDepNest r ann n l)

instance GenericB RolePiBinder where
  type RepB RolePiBinder = PairB (LiftB (LiftE ParamRole)) (WithExpl CBinder)
  fromB (RolePiBinder role b) = PairB (LiftB (LiftE role)) b
  toB   (PairB (LiftB (LiftE role)) b) = RolePiBinder role b

instance BindsAtMostOneName RolePiBinder (AtomNameC CoreIR) where
  RolePiBinder _ b @> x = b @> x
  {-# INLINE (@>) #-}

instance BindsOneName RolePiBinder (AtomNameC CoreIR) where
  binderName (RolePiBinder _ b) = binderName b

instance BindsOneAtomName CoreIR RolePiBinder where
  binderType (RolePiBinder _ b) = binderType b

instance ProvesExt   RolePiBinder
instance BindsNames  RolePiBinder
instance SinkableB   RolePiBinder
instance HoistableB  RolePiBinder
instance RenameB     RolePiBinder
instance AlphaEqB RolePiBinder
instance AlphaHashableB RolePiBinder

instance GenericE ClassDef where
  type RepE ClassDef =
    LiftE (SourceName, [SourceName], [Maybe SourceName])
     `PairE` Abs RolePiBinders (Abs (Nest CBinder) (ListE CorePiType))
  fromE (ClassDef name names paramNames b scs tys) =
    LiftE (name, names, paramNames) `PairE` Abs b (Abs scs (ListE tys))
  {-# INLINE fromE #-}
  toE (LiftE (name, names, paramNames) `PairE` Abs b (Abs scs (ListE tys))) =
    ClassDef name names paramNames b scs tys
  {-# INLINE toE #-}

instance SinkableE ClassDef
instance HoistableE  ClassDef
instance AlphaEqE ClassDef
instance AlphaHashableE ClassDef
instance RenameE     ClassDef
deriving instance Show (ClassDef n)
deriving via WrapE ClassDef n instance Generic (ClassDef n)

instance GenericE InstanceDef where
  type RepE InstanceDef =
    ClassName `PairE` Abs RolePiBinders (ListE CAtom `PairE` InstanceBody)
  fromE (InstanceDef name bs params body) =
    name `PairE` Abs bs (ListE params `PairE` body)
  toE (name `PairE` Abs bs (ListE params `PairE` body)) =
    InstanceDef name bs params body

instance SinkableE InstanceDef
instance HoistableE  InstanceDef
instance AlphaEqE InstanceDef
instance AlphaHashableE InstanceDef
instance RenameE     InstanceDef
deriving instance Show (InstanceDef n)
deriving via WrapE InstanceDef n instance Generic (InstanceDef n)

instance GenericE InstanceBody where
  type RepE InstanceBody = ListE CAtom `PairE` ListE CAtom
  fromE (InstanceBody scs methods) = ListE scs `PairE` ListE methods
  toE   (ListE scs `PairE` ListE methods) = InstanceBody scs methods

instance SinkableE InstanceBody
instance HoistableE  InstanceBody
instance AlphaEqE InstanceBody
instance AlphaHashableE InstanceBody
instance RenameE     InstanceBody

instance GenericE DictType where
  type RepE DictType = LiftE SourceName `PairE` ClassName `PairE` ListE CAtom
  fromE (DictType sourceName className params) =
    LiftE sourceName `PairE` className `PairE` ListE params
  toE (LiftE sourceName `PairE` className `PairE` ListE params) =
    DictType sourceName className params

instance SinkableE      DictType
instance HoistableE     DictType
instance AlphaEqE       DictType
instance AlphaHashableE DictType
instance RenameE        DictType

instance GenericE DictExpr where
  type RepE DictExpr =
    EitherE5
 {- InstanceDict -}      (PairE InstanceName (ListE CAtom))
 {- InstantiatedGiven -} (PairE CAtom (ListE CAtom))
 {- SuperclassProj -}    (PairE CAtom (LiftE Int))
 {- IxFin -}             CAtom
 {- DataData -}          CType
  fromE d = case d of
    InstanceDict v args -> Case0 $ PairE v (ListE args)
    InstantiatedGiven given args -> Case1 $ PairE given (ListE args)
    SuperclassProj x i -> Case2 (PairE x (LiftE i))
    IxFin x            -> Case3 x
    DataData ty        -> Case4 ty
  toE d = case d of
    Case0 (PairE v (ListE args)) -> InstanceDict v args
    Case1 (PairE given (ListE args)) -> InstantiatedGiven given args
    Case2 (PairE x (LiftE i)) -> SuperclassProj x i
    Case3 x  -> IxFin x
    Case4 ty -> DataData ty
    _ -> error "impossible"

instance SinkableE      DictExpr
instance HoistableE     DictExpr
instance AlphaEqE       DictExpr
instance AlphaHashableE DictExpr
instance RenameE        DictExpr

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

instance GenericE (LamExpr r) where
  type RepE (LamExpr r) = Abs (Nest (Binder r)) (Block r)
  fromE (LamExpr b block) = Abs b block
  {-# INLINE fromE #-}
  toE   (Abs b block) = LamExpr b block
  {-# INLINE toE #-}

instance IRRep r => SinkableE      (LamExpr r)
instance IRRep r => HoistableE     (LamExpr r)
instance IRRep r => AlphaEqE       (LamExpr r)
instance IRRep r => AlphaHashableE (LamExpr r)
instance IRRep r => RenameE        (LamExpr r)
deriving instance IRRep r => Show (LamExpr r n)
deriving via WrapE (LamExpr r) n instance IRRep r => Generic (LamExpr r n)

instance GenericE (DestBlock r) where
  type RepE (DestBlock r) = Abs (Binder r) (Block r)
  fromE (DestBlock b block) = Abs b block
  {-# INLINE fromE #-}
  toE   (Abs b block) = DestBlock b block
  {-# INLINE toE #-}

instance IRRep r => SinkableE      (DestBlock r)
instance IRRep r => HoistableE     (DestBlock r)
instance IRRep r => AlphaEqE       (DestBlock r)
instance IRRep r => AlphaHashableE (DestBlock r)
instance IRRep r => RenameE        (DestBlock r)
deriving instance IRRep r => Show (DestBlock r n)
deriving via WrapE (DestBlock r) n instance IRRep r => Generic (DestBlock r n)

instance GenericE (DestLamExpr r) where
  type RepE (DestLamExpr r) = Abs (Nest (Binder r)) (DestBlock r)
  fromE (DestLamExpr b block) = Abs b block
  {-# INLINE fromE #-}
  toE   (Abs b block) = DestLamExpr b block
  {-# INLINE toE #-}

instance IRRep r => SinkableE      (DestLamExpr r)
instance IRRep r => HoistableE     (DestLamExpr r)
instance IRRep r => AlphaEqE       (DestLamExpr r)
instance IRRep r => AlphaHashableE (DestLamExpr r)
instance IRRep r => RenameE        (DestLamExpr r)
deriving instance IRRep r => Show (DestLamExpr r n)
deriving via WrapE (DestLamExpr r) n instance IRRep r => Generic (DestLamExpr r n)

instance GenericE CoreLamExpr where
  type RepE CoreLamExpr = CorePiType `PairE` LamExpr CoreIR
  fromE (CoreLamExpr ty lam) = ty `PairE` lam
  {-# INLINE fromE #-}
  toE   (ty `PairE` lam) = CoreLamExpr ty lam
  {-# INLINE toE #-}

instance SinkableE      CoreLamExpr
instance HoistableE     CoreLamExpr
instance AlphaEqE       CoreLamExpr
instance AlphaHashableE CoreLamExpr
instance RenameE        CoreLamExpr
deriving instance Show (CoreLamExpr n)
deriving via WrapE CoreLamExpr n instance Generic (CoreLamExpr n)

instance GenericE CorePiType where
  type RepE CorePiType = LiftE AppExplicitness `PairE` Abs CoreBinders (EffectRow CoreIR `PairE` CType)
  fromE (CorePiType ex b eff resultTy) = LiftE ex `PairE` Abs b (eff `PairE` resultTy)
  {-# INLINE fromE #-}
  toE   (LiftE ex `PairE` Abs b (eff `PairE` resultTy)) = CorePiType ex b eff resultTy
  {-# INLINE toE #-}

instance SinkableE      CorePiType
instance HoistableE     CorePiType
instance AlphaEqE       CorePiType
instance AlphaHashableE CorePiType
instance RenameE        CorePiType
deriving instance Show (CorePiType n)
deriving via WrapE CorePiType n instance Generic (CorePiType n)

instance IRRep r => GenericE (IxDict r) where
  type RepE (IxDict r) =
    EitherE3
      (WhenCore r (Atom r))
      (Atom r)
      (WhenSimp r (Type r `PairE` SpecDictName `PairE` ListE (Atom r)))
  fromE = \case
    IxDictAtom x -> Case0 $ WhenIRE x
    IxDictRawFin n -> Case1 $ n
    IxDictSpecialized t d xs -> Case2 $ WhenIRE $ t `PairE` d `PairE` ListE xs
  {-# INLINE fromE #-}
  toE = \case
    Case0 (WhenIRE x)          -> IxDictAtom x
    Case1 (n)                  -> IxDictRawFin n
    Case2 (WhenIRE (t `PairE` d `PairE` ListE xs)) -> IxDictSpecialized t d xs
    _ -> error "impossible"
  {-# INLINE toE #-}

instance IRRep r => SinkableE   (IxDict r)
instance IRRep r => HoistableE  (IxDict r)
instance IRRep r => RenameE     (IxDict r)
instance IRRep r => AlphaEqE       (IxDict r)
instance IRRep r => AlphaHashableE (IxDict r)

instance IRRep r => GenericE (IxType r) where
  type RepE (IxType r) = PairE (Type r) (IxDict r)
  fromE (IxType ty d) = PairE ty d
  {-# INLINE fromE #-}
  toE   (PairE ty d) = IxType ty d
  {-# INLINE toE #-}

instance IRRep r => SinkableE   (IxType r)
instance IRRep r => HoistableE  (IxType r)
instance IRRep r => RenameE     (IxType r)

instance IRRep r => AlphaEqE (IxType r) where
  alphaEqE (IxType t1 _) (IxType t2 _) = alphaEqE t1 t2

instance IRRep r => AlphaHashableE (IxType r) where
  hashWithSaltE env salt (IxType t _) = hashWithSaltE env salt t

instance IRRep r => GenericE (TabPiType r) where
  type RepE (TabPiType r) = Abs (IxBinder r) (Type r)
  fromE (TabPiType b resultTy) = Abs b resultTy
  {-# INLINE fromE #-}
  toE   (Abs b resultTy) = TabPiType b resultTy
  {-# INLINE toE #-}

instance IRRep r => SinkableE      (TabPiType r)
instance IRRep r => HoistableE     (TabPiType r)
instance IRRep r => AlphaEqE       (TabPiType r)
instance IRRep r => AlphaHashableE (TabPiType r)
instance IRRep r => RenameE        (TabPiType r)
deriving instance IRRep r => Show (TabPiType r n)
deriving via WrapE (TabPiType r) n instance IRRep r => Generic (TabPiType r n)

instance GenericE (PiType r) where
  type RepE (PiType r) = Abs (Nest (Binder r)) (PairE (EffectRow r) (Type r))
  fromE (PiType bs eff resultTy) = Abs bs (PairE eff resultTy)
  {-# INLINE fromE #-}
  toE   (Abs bs (PairE eff resultTy)) = PiType bs eff resultTy
  {-# INLINE toE #-}

instance IRRep r => SinkableE      (PiType r)
instance IRRep r => HoistableE     (PiType r)
instance IRRep r => AlphaEqE       (PiType r)
instance IRRep r => AlphaHashableE (PiType r)
instance IRRep r => RenameE     (PiType r)
deriving instance IRRep r => Show (PiType r n)
deriving via WrapE (PiType r) n instance IRRep r => Generic (PiType r n)
instance IRRep r => Store (PiType r n)

instance GenericE (DepPairType r) where
  type RepE (DepPairType r) = PairE (LiftE DepPairExplicitness) (Abs (Binder r) (Type r))
  fromE (DepPairType expl b resultTy) = LiftE expl `PairE` Abs b resultTy
  {-# INLINE fromE #-}
  toE   (LiftE expl `PairE` Abs b resultTy) = DepPairType expl b resultTy
  {-# INLINE toE #-}

instance IRRep r => SinkableE      (DepPairType r)
instance IRRep r => HoistableE     (DepPairType r)
instance IRRep r => AlphaEqE       (DepPairType r)
instance IRRep r => AlphaHashableE (DepPairType r)
instance IRRep r => RenameE        (DepPairType r)
deriving instance IRRep r => Show (DepPairType r n)
deriving via WrapE (DepPairType r) n instance IRRep r => Generic (DepPairType r n)

instance GenericE SynthCandidates where
  type RepE SynthCandidates =
    ListE (AtomName CoreIR) `PairE` ListE (PairE ClassName (ListE InstanceName))
  fromE (SynthCandidates xs ys) = ListE xs `PairE` ListE ys'
    where ys' = map (\(k,vs) -> PairE k (ListE vs)) (M.toList ys)
  {-# INLINE fromE #-}
  toE (ListE xs `PairE` ListE ys) = SynthCandidates xs ys'
    where ys' = M.fromList $ map (\(PairE k (ListE vs)) -> (k,vs)) ys
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
      (WhenSimp r (RepVal SimpIR))                   -- TopDataBound
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

instance GenericE TopFun where
  type RepE TopFun = EitherE
        (TopFunDef `PairE` PiType SimpIR `PairE` LamExpr SimpIR `PairE` ComposeE EvalStatus TopFunLowerings)
        (LiftE (String, IFunType))
  fromE = \case
    DexTopFun def ty simp status -> LeftE (def `PairE` ty `PairE` simp `PairE` ComposeE status)
    FFITopFun name ty    -> RightE (LiftE (name, ty))
  {-# INLINE fromE #-}
  toE = \case
    LeftE  (def `PairE` ty `PairE` simp `PairE` ComposeE status) -> DexTopFun def ty simp status
    RightE (LiftE (name, ty))            -> FFITopFun name ty
  {-# INLINE toE #-}

instance SinkableE      TopFun
instance HoistableE     TopFun
instance RenameE        TopFun
instance AlphaEqE       TopFun
instance AlphaHashableE TopFun

instance GenericE SpecializationSpec where
  type RepE SpecializationSpec =
         PairE (AtomName CoreIR) (Abs (Nest (Binder CoreIR)) (ListE CAtom))
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
  type RepE SolverBinding = EitherE2
                                  (PairE CType (LiftE InfVarCtx))
                                  CType
  fromE = \case
    InfVarBound  ty ctx -> Case0 (PairE ty (LiftE ctx))
    SkolemBound  ty     -> Case1 ty
  {-# INLINE fromE #-}

  toE = \case
    Case0 (PairE ty (LiftE ct)) -> InfVarBound  ty ct
    Case1 ty                    -> SkolemBound  ty
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
      (EitherE7
          (WhenC TopFunNameC     c (TopFun))
          (WhenC FunObjCodeNameC c (CFunction))
          (WhenC ModuleNameC     c (Module))
          (WhenC PtrNameC        c (LiftE (PtrType, PtrLitVal)))
          (WhenC EffectNameC     c (EffectDef))
          (WhenC HandlerNameC    c (HandlerDef))
          (WhenC EffectOpNameC   c (EffectOpDef)))
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
    EffectBinding   effDef              -> Case1 $ Case4 $ WhenC $ effDef
    HandlerBinding  hDef                -> Case1 $ Case5 $ WhenC $ hDef
    EffectOpBinding opDef               -> Case1 $ Case6 $ WhenC $ opDef
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
    Case1 (Case4 (WhenC (effDef)))                 -> EffectBinding     effDef
    Case1 (Case5 (WhenC (hDef)))                   -> HandlerBinding    hDef
    Case1 (Case6 (WhenC (opDef)))                  -> EffectOpBinding   opDef
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

instance GenericE DotMethods where
  type RepE DotMethods = ListE (LiftE SourceName `PairE` CAtomName)
  fromE (DotMethods xys) = ListE $ [LiftE x `PairE` y | (x, y) <- M.toList xys]
  {-# INLINE fromE #-}
  toE (ListE xys) = DotMethods $ M.fromList [(x, y) | LiftE x `PairE` y <- xys]
  {-# INLINE toE #-}

instance SinkableE      DotMethods
instance HoistableE     DotMethods
instance RenameE        DotMethods
instance AlphaEqE       DotMethods
instance AlphaHashableE DotMethods

instance IRRep r => GenericE (DeclBinding r) where
  type RepE (DeclBinding r) = LiftE LetAnn `PairE` Type r `PairE` Expr r
  fromE (DeclBinding ann ty expr) = LiftE ann `PairE` ty `PairE` expr
  {-# INLINE fromE #-}
  toE   (LiftE ann `PairE` ty `PairE` expr) = DeclBinding ann ty expr
  {-# INLINE toE #-}

instance IRRep r => SinkableE      (DeclBinding r)
instance IRRep r => HoistableE     (DeclBinding r)
instance IRRep r => RenameE        (DeclBinding r)
instance IRRep r => AlphaEqE       (DeclBinding r)
instance IRRep r => AlphaHashableE (DeclBinding r)

instance GenericB (Decl r) where
  type RepB (Decl r) = AtomBinderP r (DeclBinding r)
  fromB (Let b binding) = b :> binding
  {-# INLINE fromB #-}
  toB   (b :> binding) = Let b binding
  {-# INLINE toB #-}

instance IRRep r => SinkableB      (Decl r)
instance IRRep r => HoistableB     (Decl r)
instance IRRep r => RenameB        (Decl r)
instance IRRep r => AlphaEqB       (Decl r)
instance IRRep r => AlphaHashableB (Decl r)
instance IRRep r => ProvesExt      (Decl r)
instance IRRep r => BindsNames     (Decl r)

instance IRRep r => GenericE (Effect r) where
  type RepE (Effect r) =
    EitherE4 (PairE (LiftE RWS) (Atom r))
             (LiftE (Either () ()))
             (Name EffectNameC)
             UnitE
  fromE = \case
    RWSEffect rws h    -> Case0 (PairE (LiftE rws) h)
    ExceptionEffect    -> Case1 (LiftE (Left  ()))
    IOEffect           -> Case1 (LiftE (Right ()))
    UserEffect name    -> Case2 name
    InitEffect         -> Case3 UnitE
  {-# INLINE fromE #-}
  toE = \case
    Case0 (PairE (LiftE rws) h) -> RWSEffect rws h
    Case1 (LiftE (Left  ())) -> ExceptionEffect
    Case1 (LiftE (Right ())) -> IOEffect
    Case2 name -> UserEffect name
    Case3 UnitE -> InitEffect
    _ -> error "unreachable"
  {-# INLINE toE #-}

instance IRRep r => SinkableE      (Effect r)
instance IRRep r => HoistableE     (Effect r)
instance IRRep r => AlphaEqE       (Effect r)
instance IRRep r => AlphaHashableE (Effect r)
instance IRRep r => RenameE        (Effect r)

instance IRRep r => GenericE (EffectRow r) where
  type RepE (EffectRow r) = PairE (ListE (Effect r)) (EffectRowTail r)
  fromE (EffectRow effs ext) = ListE (eSetToList effs) `PairE` ext
  {-# INLINE fromE #-}
  toE (ListE effs `PairE` ext) = EffectRow (eSetFromList effs) ext
  {-# INLINE toE #-}

instance IRRep r => SinkableE      (EffectRow r)
instance IRRep r => HoistableE     (EffectRow r)
instance IRRep r => RenameE        (EffectRow r)
instance IRRep r => AlphaEqE       (EffectRow r)
instance IRRep r => AlphaHashableE (EffectRow r)

instance IRRep r => GenericE (EffectRowTail r) where
  type RepE (EffectRowTail r) = EitherE (WhenCore r (AtomName CoreIR)) UnitE
  fromE = \case
    EffectRowTail v -> LeftE (WhenIRE v)
    NoTail          -> RightE UnitE
  {-# INLINE fromE #-}
  toE = \case
    LeftE (WhenIRE v) -> EffectRowTail v
    RightE UnitE    -> NoTail
  {-# INLINE toE #-}

instance IRRep r => SinkableE      (EffectRowTail r)
instance IRRep r => HoistableE     (EffectRowTail r)
instance IRRep r => RenameE        (EffectRowTail r)
instance IRRep r => AlphaEqE       (EffectRowTail r)
instance IRRep r => AlphaHashableE (EffectRowTail r)

instance IRRep r => GenericE (EffectAndType r) where
  type RepE (EffectAndType r) = PairE (EffectRow r) (Type r)
  fromE (EffectAndType eff ty) = eff `PairE` ty
  {-# INLINE fromE #-}
  toE   (eff `PairE` ty) = EffectAndType eff ty
  {-# INLINE toE #-}

instance IRRep r => SinkableE      (EffectAndType r)
instance IRRep r => HoistableE     (EffectAndType r)
instance IRRep r => RenameE        (EffectAndType r)
instance IRRep r => AlphaEqE       (EffectAndType r)
instance IRRep r => AlphaHashableE (EffectAndType r)

instance IRRep r => BindsAtMostOneName (Decl r) (AtomNameC r) where
  Let b _ @> x = b @> x
  {-# INLINE (@>) #-}

instance IRRep r => BindsOneName (Decl r) (AtomNameC r) where
  binderName (Let b _) = binderName b
  {-# INLINE binderName #-}

instance Semigroup (SynthCandidates n) where
  SynthCandidates xs ys <> SynthCandidates xs' ys' =
    SynthCandidates (xs<>xs') (M.unionWith (<>) ys ys')

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
    {- FinishDictSpecialization -} (SpecDictName `PairE` ListE (LamExpr SimpIR))
    {- LowerDictSpecialization -}  (SpecDictName `PairE` ListE (LamExpr SimpIR))
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
      TopFunBinding (DexTopFun def ty simp _) ->
        updateEnv f (TopFunBinding $ DexTopFun def ty simp s) e
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

instance Hashable InfVarDesc
instance Hashable IxMethod
instance Hashable ParamRole
instance Hashable a => Hashable (EvalStatus a)

instance IRRep r => Store (MiscOp r n)
instance IRRep r => Store (VectorOp r n)
instance IRRep r => Store (MemOp r n)
instance IRRep r => Store (TC r n)
instance IRRep r => Store (Con r n)
instance IRRep r => Store (PrimOp r n)
instance IRRep r => Store (RepVal r n)
instance IRRep r => Store (Type r n)
instance IRRep r => Store (Atom r n)
instance IRRep r => Store (Expr r n)
instance Store (SimpInCore n)
instance Store (SolverBinding n)
instance IRRep r => Store (AtomBinding r n)
instance Store (SpecializationSpec n)
instance Store (LinearizationSpec n)
instance IRRep r => Store (DeclBinding r n)
instance IRRep r => Store (Decl r n l)
instance Store (TyConParams n)
instance Store (DataConDefs n)
instance Store (TyConDef n)
instance Store (DataConDef n)
instance IRRep r => Store (Block r n)
instance IRRep r => Store (LamExpr r n)
instance IRRep r => Store (IxType r n)
instance Store (CorePiType n)
instance Store (CoreLamExpr n)
instance IRRep r => Store (TabPiType r n)
instance IRRep r => Store (DepPairType  r n)
instance Store (AtomRules n)
instance Store (ClassDef     n)
instance Store (InstanceDef  n)
instance Store (InstanceBody n)
instance Store (DictType n)
instance Store (DictExpr n)
instance Store (EffectDef n)
instance Store (EffectOpDef n)
instance Store (RolePiBinder n l)
instance Store (HandlerDef n)
instance Store (EffectOpType n)
instance Store (EffectOpIdx)
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
instance Store (ann n) => Store (NonDepNest r ann n l)
instance Store InfVarDesc
instance Store IxMethod
instance Store ParamRole
instance Store (SpecializedDictDef n)
instance IRRep r => Store (Hof r n)
instance IRRep r => Store (RefOp r n)
instance IRRep r => Store (BaseMonoid r n)
instance IRRep r => Store (DAMOp r n)
instance IRRep r => Store (IxDict r n)
instance Store (UserEffectOp n)
instance Store (NewtypeCon n)
instance Store (NewtypeTyCon n)
instance Store (DotMethods n)
