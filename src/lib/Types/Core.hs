-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StrictData #-}

-- Core data types for CoreIR and its variations.

module Types.Core (module Types.Core, SymbolicZeros (..)) where

import Data.Word
import Data.Maybe (fromJust)
import Data.Foldable (toList)
import Data.Hashable
import Data.String (fromString)
import Data.Text.Prettyprint.Doc
import Data.Text (Text, unsnoc, uncons)
import qualified Data.Map.Strict       as M

import GHC.Generics (Generic (..))
import Data.Store (Store (..))

import Name
import Util (Tree (..))
import IRVariants
import PPrint

import qualified Types.OpNames as P
import Types.Primitives
import Types.Source
import Types.Imp

-- === core IR ===

data Atom (r::IR) (n::S) where
  Con   :: Con r n  -> Atom r n
  Stuck :: Type r n -> Stuck r n -> Atom r n
  deriving (Show, Generic)

data Type (r::IR) (n::S) where
  TyCon   :: TyCon r n -> Type r n
  StuckTy :: CType n -> CStuck n  -> Type CoreIR n

data Dict (r::IR) (n::S) where
  DictCon :: DictCon r n -> Dict r n
  StuckDict :: CType n -> CStuck n -> Dict CoreIR n

data Con (r::IR) (n::S) where
  Lit     :: LitVal                                  -> Con r n
  ProdCon :: [Atom r n]                              -> Con r n
  SumCon  :: [Type r n] -> Int -> Atom r n           -> Con r n -- type, tag, payload
  HeapVal ::                                            Con r n
  DepPair :: Atom r n -> Atom r n -> DepPairType r n -> Con r n
  Lam        :: CoreLamExpr n                 -> Con CoreIR n
  Eff        :: EffectRow CoreIR n            -> Con CoreIR n
  NewtypeCon :: NewtypeCon n -> Atom CoreIR n -> Con CoreIR n
  DictConAtom :: DictCon CoreIR n             -> Con CoreIR n
  TyConAtom   :: TyCon CoreIR n               -> Con CoreIR n

data Stuck (r::IR) (n::S) where
  Var               :: AtomVar r n             -> Stuck r n
  StuckProject      :: Int -> Stuck r n        -> Stuck r n
  StuckTabApp       :: Stuck r n -> Atom r n   -> Stuck r n
  PtrVar            :: PtrType -> PtrName n    -> Stuck r n
  RepValAtom        :: RepVal n                -> Stuck SimpIR n
  StuckUnwrap       :: CStuck n                -> Stuck CoreIR n
  InstantiatedGiven :: CStuck n -> [CAtom n]   -> Stuck CoreIR n
  SuperclassProj    :: Int -> CStuck n         -> Stuck CoreIR n
  LiftSimp          :: CType n -> Stuck SimpIR n         -> Stuck CoreIR n
  LiftSimpFun       :: CorePiType n -> LamExpr SimpIR n  -> Stuck CoreIR n
  -- TabLam and ACase are just defunctionalization tools. The result type
  -- in both cases should *not* be `Data`.
  TabLam            :: TabLamExpr n                     -> Stuck CoreIR n
  ACase :: SStuck n -> [Abs SBinder CAtom n] -> CType n -> Stuck CoreIR n

data TyCon (r::IR) (n::S) where
  BaseType :: BaseType             -> TyCon r n
  ProdType :: [Type r n]           -> TyCon r n
  SumType  :: [Type r n]           -> TyCon r n
  RefType  :: Atom r n -> Type r n -> TyCon r n
  HeapType     ::                     TyCon r n
  TabPi        :: TabPiType r n    -> TyCon r n
  DepPairTy    :: DepPairType r n  -> TyCon r n
  TypeKind     ::                     TyCon CoreIR n
  DictTy       :: DictType n       -> TyCon CoreIR n
  Pi           :: CorePiType  n    -> TyCon CoreIR n
  NewtypeTyCon :: NewtypeTyCon n   -> TyCon CoreIR n

data AtomVar (r::IR) (n::S) = AtomVar
  { atomVarName :: AtomName r n
  , atomVarType :: Type r n }
     deriving (Show, Generic)

deriving instance IRRep r => Show (DictCon  r n)
deriving instance IRRep r => Show (Dict     r n)
deriving instance IRRep r => Show (Con      r n)
deriving instance IRRep r => Show (TyCon    r n)
deriving instance IRRep r => Show (Type     r n)
deriving instance IRRep r => Show (Stuck    r n)

deriving via WrapE (DictCon  r) n instance IRRep r => Generic (DictCon  r n)
deriving via WrapE (Dict     r) n instance IRRep r => Generic (Dict     r n)
deriving via WrapE (Con      r) n instance IRRep r => Generic (Con      r n)
deriving via WrapE (TyCon    r) n instance IRRep r => Generic (TyCon    r n)
deriving via WrapE (Type     r) n instance IRRep r => Generic (Type     r n)
deriving via WrapE (Stuck    r) n instance IRRep r => Generic (Stuck    r n)

-- TODO: factor out the EffTy and maybe merge with PrimOp
data Expr r n where
 Block  :: EffTy r n -> Block r n -> Expr r n
 TopApp :: EffTy SimpIR n -> TopFunName n -> [SAtom n]         -> Expr SimpIR n
 TabApp :: Type r n -> Atom r n -> Atom r n                    -> Expr r n
 Case   :: Atom r n -> [Alt r n] -> EffTy r n                  -> Expr r n
 Atom   :: Atom r n                                            -> Expr r n
 TabCon :: Maybe (WhenCore r (Dict CoreIR) n) -> Type r n -> [Atom r n] -> Expr r n
 PrimOp :: PrimOp r n                                          -> Expr r n
 Project     :: Type r n -> Int -> Atom r n                    -> Expr r n
 App         :: EffTy CoreIR n -> CAtom n -> [CAtom n]         -> Expr CoreIR n
 Unwrap      :: CType n -> CAtom n                             -> Expr CoreIR n
 ApplyMethod :: EffTy CoreIR n -> CAtom n -> Int -> [CAtom n]  -> Expr CoreIR n

deriving instance IRRep r => Show (Expr r n)
deriving via WrapE (Expr r) n instance IRRep r => Generic (Expr r n)

data BaseMonoid r n =
  BaseMonoid { baseEmpty   :: Atom r n
             , baseCombine :: LamExpr r n }
  deriving (Show, Generic)

data RepVal (n::S) = RepVal (SType n) (Tree (IExpr n))
     deriving (Show, Generic)

data DeclBinding r n = DeclBinding LetAnn (Expr r n)
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
type InstanceName = Name InstanceNameC
type MethodName   = Name MethodNameC
type ModuleName   = Name ModuleNameC
type PtrName      = Name PtrNameC
type SpecDictName = Name SpecializedDictNameC
type TopFunName   = Name TopFunNameC
type FunObjCodeName = Name FunObjCodeNameC

type AtomBinderP (r::IR) = BinderP (AtomNameC r)
type Binder r = AtomBinderP r (Type r) :: B
type Alt r = Abs (Binder r) (Expr r) :: E

newtype DotMethods n = DotMethods (M.Map SourceName (CAtomName n))
        deriving (Show, Generic, Monoid, Semigroup)

data TyConDef n where
  -- The `SourceName` is just for pretty-printing. The actual alpha-renamable
  -- binder name is in UExpr and Env
  TyConDef
    :: SourceName
    -> [RoleExpl]
    -> Nest CBinder n l
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

type WithDecls (r::IR) = Abs (Decls r) :: E -> E
type Block (r::IR) = WithDecls r (Expr r) :: E

data LamExpr (r::IR) (n::S) where
  LamExpr :: Nest (Binder r) n l -> Expr r l -> LamExpr r n

data CoreLamExpr (n::S) = CoreLamExpr (CorePiType n) (LamExpr CoreIR n)              deriving (Show, Generic)

type TabLamExpr = PairE (TabPiType CoreIR) (Abs SBinder CAtom)
type IxDict = Dict

data IxMethod = Size | Ordinal | UnsafeFromOrdinal
     deriving (Show, Generic, Enum, Bounded, Eq)

data IxType (r::IR) (n::S) =
  IxType { ixTypeType :: Type r n
         , ixTypeDict :: IxDict r n }
  deriving (Show, Generic)

data TabPiType (r::IR) (n::S) where
  TabPiType :: IxDict r n -> Binder r n l -> Type r l -> TabPiType r n

data PiType (r::IR) (n::S) where
  PiType :: Nest (Binder r) n l -> EffTy r l -> PiType r n

data CorePiType (n::S) where
  CorePiType :: AppExplicitness -> [Explicitness] -> Nest CBinder n l -> EffTy CoreIR l -> CorePiType n

data DepPairType (r::IR) (n::S) where
  DepPairType :: DepPairExplicitness -> Binder r n l -> Type r l -> DepPairType r n

type Val  = Atom
type Kind = Type

-- A nest where the annotation of a binder cannot depend on the binders
-- introduced before it. You can think of it as introducing a bunch of
-- names into the scope in parallel, but since safer names only reasons
-- about sequential scope extensions, we encode it differently.
data NonDepNest r ann n l = NonDepNest (Nest (AtomNameBinder r) n l) [ann n]
                            deriving (Generic)

-- === ToAtomAbs class ===

class ToBindersAbs (e::E) (body::E) (r::IR) | e -> body, e -> r where
  toAbs :: e n -> Abs (Nest (Binder r)) body n

instance ToBindersAbs CorePiType (EffTy CoreIR) CoreIR where
  toAbs (CorePiType _ _ bs effTy) = Abs bs effTy

instance ToBindersAbs CoreLamExpr (Expr CoreIR) CoreIR where
  toAbs (CoreLamExpr _ lam) = toAbs lam

instance ToBindersAbs (Abs (Nest (Binder r)) body) body r where
  toAbs = id

instance ToBindersAbs (PiType r) (EffTy r) r where
  toAbs (PiType bs effTy) = Abs bs effTy

instance ToBindersAbs (LamExpr r) (Expr r) r where
  toAbs (LamExpr bs body) = Abs bs body

instance ToBindersAbs (TabPiType r) (Type r) r where
  toAbs (TabPiType _ b eltTy) = Abs (UnaryNest b) eltTy

instance ToBindersAbs (DepPairType r) (Type r) r where
  toAbs (DepPairType _ b rhsTy) = Abs (UnaryNest b) rhsTy

instance ToBindersAbs InstanceDef (ListE CAtom `PairE` InstanceBody) CoreIR where
  toAbs (InstanceDef _ _ bs params body) = Abs bs (ListE params `PairE` body)

instance ToBindersAbs TyConDef DataConDefs CoreIR where
  toAbs (TyConDef _ _ bs body) = Abs bs body

instance ToBindersAbs ClassDef (Abs (Nest CBinder) (ListE CorePiType)) CoreIR where
  toAbs (ClassDef _ _ _ _ _ bs scBs tys) = Abs bs (Abs scBs (ListE tys))

-- === GenericOp class ===

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

data PrimOp (r::IR) (n::S) where
 UnOp     :: P.UnOp  -> Atom r n             -> PrimOp r n
 BinOp    :: P.BinOp -> Atom r n -> Atom r n -> PrimOp r n
 MemOp    :: MemOp r n                       -> PrimOp r n
 VectorOp :: VectorOp r n                    -> PrimOp r n
 MiscOp   :: MiscOp r n                      -> PrimOp r n
 Hof      :: TypedHof r n                    -> PrimOp r n
 RefOp    :: Atom r n -> RefOp r n           -> PrimOp r n
 DAMOp    :: DAMOp SimpIR n              -> PrimOp SimpIR n

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
 | VectorIdx (Atom r n) (Atom r n) (Type r n)    -- table, base ix, vector type
 | VectorSubref (Atom r n) (Atom r n) (Type r n) -- ref, base ix, vector type
   deriving (Show, Generic)

data TypedHof r n = TypedHof (EffTy r n) (Hof r n)
     deriving (Show, Generic)

data Hof r n where
 For       :: ForAnn -> IxType r n -> LamExpr r n -> Hof r n
 While     :: Expr r n -> Hof r n
 RunReader :: Atom r n -> LamExpr r n -> Hof r n
 RunWriter :: Maybe (Atom r n) -> BaseMonoid r n -> LamExpr r n -> Hof r n
 RunState  :: Maybe (Atom r n) -> Atom r n -> LamExpr r n -> Hof r n  -- dest, initial value, body lambda
 RunIO     :: Expr r n -> Hof r n
 RunInit   :: Expr r n -> Hof r n
 CatchException :: CType n -> Expr   CoreIR n -> Hof CoreIR n
 Linearize      :: LamExpr CoreIR n -> Atom CoreIR n -> Hof CoreIR n
 Transpose      :: LamExpr CoreIR n -> Atom CoreIR n -> Hof CoreIR n

deriving instance IRRep r => Show (Hof r n)
deriving via WrapE (Hof r) n instance IRRep r => Generic (Hof r n)

-- Ops for "Dex Abstract Machine"
data DAMOp r n =
   Seq (EffectRow r n) Direction (IxType r n) (Atom r n) (LamExpr r n)   -- ix dict, carry dests, body lambda
 | RememberDest (EffectRow r n) (Atom r n) (LamExpr r n)
 | AllocDest (Type r n)        -- type
 | Place (Atom r n) (Atom r n) -- reference, value
 | Freeze (Atom r n)           -- reference
   deriving (Show, Generic)

data RefOp r n =
   MAsk
 | MExtend (BaseMonoid r n) (Atom r n)
 | MGet
 | MPut (Atom r n)
 | IndexRef (Type r n) (Atom r n)
 | ProjRef (Type r n) Projection
  deriving (Show, Generic)

-- === IR variants ===

type CAtom  = Atom CoreIR
type CType  = Type CoreIR
type CDict  = Dict CoreIR
type CStuck  = Stuck CoreIR
type CBinder = Binder CoreIR
type CExpr  = Expr CoreIR
type CBlock = Block CoreIR
type CDecl  = Decl  CoreIR
type CDecls = Decls CoreIR
type CAtomName  = AtomName CoreIR
type CAtomVar   = AtomVar CoreIR

type SAtom  = Atom SimpIR
type SType  = Type SimpIR
type SDict  = Dict SimpIR
type SStuck = Stuck SimpIR
type SExpr  = Expr SimpIR
type SBlock = Block SimpIR
type SAlt   = Alt   SimpIR
type SDecl  = Decl  SimpIR
type SDecls = Decls SimpIR
type SAtomName  = AtomName SimpIR
type SAtomVar   = AtomVar SimpIR
type SBinder = Binder SimpIR
type SLam    = LamExpr SimpIR

-- === newtypes ===

-- Describes how to lift the "shallow" representation type to the newtype.
data NewtypeCon (n::S) =
   UserADTData SourceName (TyConName n) (TyConParams n) -- source name is for the type
 | NatCon
 | FinCon (Atom CoreIR n)
   deriving (Show, Generic)

data NewtypeTyCon (n::S) =
   Nat
 | Fin (Atom CoreIR n)
 | EffectRowKind
 | UserADTType SourceName (TyConName n) (TyConParams n)
   deriving (Show, Generic)

isSumCon :: NewtypeCon n -> Bool
isSumCon = \case
 UserADTData _ _ _ -> True
 _ -> False

-- === type classes ===

type RoleExpl = (ParamRole, Explicitness)

data ClassDef (n::S) where
  ClassDef
    :: SourceName            -- name of class
    -> Maybe BuiltinClassName
    -> [SourceName]          -- method source names
    -> [Maybe SourceName]    -- parameter source names
    -> [RoleExpl]            -- parameter info
    -> Nest CBinder n1 n2   -- parameters
    ->   Nest CBinder n2 n3  -- superclasses
    ->   [CorePiType n3]     -- method types
    -> ClassDef n1

data BuiltinClassName = Data | Ix  deriving (Show, Generic, Eq)

data InstanceDef (n::S) where
  InstanceDef
    :: ClassName n1
    -> [RoleExpl]           -- parameter info
    -> Nest CBinder n1 n2   -- parameters (types and dictionaries)
    ->   [CAtom n2]          -- class parameters
    ->   InstanceBody n2
    -> InstanceDef n1

data InstanceBody (n::S) =
  InstanceBody
    [CAtom n]  -- superclasses dicts
    [CAtom n]  -- method definitions
  deriving (Show, Generic)

data DictType (n::S) =
   DictType SourceName (ClassName n) [CAtom n]
 | IxDictType   (CType n)
 | DataDictType (CType n)
   deriving (Show, Generic)

data DictCon (r::IR) (n::S) where
 InstanceDict  :: CType n -> InstanceName n -> [CAtom n] -> DictCon CoreIR n
 -- Special case for `Data <something that is actually data>`
 DataData      :: CType n -> DictCon CoreIR n
 IxFin         :: CAtom n -> DictCon CoreIR n
 -- IxRawFin is like `Fin`, but it's parameterized by a newtyped-stripped
 -- `IxRepVal` instead of `Nat`, and it describes indices of type `IxRepVal`.
 -- TODO: make is SimpIR-only
 IxRawFin      :: Atom r n -> DictCon r n
 IxSpecialized :: SpecDictName n -> [SAtom n] -> DictCon SimpIR n


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

-- === effects ===

data Effect (r::IR) (n::S) =
   RWSEffect RWS (Atom r n)
 | ExceptionEffect
 | IOEffect
 | InitEffect  -- Internal effect modeling writing to a destination.
 deriving (Generic, Show)

data EffectRow (r::IR) (n::S) =
  EffectRow (ESet (Effect r) n) (EffectRowTail r n)
  deriving (Generic)

data EffectRowTail (r::IR) (n::S) where
  EffectRowTail :: AtomVar CoreIR n -> EffectRowTail CoreIR n
  NoTail        ::                     EffectRowTail r n
deriving instance IRRep r => Show (EffectRowTail r n)
deriving instance IRRep r => Eq   (EffectRowTail r n)
deriving via WrapE (EffectRowTail r) n instance IRRep r => Generic (EffectRowTail r n)

data EffTy (r::IR) (n::S) =
  EffTy { etEff :: EffectRow r n
        , etTy  :: Type r n }
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

-- === Binder utils ===

binderType :: Binder r n l -> Type r n
binderType (_:>ty) = ty

binderVar  :: (IRRep r, DExt n l) => Binder r n l -> AtomVar r l
binderVar (b:>ty) = AtomVar (binderName b) (sink ty)

bindersVars :: (Distinct l, Ext n l, IRRep r)
            => Nest (Binder r) n l -> [AtomVar r l]
bindersVars = \case
  Empty -> []
  Nest b bs -> withExtEvidence b $ withSubscopeDistinct bs $
    sink (binderVar b) : bindersVars bs

-- === ToAtom ===

class ToAtom (e::E) (r::IR) | e -> r where
  toAtom :: e n -> Atom r n

instance ToAtom (Atom r) r where toAtom = id
instance ToAtom (Con  r) r where toAtom = Con
instance ToAtom (TyCon     CoreIR) CoreIR where toAtom = Con . TyConAtom
instance ToAtom (DictCon   CoreIR) CoreIR where toAtom = Con . DictConAtom
instance ToAtom (EffectRow CoreIR) CoreIR where toAtom = Con . Eff
instance ToAtom CoreLamExpr  CoreIR where toAtom = Con . Lam
instance ToAtom DictType     CoreIR where toAtom = Con . TyConAtom . DictTy
instance ToAtom NewtypeTyCon CoreIR where toAtom = Con . TyConAtom . NewtypeTyCon
instance ToAtom (AtomVar r) r where
  toAtom (AtomVar v ty) = Stuck ty (Var (AtomVar v ty))
instance ToAtom RepVal SimpIR where
  toAtom (RepVal ty tree) = Stuck ty $ RepValAtom $ RepVal ty tree
instance ToAtom (Type CoreIR) CoreIR where
  toAtom = \case
    TyCon con -> Con $ TyConAtom con
    StuckTy t s -> Stuck t s
instance ToAtom (Dict CoreIR) CoreIR where
  toAtom = \case
    DictCon d -> Con $ DictConAtom d
    StuckDict t s -> Stuck t s

-- This can help avoid ambiguous `r` parameter with ToAtom
toAtomR :: ToAtom (e r) r => e r n -> Atom r n
toAtomR = toAtom

-- === ToType ===

class ToType (e::E) (r::IR) | e -> r where
  toType :: e n -> Type r n

instance ToType (Type        r) r where toType = id
instance ToType (TyCon       r) r where toType = TyCon
instance ToType (TabPiType   r) r where toType = TyCon . TabPi
instance ToType (DepPairType r) r where toType = TyCon . DepPairTy
instance ToType CorePiType   CoreIR where toType = TyCon . Pi
instance ToType DictType     CoreIR where toType = TyCon . DictTy
instance ToType NewtypeTyCon CoreIR where toType = TyCon . NewtypeTyCon

toMaybeType :: CAtom n -> Maybe (CType n)
toMaybeType = \case
  Stuck t s -> Just $ StuckTy t s
  Con (TyConAtom t) -> Just $ TyCon t
  _ -> Nothing

-- === ToDict ===

class ToDict (e::E) (r::IR) | e -> r where
  toDict :: e n -> Dict r n

instance ToDict (Dict       r) r where toDict = id
instance ToDict (DictCon    r) r where toDict = DictCon
instance ToDict CAtomVar CoreIR where
  toDict (AtomVar v ty) = StuckDict ty (Var (AtomVar v ty))

toMaybeDict :: CAtom n -> Maybe (CDict n)
toMaybeDict = \case
  Stuck t s -> Just $ StuckDict t s
  Con (DictConAtom d) -> Just $ DictCon d
  _ -> Nothing

-- === ToExpr ===

class ToExpr (e::E) (r::IR) | e -> r where
  toExpr :: e n -> Expr r n

instance ToExpr (Expr     r) r where toExpr = id
instance ToExpr (Atom     r) r where toExpr = Atom
instance ToExpr (Con      r) r where toExpr = Atom . Con
instance ToExpr (AtomVar  r) r where toExpr = toExpr . toAtom
instance ToExpr (PrimOp   r) r where toExpr = PrimOp
instance ToExpr (MiscOp   r) r where toExpr = PrimOp . MiscOp
instance ToExpr (MemOp    r) r where toExpr = PrimOp . MemOp
instance ToExpr (VectorOp r) r where toExpr = PrimOp . VectorOp
instance ToExpr (TypedHof r) r where toExpr = PrimOp . Hof
instance ToExpr (DAMOp SimpIR) SimpIR where toExpr = PrimOp . DAMOp

-- === Pattern synonyms ===

pattern IdxRepScalarBaseTy :: ScalarBaseType
pattern IdxRepScalarBaseTy = Word32Type

-- Type used to represent indices and sizes at run-time
pattern IdxRepTy :: Type r n
pattern IdxRepTy = TyCon (BaseType (Scalar Word32Type))

pattern IdxRepVal :: Word32 -> Atom r n
pattern IdxRepVal x = Con (Lit (Word32Lit x))

pattern IIdxRepVal :: Word32 -> IExpr n
pattern IIdxRepVal x = ILit (Word32Lit x)

pattern IIdxRepTy :: IType
pattern IIdxRepTy = Scalar Word32Type

-- Type used to represent sum type tags at run-time
pattern TagRepTy :: Type r n
pattern TagRepTy = TyCon (BaseType (Scalar Word8Type))

pattern TagRepVal :: Word8 -> Atom r n
pattern TagRepVal x = Con (Lit (Word8Lit x))

pattern CharRepTy :: Type r n
pattern CharRepTy = Word8Ty

charRepVal :: Char -> Atom r n
charRepVal c = Con (Lit (Word8Lit (fromIntegral $ fromEnum c)))

pattern Word8Ty :: Type r n
pattern Word8Ty = TyCon (BaseType (Scalar Word8Type))

pattern PairVal :: Atom r n -> Atom r n -> Atom r n
pattern PairVal x y = Con (ProdCon [x, y])

pattern PairTy :: Type r n -> Type r n -> Type r n
pattern PairTy x y = TyCon (ProdType [x, y])

pattern UnitVal :: Atom r n
pattern UnitVal = Con (ProdCon [])

pattern UnitTy :: Type r n
pattern UnitTy = TyCon (ProdType [])

pattern BaseTy :: BaseType -> Type r n
pattern BaseTy b = TyCon (BaseType b)

pattern PtrTy :: PtrType -> Type r n
pattern PtrTy ty = TyCon (BaseType (PtrType ty))

pattern RefTy :: Atom r n -> Type r n -> Type r n
pattern RefTy r a = TyCon (RefType r a)

pattern RawRefTy :: Type r n -> Type r n
pattern RawRefTy a = TyCon (RefType (Con HeapVal) a)

pattern TabTy :: IxDict r n -> Binder r n l -> Type r l -> Type r n
pattern TabTy d b body = TyCon (TabPi (TabPiType d b body))

pattern FinTy :: Atom CoreIR n -> Type CoreIR n
pattern FinTy n = TyCon (NewtypeTyCon (Fin n))

pattern NatTy :: Type CoreIR n
pattern NatTy = TyCon (NewtypeTyCon Nat)

pattern NatVal :: Word32 -> Atom CoreIR n
pattern NatVal n = Con (NewtypeCon NatCon (IdxRepVal n))

pattern TyKind :: Kind CoreIR n
pattern TyKind = TyCon TypeKind

pattern EffKind :: Kind CoreIR n
pattern EffKind = TyCon (NewtypeTyCon EffectRowKind)

pattern FinConst :: Word32 -> Type CoreIR n
pattern FinConst n = TyCon (NewtypeTyCon (Fin (NatVal n)))

pattern NullaryLamExpr :: Expr r n -> LamExpr r n
pattern NullaryLamExpr body = LamExpr Empty body

pattern UnaryLamExpr :: Binder r n l -> Expr r l -> LamExpr r n
pattern UnaryLamExpr b body = LamExpr (UnaryNest b) body

pattern BinaryLamExpr :: Binder r n l1 -> Binder r l1 l2 -> Expr r l2 -> LamExpr r n
pattern BinaryLamExpr b1 b2 body = LamExpr (BinaryNest b1 b2) body

pattern MaybeTy :: Type r n -> Type r n
pattern MaybeTy a = TyCon (SumType [UnitTy, a])

pattern NothingAtom :: Type r n -> Atom r n
pattern NothingAtom a = Con (SumCon [UnitTy, a] 0 UnitVal)

pattern JustAtom :: Type r n -> Atom r n -> Atom r n
pattern JustAtom a x = Con (SumCon [UnitTy, a] 1 x)

pattern BoolTy :: Type r n
pattern BoolTy = Word8Ty

pattern FalseAtom :: Atom r n
pattern FalseAtom = Con (Lit (Word8Lit 0))

pattern TrueAtom :: Atom r n
pattern TrueAtom = Con (Lit (Word8Lit 1))

-- === Typeclass instances for Name and other Haskell libraries ===

instance GenericE RepVal where
  type RepE RepVal= PairE SType (ComposeE Tree IExpr)
  fromE (RepVal ty tree) = ty `PairE` ComposeE tree
  toE   (ty `PairE` ComposeE tree) = RepVal ty tree

instance SinkableE      RepVal
instance RenameE        RepVal
instance HoistableE     RepVal
instance AlphaHashableE RepVal
instance AlphaEqE       RepVal

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
  type RepE TyConDef = PairE (LiftE (SourceName, [RoleExpl])) (Abs (Nest CBinder) DataConDefs)
  fromE (TyConDef sourceName expls bs cons) = PairE (LiftE (sourceName, expls)) (Abs bs cons)
  {-# INLINE fromE #-}
  toE   (PairE (LiftE (sourceName, expls)) (Abs bs cons)) = TyConDef sourceName expls bs cons
  {-# INLINE toE #-}

deriving instance Show (TyConDef n)
deriving via WrapE TyConDef n instance Generic (TyConDef n)
instance SinkableE TyConDef
instance HoistableE  TyConDef
instance RenameE     TyConDef
instance AlphaEqE TyConDef
instance AlphaHashableE TyConDef

instance HasNameHint (TyConDef n) where
  getNameHint (TyConDef v _ _ _) = getNameHint v

instance HasSourceName (TyConDef n) where
  getSourceName (TyConDef v _ _ _) = v

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
   {- UserADTData -}  (LiftE SourceName `PairE` TyConName `PairE` TyConParams)
   {- NatCon -}       UnitE
   {- FinCon -}       CAtom
  fromE = \case
    UserADTData sn d p -> Case0 $ LiftE sn `PairE` d `PairE` p
    NatCon          -> Case1 UnitE
    FinCon n        -> Case2 n
  {-# INLINE fromE #-}
  toE = \case
    Case0 (LiftE sn `PairE` d `PairE` p) -> UserADTData sn d p
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

instance IRRep r => GenericE (DAMOp r) where
  type RepE (DAMOp r) = EitherE5
  {- Seq -}            (EffectRow r `PairE` LiftE Direction `PairE` IxType r `PairE` Atom r `PairE` LamExpr r)
  {- RememberDest -}   (EffectRow r `PairE` Atom r `PairE` LamExpr r)
  {- AllocDest -}      (Type r)
  {- Place -}          (Atom r `PairE` Atom r)
  {- Freeze -}         (Atom r)
  fromE = \case
    Seq e d x y z      -> Case0 $ e `PairE` LiftE d `PairE` x `PairE` y `PairE` z
    RememberDest e x y -> Case1 (e `PairE` x `PairE` y)
    AllocDest x      -> Case2 x
    Place x y        -> Case3 (x `PairE` y)
    Freeze x         -> Case4 x
  {-# INLINE fromE #-}
  toE = \case
    Case0 (e `PairE` LiftE d `PairE` x `PairE` y `PairE` z) -> Seq e d x y z
    Case1 (e `PairE` x `PairE` y)                           -> RememberDest e x y
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

instance IRRep r => GenericE (TypedHof r) where
  type RepE (TypedHof r) = EffTy r `PairE` Hof r
  fromE (TypedHof effTy hof) = effTy `PairE` hof
  {-# INLINE fromE #-}
  toE   (effTy `PairE` hof) = TypedHof effTy hof
  {-# INLINE toE #-}

instance IRRep r => SinkableE      (TypedHof r)
instance IRRep r => HoistableE     (TypedHof r)
instance IRRep r => RenameE        (TypedHof r)
instance IRRep r => AlphaEqE       (TypedHof r)
instance IRRep r => AlphaHashableE (TypedHof r)

instance IRRep r => GenericE (Hof r) where
  type RepE (Hof r) = EitherE2
    (EitherE6
  {- For -}       (LiftE ForAnn `PairE` IxType r `PairE` LamExpr r)
  {- While -}     (Expr r)
  {- RunReader -} (Atom r `PairE` LamExpr r)
  {- RunWriter -} (MaybeE (Atom r) `PairE` BaseMonoid r `PairE` LamExpr r)
  {- RunState -}  (MaybeE (Atom r) `PairE` Atom r `PairE` LamExpr r)
  {- RunIO -}     (Expr r)
    ) (EitherE4
  {- RunInit -}        (Expr r)
  {- CatchException -} (WhenCore r (Type r `PairE` Expr r))
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
    CatchException ty body -> Case1 (Case1 (WhenIRE (ty `PairE` body)))
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
      Case1 (WhenIRE (ty `PairE` body)) -> CatchException ty body
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
    IndexRef t x               -> GenericOpRep P.IndexRef    [t] [x] []
    ProjRef t p                -> GenericOpRep (P.ProjRef p) [t] []  []
  {-# INLINE fromOp #-}
  toOp = \case
    GenericOpRep P.MAsk        [] []     []  -> Just $ MAsk
    GenericOpRep P.MExtend     [] [z, x] [f] -> Just $ MExtend (BaseMonoid z f) x
    GenericOpRep P.MGet        [] []     []  -> Just $ MGet
    GenericOpRep P.MPut        [] [x]    []  -> Just $ MPut x
    GenericOpRep P.IndexRef    [t] [x]   []  -> Just $ IndexRef t x
    GenericOpRep (P.ProjRef p) [t] []    []  -> Just $ ProjRef t p
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

instance IRRep r => GenericE (Atom r) where
  type RepE (Atom r) = EitherE (PairE (Type r) (Stuck r)) (Con r)
  fromE = \case
    Stuck t x -> LeftE (PairE t x)
    Con x -> RightE x
  {-# INLINE fromE #-}
  toE = \case
    LeftE (PairE t x) -> Stuck t x
    RightE x -> Con x
  {-# INLINE toE #-}

instance IRRep r => SinkableE      (Atom r)
instance IRRep r => HoistableE     (Atom r)
instance IRRep r => AlphaEqE       (Atom r)
instance IRRep r => AlphaHashableE (Atom r)
instance IRRep r => RenameE        (Atom r)

instance IRRep r => GenericE (Stuck r) where
  type RepE (Stuck r) = EitherE2
                         (EitherE6
 {-  Var     -}           (AtomVar r)
 {-  StuckProject -}      (LiftE Int `PairE` Stuck r)
 {-  StuckTabApp  -}      (Stuck r `PairE` Atom r)
 {-  StuckUnwrap  -}      (WhenCore r (CStuck))
 {-  InstantiatedGiven -} (WhenCore r (CStuck `PairE` ListE CAtom))
 {-  SuperclassProj    -} (WhenCore r (LiftE Int `PairE` CStuck))
                         ) (EitherE6
 {-  PtrVar -}            (LiftE PtrType `PairE` PtrName)
 {-  RepValAtom -}        (WhenSimp r RepVal)
 {-  LiftSimp -}          (WhenCore r (CType `PairE` SStuck))
 {-  LiftSimpFun -}       (WhenCore r (CorePiType `PairE` LamExpr SimpIR))
 {-  TabLam -}            (WhenCore r TabLamExpr)
 {-  ACase -}             (WhenCore r (SStuck `PairE` ListE (Abs SBinder CAtom) `PairE` CType))
                        )

  fromE = \case
    Var v                  -> Case0 $ Case0 v
    StuckProject i e       -> Case0 $ Case1 $ LiftE i `PairE` e
    StuckTabApp f x        -> Case0 $ Case2 $ f `PairE` x
    StuckUnwrap e          -> Case0 $ Case3 $ WhenIRE $ e
    InstantiatedGiven e xs -> Case0 $ Case4 $ WhenIRE $ e `PairE` ListE xs
    SuperclassProj i e     -> Case0 $ Case5 $ WhenIRE $ LiftE i `PairE` e
    PtrVar t p        -> Case1 $ Case0 $ LiftE t `PairE` p
    RepValAtom r      -> Case1 $ Case1 $ WhenIRE r
    LiftSimp t x      -> Case1 $ Case2 $ WhenIRE $ t `PairE` x
    LiftSimpFun t lam -> Case1 $ Case3 $ WhenIRE $ t `PairE` lam
    TabLam lam        -> Case1 $ Case4 $ WhenIRE lam
    ACase s alts ty   -> Case1 $ Case5 $ WhenIRE $ s `PairE` ListE alts `PairE` ty
  {-# INLINE fromE #-}

  toE = \case
    Case0 con -> case con of
      Case0 v ->    Var v
      Case1 (LiftE i `PairE` e)            -> StuckProject i e
      Case2 (f `PairE` x)                  -> StuckTabApp f x
      Case3 (WhenIRE e)                    -> StuckUnwrap e
      Case4 (WhenIRE (e `PairE` ListE xs)) -> InstantiatedGiven e xs
      Case5 (WhenIRE (LiftE i `PairE` e))  -> SuperclassProj i e
      _ -> error "impossible"
    Case1 con -> case con of
      Case0 (LiftE t `PairE` p)       -> PtrVar t p
      Case1 (WhenIRE r)               -> RepValAtom r
      Case2 (WhenIRE (t `PairE` x))   -> LiftSimp t x
      Case3 (WhenIRE (t `PairE` lam)) -> LiftSimpFun t lam
      Case4 (WhenIRE lam)             -> TabLam lam
      Case5 (WhenIRE (s `PairE` ListE alts `PairE` ty)) -> ACase s alts ty
      _ -> error "impossible"
    _ -> error "impossible"
  {-# INLINE toE #-}

instance IRRep r => SinkableE      (Stuck r)
instance IRRep r => HoistableE     (Stuck r)
instance IRRep r => AlphaEqE       (Stuck r)
instance IRRep r => AlphaHashableE (Stuck r)
instance IRRep r => RenameE        (Stuck r)

instance IRRep r => GenericE (AtomVar r) where
  type RepE (AtomVar r) = PairE (AtomName r) (Type r)
  fromE (AtomVar v t) = PairE v t
  {-# INLINE fromE #-}
  toE   (PairE v t) = AtomVar v t
  {-# INLINE toE #-}

instance HasNameHint (AtomVar r n) where
  getNameHint (AtomVar v _) = getNameHint v

instance Eq (AtomVar r n) where
  AtomVar v1 _ == AtomVar v2 _ = v1 == v2

instance IRRep r => SinkableE      (AtomVar r)
instance IRRep r => HoistableE     (AtomVar r)

-- We ignore the type annotation because it should be determined by the var
instance IRRep r => AlphaEqE (AtomVar r) where
  alphaEqE (AtomVar v _) (AtomVar v' _) = alphaEqE v v'

-- We ignore the type annotation because it should be determined by the var
instance IRRep r => AlphaHashableE (AtomVar r) where
  hashWithSaltE env salt (AtomVar v _) = hashWithSaltE env salt v

instance IRRep r => RenameE        (AtomVar r)

instance IRRep r => GenericE (Type r) where
  type RepE (Type r) = EitherE (WhenCore r (PairE (Type r) (Stuck r))) (TyCon r)
  fromE = \case
    StuckTy t x -> LeftE (WhenIRE (PairE t x))
    TyCon x -> RightE x
  {-# INLINE fromE #-}
  toE = \case
    LeftE (WhenIRE (PairE t x)) -> StuckTy t x
    RightE x -> TyCon x
  {-# INLINE toE #-}

instance IRRep r => SinkableE      (Type r)
instance IRRep r => HoistableE     (Type r)
instance IRRep r => AlphaEqE       (Type r)
instance IRRep r => AlphaHashableE (Type r)
instance IRRep r => RenameE        (Type r)

instance IRRep r => GenericE (Expr r) where
  type RepE (Expr r) = EitherE2
    ( EitherE6
 {- App -}    (WhenCore r (EffTy r `PairE` Atom r `PairE` ListE (Atom r)))
 {- TabApp -} (Type r `PairE` Atom r `PairE` Atom r)
 {- Case -}   (Atom r `PairE` ListE (Alt r) `PairE` EffTy r)
 {- Atom -}   (Atom r)
 {- TopApp -} (WhenSimp r (EffTy r `PairE` TopFunName `PairE` ListE (Atom r)))
 {- Block -}  (EffTy r `PairE` Block r)
    )
    ( EitherE5
 {- TabCon -}          (MaybeE (WhenCore r (Dict CoreIR)) `PairE` Type r `PairE` ListE (Atom r))
 {- PrimOp -}          (PrimOp r)
 {- ApplyMethod -}     (WhenCore r (EffTy r `PairE` Atom r `PairE` LiftE Int `PairE` ListE (Atom r)))
 {- Project -}         (Type r `PairE` LiftE Int `PairE` Atom r)
 {- Unwrap -}          (WhenCore r (CType `PairE` CAtom)))
  fromE = \case
    App    et f xs        -> Case0 $ Case0 (WhenIRE (et `PairE` f `PairE` ListE xs))
    TabApp  t f x         -> Case0 $ Case1 (t `PairE` f `PairE` x)
    Case e alts effTy  -> Case0 $ Case2 (e `PairE` ListE alts `PairE` effTy)
    Atom x             -> Case0 $ Case3 (x)
    TopApp et f xs     -> Case0 $ Case4 (WhenIRE (et `PairE` f `PairE` ListE xs))
    Block et block     -> Case0 $ Case5 (et `PairE` block)
    TabCon d ty xs        -> Case1 $ Case0 (toMaybeE d `PairE` ty `PairE` ListE xs)
    PrimOp op             -> Case1 $ Case1 op
    ApplyMethod et d i xs -> Case1 $ Case2 (WhenIRE (et `PairE` d `PairE` LiftE i `PairE` ListE xs))
    Project ty i x        -> Case1 $ Case3 (ty `PairE` LiftE i `PairE` x)
    Unwrap t x            -> Case1 $ Case4 (WhenIRE (t `PairE` x))
  {-# INLINE fromE #-}
  toE = \case
    Case0 case0 -> case case0 of
      Case0 (WhenIRE (et `PairE` f `PairE` ListE xs))     -> App    et f xs
      Case1 (t `PairE` f `PairE` x)                       -> TabApp t f x
      Case2 (e `PairE` ListE alts `PairE` effTy)          -> Case e alts effTy
      Case3 (x)                                           -> Atom x
      Case4 (WhenIRE (et `PairE` f `PairE` ListE xs))     -> TopApp et f xs
      Case5 (et `PairE` block)                            -> Block et block
      _ -> error "impossible"
    Case1 case1 -> case case1 of
      Case0 (d `PairE` ty `PairE` ListE xs) -> TabCon (fromMaybeE d) ty xs
      Case1 op -> PrimOp op
      Case2 (WhenIRE (et `PairE` d `PairE` LiftE i `PairE` ListE xs)) -> ApplyMethod et d i xs
      Case3 (ty `PairE` LiftE i `PairE` x) -> Project ty i x
      Case4 (WhenIRE (t `PairE` x)) -> Unwrap t x
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
   ) (EitherE3
 {- Hof -}           (TypedHof r)
 {- RefOp -}         (Atom r `PairE` RefOp r)
 {- DAMOp -}         (WhenSimp r (DAMOp SimpIR))
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
    VectorIdx x y t     -> GenericOpRep P.VectorIdx       [t] [x, y] []
    VectorSubref x y t  -> GenericOpRep P.VectorSubref    [t] [x, y] []
  {-# INLINE fromOp #-}

  toOp = \case
    GenericOpRep P.VectorBroadcast [t] [x]    [] -> Just $ VectorBroadcast x t
    GenericOpRep P.VectorIota      [t] []     [] -> Just $ VectorIota t
    GenericOpRep P.VectorIdx       [t] [x, y] [] -> Just $ VectorIdx x y t
    GenericOpRep P.VectorSubref    [t] [x, y] [] -> Just $ VectorSubref x y t
    _ -> Nothing
  {-# INLINE toOp #-}

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

instance IRRep r => GenericE (MiscOp r) where
  type RepE (MiscOp r) = GenericOpRep (OpConst MiscOp r) r
  fromE = fromEGenericOpRep
  toE   = toEGenericOpRep
instance IRRep r => SinkableE      (MiscOp r)
instance IRRep r => HoistableE     (MiscOp r)
instance IRRep r => AlphaEqE       (MiscOp r)
instance IRRep r => AlphaHashableE (MiscOp r)
instance IRRep r => RenameE        (MiscOp r)

instance IRRep r => GenericE (Con r) where
  type RepE (Con r) = EitherE2
    (EitherE5
  {- Lit -}      (LiftE LitVal)
  {- ProdCon -}  (ListE (Atom r))
  {- SumCon -}   (ListE (Type r) `PairE` LiftE Int `PairE` Atom r)
  {- HeapVal -}  UnitE
  {- DepPair -}  (Atom r `PairE` Atom r `PairE` DepPairType r))
    (WhenCore r (EitherE5
  {- Lam -}         CoreLamExpr
  {- Eff -}         (EffectRow CoreIR)
  {- NewtypeCon -}  (NewtypeCon `PairE` CAtom)
  {- DictConAtom -} (DictCon CoreIR)
  {- TyConAtom -}   (TyCon CoreIR)))
  fromE = \case
    Lit l         -> Case0 $ Case0 $ LiftE l
    ProdCon xs    -> Case0 $ Case1 $ ListE xs
    SumCon ts i x -> Case0 $ Case2 $ ListE ts `PairE` LiftE i `PairE` x
    HeapVal       -> Case0 $ Case3 $ UnitE
    DepPair x y t -> Case0 $ Case4 $ x `PairE` y `PairE` t
    Lam lam          -> Case1 $ WhenIRE $ Case0 lam
    Eff effs         -> Case1 $ WhenIRE $ Case1 effs
    NewtypeCon con x -> Case1 $ WhenIRE $ Case2 $ con `PairE` x
    DictConAtom con  -> Case1 $ WhenIRE $ Case3 con
    TyConAtom tc     -> Case1 $ WhenIRE $ Case4 tc
  {-# INLINE fromE #-}
  toE = \case
    Case0 con -> case con of
      Case0 (LiftE l) -> Lit l
      Case1 (ListE xs) -> ProdCon xs
      Case2 (ListE ts `PairE` LiftE i `PairE` x) -> SumCon ts i x
      Case3 UnitE   -> HeapVal
      Case4 (x `PairE` y `PairE` t) -> DepPair x y t
      _ -> error "impossible"
    Case1 (WhenIRE con) -> case con of
      Case0 lam             -> Lam lam
      Case1 effs            -> Eff effs
      Case2 (con' `PairE` x) -> NewtypeCon con' x
      Case3 con'             -> DictConAtom con'
      Case4 tc              -> TyConAtom tc
      _ -> error "impossible"
    _ -> error "impossible"
  {-# INLINE toE #-}

instance IRRep r => SinkableE      (Con r)
instance IRRep r => HoistableE     (Con r)
instance IRRep r => AlphaEqE       (Con r)
instance IRRep r => AlphaHashableE (Con r)
instance IRRep r => RenameE        (Con r)

instance IRRep r => GenericE (TyCon r) where
  type RepE (TyCon r) = EitherE3
                     (EitherE4
  {- BaseType -}        (LiftE BaseType)
  {- ProdType -}        (ListE (Type r))
  {- SumType -}         (ListE (Type r))
  {- RefType -}         (Atom r `PairE` Type r))
                     (EitherE4
  {- HeapType -}      UnitE
  {- TabPi -}         (TabPiType r)
  {- DepPairTy -}     (DepPairType r)
  {- TypeKind -}      (WhenCore r UnitE))
                     (EitherE3
  {- DictTy -}        (WhenCore r DictType)
  {- Pi -}            (WhenCore r CorePiType)
  {- NewtypeTyCon -}  (WhenCore r NewtypeTyCon))
  fromE = \case
    BaseType b     -> Case0 (Case0 (LiftE b))
    ProdType ts    -> Case0 (Case1 (ListE ts))
    SumType  ts    -> Case0 (Case2 (ListE ts))
    RefType h t    -> Case0 (Case3 (h `PairE` t))
    HeapType       -> Case1 (Case0 UnitE)
    TabPi t        -> Case1 (Case1 t)
    DepPairTy t    -> Case1 (Case2 t)
    TypeKind       -> Case1 (Case3 (WhenIRE UnitE))
    DictTy    t    -> Case2 (Case0 (WhenIRE t))
    Pi        t    -> Case2 (Case1 (WhenIRE t))
    NewtypeTyCon t -> Case2 (Case2 (WhenIRE t))
  {-# INLINE fromE #-}
  toE = \case
    Case0 c -> case c of
      Case0 (LiftE b ) -> BaseType b
      Case1 (ListE ts) -> ProdType ts
      Case2 (ListE ts) -> SumType ts
      Case3 (h `PairE` t) -> RefType h t
      _ -> error "impossible"
    Case1 c -> case c of
      Case0 UnitE -> HeapType
      Case1 t -> TabPi t
      Case2 t -> DepPairTy t
      Case3 (WhenIRE UnitE) -> TypeKind
      _ -> error "impossible"
    Case2 c -> case c of
      Case0 (WhenIRE t) -> DictTy       t
      Case1 (WhenIRE t) -> Pi           t
      Case2 (WhenIRE t) -> NewtypeTyCon t
      _ -> error "impossible"
    _ -> error "impossible"
  {-# INLINE toE #-}

instance IRRep r => SinkableE      (TyCon r)
instance IRRep r => HoistableE     (TyCon r)
instance IRRep r => AlphaEqE       (TyCon r)
instance IRRep r => AlphaHashableE (TyCon r)
instance IRRep r => RenameE        (TyCon r)

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

instance GenericE ClassDef where
  type RepE ClassDef =
    LiftE (SourceName, Maybe BuiltinClassName, [SourceName], [Maybe SourceName], [RoleExpl])
     `PairE` Abs (Nest CBinder) (Abs (Nest CBinder) (ListE CorePiType))
  fromE (ClassDef name builtin names paramNames roleExpls b scs tys) =
    LiftE (name, builtin, names, paramNames, roleExpls) `PairE` Abs b (Abs scs (ListE tys))
  {-# INLINE fromE #-}
  toE (LiftE (name, builtin, names, paramNames, roleExpls) `PairE` Abs b (Abs scs (ListE tys))) =
    ClassDef name builtin names paramNames roleExpls b scs tys
  {-# INLINE toE #-}

instance SinkableE ClassDef
instance HoistableE  ClassDef
instance AlphaEqE ClassDef
instance AlphaHashableE ClassDef
instance RenameE     ClassDef
deriving instance Show (ClassDef n)
deriving via WrapE ClassDef n instance Generic (ClassDef n)
instance HasSourceName (ClassDef n) where
  getSourceName = \case ClassDef name _ _ _ _ _ _ _ -> name

instance GenericE InstanceDef where
  type RepE InstanceDef =
    ClassName `PairE` LiftE [RoleExpl] `PairE` Abs (Nest CBinder) (ListE CAtom `PairE` InstanceBody)
  fromE (InstanceDef name expls bs params body) =
    name `PairE` LiftE expls `PairE` Abs bs (ListE params `PairE` body)
  toE (name `PairE` LiftE expls `PairE` Abs bs (ListE params `PairE` body)) =
    InstanceDef name expls bs params body

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
  type RepE DictType = EitherE3
   {- DictType -}     (LiftE SourceName `PairE` ClassName `PairE` ListE CAtom)
   {- IxDictType -}   CType
   {- DataDictType -} CType
  fromE = \case
    DictType sourceName className params -> Case0 $ LiftE sourceName `PairE` className `PairE` ListE params
    IxDictType   ty -> Case1 ty
    DataDictType ty -> Case2 ty
  toE = \case
    Case0 (LiftE sourceName `PairE` className `PairE` ListE params) -> DictType sourceName className params
    Case1 ty -> IxDictType   ty
    Case2 ty -> DataDictType ty
    _ -> error "impossible"

instance SinkableE      DictType
instance HoistableE     DictType
instance AlphaEqE       DictType
instance AlphaHashableE DictType
instance RenameE        DictType

instance IRRep r => GenericE (Dict r) where
  type RepE (Dict r) = EitherE (WhenCore r (PairE (Type r) (Stuck r))) (DictCon r)
  fromE = \case
    StuckDict t d -> LeftE (WhenIRE (PairE t d))
    DictCon d -> RightE d
  {-# INLINE fromE #-}
  toE = \case
    LeftE (WhenIRE (PairE t d)) -> StuckDict t d
    RightE d -> DictCon d
  {-# INLINE toE #-}

instance IRRep r => SinkableE      (Dict r)
instance IRRep r => HoistableE     (Dict r)
instance IRRep r => AlphaEqE       (Dict r)
instance IRRep r => AlphaHashableE (Dict r)
instance IRRep r => RenameE        (Dict r)

instance IRRep r => GenericE (DictCon r) where
  type RepE (DictCon r) = EitherE5
 {- InstanceDict -}      (WhenCore r (CType `PairE` PairE InstanceName (ListE CAtom)))
 {- IxFin -}             (WhenCore r CAtom)
 {- DataData -}          (WhenCore r CType)
 {- IxRawFin      -}     (Atom r)
 {- IxSpecialized -}     (WhenSimp r (SpecDictName `PairE` ListE SAtom))
  fromE = \case
    InstanceDict t v args -> Case0 $ WhenIRE $ t `PairE` PairE v (ListE args)
    IxFin x               -> Case1 $ WhenIRE $ x
    DataData ty           -> Case2 $ WhenIRE $ ty
    IxRawFin n            -> Case3 $ n
    IxSpecialized d xs    -> Case4 $ WhenIRE $ d `PairE` ListE xs
  toE = \case
    Case0 (WhenIRE (t `PairE` (PairE v (ListE args)))) -> InstanceDict t v args
    Case1 (WhenIRE x)                                  -> IxFin x
    Case2 (WhenIRE ty)                                 -> DataData ty
    Case3 n                                            -> IxRawFin n
    Case4 (WhenIRE (d `PairE` ListE xs))               -> IxSpecialized d xs
    _ -> error "impossible"

instance IRRep r => SinkableE      (DictCon r)
instance IRRep r => HoistableE     (DictCon r)
instance IRRep r => AlphaEqE       (DictCon r)
instance IRRep r => AlphaHashableE (DictCon r)
instance IRRep r => RenameE        (DictCon r)

instance GenericE (LamExpr r) where
  type RepE (LamExpr r) = Abs (Nest (Binder r)) (Expr r)
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

instance GenericE CorePiType where
  type RepE CorePiType = LiftE (AppExplicitness, [Explicitness]) `PairE` Abs (Nest CBinder) (EffTy CoreIR)
  fromE (CorePiType ex exs b effTy) = LiftE (ex, exs) `PairE` Abs b effTy
  {-# INLINE fromE #-}
  toE   (LiftE (ex, exs) `PairE` Abs b effTy) = CorePiType ex exs b effTy
  {-# INLINE toE #-}

instance SinkableE      CorePiType
instance HoistableE     CorePiType
instance AlphaEqE       CorePiType
instance AlphaHashableE CorePiType
instance RenameE        CorePiType
deriving instance Show (CorePiType n)
deriving via WrapE CorePiType n instance Generic (CorePiType n)

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
  type RepE (TabPiType r) = PairE (IxDict r) (Abs (Binder r) (Type r))
  fromE (TabPiType d b resultTy) = PairE d (Abs b resultTy)
  {-# INLINE fromE #-}
  toE   (PairE d (Abs b resultTy)) = TabPiType d b resultTy
  {-# INLINE toE #-}

instance IRRep r => AlphaEqE (TabPiType r) where
  alphaEqE (TabPiType _ b1 t1) (TabPiType _ b2 t2) =
    alphaEqE (Abs b1 t1) (Abs b2 t2)

instance IRRep r => AlphaHashableE (TabPiType r) where
  hashWithSaltE env salt (TabPiType _ b t) = hashWithSaltE env salt $ Abs b t

instance HasNameHint (TabPiType r n) where
  getNameHint (TabPiType _ b _) = getNameHint b

instance IRRep r => SinkableE      (TabPiType r)
instance IRRep r => HoistableE     (TabPiType r)
instance IRRep r => RenameE        (TabPiType r)
deriving instance IRRep r => Show (TabPiType r n)
deriving via WrapE (TabPiType r) n instance IRRep r => Generic (TabPiType r n)

instance GenericE (PiType r) where
  type RepE (PiType r) = Abs (Nest (Binder r)) (EffTy r)
  fromE (PiType bs effTy) = Abs bs effTy
  {-# INLINE fromE #-}
  toE   (Abs bs effTy) = PiType bs effTy
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
  type RepE (DeclBinding r) = LiftE LetAnn `PairE` Expr r
  fromE (DeclBinding ann expr) = LiftE ann `PairE` expr
  {-# INLINE fromE #-}
  toE   (LiftE ann `PairE` expr) = DeclBinding ann expr
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
    EitherE3 (PairE (LiftE RWS) (Atom r))
             (LiftE (Either () ()))
             UnitE
  fromE = \case
    RWSEffect rws h    -> Case0 (PairE (LiftE rws) h)
    ExceptionEffect    -> Case1 (LiftE (Left  ()))
    IOEffect           -> Case1 (LiftE (Right ()))
    InitEffect         -> Case2 UnitE
  {-# INLINE fromE #-}
  toE = \case
    Case0 (PairE (LiftE rws) h) -> RWSEffect rws h
    Case1 (LiftE (Left  ())) -> ExceptionEffect
    Case1 (LiftE (Right ())) -> IOEffect
    Case2 UnitE -> InitEffect
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
  type RepE (EffectRowTail r) = EitherE (WhenCore r (AtomVar CoreIR)) UnitE
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

instance IRRep r => GenericE (EffTy r) where
  type RepE (EffTy r) = PairE (EffectRow r) (Type r)
  fromE (EffTy eff ty) = eff `PairE` ty
  {-# INLINE fromE #-}
  toE   (eff `PairE` ty) = EffTy eff ty
  {-# INLINE toE #-}

instance IRRep r => SinkableE      (EffTy r)
instance IRRep r => HoistableE     (EffTy r)
instance IRRep r => RenameE        (EffTy r)
instance IRRep r => AlphaEqE       (EffTy r)
instance IRRep r => AlphaHashableE (EffTy r)

instance IRRep r => BindsAtMostOneName (Decl r) (AtomNameC r) where
  Let b _ @> x = b @> x
  {-# INLINE (@>) #-}

instance IRRep r => BindsOneName (Decl r) (AtomNameC r) where
  binderName (Let b _) = binderName b
  {-# INLINE binderName #-}

instance Hashable IxMethod
instance Hashable ParamRole
instance Hashable BuiltinClassName

instance IRRep r => Store (MiscOp r n)
instance IRRep r => Store (VectorOp r n)
instance IRRep r => Store (MemOp r n)
instance IRRep r => Store (TyCon r n)
instance IRRep r => Store (Con r n)
instance IRRep r => Store (PrimOp r n)
instance Store (RepVal n)
instance IRRep r => Store (Type r n)
instance IRRep r => Store (EffTy r n)
instance IRRep r => Store (Stuck r n)
instance IRRep r => Store (Atom r n)
instance IRRep r => Store (AtomVar r n)
instance IRRep r => Store (Expr r n)
instance IRRep r => Store (DeclBinding r n)
instance IRRep r => Store (Decl r n l)
instance Store (TyConParams n)
instance Store (DataConDefs n)
instance Store (TyConDef n)
instance Store (DataConDef n)
instance IRRep r => Store (LamExpr r n)
instance IRRep r => Store (IxType r n)
instance Store (CorePiType n)
instance Store (CoreLamExpr n)
instance IRRep r => Store (TabPiType r n)
instance IRRep r => Store (DepPairType  r n)
instance Store BuiltinClassName
instance Store (ClassDef     n)
instance Store (InstanceDef  n)
instance Store (InstanceBody n)
instance Store (DictType n)
instance IRRep r => Store (DictCon r n)
instance Store (EffectDef n)
instance Store (EffectOpDef n)
instance Store (EffectOpType n)
instance Store (EffectOpIdx)
instance Store (ann n) => Store (NonDepNest r ann n l)
instance Store IxMethod
instance Store ParamRole
instance IRRep r => Store (Dict r n)
instance IRRep r => Store (TypedHof r n)
instance IRRep r => Store (Hof r n)
instance IRRep r => Store (RefOp r n)
instance IRRep r => Store (BaseMonoid r n)
instance IRRep r => Store (DAMOp r n)
instance Store (NewtypeCon n)
instance Store (NewtypeTyCon n)
instance Store (DotMethods n)

-- === Pretty instances ===

instance IRRep r => Pretty (Hof r n) where pretty = prettyFromPrettyPrec
instance IRRep r => PrettyPrec (Hof r n) where
  prettyPrec hof = atPrec LowestPrec case hof of
    For _ _ lam -> "for" <+> pLowest lam
    While body    -> "while" <+> pArg body
    RunReader x body    -> "runReader" <+> pArg x <> nest 2 (line <> p body)
    RunWriter _ bm body -> "runWriter" <+> pArg bm <> nest 2 (line <> p body)
    RunState  _ x body  -> "runState"  <+> pArg x <> nest 2 (line <> p body)
    RunIO body          -> "runIO" <+> pArg body
    RunInit body        -> "runInit" <+> pArg body
    CatchException _ body -> "catchException" <+> pArg body
    Linearize body x    -> "linearize" <+> pArg body <+> pArg x
    Transpose body x    -> "transpose" <+> pArg body <+> pArg x
    where
      p :: Pretty a => a -> Doc ann
      p = pretty

instance IRRep r => Pretty (DAMOp r n) where pretty = prettyFromPrettyPrec
instance IRRep r => PrettyPrec (DAMOp r n) where
  prettyPrec op = atPrec LowestPrec case op of
    Seq _ ann _ c lamExpr -> case lamExpr of
      UnaryLamExpr b body -> do
        "seq" <+> pApp ann <+> pApp c <+> prettyLam (pretty b <> ".") body
      _ -> pretty (show op) -- shouldn't happen, but crashing pretty printers make debugging hard
    RememberDest _ x y    -> "rememberDest" <+> pArg x <+> pArg y
    Place r v -> pApp r <+> "r:=" <+> pApp v
    Freeze r  -> "freeze" <+> pApp r
    AllocDest ty -> "alloc" <+> pApp ty

instance IRRep r => Pretty (TyCon r n) where pretty = prettyFromPrettyPrec
instance IRRep r => PrettyPrec (TyCon r n) where
  prettyPrec con = case con of
    BaseType b   -> prettyPrec b
    ProdType []  -> atPrec ArgPrec $ "()"
    ProdType as  -> atPrec ArgPrec $ align $ group $
      encloseSep "(" ")" ", " $ fmap pApp as
    SumType  cs  -> atPrec ArgPrec $ align $ group $
      encloseSep "(|" "|)" " | " $ fmap pApp cs
    RefType h a -> atPrec AppPrec $ pAppArg "Ref" [h] <+> p a
    TypeKind -> atPrec ArgPrec "Type"
    HeapType -> atPrec ArgPrec "Heap"
    Pi piType -> atPrec LowestPrec $ align $ p piType
    TabPi piType -> atPrec LowestPrec $ align $ p piType
    DepPairTy ty -> prettyPrec ty
    DictTy  t -> atPrec LowestPrec $ p t
    NewtypeTyCon con' -> prettyPrec con'
    where
      p :: Pretty a => a -> Doc ann
      p = pretty

prettyPrecNewtype :: NewtypeCon n -> CAtom n -> DocPrec ann
prettyPrecNewtype con x = case (con, x) of
  (NatCon, (IdxRepVal n)) -> atPrec ArgPrec $ pretty n
  (_, x') -> prettyPrec x'

instance Pretty (NewtypeTyCon n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (NewtypeTyCon n) where
  prettyPrec = \case
    Nat   -> atPrec ArgPrec $ "Nat"
    Fin n -> atPrec AppPrec $ "Fin" <+> pArg n
    EffectRowKind -> atPrec ArgPrec "EffKind"
    UserADTType name _ (TyConParams infs params) -> case (infs, params) of
      ([], []) -> atPrec ArgPrec $ pretty name
      ([Explicit, Explicit], [l, r])
        | Just sym <- fromInfix (fromString $ pprint name) ->
        atPrec ArgPrec $ align $ group $
          parens $ flatAlt " " "" <> pApp l <> line <> pretty sym <+> pApp r
      _  -> atPrec LowestPrec $ pAppArg (pretty name) $ ignoreSynthParams (TyConParams infs params)
    where
      fromInfix :: Text -> Maybe Text
      fromInfix t = do
        ('(', t') <- uncons t
        (t'', ')') <- unsnoc t'
        return t''

instance IRRep r => Pretty (Con r n) where pretty = prettyFromPrettyPrec
instance IRRep r => PrettyPrec (Con r n) where
  prettyPrec = \case
    Lit l        -> prettyPrec l
    ProdCon [x]  -> atPrec ArgPrec $ "(" <> pLowest x <> ",)"
    ProdCon xs  -> atPrec ArgPrec $ align $ group $
      encloseSep "(" ")" ", " $ fmap pLowest xs
    SumCon _ tag payload -> atPrec ArgPrec $
      "(" <> p tag <> "|" <+> pApp payload <+> "|)"
    HeapVal -> atPrec ArgPrec "HeapValue"
    Lam lam   -> atPrec LowestPrec $ p lam
    DepPair x y _ -> atPrec ArgPrec $ align $ group $
        parens $ p x <+> ",>" <+> p y
    Eff e -> atPrec ArgPrec $ p e
    DictConAtom d -> atPrec LowestPrec $ p d
    NewtypeCon con x -> prettyPrecNewtype con x
    TyConAtom ty -> prettyPrec ty
    where
      p :: Pretty a => a -> Doc ann
      p = pretty

instance IRRep r => Pretty (PrimOp r n) where pretty = prettyFromPrettyPrec
instance IRRep r => PrettyPrec (PrimOp r n) where
  prettyPrec = \case
    MemOp    op -> prettyPrec op
    VectorOp op -> prettyPrec op
    DAMOp op -> prettyPrec op
    Hof (TypedHof _ hof) -> prettyPrec hof
    RefOp ref eff -> atPrec LowestPrec case eff of
      MAsk        -> "ask" <+> pApp ref
      MExtend _ x -> "extend" <+> pApp ref <+> pApp x
      MGet        -> "get" <+> pApp ref
      MPut x      -> pApp ref <+> ":=" <+> pApp x
      IndexRef _ i -> pApp ref <+> "!" <+> pApp i
      ProjRef _ i   -> "proj_ref" <+> pApp ref <+> p i
    UnOp  op x   -> prettyOpDefault (UUnOp  op) [x]
    BinOp op x y -> prettyOpDefault (UBinOp op) [x, y]
    MiscOp op -> prettyOpGeneric op
    where
      p :: Pretty a => a -> Doc ann
      p = pretty

instance IRRep r => Pretty (MemOp r n) where pretty = prettyFromPrettyPrec
instance IRRep r => PrettyPrec (MemOp r n) where
  prettyPrec = \case
    PtrOffset ptr idx -> atPrec LowestPrec $ pApp ptr <+> "+>" <+> pApp idx
    PtrLoad   ptr     -> atPrec AppPrec $ pAppArg "load" [ptr]
    op -> prettyOpGeneric op

instance IRRep r => Pretty (VectorOp r n) where pretty = prettyFromPrettyPrec
instance IRRep r => PrettyPrec (VectorOp r n) where
  prettyPrec = \case
    VectorBroadcast v vty -> atPrec LowestPrec $ "vbroadcast" <+> pApp v <+> pApp vty
    VectorIota vty -> atPrec LowestPrec $ "viota" <+> pApp vty
    VectorIdx tbl i vty -> atPrec LowestPrec $ "vslice" <+> pApp tbl <+> pApp i <+> pApp vty
    VectorSubref ref i _ -> atPrec LowestPrec $ "vrefslice" <+> pApp ref <+> pApp i

prettyOpGeneric :: (IRRep r, GenericOp op, Show (OpConst op r)) => op r n -> DocPrec ann
prettyOpGeneric op = case fromEGenericOpRep op of
  GenericOpRep op' [] [] [] -> atPrec ArgPrec (pretty $ show op')
  GenericOpRep op' ts xs lams -> atPrec AppPrec $ pAppArg (pretty (show op')) xs <+> pretty ts <+> pretty lams

instance Pretty IxMethod where
  pretty method = pretty $ show method

instance Pretty (TyConParams n) where
  pretty (TyConParams _ _) = undefined

instance Pretty (TyConDef n) where
  pretty (TyConDef name _ bs cons) = "enum" <+> pretty name <+> pretty bs <> pretty cons

instance Pretty (DataConDefs n) where
  pretty = undefined

instance Pretty (DataConDef n) where
  pretty (DataConDef name _ repTy _) = pretty name <+> ":" <+> pretty repTy

instance Pretty (ClassDef n) where
  pretty (ClassDef classSourceName _ methodNames _ _ params superclasses methodTys) =
    "Class:" <+> pretty classSourceName <+> pretty methodNames
    <> indented (
         line <> "parameter binders:" <+> pretty params <>
         line <> "superclasses:" <+> pretty superclasses <>
         line <> "methods:" <+> pretty methodTys)

instance Pretty ParamRole where
  pretty r = pretty (show r)

instance Pretty (InstanceDef n) where
  pretty (InstanceDef className _ bs params _) =
    "Instance" <+> pretty className <+> pretty bs <+> pretty params

instance IRRep r => Pretty (Expr r n) where pretty = prettyFromPrettyPrec
instance IRRep r => PrettyPrec (Expr r n) where
  prettyPrec = \case
    Atom x -> prettyPrec x
    Block _ (Abs decls body) -> atPrec AppPrec $ prettyBlock decls body
    App _ f xs -> atPrec AppPrec $ pApp f <+> spaced (toList xs)
    TopApp _ f xs -> atPrec AppPrec $ pApp f <+> spaced (toList xs)
    TabApp _ f x -> atPrec AppPrec $ pApp f <> brackets (p x)
    Case e alts (EffTy effs _) -> prettyPrecCase "case" e alts effs
    TabCon _ _ es -> atPrec ArgPrec $ list $ pApp <$> es
    PrimOp op -> prettyPrec op
    ApplyMethod _ d i xs -> atPrec AppPrec $ "applyMethod" <+> p d <+> p i <+> p xs
    Project _ i x -> atPrec AppPrec $ "Project" <+> p i <+> p x
    Unwrap _  x -> atPrec AppPrec $ "Unwrap" <+> p x
    where
      p :: Pretty a => a -> Doc ann
      p = pretty

prettyPrecCase :: IRRep r => Doc ann -> Atom r n -> [Alt r n] -> EffectRow r n -> DocPrec ann
prettyPrecCase name e alts effs = atPrec LowestPrec $
  name <+> pApp e <+> "of" <>
  nest 2 (foldMap (\alt -> hardline <> prettyAlt alt) alts
          <> effectLine effs)
  where
    effectLine :: IRRep r => EffectRow r n -> Doc ann
    effectLine Pure = ""
    effectLine row = hardline <> "case annotated with effects" <+> pretty row

prettyAlt :: IRRep r => Alt r n -> Doc ann
prettyAlt (Abs b body) = prettyBinderNoAnn b <+> "->" <> nest 2 (pretty body)

prettyBinderNoAnn :: Binder r n l -> Doc ann
prettyBinderNoAnn (b:>_) = pretty b

instance IRRep r => Pretty (DeclBinding r n) where
  pretty (DeclBinding ann expr) = "Decl" <> pretty ann <+> pretty expr

instance IRRep r => Pretty (Decl r n l) where
  pretty (Let b (DeclBinding ann rhs)) =
    align $ annDoc <> pretty b <+> "=" <> (nest 2 $ group $ line <> pLowest rhs)
    where annDoc = case ann of NoInlineLet -> pretty ann <> " "; _ -> pretty ann

instance IRRep r => Pretty (PiType r n) where
  pretty (PiType bs (EffTy effs resultTy)) =
    (spaced $ unsafeFromNest $ bs) <+> "->" <+> "{" <> pretty effs <> "}" <+> pretty resultTy

instance IRRep r => Pretty (LamExpr r n) where pretty = prettyFromPrettyPrec
instance IRRep r => PrettyPrec (LamExpr r n) where
  prettyPrec (LamExpr bs body) = atPrec LowestPrec $ prettyLam (pretty bs <> ".") body

instance IRRep r => Pretty (IxType r n) where
  pretty (IxType ty dict) = parens $ "IxType" <+> pretty ty <> prettyIxDict dict

instance IRRep r => Pretty (Dict r n) where
  pretty = \case
    DictCon con -> pretty con
    StuckDict _ stuck -> pretty stuck

instance IRRep r => Pretty (DictCon r n) where
  pretty = \case
    InstanceDict _ name args -> "Instance" <+> pretty name <+> pretty args
    IxFin n -> "Ix (Fin" <+> pretty n <> ")"
    DataData a -> "Data " <+> pretty a
    IxRawFin n -> "Ix (RawFin " <> pretty n <> ")"
    IxSpecialized d xs -> pretty d <+> pretty xs

instance Pretty (DictType n) where
  pretty = \case
    DictType classSourceName _ params -> pretty classSourceName <+> spaced params
    IxDictType ty -> "Ix" <+> pretty ty
    DataDictType ty -> "Data" <+> pretty ty

instance IRRep r => Pretty (DepPairType r n) where pretty = prettyFromPrettyPrec
instance IRRep r => PrettyPrec (DepPairType r n) where
  prettyPrec (DepPairType _ b rhs) =
    atPrec ArgPrec $ align $ group $ parensSep (spaceIfColinear <> "&> ") [pretty b, pretty rhs]

instance Pretty (CoreLamExpr n) where
  pretty (CoreLamExpr _ lam) = pretty lam

instance IRRep r => Pretty (Atom r n) where pretty = prettyFromPrettyPrec
instance IRRep r => PrettyPrec (Atom r n) where
  prettyPrec atom = case atom of
    Con e -> prettyPrec e
    Stuck _ e -> prettyPrec e

instance IRRep r => Pretty (Type r n) where pretty = prettyFromPrettyPrec
instance IRRep r => PrettyPrec (Type r n) where
  prettyPrec = \case
    TyCon  e -> prettyPrec e
    StuckTy _ e -> prettyPrec e

instance IRRep r => Pretty (Stuck r n) where pretty = prettyFromPrettyPrec
instance IRRep r => PrettyPrec (Stuck r n) where
  prettyPrec = \case
    Var v -> atPrec ArgPrec $ p v
    StuckProject i v -> atPrec LowestPrec $ "StuckProject" <+> p i <+> p v
    StuckTabApp f xs -> atPrec AppPrec $ pArg f <> "." <> pArg xs
    StuckUnwrap v    -> atPrec LowestPrec $ "StuckUnwrap" <+> p v
    InstantiatedGiven v args -> atPrec LowestPrec $ "Given" <+> p v <+> p (toList args)
    SuperclassProj d' i -> atPrec LowestPrec $ "SuperclassProj" <+> p d' <+> p i
    PtrVar _ v -> atPrec ArgPrec $ p v
    RepValAtom x -> atPrec LowestPrec $ pretty x
    ACase e alts _ -> atPrec AppPrec $ "acase" <+> p e <+> p alts
    LiftSimp ty x -> atPrec ArgPrec $ "<embedded-simp-atom " <+> p x <+> " : " <+> p ty <+> ">"
    LiftSimpFun ty x -> atPrec ArgPrec $ "<embedded-simp-function " <+> p x <+> " : " <+> p ty <+> ">"
    TabLam lam -> atPrec AppPrec $ "tablam" <+> p lam
    where
      p :: Pretty a => a -> Doc ann
      p = pretty

instance PrettyPrec (AtomVar r n) where
  prettyPrec (AtomVar v _) = prettyPrec v
instance Pretty (AtomVar r n) where pretty = prettyFromPrettyPrec

instance IRRep r => Pretty (EffectRow r n) where
  pretty (EffectRow effs t) = braces $ hsep (punctuate "," (map pretty (eSetToList effs))) <> pretty t

instance IRRep r => Pretty (EffectRowTail r n) where
  pretty = \case
    NoTail -> mempty
    EffectRowTail v  -> "|" <> pretty v

instance IRRep r => Pretty (Effect r n) where
  pretty eff = case eff of
    RWSEffect rws h -> pretty rws <+> pretty h
    ExceptionEffect -> "Except"
    IOEffect        -> "IO"
    InitEffect      -> "Init"

prettyLam :: Pretty a => Doc ann -> a -> Doc ann
prettyLam binders body = group $ group (nest 4 $ binders) <> group (nest 2 $ pretty body)

instance IRRep r => Pretty (TabPiType r n) where
  pretty (TabPiType dict (b:>ty) body) = let
    prettyBody = case body of
      TyCon (Pi subpi) -> pretty subpi
      _ -> pLowest body
    prettyBinder = prettyBinderHelper (b:>ty) body
    in prettyBinder <> prettyIxDict dict <> (group $ line <> "=>" <+> prettyBody)

-- A helper to let us turn dict printing on and off.  We mostly want it off to
-- reduce clutter in prints and error messages, but when debugging synthesis we
-- want it on.
prettyIxDict :: IRRep r => IxDict r n -> Doc ann
prettyIxDict dict = if False then " " <> pretty dict else mempty

prettyBinderHelper :: IRRep r => HoistableE e => Binder r n l -> e l -> Doc ann
prettyBinderHelper (b:>ty) body =
  if binderName b `isFreeIn` body
    then parens $ pretty (b:>ty)
    else pretty ty

instance Pretty (CorePiType n) where
  pretty (CorePiType appExpl expls bs (EffTy eff resultTy)) =
    prettyBindersWithExpl expls bs <+> pretty appExpl <> prettyEff <> pretty resultTy
    where
      prettyEff = case eff of
        Pure -> space
        _    -> space <> pretty eff <> space

prettyBindersWithExpl :: forall b n l ann. PrettyB b
  => [Explicitness] -> Nest b n l -> Doc ann
prettyBindersWithExpl expls bs = do
  let groups = groupByExpl $ zip expls (unsafeFromNest bs)
  let groups' = case groups of [] -> [(Explicit, [])]
                               _  -> groups
  mconcat [withExplParens expl $ commaSep bsGroup | (expl, bsGroup) <- groups']

groupByExpl :: [(Explicitness, b UnsafeS UnsafeS)] -> [(Explicitness, [b UnsafeS UnsafeS])]
groupByExpl [] = []
groupByExpl ((expl, b):bs) = do
  let (matches, rest) = span (\(expl', _) -> expl == expl') bs
  let matches' = map snd matches
  (expl, b:matches') : groupByExpl rest

withExplParens :: Explicitness -> Doc ann -> Doc ann
withExplParens Explicit x = parens x
withExplParens (Inferred _ Unify) x = braces   $ x
withExplParens (Inferred _ (Synth _)) x = brackets x

instance Pretty (RepVal n) where
  pretty (RepVal ty tree) = "<RepVal " <+> pretty tree <+> ":" <+> pretty ty <> ">"

prettyBlock :: (IRRep r, PrettyPrec (e l)) => Nest (Decl r) n l -> e l -> Doc ann
prettyBlock Empty expr = group $ line <> pLowest expr
prettyBlock decls expr = prettyLines decls' <> hardline <> pLowest expr
    where decls' = unsafeFromNest decls

instance IRRep r => Pretty (BaseMonoid r n) where pretty = prettyFromPrettyPrec
instance IRRep r => PrettyPrec (BaseMonoid r n) where
  prettyPrec (BaseMonoid x f) =
    atPrec LowestPrec $ "baseMonoid" <+> pArg x <> nest 2 (line <> pArg f)
