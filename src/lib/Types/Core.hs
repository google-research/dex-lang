-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StrictData #-}

-- Core data types for CoreIR and its variations.

module Types.Core (module Types.Core) where

import Data.Word
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

import Types.Primitives
import Types.Source (HasSourceName (..))
import Types.Imp

-- === core IR ===

data Atom (r::IR) (n::S) where
  Con   :: Con r n  -> Atom r n
  Stuck :: Type r n -> Stuck r n -> Atom r n
  deriving (Show, Generic)

data Type (r::IR) (n::S) where
  TyCon   :: TyCon r n -> Type r n
  StuckTy :: Kind -> CStuck n  -> Type CoreIR n

data Kind = DataKind | RefKind | TypeKind | FunKind | DictKind | OtherKind
     deriving (Show, Generic, Eq, Ord)

data Dict (r::IR) (n::S) where
  DictCon :: DictCon r n -> Dict r n
  StuckDict :: CType n -> CStuck n -> Dict CoreIR n

data Con (r::IR) (n::S) where
  Lit     :: LitVal                                  -> Con r n
  ProdCon :: [Atom r n]                              -> Con r n
  SumCon  :: [Type r n] -> Int -> Atom r n           -> Con r n -- type, tag, payload
  DepPair :: Atom r n -> Atom r n -> DepPairType r n -> Con r n
  Lam        :: CoreLamExpr n                 -> Con CoreIR n
  NewtypeCon :: NewtypeCon n -> Atom CoreIR n -> Con CoreIR n
  DictConAtom :: DictCon CoreIR n             -> Con CoreIR n
  TyConAtom   :: TyCon CoreIR n               -> Con CoreIR n

data Stuck (r::IR) (n::S) where
  Var               :: AtomVar r n             -> Stuck r n
  StuckProject      :: Int -> Stuck r n        -> Stuck r n
  StuckTabApp       :: Stuck r n -> Atom r n   -> Stuck r n
  PtrVar            :: PtrType -> PtrName n    -> Stuck r n
  RepValAtom        :: RepVal r n              -> Stuck r n
  StuckUnwrap       :: CStuck n                -> Stuck CoreIR n
  InstantiatedGiven :: CStuck n -> [CAtom n]   -> Stuck CoreIR n
  SuperclassProj    :: Int -> CStuck n         -> Stuck CoreIR n

data TyCon (r::IR) (n::S) where
  BaseType :: BaseType             -> TyCon r n
  ProdType :: [Type r n]           -> TyCon r n
  SumType  :: [Type r n]           -> TyCon r n
  RefType  :: Type r n             -> TyCon r n
  TabPi        :: TabPiType r n    -> TyCon r n
  DepPairTy    :: DepPairType r n  -> TyCon r n
  DictTy       :: DictType n       -> TyCon CoreIR n
  Pi           :: CorePiType  n    -> TyCon CoreIR n
  NewtypeTyCon :: NewtypeTyCon n   -> TyCon CoreIR n
  Kind         :: Kind             -> TyCon CoreIR n

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

data Expr r n where
 Block  :: EffTy r n -> Block r n -> Expr r n
 TopApp :: EffTy SimpIR n -> TopFunName n -> [SAtom n]         -> Expr SimpIR n
 TabApp :: Type r n -> Atom r n -> Atom r n                    -> Expr r n
 Case   :: Atom r n -> [Alt r n] -> EffTy r n                  -> Expr r n
 Atom   :: Atom r n                                            -> Expr r n
 TabCon :: Type r n -> [Atom r n] -> Expr r n
 PrimOp :: Type r n -> PrimOp r (Atom r n)                     -> Expr r n
 Hof    :: TypedHof r n                                        -> Expr r n
 Project     :: Type r n -> Int -> Atom r n                    -> Expr r n
 App         :: EffTy CoreIR n -> CAtom n -> [CAtom n]         -> Expr CoreIR n
 Unwrap      :: CType n -> CAtom n                             -> Expr CoreIR n
 ApplyMethod :: EffTy CoreIR n -> CAtom n -> Int -> [CAtom n]  -> Expr CoreIR n

deriving instance IRRep r => Show (Expr r n)
deriving via WrapE (Expr r) n instance IRRep r => Generic (Expr r n)

data RepVal (r::IR) (n::S) = RepVal (Type r n) (Tree (IExpr n))
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
    -> [Explicitness]
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
  PiType :: Nest (Binder r) n l -> Type r l -> PiType r n

data CorePiType (n::S) where
  CorePiType :: AppExplicitness -> [Explicitness] -> Nest CBinder n l -> CType l -> CorePiType n

data DepPairType (r::IR) (n::S) where
  DepPairType :: DepPairExplicitness -> Binder r n l -> Type r l -> DepPairType r n

-- A nest where the annotation of a binder cannot depend on the binders
-- introduced before it. You can think of it as introducing a bunch of
-- names into the scope in parallel, but since safer names only reasons
-- about sequential scope extensions, we encode it differently.
data NonDepNest r ann n l = NonDepNest (Nest (AtomNameBinder r) n l) [ann n]
                            deriving (Generic)

-- === ToAtomAbs class ===

class ToBindersAbs (e::E) (body::E) (r::IR) | e -> body, e -> r where
  toAbs :: e n -> Abs (Nest (Binder r)) body n

instance ToBindersAbs CorePiType (Type CoreIR) CoreIR where
  toAbs (CorePiType _ _ bs ty) = Abs bs ty

instance ToBindersAbs CoreLamExpr (Expr CoreIR) CoreIR where
  toAbs (CoreLamExpr _ lam) = toAbs lam

instance ToBindersAbs (Abs (Nest (Binder r)) body) body r where
  toAbs = id

instance ToBindersAbs (PiType r) (Type r) r where
  toAbs (PiType bs ty) = Abs bs ty

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

showStringBufferSize :: Word32
showStringBufferSize = 32

-- === Hofs ===

data TypedHof r n = TypedHof (EffTy r n) (Hof r n)
     deriving (Show, Generic)

data Hof r n where
 For       :: ForAnn -> IxType r n -> LamExpr r n -> Hof r n
 While     :: Expr r n -> Hof r n
 Linearize :: LamExpr CoreIR n -> Atom CoreIR n -> Hof CoreIR n
 Transpose :: LamExpr CoreIR n -> Atom CoreIR n -> Hof CoreIR n

deriving instance IRRep r => Show (Hof r n)
deriving via WrapE (Hof r) n instance IRRep r => Generic (Hof r n)

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
 | UserADTType SourceName (TyConName n) (TyConParams n)
   deriving (Show, Generic)

isSumCon :: NewtypeCon n -> Bool
isSumCon = \case
 UserADTData _ _ _ -> True
 _ -> False

-- === type classes ===

data ClassDef (n::S) where
  ClassDef
    :: SourceName            -- name of class
    -> Maybe BuiltinClassName
    -> [SourceName]          -- method source names
    -> [Maybe SourceName]    -- parameter source names
    -> [Explicitness]        -- parameter info
    -> Nest CBinder n1 n2    -- parameters
    ->   Nest CBinder n2 n3  -- superclasses
    ->   [CorePiType n3]     -- method types
    -> ClassDef n1

data BuiltinClassName = Ix  deriving (Show, Generic, Eq)

data InstanceDef (n::S) where
  InstanceDef
    :: ClassName n1
    -> [Explicitness]        -- parameter info
    -> Nest CBinder n1 n2    -- parameters (types and dictionaries)
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
   deriving (Show, Generic)

data DictCon (r::IR) (n::S) where
 InstanceDict  :: CType n -> InstanceName n -> [CAtom n] -> DictCon CoreIR n
 IxFin         :: CAtom n -> DictCon CoreIR n
 -- IxRawFin is like `Fin`, but it's parameterized by a newtyped-stripped
 -- `IxRepVal` instead of `Nat`, and it describes indices of type `IxRepVal`.
 -- TODO: make is SimpIR-only
 IxRawFin      :: Atom r n -> DictCon r n
 IxSpecialized :: SpecDictName n -> [SAtom n] -> DictCon SimpIR n

data Effects (r::IR) (n::S) = Pure | Effectful
     deriving (Generic, Show)

instance Semigroup (Effects r n) where
  Pure <> Pure = Pure
  _ <> _ = Effectful

instance Monoid (Effects r n) where
  mempty = Pure

data EffTy (r::IR) (n::S) =
  EffTy { etEff :: Effects r n
        , etTy  :: Type r n }
     deriving (Generic, Show)

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
instance ToAtom CoreLamExpr  CoreIR where toAtom = Con . Lam
instance ToAtom DictType     CoreIR where toAtom = Con . TyConAtom . DictTy
instance ToAtom NewtypeTyCon CoreIR where toAtom = Con . TyConAtom . NewtypeTyCon
instance ToAtom (AtomVar r) r where
  toAtom (AtomVar v ty) = Stuck ty (Var (AtomVar v ty))
instance IRRep r => ToAtom (RepVal r) r where
  toAtom (RepVal ty tree) = Stuck ty $ RepValAtom $ RepVal ty tree
instance ToAtom (Type CoreIR) CoreIR where
  toAtom = \case
    TyCon con -> Con $ TyConAtom con
    StuckTy k s -> Stuck (TyCon $ Kind k) s
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
  Stuck (TyCon (Kind k)) s -> Just $ StuckTy k s
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

pattern RefTy :: Type r n -> Type r n
pattern RefTy a = TyCon (RefType a)

pattern TabTy :: IxDict r n -> Binder r n l -> Type r l -> Type r n
pattern TabTy d b body = TyCon (TabPi (TabPiType d b body))

pattern FinTy :: Atom CoreIR n -> Type CoreIR n
pattern FinTy n = TyCon (NewtypeTyCon (Fin n))

pattern NatTy :: Type CoreIR n
pattern NatTy = TyCon (NewtypeTyCon Nat)

pattern NatVal :: Word32 -> Atom CoreIR n
pattern NatVal n = Con (NewtypeCon NatCon (IdxRepVal n))

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

instance IRRep r => GenericE (RepVal r) where
  type RepE (RepVal r) = PairE (Type r) (ComposeE Tree IExpr)
  fromE (RepVal ty tree) = ty `PairE` ComposeE tree
  toE   (ty `PairE` ComposeE tree) = RepVal ty tree

instance IRRep r => SinkableE      (RepVal r)
instance IRRep r => RenameE        (RepVal r)
instance IRRep r => HoistableE     (RepVal r)
instance IRRep r => AlphaHashableE (RepVal r)
instance IRRep r => AlphaEqE       (RepVal r)

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
  type RepE TyConDef = PairE (LiftE (SourceName, [Explicitness])) (Abs (Nest CBinder) DataConDefs)
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
  type RepE NewtypeTyCon = EitherE3
    {- Nat -}              UnitE
    {- Fin -}              CAtom
    {- UserADTType -}      (LiftE SourceName `PairE` TyConName `PairE` TyConParams)
  fromE = \case
    Nat               -> Case0 UnitE
    Fin n             -> Case1 n
    UserADTType s d p -> Case2 (LiftE s `PairE` d `PairE` p)
  {-# INLINE fromE #-}

  toE = \case
    Case0 UnitE -> Nat
    Case1 n     -> Fin n
    Case2 (LiftE s `PairE` d `PairE` p) -> UserADTType s d p
    _ -> error "impossible"
  {-# INLINE toE #-}

instance SinkableE      NewtypeTyCon
instance HoistableE     NewtypeTyCon
instance AlphaEqE       NewtypeTyCon
instance AlphaHashableE NewtypeTyCon
instance RenameE        NewtypeTyCon

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
  type RepE (Hof r) = EitherE4
  {- For -}       (LiftE ForAnn `PairE` IxType r `PairE` LamExpr r)
  {- While -}     (Expr r)
  {- Linearize -} (WhenCore r (LamExpr r `PairE` Atom r))
  {- Transpose -} (WhenCore r (LamExpr r `PairE` Atom r))

  fromE = \case
    For ann d body      -> Case0 (LiftE ann `PairE` d `PairE` body)
    While body          -> Case1 body
    Linearize body x    -> Case2 (WhenIRE (PairE body x))
    Transpose body x    -> Case3 (WhenIRE (PairE body x))
  {-# INLINE fromE #-}
  toE = \case
    Case0 (LiftE ann `PairE` d `PairE` body) -> For ann d body
    Case1 body                        -> While body
    Case2 (WhenIRE (PairE body x)) -> Linearize body x
    Case3 (WhenIRE (PairE body x)) -> Transpose body x
    _ -> error "impossible"
  {-# INLINE toE #-}

instance IRRep r => SinkableE (Hof r)
instance IRRep r => HoistableE  (Hof r)
instance IRRep r => RenameE     (Hof r)
instance IRRep r => AlphaEqE (Hof r)
instance IRRep r => AlphaHashableE (Hof r)

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
                         ) (EitherE2
 {-  PtrVar -}            (LiftE PtrType `PairE` PtrName)
 {-  RepValAtom -}        (RepVal r)
                        )

  fromE = \case
    Var v                  -> Case0 $ Case0 v
    StuckProject i e       -> Case0 $ Case1 $ LiftE i `PairE` e
    StuckTabApp f x        -> Case0 $ Case2 $ f `PairE` x
    StuckUnwrap e          -> Case0 $ Case3 $ WhenIRE $ e
    InstantiatedGiven e xs -> Case0 $ Case4 $ WhenIRE $ e `PairE` ListE xs
    SuperclassProj i e     -> Case0 $ Case5 $ WhenIRE $ LiftE i `PairE` e
    PtrVar t p        -> Case1 $ Case0 $ LiftE t `PairE` p
    RepValAtom r      -> Case1 $ Case1 $ r
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
      Case1 r                         -> RepValAtom r
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
  type RepE (Type r) = EitherE (WhenCore r (PairE (LiftE Kind) (Stuck r))) (TyCon r)
  fromE = \case
    StuckTy k x -> LeftE (WhenIRE (PairE (LiftE k) x))
    TyCon x -> RightE x
  {-# INLINE fromE #-}
  toE = \case
    LeftE (WhenIRE (PairE (LiftE k) x)) -> StuckTy k x
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
    ( EitherE6
 {- TabCon -}          (Type r `PairE` ListE (Atom r))
 {- PrimOp -}          (Type r `PairE` ComposeE (PrimOp r) (Atom r))
 {- ApplyMethod -}     (WhenCore r (EffTy r `PairE` Atom r `PairE` LiftE Int `PairE` ListE (Atom r)))
 {- Project -}         (Type r `PairE` LiftE Int `PairE` Atom r)
 {- Unwrap -}          (WhenCore r (CType `PairE` CAtom))
 {- Hof -}             (TypedHof r))
  fromE = \case
    App    et f xs        -> Case0 $ Case0 (WhenIRE (et `PairE` f `PairE` ListE xs))
    TabApp  t f x         -> Case0 $ Case1 (t `PairE` f `PairE` x)
    Case e alts effTy  -> Case0 $ Case2 (e `PairE` ListE alts `PairE` effTy)
    Atom x             -> Case0 $ Case3 (x)
    TopApp et f xs     -> Case0 $ Case4 (WhenIRE (et `PairE` f `PairE` ListE xs))
    Block et block     -> Case0 $ Case5 (et `PairE` block)
    TabCon ty xs          -> Case1 $ Case0 (ty `PairE` ListE xs)
    PrimOp ty op          -> Case1 $ Case1 (ty `PairE` ComposeE op)
    ApplyMethod et d i xs -> Case1 $ Case2 (WhenIRE (et `PairE` d `PairE` LiftE i `PairE` ListE xs))
    Project ty i x        -> Case1 $ Case3 (ty `PairE` LiftE i `PairE` x)
    Unwrap t x            -> Case1 $ Case4 (WhenIRE (t `PairE` x))
    Hof hof               -> Case1 $ Case5 hof
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
      Case0 (ty `PairE` ListE xs) -> TabCon ty xs
      Case1 (ty `PairE`  ComposeE op) -> PrimOp ty op
      Case2 (WhenIRE (et `PairE` d `PairE` LiftE i `PairE` ListE xs)) -> ApplyMethod et d i xs
      Case3 (ty `PairE` LiftE i `PairE` x) -> Project ty i x
      Case4 (WhenIRE (t `PairE` x)) -> Unwrap t x
      Case5 hof -> Hof hof
      _ -> error "impossible"
    _ -> error "impossible"
  {-# INLINE toE #-}

instance IRRep r => SinkableE      (Expr r)
instance IRRep r => HoistableE     (Expr r)
instance IRRep r => AlphaEqE       (Expr r)
instance IRRep r => AlphaHashableE (Expr r)
instance IRRep r => RenameE        (Expr r)

instance IRRep r => GenericE (Con r) where
  type RepE (Con r) = EitherE2
    (EitherE4
  {- Lit -}      (LiftE LitVal)
  {- ProdCon -}  (ListE (Atom r))
  {- SumCon -}   (ListE (Type r) `PairE` LiftE Int `PairE` Atom r)
  {- DepPair -}  (Atom r `PairE` Atom r `PairE` DepPairType r))
    (WhenCore r (EitherE4
  {- Lam -}         CoreLamExpr
  {- NewtypeCon -}  (NewtypeCon `PairE` CAtom)
  {- DictConAtom -} (DictCon CoreIR)
  {- TyConAtom -}   (TyCon CoreIR)))
  fromE = \case
    Lit l         -> Case0 $ Case0 $ LiftE l
    ProdCon xs    -> Case0 $ Case1 $ ListE xs
    SumCon ts i x -> Case0 $ Case2 $ ListE ts `PairE` LiftE i `PairE` x
    DepPair x y t -> Case0 $ Case3 $ x `PairE` y `PairE` t
    Lam lam          -> Case1 $ WhenIRE $ Case0 lam
    NewtypeCon con x -> Case1 $ WhenIRE $ Case1 $ con `PairE` x
    DictConAtom con  -> Case1 $ WhenIRE $ Case2 con
    TyConAtom tc     -> Case1 $ WhenIRE $ Case3 tc
  {-# INLINE fromE #-}
  toE = \case
    Case0 con -> case con of
      Case0 (LiftE l) -> Lit l
      Case1 (ListE xs) -> ProdCon xs
      Case2 (ListE ts `PairE` LiftE i `PairE` x) -> SumCon ts i x
      Case3 (x `PairE` y `PairE` t) -> DepPair x y t
      _ -> error "impossible"
    Case1 (WhenIRE con) -> case con of
      Case0 lam             -> Lam lam
      Case1 (con' `PairE` x) -> NewtypeCon con' x
      Case2 con'             -> DictConAtom con'
      Case3 tc              -> TyConAtom tc
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
  {- RefType -}         (Type r))
                     (EitherE3
  {- TabPi -}         (TabPiType r)
  {- DepPairTy -}     (DepPairType r)
  {- Kind -}         (WhenCore r (LiftE Kind)))
                     (EitherE3
  {- DictTy -}        (WhenCore r DictType)
  {- Pi -}            (WhenCore r CorePiType)
  {- NewtypeTyCon -}  (WhenCore r NewtypeTyCon))
  fromE = \case
    BaseType b     -> Case0 (Case0 (LiftE b))
    ProdType ts    -> Case0 (Case1 (ListE ts))
    SumType  ts    -> Case0 (Case2 (ListE ts))
    RefType t      -> Case0 (Case3 t)
    TabPi t        -> Case1 (Case0 t)
    DepPairTy t    -> Case1 (Case1 t)
    Kind k         -> Case1 (Case2 (WhenIRE (LiftE k)))
    DictTy    t    -> Case2 (Case0 (WhenIRE t))
    Pi        t    -> Case2 (Case1 (WhenIRE t))
    NewtypeTyCon t -> Case2 (Case2 (WhenIRE t))
  {-# INLINE fromE #-}
  toE = \case
    Case0 c -> case c of
      Case0 (LiftE b ) -> BaseType b
      Case1 (ListE ts) -> ProdType ts
      Case2 (ListE ts) -> SumType ts
      Case3 t -> RefType t
      _ -> error "impossible"
    Case1 c -> case c of
      Case0 t -> TabPi t
      Case1 t -> DepPairTy t
      Case2 (WhenIRE (LiftE k)) -> Kind k
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
    LiftE (SourceName, Maybe BuiltinClassName, [SourceName], [Maybe SourceName], [Explicitness])
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
    ClassName `PairE` LiftE [Explicitness] `PairE` Abs (Nest CBinder) (ListE CAtom `PairE` InstanceBody)
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
  type RepE DictType = EitherE2
   {- DictType -}     (LiftE SourceName `PairE` ClassName `PairE` ListE CAtom)
   {- IxDictType -}   CType
  fromE = \case
    DictType sourceName className params -> Case0 $ LiftE sourceName `PairE` className `PairE` ListE params
    IxDictType   ty -> Case1 ty
  toE = \case
    Case0 (LiftE sourceName `PairE` className `PairE` ListE params) -> DictType sourceName className params
    Case1 ty -> IxDictType   ty
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
  type RepE (DictCon r) = EitherE4
 {- InstanceDict -}      (WhenCore r (CType `PairE` PairE InstanceName (ListE CAtom)))
 {- IxFin -}             (WhenCore r CAtom)
 {- IxRawFin      -}     (Atom r)
 {- IxSpecialized -}     (WhenSimp r (SpecDictName `PairE` ListE SAtom))
  fromE = \case
    InstanceDict t v args -> Case0 $ WhenIRE $ t `PairE` PairE v (ListE args)
    IxFin x               -> Case1 $ WhenIRE $ x
    IxRawFin n            -> Case2 $ n
    IxSpecialized d xs    -> Case3 $ WhenIRE $ d `PairE` ListE xs
  toE = \case
    Case0 (WhenIRE (t `PairE` (PairE v (ListE args)))) -> InstanceDict t v args
    Case1 (WhenIRE x)                                  -> IxFin x
    Case2 n                                            -> IxRawFin n
    Case3 (WhenIRE (d `PairE` ListE xs))               -> IxSpecialized d xs
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
  type RepE CorePiType = LiftE (AppExplicitness, [Explicitness]) `PairE` Abs (Nest CBinder) (Type CoreIR)
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
  type RepE (PiType r) = Abs (Nest (Binder r)) (Type r)
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

instance IRRep r => GenericE (Effects r) where
  type RepE (Effects r) = EitherE UnitE UnitE
  fromE = \case
    Pure -> LeftE UnitE
    Effectful -> RightE UnitE
  {-# INLINE fromE #-}
  toE = \case
    LeftE UnitE -> Pure
    RightE UnitE -> Effectful
  {-# INLINE toE #-}

instance IRRep r => SinkableE      (Effects r)
instance IRRep r => HoistableE     (Effects r)
instance IRRep r => RenameE        (Effects r)
instance IRRep r => AlphaEqE       (Effects r)
instance IRRep r => AlphaHashableE (Effects r)

instance IRRep r => GenericE (EffTy r) where
  type RepE (EffTy r) = PairE (Effects r) (Type r)
  fromE (EffTy eff ty) = eff `PairE` ty
  {-# INLINE fromE #-}
  toE   (eff `PairE` ty) = EffTy eff ty
  {-# INLINE toE #-}

instance IRRep r => SinkableE      (EffTy r)
instance IRRep r => HoistableE     (EffTy r)
instance IRRep r => RenameE        (EffTy r)
instance IRRep r => AlphaEqE       (EffTy r)
instance IRRep r => AlphaHashableE (EffTy r)

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

instance IRRep r => BindsAtMostOneName (Decl r) (AtomNameC r) where
  Let b _ @> x = b @> x
  {-# INLINE (@>) #-}

instance IRRep r => BindsOneName (Decl r) (AtomNameC r) where
  binderName (Let b _) = binderName b
  {-# INLINE binderName #-}

instance Hashable IxMethod
instance Hashable BuiltinClassName
instance Hashable Kind

instance IRRep r => Store (TyCon r n)
instance IRRep r => Store (Con r n)
instance IRRep r => Store (RepVal r n)
instance IRRep r => Store (Type r n)
instance Store Kind
instance IRRep r => Store (Effects r n)
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
instance Store (ann n) => Store (NonDepNest r ann n l)
instance Store IxMethod
instance IRRep r => Store (Dict r n)
instance IRRep r => Store (TypedHof r n)
instance IRRep r => Store (Hof r n)
instance Store (NewtypeCon n)
instance Store (NewtypeTyCon n)
instance Store (DotMethods n)

-- === Pretty instances ===

instance IRRep r => Pretty (Hof r n) where pretty = prettyFromPrettyPrec
instance IRRep r => PrettyPrec (Hof r n) where
  prettyPrec hof = atPrec LowestPrec case hof of
    For _ _ lam -> "for" <+> pLowest lam
    While body    -> "while" <+> pArg body
    Linearize body x    -> "linearize" <+> pArg body <+> pArg x
    Transpose body x    -> "transpose" <+> pArg body <+> pArg x

instance IRRep r => Pretty (TyCon r n) where pretty = prettyFromPrettyPrec
instance IRRep r => PrettyPrec (TyCon r n) where
  prettyPrec con = case con of
    BaseType b   -> prettyPrec b
    ProdType []  -> atPrec ArgPrec $ "()"
    ProdType as  -> atPrec ArgPrec $ align $ group $
      encloseSep "(" ")" ", " $ fmap pApp as
    SumType  cs  -> atPrec ArgPrec $ align $ group $
      encloseSep "(|" "|)" " | " $ fmap pApp cs
    RefType a -> atPrec AppPrec $ "Ref" <+> p a
    Kind k    -> atPrec ArgPrec $ pretty $ show k
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
    Lam lam   -> atPrec LowestPrec $ p lam
    DepPair x y _ -> atPrec ArgPrec $ align $ group $
        parens $ p x <+> ",>" <+> p y
    DictConAtom d -> atPrec LowestPrec $ p d
    NewtypeCon con x -> prettyPrecNewtype con x
    TyConAtom ty -> prettyPrec ty
    where
      p :: Pretty a => a -> Doc ann
      p = pretty

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
    Case e alts _ -> prettyPrecCase "case" e alts
    TabCon _ es -> atPrec ArgPrec $ list $ pApp <$> es
    PrimOp _ op -> prettyPrec op
    ApplyMethod _ d i xs -> atPrec AppPrec $ "applyMethod" <+> p d <+> p i <+> p xs
    Project _ i x -> atPrec AppPrec $ "Project" <+> p i <+> p x
    Unwrap _  x -> atPrec AppPrec $ "Unwrap" <+> p x
    Hof (TypedHof _ hof) -> prettyPrec hof
    where
      p :: Pretty a => a -> Doc ann
      p = pretty

prettyPrecCase :: IRRep r => Doc ann -> Atom r n -> [Alt r n] -> DocPrec ann
prettyPrecCase name e alts = atPrec LowestPrec $
  name <+> pApp e <+> "of" <>
  nest 2 (foldMap (\alt -> hardline <> prettyAlt alt) alts)

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
  pretty (PiType bs resultTy) =
    (spaced $ unsafeFromNest $ bs) <+> "->" <+> pretty resultTy

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
    IxRawFin n -> "Ix (RawFin " <> pretty n <> ")"
    IxSpecialized d xs -> pretty d <+> pretty xs

instance Pretty (DictType n) where
  pretty = \case
    DictType classSourceName _ params -> pretty classSourceName <+> spaced params
    IxDictType ty -> "Ix" <+> pretty ty

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
    where
      p :: Pretty a => a -> Doc ann
      p = pretty

instance PrettyPrec (AtomVar r n) where
  prettyPrec (AtomVar v _) = prettyPrec v
instance Pretty (AtomVar r n) where pretty = prettyFromPrettyPrec

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
  pretty (CorePiType appExpl expls bs resultTy) =
    prettyBindersWithExpl expls bs <+> pretty appExpl <> pretty resultTy

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

instance IRRep r => Pretty (RepVal r n) where
  pretty (RepVal ty tree) = "<RepVal " <+> pretty tree <+> ":" <+> pretty ty <> ">"

prettyBlock :: (IRRep r, PrettyPrec (e l)) => Nest (Decl r) n l -> e l -> Doc ann
prettyBlock Empty expr = group $ line <> pLowest expr
prettyBlock decls expr = prettyLines decls' <> hardline <> pLowest expr
    where decls' = unsafeFromNest decls
