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
import PPrint

import Types.Primitives
import Types.Source (HasSourceName (..))
import Types.Imp

-- === core IR ===

data Atom (n::S) =
   Con   (Con n)
 | Stuck (Type n) (Stuck n)
   deriving (Show, Generic)

data Type (n::S) where
  TyCon   :: TyCon n -> Type n
  StuckTy :: Kind -> CStuck n  -> Type n

data Kind = DataKind | RefKind | TypeKind | FunKind | DictKind | OtherKind
     deriving (Show, Generic, Eq, Ord)

data Dict (n::S) where
  DictCon :: DictCon n -> Dict n
  StuckDict :: CType n -> CStuck n -> Dict n

data Con (n::S) where
  Lit     :: LitVal                                  -> Con n
  ProdCon :: [Atom n]                              -> Con n
  SumCon  :: [Type n] -> Int -> Atom n           -> Con n -- type, tag, payload
  DepPair :: Atom n -> Atom n -> DepPairType n -> Con n
  Lam        :: CoreLamExpr n                 -> Con n
  NewtypeCon :: NewtypeCon n -> Atom n -> Con n
  DictConAtom :: DictCon n             -> Con n
  TyConAtom   :: TyCon n               -> Con n

data Stuck (n::S) where
  Var               :: AtomVar n             -> Stuck n
  StuckProject      :: Int -> Stuck n        -> Stuck n
  StuckTabApp       :: Stuck n -> Atom n   -> Stuck n
  PtrVar            :: PtrType -> PtrName n    -> Stuck n
  RepValAtom        :: RepVal n              -> Stuck n
  StuckUnwrap       :: CStuck n                -> Stuck n
  InstantiatedGiven :: CStuck n -> [CAtom n]   -> Stuck n
  SuperclassProj    :: Int -> CStuck n         -> Stuck n

data TyCon (n::S) where
  BaseType :: BaseType             -> TyCon n
  ProdType :: [Type n]           -> TyCon n
  SumType  :: [Type n]           -> TyCon n
  RefType  :: Type n             -> TyCon n
  TabPi        :: TabPiType n    -> TyCon n
  DepPairTy    :: DepPairType n  -> TyCon n
  DictTy       :: DictType n       -> TyCon n
  Pi           :: CorePiType  n    -> TyCon n
  NewtypeTyCon :: NewtypeTyCon n   -> TyCon n
  Kind         :: Kind             -> TyCon n

data AtomVar (n::S) = AtomVar
  { atomVarName :: AtomName n
  , atomVarType :: Type n }
     deriving (Show, Generic)

deriving instance Show (DictCon  n)
deriving instance Show (Dict     n)
deriving instance Show (Con      n)
deriving instance Show (TyCon    n)
deriving instance Show (Type     n)
deriving instance Show (Stuck    n)

deriving via WrapE DictCon  n instance Generic (DictCon  n)
deriving via WrapE Dict     n instance Generic (Dict     n)
deriving via WrapE Con      n instance Generic (Con      n)
deriving via WrapE TyCon    n instance Generic (TyCon    n)
deriving via WrapE Type     n instance Generic (Type     n)
deriving via WrapE Stuck    n instance Generic (Stuck    n)

data Expr n where
 Block  :: EffTy n -> Block n -> Expr n
 TopApp :: EffTy n -> TopFunName n -> [SAtom n]         -> Expr n
 TabApp :: Type n -> Atom n -> Atom n                    -> Expr n
 Case   :: Atom n -> [Alt n] -> EffTy n                  -> Expr n
 Atom   :: Atom n                                            -> Expr n
 TabCon :: Type n -> [Atom n] -> Expr n
 PrimOp :: Type n -> PrimOp (Atom n)                     -> Expr n
 Hof    :: TypedHof n                                        -> Expr n
 Project     :: Type n -> Int -> Atom n                    -> Expr n
 App         :: EffTy n -> CAtom n -> [CAtom n]         -> Expr n
 Unwrap      :: CType n -> CAtom n                             -> Expr n
 ApplyMethod :: EffTy n -> CAtom n -> Int -> [CAtom n]  -> Expr n

deriving instance Show (Expr n)
deriving via WrapE Expr n instance Generic (Expr n)

data RepVal (n::S) = RepVal (Type n) (Tree (IExpr n))
     deriving (Show, Generic)

data DeclBinding n = DeclBinding LetAnn (Expr n)
     deriving (Show, Generic)
data Decl (n::S) (l::S) = Let (AtomNameBinder n l) (DeclBinding n)
     deriving (Show, Generic)
type Decls = Nest Decl

type AtomName       = Name
type AtomNameBinder = NameBinder

type ClassName    = Name
type TyConName    = Name
type DataConName  = Name
type InstanceName = Name
type MethodName   = Name
type ModuleName   = Name
type SpecDictName = Name
type TopFunName   = Name

type AtomBinderP = BinderP
type Binder = AtomBinderP Type :: B
type Alt = Abs Binder Expr :: E

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
data TyConParams n = TyConParams [Explicitness] [Atom n]
     deriving (Show, Generic)

type WithDecls = Abs Decls :: E -> E
type Block = WithDecls Expr :: E

data LamExpr (n::S) where
  LamExpr :: Nest Binder n l -> Expr l -> LamExpr n

data CoreLamExpr (n::S) = CoreLamExpr (CorePiType n) (LamExpr n) deriving (Show, Generic)

type TabLamExpr = PairE TabPiType (Abs SBinder CAtom)
type IxDict = Dict

data IxMethod = Size | Ordinal | UnsafeFromOrdinal
     deriving (Show, Generic, Enum, Bounded, Eq)

data IxType (n::S) =
  IxType { ixTypeType :: Type n
         , ixTypeDict :: IxDict n }
  deriving (Show, Generic)

data TabPiType (n::S) where
  TabPiType :: IxDict n -> Binder n l -> Type l -> TabPiType n

data PiType (n::S) where
  PiType :: Nest Binder n l -> Type l -> PiType n

data CorePiType (n::S) where
  CorePiType :: AppExplicitness -> [Explicitness] -> Nest CBinder n l -> CType l -> CorePiType n

data DepPairType (n::S) where
  DepPairType :: DepPairExplicitness -> Binder n l -> Type l -> DepPairType n

-- A nest where the annotation of a binder cannot depend on the binders
-- introduced before it. You can think of it as introducing a bunch of
-- names into the scope in parallel, but since safer names only reasons
-- about sequential scope extensions, we encode it differently.
data NonDepNest ann n l = NonDepNest (Nest AtomNameBinder n l) [ann n]
                            deriving (Generic)

-- === ToAtomAbs class ===

class ToBindersAbs (e::E) (body::E) | e -> body where
  toAbs :: e n -> Abs (Nest Binder) body n

instance ToBindersAbs CorePiType Type where
  toAbs (CorePiType _ _ bs ty) = Abs bs ty

instance ToBindersAbs CoreLamExpr Expr where
  toAbs (CoreLamExpr _ lam) = toAbs lam

instance ToBindersAbs (Abs (Nest Binder) body) body where
  toAbs = id

instance ToBindersAbs PiType Type where
  toAbs (PiType bs ty) = Abs bs ty

instance ToBindersAbs LamExpr Expr where
  toAbs (LamExpr bs body) = Abs bs body

instance ToBindersAbs TabPiType Type where
  toAbs (TabPiType _ b eltTy) = Abs (UnaryNest b) eltTy

instance ToBindersAbs DepPairType Type where
  toAbs (DepPairType _ b rhsTy) = Abs (UnaryNest b) rhsTy

instance ToBindersAbs InstanceDef (ListE CAtom `PairE` InstanceBody) where
  toAbs (InstanceDef _ _ bs params body) = Abs bs (ListE params `PairE` body)

instance ToBindersAbs TyConDef DataConDefs where
  toAbs (TyConDef _ _ bs body) = Abs bs body

instance ToBindersAbs ClassDef (Abs (Nest CBinder) (ListE CorePiType)) where
  toAbs (ClassDef _ _ _ _ _ bs scBs tys) = Abs bs (Abs scBs (ListE tys))

showStringBufferSize :: Word32
showStringBufferSize = 32

-- === Hofs ===

data TypedHof n = TypedHof (EffTy n) (Hof n)
     deriving (Show, Generic)

data Hof n =
   For       ForAnn (IxType n) (LamExpr n)
 | While     (Expr n)
 | Linearize (LamExpr n) (CAtom n)
 | Transpose (LamExpr n) (CAtom n)
 deriving (Show, Generic)

-- === IR variants ===

type CAtom  = Atom
type CType  = Type
type CDict  = Dict
type CStuck  = Stuck
type CBinder = Binder
type CExpr  = Expr
type CBlock = Block
type CDecl  = Decl
type CDecls = Decls
type CAtomName  = AtomName
type CAtomVar   = AtomVar

type SAtom  = Atom
type SType  = Type
type SDict  = Dict
type SStuck = Stuck
type SExpr  = Expr
type SBlock = Block
type SAlt   = Alt
type SDecl  = Decl
type SDecls = Decls
type SAtomName  = AtomName
type SAtomVar   = AtomVar
type SBinder = Binder
type SLam    = LamExpr

-- === newtypes ===

-- Describes how to lift the "shallow" representation type to the newtype.
data NewtypeCon (n::S) =
   UserADTData SourceName (TyConName n) (TyConParams n) -- source name is for the type
 | NatCon
 | FinCon (Atom n)
   deriving (Show, Generic)

data NewtypeTyCon (n::S) =
   Nat
 | Fin (Atom n)
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

data DictCon (n::S) where
 InstanceDict  :: CType n -> InstanceName n -> [CAtom n] -> DictCon n
 IxFin         :: CAtom n -> DictCon n
 -- IxRawFin is like `Fin`, but it's parameterized by a newtyped-stripped
 -- `IxRepVal` instead of `Nat`, and it describes indices of type `IxRepVal`.
 -- TODO: make is-only
 IxRawFin      :: Atom n -> DictCon n
 IxSpecialized :: SpecDictName n -> [SAtom n] -> DictCon n

data Effects (n::S) = Pure | Effectful
     deriving (Generic, Show)

instance Semigroup (Effects n) where
  Pure <> Pure = Pure
  _ <> _ = Effectful

instance Monoid (Effects n) where
  mempty = Pure

data EffTy (n::S) =
  EffTy { etEff :: Effects n
        , etTy  :: Type n }
     deriving (Generic, Show)

-- === Binder utils ===

binderType :: Binder n l -> Type n
binderType (_:>ty) = ty

binderVar  :: (DExt n l) => Binder n l -> AtomVar l
binderVar (b:>ty) = AtomVar (binderName b) (sink ty)

bindersVars :: (Distinct l, Ext n l) => Nest Binder n l -> [AtomVar l]
bindersVars = \case
  Empty -> []
  Nest b bs -> withExtEvidence b $ withSubscopeDistinct bs $
    sink (binderVar b) : bindersVars bs

-- === ToAtom ===

class ToAtom (e::E) where
  toAtom :: e n -> Atom n

instance ToAtom Atom where toAtom = id
instance ToAtom Con  where toAtom = Con
instance ToAtom (TyCon    ) where toAtom = Con . TyConAtom
instance ToAtom (DictCon  ) where toAtom = Con . DictConAtom
instance ToAtom CoreLamExpr  where toAtom = Con . Lam
instance ToAtom DictType     where toAtom = Con . TyConAtom . DictTy
instance ToAtom NewtypeTyCon where toAtom = Con . TyConAtom . NewtypeTyCon
instance ToAtom AtomVar where
  toAtom (AtomVar v ty) = Stuck ty (Var (AtomVar v ty))
instance ToAtom RepVal where
  toAtom (RepVal ty tree) = Stuck ty $ RepValAtom $ RepVal ty tree
instance ToAtom (Type) where
  toAtom = \case
    TyCon con -> Con $ TyConAtom con
    StuckTy k s -> Stuck (TyCon $ Kind k) s
instance ToAtom (Dict) where
  toAtom = \case
    DictCon d -> Con $ DictConAtom d
    StuckDict t s -> Stuck t s

-- This can help avoid ambiguous `r` parameter with ToAtom
toAtomR :: ToAtom e => e n -> Atom n
toAtomR = toAtom

-- === ToType ===

class ToType (e::E) where
  toType :: e n -> Type n

instance ToType Type        where toType = id
instance ToType TyCon       where toType = TyCon
instance ToType TabPiType   where toType = TyCon . TabPi
instance ToType DepPairType where toType = TyCon . DepPairTy
instance ToType CorePiType   where toType = TyCon . Pi
instance ToType DictType     where toType = TyCon . DictTy
instance ToType NewtypeTyCon where toType = TyCon . NewtypeTyCon

toMaybeType :: CAtom n -> Maybe (CType n)
toMaybeType = \case
  Stuck (TyCon (Kind k)) s -> Just $ StuckTy k s
  Con (TyConAtom t) -> Just $ TyCon t
  _ -> Nothing

-- === ToDict ===

class ToDict (e::E) where
  toDict :: e n -> Dict n

instance ToDict Dict       where toDict = id
instance ToDict DictCon    where toDict = DictCon
instance ToDict CAtomVar where
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
pattern IdxRepTy :: Type n
pattern IdxRepTy = TyCon (BaseType (Scalar Word32Type))

pattern IdxRepVal :: Word32 -> Atom n
pattern IdxRepVal x = Con (Lit (Word32Lit x))

pattern IIdxRepVal :: Word32 -> IExpr n
pattern IIdxRepVal x = ILit (Word32Lit x)

pattern IIdxRepTy :: IType
pattern IIdxRepTy = Scalar Word32Type

-- Type used to represent sum type tags at run-time
pattern TagRepTy :: Type n
pattern TagRepTy = TyCon (BaseType (Scalar Word8Type))

pattern TagRepVal :: Word8 -> Atom n
pattern TagRepVal x = Con (Lit (Word8Lit x))

pattern CharRepTy :: Type n
pattern CharRepTy = Word8Ty

charRepVal :: Char -> Atom n
charRepVal c = Con (Lit (Word8Lit (fromIntegral $ fromEnum c)))

pattern Word8Ty :: Type n
pattern Word8Ty = TyCon (BaseType (Scalar Word8Type))

pattern PairVal :: Atom n -> Atom n -> Atom n
pattern PairVal x y = Con (ProdCon [x, y])

pattern PairTy :: Type n -> Type n -> Type n
pattern PairTy x y = TyCon (ProdType [x, y])

pattern UnitVal :: Atom n
pattern UnitVal = Con (ProdCon [])

pattern UnitTy :: Type n
pattern UnitTy = TyCon (ProdType [])

pattern BaseTy :: BaseType -> Type n
pattern BaseTy b = TyCon (BaseType b)

pattern PtrTy :: PtrType -> Type n
pattern PtrTy ty = TyCon (BaseType (PtrType ty))

pattern RefTy :: Type n -> Type n
pattern RefTy a = TyCon (RefType a)

pattern TabTy :: IxDict n -> Binder n l -> Type l -> Type n
pattern TabTy d b body = TyCon (TabPi (TabPiType d b body))

pattern FinTy :: Atom n -> Type n
pattern FinTy n = TyCon (NewtypeTyCon (Fin n))

pattern NatTy :: Type n
pattern NatTy = TyCon (NewtypeTyCon Nat)

pattern NatVal :: Word32 -> Atom n
pattern NatVal n = Con (NewtypeCon NatCon (IdxRepVal n))

pattern FinConst :: Word32 -> Type n
pattern FinConst n = TyCon (NewtypeTyCon (Fin (NatVal n)))

pattern NullaryLamExpr :: Expr n -> LamExpr n
pattern NullaryLamExpr body = LamExpr Empty body

pattern UnaryLamExpr :: Binder n l -> Expr l -> LamExpr n
pattern UnaryLamExpr b body = LamExpr (UnaryNest b) body

pattern BinaryLamExpr :: Binder n l1 -> Binder l1 l2 -> Expr l2 -> LamExpr n
pattern BinaryLamExpr b1 b2 body = LamExpr (BinaryNest b1 b2) body

pattern MaybeTy :: Type n -> Type n
pattern MaybeTy a = TyCon (SumType [UnitTy, a])

pattern NothingAtom :: Type n -> Atom n
pattern NothingAtom a = Con (SumCon [UnitTy, a] 0 UnitVal)

pattern JustAtom :: Type n -> Atom n -> Atom n
pattern JustAtom a x = Con (SumCon [UnitTy, a] 1 x)

pattern BoolTy :: Type n
pattern BoolTy = Word8Ty

pattern FalseAtom :: Atom n
pattern FalseAtom = Con (Lit (Word8Lit 0))

pattern TrueAtom :: Atom n
pattern TrueAtom = Con (Lit (Word8Lit 1))

-- === Typeclass instances for Name and other Haskell libraries ===

instance GenericE RepVal where
  type RepE RepVal = PairE Type (ComposeE Tree IExpr)
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
    `PairE` EmptyAbs (Nest CBinder) `PairE` Type
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

instance GenericE TypedHof where
  type RepE TypedHof = EffTy `PairE` Hof
  fromE (TypedHof effTy hof) = effTy `PairE` hof
  {-# INLINE fromE #-}
  toE   (effTy `PairE` hof) = TypedHof effTy hof
  {-# INLINE toE #-}

instance SinkableE      TypedHof
instance HoistableE     TypedHof
instance RenameE        TypedHof
instance AlphaEqE       TypedHof
instance AlphaHashableE TypedHof

instance GenericE Hof where
  type RepE Hof = EitherE4
  {- For -}       (LiftE ForAnn `PairE` IxType `PairE` LamExpr)
  {- While -}     Expr
  {- Linearize -} (LamExpr `PairE` Atom)
  {- Transpose -} (LamExpr `PairE` Atom)

  fromE = \case
    For ann d body      -> Case0 (LiftE ann `PairE` d `PairE` body)
    While body          -> Case1 body
    Linearize body x    -> Case2 (PairE body x)
    Transpose body x    -> Case3 (PairE body x)
  {-# INLINE fromE #-}
  toE = \case
    Case0 (LiftE ann `PairE` d `PairE` body) -> For ann d body
    Case1 body                        -> While body
    Case2 (PairE body x) -> Linearize body x
    Case3 (PairE body x) -> Transpose body x
    _ -> error "impossible"
  {-# INLINE toE #-}

instance SinkableE Hof
instance HoistableE  Hof
instance RenameE     Hof
instance AlphaEqE Hof
instance AlphaHashableE Hof

instance GenericE Atom where
  type RepE Atom = EitherE (PairE Type Stuck) Con
  fromE = \case
    Stuck t x -> LeftE (PairE t x)
    Con x -> RightE x
  {-# INLINE fromE #-}
  toE = \case
    LeftE (PairE t x) -> Stuck t x
    RightE x -> Con x
  {-# INLINE toE #-}

instance SinkableE      Atom
instance HoistableE     Atom
instance AlphaEqE       Atom
instance AlphaHashableE Atom
instance RenameE        Atom

instance GenericE Stuck where
  type RepE Stuck = EitherE2
                         (EitherE6
 {-  Var     -}           AtomVar
 {-  StuckProject -}      (LiftE Int `PairE` Stuck)
 {-  StuckTabApp  -}      (Stuck `PairE` Atom)
 {-  StuckUnwrap  -}      (CStuck)
 {-  InstantiatedGiven -} (CStuck `PairE` ListE CAtom)
 {-  SuperclassProj    -} (LiftE Int `PairE` CStuck)
                        ) (EitherE2
 {-  PtrVar -}            (LiftE PtrType `PairE` PtrName)
 {-  RepValAtom -}        RepVal
                        )

  fromE = \case
    Var v                  -> Case0 $ Case0 v
    StuckProject i e       -> Case0 $ Case1 $ LiftE i `PairE` e
    StuckTabApp f x        -> Case0 $ Case2 $ f `PairE` x
    StuckUnwrap e          -> Case0 $ Case3 $ e
    InstantiatedGiven e xs -> Case0 $ Case4 $ e `PairE` ListE xs
    SuperclassProj i e     -> Case0 $ Case5 $ LiftE i `PairE` e
    PtrVar t p             -> Case1 $ Case0 $ LiftE t `PairE` p
    RepValAtom r           -> Case1 $ Case1 $ r
  {-# INLINE fromE #-}

  toE = \case
    Case0 con -> case con of
      Case0 v ->    Var v
      Case1 (LiftE i `PairE` e)  -> StuckProject i e
      Case2 (f `PairE` x)        -> StuckTabApp f x
      Case3 e                    -> StuckUnwrap e
      Case4 (e `PairE` ListE xs) -> InstantiatedGiven e xs
      Case5 (LiftE i `PairE` e)  -> SuperclassProj i e
      _ -> error "impossible"
    Case1 con -> case con of
      Case0 (LiftE t `PairE` p)  -> PtrVar t p
      Case1 r                    -> RepValAtom r
      _ -> error "impossible"
    _ -> error "impossible"
  {-# INLINE toE #-}

instance SinkableE      Stuck
instance HoistableE     Stuck
instance AlphaEqE       Stuck
instance AlphaHashableE Stuck
instance RenameE        Stuck

instance GenericE AtomVar where
  type RepE AtomVar = PairE AtomName Type
  fromE (AtomVar v t) = PairE v t
  {-# INLINE fromE #-}
  toE   (PairE v t) = AtomVar v t
  {-# INLINE toE #-}

instance HasNameHint (AtomVar n) where
  getNameHint (AtomVar v _) = getNameHint v

instance Eq (AtomVar n) where
  AtomVar v1 _ == AtomVar v2 _ = v1 == v2

instance SinkableE      AtomVar
instance HoistableE     AtomVar

-- We ignore the type annotation because it should be determined by the var
instance AlphaEqE AtomVar where
  alphaEqE (AtomVar v _) (AtomVar v' _) = alphaEqE v v'

-- We ignore the type annotation because it should be determined by the var
instance AlphaHashableE AtomVar where
  hashWithSaltE env salt (AtomVar v _) = hashWithSaltE env salt v

instance RenameE        AtomVar

instance GenericE Type where
  type RepE Type = EitherE (PairE (LiftE Kind) Stuck ) TyCon
  fromE = \case
    StuckTy k x -> LeftE (PairE (LiftE k) x)
    TyCon x -> RightE x
  {-# INLINE fromE #-}
  toE = \case
    LeftE (PairE (LiftE k) x) -> StuckTy k x
    RightE x -> TyCon x
  {-# INLINE toE #-}

instance SinkableE      Type
instance HoistableE     Type
instance AlphaEqE       Type
instance AlphaHashableE Type
instance RenameE        Type

instance GenericE Expr where
  type RepE Expr = EitherE2
    ( EitherE6
 {- App -}    (EffTy `PairE` Atom `PairE` ListE Atom)
 {- TabApp -} (Type `PairE` Atom `PairE` Atom)
 {- Case -}   (Atom `PairE` ListE Alt `PairE` EffTy)
 {- Atom -}   Atom
 {- TopApp -} (EffTy `PairE` TopFunName `PairE` ListE Atom)
 {- Block -}  (EffTy `PairE` Block)
    )
    ( EitherE6
 {- TabCon -}          (Type `PairE` ListE Atom)
 {- PrimOp -}          (Type `PairE` ComposeE PrimOp Atom)
 {- ApplyMethod -}     (EffTy `PairE` Atom `PairE` LiftE Int `PairE` ListE Atom)
 {- Project -}         (Type `PairE` LiftE Int `PairE` Atom)
 {- Unwrap -}          (CType `PairE` CAtom)
 {- Hof -}             TypedHof)
  fromE = \case
    App    et f xs        -> Case0 $ Case0 (et `PairE` f `PairE` ListE xs)
    TabApp  t f x         -> Case0 $ Case1 (t `PairE` f `PairE` x)
    Case e alts effTy  -> Case0 $ Case2 (e `PairE` ListE alts `PairE` effTy)
    Atom x             -> Case0 $ Case3 (x)
    TopApp et f xs     -> Case0 $ Case4 (et `PairE` f `PairE` ListE xs)
    Block et block     -> Case0 $ Case5 (et `PairE` block)
    TabCon ty xs          -> Case1 $ Case0 (ty `PairE` ListE xs)
    PrimOp ty op          -> Case1 $ Case1 (ty `PairE` ComposeE op)
    ApplyMethod et d i xs -> Case1 $ Case2 (et `PairE` d `PairE` LiftE i `PairE` ListE xs)
    Project ty i x        -> Case1 $ Case3 (ty `PairE` LiftE i `PairE` x)
    Unwrap t x            -> Case1 $ Case4 (t `PairE` x)
    Hof hof               -> Case1 $ Case5 hof
  {-# INLINE fromE #-}
  toE = \case
    Case0 case0 -> case case0 of
      Case0 (et `PairE` f `PairE` ListE xs)     -> App    et f xs
      Case1 (t `PairE` f `PairE` x)                       -> TabApp t f x
      Case2 (e `PairE` ListE alts `PairE` effTy)          -> Case e alts effTy
      Case3 (x)                                           -> Atom x
      Case4 (et `PairE` f `PairE` ListE xs)     -> TopApp et f xs
      Case5 (et `PairE` block)                            -> Block et block
      _ -> error "impossible"
    Case1 case1 -> case case1 of
      Case0 (ty `PairE` ListE xs) -> TabCon ty xs
      Case1 (ty `PairE`  ComposeE op) -> PrimOp ty op
      Case2 (et `PairE` d `PairE` LiftE i `PairE` ListE xs) -> ApplyMethod et d i xs
      Case3 (ty `PairE` LiftE i `PairE` x) -> Project ty i x
      Case4 (t `PairE` x) -> Unwrap t x
      Case5 hof -> Hof hof
      _ -> error "impossible"
    _ -> error "impossible"
  {-# INLINE toE #-}

instance SinkableE      Expr
instance HoistableE     Expr
instance AlphaEqE       Expr
instance AlphaHashableE Expr
instance RenameE        Expr

instance GenericE Con where
  type RepE Con = EitherE2
    (EitherE4
  {- Lit -}      (LiftE LitVal)
  {- ProdCon -}  (ListE Atom)
  {- SumCon -}   (ListE Type `PairE` LiftE Int `PairE` Atom)
  {- DepPair -}  (Atom `PairE` Atom `PairE` DepPairType)
    ) (EitherE4
  {- Lam -}         CoreLamExpr
  {- NewtypeCon -}  (NewtypeCon `PairE` CAtom)
  {- DictConAtom -} (DictCon)
  {- TyConAtom -}   TyCon)
  fromE = \case
    Lit l         -> Case0 $ Case0 $ LiftE l
    ProdCon xs    -> Case0 $ Case1 $ ListE xs
    SumCon ts i x -> Case0 $ Case2 $ ListE ts `PairE` LiftE i `PairE` x
    DepPair x y t -> Case0 $ Case3 $ x `PairE` y `PairE` t
    Lam lam          -> Case1 $ Case0 lam
    NewtypeCon con x -> Case1 $ Case1 $ con `PairE` x
    DictConAtom con  -> Case1 $ Case2 con
    TyConAtom tc     -> Case1 $ Case3 tc
  {-# INLINE fromE #-}
  toE = \case
    Case0 con -> case con of
      Case0 (LiftE l) -> Lit l
      Case1 (ListE xs) -> ProdCon xs
      Case2 (ListE ts `PairE` LiftE i `PairE` x) -> SumCon ts i x
      Case3 (x `PairE` y `PairE` t) -> DepPair x y t
      _ -> error "impossible"
    Case1 (con) -> case con of
      Case0 lam             -> Lam lam
      Case1 (con' `PairE` x) -> NewtypeCon con' x
      Case2 con'             -> DictConAtom con'
      Case3 tc              -> TyConAtom tc
      _ -> error "impossible"
    _ -> error "impossible"
  {-# INLINE toE #-}

instance SinkableE      Con
instance HoistableE     Con
instance AlphaEqE       Con
instance AlphaHashableE Con
instance RenameE        Con

instance GenericE TyCon where
  type RepE TyCon = EitherE3
                     (EitherE4
  {- BaseType -}        (LiftE BaseType)
  {- ProdType -}        (ListE Type)
  {- SumType -}         (ListE Type)
  {- RefType -}         Type)
                     (EitherE3
  {- TabPi -}         TabPiType
  {- DepPairTy -}     DepPairType
  {- Kind -}         (LiftE Kind))
                     (EitherE3
  {- DictTy -}        (DictType)
  {- Pi -}            (CorePiType)
  {- NewtypeTyCon -}  (NewtypeTyCon))
  fromE = \case
    BaseType b     -> Case0 (Case0 (LiftE b))
    ProdType ts    -> Case0 (Case1 (ListE ts))
    SumType  ts    -> Case0 (Case2 (ListE ts))
    RefType t      -> Case0 (Case3 t)
    TabPi t        -> Case1 (Case0 t)
    DepPairTy t    -> Case1 (Case1 t)
    Kind k         -> Case1 (Case2 (LiftE k))
    DictTy    t    -> Case2 (Case0 t)
    Pi        t    -> Case2 (Case1 t)
    NewtypeTyCon t -> Case2 (Case2 t)
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
      Case2 (LiftE k) -> Kind k
      _ -> error "impossible"
    Case2 c -> case c of
      Case0 t -> DictTy       t
      Case1 t -> Pi           t
      Case2 t -> NewtypeTyCon t
      _ -> error "impossible"
    _ -> error "impossible"
  {-# INLINE toE #-}

instance SinkableE      TyCon
instance HoistableE     TyCon
instance AlphaEqE       TyCon
instance AlphaHashableE TyCon
instance RenameE        TyCon

instance GenericB (NonDepNest ann) where
  type RepB (NonDepNest ann) = (LiftB (ListE ann)) `PairB` Nest AtomNameBinder
  fromB (NonDepNest bs anns) = LiftB (ListE anns) `PairB` bs
  {-# INLINE fromB #-}
  toB (LiftB (ListE anns) `PairB` bs) = NonDepNest bs anns
  {-# INLINE toB #-}
instance ProvesExt (NonDepNest ann)
instance BindsNames (NonDepNest ann)
instance (SinkableE  ann) => SinkableB  (NonDepNest ann)
instance (HoistableE ann) => HoistableB (NonDepNest ann)
instance (RenameE ann, SinkableE ann) => RenameB (NonDepNest ann)
instance (AlphaEqE       ann) => AlphaEqB       (NonDepNest ann)
instance (AlphaHashableE ann) => AlphaHashableB (NonDepNest ann)
deriving instance (Show (ann n)) => Show (NonDepNest ann n l)

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

instance GenericE Dict where
  type RepE Dict = EitherE (PairE Type Stuck) DictCon
  fromE = \case
    StuckDict t d -> LeftE (PairE t d)
    DictCon d -> RightE d
  {-# INLINE fromE #-}
  toE = \case
    LeftE (PairE t d) -> StuckDict t d
    RightE d -> DictCon d
  {-# INLINE toE #-}

instance SinkableE      Dict
instance HoistableE     Dict
instance AlphaEqE       Dict
instance AlphaHashableE Dict
instance RenameE        Dict

instance GenericE DictCon where
  type RepE DictCon = EitherE4
 {- InstanceDict -}      (CType `PairE` PairE InstanceName (ListE CAtom))
 {- IxFin -}             CAtom
 {- IxRawFin      -}     Atom
 {- IxSpecialized -}     (SpecDictName `PairE` ListE SAtom)
  fromE = \case
    InstanceDict t v args -> Case0 $ t `PairE` PairE v (ListE args)
    IxFin x               -> Case1 $ x
    IxRawFin n            -> Case2 $ n
    IxSpecialized d xs    -> Case3 $ d `PairE` ListE xs
  toE = \case
    Case0 (t `PairE` (PairE v (ListE args))) -> InstanceDict t v args
    Case1 x                                  -> IxFin x
    Case2 n                                  -> IxRawFin n
    Case3 (d `PairE` ListE xs)               -> IxSpecialized d xs
    _ -> error "impossible"

instance SinkableE      DictCon
instance HoistableE     DictCon
instance AlphaEqE       DictCon
instance AlphaHashableE DictCon
instance RenameE        DictCon

instance GenericE LamExpr where
  type RepE LamExpr = Abs (Nest Binder) Expr
  fromE (LamExpr b block) = Abs b block
  {-# INLINE fromE #-}
  toE   (Abs b block) = LamExpr b block
  {-# INLINE toE #-}

instance SinkableE      LamExpr
instance HoistableE     LamExpr
instance AlphaEqE       LamExpr
instance AlphaHashableE LamExpr
instance RenameE        LamExpr
deriving instance Show (LamExpr n)
deriving via WrapE LamExpr n instance Generic (LamExpr n)

instance GenericE CoreLamExpr where
  type RepE CoreLamExpr = CorePiType `PairE` LamExpr
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
  type RepE CorePiType = LiftE (AppExplicitness, [Explicitness]) `PairE` Abs (Nest CBinder) (Type)
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

instance GenericE IxType where
  type RepE IxType = PairE Type IxDict
  fromE (IxType ty d) = PairE ty d
  {-# INLINE fromE #-}
  toE   (PairE ty d) = IxType ty d
  {-# INLINE toE #-}

instance SinkableE   IxType
instance HoistableE  IxType
instance RenameE     IxType

instance AlphaEqE IxType where
  alphaEqE (IxType t1 _) (IxType t2 _) = alphaEqE t1 t2

instance AlphaHashableE IxType where
  hashWithSaltE env salt (IxType t _) = hashWithSaltE env salt t

instance GenericE TabPiType where
  type RepE TabPiType = PairE IxDict (Abs Binder Type)
  fromE (TabPiType d b resultTy) = PairE d (Abs b resultTy)
  {-# INLINE fromE #-}
  toE   (PairE d (Abs b resultTy)) = TabPiType d b resultTy
  {-# INLINE toE #-}

instance AlphaEqE TabPiType where
  alphaEqE (TabPiType _ b1 t1) (TabPiType _ b2 t2) =
    alphaEqE (Abs b1 t1) (Abs b2 t2)

instance AlphaHashableE TabPiType where
  hashWithSaltE env salt (TabPiType _ b t) = hashWithSaltE env salt $ Abs b t

instance HasNameHint (TabPiType n) where
  getNameHint (TabPiType _ b _) = getNameHint b

instance SinkableE      TabPiType
instance HoistableE     TabPiType
instance RenameE        TabPiType
deriving instance Show (TabPiType n)
deriving via WrapE TabPiType n instance Generic (TabPiType n)

instance GenericE PiType where
  type RepE PiType = Abs (Nest Binder) Type
  fromE (PiType bs effTy) = Abs bs effTy
  {-# INLINE fromE #-}
  toE   (Abs bs effTy) = PiType bs effTy
  {-# INLINE toE #-}

instance SinkableE      PiType
instance HoistableE     PiType
instance AlphaEqE       PiType
instance AlphaHashableE PiType
instance RenameE     PiType
deriving instance Show (PiType n)
deriving via WrapE PiType n instance Generic (PiType n)
instance Store (PiType n)

instance GenericE DepPairType where
  type RepE DepPairType = PairE (LiftE DepPairExplicitness) (Abs Binder Type)
  fromE (DepPairType expl b resultTy) = LiftE expl `PairE` Abs b resultTy
  {-# INLINE fromE #-}
  toE   (LiftE expl `PairE` Abs b resultTy) = DepPairType expl b resultTy
  {-# INLINE toE #-}

instance SinkableE      DepPairType
instance HoistableE     DepPairType
instance AlphaEqE       DepPairType
instance AlphaHashableE DepPairType
instance RenameE        DepPairType
deriving instance Show (DepPairType n)
deriving via WrapE DepPairType n instance Generic (DepPairType n)

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

instance GenericE Effects where
  type RepE Effects = EitherE UnitE UnitE
  fromE = \case
    Pure -> LeftE UnitE
    Effectful -> RightE UnitE
  {-# INLINE fromE #-}
  toE = \case
    LeftE UnitE -> Pure
    RightE UnitE -> Effectful
  {-# INLINE toE #-}

instance SinkableE      Effects
instance HoistableE     Effects
instance RenameE        Effects
instance AlphaEqE       Effects
instance AlphaHashableE Effects

instance GenericE EffTy where
  type RepE EffTy = PairE Effects Type
  fromE (EffTy eff ty) = eff `PairE` ty
  {-# INLINE fromE #-}
  toE   (eff `PairE` ty) = EffTy eff ty
  {-# INLINE toE #-}

instance SinkableE      EffTy
instance HoistableE     EffTy
instance RenameE        EffTy
instance AlphaEqE       EffTy
instance AlphaHashableE EffTy

instance GenericE DeclBinding where
  type RepE DeclBinding = LiftE LetAnn `PairE` Expr
  fromE (DeclBinding ann expr) = LiftE ann `PairE` expr
  {-# INLINE fromE #-}
  toE   (LiftE ann `PairE` expr) = DeclBinding ann expr
  {-# INLINE toE #-}

instance SinkableE      DeclBinding
instance HoistableE     DeclBinding
instance RenameE        DeclBinding
instance AlphaEqE       DeclBinding
instance AlphaHashableE DeclBinding

instance GenericB Decl where
  type RepB Decl = AtomBinderP DeclBinding
  fromB (Let b binding) = b :> binding
  {-# INLINE fromB #-}
  toB   (b :> binding) = Let b binding
  {-# INLINE toB #-}

instance SinkableB      Decl
instance HoistableB     Decl
instance RenameB        Decl
instance AlphaEqB       Decl
instance AlphaHashableB Decl
instance ProvesExt      Decl
instance BindsNames     Decl

instance BindsAtMostOneName Decl where
  Let b _ @> x = b @> x
  {-# INLINE (@>) #-}

instance BindsOneName Decl where
  binderName (Let b _) = binderName b
  {-# INLINE binderName #-}

instance Hashable IxMethod
instance Hashable BuiltinClassName
instance Hashable Kind

instance Store (TyCon n)
instance Store (Con n)
instance Store (RepVal n)
instance Store (Type n)
instance Store Kind
instance Store (Effects n)
instance Store (EffTy n)
instance Store (Stuck n)
instance Store (Atom n)
instance Store (AtomVar n)
instance Store (Expr n)
instance Store (DeclBinding n)
instance Store (Decl n l)
instance Store (TyConParams n)
instance Store (DataConDefs n)
instance Store (TyConDef n)
instance Store (DataConDef n)
instance Store (LamExpr n)
instance Store (IxType n)
instance Store (CorePiType n)
instance Store (CoreLamExpr n)
instance Store (TabPiType n)
instance Store (DepPairType  n)
instance Store BuiltinClassName
instance Store (ClassDef     n)
instance Store (InstanceDef  n)
instance Store (InstanceBody n)
instance Store (DictType n)
instance Store (DictCon n)
instance Store (ann n) => Store (NonDepNest ann n l)
instance Store IxMethod
instance Store (Dict n)
instance Store (TypedHof n)
instance Store (Hof n)
instance Store (NewtypeCon n)
instance Store (NewtypeTyCon n)
instance Store (DotMethods n)

-- === Pretty instances ===

instance Pretty (Hof n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (Hof n) where
  prettyPrec hof = atPrec LowestPrec case hof of
    For _ _ lam -> "for" <+> pLowest lam
    While body    -> "while" <+> pArg body
    Linearize body x    -> "linearize" <+> pArg body <+> pArg x
    Transpose body x    -> "transpose" <+> pArg body <+> pArg x

instance Pretty (TyCon n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (TyCon n) where
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

instance Pretty (Con n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (Con n) where
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

instance Pretty (Expr n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (Expr n) where
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

prettyPrecCase :: Doc ann -> Atom n -> [Alt n] -> DocPrec ann
prettyPrecCase name e alts = atPrec LowestPrec $
  name <+> pApp e <+> "of" <>
  nest 2 (foldMap (\alt -> hardline <> prettyAlt alt) alts)

prettyAlt :: Alt n -> Doc ann
prettyAlt (Abs b body) = prettyBinderNoAnn b <+> "->" <> nest 2 (pretty body)

prettyBinderNoAnn :: Binder n l -> Doc ann
prettyBinderNoAnn (b:>_) = pretty b

instance Pretty (DeclBinding n) where
  pretty (DeclBinding ann expr) = "Decl" <> pretty ann <+> pretty expr

instance Pretty (Decl n l) where
  pretty (Let b (DeclBinding ann rhs)) =
    align $ annDoc <> pretty b <+> "=" <> (nest 2 $ group $ line <> pLowest rhs)
    where annDoc = case ann of NoInlineLet -> pretty ann <> " "; _ -> pretty ann

instance Pretty (PiType n) where
  pretty (PiType bs resultTy) =
    (spaced $ unsafeFromNest $ bs) <+> "->" <+> pretty resultTy

instance Pretty (LamExpr n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (LamExpr n) where
  prettyPrec (LamExpr bs body) = atPrec LowestPrec $ prettyLam (pretty bs <> ".") body

instance Pretty (IxType n) where
  pretty (IxType ty dict) = parens $ "IxType" <+> pretty ty <> prettyIxDict dict

instance Pretty (Dict n) where
  pretty = \case
    DictCon con -> pretty con
    StuckDict _ stuck -> pretty stuck

instance Pretty (DictCon n) where
  pretty = \case
    InstanceDict _ name args -> "Instance" <+> pretty name <+> pretty args
    IxFin n -> "Ix (Fin" <+> pretty n <> ")"
    IxRawFin n -> "Ix (RawFin " <> pretty n <> ")"
    IxSpecialized d xs -> pretty d <+> pretty xs

instance Pretty (DictType n) where
  pretty = \case
    DictType classSourceName _ params -> pretty classSourceName <+> spaced params
    IxDictType ty -> "Ix" <+> pretty ty

instance Pretty (DepPairType n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (DepPairType n) where
  prettyPrec (DepPairType _ b rhs) =
    atPrec ArgPrec $ align $ group $ parensSep (spaceIfColinear <> "&> ") [pretty b, pretty rhs]

instance Pretty (CoreLamExpr n) where
  pretty (CoreLamExpr _ lam) = pretty lam

instance Pretty (Atom n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (Atom n) where
  prettyPrec atom = case atom of
    Con e -> prettyPrec e
    Stuck _ e -> prettyPrec e

instance Pretty (Type n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (Type n) where
  prettyPrec = \case
    TyCon  e -> prettyPrec e
    StuckTy _ e -> prettyPrec e

instance Pretty (Stuck n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (Stuck n) where
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

instance PrettyPrec (AtomVar n) where
  prettyPrec (AtomVar v _) = prettyPrec v
instance Pretty (AtomVar n) where pretty = prettyFromPrettyPrec

prettyLam :: Pretty a => Doc ann -> a -> Doc ann
prettyLam binders body = group $ group (nest 4 $ binders) <> group (nest 2 $ pretty body)

instance Pretty (TabPiType n) where
  pretty (TabPiType dict (b:>ty) body) = let
    prettyBody = case body of
      TyCon (Pi subpi) -> pretty subpi
      _ -> pLowest body
    prettyBinder = prettyBinderHelper (b:>ty) body
    in prettyBinder <> prettyIxDict dict <> (group $ line <> "=>" <+> prettyBody)

-- A helper to let us turn dict printing on and off.  We mostly want it off to
-- reduce clutter in prints and error messages, but when debugging synthesis we
-- want it on.
prettyIxDict :: IxDict n -> Doc ann
prettyIxDict dict = if False then " " <> pretty dict else mempty

prettyBinderHelper :: HoistableE e => Binder n l -> e l -> Doc ann
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

instance Pretty (RepVal n) where
  pretty (RepVal ty tree) = "<RepVal " <+> pretty tree <+> ":" <+> pretty ty <> ">"

prettyBlock :: PrettyPrec (e l) => Nest Decl n l -> e l -> Doc ann
prettyBlock Empty expr = group $ line <> pLowest expr
prettyBlock decls expr = prettyLines decls' <> hardline <> pLowest expr
    where decls' = unsafeFromNest decls
