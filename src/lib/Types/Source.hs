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

module Types.Source where

import Data.Hashable
import Data.Foldable
import qualified Data.Map.Strict       as M
import qualified Data.Set              as S
import Data.String (IsString, fromString)
import Data.Text (Text)
import Data.Text.Prettyprint.Doc (Pretty (..), hardline, (<+>))
import Data.Word

import GHC.Generics (Generic (..))
import Data.Store (Store (..))

import Name
import IRVariants
import Err
import LabeledItems
import Util (File (..))

import Types.Primitives

data SourceNameOr (a::E) (n::S) where
  -- Only appears before renaming pass
  SourceName :: SourceName -> SourceNameOr a n
  -- Only appears after renaming pass
  -- We maintain the source name for user-facing error messages.
  InternalName :: SourceName -> a n -> SourceNameOr a n
deriving instance Eq (a n) => Eq (SourceNameOr (a::E) (n::S))
deriving instance Ord (a n) => Ord (SourceNameOr a n)
deriving instance Show (a n) => Show (SourceNameOr a n)

newtype SourceOrInternalName (c::C) (n::S) = SourceOrInternalName (SourceNameOr (Name c) n)
  deriving (Eq, Ord, Show)

pattern SISourceName :: (n ~ VoidS) => SourceName -> SourceOrInternalName c n
pattern SISourceName n = SourceOrInternalName (SourceName n)

pattern SIInternalName :: SourceName -> Name c n -> SourceOrInternalName c n
pattern SIInternalName n a = SourceOrInternalName (InternalName n a)

-- === Concrete syntax ===
-- The grouping-level syntax of the source language

-- optional arrow, effects, result type
type ExplicitParams = [Group]
type GivenClause = ([Group], Maybe [Group])

type CTopDecl = WithSrc CTopDecl'
data CTopDecl'
  = CSDecl LetAnn CSDecl'
  | CData
      SourceName      -- Type constructor name
      ExplicitParams
      [(SourceName, ExplicitParams)]   -- Constructor names and argument sets
  | CStruct
      SourceName      -- Type constructor name
      ExplicitParams
      [(SourceName, Group)] -- Field names and types
  | CInterface
      SourceName  -- Interface name
      ExplicitParams
      [(SourceName, Group)]  -- Method declarations
  | CEffectDecl SourceName [(SourceName, UResumePolicy, Group)]
  | CHandlerDecl SourceName -- Handler name
      SourceName -- Effect name
      SourceName -- Body type parameter
      Group -- Handler arguments
      Group -- Handler type annotation
      [(SourceName, Maybe UResumePolicy, CSBlock)] -- Handler methods
  deriving (Show, Generic)

type CSDecl = WithSrc CSDecl'
data CSDecl'
  = CLet Group CSBlock
  -- Arrow binder <-
  | CBind Group CSBlock
  | CDefDecl CDef
  -- header, givens (may be empty), methods, optional name.  The header should contain
  -- the prerequisites, class name, and class arguments.
  | CInstanceDecl CInstanceDef
  | CDerivingDecl CDerivingDef
  | CExpr Group
  | CPass
    deriving (Show, Generic)

type CEffs = ([Group], Maybe Group)
data CDef = CDef
  SourceName
  (ExplicitParams)
  (Maybe CDefRhs)
  (Maybe GivenClause)
  CSBlock
  deriving (Show, Generic)

type CDefRhs = (AppExplicitness, Maybe CEffs, Group)

data CInstanceDef = CInstanceDef
  SourceName         -- interface name
  [Group]            -- args at which we're instantiating the interface
  (Maybe GivenClause)
  CSBlock            -- Method definitions
  (Maybe (SourceName, Maybe [Group])) -- Optional name of instance, with explicit parameters
  deriving (Show, Generic)

data CDerivingDef = CDerivingDef
  SourceName         -- interface name
  [Group]            -- args at which we're instantiating the interface
  (Maybe GivenClause)
  deriving (Show, Generic)

type Group = WithSrc Group'
data Group'
  = CEmpty
  | CIdentifier SourceName
  | CPrim PrimName [Group]
  | CNat Word64
  | CInt Int
  | CString String
  | CChar Char
  | CFloat Double
  | CHole
  | CLabel LabelPrefix String
  | CParens   [Group]
  | CBrackets [Group]
  | CBraces   [Group]
  | CBin Bin Group Group
  | CPrefix SourceName Group -- covers unary - and unary + among others
  | CPostfix SourceName Group
  | CLambda [Group] CSBlock
  | CFor ForKind [Group] CSBlock -- also for_, rof, rof_
  | CCase Group [(Group, CSBlock)] -- scrutinee, alternatives
  | CIf Group CSBlock (Maybe CSBlock)
  | CDo CSBlock
  | CGivens GivenClause
  | CArrow Group (Maybe CEffs) Group
    deriving (Show, Generic)

type Bin = WithSrc Bin'
data Bin'
  = JuxtaposeWithSpace
  | JuxtaposeNoSpace
  | EvalBinOp String
  | DepAmpersand
  | Dot
  | DepComma
  | Colon
  | DoubleColon
  | Dollar
  | ImplicitArrow -- ->>
  | FatArrow      -- =>
  | Pipe
  | CSEqual
  deriving (Eq, Ord, Show, Generic)

data LabelPrefix = PlainLabel
  deriving (Show, Generic)

data ForKind
  = KFor
  | KFor_
  | KRof
  | KRof_
  deriving (Show, Generic)

-- `CSBlock` instead of `CBlock` because the latter is an alias for `Block CoreIR`.
data CSBlock = CSBlock [CSDecl] -- last decl should be a CExpr
  deriving (Show, Generic)

-- === Untyped IR ===
-- The AST of Dex surface language.

data UEffect (n::S) =
   URWSEffect RWS (SourceOrInternalName (AtomNameC CoreIR) n)
 | UExceptionEffect
 | UIOEffect
 | UUserEffect (SourceOrInternalName EffectNameC n)
 | UInitEffect

data UEffectRow (n::S) =
  UEffectRow (S.Set (UEffect n)) (Maybe (SourceOrInternalName (AtomNameC CoreIR) n))
  deriving (Generic)

pattern UPure :: UEffectRow n
pattern UPure <- ((\(UEffectRow effs t) -> (S.null effs, t)) -> (True, Nothing))
  where UPure = UEffectRow mempty Nothing

data UVar (n::S) =
   UAtomVar     (Name (AtomNameC CoreIR) n)
 | UTyConVar    (Name TyConNameC    n)
 | UDataConVar  (Name DataConNameC  n)
 | UClassVar    (Name ClassNameC    n)
 | UEffectVar   (Name EffectNameC   n)
 | UMethodVar   (Name MethodNameC   n)
 | UEffectOpVar (Name EffectOpNameC n)
 | UHandlerVar  (Name HandlerNameC  n)
   deriving (Eq, Ord, Show, Generic)

type UAtomBinder = UBinder (AtomNameC CoreIR)
data UBinder (c::C) (n::S) (l::S) where
  -- Only appears before renaming pass
  UBindSource :: SourceName -> UBinder c n n
  -- May appear before or after renaming pass
  UIgnore :: UBinder c n n
  -- The following binders only appear after the renaming pass.
  -- We maintain the source name for user-facing error messages
  -- and named arguments.
  UBind :: SourceName -> NameBinder c n l -> UBinder c n l

type UExpr = WithSrcE UExpr'
data UExpr' (n::S) =
   UVar (SourceNameOr UVar n)
 | ULam (ULamExpr n)
 | UPi  (UPiExpr n)
 | UApp (UExpr n) [UExpr n] [UNamedArg n]
 | UTabPi  (UTabPiExpr n)
 | UDepPairTy (UDepPairType n)
 | UDepPair (UExpr n) (UExpr n)
 | UTabApp (UExpr n) [UExpr n]
 | UDecl (UDeclExpr n)
 | UFor Direction (UForExpr n)
 | UCase (UExpr n) [UAlt n]
 | UHole
 | UTypeAnn (UExpr n) (UExpr n)
 | UTabCon [UExpr n]
 | UPrim PrimName [UExpr n]
 | ULabel String
 | UFieldAccess (UExpr n) FieldName
 | URecord (UFieldRowElems n)                        -- {@v=x, a=y, b=z, ...rest}
 | ULabeledRow (UFieldRowElems n)                    -- {@v:X ? a:Y ? b:Z ? ...rest}
 | URecordTy (UFieldRowElems n)                      -- {@v:X & a:Y & b:Z & ...rest}
 | UNatLit   Word64
 | UIntLit   Int
 | UFloatLit Double
   deriving (Show, Generic)

type UNamedArg (n::S) = (SourceName, UExpr n)
type UFieldRowElems (n::S) = [UFieldRowElem n]
data UFieldRowElem (n::S)
  = UStaticField String                (UExpr n)
  | UDynField    (SourceNameOr UVar n) (UExpr n)
  | UDynFields   (UExpr n)
  deriving (Show)

type FieldName = WithSrc String

data ULamExpr (n::S) where
  ULamExpr
    :: Nest (WithExpl UOptAnnBinder) n l  -- args
    -> AppExplicitness
    -> Maybe (UEffectRow l)               -- optional effect
    -> Maybe (UType l)                    -- optional result type
    -> UExpr l                            -- body
    -> ULamExpr n

data UPiExpr (n::S) where
  UPiExpr :: Nest (WithExpl UOptAnnBinder) n l -> AppExplicitness -> UEffectRow l -> UType l -> UPiExpr n

data UTabPiExpr (n::S) where
  UTabPiExpr :: UOptAnnBinder n l -> UType l -> UTabPiExpr n

data UDepPairType (n::S) where
  UDepPairType :: UOptAnnBinder n l -> UType l -> UDepPairType n

data UDeclExpr (n::S) where
  UDeclExpr :: UDecl n l -> UExpr l -> UDeclExpr n

type UConDef (n::S) (l::S) = (SourceName, Nest UReqAnnBinder n l)

data UDataDef (n::S) where
  UDataDef
    :: SourceName  -- source name for pretty printing
    -> Nest (WithExpl UOptAnnBinder) n l
    -> [(SourceName, UDataDefTrail l)] -- data constructor types
    -> UDataDef n

data UStructDef (n::S) where
  UStructDef
    :: SourceName    -- source name for pretty printing
    -> Nest (WithExpl UOptAnnBinder) n l
    -> [(SourceName, UType l)]  -- named payloads
    -> UStructDef n

data UDataDefTrail (l::S) where
  UDataDefTrail :: Nest UReqAnnBinder l l' -> UDataDefTrail l

data UDecl (n::S) (l::S) where
  ULet :: LetAnn -> UPat n l -> Maybe (UType n) -> UExpr n -> UDecl n l
  UDataDefDecl
    :: UDataDef n                          -- actual definition
    -> UBinder TyConNameC n l'             -- type constructor name
    ->   Nest (UBinder DataConNameC) l' l  -- data constructor names
    -> UDecl n l
  UStructDecl
    :: UStructDef n                        -- actual definition
    -> UBinder TyConNameC n l              -- type constructor name
    -> UDecl n l
  UInterface
    :: Nest (WithExpl UOptAnnBinder) n p   -- parameter binders
    ->   [UType p]                         -- method types
    -> UBinder ClassNameC n l'             -- class name
    ->   Nest (UBinder MethodNameC) l' l   -- method names
    -> UDecl n l
  UInstance
    :: SourceNameOr (Name ClassNameC) n  -- class name
    -> Nest (WithExpl UOptAnnBinder) n l'
    ->   [UExpr l']                      -- class parameters
    ->   [UMethodDef l']                 -- method definitions
    -- Maybe we should make a separate color (namespace) for instance names?
    -> MaybeB UAtomBinder n l    -- optional instance name
    -> AppExplicitness           -- explicitness (only relevant for named instances)
    -> UDecl n l
  UDerivingInstance
    :: SourceNameOr (Name ClassNameC) n    -- class name
    -> Nest (WithExpl UOptAnnBinder) n l'  -- givens
    ->   [UExpr l']                        -- class parameters
    -- Note that no new symbols are brough into scope by a deriving instance
    -- declaration. Hence the double occurrence of `n` in `UDecl n n`.
    -> UDecl n n
  UEffectDecl
    :: [UEffectOpType n]                  -- operation types
    -> UBinder EffectNameC n l'           -- effect name
    -> Nest (UBinder EffectOpNameC) l' l  -- operation names
    -> UDecl n l
  UHandlerDecl
    :: SourceNameOr (Name EffectNameC) n  -- effect name
    -> UAtomBinder n b                    -- body type argument
    -> Nest (WithExpl UOptAnnBinder) b l' -- type args
    ->   UEffectRow l'                    -- returning effect
    ->   UType l'                         -- returning type
    ->   [UEffectOpDef l']                -- operation definitions
    -> UBinder HandlerNameC n l           -- handler name
    -> UDecl n l
  UPass :: UDecl n n

type UType = UExpr
type UConstraint = UExpr

data UEffectOpType (n::S) where
  UEffectOpType :: UResumePolicy -> UType s -> UEffectOpType s
  deriving (Show, Generic)

data UResumePolicy =
    UNoResume
  | ULinearResume
  | UAnyResume
  deriving (Show, Eq, Generic)

instance Hashable UResumePolicy
instance Store UResumePolicy

data UForExpr (n::S) where
  UForExpr :: UOptAnnBinder n l -> UExpr l -> UForExpr n

type UMethodDef = WithSrcE UMethodDef'
data UMethodDef' (n::S) = UMethodDef (SourceNameOr (Name MethodNameC) n) (ULamExpr n)
  deriving (Show, Generic)

data UEffectOpDef (n::S) =
    UEffectOpDef UResumePolicy (SourceNameOr (Name EffectOpNameC) n) (UExpr n)
  | UReturnOpDef (UExpr n)
  deriving (Show, Generic)

data AnnRequirement = AnnRequired | AnnOptional

data UAnn (annReq::AnnRequirement) (n::S) where
  UAnn   :: UType n -> UAnn annReq      n
  UNoAnn ::            UAnn AnnOptional n
deriving instance Show (UAnn annReq n)


data UAnnBinder (annReq::AnnRequirement) (n::S) (l::S) =
  UAnnBinder (UAtomBinder n l) (UAnn annReq n) [UConstraint n]
  deriving (Show, Generic)

type UReqAnnBinder = UAnnBinder AnnRequired :: B
type UOptAnnBinder = UAnnBinder AnnOptional :: B

data UAlt (n::S) where
  UAlt :: UPat n l -> UExpr l -> UAlt n

data UFieldRowPat (n::S) (l::S) where
  UEmptyRowPat    :: UFieldRowPat n n
  URemFieldsPat   :: UAtomBinder n l -> UFieldRowPat n l
  UStaticFieldPat :: Label               -> UPat n l' -> UFieldRowPat l' l -> UFieldRowPat n l
  UDynFieldsPat   :: SourceNameOr UVar n -> UPat n l' -> UFieldRowPat l' l -> UFieldRowPat n l
  UDynFieldPat    :: SourceNameOr UVar n -> UPat n l' -> UFieldRowPat l' l -> UFieldRowPat n l

instance Show (UFieldRowPat n l) where
  show _ = "UFieldRowPat <TODO>"

type UPat = WithSrcB UPat'
data UPat' (n::S) (l::S) =
   UPatBinder (UAtomBinder n l)
 | UPatCon (SourceNameOr (Name DataConNameC) n) (Nest UPat n l)
 | UPatProd (Nest UPat n l)
 | UPatDepPair (PairB UPat UPat n l)
 -- The name+ExtLabeledItems and the PairBs are parallel, constrained by the parser.
 | UPatRecord (UFieldRowPat n l)
 | UPatTable (Nest UPat n l)
  deriving (Show)

pattern UPatIgnore :: UPat' (n::S) n
pattern UPatIgnore = UPatBinder UIgnore

-- === Source context helpers ===

data WithSrc a = WithSrc SrcPosCtx a
  deriving (Show, Functor)

data WithSrcE (a::E) (n::S) = WithSrcE SrcPosCtx (a n)
  deriving (Show)

data WithSrcB (binder::B) (n::S) (l::S) = WithSrcB SrcPosCtx (binder n l)
  deriving (Show)

class HasSrcPos a where
  srcPos :: a -> SrcPosCtx

instance HasSrcPos (WithSrcE (a::E) (n::S)) where
  srcPos (WithSrcE pos _) = pos

instance HasSrcPos (WithSrcB (b::B) (n::S) (n::S)) where
  srcPos (WithSrcB pos _) = pos

-- === SourceMap ===

data SourceNameDef n =
    LocalVar  (UVar n)                          -- bound within a decl or expression
    -- the Nothing case is for vars whose definitions have errors
  | ModuleVar ModuleSourceName (Maybe (UVar n)) -- bound at the module level
    deriving (Show, Generic)

data SourceMap (n::S) = SourceMap
  {fromSourceMap :: M.Map SourceName [SourceNameDef n]}
  deriving Show

-- === Source modules ===

data ModuleSourceName = Prelude | Main | OrdinaryModule SourceName
     deriving (Show, Eq, Ord, Generic)

-- Parsed just enough to know the dependencies.
data UModulePartialParse = UModulePartialParse
  { umppName          :: ModuleSourceName
  , umppDirectImports :: [ModuleSourceName]
  , umppSource        :: File }
  deriving (Show, Generic)

data UModule = UModule
  { uModuleName          :: ModuleSourceName
  , uModuleDirectImports :: [ModuleSourceName]
  , uModuleSourceBlocks  :: [SourceBlock] }
  deriving (Show, Generic)

-- === top-level blocks ===

data SourceBlock = SourceBlock
  { sbLine     :: Int
  , sbOffset   :: Int
  , sbLogLevel :: LogLevel
  , sbText     :: Text
  , sbContents :: SourceBlock' }
  deriving (Show, Generic)

type ReachedEOF = Bool

data SymbolicZeros = SymbolicZeros | InstantiateZeros
                     deriving (Generic, Eq, Show)

data SourceBlock'
  = TopDecl CTopDecl
  | Command CmdName CSBlock
  | DeclareForeign SourceName SourceName Group
  | DeclareCustomLinearization SourceName SymbolicZeros Group
  | Misc SourceBlockMisc
  | UnParseable ReachedEOF String
  deriving (Show, Generic)

data SourceBlockMisc
  = GetNameType SourceName
  | ImportModule ModuleSourceName
  | QueryEnv EnvQuery
  | ProseBlock Text
  | CommentLine
  | EmptyLines
  deriving (Show, Generic)

data CmdName = GetType | EvalExpr OutFormat | ExportFun String
               deriving  (Show, Generic)

data LogLevel = LogNothing | PrintEvalTime | PrintBench String
              | LogPasses [PassName] | LogAll
                deriving  (Show, Generic)

data PrintBackend =
   PrintCodegen  -- Soon-to-be default path based on `PrintAny`
 | PrintHaskell  -- Backup path for debugging in case the codegen path breaks.
                 -- Uses PPrint.hs directly and doesn't make any attempt to
                 -- hide internals: SumAsProd, TabLam, AtomRepVal, etc
                 -- are printed as they are. Also accessible via `:pp`.

 deriving (Show, Eq, Generic)

data OutFormat = Printed (Maybe PrintBackend) | RenderHtml  deriving (Show, Eq, Generic)

data PassName = Parse | RenamePass | TypePass | SynthPass | SimpPass | ImpPass | JitPass
              | LLVMOpt | AsmPass | JAXPass | JAXSimpPass | LLVMEval | LowerOptPass | LowerPass
              | ResultPass | JaxprAndHLO | EarlyOptPass | OptPass | VectPass | OccAnalysisPass
              | InlinePass
                deriving (Ord, Eq, Bounded, Enum, Generic)

instance Show PassName where
  show p = case p of
    Parse    -> "parse" ; RenamePass -> "rename";
    TypePass -> "typed"   ; SynthPass -> "synth"
    SimpPass -> "simp"  ; ImpPass  -> "imp"     ; JitPass   -> "llvm"
    LLVMOpt  -> "llvmopt" ; AsmPass   -> "asm"
    JAXPass  -> "jax"   ; JAXSimpPass -> "jsimp"; ResultPass -> "result"
    LLVMEval -> "llvmeval" ; JaxprAndHLO -> "jaxprhlo";
    LowerOptPass -> "lower-opt"; LowerPass -> "lower"
    EarlyOptPass -> "early-opt"; OptPass -> "opt"; OccAnalysisPass -> "occ-analysis"
    VectPass -> "vect"; InlinePass -> "inline"

data EnvQuery =
   DumpSubst
 | InternalNameInfo RawName
 | SourceNameInfo   SourceName
   deriving (Show, Generic)

-- === Primitive names ===

data PrimName =
    UPrimTC  (PrimTC CoreIR ())
  | UPrimCon (PrimCon CoreIR ())
  | UPrimOp  (PrimOp ())
  | URecordOp (RecordOp ())
  | UMAsk | UMExtend | UMGet | UMPut
  | UWhile | ULinearize | UTranspose
  | URunReader | URunWriter | URunState | URunIO | UCatchException
  | UProjNewtype | UExplicitApply | UMonoLiteral
  | UIndexRef | UProjRef Int | UApplyMethod Int
  | UNat | UNatCon | UFin | ULabelType
  | UEffectRowKind | ULabeledRowKind
  | UTuple -- overloaded for type constructor and data constructor, resolved in inference
    deriving (Show, Eq)

-- === instances ===

instance Semigroup (SourceMap n) where
  m1 <> m2 = SourceMap $ M.unionWith (++) (fromSourceMap m2) (fromSourceMap m1)

instance Monoid (SourceMap n) where
  mempty = SourceMap mempty

instance GenericE SourceNameDef where
  type RepE SourceNameDef = EitherE UVar (LiftE ModuleSourceName `PairE` MaybeE UVar)
  fromE (LocalVar v) = LeftE v
  fromE (ModuleVar name maybeUVar) = RightE (PairE (LiftE name) (toMaybeE maybeUVar))
  {-# INLINE fromE #-}
  toE (LeftE v) = LocalVar v
  toE (RightE (PairE (LiftE name) maybeUVar)) = ModuleVar name (fromMaybeE maybeUVar)
  {-# INLINE toE #-}

instance SinkableE      SourceNameDef
instance HoistableE     SourceNameDef
instance AlphaEqE       SourceNameDef
instance AlphaHashableE SourceNameDef
instance RenameE        SourceNameDef

instance GenericE SourceMap where
  type RepE SourceMap = ListE (PairE (LiftE SourceName) (ListE SourceNameDef))
  fromE (SourceMap m) = ListE [PairE (LiftE v) (ListE defs) | (v, defs) <- M.toList m]
  {-# INLINE fromE #-}
  toE   (ListE pairs) = SourceMap $ M.fromList [(v, defs) | (PairE (LiftE v) (ListE defs)) <- pairs]
  {-# INLINE toE #-}

deriving via WrapE SourceMap n instance Generic (SourceMap n)

instance SinkableE      SourceMap
instance HoistableE     SourceMap
instance AlphaEqE       SourceMap
instance AlphaHashableE SourceMap
instance RenameE        SourceMap

instance Pretty (SourceNameDef n) where
  pretty def = case def of
    LocalVar v -> pretty v
    ModuleVar _ Nothing -> "<error in definition>"
    ModuleVar mname (Just v) -> pretty v <> " defined in " <> pretty mname

instance Pretty ModuleSourceName where
  pretty Main = "main"
  pretty Prelude = "prelude"
  pretty (OrdinaryModule s) = pretty s

instance Pretty (SourceMap n) where
  pretty (SourceMap m) =
    fold [pretty v <+> "@>" <+> pretty x <> hardline | (v, x) <- M.toList m ]

instance GenericE UVar where
  type RepE UVar = EitherE8 (Name (AtomNameC CoreIR)) (Name TyConNameC)
                            (Name DataConNameC)  (Name ClassNameC)
                            (Name MethodNameC)   (Name EffectNameC)
                            (Name EffectOpNameC) (Name HandlerNameC)
  fromE name = case name of
    UAtomVar     v -> Case0 v
    UTyConVar    v -> Case1 v
    UDataConVar  v -> Case2 v
    UClassVar    v -> Case3 v
    UMethodVar   v -> Case4 v
    UEffectVar   v -> Case5 v
    UEffectOpVar v -> Case6 v
    UHandlerVar  v -> Case7 v
  {-# INLINE fromE #-}

  toE name = case name of
    Case0 v -> UAtomVar     v
    Case1 v -> UTyConVar    v
    Case2 v -> UDataConVar  v
    Case3 v -> UClassVar    v
    Case4 v -> UMethodVar   v
    Case5 v -> UEffectVar   v
    Case6 v -> UEffectOpVar v
    Case7 v -> UHandlerVar  v
  {-# INLINE toE #-}

instance Pretty (UVar n) where
  pretty name = case name of
    UAtomVar     v -> "Atom name: " <> pretty v
    UTyConVar    v -> "Type constructor name: " <> pretty v
    UDataConVar  v -> "Data constructor name: " <> pretty v
    UClassVar    v -> "Class name: " <> pretty v
    UMethodVar   v -> "Method name: " <> pretty v
    UEffectVar   v -> "Effect name: " <> pretty v
    UEffectOpVar v -> "Effect operation name: " <> pretty v
    UHandlerVar  v -> "Handler name: " <> pretty v

-- TODO: name subst instances for the rest of UExpr
instance SinkableE      UVar
instance HoistableE     UVar
instance AlphaEqE       UVar
instance AlphaHashableE UVar
instance RenameE        UVar

instance HasNameHint (b n l) => HasNameHint (WithSrcB b n l) where
  getNameHint (WithSrcB _ b) = getNameHint b

instance HasNameHint (UPat' n l) where
  getNameHint (UPatBinder b) = getNameHint b
  getNameHint _ = noHint

instance HasNameHint ModuleSourceName where
  getNameHint (OrdinaryModule name) = getNameHint name
  getNameHint Prelude = getNameHint @String "prelude"
  getNameHint Main = getNameHint @String "main"

instance HasNameHint (UBinder c n l) where
  getNameHint b = case b of
    UBindSource v -> getNameHint v
    UIgnore       -> noHint
    UBind v _     -> getNameHint v

instance Color c => BindsNames (UBinder c) where
  toScopeFrag (UBindSource _) = emptyOutFrag
  toScopeFrag (UIgnore)       = emptyOutFrag
  toScopeFrag (UBind _ b)     = toScopeFrag b

instance Color c => ProvesExt (UBinder c) where
instance Color c => BindsAtMostOneName (UBinder c) c where
  b @> x = case b of
    UBindSource _ -> emptyInFrag
    UIgnore       -> emptyInFrag
    UBind _ b'    -> b' @> x

uBinderSourceName :: UBinder c n l -> SourceName
uBinderSourceName b = case b of
  UBindSource v -> v
  UIgnore       -> "_"
  UBind v _     -> v

instance ProvesExt  (UAnnBinder  req) where
instance BindsNames  (UAnnBinder req) where
  toScopeFrag (UAnnBinder b _ _) = toScopeFrag b

instance BindsAtMostOneName (UAnnBinder req) (AtomNameC CoreIR) where
  UAnnBinder b _ _ @> x = b @> x

instance GenericE (WithSrcE e) where
  type RepE (WithSrcE e) = PairE (LiftE SrcPosCtx) e
  fromE (WithSrcE ctx x) = PairE (LiftE ctx) x
  toE   (PairE (LiftE ctx) x) = WithSrcE ctx x

instance SinkableE e => SinkableE (WithSrcE e)

instance SinkableE UExpr' where
  sinkingProofE _ = todoSinkableProof

instance SinkableB UDecl where
  sinkingProofB _ _ _ = todoSinkableProof

instance Eq SourceBlock where
  x == y = sbText x == sbText y

instance Ord SourceBlock where
  compare x y = compare (sbText x) (sbText y)

instance Store SymbolicZeros
instance Store LogLevel
instance Store PassName
instance Store ModuleSourceName
instance Store (UVar n)
instance Store (SourceNameDef n)
instance Store (SourceMap n)

instance Hashable ModuleSourceName

instance IsString (SourceNameOr a VoidS) where
  fromString = SourceName

instance IsString (SourceOrInternalName c VoidS) where
  fromString = SISourceName

instance IsString (UBinder s VoidS VoidS) where
  fromString = UBindSource

instance IsString (UPat' VoidS VoidS) where
  fromString = UPatBinder . fromString

instance IsString (UOptAnnBinder VoidS VoidS) where
  fromString s = UAnnBinder (fromString s) UNoAnn []

instance IsString (UExpr' VoidS) where
  fromString = UVar . fromString

instance IsString (a n) => IsString (WithSrcE a n) where
  fromString = WithSrcE Nothing . fromString

instance IsString (b n l) => IsString (WithSrcB b n l) where
  fromString = WithSrcB Nothing . fromString

deriving instance Show (UBinder s n l)
deriving instance Show (UDataDefTrail n)
deriving instance Show (ULamExpr n)
deriving instance Show (UPiExpr n)
deriving instance Show (UTabPiExpr n)
deriving instance Show (UDepPairType n)
deriving instance Show (UDeclExpr n)
deriving instance Show (UDataDef n)
deriving instance Show (UStructDef n)
deriving instance Show (UDecl n l)
deriving instance Show (UForExpr n)
deriving instance Show (UAlt n)

deriving instance Show (UEffect n)
deriving instance Eq   (UEffect n)
deriving instance Ord  (UEffect n)

deriving instance Show (UEffectRow n)
deriving instance Eq   (UEffectRow n)
deriving instance Ord  (UEffectRow n)
