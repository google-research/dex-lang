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

import Data.Aeson (ToJSON (..))
import Data.Hashable
import Data.Foldable
import qualified Data.Map.Strict       as M
import Data.Word
import Data.Tuple (swap)

import GHC.Generics (Generic (..))
import Data.Store (Store (..))
import Data.String (fromString)

import Err
import PPrint
import Name
import MonadUtil
import Util (BString, File (..), SnocList)

import Types.Primitives

data SourceNameOr (a::E) (n::S) where
  -- Only appears before renaming pass
  SourceName :: SrcId -> SourceName -> SourceNameOr a n
  -- Only appears after renaming pass
  -- We maintain the source name for user-facing error messages.
  InternalName :: SrcId -> SourceName -> a n -> SourceNameOr a n
deriving instance Eq (a n) => Eq (SourceNameOr a n)
deriving instance Ord (a n) => Ord (SourceNameOr a n)
deriving instance Show (a n) => Show (SourceNameOr a n)

-- === Source Info ===

-- This is just for syntax highlighting. It won't be needed if we have
-- a separate lexing pass where we have a complete lossless data type for
-- lexemes.
data LexemeType =
   Keyword
 | Symbol
 | TypeName
 | LowerName
 | UpperName
 | LiteralLexeme
 | StringLiteralLexeme
 | MiscLexeme
 deriving (Show, Generic)

type Span = (Int, Int)
data LexemeInfo = LexemeInfo
  { lexemeList  :: SnocList SrcId
  , lexemeInfo  :: M.Map SrcId (LexemeType, Span) }
  deriving (Show, Generic)

type LexemeId = SrcId
type LexemeSpan = (LexemeId, LexemeId)
data GroupTree = GroupTree
  { gtSrcId :: SrcId
  , gtSpan  :: LexemeSpan
  , gtChildren :: [GroupTree]
  , gtIsAtomicLexeme :: Bool }
    deriving (Show, Eq, Generic)

instance Semigroup LexemeInfo where
  LexemeInfo a b <> LexemeInfo a' b' = LexemeInfo (a <> a') (b <> b')
instance Monoid LexemeInfo where
  mempty = LexemeInfo mempty mempty

-- === Source info ===

data SourceInfo =
   SIGroupingInfo  GroupingInfo
 | SINamingInfo    NamingInfo
 | SITypingInfo    TypingInfo
   deriving (Show, Eq, Generic)

newtype GroupingInfo = GroupingInfo (M.Map SrcId GroupTreeNode)
        deriving (Show, Eq, Semigroup, Monoid, Generic)
data GroupTreeNode = GroupTreeNode
  { gtnParent         :: Maybe SrcId
  , gtnSpan           :: LexemeSpan
  , gtnChildren       :: [SrcId]
  , gtnIsAtomicLexeme :: Bool }
    deriving (Show, Eq, Generic)

newtype NamingInfo = NamingInfo (M.Map SrcId NameInfo)
  deriving (Show, Eq, Generic, Semigroup, Monoid)
data NameInfo =
   LocalBinder [SrcId] -- src ids of groups for which this binder is in scope
 | LocalOcc SrcId      -- src id of this occ's binder
 | TopOcc BString
 deriving (Show, Eq, Generic)

newtype TypingInfo = TypingInfo (M.Map SrcId TypeInfo)
        deriving (Show, Eq, Semigroup, Monoid, Generic)
type TypeStr = BString
type ExprStr = BString
data TypeInfo =
   ExprType TypeStr      -- type of arbitrary expression
 | BinderType TypeStr
 | AppType
    TypeStr             -- type of whole application expression
    [(BString, TypeStr)] -- names and inferred types of implicit args
    [ExprStr]           -- values of synthesized dictionaries
    [SrcId]             -- binder srcIds for vars ocurring in terms produce by inference
  deriving (Show, Eq, Generic)

-- === Results ===

type TopLogger = Logger Outputs
type TopLogger1 (m::MonadKind1) = forall n. Logger Outputs (m n)

type LitProg = [(SourceBlock, Outputs)]

newtype Outputs = Outputs [Output] deriving (Show, Eq, Generic, Semigroup, Monoid)
data Output =
    TextOut BString
  | HtmlOut BString
  | SourceInfo SourceInfo       -- hovertips etc
  | PassResult PassName (Maybe BString)
  | MiscLog BString
  | Error Err
    deriving (Show, Eq, Generic)

type PassLogger = IOLogger Outputs
data OptLevel = NoOptimize | Optimize

-- === Concrete syntax ===
-- The grouping-level syntax of the source language

-- aliases for the "with source ID versions"

type GroupW      = WithSrcs Group
type CTopDeclW   = WithSrcs CTopDecl
type CSDeclW     = WithSrcs CSDecl
type SourceNameW = WithSrc SourceName

type BracketedGroup = WithSrcs [GroupW]
type ExplicitParams = BracketedGroup
type GivenClause = (BracketedGroup, Maybe BracketedGroup)  -- implicits, classes
type WithClause  = BracketedGroup -- no classes because we don't want to carry class dicts at runtime

data CTopDecl
  = CSDecl LetAnn CSDecl
  | CData
      SourceNameW      -- Type constructor name
      (Maybe ExplicitParams)
      (Maybe GivenClause)
      [(SourceNameW, Maybe ExplicitParams)]  -- Constructor names and argument sets
  | CStruct
      SourceNameW      -- Type constructor name
      (Maybe ExplicitParams)
      (Maybe GivenClause)
      [(SourceNameW, GroupW)] -- Field names and types
      [(LetAnn, CDef)]
  | CInterface
      SourceNameW  -- Interface name
      ExplicitParams
      [(SourceNameW, GroupW)]  -- Method declarations
  -- header, givens (may be empty), methods, optional name.  The header should contain
  -- the prerequisites, class name, and class arguments.
  | CInstanceDecl CInstanceDef
  deriving (Show, Generic)

data CSDecl
  = CLet GroupW CSBlock
  | CDefDecl CDef
  | CExpr GroupW
  | CPass
    deriving (Show, Generic)

data CDef = CDef
  SourceNameW
  ExplicitParams
  (Maybe CDefRhs)
  (Maybe GivenClause)
  CSBlock
  deriving (Show, Generic)

type CDefRhs = (AppExplicitness, GroupW)

data CInstanceDef = CInstanceDef
  SourceNameW -- interface name
  [GroupW]              -- args at which we're instantiating the interface
  (Maybe GivenClause)
  [CSDeclW]           -- Method definitions
  (Maybe (SourceNameW, Maybe BracketedGroup)) -- Optional name of instance, with explicit parameters
  deriving (Show, Generic)

data Group
  = CLeaf CLeaf
  | CPrim PrimName [GroupW]
  | CParens   [GroupW]
  | CBrackets [GroupW]
  | CBin Bin GroupW GroupW
  | CJuxtapose Bool GroupW GroupW -- Bool means "there's a space between the groups"
  | CPrefix SourceNameW GroupW -- covers unary - and unary + among others
  | CGivens GivenClause
  | CLambda [GroupW] CSBlock
  | CFor ForKind [GroupW] CSBlock -- also for_, rof, rof_
  | CCase GroupW [CaseAlt] -- scrutinee, alternatives
  | CIf GroupW CSBlock (Maybe CSBlock)
  | CDo CSBlock
  | CArrow GroupW GroupW
  | CWith GroupW WithClause
    deriving (Show, Generic)

data CLeaf
  = CIdentifier SourceName
  | CNat Word64
  | CInt Int
  | CString BString
  | CChar Char
  | CFloat Double
  | CHole
    deriving (Show, Generic)

type CaseAlt = (GroupW, CSBlock) -- scrutinee, lexeme Id, body

data Bin
  = EvalBinOp SourceNameW
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
  deriving (Show, Generic)

data LabelPrefix = PlainLabel
  deriving (Show, Generic)

data ForKind
  = KFor
  | KFor_
  | KRof
  | KRof_
  deriving (Show, Generic)

-- `CSBlock` instead of `CBlock` because the latter is an alias for `Block CoreIR`.
data CSBlock =
   IndentedBlock SrcId [CSDeclW] -- last decl should be a CExpr
 | ExprBlock GroupW
   deriving (Show, Generic)

-- === Untyped IR ===
-- The AST of Dex surface language.

type UVar = Name

type TopBinder = WithSrc SourceName

type UBinder = WithSrcB UBinder'
data UBinder' (n::S) (l::S) where
  -- Only appears before renaming pass
  UBindSource :: SourceName -> UBinder' n n
  -- May appear before or after renaming pass
  UIgnore :: UBinder' n n
  -- The following binders only appear after the renaming pass.
  -- We maintain the source name for user-facing error messages
  -- and named arguments.
  UBind :: SourceName -> NameBinder n l -> UBinder' n l

type UBlock = WithSrcE UBlock'
data UBlock' (n::S) where
  UBlock :: Nest UDecl n l -> UExpr l -> UBlock' n

type UDecl = WithSrcB UDecl'
data UDecl' (n::S) (l::S) where
  ULet      :: LetAnn -> UPat n l -> Maybe (UType n) -> UExpr n -> UDecl' n l
  UExprDecl :: UExpr n -> UDecl' n n
  UPass     :: UDecl' n n

type UExpr = WithSrcE UExpr'
data UExpr' (n::S) =
   UVar (SourceNameOr UVar n)
 | ULit LitVal
 | ULam (ULamExpr n)
 | UPi  (UPiExpr n)
 | UApp (UExpr n) [UExpr n] [UNamedArg n]
 | UTabPi  (UTabPiExpr n)
 | UDepPairTy (UDepPairType n)
 | UDepPair (UExpr n) (UExpr n)
 | UTabApp (UExpr n) [UExpr n]
 | UFor Direction (UForExpr n)
 | UCase (UExpr n) [UAlt n]
 | UDo (UBlock n)
 | UHole
 | UTypeAnn (UExpr n) (UExpr n)
 | UTabCon [UExpr n]
 | UPrim PrimName [UExpr n]
 | UFieldAccess (UExpr n) FieldName
 | UNatLit   Word64
 | UIntLit   Int
 | UFloatLit Double
   deriving (Show, Generic)

type UNamedArg (n::S) = (SourceName, UExpr n)
type FieldName = WithSrc FieldName'
data FieldName' =
   FieldName SourceName
 | FieldNum  Int
  deriving (Show, Eq, Ord)

data ULamExpr (n::S) where
  ULamExpr
    :: Nest UAnnBinder n l  -- args
    -> AppExplicitness
    -> Maybe (UType l)                    -- optional result type
    -> UBlock l                           -- body
    -> ULamExpr n

data UPiExpr (n::S) where
  UPiExpr :: Nest UAnnBinder n l -> AppExplicitness -> UType l -> UPiExpr n

data UTabPiExpr (n::S) where
  UTabPiExpr :: UAnnBinder n l -> UType l -> UTabPiExpr n

data UDepPairType (n::S) where
  UDepPairType :: DepPairExplicitness -> UAnnBinder n l -> UType l -> UDepPairType n

type UConDef (n::S) (l::S) = (SourceName, Nest UAnnBinder n l)

data UDataDef where
  UDataDef
    :: SourceName  -- source name for pretty printing
    -> Nest UAnnBinder VoidS l
    -> [(SourceName, UDataDefTrail l)] -- data constructor types
    -> UDataDef

data UStructDef where
  UStructDef
    :: SourceName    -- source name for pretty printing
    -> Nest UAnnBinder VoidS l
    -> [(SourceNameW, UType l)]                    -- named payloads
    -> [(LetAnn, SourceName, Abs UBinder ULamExpr l)] -- named methods (initial binder is for `self`)
    -> UStructDef

data UDataDefTrail (l::S) where
  UDataDefTrail :: Nest UAnnBinder l l' -> UDataDefTrail l

data UInterfaceDef where
  UInterfaceDef
    :: Nest UAnnBinder VoidS p   -- parameter binders
    -> [UType p]                 -- method types
    -> UInterfaceDef

data UInstanceDef where
  UInstanceDef
    :: Nest UAnnBinder VoidS l'
    ->   [UExpr l']          -- class parameters
    ->   [UMethodDef l']     -- method definitions
    -> UInstanceDef

data UTopDecl =
   UTopLet TopBinder (Maybe (UType VoidS)) (UExpr VoidS)
 | UTopExpr (UExpr VoidS)
 | UDataDefDecl
     UDataDef
     TopBinder               -- type constructor name
     [TopBinder]             -- data constructor names
 | UStructDecl
     UStructDef
     TopBinder              -- type constructor name
 | UInterface
    UInterfaceDef
    TopBinder               -- class name
    [TopBinder]             -- method names
 | UInstance UInstanceDef

type UType = UExpr
type UConstraint = UExpr

data UForExpr (n::S) where
  UForExpr :: UAnnBinder n l -> UBlock l -> UForExpr n

type UMethodDef = WithSrcE UMethodDef'
data UMethodDef' (n::S) = UMethodDef (SourceNameOr Name n) (ULamExpr n)
  deriving (Show, Generic)

data UAnn (n::S) = UAnn (UType n) | UNoAnn deriving Show

-- TODO: SrcId
data UAnnBinder (n::S) (l::S) =
  UAnnBinder Explicitness (UBinder n l) (UAnn n) [UConstraint n]
  deriving (Show, Generic)

data UAlt (n::S) where
  UAlt :: UPat n l -> UBlock l -> UAlt n

type UPat = WithSrcB UPat'
data UPat' (n::S) (l::S) =
   UPatBinder (UBinder n l)
 | UPatCon (SourceNameOr Name n) (Nest UPat n l)
 | UPatProd (Nest UPat n l)
 | UPatDepPair (PairB UPat UPat n l)
 | UPatTable (Nest UPat n l)
  deriving (Show, Generic)

-- === source names for error messages ===

class HasSourceName a where
  getSourceName :: a -> SourceName

instance HasSourceName (b n l) => HasSourceName (WithSrcB b n l) where
  getSourceName (WithSrcB _ b) = getSourceName b

instance HasSourceName (UAnnBinder n l) where
  getSourceName (UAnnBinder _ b _ _) = getSourceName b

instance HasSourceName (UBinder' n l) where
  getSourceName = \case
    UBindSource sn -> sn
    UIgnore        -> "_"
    UBind sn _     -> sn

-- === Source context helpers ===

-- First SrcId is for the group itself. The rest are for keywords, symbols, etc.
data WithSrcs a = WithSrcs SrcId [SrcId] a
  deriving (Show, Functor, Generic)

data WithSrc a = WithSrc SrcId a
  deriving (Show, Functor, Generic)

data WithSrcE (a::E) (n::S) = WithSrcE SrcId (a n)
  deriving (Show, Generic)

data WithSrcB (binder::B) (n::S) (l::S) = WithSrcB SrcId (binder n l)
  deriving (Show, Generic)

instance HasSrcId (WithSrc  a    ) where getSrcId (WithSrc  sid _  ) = sid
instance HasSrcId (WithSrcs a    ) where getSrcId (WithSrcs sid _ _) = sid
instance HasSrcId (WithSrcE e n  ) where getSrcId (WithSrcE sid _  ) = sid
instance HasSrcId (WithSrcB b n l) where getSrcId (WithSrcB sid _  ) = sid

instance HasSrcId (UAnnBinder n l) where
  getSrcId (UAnnBinder _ b _ _) = getSrcId b

class HasSrcPos withSrc a | withSrc -> a where
  srcPos :: withSrc -> SrcId
  withoutSrc :: withSrc -> a

instance HasSrcPos (WithSrc (a:: *)) a where
  srcPos (WithSrc pos _) = pos
  withoutSrc (WithSrc _ x) = x

instance HasSrcPos (WithSrcs (a:: *)) a where
  srcPos (WithSrcs pos _ _) = pos
  withoutSrc (WithSrcs _ _ x) = x

instance HasSrcPos (WithSrcE (e::E) (n::S)) (e n) where
  srcPos (WithSrcE pos _) = pos
  withoutSrc (WithSrcE _ x) = x

instance HasSrcPos (WithSrcB (b::B) (n::S) (l::S)) (b n l) where
  srcPos (WithSrcB pos _) = pos
  withoutSrc (WithSrcB _ x) = x

class FromSourceNameW a where
  fromSourceNameW :: SourceNameW -> a

instance FromSourceNameW (SourceNameOr a VoidS) where
  fromSourceNameW (WithSrc sid x) = SourceName sid x

instance FromSourceNameW (UBinder' VoidS VoidS) where
  fromSourceNameW x = UBindSource $ withoutSrc x

instance FromSourceNameW (UPat' VoidS VoidS) where
  fromSourceNameW = UPatBinder . fromSourceNameW

instance FromSourceNameW (UAnnBinder VoidS VoidS) where
  fromSourceNameW s = UAnnBinder Explicit (fromSourceNameW s) UNoAnn []

instance FromSourceNameW (UExpr' VoidS) where
  fromSourceNameW = UVar . fromSourceNameW

instance FromSourceNameW TopBinder where
  fromSourceNameW x = x

instance FromSourceNameW (a n) => FromSourceNameW (WithSrcE a n) where
  fromSourceNameW x = WithSrcE (srcPos x) $ fromSourceNameW x

instance FromSourceNameW (b n l) => FromSourceNameW (WithSrcB b n l) where
  fromSourceNameW x = WithSrcB (srcPos x) $ fromSourceNameW x

-- === SourceMap ===

-- TODO: line in module where it's defined
data TopNameDescription = TopNameDescription
  { tndModuleName  :: ModuleSourceName
  , tndTextSummary :: BString }
    deriving (Show, Eq, Ord, Generic)

data SourceNameDef n =
    LocalVar  SrcId (UVar n)                      -- bound within a decl or expression
    -- the Nothing case is for vars whose definitions have errors
  | ModuleVar TopNameDescription (Maybe (UVar n)) -- bound at the module level
    deriving (Show, Generic)

data SourceMap (n::S) = SourceMap
  {fromSourceMap :: M.Map SourceName [SourceNameDef n]}
  deriving Show

makeTopNameDescription :: ModuleSourceName -> SourceBlock -> TopNameDescription
makeTopNameDescription mname sb = TopNameDescription mname sb.sbText

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
  { sbLine       :: Int
  , sbOffset     :: Int
  , sbText       :: BString
  , sbLexemeInfo :: LexemeInfo
  , sbContents   :: SourceBlock' }
  deriving (Show, Generic)

type ReachedEOF = Bool

data SymbolicZeros = SymbolicZeros | InstantiateZeros
                     deriving (Generic, Eq, Show)

data SourceBlock'
  = TopDecl CTopDeclW
  | Misc SourceBlockMisc
  | UnParseable ReachedEOF BString
  deriving (Show, Generic)

data SourceBlockMisc
  = ImportModule ModuleSourceName
  | ProseBlock BString
  | CommentLine
  | EmptyLines
  deriving (Show, Generic)

data CmdName = GetType | EvalExpr OutFormat | ExportFun BString
               deriving  (Show, Generic)

data PrintBackend =
   PrintCodegen  -- Soon-to-be default path based on `PrintAny`
 | PrintHaskell  -- Backup path for debugging in case the codegen path breaks.
                 -- Uses PPrint.hs directly and doesn't make any attempt to
                 -- hide internals: SumAsProd, TabLam, AtomRepVal, etc
                 -- are printed as they are. Also accessible via `:pp`.

 deriving (Show, Eq, Generic)

data OutFormat = Printed (Maybe PrintBackend) | RenderHtml  deriving (Show, Eq, Generic)

data PassName = Parse | RenamePass | TypePass | SimpPass | ImpPass | LLVMPass
              | LLVMOpt | AsmPass | JAXPass | JAXSimpPass | LLVMEval | LowerOptPass | LowerPass
              | ResultPass | JaxprAndHLO | EarlyOptPass | OptPass | VectPass | OccAnalysisPass
              | InlinePass
                deriving (Ord, Eq, Bounded, Enum, Generic)

instance Show PassName where
  show p = case p of
    Parse    -> "parse" ; RenamePass -> "rename"; TypePass -> "typed"
    SimpPass -> "simp"  ; ImpPass  -> "imp"
    LLVMOpt  -> "llvmopt" ; AsmPass   -> "asm"
    JAXPass  -> "jax"   ; JAXSimpPass -> "jsimp"; ResultPass -> "result"
    LLVMEval -> "llvmeval" ; JaxprAndHLO -> "jaxprhlo";
    LowerOptPass -> "lower-opt"; LowerPass -> "lower"
    EarlyOptPass -> "early-opt"; OptPass -> "opt"; OccAnalysisPass -> "occ-analysis"
    VectPass -> "vect"; InlinePass -> "inline"; LLVMPass -> "llvm"

data EnvQuery =
   DumpSubst
 | InternalNameInfo RawName
 | SourceNameInfo   SourceName
   deriving (Show, Generic)

-- === instances ===

instance Semigroup (SourceMap n) where
  m1 <> m2 = SourceMap $ M.unionWith (++) (fromSourceMap m2) (fromSourceMap m1)

instance Monoid (SourceMap n) where
  mempty = SourceMap mempty

instance GenericE SourceNameDef where
  type RepE SourceNameDef = EitherE (LiftE SrcId `PairE` UVar) (LiftE TopNameDescription `PairE` MaybeE UVar)
  fromE (LocalVar sid v) = LeftE (PairE (LiftE sid) v)
  fromE (ModuleVar name maybeUVar) = RightE (PairE (LiftE name) (toMaybeE maybeUVar))
  {-# INLINE fromE #-}
  toE (LeftE (PairE (LiftE sid) v)) = LocalVar sid v
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

instance Pretty TopNameDescription where
  pr (TopNameDescription moduleName sourceText) = undefined
      --    "Top-level name defined in " <> pr moduleName <> ":"
      -- <> hardline <> pr sourceText

instance Pretty (SourceNameDef n) where
  pr def = case def of
    LocalVar _ v -> pr v
    ModuleVar _ Nothing -> "<error in definition>"
    ModuleVar desc (Just v) -> hcat [pr v, " defined in ", pr (tndModuleName desc)]

instance Pretty ModuleSourceName where
  pr Main = "main"
  pr Prelude = "prelude"
  pr (OrdinaryModule s) = pr s

instance Pretty (SourceMap n) where
  pr (SourceMap m) = undefined
    -- fold [pr v <+> "@>" <+> pr x <> hardline | (v, x) <- M.toList m ]

instance HasNameHint (b n l) => HasNameHint (WithSrcB b n l) where
  getNameHint (WithSrcB _ b) = getNameHint b

instance HasNameHint (UPat' n l) where
  getNameHint (UPatBinder b) = getNameHint b
  getNameHint _ = noHint

instance HasNameHint ModuleSourceName where
  getNameHint (OrdinaryModule name) = getNameHint name
  getNameHint Prelude = getNameHint @String "prelude"
  getNameHint Main = getNameHint @String "main"

instance HasNameHint (UBinder' n l) where
  getNameHint b = case b of
    UBindSource v -> getNameHint v
    UIgnore       -> noHint
    UBind v _     -> getNameHint v

instance BindsNames UBinder' where
  toScopeFrag (UBindSource _) = emptyOutFrag
  toScopeFrag (UIgnore)       = emptyOutFrag
  toScopeFrag (UBind _ b)     = toScopeFrag b

instance ProvesExt UBinder' where
instance BindsAtMostOneName UBinder' where
  b @> x = case b of
    UBindSource _ -> emptyInFrag
    UIgnore       -> emptyInFrag
    UBind _ b'    -> b' @> x

instance SinkableB UBinder' where
  sinkingProofB _ _ _ = todoSinkableProof

instance RenameB UBinder' where
  renameB env ub cont = case ub of
    UBindSource sn -> cont env $ UBindSource sn
    UIgnore -> cont env UIgnore
    UBind sn b -> renameB env b \env' b' -> cont env' $ UBind sn b'

instance SinkableB b => SinkableB (WithSrcB b) where
  sinkingProofB _ _ _ = todoSinkableProof

instance RenameB b => RenameB (WithSrcB b) where
  renameB env (WithSrcB sid b) cont =
    renameB env b \env' b' -> cont env' (WithSrcB sid b')

instance ProvesExt b => ProvesExt (WithSrcB b) where
  toExtEvidence (WithSrcB _ b) = toExtEvidence b

instance BindsNames b => BindsNames (WithSrcB b)  where
  toScopeFrag (WithSrcB _ b) = toScopeFrag b

instance BindsAtMostOneName b => BindsAtMostOneName (WithSrcB b) where
  WithSrcB _ b @> x = b @> x

instance ProvesExt  UAnnBinder where
instance BindsNames  UAnnBinder where
  toScopeFrag (UAnnBinder _ b _ _) = toScopeFrag b

instance BindsAtMostOneName UAnnBinder where
  UAnnBinder _ b _ _ @> x = b @> x

instance GenericE (WithSrcE e) where
  type RepE (WithSrcE e) = PairE (LiftE SrcId) e
  fromE (WithSrcE ctx x) = PairE (LiftE ctx) x
  toE   (PairE (LiftE ctx) x) = WithSrcE ctx x

instance SinkableE e => SinkableE (WithSrcE e)

instance SinkableE UExpr' where
  sinkingProofE _ = todoSinkableProof

instance SinkableE UBlock' where
  sinkingProofE _ = todoSinkableProof

instance SinkableB UDecl where
  sinkingProofB _ _ _ = todoSinkableProof

instance Eq SourceBlock where
  x == y = sbText x == sbText y

instance Ord SourceBlock where
  compare x y = compare (sbText x) (sbText y)

instance Store SymbolicZeros
instance Store PassName
instance Store ModuleSourceName
instance Store (SourceNameDef n)
instance Store (SourceMap n)
instance Store TopNameDescription

instance Hashable ModuleSourceName
instance Hashable TopNameDescription

deriving instance Show (UBinder' n l)
deriving instance Show (UDataDefTrail n)
deriving instance Show (ULamExpr n)
deriving instance Show (UPiExpr n)
deriving instance Show (UTabPiExpr n)
deriving instance Show (UDepPairType n)
deriving instance Show UDataDef
deriving instance Show UStructDef
deriving instance Show (UDecl' n l)
deriving instance Show (UBlock' n)
deriving instance Show (UForExpr n)
deriving instance Show (UAlt n)

instance ToJSON LexemeType
instance ToJSON PassName

-- === Pretty instances ===

instance Pretty CSBlock where
  pr (IndentedBlock _ decls) = undefined -- nest 2 $ prLines decls
  pr (ExprBlock g) = pr g

instance Pretty Group where
  pr = \case
    CLeaf leaf -> pr leaf
    CPrim prim args -> app (pr $ primNameToStr prim) (map pr args)


-- prettyOpDefault :: PrettyPrec a => PrimName -> [a] -> DocPrec ann
-- prettyOpDefault name args =
--   case length args of
--     0 -> atPrec ArgPrec primName
--     _ -> atPrec AppPrec $ pAppArg primName args
--   where primName = pretty name
  -- prettyPrec (CParens blk)  =
  --   atPrec ArgPrec $ "(" <> p blk <> ")"
  -- prettyPrec (CBrackets g) = atPrec ArgPrec $ pretty g
  -- prettyPrec (CBin op lhs rhs) =
  --   atPrec LowestPrec $ pArg lhs <+> p op <+> pArg rhs
  -- prettyPrec (CLambda args body) =
  --   atPrec LowestPrec $ "\\" <> spaced args <> "." <> p body
  -- prettyPrec (CCase scrut alts) =
  --   atPrec LowestPrec $ "case " <> p scrut <> " of " <> prettyLines alts
  -- prettyPrec g = atPrec ArgPrec $ fromString $ show g

instance Pretty CLeaf where
  pr = \case
    CIdentifier s -> pr s
    CNat n -> pr n
    CInt n -> pr n
    CString s -> pr $ show s
    CChar c -> pr $ show c
    CFloat f -> pr f
    CHole -> "_"

instance Pretty Bin where
  pr = \case
    EvalBinOp name -> pr name
    DepAmpersand -> "&>"
    Dot -> "."
    DepComma -> ",>"
    Colon -> ":"
    DoubleColon -> "::"
    Dollar -> "$"
    ImplicitArrow -> "->>"
    FatArrow -> "->>"
    Pipe -> "|"
    CSEqual -> "="

instance Pretty SourceBlock' where
  pr = \case
    TopDecl decl -> pr decl

instance Pretty CTopDecl where
  pr (CSDecl ann decl) = hcat [annDoc, pr decl]
    where annDoc = case ann of
            PlainLet -> ""
            _ -> hcat [pr ann, " "]
  pr d = fromString $ show d

instance Pretty CSDecl where
  pr (CLet pat blk) = hcat [pr pat, "=", pr blk]
  -- pr (CDefDecl (CDef name args maybeAnn blk)) =
  --   "def " <> fromString name <> " " <> prParamGroups args <+> annDoc
  --     <> nest 2 (hardline <> p blk)
  --   where annDoc = case maybeAnn of Just (expl, ty) -> p expl <+> pArg ty
  --                                   Nothing -> mempty
  -- pr (CInstance header givens methods name) =
  --   name' <> p header <> p givens <> nest 2 (hardline <> p methods) where
  --   name' = case name of
  --     Nothing  -> "instance "
  --     (Just n) -> "named-instance " <> p n <> " "
  -- pr (CExpr e) = p e

instance Pretty (UDataDefTrail n) where
  pr (UDataDefTrail bs) = pr $ unsafeFromNest bs

instance Pretty (UAnnBinder n l) where
  pr (UAnnBinder _ b ty _) = undefined -- pr b <> ":" <> pr ty

instance Pretty (UAnn n) where
  pr (UAnn ty) = hcat [":", pr ty]
  pr UNoAnn = ""

instance Pretty (UMethodDef' n) where
  pr (UMethodDef b rhs) = undefined -- pr b <+> "=" <+> pr rhs

instance Pretty (UPat' n l) where
  pr = \case
    UPatBinder x -> pr x
    -- UPatProd xs -> parens $ commaSep (unsafeFromNest xs)
    -- UPatDepPair (PairB x y) -> atPrec ArgPrec $ parens $ p x <> ",> " <> p y
    -- UPatCon con pats -> atPrec AppPrec $ parens $ p con <+> spaced (unsafeFromNest pats)
    -- UPatTable pats -> atPrec ArgPrec $ p pats
    -- where
    --   p :: Pretty a => a -> Doc ann
    --   p = pretty

instance Pretty (UAlt n) where
  pr (UAlt pat body) = undefined -- pr pat <+> "->" <+> pr body

instance Pretty UTopDecl where
  pr = \case
    UTopLet b _ expr -> hcat [pr b, " = ", pr expr]
    UTopExpr expr -> pr expr
     -- (Maybe (UType VoidS)) (UExpr VoidS)
  --   UDataDefDecl (UDataDef nm bs dataCons) bTyCon bDataCons ->
  --     "enum" <+> p bTyCon <+> p nm <+> spaced (unsafeFromNest bs) <+> "where" <> nest 2
  --        (prettyLines (zip (toList $ unsafeFromNest bDataCons) dataCons))
  --   UStructDecl bTyCon (UStructDef nm bs fields defs) ->
  --     "struct" <+> p bTyCon <+> p nm <+> spaced (unsafeFromNest bs) <+> "where" <> nest 2
  --       (prettyLines fields <> prettyLines defs)
  --   UInterface params methodTys interfaceName methodNames ->
  --     "interface" <+> p params <+> p interfaceName
  --        <> hardline <> foldMap (<>hardline) methods
  --     where
  --       methods = [ p b <> ":" <> p (unsafeCoerceE ty)
  --                 | (b, ty) <- zip (toList $ unsafeFromNest methodNames) methodTys]
  --   UInstance className bs params methods (RightB UnitB) _ ->
  --     "instance" <+> p bs <+> p className <+> spaced params <+>
  --        prettyLines methods
  --   UInstance className bs params methods (LeftB v) _ ->
  --     "named-instance" <+> p v <+> ":" <+> p bs <+> p className <+> p params
  --       <> prettyLines methods
  --   ULocalDecl decl -> p decl
  --   where
  --     p :: Pretty a => a -> Doc ann
  --     p = pretty

instance Pretty (UDecl' n l) where
  pr = \case
    -- ULet ann b _ rhs -> align $ pr ann <+> pr b <+> "=" <> (nest 2 $ group $ line <> pLowest rhs)
    -- UExprDecl expr -> pr expr
    UPass -> "pass"

instance Pretty e => Pretty (WithSrcs e) where pr (WithSrcs _ _ x) = pr x
instance Pretty e => Pretty (WithSrc e) where pr (WithSrc _ x) = pr x
instance PrettyE e => Pretty (WithSrcE e n) where pr (WithSrcE _ x) = pr x
instance PrettyB b => Pretty (WithSrcB b n l) where pr (WithSrcB _ x) = pr x
instance PrettyE e => Pretty (SourceNameOr e n) where
  pr (SourceName _ v) = pr v
  pr (InternalName _ v _) = pr v

instance Pretty (ULamExpr n) where
  pr (ULamExpr bs _ _ body) = undefined
    -- atPrec LowestPrec $
    -- "\\" <> pretty bs <+> "." <+> indented (pretty body)

instance Pretty (UPiExpr n) where
  pr (UPiExpr pats appExpl ty) = undefined
  -- atPrec LowestPrec $ align $
  --   pretty pats <+> pretty appExpl <+> pLowest ty

instance Pretty (UTabPiExpr n) where
  pr (UTabPiExpr pat ty) = undefined
  -- atPrec LowestPrec $ align $
  --   pretty pat <+> "=>" <+> pLowest ty

instance Pretty (UDepPairType n) where
  -- TODO: print explicitness info
  pr (UDepPairType _ pat ty) = undefined
  -- atPrec LowestPrec $ align $
  --   pr pat <+> "&>" <+> pLowest ty

instance Pretty (UBlock' n) where
  pr (UBlock decls result) = undefined
  -- pretty (UBlock decls result) =
  --   prettyLines (unsafeFromNest decls) <> hardline <> pLowest result

instance Pretty (UExpr' n) where
  pr = \case
    ULit l -> pr l
    UVar v -> pr v
--     ULam lam -> prettyPrec lam
--     UApp    f xs named -> atPrec AppPrec $ pAppArg (pApp f) xs <+> p named
--     UTabApp f x -> atPrec AppPrec $ pArg f <> "." <> pArg x
--     UFor dir (UForExpr binder body) ->
--       atPrec LowestPrec $ kw <+> p binder <> "."
--                              <+> nest 2 (p body)
--       where kw = case dir of Fwd -> "for"
--                              Rev -> "rof"
--     UPi piType -> prettyPrec piType
--     UTabPi piType -> prettyPrec piType
--     UDepPairTy depPairType -> prettyPrec depPairType
--     UDepPair lhs rhs -> atPrec ArgPrec $ parens $
--       p lhs <+> ",>" <+> p rhs
--     UHole -> atPrec ArgPrec "_"
--     UTypeAnn v ty -> atPrec LowestPrec $
--       group $ pApp v <> line <> ":" <+> pApp ty
--     UTabCon xs -> atPrec ArgPrec $ p xs
    UPrim prim xs -> app (pr (primNameToStr prim)) (map pr xs)
--     UCase e alts -> atPrec LowestPrec $ "case" <+> p e <>
--       nest 2 (prettyLines alts)
--     UFieldAccess x (WithSrc _ f) -> atPrec AppPrec $ p x <> "~" <> p f
    UNatLit   v -> pr v
    UIntLit   v -> pr v
    UFloatLit v -> pr v
--     UDo block -> atPrec LowestPrec $ p block
--     where
--       p :: Pretty a => a -> Doc ann
--       p = pretty

instance Pretty SourceBlock where
  pr block = pr $ sbText block

instance Pretty Output where
  prLines = \case
    TextOut s -> prLines s
    HtmlOut _ -> "<html output>"
    SourceInfo _ -> "<source info>"
    PassResult name s -> do
      emitLine $ hcat [" === ", pr name, " ==="]
      prLines s
    MiscLog s -> prLines s
    Error e -> prLines e

instance Pretty PassName where
  pr x = pr $ show x

instance Pretty (UBinder' n l) where
  pr = \case
    UBindSource v -> pr v
    UIgnore       -> "_"
    UBind v _     -> pr v

instance Pretty FieldName' where
  pr = \case
    FieldName s -> pr s
    FieldNum n  -> pr n
