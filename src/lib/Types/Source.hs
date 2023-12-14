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
import qualified Data.Set              as S
import qualified Data.Text             as T
import Data.Text (Text)
import Data.Word
import Data.Text.Prettyprint.Doc (line, group, parens, nest, align, punctuate, hsep)
import Data.Text (snoc, unsnoc)
import Data.Tuple (swap)

import GHC.Generics (Generic (..))
import Data.Store (Store (..))
import Data.String (fromString)

import Err
import PPrint
import Name
import qualified Types.OpNames as P
import IRVariants
import MonadUtil
import Util (File (..), SnocList)

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

newtype SourceOrInternalName (c::C) (n::S) = SourceOrInternalName (SourceNameOr (Name c) n)
  deriving (Eq, Ord, Show, Generic)

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
 | TopOcc String
 deriving (Show, Eq, Generic)

newtype TypingInfo = TypingInfo (M.Map SrcId TypeInfo)
        deriving (Show, Eq, Semigroup, Monoid, Generic)
type TypeStr = String
type ExprStr = String
data TypeInfo =
   ExprType TypeStr      -- type of arbitrary expression
 | BinderType TypeStr
 | AppType
    TypeStr             -- type of whole application expression
    [(String, TypeStr)] -- names and inferred types of implicit args
    [ExprStr]           -- values of synthesized dictionaries
    [SrcId]             -- binder srcIds for vars ocurring in terms produce by inference
  deriving (Show, Eq, Generic)

-- === Results ===

type TopLogger1 (m::MonadKind1) = forall n. Logger Outputs (m n)

type LitProg = [(SourceBlock, Outputs)]

newtype Outputs = Outputs [Output] deriving (Show, Eq, Generic, Semigroup, Monoid)
data Output =
    TextOut String
  | HtmlOut String
  | SourceInfo SourceInfo       -- hovertips etc
  | PassResult PassName (Maybe String)
  | MiscLog String
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
-- optional arrow, effects, result type
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
  | CBind GroupW CSBlock -- Arrow binder <-
  | CPass
    deriving (Show, Generic)

type CEffs = WithSrcs ([GroupW], Maybe GroupW)
data CDef = CDef
  SourceNameW
  ExplicitParams
  (Maybe CDefRhs)
  (Maybe GivenClause)
  CSBlock
  deriving (Show, Generic)

type CDefRhs = (AppExplicitness, Maybe CEffs, GroupW)

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
  | CArrow GroupW (Maybe CEffs) GroupW
  | CWith GroupW WithClause
    deriving (Show, Generic)

data CLeaf
  = CIdentifier SourceName
  | CNat Word64
  | CInt Int
  | CString String
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

data UEffect (n::S) =
   URWSEffect RWS (SourceOrInternalName (AtomNameC CoreIR) n)
 | UExceptionEffect
 | UIOEffect
 deriving (Generic)

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
 | UMethodVar   (Name MethodNameC   n)
 | UPunVar      (Name TyConNameC n) -- for names also used as data constructors
   deriving (Eq, Ord, Show, Generic)

type UAtomBinder = UBinder (AtomNameC CoreIR)
type UBinder c = WithSrcB (UBinder' c)
data UBinder' (c::C) (n::S) (l::S) where
  -- Only appears before renaming pass
  UBindSource :: SourceName -> UBinder' c n n
  -- May appear before or after renaming pass
  UIgnore :: UBinder' c n n
  -- The following binders only appear after the renaming pass.
  -- We maintain the source name for user-facing error messages
  -- and named arguments.
  UBind :: SourceName -> NameBinder c n l -> UBinder' c n l

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
    -> Maybe (UEffectRow l)               -- optional effect
    -> Maybe (UType l)                    -- optional result type
    -> UBlock l                           -- body
    -> ULamExpr n

data UPiExpr (n::S) where
  UPiExpr :: Nest UAnnBinder n l -> AppExplicitness -> UEffectRow l -> UType l -> UPiExpr n

data UTabPiExpr (n::S) where
  UTabPiExpr :: UAnnBinder n l -> UType l -> UTabPiExpr n

data UDepPairType (n::S) where
  UDepPairType :: DepPairExplicitness -> UAnnBinder n l -> UType l -> UDepPairType n

type UConDef (n::S) (l::S) = (SourceName, Nest UAnnBinder n l)

data UDataDef (n::S) where
  UDataDef
    :: SourceName  -- source name for pretty printing
    -> Nest UAnnBinder n l
    -> [(SourceName, UDataDefTrail l)] -- data constructor types
    -> UDataDef n

data UStructDef (n::S) where
  UStructDef
    :: SourceName    -- source name for pretty printing
    -> Nest UAnnBinder n l
    -> [(SourceNameW, UType l)]                    -- named payloads
    -> [(LetAnn, SourceName, Abs UAtomBinder ULamExpr l)] -- named methods (initial binder is for `self`)
    -> UStructDef n

data UDataDefTrail (l::S) where
  UDataDefTrail :: Nest UAnnBinder l l' -> UDataDefTrail l

data UTopDecl (n::S) (l::S) where
  ULocalDecl :: UDecl n l -> UTopDecl n l
  UDataDefDecl
    :: UDataDef n                          -- actual definition
    -> UBinder TyConNameC n l'             -- type constructor name
    ->   Nest (UBinder DataConNameC) l' l  -- data constructor names
    -> UTopDecl n l
  UStructDecl
    :: UBinder TyConNameC n l              -- type constructor name
    -> UStructDef l                        -- actual definition
    -> UTopDecl n l
  UInterface
    :: Nest UAnnBinder n p   -- parameter binders
    ->   [UType p]                         -- method types
    -> UBinder ClassNameC n l'             -- class name
    ->   Nest (UBinder MethodNameC) l' l   -- method names
    -> UTopDecl n l
  UInstance
    :: SourceNameOr (Name ClassNameC) n  -- class name
    -> Nest UAnnBinder n l'
    ->   [UExpr l']                      -- class parameters
    ->   [UMethodDef l']                 -- method definitions
    -- Maybe we should make a separate color (namespace) for instance names?
    -> MaybeB UAtomBinder n l    -- optional instance name
    -> AppExplicitness           -- explicitness (only relevant for named instances)
    -> UTopDecl n l

type UType = UExpr
type UConstraint = UExpr

data UResumePolicy =
    UNoResume
  | ULinearResume
  | UAnyResume
  deriving (Show, Eq, Generic)

instance Hashable UResumePolicy
instance Store UResumePolicy

data UForExpr (n::S) where
  UForExpr :: UAnnBinder n l -> UBlock l -> UForExpr n

type UMethodDef = WithSrcE UMethodDef'
data UMethodDef' (n::S) = UMethodDef (SourceNameOr (Name MethodNameC) n) (ULamExpr n)
  deriving (Show, Generic)

data UAnn (n::S) = UAnn (UType n) | UNoAnn deriving Show

-- TODO: SrcId
data UAnnBinder (n::S) (l::S) =
  UAnnBinder Explicitness (UAtomBinder n l) (UAnn n) [UConstraint n]
  deriving (Show, Generic)

data UAlt (n::S) where
  UAlt :: UPat n l -> UBlock l -> UAlt n

type UPat = WithSrcB UPat'
data UPat' (n::S) (l::S) =
   UPatBinder (UAtomBinder n l)
 | UPatCon (SourceNameOr (Name DataConNameC) n) (Nest UPat n l)
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

instance HasSourceName (UBinder' c n l) where
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

instance FromSourceNameW (SourceOrInternalName c VoidS) where
  fromSourceNameW x = SourceOrInternalName $ fromSourceNameW x

instance FromSourceNameW (UBinder' s VoidS VoidS) where
  fromSourceNameW x = UBindSource $ withoutSrc x

instance FromSourceNameW (UPat' VoidS VoidS) where
  fromSourceNameW = UPatBinder . fromSourceNameW

instance FromSourceNameW (UAnnBinder VoidS VoidS) where
  fromSourceNameW s = UAnnBinder Explicit (fromSourceNameW s) UNoAnn []

instance FromSourceNameW (UExpr' VoidS) where
  fromSourceNameW = UVar . fromSourceNameW

instance FromSourceNameW (a n) => FromSourceNameW (WithSrcE a n) where
  fromSourceNameW x = WithSrcE (srcPos x) $ fromSourceNameW x

instance FromSourceNameW (b n l) => FromSourceNameW (WithSrcB b n l) where
  fromSourceNameW x = WithSrcB (srcPos x) $ fromSourceNameW x

-- === SourceMap ===

-- TODO: line in module where it's defined
data TopNameDescription = TopNameDescription
  { tndModuleName  :: ModuleSourceName
  , tndTextSummary :: String }
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
makeTopNameDescription mname sb = TopNameDescription mname (T.unpack $ sbText sb)

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
  , sbText       :: Text
  , sbLexemeInfo :: LexemeInfo
  , sbContents   :: SourceBlock' }
  deriving (Show, Generic)

type ReachedEOF = Bool

data SymbolicZeros = SymbolicZeros | InstantiateZeros
                     deriving (Generic, Eq, Show)

data SourceBlock'
  = TopDecl CTopDeclW
  | Command CmdName GroupW
  | DeclareForeign SourceNameW SourceNameW GroupW
  | DeclareCustomLinearization SourceNameW SymbolicZeros GroupW
  | Misc SourceBlockMisc
  | UnParseable ReachedEOF String
  deriving (Show, Generic)

data SourceBlockMisc
  = GetNameType SourceNameW
  | ImportModule ModuleSourceName
  | QueryEnv EnvQuery
  | ProseBlock Text
  | CommentLine
  | EmptyLines
  deriving (Show, Generic)

data CmdName = GetType | EvalExpr OutFormat | ExportFun String
               deriving  (Show, Generic)

data PrintBackend =
   PrintCodegen  -- Soon-to-be default path based on `PrintAny`
 | PrintHaskell  -- Backup path for debugging in case the codegen path breaks.
                 -- Uses PPrint.hs directly and doesn't make any attempt to
                 -- hide internals: SumAsProd, TabLam, AtomRepVal, etc
                 -- are printed as they are. Also accessible via `:pp`.

 deriving (Show, Eq, Generic)

data OutFormat = Printed (Maybe PrintBackend) | RenderHtml  deriving (Show, Eq, Generic)

data PassName = Parse | RenamePass | TypePass | SimpPass | ImpPass | JitPass
              | LLVMOpt | AsmPass | JAXPass | JAXSimpPass | LLVMEval | LowerOptPass | LowerPass
              | ResultPass | JaxprAndHLO | EarlyOptPass | OptPass | VectPass | OccAnalysisPass
              | InlinePass
                deriving (Ord, Eq, Bounded, Enum, Generic)

instance Show PassName where
  show p = case p of
    Parse    -> "parse" ; RenamePass -> "rename"; TypePass -> "typed"
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
   UBaseType BaseType
 | UPrimTC   P.TC
 | UCon      P.Con
 | UMemOp    P.MemOp
 | UVectorOp P.VectorOp
 | UMiscOp   P.MiscOp
 | UUnOp     UnOp
 | UBinOp    BinOp
 | UMAsk | UMExtend | UMGet | UMPut
 | UWhile | ULinearize | UTranspose
 | URunReader | URunWriter | URunState | URunIO | UCatchException
 | UProjNewtype | UExplicitApply | UMonoLiteral
 | UIndexRef | UApplyMethod Int
 | UNat | UNatCon | UFin | UEffectRowKind
 | UTuple -- overloaded for type constructor and data constructor, resolved in inference
   deriving (Show, Eq, Generic)

-- === primitive constructors and operators ===

strToPrimName :: String -> Maybe PrimName
strToPrimName s = M.lookup s primNames

primNameToStr :: PrimName -> String
primNameToStr prim = case lookup prim $ map swap $ M.toList primNames of
  Just s  -> s
  Nothing -> show prim

showPrimName :: PrimName -> String
showPrimName prim = primNameToStr prim
{-# NOINLINE showPrimName #-}

primNames :: M.Map String PrimName
primNames = M.fromList
  [ ("ask"      , UMAsk), ("mextend", UMExtend)
  , ("get"      , UMGet), ("put"    , UMPut)
  , ("while"    , UWhile)
  , ("linearize", ULinearize), ("linearTranspose", UTranspose)
  , ("runReader", URunReader), ("runWriter"      , URunWriter), ("runState", URunState)
  , ("runIO"    , URunIO    ), ("catchException" , UCatchException)
  , ("iadd" , binary IAdd),  ("isub"  , binary ISub)
  , ("imul" , binary IMul),  ("fdiv"  , binary FDiv)
  , ("fadd" , binary FAdd),  ("fsub"  , binary FSub)
  , ("fmul" , binary FMul),  ("idiv"  , binary IDiv)
  , ("irem" , binary IRem)
  , ("fpow" , binary FPow)
  , ("and"  , binary BAnd),  ("or"    , binary BOr )
  , ("not"  , unary  BNot),  ("xor"   , binary BXor)
  , ("shl"  , binary BShL),  ("shr"   , binary BShR)
  , ("ieq"  , binary (ICmp Equal)),   ("feq", binary (FCmp Equal))
  , ("igt"  , binary (ICmp Greater)), ("fgt", binary (FCmp Greater))
  , ("ilt"  , binary (ICmp Less)),    ("flt", binary (FCmp Less))
  , ("fneg" , unary  FNeg)
  , ("exp"  , unary  Exp),   ("exp2"  , unary Exp2)
  , ("log"  , unary  Log),   ("log2"  , unary Log2), ("log10" , unary Log10)
  , ("sin"  , unary  Sin),   ("cos"   , unary Cos)
  , ("tan"  , unary  Tan),   ("sqrt"  , unary Sqrt)
  , ("floor", unary  Floor), ("ceil"  , unary Ceil), ("round", unary Round)
  , ("log1p", unary  Log1p), ("lgamma", unary LGamma)
  , ("erf"  , unary Erf),    ("erfc"  , unary Erfc)
  , ("TyKind"    , UPrimTC $ P.TypeKind)
  , ("Float64"   , baseTy $ Scalar Float64Type)
  , ("Float32"   , baseTy $ Scalar Float32Type)
  , ("Int64"     , baseTy $ Scalar Int64Type)
  , ("Int32"     , baseTy $ Scalar Int32Type)
  , ("Word8"     , baseTy $ Scalar Word8Type)
  , ("Word32"    , baseTy $ Scalar Word32Type)
  , ("Word64"    , baseTy $ Scalar Word64Type)
  , ("Int32Ptr"  , baseTy $ ptrTy $ Scalar Int32Type)
  , ("Word8Ptr"  , baseTy $ ptrTy $ Scalar Word8Type)
  , ("Word32Ptr" , baseTy $ ptrTy $ Scalar Word32Type)
  , ("Word64Ptr" , baseTy $ ptrTy $ Scalar Word64Type)
  , ("Float32Ptr", baseTy $ ptrTy $ Scalar Float32Type)
  , ("PtrPtr"    , baseTy $ ptrTy $ ptrTy $ Scalar Word8Type)
  , ("Nat"           , UNat)
  , ("Fin"           , UFin)
  , ("EffKind"       , UEffectRowKind)
  , ("NatCon"        , UNatCon)
  , ("Ref"       , UPrimTC $ P.RefType)
  , ("HeapType"  , UPrimTC $ P.HeapType)
  , ("indexRef"   , UIndexRef)
  , ("alloc"    , memOp $ P.IOAlloc)
  , ("free"     , memOp $ P.IOFree)
  , ("ptrOffset", memOp $ P.PtrOffset)
  , ("ptrLoad"  , memOp $ P.PtrLoad)
  , ("ptrStore" , memOp $ P.PtrStore)
  , ("throwError"    , miscOp $ P.ThrowError)
  , ("throwException", miscOp $ P.ThrowException)
  , ("dataConTag"    , miscOp $ P.SumTag)
  , ("toEnum"        , miscOp $ P.ToEnum)
  , ("outputStream"  , miscOp $ P.OutputStream)
  , ("cast"          , miscOp $ P.CastOp)
  , ("bitcast"       , miscOp $ P.BitcastOp)
  , ("unsafeCoerce"  , miscOp $ P.UnsafeCoerce)
  , ("garbageVal"    , miscOp $ P.GarbageVal)
  , ("select"        , miscOp $ P.Select)
  , ("showAny"       , miscOp $ P.ShowAny)
  , ("showScalar"    , miscOp $ P.ShowScalar)
  , ("projNewtype" , UProjNewtype)
  , ("applyMethod0" , UApplyMethod 0)
  , ("applyMethod1" , UApplyMethod 1)
  , ("applyMethod2" , UApplyMethod 2)
  , ("explicitApply", UExplicitApply)
  , ("monoLit", UMonoLiteral)
  ]
  where
    binary op = UBinOp op
    baseTy b  = UBaseType b
    memOp op  = UMemOp op
    unary  op = UUnOp  op
    ptrTy  ty = PtrType (CPU, ty)
    miscOp op = UMiscOp op


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
  pretty (TopNameDescription moduleName sourceText) =
         "Top-level name defined in " <> pretty moduleName <> ":"
      <> hardline <> pretty sourceText

instance Pretty (SourceNameDef n) where
  pretty def = case def of
    LocalVar _ v -> pretty v
    ModuleVar _ Nothing -> "<error in definition>"
    ModuleVar desc (Just v) -> pretty v <> " defined in " <> pretty (tndModuleName desc)

instance Pretty ModuleSourceName where
  pretty Main = "main"
  pretty Prelude = "prelude"
  pretty (OrdinaryModule s) = pretty s

instance Pretty (SourceMap n) where
  pretty (SourceMap m) =
    fold [pretty v <+> "@>" <+> pretty x <> hardline | (v, x) <- M.toList m ]

instance GenericE UVar where
  type RepE UVar = EitherE6 (Name (AtomNameC CoreIR)) (Name TyConNameC)
                            (Name DataConNameC)  (Name ClassNameC)
                            (Name MethodNameC)   (Name TyConNameC)
  fromE name = case name of
    UAtomVar     v -> Case0 v
    UTyConVar    v -> Case1 v
    UDataConVar  v -> Case2 v
    UClassVar    v -> Case3 v
    UMethodVar   v -> Case4 v
    UPunVar      v -> Case5 v
  {-# INLINE fromE #-}

  toE name = case name of
    Case0 v -> UAtomVar     v
    Case1 v -> UTyConVar    v
    Case2 v -> UDataConVar  v
    Case3 v -> UClassVar    v
    Case4 v -> UMethodVar   v
    Case5 v -> UPunVar v
    _ -> error "impossible"
  {-# INLINE toE #-}

instance Pretty (UVar n) where
  pretty name = case name of
    UAtomVar     v -> "Atom name: " <> pretty v
    UTyConVar    v -> "Type constructor name: " <> pretty v
    UDataConVar  v -> "Data constructor name: " <> pretty v
    UClassVar    v -> "Class name: " <> pretty v
    UMethodVar   v -> "Method name: " <> pretty v
    UPunVar      v -> "Shared type constructor / data constructor name: " <> pretty v

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

instance HasNameHint (UBinder' c n l) where
  getNameHint b = case b of
    UBindSource v -> getNameHint v
    UIgnore       -> noHint
    UBind v _     -> getNameHint v

instance Color c => BindsNames (UBinder' c) where
  toScopeFrag (UBindSource _) = emptyOutFrag
  toScopeFrag (UIgnore)       = emptyOutFrag
  toScopeFrag (UBind _ b)     = toScopeFrag b

instance Color c => ProvesExt (UBinder' c) where
instance Color c => BindsAtMostOneName (UBinder' c) c where
  b @> x = case b of
    UBindSource _ -> emptyInFrag
    UIgnore       -> emptyInFrag
    UBind _ b'    -> b' @> x

instance Color c => SinkableB (UBinder' c) where
  sinkingProofB _ _ _ = todoSinkableProof

instance Color c => RenameB (UBinder' c) where
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

instance BindsAtMostOneName b r => BindsAtMostOneName (WithSrcB b) r where
  WithSrcB _ b @> x = b @> x

instance ProvesExt  UAnnBinder where
instance BindsNames  UAnnBinder where
  toScopeFrag (UAnnBinder _ b _ _) = toScopeFrag b

instance BindsAtMostOneName UAnnBinder (AtomNameC CoreIR) where
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

instance SinkableB UTopDecl where
  sinkingProofB _ _ _ = todoSinkableProof

instance Eq SourceBlock where
  x == y = sbText x == sbText y

instance Ord SourceBlock where
  compare x y = compare (sbText x) (sbText y)

instance Store SymbolicZeros
instance Store PassName
instance Store ModuleSourceName
instance Store (UVar n)
instance Store (SourceNameDef n)
instance Store (SourceMap n)
instance Store TopNameDescription

instance Hashable ModuleSourceName
instance Hashable TopNameDescription

deriving instance Show (UBinder' s n l)
deriving instance Show (UDataDefTrail n)
deriving instance Show (ULamExpr n)
deriving instance Show (UPiExpr n)
deriving instance Show (UTabPiExpr n)
deriving instance Show (UDepPairType n)
deriving instance Show (UDataDef n)
deriving instance Show (UStructDef n)
deriving instance Show (UDecl' n l)
deriving instance Show (UBlock' n)
deriving instance Show (UForExpr n)
deriving instance Show (UAlt n)

deriving instance Show (UEffect n)
deriving instance Eq   (UEffect n)
deriving instance Ord  (UEffect n)

deriving instance Show (UEffectRow n)
deriving instance Eq   (UEffectRow n)
deriving instance Ord  (UEffectRow n)

instance ToJSON LexemeType
instance ToJSON PassName

-- === Pretty instances ===

instance Pretty CSBlock where
  pretty (IndentedBlock _ decls) = nest 2 $ prettyLines decls
  pretty (ExprBlock g) = pArg g

instance Pretty Group where pretty = prettyFromPrettyPrec
instance PrettyPrec Group where
  prettyPrec = undefined
  -- prettyPrec (CIdentifier n) = atPrec ArgPrec $ fromString n
  -- prettyPrec (CPrim prim args) = prettyOpDefault prim args
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

instance Pretty Bin where
  pretty = \case
    EvalBinOp name -> pretty name
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
  pretty (TopDecl decl) = pretty decl
  pretty d = fromString $ show d

instance Pretty CTopDecl where
  pretty (CSDecl ann decl) = annDoc <> pretty decl
    where annDoc = case ann of
            PlainLet -> mempty
            _ -> pretty ann <> " "
  pretty d = fromString $ show d

instance Pretty CSDecl where
  pretty = undefined
  -- pretty (CLet pat blk) = pArg pat <+> "=" <+> p blk
  -- pretty (CBind pat blk) = pArg pat <+> "<-" <+> p blk
  -- pretty (CDefDecl (CDef name args maybeAnn blk)) =
  --   "def " <> fromString name <> " " <> prettyParamGroups args <+> annDoc
  --     <> nest 2 (hardline <> p blk)
  --   where annDoc = case maybeAnn of Just (expl, ty) -> p expl <+> pArg ty
  --                                   Nothing -> mempty
  -- pretty (CInstance header givens methods name) =
  --   name' <> p header <> p givens <> nest 2 (hardline <> p methods) where
  --   name' = case name of
  --     Nothing  -> "instance "
  --     (Just n) -> "named-instance " <> p n <> " "
  -- pretty (CExpr e) = p e

instance Pretty PrimName where
   pretty primName = pretty $ "%" ++ showPrimName primName

instance Pretty (UDataDefTrail n) where
  pretty (UDataDefTrail bs) = pretty $ unsafeFromNest bs

instance Pretty (UAnnBinder n l) where
  pretty (UAnnBinder _ b ty _) = pretty b <> ":" <> pretty ty

instance Pretty (UAnn n) where
  pretty (UAnn ty) = ":" <> pretty ty
  pretty UNoAnn = mempty

instance Pretty (UMethodDef' n) where
  pretty (UMethodDef b rhs) = pretty b <+> "=" <+> pretty rhs

instance Pretty (UPat' n l) where pretty = prettyFromPrettyPrec
instance PrettyPrec (UPat' n l) where
  prettyPrec pat = case pat of
    UPatBinder x -> atPrec ArgPrec $ p x
    UPatProd xs -> atPrec ArgPrec $ parens $ commaSep (unsafeFromNest xs)
    UPatDepPair (PairB x y) -> atPrec ArgPrec $ parens $ p x <> ",> " <> p y
    UPatCon con pats -> atPrec AppPrec $ parens $ p con <+> spaced (unsafeFromNest pats)
    UPatTable pats -> atPrec ArgPrec $ p pats
    where
      p :: Pretty a => a -> Doc ann
      p = pretty

instance Pretty (UAlt n) where
  pretty (UAlt pat body) = pretty pat <+> "->" <+> pretty body

instance Pretty (UTopDecl n l) where
  pretty = \case
    UDataDefDecl (UDataDef nm bs dataCons) bTyCon bDataCons ->
      "enum" <+> p bTyCon <+> p nm <+> spaced (unsafeFromNest bs) <+> "where" <> nest 2
         (prettyLines (zip (toList $ unsafeFromNest bDataCons) dataCons))
    UStructDecl bTyCon (UStructDef nm bs fields defs) ->
      "struct" <+> p bTyCon <+> p nm <+> spaced (unsafeFromNest bs) <+> "where" <> nest 2
        (prettyLines fields <> prettyLines defs)
    UInterface params methodTys interfaceName methodNames ->
      "interface" <+> p params <+> p interfaceName
         <> hardline <> foldMap (<>hardline) methods
      where
        methods = [ p b <> ":" <> p (unsafeCoerceE ty)
                  | (b, ty) <- zip (toList $ unsafeFromNest methodNames) methodTys]
    UInstance className bs params methods (RightB UnitB) _ ->
      "instance" <+> p bs <+> p className <+> spaced params <+>
         prettyLines methods
    UInstance className bs params methods (LeftB v) _ ->
      "named-instance" <+> p v <+> ":" <+> p bs <+> p className <+> p params
        <> prettyLines methods
    ULocalDecl decl -> p decl
    where
      p :: Pretty a => a -> Doc ann
      p = pretty

instance Pretty (UDecl' n l) where
  pretty = \case
    ULet ann b _ rhs -> align $ pretty ann <+> pretty b <+> "=" <> (nest 2 $ group $ line <> pLowest rhs)
    UExprDecl expr -> pretty expr
    UPass -> "pass"

instance Pretty (UEffectRow n) where
  pretty (UEffectRow x Nothing) = encloseSep "<" ">" "," $ (pretty <$> toList x)
  pretty (UEffectRow x (Just y)) = "{" <> (hsep $ punctuate "," (pretty <$> toList x)) <+> "|" <+> pretty y <> "}"

instance Pretty e => Pretty (WithSrcs e) where pretty (WithSrcs _ _ x) = pretty x
instance PrettyPrec e => PrettyPrec (WithSrcs e) where prettyPrec (WithSrcs _ _ x) = prettyPrec x

instance Pretty e => Pretty (WithSrc e) where pretty (WithSrc _ x) = pretty x
instance PrettyPrec e => PrettyPrec (WithSrc e) where prettyPrec (WithSrc _ x) = prettyPrec x

instance PrettyE e => Pretty (WithSrcE e n) where pretty (WithSrcE _ x) = pretty x
instance PrettyPrecE e => PrettyPrec (WithSrcE e n) where prettyPrec (WithSrcE _ x) = prettyPrec x

instance PrettyB b => Pretty (WithSrcB b n l) where pretty (WithSrcB _ x) = pretty x
instance PrettyPrecB b => PrettyPrec (WithSrcB b n l) where prettyPrec (WithSrcB _ x) = prettyPrec x

instance PrettyE e => Pretty (SourceNameOr e n) where
  pretty (SourceName _ v) = pretty v
  pretty (InternalName _ v _) = pretty v

instance Pretty (SourceOrInternalName c n) where
  pretty (SourceOrInternalName sn) = pretty sn

instance Pretty (ULamExpr n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (ULamExpr n) where
  prettyPrec (ULamExpr bs _ _ _ body) = atPrec LowestPrec $
    "\\" <> pretty bs <+> "." <+> indented (pretty body)

instance Pretty (UPiExpr n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (UPiExpr n) where
  prettyPrec (UPiExpr pats appExpl UPure ty) = atPrec LowestPrec $ align $
    pretty pats <+> pretty appExpl <+> pLowest ty
  prettyPrec (UPiExpr pats appExpl eff ty) = atPrec LowestPrec $ align $
    pretty pats <+> pretty appExpl <+> pretty eff <+> pLowest ty

instance Pretty (UTabPiExpr n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (UTabPiExpr n) where
  prettyPrec (UTabPiExpr pat ty) = atPrec LowestPrec $ align $
    pretty pat <+> "=>" <+> pLowest ty

instance Pretty (UDepPairType n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (UDepPairType n) where
  -- TODO: print explicitness info
  prettyPrec (UDepPairType _ pat ty) = atPrec LowestPrec $ align $
    pretty pat <+> "&>" <+> pLowest ty

instance Pretty (UBlock' n) where
  pretty (UBlock decls result) =
    prettyLines (unsafeFromNest decls) <> hardline <> pLowest result

instance Pretty (UExpr' n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (UExpr' n) where
  prettyPrec expr = case expr of
    ULit l -> prettyPrec l
    UVar v -> atPrec ArgPrec $ p v
    ULam lam -> prettyPrec lam
    UApp    f xs named -> atPrec AppPrec $ pAppArg (pApp f) xs <+> p named
    UTabApp f x -> atPrec AppPrec $ pArg f <> "." <> pArg x
    UFor dir (UForExpr binder body) ->
      atPrec LowestPrec $ kw <+> p binder <> "."
                             <+> nest 2 (p body)
      where kw = case dir of Fwd -> "for"
                             Rev -> "rof"
    UPi piType -> prettyPrec piType
    UTabPi piType -> prettyPrec piType
    UDepPairTy depPairType -> prettyPrec depPairType
    UDepPair lhs rhs -> atPrec ArgPrec $ parens $
      p lhs <+> ",>" <+> p rhs
    UHole -> atPrec ArgPrec "_"
    UTypeAnn v ty -> atPrec LowestPrec $
      group $ pApp v <> line <> ":" <+> pApp ty
    UTabCon xs -> atPrec ArgPrec $ p xs
    UPrim prim xs -> atPrec AppPrec $ p (show prim) <+> p xs
    UCase e alts -> atPrec LowestPrec $ "case" <+> p e <>
      nest 2 (prettyLines alts)
    UFieldAccess x (WithSrc _ f) -> atPrec AppPrec $ p x <> "~" <> p f
    UNatLit   v -> atPrec ArgPrec $ p v
    UIntLit   v -> atPrec ArgPrec $ p v
    UFloatLit v -> atPrec ArgPrec $ p v
    UDo block -> atPrec LowestPrec $ p block
    where
      p :: Pretty a => a -> Doc ann
      p = pretty

instance Pretty SourceBlock where
  pretty block = pretty $ ensureNewline (sbText block) where
    -- Force the SourceBlock to end in a newline for echoing, even if
    -- it was terminated with EOF in the original program.
    ensureNewline t = case unsnoc t of
      Nothing -> t
      Just (_, '\n') -> t
      _ -> t `snoc` '\n'

instance Pretty Output where
  pretty = \case
    TextOut s -> pretty s
    HtmlOut _ -> "<html output>"
    SourceInfo _ -> ""
    PassResult _ s -> pretty s
    MiscLog s -> pretty s
    Error e -> pretty e

instance Pretty PassName where
  pretty x = pretty $ show x

instance Pretty (UBinder' c n l) where pretty = prettyFromPrettyPrec
instance PrettyPrec (UBinder' c n l) where
  prettyPrec b = atPrec ArgPrec case b of
    UBindSource v -> pretty v
    UIgnore       -> "_"
    UBind v _     -> pretty v

instance Pretty FieldName' where
  pretty = \case
    FieldName s -> pretty s
    FieldNum n  -> pretty n

instance Pretty (UEffect n) where
  pretty eff = case eff of
    URWSEffect rws h -> pretty rws <+> pretty h
    UExceptionEffect -> "Except"
    UIOEffect        -> "IO"

prettyOpDefault :: PrettyPrec a => PrimName -> [a] -> DocPrec ann
prettyOpDefault name args =
  case length args of
    0 -> atPrec ArgPrec primName
    _ -> atPrec AppPrec $ pAppArg primName args
  where primName = pretty name
