-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE EmptyCase #-}

module SaferNames.Syntax (
    Type, Kind, BaseType (..), ScalarBaseType (..), Except,
    EffectP (..), Effect, UEffect, RWS (..), EffectRowP (..), EffectRow, UEffectRow,
    SrcPos, Binder, Block (..), Decl (..),
    Expr (..), Atom (..), Arrow (..), PrimTC (..), Abs (..),
    PrimExpr (..), PrimCon (..), LitVal (..), PrimEffect (..), PrimOp (..),
    PrimHof (..), LamExpr (..), PiType (..), LetAnn (..),
    BinOp (..), UnOp (..), CmpOp (..), SourceMap (..),
    ForAnn (..), Val, Op, Con, Hof, TC, Module (..), UModule (..), SourceNameDef (..),
    FromSourceNameDef, fromSourceNameDef, ClassDef (..),
    EvaluatedModule (..), SynthCandidates (..), TopState (..),
    TopBindings (..), emptyTopState,
    DataConRefBinding (..), MethodDef (..), SuperclassDef (..),
    DataConNameDef (..), TyConNameDef (..),
    AltP, Alt, AtomNameDef (..), AtomBinderInfo (..),
    SubstE (..), SubstB (..), Ptr, PtrType,
    AddressSpace (..), Device (..), showPrimName, strToPrimName, primNameToStr,
    Direction (..), Limit (..), DataDef (..), DataConDef (..), Nest (..), IndexStructure,
    mkConsList, mkConsListTy, fromConsList, fromConsListTy, fromLeftLeaningConsListTy,
    mkBundle, mkBundleTy, BundleDesc,
    BaseMonoidP (..), BaseMonoid, getIntLit, getFloatLit, sizeOf, ptrSize, vectorWidth,
    IRVariant (..), SubstVal (..), AtomName, AtomSubstVal,
    SourceName, SourceNameOr (..), UVar (..), UBinder (..),
    UExpr, UExpr' (..), UConDef, UDataDef (..), UDataDefTrail (..), UDecl (..),
    ULamExpr (..), UPiExpr (..), UDeclExpr (..), UForExpr (..), UAlt (..),
    UPat, UPat' (..), UPatAnn (..), UPatAnnArrow (..),
    UMethodDef (..), UAnnBinder (..),
    WithSrcE (..), WithSrcB (..), srcPos,
    SourceBlock (..), SourceBlock' (..),
    SourceUModule (..), UType,
    CmdName (..), LogLevel (..), PassName, OutFormat (..),
    TopBindingsFrag, TopBinding (..), NamedDataDef,
    pattern IdxRepTy, pattern IdxRepVal, pattern TagRepTy,
    pattern TagRepVal, pattern Word8Ty,
    pattern UnitTy, pattern PairTy,
    pattern FixedIntRange, pattern Fin, pattern RefTy, pattern RawRefTy,
    pattern BaseTy, pattern PtrTy, pattern UnitVal,
    pattern PairVal, pattern TyKind,
    pattern Pure, pattern LabeledRowKind, pattern EffKind,
    pattern FunTy, pattern BinaryFunTy, pattern UPatIgnore,
    pattern IntLitExpr, pattern FloatLitExpr,
    (-->), (?-->), (--@), (==>) ) where

import Data.Foldable (toList, fold)
import Control.Monad.Except hiding (Except)
import qualified Data.List.NonEmpty    as NE
import qualified Data.Map.Strict       as M
import qualified Data.Set              as S
import Data.Int
import Data.String (IsString, fromString)
import Data.Text.Prettyprint.Doc
import Data.Word
import Type.Reflection (Typeable, TypeRep, typeRep)
import Foreign.Ptr

import GHC.Generics (Generic (..), Rep)
import Data.Store (Store)

import Syntax
  ( LetAnn (..), IRVariant (..)
  , PrimExpr (..), PrimTC (..), PrimCon (..), PrimOp (..), PrimHof (..)
  , BaseMonoid, BaseMonoidP (..), PrimEffect (..), BinOp (..), UnOp (..)
  , CmpOp (..), Direction (..)
  , ForAnn (..), Limit (..), strToPrimName, primNameToStr, showPrimName
  , BlockId, ReachedEOF, ModuleName, CmdName (..), LogLevel (..)
  , RWS (..), LitVal (..), ScalarBaseType (..), BaseType (..)
  , AddressSpace (..), Device (..), PtrType, sizeOf, ptrSize, vectorWidth
  , PassName, OutFormat (..))

import SaferNames.Name
import PPrint ()
import Err
import LabeledItems

-- === core IR ===

data Atom (n::S) =
   Var (AtomName n)
 | Lam (LamExpr n)
 | Pi  (PiType  n)
   -- SourceName is purely for printing
 | DataCon SourceName (NamedDataDef n) [Atom n] Int [Atom n]
 | TypeCon (NamedDataDef n) [Atom n]
 | LabeledRow (ExtLabeledItems (Type n) (AtomName n))
 | Record (LabeledItems (Atom n))
 | RecordTy  (ExtLabeledItems (Type n) (AtomName n))
 | Variant   (ExtLabeledItems (Type n) (AtomName n)) Label Int (Atom n)
 | VariantTy (ExtLabeledItems (Type n) (AtomName n))
 | Con (Con n)
 | TC  (TC  n)
 | Eff (EffectRow n)
 | ACase (Atom n) [AltP Atom n] (Type n)
   -- single-constructor only for now
 | DataConRef (NamedDataDef n) [Atom n] (EmptyAbs (Nest DataConRefBinding) n)
 | BoxedRef (Atom n) (Block n) (Abs Binder Atom n)  -- ptr, size, binder/body
 -- access a nested member of a binder
 -- XXX: Variable name must not be an alias for another name or for
 -- a statically-known atom. This is because the variable name used
 -- here may also appear in the type of the atom. (We maintain this
 -- invariant during substitution and in Builder.hs.)
 | ProjectElt (NE.NonEmpty Int) (AtomName n)
   deriving (Show, Generic)

data Expr n =
   App (Atom n) (Atom n)
 | Case (Atom n) [Alt n] (Type n)
 | Atom (Atom n)
 | Op  (Op  n)
 | Hof (Hof n)
   deriving (Show, Generic)

data AtomBinderInfo (n::S) =
   LetBound LetAnn (Expr n)
 | LamBound Arrow
 | PiBound
 | MiscBound
 | InferenceName
   deriving (Show, Generic)

-- We inline the definition for compatibility with the unsafe IR.
-- TODO: remove once we don't need the bridge anymore
type NamedDataDef n = (Name DataDef n, DataDef n)

data AtomNameDef (n::S) = AtomNameDef (Type n) (AtomBinderInfo n)
     deriving (Show, Generic)

data Decl n l = Let LetAnn (Binder n l) (Expr n)
                deriving (Show, Generic)

type AtomName = Name AtomNameDef

type Binder = BinderP (NameBinder AtomNameDef) Type
data DataConRefBinding (n::S) (l::S) = DataConRefBinding (Binder n l) (Atom n)

type AltP (e::E) = Abs (Nest Binder) e :: E
type Alt = AltP Block                  :: E

data DataDef n where
  -- The `SourceName` is just for pretty-printing. The actual alpha-renamable
  -- binder name is in UExpr and Bindings
  DataDef :: SourceName -> Nest Binder n l -> [DataConDef l] -> DataDef n

-- As above, the `SourceName` is just for pretty-printing
data DataConDef n =
  DataConDef SourceName (EmptyAbs (Nest Binder) n)
  deriving (Show, Generic)

-- The Type is the type of the result expression (and thus the type of the
-- block). It's given by querying the result expression's type, and checking
-- that it doesn't have any free names bound by the decls in the block. We store
-- it separately as an optimization, to avoid having to traverse the block.
data Block n where
  Block :: Type n -> Nest Decl n l ->  Expr l -> Block n

data LamExpr (n::S) where
  LamExpr :: Arrow -> Binder n l -> EffectRow l -> Block l -> LamExpr n

data PiType  (n::S) where
  PiType :: Arrow -> Binder n l -> EffectRow l -> Type  l -> PiType n

data Arrow =
   PlainArrow
 | ImplicitArrow
 | ClassArrow
 | TabArrow
 | LinArrow
   deriving (Show, Eq, Generic)

type Val  = Atom
type Type = Atom
type Kind = Type

type TC  n = PrimTC  (Atom n)
type Con n = PrimCon (Atom n)
type Op  n = PrimOp  (Atom n)
type Hof n = PrimHof (Atom n)

type IndexStructure = Nest Binder

type AtomSubstVal = SubstVal AtomNameDef Atom :: E -> E

-- === front-end language AST ===

data SourceNameOr (a::E) (n::S) where
  -- Only appears before renaming pass
  SourceName :: SourceName -> SourceNameOr a VoidS
  -- Only appears after renaming pass
  InternalName :: a n -> SourceNameOr a n
deriving instance Eq (a n) => Eq (SourceNameOr (a::E) (n::S))
deriving instance Ord (a n) => Ord (SourceNameOr a n)
deriving instance Show (a n) => Show (SourceNameOr a n)

data UVar (n::S) =
   UAtomVar (Name AtomNameDef n)
 | UTyConVar (Name TyConNameDef n)
 | UDataConVar (Name DataConNameDef n)
 | UClassVar (Name ClassDef n)
 | UMethodVar (Name MethodDef n)
   deriving (Eq, Ord, Show, Generic)

data UBinder (s::E) (n::S) (l::S) where
  -- Only appears before renaming pass
  UBindSource :: SourceName -> UBinder s VoidS VoidS
  -- May appear before or after renaming pass
  UIgnore :: UBinder s n n
  -- The following binders only appear after the renaming pass.
  UBind :: (NameBinder s n l) -> UBinder s n l

type UExpr = WithSrcE UExpr'
data UExpr' (n::S) =
   UVar (SourceNameOr UVar n)
 | ULam (ULamExpr n)
 | UPi  (UPiExpr n)
 | UApp Arrow (UExpr n) (UExpr n)
 | UDecl (UDeclExpr n)
 | UFor Direction (UForExpr n)
 | UCase (UExpr n) [UAlt n]
 | UHole
 | UTypeAnn (UExpr n) (UExpr n)
 | UTabCon [UExpr n]
 | UIndexRange (Limit (UExpr n)) (Limit (UExpr n))
 | UPrimExpr (PrimExpr (UExpr n))
 | URecord (ExtLabeledItems (UExpr n) (UExpr n))     -- {a=x, b=y, ...rest}
 | UVariant (LabeledItems ()) Label (UExpr n)        -- {|a|b| a=x |}
 | UVariantLift (LabeledItems ()) (UExpr n)          -- {|a|b| ...rest |}
 | URecordTy (ExtLabeledItems (UExpr n) (UExpr n))   -- {a:X & b:Y & ...rest}
 | UVariantTy (ExtLabeledItems (UExpr n) (UExpr n))  -- {a:X | b:Y | ...rest}
 | UIntLit  Int
 | UFloatLit Double
  deriving (Show, Generic)

data ULamExpr (n::S) where
  ULamExpr :: Arrow -> UPatAnn n l -> UExpr l -> ULamExpr n

data UPiExpr (n::S) where
  UPiExpr :: Arrow -> UPatAnn n l -> UEffectRow l -> UType l -> UPiExpr n

data UDeclExpr (n::S) where
  UDeclExpr :: UDecl n l -> UExpr l -> UDeclExpr n

type UConDef (n::S) (l::S) = (SourceName, Nest (UAnnBinder AtomNameDef) n l)

-- TODO Why are the type and data constructor names SourceName, rather
-- than being scoped names of the proper color of their own?
data UDataDef (n::S) where
  UDataDef
    :: (SourceName, Nest (UAnnBinder AtomNameDef) n l)    -- param binders
    -- Trailing l' is the last scope for the chain of potentially
    -- dependent constructor argument types.
    -> [(SourceName, UDataDefTrail l)] -- data constructor types
    -> UDataDef n

data UDataDefTrail (l::S) where
  UDataDefTrail :: Nest (UAnnBinder AtomNameDef) l l' -> UDataDefTrail l

data UDecl (n::S) (l::S) where
  ULet :: LetAnn -> UPatAnn n l -> UExpr n -> UDecl n l
  UDataDefDecl
    :: UDataDef n                            -- actual definition
    -> UBinder TyConNameDef n l'             -- type constructor name
    ->   Nest (UBinder DataConNameDef) l' l  -- data constructor names
    -> UDecl n l
  UInterface
    :: Nest (UAnnBinder AtomNameDef) n p  -- parameter binders
    ->  [UType p]                         -- superclasses
    ->  [UType p]                         -- method types
    -> UBinder ClassDef n l'              -- class name
    ->   Nest (UBinder MethodDef) l' l    -- method names
    -> UDecl n l
  UInstance
    :: Nest UPatAnnArrow n l'            -- dictionary args (i.e. conditions)
    ->   SourceNameOr (Name ClassDef) l' -- class variable
    ->   [UExpr l']                      -- class parameters
    ->   [UMethodDef l']                 -- method definitions
    -- Maybe we should make a separate color (namespace) for instance names?
    -> MaybeB (UBinder AtomNameDef) n l  -- optional instance name
    -> UDecl n l

type UType  = UExpr

data UForExpr (n::S) where
  UForExpr :: UPatAnn n l -> UExpr l -> UForExpr n

data UMethodDef (n::S) = UMethodDef (SourceNameOr (Name MethodDef) n) (UExpr n)
  deriving (Show, Generic)

data UPatAnn (n::S) (l::S) = UPatAnn (UPat n l) (Maybe (UType n))
  deriving (Show, Generic)

data UPatAnnArrow (n::S) (l::S) = UPatAnnArrow (UPatAnn n l) Arrow
  deriving (Show, Generic)

data UAnnBinder (s::E) (n::S) (l::S) = UAnnBinder (UBinder s n l) (UType n)
  deriving (Show, Generic)

data UAlt (n::S) where
  UAlt :: UPat n l -> UExpr l -> UAlt n

type UPat = WithSrcB UPat'
data UPat' (n::S) (l::S) =
   UPatBinder (UBinder AtomNameDef n l)
 | UPatCon (SourceNameOr (Name DataConNameDef) n) (Nest UPat n l)
 | UPatPair (PairB UPat UPat n l)
 | UPatUnit (UnitB n l)
 -- The ExtLabeledItems and the Nest are meant to be parallel.  If the
 -- ExtLabeledItems has a Just at the end, that corresponds to the
 -- last item in the given Nest.
 | UPatRecord (ExtLabeledItems () ()) (Nest UPat n l)     -- {a=x, b=y, ...rest}
 | UPatVariant (LabeledItems ()) Label (UPat n l)   -- {|a|b| a=x |}
 | UPatVariantLift (LabeledItems ()) (UPat n l)     -- {|a|b| ...rest |}
 | UPatTable (Nest UPat n l)
  deriving (Show)

data WithSrcE (a::E) (n::S) = WithSrcE SrcCtx (a n)
  deriving (Show)

data WithSrcB (binder::B) (n::S) (l::S) = WithSrcB SrcCtx (binder n l)
  deriving (Show)

class HasSrcPos a where
  srcPos :: a -> SrcCtx

instance HasSrcPos (WithSrcE (a::E) (n::S)) where
  srcPos (WithSrcE pos _) = pos

instance HasSrcPos (WithSrcB (b::B) (n::S) (n::S)) where
  srcPos (WithSrcB pos _) = pos

pattern UPatIgnore :: UPat' (n::S) n
pattern UPatIgnore = UPatBinder UIgnore

-- === top-level modules ===

type SourceName = String

-- body must only contain SourceName version of names and binders
data SourceUModule = SourceUModule (UDecl VoidS VoidS) deriving (Show)

-- body must only contain Name version of names and binders
data UModule (n::S) where
  UModule
    :: Distinct l
    => ScopeFrag n l
    -> SourceMap l
    -> UDecl n l
    -> UModule n

data SourceBlock = SourceBlock
  { sbLine     :: Int
  , sbOffset   :: Int
  , sbLogLevel :: LogLevel
  , sbText     :: String
  , sbContents :: SourceBlock'
  , sbId       :: Maybe BlockId }  deriving (Show)

data SourceBlock' =
   RunModule SourceUModule
 | Command CmdName (SourceName, SourceUModule)
 | GetNameType SourceName
 -- TODO Add a color for module names?
 | ImportModule ModuleName
 | ProseBlock String
 | CommentLine
 | EmptyLines
 | UnParseable ReachedEOF String
  deriving (Show, Generic)

data TopState n = TopState
  { topBindings        :: TopBindings n
  , topSynthCandidates :: SynthCandidates n
  , topSourceMap       :: SourceMap   n }
  deriving Show

data TopBindings n where
  TopBindings :: Distinct n => Env TopBinding n n -> TopBindings n

type TopBindingsFrag n l = EnvFrag TopBinding n l l

-- TODO: add Store, PPrint etc
data TopBinding (e::E) (n::S) where
  TopBinding :: (Typeable e, SubstE AtomSubstVal e, SubstE Name e, InjectableE e)
             => e n -> TopBinding e n

emptyTopState :: TopState VoidS
emptyTopState = TopState (TopBindings emptyEnv) mempty (SourceMap mempty)

data SourceNameDef (n::S) =
   SrcAtomName    (Name AtomNameDef n)
 | SrcTyConName   (Name TyConNameDef n)
 | SrcDataConName (Name DataConNameDef n)
 | SrcClassName   (Name ClassDef n)
 | SrcMethodName  (Name MethodDef n)
 deriving (Show, Generic)

class FromSourceNameDef (color::E) where
  fromSourceNameDef :: SourceNameDef n -> Maybe (Name color n)

data TyConNameDef   n = TyConNameDef   (Name DataDef n)                    deriving (Show, Generic)
data DataConNameDef n = DataConNameDef (Name DataDef n) Int                deriving (Show, Generic)
data ClassDef       n = ClassDef SourceName [SourceName] (NamedDataDef n)  deriving (Show, Generic)
data MethodDef      n = MethodDef (Name ClassDef n) Int (Atom n)           deriving (Show, Generic)
data SuperclassDef  n = SuperclassDef (Name ClassDef n) Int (Atom n)       deriving (Show, Generic)

data SourceMap (n::S) = SourceMap
  { fromSourceMap :: M.Map SourceName (SourceNameDef n)}
  deriving (Show, Generic)

data Module n where
  Module
    :: IRVariant
    -> Nest Decl n l      -- Unevaluated decls representing runtime work to be done
    -> EvaluatedModule l
    -> Module n

data EvaluatedModule (n::S) where
  EvaluatedModule
    :: TopBindingsFrag n l  -- Evaluated bindings
    -> SynthCandidates l    -- Values considered in scope for dictionary synthesis
    -> SourceMap l          -- Mapping of module's source names to internal names
    -> EvaluatedModule n

-- TODO: we could add a lot more structure for querying by dict type, caching, etc.
data SynthCandidates n = SynthCandidates
  { lambdaDicts       :: [Atom n]
  , superclassGetters :: [Atom n]
  , instanceDicts     :: [Atom n] }
  deriving (Show, Generic)

-- === effects ===

data EffectP (name::E) (n::S) =
  RWSEffect RWS (name n) | ExceptionEffect | IOEffect
  deriving (Show, Eq, Ord, Generic)

type Effect = EffectP AtomName
type UEffect = EffectP (SourceNameOr (Name AtomNameDef))

data EffectRowP (name::E) (n::S) =
  EffectRow (S.Set (EffectP name n)) (Maybe (name n))
  deriving (Show, Eq, Ord, Generic)

type EffectRow = EffectRowP AtomName
type UEffectRow = EffectRowP (SourceNameOr (Name AtomNameDef))

pattern Pure :: Ord (name n) => EffectRowP name n
pattern Pure <- ((\(EffectRow effs t) -> (S.null effs, t)) -> (True, Nothing))
 where  Pure = EffectRow mempty Nothing

extendEffRow :: S.Set (Effect n) -> (EffectRow n) -> (EffectRow n)
extendEffRow effs (EffectRow effs' t) = EffectRow (effs <> effs') t

-- === Synonyms ===

infixr 1 -->
infixr 1 --@
infixr 2 ==>

nonDepPiType :: (ScopeReader m, ScopeExtender m)
             => Arrow -> Type n -> EffectRow n -> Type n -> m n (Type n)
nonDepPiType arr argTy eff resultTy =
  toConstAbs (PairE eff resultTy) >>= \case
    Abs b (PairE eff' resultTy') ->
      return $ Pi $ PiType arr (b:>argTy) eff' resultTy'

(?-->) :: (ScopeReader m, ScopeExtender m) => Type n -> Type n -> m n (Type n)
a ?--> b = nonDepPiType ImplicitArrow a Pure b

(-->) :: (ScopeReader m, ScopeExtender m) => Type n -> Type n -> m n (Type n)
a --> b = nonDepPiType PlainArrow a Pure b

(--@) :: (ScopeReader m, ScopeExtender m) => Type n -> Type n -> m n (Type n)
a --@ b = nonDepPiType LinArrow a Pure b

(==>) :: (ScopeReader m, ScopeExtender m) => Type n -> Type n -> m n (Type n)
a ==> b = nonDepPiType TabArrow a Pure b

pattern IntLitExpr :: Int -> UExpr' n
pattern IntLitExpr x = UIntLit x

pattern FloatLitExpr :: Double -> UExpr' n
pattern FloatLitExpr x = UFloatLit x

getIntLit :: LitVal -> Int
getIntLit l = case l of
  Int64Lit i -> fromIntegral i
  Int32Lit i -> fromIntegral i
  Word8Lit  i -> fromIntegral i
  _ -> error $ "Expected an integer literal"

getFloatLit :: LitVal -> Double
getFloatLit l = case l of
  Float64Lit f -> f
  Float32Lit f -> realToFrac f
  _ -> error $ "Expected a floating-point literal"

-- Type used to represent indices at run-time
pattern IdxRepTy :: Type n
pattern IdxRepTy = TC (BaseType (Scalar Int32Type))

pattern IdxRepVal :: Int32 -> Atom n
pattern IdxRepVal x = Con (Lit (Int32Lit x))

-- Type used to represent sum type tags at run-time
pattern TagRepTy :: Type n
pattern TagRepTy = TC (BaseType (Scalar Word8Type))

pattern TagRepVal :: Word8 -> Atom n
pattern TagRepVal x = Con (Lit (Word8Lit x))

pattern Word8Ty :: Type n
pattern Word8Ty = TC (BaseType (Scalar Word8Type))

pattern PairVal :: Atom n -> Atom n -> Atom n
pattern PairVal x y = Con (ProdCon [x, y])

pattern PairTy :: Type n -> Type n -> Type n
pattern PairTy x y = TC (ProdType [x, y])

pattern UnitVal :: Atom n
pattern UnitVal = Con (ProdCon [])

pattern UnitTy :: Type n
pattern UnitTy = TC (ProdType [])

pattern BaseTy :: BaseType -> Type n
pattern BaseTy b = TC (BaseType b)

pattern PtrTy :: PtrType -> Type n
pattern PtrTy ty = BaseTy (PtrType ty)

pattern RefTy :: Atom n -> Type n -> Type n
pattern RefTy r a = TC (RefType (Just r) a)

pattern RawRefTy :: Type n -> Type n
pattern RawRefTy a = TC (RefType Nothing a)

pattern TyKind :: Kind n
pattern TyKind = TC TypeKind

pattern EffKind :: Kind n
pattern EffKind = TC EffectRowKind

pattern LabeledRowKind :: Kind n
pattern LabeledRowKind = TC LabeledRowKindTC

pattern FixedIntRange :: Int32 -> Int32 -> Type n
pattern FixedIntRange low high = TC (IntRange (IdxRepVal low) (IdxRepVal high))

pattern Fin :: Atom n -> Type n
pattern Fin n = TC (IntRange (IdxRepVal 0) n)

mkConsListTy :: [Type n] -> Type n
mkConsListTy = foldr PairTy UnitTy

mkConsList :: [Atom n] -> Atom n
mkConsList = foldr PairVal UnitVal

fromConsListTy :: MonadError Err m => Type n -> m [Type n]
fromConsListTy ty = case ty of
  UnitTy         -> return []
  PairTy t rest -> (t:) <$> fromConsListTy rest
  _              -> throw CompilerErr $ "Not a pair or unit: " ++ show ty

-- ((...((ans & x{n}) & x{n-1})... & x2) & x1) -> (ans, [x1, ..., x{n}])
fromLeftLeaningConsListTy :: MonadError Err m => Int -> Type n -> m (Type n, [Type n])
fromLeftLeaningConsListTy depth initTy = go depth initTy []
  where
    go 0        ty xs = return (ty, reverse xs)
    go remDepth ty xs = case ty of
      PairTy lt rt -> go (remDepth - 1) lt (rt : xs)
      _ -> throw CompilerErr $ "Not a pair: " ++ show xs

fromConsList :: MonadError Err m => Atom n -> m [Atom n]
fromConsList xs = case xs of
  UnitVal        -> return []
  PairVal x rest -> (x:) <$> fromConsList rest
  _              -> throw CompilerErr $ "Not a pair or unit: " ++ show xs

type BundleDesc = Int  -- length

bundleFold :: a -> (a -> a -> a) -> [a] -> (a, BundleDesc)
bundleFold empty pair els = case els of
  []  -> (empty, 0)
  [e] -> (e, 1)
  h:t -> (pair h tb, td + 1)
    where (tb, td) = bundleFold empty pair t

mkBundleTy :: [Type n] -> (Type n, BundleDesc)
mkBundleTy = bundleFold UnitTy PairTy

mkBundle :: [Atom n] -> (Atom n, BundleDesc)
mkBundle = bundleFold UnitVal PairVal

pattern FunTy :: Binder n l -> EffectRow l -> Type l -> Type n
pattern FunTy b eff bodyTy = Pi (PiType PlainArrow b eff bodyTy)

pattern BinaryFunTy :: Binder n l -> Binder l l' -> EffectRow l' -> Type l' -> Type n
pattern BinaryFunTy b1 b2 eff bodyTy = FunTy b1 Pure (FunTy b2 eff bodyTy)

-- -- === instances ===

instance TypesNotEqual AtomNameDef DataDef  where notEqProof = \case
instance TypesNotEqual AtomNameDef ClassDef where notEqProof = \case

-- right-biased, unlike the underlying Map
instance Semigroup (SourceMap n) where
  m1 <> m2 = SourceMap $ fromSourceMap m2 <> fromSourceMap m1

instance Monoid (SourceMap n) where
  mempty = SourceMap mempty

instance GenericE DataDef where
  type RepE DataDef = PairE (LiftE SourceName) (Abs (Nest Binder) (ListE DataConDef))
  fromE (DataDef name bs cons) = PairE (LiftE name) (Abs bs (ListE cons))
  toE   (PairE (LiftE name) (Abs bs (ListE cons))) = DataDef name bs cons
deriving instance (Show (DataDef n))
instance InjectableE DataDef
instance SubstE Name DataDef
instance SubstE AtomSubstVal DataDef
instance AlphaEqE DataDef

instance GenericE DataConDef where
  type RepE DataConDef = PairE (LiftE SourceName) (Abs (Nest Binder) UnitE)
  fromE (DataConDef name ab) = PairE (LiftE name) ab
  toE   (PairE (LiftE name) ab) = DataConDef name ab
instance InjectableE DataConDef
instance SubstE Name DataConDef
instance SubstE AtomSubstVal DataConDef
instance AlphaEqE DataConDef

instance GenericE MethodDef where
  type RepE MethodDef = PairE (Name ClassDef) (PairE (LiftE Int) Atom)
  fromE (MethodDef name idx getter) = PairE name (PairE (LiftE idx) getter)
  toE   (PairE name (PairE (LiftE idx) getter)) = MethodDef name idx getter
instance SubstE Name MethodDef
instance SubstE AtomSubstVal MethodDef
instance InjectableE MethodDef

instance GenericE SuperclassDef where
  type RepE SuperclassDef = PairE (Name ClassDef) (PairE (LiftE Int) Atom)
  fromE (SuperclassDef name idx getter) = PairE name (PairE (LiftE idx) getter)
  toE   (PairE name (PairE (LiftE idx) getter)) = SuperclassDef name idx getter
instance SubstE Name SuperclassDef
instance SubstE AtomSubstVal SuperclassDef
instance InjectableE SuperclassDef

instance GenericE DataConNameDef where
  type RepE DataConNameDef = PairE (Name DataDef) (LiftE Int)
  fromE (DataConNameDef name idx) = PairE name (LiftE idx)
  toE   (PairE name (LiftE idx)) = DataConNameDef name idx
instance SubstE Name DataConNameDef
instance SubstE AtomSubstVal DataConNameDef
instance InjectableE DataConNameDef

instance GenericE TyConNameDef where
  type RepE TyConNameDef = Name DataDef
  fromE (TyConNameDef name) = name
  toE   name = TyConNameDef name
instance SubstE Name TyConNameDef
instance SubstE AtomSubstVal TyConNameDef
instance InjectableE TyConNameDef

instance GenericE ClassDef where
  type RepE ClassDef = PairE (LiftE (SourceName, [SourceName])) (PairE (Name DataDef) DataDef)
  fromE (ClassDef className methodNames (dataDefName, dataDef)) =
          PairE (LiftE (className, methodNames)) (PairE dataDefName dataDef)
  toE (PairE (LiftE (className, methodNames)) (PairE dataDefName dataDef)) =
        ClassDef className methodNames (dataDefName, dataDef)
instance InjectableE ClassDef
instance SubstE Name ClassDef
instance SubstE AtomSubstVal ClassDef

instance GenericB DataConRefBinding where
  type RepB DataConRefBinding = BinderP Binder Atom
  fromB (DataConRefBinding b val) = b :> val
  toB   (b :> val) = DataConRefBinding b val
instance InjectableB DataConRefBinding
instance BindsNames DataConRefBinding
instance SubstB Name DataConRefBinding
instance SubstB AtomSubstVal DataConRefBinding
instance AlphaEqB DataConRefBinding
deriving instance Show (DataConRefBinding n l)
deriving instance Generic (DataConRefBinding n l)

newtype ExtLabeledItemsE (e1::E) (e2::E) (n::S) =
  ExtLabeledItemsE (ExtLabeledItems (e1 n) (e2 n))

instance GenericE Atom where
  type RepE Atom =
      EitherE5
              (EitherE2
                   -- We isolate the Var and ProjectElt cases (and reorder them
                   -- compared to the data definition) because they need special
                   -- handling when you substitute with atoms. The rest just act
                   -- like containers
  {- Var -}        AtomName
  {- ProjectElt -} ( LiftE (NE.NonEmpty Int) `PairE` AtomName )
            ) (EitherE4
  {- Lam -}        LamExpr
  {- Pi -}         PiType
  {- DataCon -}    ( LiftE (SourceName, Int)      `PairE`
                     PairE (Name DataDef) DataDef `PairE`
                     ListE Atom                   `PairE`
                     ListE Atom )
  {- TypeCon -}    ( PairE (Name DataDef) DataDef `PairE` ListE Atom )
            ) (EitherE5
  {- LabeledRow -} (ExtLabeledItemsE Type AtomName)
  {- Record -}     (ComposeE LabeledItems Atom)
  {- RecordTy -}   (ExtLabeledItemsE Type AtomName)
  {- Variant -}    ( ExtLabeledItemsE Type AtomName `PairE`
                     LiftE (Label, Int) `PairE` Atom )
  {- VariantTy -}  (ExtLabeledItemsE Type AtomName)
            ) (EitherE2
  {- Con -}        (ComposeE PrimCon Atom)
  {- TC -}         (ComposeE PrimTC  Atom)
            ) (EitherE4
  {- Eff -}        EffectRow
  {- ACase -}      ( Atom `PairE` ListE (AltP Atom) `PairE` Type )
  {- DataConRef -} ( PairE (Name DataDef) DataDef `PairE`
                     ListE Atom                   `PairE`
                     EmptyAbs (Nest DataConRefBinding) )
  {- BoxedRef -}   ( Atom `PairE` Block `PairE` Abs Binder Atom ))

  fromE atom = case atom of
    Var v -> Case0 (Case0 v)
    ProjectElt idxs x -> Case0 (Case1 (PairE (LiftE idxs) x))
    Lam lamExpr -> Case1 (Case0 lamExpr)
    Pi  piExpr  -> Case1 (Case1 piExpr)
    DataCon printName (defName, def) params con args -> Case1 $ Case2 $
      LiftE (printName, con) `PairE`
      PairE defName def      `PairE`
      ListE params           `PairE`
      ListE args
    TypeCon (defName, def) params ->
      Case1 $ Case3 $ PairE defName def `PairE` ListE params
    LabeledRow extItems -> Case2 $ Case0 $ ExtLabeledItemsE extItems
    Record items        -> Case2 $ Case1 $ ComposeE items
    RecordTy extItems   -> Case2 $ Case2 $ ExtLabeledItemsE extItems
    Variant extItems l con payload -> Case2 $ Case3 $
      ExtLabeledItemsE extItems `PairE` LiftE (l, con) `PairE` payload
    VariantTy extItems  -> Case2 $ Case4 $ ExtLabeledItemsE extItems
    Con con -> Case3 $ Case0 $ ComposeE con
    TC  con -> Case3 $ Case1 $ ComposeE con
    Eff effs -> Case4 $ Case0 $ effs
    ACase scrut alts ty -> Case4 $ Case1 $ scrut `PairE` ListE alts `PairE` ty
    DataConRef (defName, def) params bs ->
      Case4 $ Case2 $ PairE defName def `PairE` ListE params `PairE` bs
    BoxedRef ptr size ab ->
      Case4 $ Case3 $ ptr `PairE` size `PairE` ab

  toE atom = case atom of
    Case0 val -> case val of
      Case0 v -> Var v
      Case1 (PairE (LiftE idxs) x) -> ProjectElt idxs x
    Case1 val -> case val of
      Case0 lamExpr -> Lam lamExpr
      Case1 piExpr  -> Pi  piExpr
      Case2 ( LiftE (printName, con) `PairE`
              PairE defName def      `PairE`
              ListE params           `PairE`
              ListE args ) ->
        DataCon printName (defName, def) params con args
      Case3 (PairE defName def `PairE` ListE params) ->
        TypeCon (defName, def) params
    Case2 val -> case val of
      Case0 (ExtLabeledItemsE extItems) -> LabeledRow extItems
      Case1 (ComposeE items) -> Record items
      Case2 (ExtLabeledItemsE extItems) -> RecordTy extItems
      Case3 ( (ExtLabeledItemsE extItems) `PairE`
              LiftE (l, con)              `PairE`
              payload) -> Variant extItems l con payload
      Case4 (ExtLabeledItemsE extItems) -> VariantTy extItems
    Case3 val -> case val of
      Case0 (ComposeE con) -> Con con
      Case1 (ComposeE con) -> TC con
    Case4 val -> case val of
      Case0 effs -> Eff effs
      Case1 (scrut `PairE` ListE alts `PairE` ty) -> ACase scrut alts ty
      Case2 (PairE defName def `PairE` ListE params `PairE` bs) ->
        DataConRef (defName, def) params bs
      Case3 (ptr `PairE` size `PairE` ab) -> BoxedRef ptr size ab

instance InjectableE Atom
instance AlphaEqE Atom
instance SubstE Name Atom

instance SubstE AtomSubstVal Atom where
  substE atom = case fromE atom of
    LeftE specialCase -> case specialCase of
      -- Var
      Case0 v -> do
        substVal <- lookupEnvM v
        case substVal of
          Rename v' -> return $ Var v'
          SubstVal x -> return x
      -- ProjectElt
      Case1 (PairE (LiftE idxs) v) -> do
        substVal <- lookupEnvM v
        v' <- case substVal of
          SubstVal x -> return x
          Rename v'  -> return $ Var v'
        return $ getProjection (NE.toList idxs) v'
        where
          getProjection :: [Int] -> Atom n -> Atom n
          getProjection [] a = a
          getProjection (i:is) a = case getProjection is a of
            Var name -> ProjectElt (NE.fromList [i]) name
            ProjectElt idxs' a' -> ProjectElt (NE.cons i idxs') a'
            DataCon _ _ _ _ xs -> xs !! i
            Record items -> toList items !! i
            PairVal x _ | i == 0 -> x
            PairVal _ y | i == 1 -> y
            _ -> error $ "Not a valid projection: " ++ show i ++ " of " ++ show a
      Case1 _ -> error "impossible"
      _ -> error "impossible"
    RightE rest -> (toE . RightE) <$> substE rest

instance GenericE Expr where
  type RepE Expr =
     EitherE5
        (PairE Atom Atom)
        (PairE Atom (PairE (ListE Alt) Type))
        (Atom)
        (ComposeE PrimOp Atom)
        (ComposeE PrimHof Atom)
  fromE = \case
    App f e        -> Case0 (PairE f e)
    Case e alts ty -> Case1 (PairE e (PairE (ListE alts) ty))
    Atom x         -> Case2 (x)
    Op op          -> Case3 (ComposeE op)
    Hof hof        -> Case4 (ComposeE hof)

  toE = \case
    Case0 (PairE f e)                       -> App f e
    Case1 (PairE e (PairE (ListE alts) ty)) -> Case e alts ty
    Case2 (x)                               -> Atom x
    Case3 (ComposeE op)                     -> Op op
    Case4 (ComposeE hof)                    -> Hof hof
    _ -> error "impossible"

instance InjectableE Expr where
instance AlphaEqE Expr
instance SubstE Name Expr where
instance SubstE AtomSubstVal Expr where

instance GenericE (ExtLabeledItemsE e1 e2) where
  type RepE (ExtLabeledItemsE e1 e2) = EitherE (ComposeE LabeledItems e1)
                                               (ComposeE LabeledItems e1 `PairE` e2)
  fromE (ExtLabeledItemsE (Ext items Nothing))  = LeftE  (ComposeE items)
  fromE (ExtLabeledItemsE (Ext items (Just t))) = RightE (ComposeE items `PairE` t)

  toE (LeftE  (ComposeE items          )) = ExtLabeledItemsE (Ext items Nothing)
  toE (RightE (ComposeE items `PairE` t)) = ExtLabeledItemsE (Ext items (Just t))

instance (InjectableE e1, InjectableE e2) => InjectableE (ExtLabeledItemsE e1 e2)
instance (AlphaEqE    e1, AlphaEqE    e2) => AlphaEqE    (ExtLabeledItemsE e1 e2)
instance (SubstE Name e1, SubstE Name e2) => SubstE Name (ExtLabeledItemsE e1 e2)

instance SubstE AtomSubstVal (ExtLabeledItemsE Atom AtomName) where
  substE (ExtLabeledItemsE (Ext items maybeExt)) = do
    items' <- mapM substE items
    ext <- case maybeExt of
      Nothing -> return $ NoExt NoLabeledItems
      Just v ->
        lookupEnvM v >>= \case
          Rename        v'  -> return $ Ext NoLabeledItems $ Just v'
          SubstVal (Var v') -> return $ Ext NoLabeledItems $ Just v'
          SubstVal (LabeledRow row) -> return row
          _ -> error "Not a valid labeled row substitution"
    return $ ExtLabeledItemsE $ prefixExtLabeledItems items' ext

instance GenericE Block where
  type RepE Block = PairE Type (Abs (Nest Decl) Expr)
  fromE (Block ty decls result) = PairE ty (Abs decls result)
  toE   (PairE ty (Abs decls result)) = Block ty decls result
instance InjectableE Block
instance AlphaEqE Block
instance SubstE Name Block
instance SubstE AtomSubstVal Block
deriving instance Show (Block n)

instance GenericE LamExpr where
  type RepE LamExpr = PairE (LiftE Arrow) (Abs Binder (PairE EffectRow Block))
  fromE (LamExpr arr b effs block) = PairE (LiftE arr) (Abs b (PairE effs block))
  toE   (PairE (LiftE arr) (Abs b (PairE effs block))) = LamExpr arr b effs block
instance InjectableE LamExpr
instance AlphaEqE LamExpr
instance SubstE Name LamExpr
instance SubstE AtomSubstVal LamExpr
deriving instance Show (LamExpr n)

instance GenericE PiType where
  type RepE PiType = PairE (LiftE Arrow) (Abs Binder (PairE EffectRow Type))
  fromE (PiType arr b effs ty) = PairE (LiftE arr) (Abs b (PairE effs ty))
  toE   (PairE (LiftE arr) (Abs b (PairE effs ty))) = PiType arr b effs ty
instance InjectableE PiType
instance AlphaEqE PiType
instance SubstE Name PiType
instance SubstE AtomSubstVal PiType
deriving instance Show (PiType n)

instance GenericE (EffectP name) where
  type RepE (EffectP name) =
    EitherE (PairE (LiftE RWS) name)
            (LiftE (Either () ()))
  fromE = \case
    RWSEffect rws name -> LeftE  (PairE (LiftE rws) name)
    ExceptionEffect -> RightE (LiftE (Left  ()))
    IOEffect        -> RightE (LiftE (Right ()))
  toE = \case
    LeftE  (PairE (LiftE rws) name) -> RWSEffect rws name
    RightE (LiftE (Left  ())) -> ExceptionEffect
    RightE (LiftE (Right ())) -> IOEffect

instance InjectableE name => InjectableE (EffectP name)
instance AlphaEqE    name => AlphaEqE    (EffectP name)
instance SubstE Name (EffectP AtomName)
instance SubstE AtomSubstVal (EffectP AtomName) where
  substE eff = case eff of
    RWSEffect rws v -> do
      v' <- lookupEnvM v >>= \case
              Rename        v'  -> return v'
              SubstVal (Var v') -> return v'
              SubstVal _ -> error "Heap parameter must be a name"
      return $ RWSEffect rws v'
    ExceptionEffect -> return ExceptionEffect
    IOEffect        -> return IOEffect

instance OrdE name => GenericE (EffectRowP name) where
  type RepE (EffectRowP name) = PairE (ListE (EffectP name)) (MaybeE name)
  fromE (EffectRow effs ext) = ListE (S.toList effs) `PairE` ext'
    where ext' = case ext of Just v  -> JustE v
                             Nothing -> NothingE
  toE (ListE effs `PairE` ext) = EffectRow (S.fromList effs) ext'
    where ext' = case ext of JustE v  -> Just v
                             NothingE -> Nothing

instance InjectableE (EffectRowP AtomName)
instance SubstE Name (EffectRowP AtomName)
instance AlphaEqE    (EffectRowP AtomName)

instance SubstE AtomSubstVal (EffectRowP AtomName) where
  substE (EffectRow effs tailVar) = do
    effs' <- S.fromList <$> mapM substE (S.toList effs)
    tailEffRow <- case tailVar of
      Nothing -> return $ EffectRow mempty Nothing
      Just v -> lookupEnvM v >>= \case
        Rename        v'  -> return $ EffectRow mempty (Just v')
        SubstVal (Var v') -> return $ EffectRow mempty (Just v')
        SubstVal (Eff r)  -> return r
        _ -> error "Not a valid effect substitution"
    return $ extendEffRow effs' tailEffRow

instance GenericE SynthCandidates where
  type RepE SynthCandidates = PairE (ListE Atom) (PairE (ListE Atom) (ListE Atom))
  fromE (SynthCandidates xs ys zs) = PairE (ListE xs) (PairE (ListE ys) (ListE zs))
  toE   (PairE (ListE xs) (PairE (ListE ys) (ListE zs))) = SynthCandidates xs ys zs

instance InjectableE SynthCandidates
instance SubstE Name SynthCandidates
instance SubstE AtomSubstVal SynthCandidates

instance GenericE SourceNameDef where
  type RepE SourceNameDef =
     EitherE5
        (Name AtomNameDef)
        (Name TyConNameDef)
        (Name DataConNameDef)
        (Name ClassDef)
        (Name MethodDef)

  fromE = \case
    SrcAtomName    name -> Case0 name
    SrcTyConName   name -> Case1 name
    SrcDataConName name -> Case2 name
    SrcClassName   name -> Case3 name
    SrcMethodName  name -> Case4 name

  toE = \case
    Case0 name -> SrcAtomName    name
    Case1 name -> SrcTyConName   name
    Case2 name -> SrcDataConName name
    Case3 name -> SrcClassName   name
    Case4 name -> SrcMethodName  name
    _ -> error "impossible"

instance InjectableE SourceNameDef
instance SubstE Name SourceNameDef

instance SubstE Name EvaluatedModule where
  substE (EvaluatedModule bindings scs sourceMap) =
    withSubstB (RecEnvFrag bindings) \(RecEnvFrag bindings') ->
      EvaluatedModule bindings' <$> substE scs <*> substE sourceMap

instance GenericE AtomBinderInfo where
  type RepE AtomBinderInfo =
     EitherE5
        (PairE (LiftE LetAnn) Expr)
        (LiftE Arrow)
        UnitE
        UnitE
        UnitE

  fromE = \case
    LetBound ann e -> Case0 (PairE (LiftE ann) e)
    LamBound arr   -> Case1 (LiftE arr)
    PiBound        -> Case2 UnitE
    MiscBound      -> Case3 UnitE
    InferenceName  -> Case4 UnitE

  toE = \case
    Case0 (PairE (LiftE ann) e) -> LetBound ann e
    Case1 (LiftE arr)           -> LamBound arr
    Case2 UnitE                 -> PiBound
    Case3 UnitE                 -> MiscBound
    Case4 UnitE                 -> InferenceName
    _ -> error "impossible"

instance InjectableE AtomBinderInfo
instance SubstE Name AtomBinderInfo
instance SubstE AtomSubstVal AtomBinderInfo
instance AlphaEqE AtomBinderInfo

instance GenericE AtomNameDef where
  type RepE AtomNameDef = PairE Type AtomBinderInfo
  fromE (AtomNameDef ty info) = PairE ty info
  toE   (PairE ty info) = AtomNameDef ty info

instance InjectableE AtomNameDef
instance SubstE Name AtomNameDef
instance SubstE AtomSubstVal AtomNameDef
instance AlphaEqE AtomNameDef

instance GenericB Decl where
  type RepB Decl = BinderP Binder (PairE (LiftE LetAnn) Expr)
  fromB (Let ann b expr) = b :> PairE (LiftE ann) expr
  toB   (b :> PairE (LiftE ann) expr) = Let ann b expr

instance InjectableB Decl
instance SubstB AtomSubstVal Decl
instance SubstB Name Decl
instance AlphaEqB Decl
instance BindsNames Decl

instance Pretty Arrow where
  pretty arr = case arr of
    PlainArrow     -> "->"
    TabArrow       -> "=>"
    LinArrow       -> "--o"
    ImplicitArrow  -> "?->"
    ClassArrow     -> "?=>"

instance Semigroup (SynthCandidates n) where
  SynthCandidates xs ys zs <> SynthCandidates xs' ys' zs' =
    SynthCandidates (xs<>xs') (ys<>ys') (zs<>zs')

instance Monoid (SynthCandidates n) where
  mempty = SynthCandidates mempty mempty mempty

instance InjectableE (TopBinding e) where
  injectionProofE fresh (TopBinding e) = TopBinding $ injectionProofE fresh e

instance SubstE Name (TopBinding e) where
  substE (TopBinding e) = TopBinding <$> substE e

instance SubstE AtomSubstVal (TopBinding e) where
  substE (TopBinding e) = TopBinding <$> substE e

instance Show (TopBindings n)

instance GenericE SourceMap where
  type RepE SourceMap = ListE (PairE (LiftE SourceName) SourceNameDef)
  fromE (SourceMap m) = ListE [PairE (LiftE v) def | (v, def) <- M.toList m]
  toE   (ListE pairs) = SourceMap $ M.fromList [(v, def) | (PairE (LiftE v) def) <- pairs]

instance InjectableE SourceMap
instance SubstE Name SourceMap

instance Pretty (SourceMap n) where
  pretty (SourceMap m) =
    fold [pretty v <+> "@>" <+> pretty x <> hardline | (v, x) <- M.toList m ]

instance Pretty (SourceNameDef n) where
  pretty def = case def of
   SrcAtomName    name -> "atom name:"        <+> pretty name
   SrcTyConName   name -> "type constructor:" <+> pretty name
   SrcDataConName name -> "data constructor:" <+> pretty name
   SrcClassName   name -> "class name:"       <+> pretty name
   SrcMethodName  name -> "method name:"      <+> pretty name

instance Pretty (TopBinding s n) where
  pretty (TopBinding x) = prettyTypeOf x

prettyTypeOf :: forall (n::S) (e::E) ann . Typeable e => e n -> Doc ann
prettyTypeOf _ = pretty $ show (typeRep :: TypeRep e)

instance Pretty (TopBindings n) where
  pretty (TopBindings env) = pretty env

instance Pretty (TopState n) where
  pretty s =
    "bindings: "        <> nest 2 (hardline <> pretty (topBindings s))  <> hardline <>
    "synth candidates:" <> hardline <>
    "source map: "      <> nest 2 (hardline <> pretty (topSourceMap s)) <> hardline

instance Generic (Block n) where
  type Rep (Block n) = Rep (PairE Type (Abs (Nest Decl) Expr) n)
  from (Block ty decls result) = from $ PairE ty $ Abs decls result
  to rep = case to rep of
    PairE ty (Abs decls result) -> Block ty decls result

instance Generic (LamExpr n) where
  type Rep (LamExpr n) = Rep (Arrow, Abs Binder (PairE EffectRow Block) n)
  from (LamExpr arr b row block) = from (arr, Abs b (PairE row block))
  to rep = case to rep of
    (arr, Abs b (PairE row block)) -> LamExpr arr b row block

instance Generic (PiType n) where
  type Rep (PiType n) = Rep (Arrow, Abs Binder (PairE EffectRow Type) n)
  from (PiType arr b row ty) = from (arr, Abs b (PairE row ty))
  to rep = case to rep of
    (arr, Abs b (PairE row ty)) -> PiType arr b row ty

instance Generic (DataDef n) where
  type Rep (DataDef n) = Rep (SourceName, Abs (Nest Binder) (ListE DataConDef) n)
  from (DataDef name bs dataCons) = from (name, Abs bs (ListE dataCons))
  to rep = case to rep of
    (name, Abs bs (ListE dataCons)) -> DataDef name bs dataCons

instance Store (Atom n)
instance Store (Expr n)
instance Store (AtomBinderInfo n)
instance Store (AtomNameDef n)
instance Store (Decl n l)
instance Store (DataDef n)
instance Store (DataConDef n)
instance Store (Block n)
instance Store (LamExpr n)
instance Store (PiType  n)
instance Store Arrow
instance Store (SourceNameDef n)
instance Store (TyConNameDef   n)
instance Store (DataConNameDef n)
instance Store (ClassDef       n)
instance Store (MethodDef      n)
instance Store (SuperclassDef  n)
instance Store (SourceMap n)
instance Store (SynthCandidates n)
instance Store (EffectRow n)
instance Store (Effect n)
instance Store (DataConRefBinding n l)

instance IsString (SourceNameOr a VoidS) where
  fromString = SourceName

instance IsString (UBinder s VoidS VoidS) where
  fromString = UBindSource

instance IsString (UPat' VoidS VoidS) where
  fromString = UPatBinder . fromString

instance IsString (UPatAnn VoidS VoidS) where
  fromString s = UPatAnn (fromString s) Nothing

instance IsString (UExpr' VoidS) where
  fromString = UVar . fromString

instance IsString (a n) => IsString (WithSrcE a n) where
  fromString = WithSrcE Nothing . fromString

instance IsString (b n l) => IsString (WithSrcB b n l) where
  fromString = WithSrcB Nothing . fromString

instance FromSourceNameDef AtomNameDef where
  fromSourceNameDef (SrcAtomName name) = Just name
  fromSourceNameDef _ = Nothing

instance FromSourceNameDef TyConNameDef where
  fromSourceNameDef (SrcTyConName name) = Just name
  fromSourceNameDef _ = Nothing

instance FromSourceNameDef DataConNameDef where
  fromSourceNameDef (SrcDataConName name) = Just name
  fromSourceNameDef _ = Nothing

instance FromSourceNameDef ClassDef where
  fromSourceNameDef (SrcClassName name) = Just name
  fromSourceNameDef _ = Nothing

instance FromSourceNameDef MethodDef where
  fromSourceNameDef (SrcMethodName name) = Just name
  fromSourceNameDef _ = Nothing

deriving instance Show (UBinder s n l)
deriving instance Show (UDataDefTrail n)
deriving instance Show (ULamExpr n)
deriving instance Show (UPiExpr n)
deriving instance Show (UDeclExpr n)
deriving instance Show (UDataDef n)
deriving instance Show (UDecl n l)
deriving instance Show (UForExpr n)
deriving instance Show (UAlt n)
