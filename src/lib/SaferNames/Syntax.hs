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

module SaferNames.Syntax (
    Type, Kind, BaseType (..), ScalarBaseType (..), Except,
    EffectP (..), Effect, UEffect, RWS (..), EffectRowP (..), EffectRow, UEffectRow,
    SrcPos, Binder (..), Block (..), Decl (..),
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
import Util (zipErr)
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

data Binder (n::S) (l::S) =
  (:>) (NameBinder AtomNameDef n l) (Type n)
  deriving (Show, Generic)

data DataConRefBinding n l =
  DataConRefBinding (Binder n l) (Atom n)
  deriving (Show, Generic)

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
 | UPatPair (NestPair UPat UPat n l)
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

-- This cuts down boilerplate by letting us share a single instance for `SubstE
-- Name` and `SubstE AtomSubstVal`
class InjectableToAtomSubstVal (v::E->E) where
  injectToAtomSubstVal :: v s n -> AtomSubstVal s n

instance (InjectableToAtomSubstVal AtomSubstVal) where
  injectToAtomSubstVal = id

instance (InjectableToAtomSubstVal Name) where
  injectToAtomSubstVal = Rename

lookupAtomSubstVal :: (EnvReader v m, Typeable s, InjectableE s, InjectableToAtomSubstVal v)
                   => Name s i -> m i o (AtomSubstVal s o)
lookupAtomSubstVal name = injectToAtomSubstVal <$> lookupEnvM name

-- right-biased, unlike the underlying Map
instance Semigroup (SourceMap n) where
  m1 <> m2 = SourceMap $ fromSourceMap m2 <> fromSourceMap m1

instance Monoid (SourceMap n) where
  mempty = SourceMap mempty

ipe :: InjectableE e => InjectionCoercion n l -> e n -> e l
ipe = injectionProofE

(<++>) :: String -> String -> String
(<++>) s1 s2 = s1 <> " " <> s2

showParens :: Show a => a -> String
showParens x = "(" <> show x <> ")"

instance Show (DataDef n) where
  show (DataDef name bs cons) =
    "DataDef" <++> showParens name <++> showParens bs <++> showParens cons

instance InjectableE SourceMap where
  injectionProofE c (SourceMap m) = SourceMap $ injectionProofE c `fmap` m

instance InjectableE SourceNameDef where
  injectionProofE c (SrcAtomName n) = SrcAtomName $ injectionProofE c n
  injectionProofE c (SrcTyConName n) = SrcTyConName $ injectionProofE c n
  injectionProofE c (SrcDataConName n) = SrcDataConName $ injectionProofE c n
  injectionProofE c (SrcClassName n) = SrcClassName $ injectionProofE c n
  injectionProofE c (SrcMethodName n) = SrcMethodName $ injectionProofE c n

instance InjectableE DataDef where
  injectionProofE fresh (DataDef name bs cons) =
    case injectionProofE fresh (Abs bs (ListE cons)) of
      Abs bs' (ListE cons') -> DataDef name bs' cons'

instance InjectableToAtomSubstVal v => SubstE v DataDef where
  substE (DataDef name bs cons) =
    substE (Abs bs (ListE cons)) >>= \case
      Abs bs' (ListE cons') -> return $ DataDef name bs' cons'

instance InjectableE DataConDef where
  injectionProofE fresh (DataConDef name ab) = DataConDef name $ ipe fresh ab

instance InjectableToAtomSubstVal v => SubstE v DataConDef where
  substE (DataConDef name ab) = DataConDef name <$> substE ab

instance InjectableToAtomSubstVal v => SubstE v MethodDef where
instance InjectableE MethodDef where

instance InjectableToAtomSubstVal v => SubstE v SuperclassDef where
instance InjectableE SuperclassDef where

instance InjectableToAtomSubstVal v => SubstE v DataConNameDef where
instance InjectableE DataConNameDef where

instance InjectableToAtomSubstVal v => SubstE v TyConNameDef where
instance InjectableE TyConNameDef where

instance InjectableToAtomSubstVal v => SubstE v ClassDef where
instance InjectableE ClassDef where

instance InjectableB DataConRefBinding where
  injectionProofB f (DataConRefBinding b ref) cont = do
    let ref' = ipe f ref
    injectionProofB f b \f' b' -> cont f' $ DataConRefBinding b' ref'

instance BindsNames DataConRefBinding where
  toScopeFrag (DataConRefBinding b _) = toScopeFrag b

instance InjectableToAtomSubstVal v => SubstB v DataConRefBinding where
  substB (DataConRefBinding b ref) =
    substE ref `liftSG` \ref' ->
    substB b   `bindSG` \b' ->
    returnSG $ DataConRefBinding b' ref'

instance InjectableE Atom where
  injectionProofE f atom = case atom of
    Var name -> Var $ ipe f name
    Lam lam  -> Lam $ ipe f lam
    Pi  piTy -> Pi  $ ipe f piTy
    DataCon printName (defName, def) params con args ->
      DataCon printName (ipe f defName, ipe f def) (fmap (ipe f) params) con (fmap (ipe f) args)
    TypeCon (defName, def) params ->
      TypeCon (ipe f defName, ipe f def) (fmap (ipe f) params)
    LabeledRow (Ext items ext) -> LabeledRow $ Ext (fmap (ipe f) items) (fmap (ipe f) ext)
    Record items -> Record $ fmap (ipe f) items
    RecordTy (Ext items ext) -> RecordTy $ Ext (fmap (ipe f) items) (fmap (ipe f) ext)
    Variant (Ext items ext) l con payload -> do
      let extItems = Ext (fmap (ipe f) items) (fmap (ipe f) ext)
      Variant extItems l con $ ipe f payload
    VariantTy (Ext items ext) -> VariantTy $
      Ext (fmap (ipe f) items) (fmap (ipe f) ext)
    Con con -> Con $ fmap (ipe f) con
    TC  tc  -> TC  $ fmap (ipe f) tc
    Eff eff -> Eff $ ipe f eff
    ACase scrut alts ty -> ACase (ipe f scrut) (fmap (ipe f) alts) (ipe f ty)
    DataConRef (defName, def) params bs ->
      DataConRef (ipe f defName, ipe f def) (fmap (ipe f) params) (ipe f bs)
    BoxedRef ptr size ab -> BoxedRef (ipe f ptr) (ipe f size) (ipe f ab)
    ProjectElt idxs x -> ProjectElt idxs $ ipe f x

instance InjectableToAtomSubstVal v => SubstE v Atom where
  substE atom = case atom of
    Var v -> lookupAtomSubstVal v >>= \case
               SubstVal x -> return x
               Rename v' -> return $ Var v'
    Lam ab -> Lam <$> substE ab
    Pi  ab -> Pi  <$> substE ab
    DataCon printName def params con args ->
      DataCon printName <$> substDataDefName def <*> mapM substE params
                        <*> pure con <*> mapM substE args
    TypeCon def params -> TypeCon <$> substDataDefName def <*> mapM substE params
    LabeledRow (Ext items ext) -> (LabeledRow <$>) $
      prefixExtLabeledItems <$> mapM substE items <*> substTail ext
    Record items -> Record <$> mapM substE items
    RecordTy (Ext items ext) -> (RecordTy <$>) $
      prefixExtLabeledItems <$> mapM substE items <*> substTail ext
    Variant (Ext items ext) l con payload -> do
      extItems <- prefixExtLabeledItems <$> mapM substE items <*> substTail ext
      payload' <- substE payload
      return $ Variant extItems l con payload'
    VariantTy (Ext items ext) -> (VariantTy <$>) $
      prefixExtLabeledItems <$> mapM substE items <*> substTail ext
    Con con -> Con <$> traverse substE con
    TC  con -> TC  <$> traverse substE con
    Eff effs -> Eff <$> substE effs
    ACase scrut alts ty -> ACase <$> substE scrut <*> traverse substE alts <*> substE ty
    DataConRef def params bs -> DataConRef <$> substDataDefName def <*> mapM substE params <*> substE bs
    BoxedRef ptr size ab -> BoxedRef <$> substE ptr <*> substE size <*> substE ab
    ProjectElt idxs v -> do
      v' <- lookupAtomSubstVal v >>= \case
              SubstVal x -> return x
              Rename v'  -> return $ Var v'
      return $ getProjection (NE.toList idxs) v'
    where
      substTail
        :: InjectableToAtomSubstVal v => EnvReader v m
        => Maybe (AtomName i)
        -> m i o (ExtLabeledItems (Atom o) (AtomName o))
      substTail Nothing = return $ NoExt NoLabeledItems
      substTail (Just v) =
        lookupAtomSubstVal v >>= \case
          Rename        v'  -> return $ Ext NoLabeledItems $ Just v'
          SubstVal (Var v') -> return $ Ext NoLabeledItems $ Just v'
          SubstVal (LabeledRow row) -> return row
          _ -> error "Not a valid labeled row substitution"

      getProjection :: [Int] -> Atom n -> Atom n
      getProjection [] a = a
      getProjection (i:is) a = case getProjection is a of
        Var v -> ProjectElt (NE.fromList [i]) v
        ProjectElt idxs' a' -> ProjectElt (NE.cons i idxs') a'
        DataCon _ _ _ _ xs -> xs !! i
        Record items -> toList items !! i
        PairVal x _ | i == 0 -> x
        PairVal _ y | i == 1 -> y
        _ -> error $ "Not a valid projection: " ++ show i ++ " of " ++ show a

substDataDefName :: (InjectableToAtomSubstVal v, EnvReader v m, ScopeReader2 m,
                     ScopeExtender2 m, Renamer m)
                 => NamedDataDef i -> m i o (NamedDataDef o)
substDataDefName (name, def) = do
  def' <- substE def
  lookupAtomSubstVal name >>= \case
    Rename name' -> return (name', def')

instance AlphaEqE Atom where
  alphaEqE atom1 atom2 = case (atom1, atom2) of
    (Var v, Var v') -> alphaEqE v v'
    (Pi ab, Pi ab') -> alphaEqE ab ab'
    (DataCon _ (def,_) params con args, DataCon _ (def',_) params' con' args') -> do
      alphaEqE def def'
      alphaEqTraversable params params'
      assertEq con con' ""
      alphaEqTraversable args args'
    (TypeCon (def, _) params, TypeCon (def', _) params') -> do
      alphaEqE def def'
      alphaEqTraversable params params'
    (Variant (Ext items  ext ) l  con  payload ,
     Variant (Ext items' ext') l' con' payload') -> do
      alphaEqTraversable items items'
      alphaEqTraversable ext ext'
      alphaEqE payload payload'
      assertEq l l' ""
      assertEq con con' ""
    (Record items, Record items') ->
      alphaEqTraversable items items'
    (RecordTy (Ext items ext), RecordTy (Ext items' ext')) -> do
      alphaEqTraversable items items'
      alphaEqTraversable ext ext'
    (VariantTy (Ext items ext), VariantTy (Ext items' ext')) -> do
      alphaEqTraversable items items'
      alphaEqTraversable ext ext'
    (Con con, Con con') -> alphaEqTraversable con con'
    (TC  con, TC  con') -> alphaEqTraversable con con'
    (Eff eff, Eff eff') -> alphaEqE eff eff'
    (ProjectElt idxs v, ProjectElt idxs' v') -> do
      assertEq idxs idxs' ""
      alphaEqE v v'
    _ -> zipErr

instance InjectableE Expr where
  injectionProofE f expr = case expr of
    App e1 e2 -> App (ipe f e1) (ipe f e2)
    Case scrut alts ty -> Case (ipe f scrut) (fmap (ipe f) alts) (ipe f ty)
    Atom atom -> Atom $ ipe f atom
    Op  op  -> Op  $ fmap (ipe f) op
    Hof hof -> Hof $ fmap (ipe f) hof

instance InjectableToAtomSubstVal v => SubstE v Expr where
  substE expr = case expr of
    App e1 e2 -> App <$> substE e1 <*> substE e2
    Case scrut alts ty ->
      Case <$> substE scrut <*> traverse substE alts <*> substE ty
    Atom atom -> Atom <$> substE atom
    Op  op  -> Op  <$> traverse substE op
    Hof hof -> Hof <$> traverse substE hof

instance AlphaEqE Expr where
  alphaEqE expr1 expr2 = case (expr1, expr2) of
    (App e1 e2, App e1' e2') -> do
      alphaEqE e1 e1'
      alphaEqE e2 e2'
    (Case scrut alts ty, Case scrut' alts' ty') -> do
      alphaEqE scrut scrut'
      alphaEqTraversable alts alts'
      alphaEqE ty ty'
    (Atom atom, Atom atom') -> alphaEqE atom atom'
    (Op op, Op op') -> alphaEqTraversable op op'
    (Hof hof, Hof hof') -> alphaEqTraversable hof hof'
    _ -> zipErr

instance Show (Block n) where
  show (Block ty decls result) =
    "Block" <++> showParens ty <++> showParens decls <++> showParens result

instance InjectableE Block where
  injectionProofE fresh (Block resultTy decls result) = do
    let resultTy' = (ipe fresh resultTy)
    case ipe fresh $ Abs decls result of
      Abs decls' result' -> Block resultTy' decls' result'

instance InjectableToAtomSubstVal v => SubstE v Block where
  substE (Block resultTy decls result) = do
    resultTy' <- substE resultTy
    Abs decls' result' <- substE (Abs decls result)
    return $ Block resultTy' decls' result'

instance AlphaEqE Block where
  alphaEqE (Block resultTy  decls  result )
           (Block resultTy' decls' result') = do
    alphaEqE resultTy resultTy'
    alphaEqE (Abs decls result) (Abs decls' result')

instance Show (LamExpr n) where
  show (LamExpr arr b eff body) =
    "LamExpr" <++> showParens arr <++> showParens b <++> showParens eff <++> showParens body

instance InjectableE LamExpr where
  injectionProofE fresh (LamExpr arr b eff body) = do
    case ipe fresh $ Abs b (PairE eff body) of
      Abs b' (PairE eff' body') -> LamExpr arr b' eff' body'

instance AlphaEqE LamExpr where
  alphaEqE (LamExpr arr  b  eff  body )
           (LamExpr arr' b' eff' body') = do
    assertEq arr arr' ""
    alphaEqE (Abs b  (PairE eff  body ))
             (Abs b' (PairE eff' body'))

instance InjectableToAtomSubstVal v => SubstE v LamExpr where
  substE (LamExpr arr b eff body) = do
    Abs b' (PairE eff' body') <- substE $ Abs b (PairE eff body)
    return $ LamExpr arr b' eff' body'

instance Show (PiType n) where
  show (PiType arr b eff body) =
    "Pi" <++> showParens arr <++> showParens b <++> showParens eff <++> showParens body

instance InjectableE PiType where
  injectionProofE f (PiType arr b eff body) =
    injectionProofB f b \f' b' ->
      PiType arr b' (ipe f' eff) (ipe f' body)

instance AlphaEqE PiType where
  alphaEqE (PiType arr  b  eff  resultTy )
           (PiType arr' b' eff' resultTy') = do
    assertEq arr arr' ""
    alphaEqE (Abs b  (PairE eff  resultTy ))
             (Abs b' (PairE eff' resultTy'))

instance InjectableToAtomSubstVal v => SubstE v PiType where
  substE (PiType arr b eff bodyTy) = do
    Abs b' (PairE eff' bodyTy') <- substE $ Abs b (PairE eff bodyTy)
    return $ PiType arr b' eff' bodyTy'

instance InjectableE Effect where
  injectionProofE f eff = case eff of
    RWSEffect rws v -> RWSEffect rws $ ipe f v
    ExceptionEffect -> ExceptionEffect
    IOEffect        -> IOEffect

instance InjectableToAtomSubstVal v => SubstE v Effect where
  substE eff = case eff of
    RWSEffect rws v -> do
      v' <- lookupAtomSubstVal v >>= \case
              Rename        v'  -> return v'
              SubstVal (Var v') -> return v'
              SubstVal _ -> error "Heap parameter must be a name"
      return $ RWSEffect rws v'
    ExceptionEffect -> return ExceptionEffect
    IOEffect        -> return IOEffect

instance AlphaEqE Effect where
  alphaEqE eff eff' = case (eff, eff') of
    (RWSEffect rws v, RWSEffect rws' v') -> do
      assertEq rws rws' ""
      alphaEqE v v'
    (ExceptionEffect, ExceptionEffect) -> return ()
    (IOEffect       , IOEffect       ) -> return ()
    _ -> zipErr

instance InjectableE EffectRow where
  injectionProofE f (EffectRow effs tailVar) = do
    let effs' = S.fromList $ fmap (ipe f) (S.toList effs)
    let tailVar' = fmap (ipe f) tailVar
    EffectRow effs' tailVar'

instance InjectableToAtomSubstVal v => SubstE v EffectRow where
  substE (EffectRow effs tailVar) = do
    effs' <- S.fromList <$> mapM substE (S.toList effs)
    tailEffRow <- case tailVar of
      Nothing -> return $ EffectRow mempty Nothing
      Just v -> lookupAtomSubstVal v >>= \case
        Rename        v'  -> return $ EffectRow mempty (Just v')
        SubstVal (Var v') -> return $ EffectRow mempty (Just v')
        SubstVal (Eff r)  -> return r
        _ -> error "Not a valid effect substitution"
    return $ extendEffRow effs' tailEffRow

instance AlphaEqE EffectRow where
  alphaEqE (EffectRow effs tailVar) (EffectRow effs' tailVar') = do
    alphaEqTraversable (S.toList effs) (S.toList effs')
    alphaEqTraversable tailVar tailVar'

instance BindsNames Binder where
  toScopeFrag (b:>_) = toScopeFrag b

instance InjectableB Binder where
  injectionProofB f (b:>ty) cont = do
    let ty' = injectionProofE f ty
    injectionProofB f b \f' b' -> cont f' (b':>ty')

instance SubstB Name Binder where
  substB (b:>ty) =
    substE ty `liftSG` \ty' ->
    substB b  `bindSG` \b' ->
    returnSG $ b':>ty'

instance InjectableToAtomSubstVal v => SubstB v Binder where
  substB (b:>ty) =
    substE ty `liftSG` \ty' ->
    substB b  `bindSG` \b' ->
    returnSG $ b':>ty'

instance AlphaEqB Binder where
  withAlphaEqB (b1:>ty1) (b2:>ty2) cont = do
    alphaEqE ty1 ty2
    withAlphaEqB b1 b2 cont

instance BindsOneName Binder AtomNameDef where
  (b:>_) @> x = b @> x
  binderName (b:>_) = binderName b


instance InjectableToAtomSubstVal v => SubstE v SynthCandidates where
  substE (SynthCandidates xs ys zs) =
    SynthCandidates <$> mapM substE xs <*> mapM substE ys <*> mapM substE zs

instance SubstE Name SourceNameDef where
  substE def = case def of
    SrcAtomName    v -> SrcAtomName    <$> substE v
    SrcTyConName   v -> SrcTyConName   <$> substE v
    SrcDataConName v -> SrcDataConName <$> substE v
    SrcClassName   v -> SrcClassName   <$> substE v
    SrcMethodName  v -> SrcMethodName  <$> substE v

instance SubstE Name SourceMap where
  substE (SourceMap m) = SourceMap <$> mapM substE m

instance SubstE Name EvaluatedModule where
  substE (EvaluatedModule bindings scs sourceMap) =
    withSubstB (RecEnvFrag bindings) \(RecEnvFrag bindings') ->
      EvaluatedModule bindings' <$> substE scs <*> substE sourceMap

instance InjectableE AtomBinderInfo where
  injectionProofE f info = case info of
    LetBound ann expr -> LetBound ann (ipe f expr)
    LamBound arr  -> LamBound arr
    PiBound       -> PiBound
    MiscBound     -> MiscBound
    InferenceName -> InferenceName

instance InjectableToAtomSubstVal v => SubstE v AtomBinderInfo where
  substE info = case info of
    LetBound ann expr -> LetBound ann <$> substE expr
    LamBound arr  -> return $ LamBound arr
    PiBound       -> return PiBound
    MiscBound     -> return MiscBound
    InferenceName -> return InferenceName

instance AlphaEqE AtomBinderInfo where
  alphaEqE info1 info2 = case (info1, info2) of
    (LetBound ann expr, LetBound ann' expr') -> do
      assertEq ann ann' ""
      alphaEqE expr expr'
    (LamBound arr , LamBound arr') -> assertEq arr arr' ""
    (PiBound      , PiBound      ) -> return ()
    (InferenceName, InferenceName) -> return ()
    (MiscBound    , MiscBound    ) -> return ()
    _ -> zipErr

instance InjectableE AtomNameDef where
  injectionProofE f (AtomNameDef ty info) =
    AtomNameDef (ipe f ty) (ipe f info)

instance InjectableToAtomSubstVal v => SubstE v AtomNameDef where
  substE (AtomNameDef ty info) =
    AtomNameDef <$> substE ty <*> substE info

instance AlphaEqE AtomNameDef where
  alphaEqE (AtomNameDef ty info) (AtomNameDef ty' info') = do
    alphaEqE ty ty'
    alphaEqE info info'

instance InjectableB Decl where
  injectionProofB f (Let ann b expr) cont = do
    let expr' = ipe f expr
    injectionProofB f b \f' b' -> cont f' $ Let ann b' expr'

instance InjectableToAtomSubstVal v => SubstB v Decl where
  substB (Let ann b expr) =
    substE expr `liftSG` \expr' ->
    substB b    `bindSG` \b' ->
    returnSG $ Let ann b' expr'

instance BindsNames Decl where
  toScopeFrag (Let _ b _) = toScopeFrag b

instance AlphaEqB Decl where
  withAlphaEqB (Let ann b expr) (Let ann' b' expr') cont = do
    assertEq ann ann' ""
    alphaEqE expr expr'
    withAlphaEqB b b' cont

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
instance Store (Binder n l)
instance Store (DataConRefBinding n l)
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

instance Eq (a n) => Eq (SourceNameOr (a::E) (n::S)) where
  (SourceName name1) == (SourceName name2) = name1 == name2
  (InternalName name1) == (InternalName name2) = name1 == name2
  _ == _ = False

instance Ord (a n) => Ord (SourceNameOr a n) where
  (SourceName name1) `compare` (SourceName name2) = name1 `compare` name2
  (InternalName name1) `compare` (InternalName name2) = name1 `compare` name2
  (SourceName _) `compare` (InternalName _) = LT
  (InternalName _) `compare` (SourceName _) = GT

instance Show (SourceNameOr a n) where
  show = undefined

instance Show (UBinder s n l) where
  show = undefined

instance Show (ULamExpr n) where
  show = undefined

instance Show (UPiExpr n) where
  show = undefined

instance Show (UDeclExpr n) where
  show = undefined

instance Show (UDataDef n) where
  show = undefined

instance Show (UDecl n l) where
  show = undefined

instance Show (UForExpr n) where
  show = undefined

instance Show (UAlt n) where
  show = undefined
