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

module SaferNames.Syntax (
    Type, Kind, BaseType (..), ScalarBaseType (..),
    Effect (..), RWS (..), EffectRow (..),
    SrcPos, Binder, BinderList, Block (..), Decl (..),
    Expr (..), Atom (..), ArrowP (..), Arrow, PrimTC (..), Abs (..),
    PrimExpr (..), PrimCon (..), LitVal (..), PrimEffect (..), PrimOp (..),
    PrimHof (..), LamExpr, PiType, LetAnn (..),
    LamBinder (..), PiBinder (..), AltBinder (..),
    BinOp (..), UnOp (..), CmpOp (..), SourceNameMap (..),
    ForAnn (..), Val, Op, Con, Hof, TC, Module (..), EvaluatedModule (..),
    DataConRefBinding (..),
    AltP, Alt, AtomBinderInfo (..), TypedBinderInfo (..),
    SubstE (..), SubstB (..), Ptr, PtrType,
    AddressSpace (..), Device (..), showPrimName, strToPrimName, primNameToStr,
    Direction (..), Limit (..), DataDef (..), DataConDef (..), Nest (..), IndexStructure,
    mkConsList, mkConsListTy, fromConsList, fromConsListTy, fromLeftLeaningConsListTy,
    mkBundle, mkBundleTy, BundleDesc,
    BaseMonoidP (..), BaseMonoid, getIntLit, getFloatLit, sizeOf, ptrSize, vectorWidth,
    IRVariant (..), SubstVal (..), AtomName, AtomSubstVal,
    pattern IdxRepTy, pattern IdxRepVal, pattern TagRepTy,
    pattern TagRepVal, pattern Word8Ty,
    pattern UnitTy, pattern PairTy, pattern FunTy, pattern PiTy,
    pattern FixedIntRange, pattern Fin, pattern RefTy, pattern RawRefTy,
    pattern BaseTy, pattern PtrTy, pattern UnitVal,
    pattern PairVal, pattern PureArrow,
    pattern TyKind, pattern LamVal,
    pattern TabTy, pattern TabTyAbs, pattern TabVal,
    pattern Pure, pattern BinaryFunTy,
    pattern LabeledRowKind, pattern EffKind,
    (-->), (?-->), (--@), (==>) ) where

import Control.Monad.Except hiding (Except)
import qualified Data.List.NonEmpty    as NE
import qualified Data.Map.Strict       as M
import qualified Data.Set              as S
import qualified Data.Text             as T
import Data.Int
import Data.Word
import Foreign.Ptr

import Syntax
  ( ArrowP (..), LetAnn (..), IRVariant (..)
  , PrimExpr (..), PrimTC (..), PrimCon (..), PrimOp (..), PrimHof (..)
  , BaseMonoid, BaseMonoidP (..), PrimEffect (..), BinOp (..), UnOp (..)
  , CmpOp (..), Direction (..)
  , ForAnn (..), Limit (..), strToPrimName, primNameToStr, showPrimName
  , RWS (..), LitVal (..), ScalarBaseType (..), BaseType (..)
  , AddressSpace (..), Device (..), PtrType, sizeOf, ptrSize, vectorWidth)

import SaferNames.Name
import Err
import LabeledItems

-- === core IR ===

data Atom n =
   Var (AtomName n)
 | Lam (LamExpr n)
 | Pi  (PiType  n)
 | DataCon (Name DataDef n) [Atom n] Int [Atom n]
 | TypeCon (Name DataDef n) [Atom n]
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
 | DataConRef (Name DataDef n) [Atom n] (EmptyAbs (Nest DataConRefBinding) n)
 | BoxedRef (Atom n) (Block n) (Abs Binder Atom n)  -- ptr, size, binder/body
 -- access a nested member of a binder
 -- XXX: Variable name must not be an alias for another name or for
 -- a statically-known atom. This is because the variable name used
 -- here may also appear in the type of the atom. (We maintain this
 -- invariant during substitution and in Builder.hs.)
 | ProjectElt (NE.NonEmpty Int) (AtomName n)
   deriving (Show)

data Expr n =
   App (Atom n) (Atom n)
 | Case (Atom n) [Alt n] (Type n)
 | Atom (Atom n)
 | Op  (Op  n)
 | Hof (Hof n)
   deriving (Show)

data AtomBinderInfo (n::S) =
   LetBound LetAnn (Expr n)
 | LamBound (ArrowP ())
 | PiBound
 | AltBound
 | InferenceName

data TypedBinderInfo (n::S) = TypedBinderInfo (Type n) (AtomBinderInfo n)

data Decl n l = Let LetAnn (Binder n l) (Expr n)
                deriving (Show)

type AtomName   = Name TypedBinderInfo
type Binder     = AnnBinderP (PlainBinder     TypedBinderInfo)        Type   :: B
type BinderList = AnnBinderP (PlainBinderList TypedBinderInfo) (ListE Type)  :: B

data DataConRefBinding n l = DataConRefBinding (Binder n l) (Atom n) deriving Show

type AltP (e::E) = Abs (Nest AltBinder) e :: E
type Alt = AltP Block                  :: E

data DataDef n where
  -- The `RawName` is just for pretty-printing. The actual alpha-renamable
  -- binder name is in UExpr and Bindings
  DataDef :: RawName -> BinderList n l -> [DataConDef l] -> DataDef n

-- As above, the `RawName` is just for pretty-printing
data DataConDef n = DataConDef RawName (EmptyAbs (Nest Binder) n)
                    deriving Show

data Block n where Block :: Type n -> Nest Decl n l ->  Expr l -> Block n

data LamBinder (n::S) (l::S) = LamBinder (Binder n l) (Arrow l)  deriving (Show)
data PiBinder  (n::S) (l::S) = PiBinder  (Binder n l) (Arrow l)  deriving (Show)
newtype AltBinder (n::S) (l::S) = AltBinder { fromAltBinder :: Binder n l }  deriving (Show)

type LamExpr = Abs LamBinder Block  :: E
type PiType  = Abs PiBinder  Type   :: E

type Arrow n = ArrowP (EffectRow n)

type Val  = Atom
type Type = Atom
type Kind = Type

type TC  n = PrimTC  (Atom n)
type Con n = PrimCon (Atom n)
type Op  n = PrimOp  (Atom n)
type Hof n = PrimHof (Atom n)

type IndexStructure = Nest Binder

type AtomSubstVal = SubstVal TypedBinderInfo Atom :: E -> E

-- === top-level modules ===

type SourceName = T.Text

data SourceNameMap n = SourceNameMap
  { fromSourceNameMap :: M.Map SourceName (Name UnitE n)}

data Module n where
  Module :: IRVariant
         -> Nest Decl n l
         -> ScopeFrag l l'
         -> SourceNameMap l'
         -> Module n

data EvaluatedModule (n::S) where
  EvaluatedModule :: ScopeFrag n l -> SourceNameMap l -> EvaluatedModule n

-- === effects ===

data EffectRow n = EffectRow (S.Set (Effect n)) (Maybe (AtomName n))
                   deriving (Show, Eq)

data Effect n = RWSEffect RWS (AtomName n) | ExceptionEffect | IOEffect
                deriving (Show, Eq, Ord)

pattern Pure :: EffectRow n
pattern Pure <- ((\(EffectRow effs t) -> (S.null effs, t)) -> (True, Nothing))
 where  Pure = EffectRow mempty Nothing

-- === Synonyms ===

infixr 1 -->
infixr 1 --@
infixr 2 ==>

(?-->) :: Type n -> Type n -> Type n
a ?--> b = Pi (Abs (PiBinder (Ignore:>a) ImplicitArrow) b)

(-->) :: Type n -> Type n -> Type n
a --> b = Pi (Abs (PiBinder (Ignore:>a) PureArrow) b)

(--@) :: Type n -> Type n -> Type n
a --@ b = Pi (Abs (PiBinder (Ignore:>a) LinArrow) b)

(==>) :: Type n -> Type n -> Type n
a ==> b = Pi (Abs (PiBinder (Ignore:>a) TabArrow) b)

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
pattern PairVal x y = Con (PairCon x y)

pattern PairTy :: Type n -> Type n -> Type n
pattern PairTy x y = TC (PairType x y)

pattern UnitVal :: Atom n
pattern UnitVal = Con UnitCon

pattern UnitTy :: Type n
pattern UnitTy = TC UnitType

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

pattern PureArrow :: Arrow n
pattern PureArrow = PlainArrow Pure

pattern TabTy :: Binder n l -> Type l -> Type n
pattern TabTy v i = Pi (Abs (PiBinder v TabArrow) i)

pattern TabTyAbs :: PiType n -> Type n
pattern TabTyAbs a <- Pi a@(Abs (PiBinder _ TabArrow) _)

pattern LamVal :: Binder n l -> Block l -> Atom n
pattern LamVal v b <- Lam (Abs (LamBinder v _) b)

pattern TabVal :: Binder n l -> Block l -> Atom n
pattern TabVal v b = Lam (Abs (LamBinder v TabArrow) b)

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
pattern FunTy b eff bodyTy = Pi (Abs (PiBinder b (PlainArrow eff)) bodyTy)

pattern PiTy :: Binder n l -> Arrow l -> Type l -> Type n
pattern PiTy b arr bodyTy = Pi (Abs (PiBinder b arr) bodyTy)

pattern BinaryFunTy :: Binder n l -> Binder l l' -> EffectRow l' -> Type l' -> Type n
pattern BinaryFunTy b1 b2 eff bodyTy = FunTy b1 Pure (FunTy b2 eff bodyTy)

-- -- === instances ===

-- right-biased, unlike the underlying Map
instance Semigroup (SourceNameMap n) where
  m1 <> m2 = SourceNameMap $ fromSourceNameMap m2 <> fromSourceNameMap m1

instance Monoid (SourceNameMap n) where
  mempty = SourceNameMap mempty

instance Show (Block n) where
  show _ = "TODO"

instance Show (DataDef n) where
  show _ = "TODO"

-- shorthand to makes instance implementations easier
tne :: HasNamesE e => Monad m => Scope o -> NameTraversal m i o -> e i -> m (e o)
tne = traverseNamesE

instance HasNamesE DataDef where
  traverseNamesE = undefined

instance SubstE AtomSubstVal DataDef where
  substE = undefined

instance HasNamesE Atom where
  traverseNamesE s t atom = case atom of
    -- Var v ->
    --   lookupNameTraversal t v >>= \case
    --     Left substVal -> case substVal of
    --       SubstVal x -> return x
    --       Rename v'  -> return $ Var v'
    --     Right v' -> return $ Var v'
    Lam ab -> Lam <$> tne s t ab
    Pi  ab -> Pi  <$> tne s t ab
    DataCon def params con args ->
      DataCon <$> tne s t def <*> mapM (tne s t) params
              <*> pure con <*> mapM (tne s t) args
    TypeCon def params -> TypeCon <$> tne s t def <*> mapM (tne s t) params
    -- LabeledRow (ExtLabeledItems (Type n) (Name n))
    Record items -> Record <$> mapM (tne s t) items
    -- RecordTy  (ExtLabeledItems (Type n) (Name n))
    -- Variant   (ExtLabeledItems (Type n) (Name n)) Label Int (Atom n)
    -- VariantTy (ExtLabeledItems (Type n) (Name n))
    Con con -> Con <$> traverse (tne s t) con
    TC  con -> TC  <$> traverse (tne s t) con
    -- Eff effs -> Eff <$> tne s t effs
    ACase scrut alts ty ->
      ACase <$> tne s t scrut <*> traverse (tne s t) alts <*> tne s t ty
    -- DataConRef (DataDef n) [Atom n] (EmptyNest DataConRefBinding n)
    -- BoxedRef (Atom n) (Atom n) (Abs Binder Block n)  -- ptr, size, binder/body
    -- ProjectElt (NE.NonEmpty Int) (Var n)
    _ -> undefined
instance SubstE AtomSubstVal Atom where
  substE = undefined

instance AlphaEqE Atom where
  alphaEqE = undefined
  -- alphaEqE atom1 atom2 = undefined
  -- alphaEqE atom1 atom2 = case (atom1, atom2) of
    -- (Var v, Var v') -> alphaEqE v v'
    -- (Pi ab, Pi ab') -> alphaEqE ab ab'
  -- DataCon def params con args == DataCon def' params' con' args' =
  --   def == def' && params == params' && con == con' && args == args'
  -- TypeCon def params == TypeCon def' params' = def == def' && params == params'
  -- Variant lr l i v == Variant lr' l' i' v' =
  --   (lr, l, i, v) == (lr', l', i', v')
  -- Record lr    == Record lr'      = lr == lr'
  -- RecordTy lr  == RecordTy lr'    = lr == lr'
  -- VariantTy lr == VariantTy lr'   = lr == lr'
    -- (Con con, Con con') -> alphaEqTraversable con con'
    -- (TC  con, TC  con') -> alphaEqTraversable con con'
  -- Eff eff == Eff eff' = eff == eff'
  -- ProjectElt idxs v == ProjectElt idxs' v' = (idxs, v) == (idxs', v')
    -- _ -> zipErr

instance HasNamesE Expr where
  traverseNamesE s t expr = case expr of
    App e1 e2 -> App <$> tne s t e1 <*> tne s t e2
    Case scrut alts ty ->
      Case <$> tne s t scrut <*> traverse (tne s t) alts <*> tne s t ty
    Atom atom -> Atom <$> tne s t atom
    Op  op  -> Op  <$> traverse (tne s t) op
    Hof hof -> Hof <$> traverse (tne s t) hof

instance SubstE AtomSubstVal Expr where
  substE expr = case expr of
    App e1 e2 -> App <$> substE e1 <*> substE e2
    Case scrut alts ty ->
      Case <$> substE scrut <*> traverse substE alts <*> substE ty
    Atom atom -> Atom <$> substE atom
    Op  op  -> Op  <$> traverse substE op
    Hof hof -> Hof <$> traverse substE hof

instance HasNamesE Block where
  traverseNamesE = undefined

instance SubstE AtomSubstVal Block where
  substE = undefined

instance HasNamesE EffectRow where
  traverseNamesE = undefined

instance SubstE AtomSubstVal EffectRow where
  substE = undefined

instance AlphaEqE EffectRow where
  alphaEqE _ _ = undefined

instance HasNamesB LamBinder where
  traverseNamesB _ _ _ _ = undefined

instance SubstB AtomSubstVal LamBinder where
  substB _ _ = undefined

instance HasNamesB PiBinder where
  traverseNamesB _ _ _ _ = undefined

instance SubstB AtomSubstVal PiBinder where
  substB _ _ = undefined

instance HasNamesB AltBinder where
  traverseNamesB _ _ _ _ = undefined

instance SubstB AtomSubstVal AltBinder where
  substB _ _ = undefined

instance HasNamesB Decl where
  traverseNamesB _ _ _ _ = undefined

instance SubstB AtomSubstVal Decl where
  substB _ _ = undefined
