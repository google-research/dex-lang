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
    SrcPos, Binder (..), Block (..), Decl (..),
    Expr (..), Atom (..), Arrow (..), PrimTC (..), Abs (..),
    PrimExpr (..), PrimCon (..), LitVal (..), PrimEffect (..), PrimOp (..),
    PrimHof (..), LamExpr (..), PiType (..), LetAnn (..),
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
    pattern UnitTy, pattern PairTy,
    pattern FixedIntRange, pattern Fin, pattern RefTy, pattern RawRefTy,
    pattern BaseTy, pattern PtrTy, pattern UnitVal,
    pattern PairVal, pattern TyKind,
    pattern Pure, pattern LabeledRowKind, pattern EffKind,
    pattern FunTy, pattern BinaryFunTy,
    (-->), (?-->), (--@), (==>) ) where

import Data.Foldable (toList)
import Control.Monad.Except hiding (Except)
import qualified Data.List.NonEmpty    as NE
import qualified Data.Map.Strict       as M
import qualified Data.Set              as S
import qualified Data.Text             as T
import Data.Int
import Data.Text.Prettyprint.Doc
import Data.Word
import Foreign.Ptr

import Syntax
  ( LetAnn (..), IRVariant (..)
  , PrimExpr (..), PrimTC (..), PrimCon (..), PrimOp (..), PrimHof (..)
  , BaseMonoid, BaseMonoidP (..), PrimEffect (..), BinOp (..), UnOp (..)
  , CmpOp (..), Direction (..)
  , ForAnn (..), Limit (..), strToPrimName, primNameToStr, showPrimName
  , RWS (..), LitVal (..), ScalarBaseType (..), BaseType (..)
  , AddressSpace (..), Device (..), PtrType, sizeOf, ptrSize, vectorWidth)

import SaferNames.Name
import Util (zipErr)
import PPrint ()
import Err
import LabeledItems

-- === core IR ===

data Atom n =
   Var (AtomName n)
 | Lam (LamExpr n)
 | Pi  (PiType  n)
   -- RawName is purely for printing
 | DataCon RawName (Name DataDef n) [Atom n] Int [Atom n]
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
 | LamBound Arrow
 | PiBound
 | MiscBound
 | InferenceName

data TypedBinderInfo (n::S) = TypedBinderInfo (Type n) (AtomBinderInfo n)

data Decl n l = Let LetAnn (Binder n l) (Expr n)
                deriving (Show)

type AtomName   = Name TypedBinderInfo

data Binder (n::S) (l::S) =
  (:>) (NameBinder TypedBinderInfo n l) (Type n)  deriving Show

data DataConRefBinding n l = DataConRefBinding (Binder n l) (Atom n) deriving Show

type AltP (e::E) = Abs (Nest Binder) e :: E
type Alt = AltP Block                  :: E

data DataDef n where
  -- The `RawName` is just for pretty-printing. The actual alpha-renamable
  -- binder name is in UExpr and Bindings
  DataDef :: RawName -> Nest Binder n l -> [DataConDef l] -> DataDef n

-- As above, the `RawName` is just for pretty-printing
data DataConDef n = DataConDef RawName (EmptyAbs (Nest Binder) n)
                    deriving Show

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
   deriving (Show, Eq)

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
  Module
    :: IRVariant
    -> Nest Decl n l    -- Unevaluated decls representing runtime work to be done
    -> ScopeFrag l l'   -- Evaluated bindings
    -> SourceNameMap l' -- Mapping of module's source names to internal names
    -> Module n

data EvaluatedModule (n::S) where
  EvaluatedModule
    :: ScopeFrag n l     -- Evaluated bindings
    -> SourceNameMap l   -- Mapping of module's source names to internal names
    -> EvaluatedModule n

-- === effects ===

data EffectRow n = EffectRow (S.Set (Effect n)) (Maybe (AtomName n))
                   deriving (Show, Eq)

data Effect n = RWSEffect RWS (AtomName n) | ExceptionEffect | IOEffect
                deriving (Show, Eq, Ord)

pattern Pure :: EffectRow n
pattern Pure <- ((\(EffectRow effs t) -> (S.null effs, t)) -> (True, Nothing))
 where  Pure = EffectRow mempty Nothing

extendEffRow :: S.Set (Effect n) -> (EffectRow n) -> (EffectRow n)
extendEffRow effs (EffectRow effs' t) = EffectRow (effs <> effs') t

-- === Synonyms ===

infixr 1 -->
infixr 1 --@
infixr 2 ==>

nonDepPiType :: ScopeReader m => Arrow -> Type n -> EffectRow n -> Type n -> m n (Type n)
nonDepPiType arr argTy eff resultTy =
  toConstAbs (TypedBinderInfo argTy PiBound) (PairE eff resultTy) >>= \case
    Abs b (PairE eff' resultTy') ->
      return $ Pi $ PiType arr (b:>argTy) eff' resultTy'

(?-->) :: ScopeReader m => Type n -> Type n -> m n (Type n)
a ?--> b = nonDepPiType ImplicitArrow a Pure b

(-->) :: ScopeReader m => Type n -> Type n -> m n (Type n)
a --> b = nonDepPiType PlainArrow a Pure b

(--@) :: ScopeReader m => Type n -> Type n -> m n (Type n)
a --@ b = nonDepPiType LinArrow a Pure b

(==>) :: ScopeReader m => Type n -> Type n -> m n (Type n)
a ==> b = nonDepPiType TabArrow a Pure b

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

-- right-biased, unlike the underlying Map
instance Semigroup (SourceNameMap n) where
  m1 <> m2 = SourceNameMap $ fromSourceNameMap m2 <> fromSourceNameMap m1

instance Monoid (SourceNameMap n) where
  mempty = SourceNameMap mempty

-- shorthand to makes instance implementations easier
tne :: HasNamesE e => Monad m => e i -> NameTraversalT m i o (e o)
tne = traverseNamesE

ipe :: InjectableE e => ObservablyFresh n l -> e n -> e l
ipe = injectionProofE

(<++>) :: String -> String -> String
(<++>) s1 s2 = s1 <> " " <> s2

showParens :: Show a => a -> String
showParens x = "(" <> show x <> ")"

instance Show (DataDef n) where
  show (DataDef name bs cons) =
    "DataDef" <++> showParens name <++> showParens bs <++> showParens cons

instance SubstE AtomSubstVal (Name DataDef) where
  substE name =
    lookupSubstM name >>= \case
      Rename name' -> return name'

instance InjectableE DataDef where
  injectionProofE fresh (DataDef name bs cons) =
    case injectionProofE fresh (Abs bs (ListE cons)) of
      Abs bs' (ListE cons') -> DataDef name bs' cons'

instance HasNamesE DataDef where
  traverseNamesE (DataDef name bs cons) =
    tne (Abs bs (ListE cons)) >>= \case
      Abs bs' (ListE cons') -> return $ DataDef name bs' cons'

instance SubstE AtomSubstVal DataDef where
  substE (DataDef name bs cons) =
    substE (Abs bs (ListE cons)) >>= \case
      Abs bs' (ListE cons') -> return $ DataDef name bs' cons'

instance InjectableE DataConDef where
  injectionProofE fresh (DataConDef name ab) = DataConDef name $ ipe fresh ab

instance HasNamesE DataConDef where
  traverseNamesE (DataConDef name ab) = DataConDef name <$> tne ab

instance SubstE AtomSubstVal DataConDef where
  substE (DataConDef name ab) = DataConDef name <$> substE ab


instance InjectableB DataConRefBinding where
  injectionProofB f (DataConRefBinding b ref) cont = do
    let ref' = ipe f ref
    injectionProofB f b \f' b' -> cont f' $ DataConRefBinding b' ref'

instance BindsNames DataConRefBinding where
  toExtVal (DataConRefBinding b _) = toExtVal b

instance HasNamesB DataConRefBinding where
  traverseNamesB (DataConRefBinding b ref) cont = do
    ref' <- traverseNamesE ref
    traverseNamesB b \b' -> cont $ DataConRefBinding b' ref'

instance SubstB AtomSubstVal DataConRefBinding where
  substB (DataConRefBinding b ref) cont = do
    ref' <- substE ref
    substB b \b' -> cont $ DataConRefBinding b' ref'

instance InjectableE Atom where
  injectionProofE f atom = case atom of
    Var name -> Var $ ipe f name
    Lam lam  -> Lam $ ipe f lam
    Pi  piTy -> Pi  $ ipe f piTy
    DataCon printName defName params con args ->
      DataCon printName (ipe f defName) (fmap (ipe f) params) con (fmap (ipe f) args)
    TypeCon defName params ->
      TypeCon (ipe f defName) (fmap (ipe f) params)
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
    DataConRef def params bs -> DataConRef (ipe f def) (fmap (ipe f) params) (ipe f bs)
    BoxedRef ptr size ab -> BoxedRef (ipe f ptr) (ipe f size) (ipe f ab)
    ProjectElt idxs x -> ProjectElt idxs $ ipe f x

instance HasNamesE Atom where
  traverseNamesE atom = case atom of
    Var v -> Var <$> tne v
    Lam ab -> Lam <$> tne ab
    Pi  ab -> Pi  <$> tne ab
    DataCon printName def params con args ->
      DataCon printName <$> tne def <*> mapM tne params
                        <*> pure con <*> mapM tne args
    TypeCon def params -> TypeCon <$> tne def <*> mapM tne params
    LabeledRow (Ext items ext) -> (LabeledRow <$>) $
      Ext <$> mapM tne items <*> mapM tne ext
    Record items -> Record <$> mapM tne items
    RecordTy (Ext items ext) -> (RecordTy <$>) $ Ext <$> mapM tne items <*> mapM tne ext
    Variant (Ext items ext) l con payload -> do
      extItems <- Ext <$> mapM tne items <*> mapM tne ext
      Variant extItems l con <$> tne payload
    VariantTy (Ext items ext) -> (VariantTy <$>) $
      Ext <$> mapM tne items <*> mapM tne ext
    Con con -> Con <$> traverse tne con
    TC  con -> TC  <$> traverse tne con
    Eff effs -> Eff <$> tne effs
    ACase scrut alts ty -> ACase <$> tne scrut <*> traverse tne alts <*> tne ty
    DataConRef def params bs -> DataConRef <$> tne def <*> mapM tne params <*> tne bs
    BoxedRef ptr size ab -> BoxedRef <$> tne ptr <*> tne size <*> tne ab
    ProjectElt idxs v -> ProjectElt idxs <$> tne v

instance SubstE AtomSubstVal Atom where
  substE atom = case atom of
    Var v ->
      lookupSubstM v >>= \case
        SubstVal x -> return x
        Rename v' -> return $ Var v'
    Lam ab -> Lam <$> substE ab
    Pi  ab -> Pi  <$> substE ab
    DataCon printName def params con args ->
      DataCon printName <$> substE def <*> mapM substE params
                        <*> pure con <*> mapM substE args
    TypeCon def params -> TypeCon <$> substE def <*> mapM substE params
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
    DataConRef def params bs -> DataConRef <$> substE def <*> mapM substE params <*> substE bs
    BoxedRef ptr size ab -> BoxedRef <$> substE ptr <*> substE size <*> substE ab
    ProjectElt idxs v -> do
      v' <- lookupSubstM v >>= \case
              SubstVal x -> return x
              Rename v'  -> return $ Var v'
      return $ getProjection (NE.toList idxs) v'
    where
      substTail
        :: SubstReader AtomSubstVal m
        => Maybe (AtomName i)
        -> m i o (ExtLabeledItems (Atom o) (AtomName o))
      substTail Nothing = return $ NoExt NoLabeledItems
      substTail (Just v) =
        lookupSubstM v >>= \case
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

instance AlphaEqE Atom where
  alphaEqE atom1 atom2 = case (atom1, atom2) of
    (Var v, Var v') -> alphaEqE v v'
    (Pi ab, Pi ab') -> alphaEqE ab ab'
    (DataCon _ def params con args, DataCon _ def' params' con' args') -> do
      alphaEqE def def'
      alphaEqTraversable params params'
      assertEq con con' ""
      alphaEqTraversable args args'
    (TypeCon def params, TypeCon def' params') -> do
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

instance HasNamesE Expr where
  traverseNamesE expr = case expr of
    App e1 e2 -> App <$> tne e1 <*> tne e2
    Case scrut alts ty ->
      Case <$> tne scrut <*> traverse tne alts <*> tne ty
    Atom atom -> Atom <$> tne atom
    Op  op  -> Op  <$> traverse tne op
    Hof hof -> Hof <$> traverse tne hof

instance SubstE AtomSubstVal Expr where
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

instance HasNamesE Block where
  traverseNamesE (Block resultTy decls result) = do
    resultTy' <- tne resultTy
    Abs decls' result' <- tne (Abs decls result)
    return $ Block resultTy' decls' result'

instance SubstE AtomSubstVal Block where
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

instance HasNamesE LamExpr where
  traverseNamesE (LamExpr arr b eff body) = do
    Abs b' (PairE eff' body') <- tne $ Abs b (PairE eff body)
    return $ LamExpr arr b' eff' body'

instance SubstE AtomSubstVal LamExpr where
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

instance HasNamesE PiType where
  traverseNamesE (PiType arr b eff bodyTy) = do
    Abs b' (PairE eff' bodyTy') <- tne $ Abs b (PairE eff bodyTy)
    return $ PiType arr b' eff' bodyTy'

instance AlphaEqE PiType where
  alphaEqE (PiType arr  b  eff  resultTy )
           (PiType arr' b' eff' resultTy') = do
    assertEq arr arr' ""
    alphaEqE (Abs b  (PairE eff  resultTy ))
             (Abs b' (PairE eff' resultTy'))

instance SubstE AtomSubstVal PiType where
  substE (PiType arr b eff bodyTy) = do
    Abs b' (PairE eff' bodyTy') <- substE $ Abs b (PairE eff bodyTy)
    return $ PiType arr b' eff' bodyTy'

instance InjectableE Effect where
  injectionProofE f eff = case eff of
    RWSEffect rws v -> RWSEffect rws $ ipe f v
    ExceptionEffect -> ExceptionEffect
    IOEffect        -> IOEffect

instance HasNamesE Effect where
  traverseNamesE eff = case eff of
    RWSEffect rws v -> RWSEffect rws <$> tne v
    ExceptionEffect -> return ExceptionEffect
    IOEffect        -> return IOEffect

instance SubstE AtomSubstVal Effect where
  substE eff = case eff of
    RWSEffect rws v -> do
      v' <- lookupSubstM v >>= \case
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

instance HasNamesE EffectRow where
  traverseNamesE (EffectRow effs tailVar) = do
    effs' <- S.fromList <$> mapM tne (S.toList effs)
    tailVar' <- mapM tne tailVar
    return $ EffectRow effs' tailVar'

instance SubstE AtomSubstVal EffectRow where
  substE (EffectRow effs tailVar) = do
    effs' <- S.fromList <$> mapM substE (S.toList effs)
    tailEffRow <- case tailVar of
      Nothing -> return $ EffectRow mempty Nothing
      Just v -> lookupSubstM v >>= \case
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
  toExtVal (b:>_) = toExtVal b

instance InjectableB Binder where
  injectionProofB f (b:>ty) cont = do
    let ty' = injectionProofE f ty
    injectionProofB f b \f' b' -> cont f' (b':>ty')

instance HasNamesB Binder where
  traverseNamesB (b:>ty) cont = do
    ty' <- tne ty
    traverseNamesB b \b' ->
      cont (b':>ty')

instance SubstB AtomSubstVal Binder where
  substB (b:>ty) cont = do
    ty' <- substE ty
    withFreshM (TypedBinderInfo ty' MiscBound) \b' ->
       extendSubst (b@>Rename (binderName b')) $ cont $ b':>ty'

instance AlphaEqB Binder where
  withAlphaEqB (b1:>ty1) (b2:>ty2) cont = do
    alphaEqE ty1 ty2
    withAlphaEqB b1 b2 cont

instance BindsOneName Binder TypedBinderInfo where
  (b:>_) @> x = b @> x
  binderName (b:>_) = binderName b

instance InjectableE AtomBinderInfo where
  injectionProofE f info = case info of
    LetBound ann expr -> LetBound ann (ipe f expr)
    LamBound arr  -> LamBound arr
    PiBound       -> PiBound
    MiscBound     -> MiscBound
    InferenceName -> InferenceName

instance HasNamesE AtomBinderInfo where
  traverseNamesE info = case info of
    LetBound ann expr -> LetBound ann <$> tne expr
    LamBound arr  -> return $ LamBound arr
    PiBound       -> return PiBound
    MiscBound     -> return MiscBound
    InferenceName -> return InferenceName

instance SubstE AtomSubstVal AtomBinderInfo where
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

instance InjectableE TypedBinderInfo where
  injectionProofE f (TypedBinderInfo ty info) =
    TypedBinderInfo (ipe f ty) (ipe f info)

instance HasNamesE TypedBinderInfo where
  traverseNamesE (TypedBinderInfo ty info) =
    TypedBinderInfo <$> tne ty <*> tne info

instance SubstE AtomSubstVal TypedBinderInfo where
  substE (TypedBinderInfo ty info) =
    TypedBinderInfo <$> substE ty <*> substE info

instance AlphaEqE TypedBinderInfo where
  alphaEqE (TypedBinderInfo ty info) (TypedBinderInfo ty' info') = do
    alphaEqE ty ty'
    alphaEqE info info'

instance InjectableB Decl where
  injectionProofB f (Let ann b expr) cont = do
    let expr' = ipe f expr
    injectionProofB f b \f' b' -> cont f' $ Let ann b' expr'

instance HasNamesB Decl where
  traverseNamesB (Let ann b expr) cont = do
    expr' <- tne expr
    traverseNamesB b \b' -> cont $ Let ann b' expr'

instance BindsNames Decl where
  toExtVal (Let _ b _) = toExtVal b

instance SubstB AtomSubstVal Decl where
  substB (Let ann (b:>ty) expr) cont = do
    expr' <- substE expr
    ty' <- substE ty
    let binderInfo = TypedBinderInfo ty' (LetBound ann expr')
    withFreshM binderInfo \b' ->
      extendSubst (b @> Rename (binderName b')) $
        cont $ Let ann (b':>ty') expr'

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
