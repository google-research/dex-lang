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
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}

module SaferNames.Syntax (
    Type, Kind, BaseType (..), ScalarBaseType (..),
    Effect (..), RWS (..), EffectRow (..),
    SrcPos, Var, Binder, BinderList, Block (..), Decl (..),
    Expr (..), Atom (..), ArrowP (..), Arrow, PrimTC (..), Abs (..),
    PrimExpr (..), PrimCon (..), LitVal (..), PrimEffect (..), PrimOp (..),
    PrimHof (..), LamExpr, PiType, LetAnn (..),
    BinOp (..), UnOp (..), CmpOp (..), SourceNameMap (..),
    SubstEnv, ForAnn (..),
    Val, Op, Con, Hof, TC, Module (..), EvaluatedModule, WithBindings,
    emptyEvaluatedModule, DataConRefBinding (..),
    AltP, Alt, BinderInfo (..), TypedBinderInfo (..), Bindings, BindingsFrag,
    SubstE (..), SubstB (..), Ptr, PtrType,
    AddressSpace (..), showPrimName, strToPrimName, primNameToStr,
    Direction (..), Limit (..),
    DataDef (..), NamedDataDef (..), DataConDef (..), Nest (..),
    AnnVarP (..), IndexStructure,
    mkConsList, mkConsListTy, fromConsList, fromConsListTy, fromLeftLeaningConsListTy,
    mkBundle, mkBundleTy, BundleDesc,
    binderType, isTabTy, BaseMonoidP (..), BaseMonoid, getBaseMonoidType,
    getIntLit, getFloatLit, sizeOf, ptrSize, vectorWidth, WithArrow (..),
    pattern IdxRepVal, pattern TagRepTy, pattern TagRepVal, pattern Word8Ty,
    pattern UnitTy, pattern PairTy, pattern FunTy, pattern PiTy,
    pattern FixedIntRange, pattern Fin, pattern RefTy, pattern RawRefTy,
    pattern BaseTy, pattern PtrTy, pattern UnitVal,
    pattern PairVal, pattern PureArrow,
    pattern TyKind, pattern LamVal,
    pattern TabTy, pattern TabTyAbs, pattern TabVal, pattern TabValA,
    pattern Pure, pattern BinaryFunTy, pattern BinaryFunVal,
    pattern LabeledRowKind, pattern EffKind,
    (-->), (--@), (==>) ) where

import Prelude hiding ((.), id)
import Control.Monad.Except hiding (Except)
import qualified Data.List.NonEmpty    as NE
import qualified Data.Map.Strict       as M
import qualified Data.Set              as S
import qualified Data.Text             as T
import Data.Int
import Data.Word
import Foreign.Ptr

import Syntax
  ( ArrowP (..), LetAnn (..), IRVariant
  , PrimExpr (..), PrimTC (..), PrimCon (..), PrimOp (..), PrimHof (..)
  , BaseMonoid, BaseMonoidP (..), PrimEffect (..), BinOp (..), UnOp (..)
  , CmpOp (..), Direction (..)
  , ForAnn (..), Limit (..), strToPrimName, primNameToStr, showPrimName
  , RWS (..), LitVal (..), ScalarBaseType (..), BaseType (..)
  , AddressSpace (..), PtrType, sizeOf, ptrSize, vectorWidth)

import SaferNames.Name
import Err
import LabeledItems

-- === core IR ===

data Atom n =
   Var (Var n)
 | Lam (LamExpr n)
 | Pi  (PiType  n)
 | DataCon (NamedDataDef n) [Atom n] Int [Atom n]
 | TypeCon (NamedDataDef n) [Atom n]
 | LabeledRow (ExtLabeledItems (Type n) (Name n))
 | Record (LabeledItems (Atom n))
 | RecordTy  (ExtLabeledItems (Type n) (Name n))
 | Variant   (ExtLabeledItems (Type n) (Name n)) Label Int (Atom n)
 | VariantTy (ExtLabeledItems (Type n) (Name n))
 | Con (Con n)
 | TC  (TC  n)
 | Eff (EffectRow n)
 | ACase (Atom n) [AltP Atom n] (Type n)
   -- single-constructor only for now
 | DataConRef (NamedDataDef n) [Atom n] (Abs (Nest DataConRefBinding) UnitE n)
 | BoxedRef (Atom n) (Block n) (Abs Binder Atom n)  -- ptr, size, binder/body
 -- access a nested member of a binder
 -- XXX: Variable name must not be an alias for another name or for
 -- a statically-known atom. This is because the variable name used
 -- here may also appear in the type of the atom. (We maintain this
 -- invariant during substitution and in Builder.hs.)
 | ProjectElt (NE.NonEmpty Int) (Var n)
   deriving (Show)

data Expr n =
   App (Atom n) (Atom n)
 | Case (Atom n) [Alt n] (Type n)
 | Atom (Atom n)
 | Op  (Op  n)
 | Hof (Hof n)
   deriving (Show)

data Decl n l = Let LetAnn (Binder n l) (Expr n)
                deriving (Show)

data DataConRefBinding n l = DataConRefBinding (Binder n l) (Atom n)
                             deriving Show

type AltP (e::E) = Abs (Nest Binder) e :: E
type Alt = AltP Block                  :: E

-- TODO: get rid of annotations on variable occurrences
data AnnVarP (ann::E) n = AnnVar (Name n) (ann n)
                          deriving Show

type Var = AnnVarP Type :: E
type Binder     = AnnBinderP PlainBinder            Type  :: B
type BinderList = AnnBinderP PlainBinderList (ListE Type) :: B

data DataDef n where
  -- The `RawName` is just for pretty-printing. The actual alpha-renamable binder name is in
  -- UExpr and Bindings
  DataDef :: RawName -> BinderList n l -> ListE DataConDef l -> DataDef n

data DataConDef n = DataConDef RawName (Abs (Nest Binder) UnitE n)
                    deriving Show

data NamedDataDef n = NamedDataDef (Name n) (DataDef n)
                      deriving Show

data Block n where Block :: Nest Decl n l -> Expr l -> Block n

type LamExpr = Abs Binder (WithArrow Block)  :: E
type PiType  = Abs Binder (WithArrow Type)   :: E

data WithArrow (e::E) (n::S) = WithArrow { justArrow :: Arrow n , withoutArrow :: e n }
                               deriving Show

type Arrow n = ArrowP (EffectRow n)

type Val  = Atom
type Type = Atom
type Kind = Type

type TC  n = PrimTC  (Atom n)
type Con n = PrimCon (Atom n)
type Op  n = PrimOp  (Atom n)
type Hof n = PrimHof (Atom n)

-- === top-level modules ===

type SourceName = T.Text

data SourceNameMap n = SourceNameMap
  { fromSourceNameMap :: M.Map SourceName (Name n)}

data Module n where
  Module :: IRVariant
         -> Nest Decl n l
         -> BindingsFrag l l'
         -> SourceNameMap l'
         -> Module n

type WithBindings = Abs BindingsFrag :: E -> E
type EvaluatedModule = WithBindings SourceNameMap  :: E

emptyEvaluatedModule :: EvaluatedModule n
emptyEvaluatedModule = Abs (RecEnvFrag emptyEnv) mempty

type IndexStructure = Nest Binder

getBaseMonoidType :: Scope n -> Type n -> Type n
getBaseMonoidType scope ty = case ty of
  TabTy i b -> case projectNamesL scope (i@>()) b of
    Just b' -> b'
    Nothing -> error "Can't use a dependent table as a monoid"
  _         -> ty

-- === effects ===

data EffectRow n = EffectRow (S.Set (Effect n)) (Maybe (Name n))
                   deriving Show

data Effect n = RWSEffect RWS (Name n) | ExceptionEffect | IOEffect
                deriving (Show, Eq, Ord)

pattern Pure :: EffectRow n
pattern Pure <- ((\(EffectRow effs t) -> (S.null effs, t)) -> (True, Nothing))
 where  Pure = EffectRow mempty Nothing

-- === Recursive bindings ===

data BinderInfo n =
   LamBound (ArrowP ())
 -- TODO: make the expression optional, for when it's effectful?
 -- (or we could put the effect tag on the let annotation)
 | PatBound
 | LetBound LetAnn (Expr n)
 | PiBound
 | UnknownBinder
 | DataDefName (DataDef n)
 | ClassName -- TODO
 | MethodName  (NamedDataDef n) Int  -- TODO: just have a class name and a label
 | DataConName (NamedDataDef n) Int
 | TypeConName (NamedDataDef n)
 -- TODO: avoid this case by having the inference monad use an alternative
 -- version of BinderInfo
 | InferenceName

-- The `Nothing` case is for things without types, like `DataDefName`. Everything
-- that can have a type must have a type.
data TypedBinderInfo n = TypedBinderInfo (Maybe (Type n)) (BinderInfo n)

type Bindings     = RecEnv     TypedBinderInfo
type BindingsFrag = RecEnvFrag TypedBinderInfo

-- === traversals with atom substitutions ===

data SubstVal e n = SubstVal (e n) | Rename (Name n)

-- TODO: make this just `Env (Atom o) i` if we remove type annotations from
-- variable occurrences
type AtomSubstVal = SubstVal Atom
type SubstEnv i o = Env i (AtomSubstVal o)

type CoreTraversal = NameTraversal AtomSubstVal

class HasNamesE e => SubstE e where
  traverseCoreE
    :: Monad m
    => Scope o
    -> CoreTraversal m i o
    -> e i
    -> m (e o)

class HasNamesB b => SubstB (b::B) where
  traverseCoreB
    :: Monad m
    => Scope o
    -> CoreTraversal m i o
    -> b i i'
    -> m (FreshBinder b o (i:=>:i') )

  asBindingsFrag :: b n l -> BindingsFrag n l

coreTraversalFromRenameTraversal :: Monad m => RenameTraversal m i o -> CoreTraversal m i o
coreTraversalFromRenameTraversal (NameTraversal f renamer) =
  NameTraversal f' renamer
  where f' name = Rename <$> f name

traverseNamesFromSubstE :: (SubstE e, Monad m)
                           => Scope o -> RenameTraversal m i o -> e i -> m (e o)
traverseNamesFromSubstE scope t e =
  traverseCoreE scope (coreTraversalFromRenameTraversal t) e

traverseNamesFromSubstB
  :: (SubstB b, Monad m)
  => Scope o -> RenameTraversal m i o -> b i i' -> m (FreshBinder b o (i:=>:i'))
traverseNamesFromSubstB s t b =
  traverseCoreB s (coreTraversalFromRenameTraversal t) b

-- === Synonyms ===

binderType :: Binder n l -> Type n
binderType (_:>ann) = ann

infixr 1 -->
infixr 1 --@
infixr 2 ==>

(-->) :: Type n -> Type n -> Type n
a --> b = Pi (Abs (Ignore:>a) (WithArrow PureArrow b))

(--@) :: Type n -> Type n -> Type n
a --@ b = Pi (Abs (Ignore:>a) (WithArrow LinArrow b))

(==>) :: Type n -> Type n -> Type n
a ==> b = Pi (Abs (Ignore:>a) (WithArrow TabArrow b))

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
pattern TabTy v i = Pi (Abs v (WithArrow TabArrow i))

pattern TabTyAbs :: PiType n -> Type n
pattern TabTyAbs a <- Pi a@(Abs _ (WithArrow TabArrow _))

pattern LamVal :: Binder n l -> Block l -> Atom n
pattern LamVal v b <- Lam (Abs v (WithArrow _ b))

pattern TabVal :: Binder n l -> Block l -> Atom n
pattern TabVal v b = Lam (Abs v (WithArrow TabArrow b))

pattern TabValA :: Binder n l -> Atom l -> Atom n
pattern TabValA v a = Lam (Abs v (WithArrow TabArrow (Block Empty (Atom a))))

isTabTy :: Type n -> Bool
isTabTy (TabTy _ _) = True
isTabTy _ = False

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
pattern FunTy b eff bodyTy = Pi (Abs b (WithArrow (PlainArrow eff) bodyTy))

pattern PiTy :: Binder n l -> Arrow l -> Type l -> Type n
pattern PiTy b arr bodyTy = Pi (Abs b (WithArrow arr bodyTy))

pattern BinaryFunTy :: Binder n l -> Binder l l' -> EffectRow l' -> Type l' -> Type n
pattern BinaryFunTy b1 b2 eff bodyTy = FunTy b1 Pure (FunTy b2 eff bodyTy)

pattern BinaryFunVal :: Binder n l -> Binder l l' -> EffectRow l' -> Block l' -> Atom n
pattern BinaryFunVal b1 b2 eff body =
          Lam (Abs b1 (WithArrow PureArrow (Block Empty (Atom (
          Lam (Abs b2 (WithArrow (PlainArrow eff) body)))))))

-- === instances ===

-- right-biased, unlike the underlying Map
instance Semigroup (SourceNameMap n) where
  m1 <> m2 = SourceNameMap $ fromSourceNameMap m2 <> fromSourceNameMap m1

instance Monoid (SourceNameMap n) where
  mempty = SourceNameMap mempty

instance Show (Block n) where
  show _ = "TODO"

instance Show (DataDef n) where
  show _ = "TODO"

-- variant with the common extension built in
withTraverseCoreB
  :: (SubstB b, Monad m)
  =>                              Scope  o  -> CoreTraversal m  i  o  -> b i i'
  -> (forall o'. FreshExt o o' -> Scope  o' -> CoreTraversal m  i' o' -> b o o' -> m a)
  -> m a
withTraverseCoreB s t b cont = do
  traverseCoreB s t b >>= \case
    FreshBinder ext b' renamer -> do
      let t' = extendInjectNameTraversal ext renamer t
      let s' = extendScope s b'
      cont ext s' t' b'

-- shorthand to makes instance implementations easier
tce :: SubstE e => Monad m => Scope o -> CoreTraversal m i o -> e i -> m (e o)
tce = traverseCoreE

instance SubstB PlainBinder where
  traverseCoreB = undefined
  asBindingsFrag = undefined

instance (SubstB b, SubstE e) => SubstE (Abs b e) where
  traverseCoreE s t (Abs b body) = do
    withTraverseCoreB s t b \_ s' t' b' ->
      Abs b' <$> traverseCoreE s' t' body

instance (SubstB b, SubstE e) => SubstB (AnnBinderP b e) where
  traverseCoreB s t (b:>ann) = do
    ann' <- traverseCoreE s t ann
    traverseCoreB s t b >>= \case
      FreshBinder ext b' renamer -> return $ FreshBinder ext (b':>ann') renamer
  asBindingsFrag = undefined

instance HasNamesE EffectRow where traverseNamesE = traverseNamesFromSubstE
instance SubstE EffectRow where
  traverseCoreE = undefined

instance SubstE e => HasNamesE (SubstVal e) where traverseNamesE = traverseNamesFromSubstE
instance SubstE e => SubstE (SubstVal e) where
  traverseCoreE = undefined

instance SubstE e => HasNamesE (WithArrow e) where
  traverseNamesE = traverseNamesFromSubstE
instance SubstE e => SubstE (WithArrow e) where
  traverseCoreE s t (WithArrow arr e) =
    WithArrow <$> traverse (tce s t) arr <*> tce s t e

instance HasNamesE Block where traverseNamesE = traverseNamesFromSubstE
instance SubstE Block where
  traverseCoreE s t (Block decls result) =
    traverseCoreE s t (Abs decls result) >>= \case
      Abs decls' result' -> return $ Block decls' result'

instance HasNamesB Decl where
  traverseNamesB = traverseNamesFromSubstB
  boundScope = undefined
instance SubstB Decl where
  traverseCoreB s t (Let ann b expr) = do
    expr' <- traverseCoreE s t expr
    traverseCoreB s t b >>= \case
      FreshBinder ext b' renamer ->
        return $ FreshBinder ext (Let ann b' expr') renamer
  asBindingsFrag = undefined

instance HasNamesB DataConRefBinding where
  traverseNamesB = undefined
  boundScope = undefined

instance SubstB b => SubstB (Nest b) where
  traverseCoreB s t nest = case nest of
    Empty -> do return $ FreshBinder emptyFreshExt Empty emptyEnv
    Nest b rest ->
      traverseCoreB s t (NestPair b rest) >>= \case
        FreshBinder ext (NestPair b' rest') renamer ->
          return $ FreshBinder ext (Nest b' rest') renamer
  asBindingsFrag = undefined

instance (SubstB b1, SubstB b2) => SubstB (NestPair b1 b2) where
  traverseCoreB = undefined
  asBindingsFrag = undefined

instance HasNamesE NamedDataDef where traverseNamesE = traverseNamesFromSubstE
instance SubstE NamedDataDef where
  traverseCoreE = undefined

instance HasNamesE DataDef where traverseNamesE = traverseNamesFromSubstE
instance SubstE DataDef where
  traverseCoreE = undefined

instance HasNamesE Atom where traverseNamesE = traverseNamesFromSubstE
instance SubstE Atom where
  traverseCoreE s t atom = case atom of
    Var (AnnVar v ann) ->
      lookupNameTraversal t v >>= \case
        Left substVal -> case substVal of
          SubstVal x -> return x
          Rename v' -> do
            ann' <- traverseCoreE s t ann
            return $ Var $ AnnVar v' ann'
        Right v' -> do
          ann' <- traverseCoreE s t ann
          return $ Var $ AnnVar v' ann'
    Lam ab -> Lam <$> tce s t ab
    Pi  ab -> Pi  <$> tce s t ab
    DataCon def params con args ->
      DataCon <$> tce s t def <*> mapM (tce s t) params
              <*> pure con <*> mapM (tce s t) args
    TypeCon def params -> TypeCon <$> tce s t def <*> mapM (tce s t) params
    -- LabeledRow (ExtLabeledItems (Type n) (Name n))
    Record items -> Record <$> mapM (tce s t) items
    -- RecordTy  (ExtLabeledItems (Type n) (Name n))
    -- Variant   (ExtLabeledItems (Type n) (Name n)) Label Int (Atom n)
    -- VariantTy (ExtLabeledItems (Type n) (Name n))
    Con con -> Con <$> traverse (tce s t) con
    TC  con -> TC  <$> traverse (tce s t) con
    Eff effs -> Eff <$> tce s t effs
    ACase scrut alts ty ->
      ACase <$> tce s t scrut <*> traverse (tce s t) alts <*> tce s t ty
    -- DataConRef (DataDef n) [Atom n] (EmptyNest DataConRefBinding n)
    -- BoxedRef (Atom n) (Atom n) (Abs Binder Block n)  -- ptr, size, binder/body
    -- ProjectElt (NE.NonEmpty Int) (Var n)
    _ -> undefined

instance HasNamesE Expr where traverseNamesE = traverseNamesFromSubstE
instance SubstE Expr where
  traverseCoreE s t expr = case expr of
    App e1 e2 -> App <$> tce s t e1 <*> tce s t e2
    Case scrut alts ty ->
      Case <$> tce s t scrut <*> traverse (tce s t) alts <*> tce s t ty
    Atom atom -> Atom <$> tce s t atom
    Op  op  -> Op  <$> traverse (tce s t) op
    Hof hof -> Hof <$> traverse (tce s t) hof

instance HasNamesE SourceNameMap where
  traverseNamesE = undefined

instance HasNamesE TypedBinderInfo where
  traverseNamesE = undefined
