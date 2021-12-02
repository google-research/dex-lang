-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module SaferNames.Builder (
  emit, emitOp,
  buildPureLam, BuilderT (..), Builder (..), Builder2, BuilderM,
  runBuilderT, buildBlock, buildBlockReduced, app, add, mul, sub, neg, div',
  iadd, imul, isub, idiv, ilt, ieq, irem,
  fpow, flog, fLitLike, recGetHead, buildPureNaryLam,
  emitMethodType, emitSuperclass,
  makeSuperclassGetter, makeMethodGetter,
  select, getUnpacked, emitUnpacked,
  fromPair, getFst, getSnd, getProj, getProjRef, naryApp,
  ptrOffset, unsafePtrLoad, ptrLoad,
  getClassDef, getDataCon,
  Emits, EmitsEvidence (..), buildPi, buildNonDepPi, buildLam, buildLamGeneral,
  buildAbs, buildNaryAbs, buildAlt, buildUnaryAlt, buildNewtype, fromNewtype,
  emitDataDef, emitClassDef, emitDataConName, emitTyConName,
  buildCase, buildSplitCase,
  emitBlock, emitDecls, BuilderEmissions, emitAtomToName,
  TopBuilder (..), TopBuilderT (..), runTopBuilderT, TopBuilder2,
   emitSourceMap, emitSynthCandidates,
  TopBindingsFrag (..),
  inlineLastDecl, fabricateEmitsEvidence, fabricateEmitsEvidenceM,
  singletonBinderNest, runBuilderM, liftBuilder, makeBlock,
  indexToInt, indexSetSize, intToIndex
  ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Writer.Strict hiding (Alt)
import Data.Functor ((<&>))
import Data.Foldable (toList)
import Data.List (elemIndex)
import Data.Maybe (fromJust)

import qualified Unsafe.Coerce as TrulyUnsafe

import SaferNames.Name
import SaferNames.Syntax
import SaferNames.Type
import SaferNames.PPrint ()
import SaferNames.CheapReduction

import LabeledItems
import Util (enumerate)
import Err

-- === Ordinary (local) builder class ===

class (BindingsReader m, BindingsExtender m, Fallible1 m)
      => Builder (m::MonadKind1) where
  emitDecl
    :: (Builder m, Emits n)
    => NameHint -> LetAnn -> Expr n -> m n (AtomName n)
  buildScoped
    :: (InjectableE e, Immut n)
    => (forall l. (Emits l, Distinct l, Ext n l) => m l (e l))
    -> m n (DistinctAbs (Nest Decl) e n)

type Builder2 (m :: MonadKind2) = forall i. Builder (m i)

emit :: (Builder m, Emits n) => Expr n -> m n (AtomName n)
emit expr = emitDecl NoHint PlainLet expr

emitOp :: (Builder m, Emits n) => Op n -> m n (Atom n)
emitOp op = Var <$> emit (Op op)

emitBlock :: (Builder m, Emits n) => Block n -> m n (Atom n)
emitBlock (Block _ decls result) = do
  result' <- emitDecls decls result
  case result' of
    Atom x -> return x
    _ -> Var <$> emit result'

emitDecls :: (Builder m, Emits n, SubstE Name e, InjectableE e)
          => Nest Decl n l -> e l -> m n (e n)
emitDecls decls result = runEnvReaderT idEnv $ emitDecls' decls result

emitDecls' :: (Builder m, Emits o, SubstE Name e, InjectableE e)
           => Nest Decl i i' -> e i' -> EnvReaderT Name m i o (e o)
emitDecls' Empty e = substM e
emitDecls' (Nest (Let b (DeclBinding ann _ expr)) rest) e = do
  expr' <- substM expr
  v <- emitDecl (getNameHint b) ann expr'
  extendEnv (b @> v) $ emitDecls' rest e

emitAtomToName :: (Builder m, Emits n) => Atom n -> m n (AtomName n)
emitAtomToName (Var v) = return v
emitAtomToName x = emit (Atom x)

-- === Top-level builder class ===

class (BindingsReader m, MonadFail1 m)
      => TopBuilder (m::MonadKind1) where
  -- `emitBinding` is expressible in terms of `emitBindings` but it can be
  -- implemented more efficiently by avoiding a double substitution
  -- XXX: emitBinding/emitBindings don't extend the synthesis candidates
  emitBinding :: Mut n => NameColor c => NameHint -> Binding c n -> m n (Name c n)
  emitBindings :: (Mut n, InjectableE e, SubstE Name e)
                  => Abs TopBindingsFrag e n -> m n (e n)
  emitNamelessBindings :: TopBindingsFrag n n -> m n ()
  localTopBuilder :: (Immut n, InjectableE e)
                  => (forall l. (Mut l, Ext n l) => m l (e l))
                  -> m n (DistinctAbs TopBindingsFrag e n)

emitSourceMap :: TopBuilder m => SourceMap n -> m n ()
emitSourceMap sm = emitNamelessBindings $ TopBindingsFrag emptyOutFrag mempty sm

emitSynthCandidates :: TopBuilder m => SynthCandidates n -> m n ()
emitSynthCandidates sc = emitNamelessBindings $ TopBindingsFrag emptyOutFrag sc mempty

newtype TopBuilderT (m::MonadKind) (n::S) (a:: *) =
  TopBuilderT { runTopBuilderT' :: InplaceT Bindings TopBindingsFrag m n a }
  deriving ( Functor, Applicative, Monad, MonadFail, Fallible
           , CtxReader, ScopeReader, MonadTrans1, MonadReader r, MonadIO)

instance Fallible m => BindingsReader (TopBuilderT m) where
  getBindings = TopBuilderT $ getOutMapInplaceT

instance Fallible m => TopBuilder (TopBuilderT m) where
  emitBinding hint binding = TopBuilderT $
    emitInplaceT hint binding \b binding' ->
      TopBindingsFrag (toBindingsFrag (b:>binding')) mempty mempty

  emitBindings ab = TopBuilderT do
    extendInplaceT do
      scope <- getScope
      ab' <- injectM ab
      return $ refreshAbs scope ab'

  emitNamelessBindings bs = TopBuilderT $ extendTrivialInplaceT bs

  localTopBuilder cont = TopBuilderT $
    locallyMutableInplaceT $ runTopBuilderT' cont

instance (InjectableV v, TopBuilder m) => TopBuilder (EnvReaderT v m i) where
  emitBinding hint binding = EnvReaderT $ lift $ emitBinding hint binding
  emitBindings ab = EnvReaderT $ lift $ emitBindings ab
  emitNamelessBindings bs = EnvReaderT $ lift $ emitNamelessBindings bs
  localTopBuilder cont = EnvReaderT $ ReaderT \env -> do
    localTopBuilder do
      Distinct <- getDistinct
      runReaderT (runEnvReaderT' cont) (inject env)

runTopBuilderT
  :: (Fallible m, Distinct n)
  => Bindings n
  -> TopBuilderT m n a
  -> m a
runTopBuilderT bindings cont = do
  Immut <- return $ toImmutEvidence bindings
  liftM snd $ runInplaceT bindings $ runTopBuilderT' $ cont

type TopBuilder2 (m :: MonadKind2) = forall i. TopBuilder (m i)

-- === BuilderT ===

type BuilderEmissions = Nest Decl

instance ExtOutMap Bindings BuilderEmissions where
  extendOutMap bindings emissions =
    bindings `extendOutMap` toBindingsFrag emissions

newtype BuilderT (m::MonadKind) (n::S) (a:: *) =
  BuilderT { runBuilderT' :: InplaceT Bindings BuilderEmissions m n a }
  deriving ( Functor, Applicative, Monad, MonadTrans1, MonadFail, Fallible
           , CtxReader, ScopeReader, Alternative, Searcher, MonadWriter w)

type BuilderM = BuilderT HardFailM

runBuilderT
  :: (Fallible m, Distinct n)
  => Bindings n
  -> BuilderT m n a
  -> m a
runBuilderT bindings cont = do
  Immut <- return $ toImmutEvidence bindings
  (Empty, result) <- runInplaceT bindings $ runBuilderT' cont
  return result

runBuilderM :: Distinct n => Bindings n -> BuilderM n a -> a
runBuilderM bindings m = runHardFail $ runBuilderT bindings m

liftBuilder
  :: (BindingsReader m, InjectableE e)
  => (forall l. (Immut l, Distinct l, Ext n l) => BuilderM l (e l))
  -> m n (e n)
liftBuilder cont = liftImmut do
  DB bindings <- getDB
  return $ runBuilderM bindings $ cont

instance Fallible m => Builder (BuilderT m) where
  emitDecl hint ann expr = do
    ty <- getType expr
    BuilderT $ emitInplaceT hint (DeclBinding ann ty expr) \b rhs ->
      Nest (Let b rhs) Empty

  buildScoped cont = BuilderT $
    locallyMutableInplaceT $
      runBuilderT' do
        Emits <- fabricateEmitsEvidenceM
        Distinct <- getDistinct
        cont

instance Fallible m => BindingsReader (BuilderT m) where
  getBindings = BuilderT $ getOutMapInplaceT

instance Fallible m => BindingsExtender (BuilderT m) where
  extendBindings frag cont = BuilderT $
    extendInplaceTLocal (\bindings -> extendOutMap bindings frag) $
      withExtEvidence (toExtEvidence frag) $
        runBuilderT' cont

instance (InjectableV v, Builder m) => Builder (EnvReaderT v m i) where
  emitDecl hint ann expr = EnvReaderT $ lift $ emitDecl hint ann expr
  buildScoped cont = EnvReaderT $ ReaderT \env ->
    buildScoped $
      runReaderT (runEnvReaderT' cont) (inject env)

instance (InjectableE e, Builder m) => Builder (OutReaderT e m) where
  emitDecl hint ann expr =
    OutReaderT $ lift $ emitDecl hint ann expr
  buildScoped cont = OutReaderT $ ReaderT \env ->
    buildScoped do
      env' <- injectM env
      runReaderT (runOutReaderT' cont) env'

-- === Emits predicate ===

-- We use the `Emits` predicate on scope parameters to indicate that we may emit
-- decls. This lets us ensure that a computation *doesn't* emit decls, by
-- supplying a fresh name without supplying the `Emits` predicate.

class Mut n => Emits (n::S)
data EmitsEvidence (n::S) where
  Emits :: Emits n => EmitsEvidence n
instance Emits UnsafeS

fabricateEmitsEvidence :: forall n. EmitsEvidence n
fabricateEmitsEvidence =
  withEmitsEvidence (error "pure fabrication" :: EmitsEvidence n) Emits

fabricateEmitsEvidenceM :: forall m n. Monad1 m => m n (EmitsEvidence n)
fabricateEmitsEvidenceM = return fabricateEmitsEvidence

withEmitsEvidence :: forall n a. EmitsEvidence n -> (Emits n => a) -> a
withEmitsEvidence _ cont = fromWrapWithEmits
 ( TrulyUnsafe.unsafeCoerce ( WrapWithEmits cont :: WrapWithEmits n       a
                                               ) :: WrapWithEmits UnsafeS a)
newtype WrapWithEmits n r =
  WrapWithEmits { fromWrapWithEmits :: Emits n => r }

-- === lambda-like things ===

buildBlock
  :: Builder m
  => (forall l. (Emits l, Ext n l) => m l (Atom l))
  -> m n (Block n)
buildBlock cont = liftImmut do
  DistinctAbs decls results <- buildScoped do
    result <- cont
    ty <- getType result
    return $ result `PairE` ty
  let (result `PairE` ty) = results
  ty' <- liftHoistExcept $ hoist decls ty
  Abs decls' result' <- return $ inlineLastDecl decls $ Atom result
  return $ Block (BlockAnn ty') decls' result'

makeBlock :: (BindingsReader m, BindingsExtender m, Fallible1 m)
          => Nest Decl n l -> Expr l -> m l (Block n)
makeBlock decls expr = do
  ty <- getType expr
  ty' <- liftHoistExcept $ hoist decls ty
  return $ Block (BlockAnn ty') decls expr

inlineLastDecl :: Nest Decl n l -> Expr l -> Abs (Nest Decl) Expr n
inlineLastDecl Empty result = Abs Empty result
inlineLastDecl (Nest (Let b (DeclBinding _ _ expr)) Empty) (Atom (Var v))
  | v == binderName b = Abs Empty expr
inlineLastDecl (Nest decl rest) result =
  case inlineLastDecl rest result of
   Abs decls' result' ->
     Abs (Nest decl decls') result'

buildBlockReduced
  :: Builder m
  => (forall l. (Emits l, Ext n l) => m l (Atom l))
  -> m n (Maybe (Atom n))
buildBlockReduced cont = do
  Block _ decls result <- buildBlock cont
  cheapReduceToAtom $ Abs decls result

buildPureLam :: Builder m
             => NameHint -> Arrow -> Type n
             -> (forall l. (Emits l, Ext n l) => AtomName l -> m l (Atom l))
             -> m n (Atom n)
buildPureLam hint arr ty body =
 buildLamGeneral hint arr ty (const $ return Pure) body

buildLam
  :: Builder m
  => NameHint -> Arrow -> Type n -> EffectRow n
  -> (forall l. (Emits l, Ext n l) => AtomName l -> m l (Atom l))
  -> m n (Atom n)
buildLam hint arr ty eff body = buildLamGeneral hint arr ty (const $ injectM eff) body

buildLamGeneral
  :: Builder m
  => NameHint -> Arrow -> Type n
  -> (forall l. (Immut l, Ext n l) => AtomName l -> m l (EffectRow l))
  -> (forall l. (Emits l, Ext n l) => AtomName l -> m l (Atom l))
  -> m n (Atom n)
buildLamGeneral hint arr ty fEff fBody = liftImmut do
  ty' <- injectM ty
  withFreshBinder hint (LamBinding arr ty') \b -> do
    let v = binderName b
    effs <- fEff v
    body <- withAllowedEffects effs $ buildBlock do
      v' <- injectM v
      fBody v'
    return $ Lam $ LamExpr (LamBinder b ty' arr effs) body

-- Body must be an Atom because otherwise the nullary case would require
-- emitting decls into the enclosing scope.
buildPureNaryLam :: Builder m
                 => EmptyAbs (Nest PiBinder) n
                 -> (forall l. Ext n l => [AtomName l] -> m l (Atom l))
                 -> m n (Atom n)
buildPureNaryLam (EmptyAbs Empty) cont = cont []
buildPureNaryLam (EmptyAbs (Nest (PiBinder b ty arr) rest)) cont = do
  buildPureLam (getNameHint b) arr ty \x -> do
    restAbs <- injectM $ Abs b $ EmptyAbs rest
    rest' <- applyAbs restAbs x
    buildPureNaryLam rest' \xs -> do
      x' <- injectM x
      cont (x':xs)
buildPureNaryLam _ _ = error "impossible"

buildPi :: (Fallible1 m, Builder m)
        => NameHint -> Arrow -> Type n
        -> (forall l. Ext n l => AtomName l -> m l (EffectRow l, Type l))
        -> m n (PiType n)
buildPi hint arr ty body = liftImmut do
  ty' <- injectM ty
  withFreshPiBinder hint (PiBinding arr ty') \b -> do
    (effs, resultTy) <- body $ binderName b
    return $ PiType b effs resultTy

buildNonDepPi :: BindingsReader m
              => NameHint -> Arrow -> Type n -> EffectRow n -> Type n
              -> m n (PiType n)
buildNonDepPi hint arr argTy effs resultTy = liftBuilder do
  argTy' <- injectM argTy
  buildPi hint arr argTy' \_ -> do
    resultTy' <- injectM resultTy
    effs'     <- injectM effs
    return (effs', resultTy')

buildAbs
  :: ( BindingsReader m, BindingsExtender m
     , InjectableE e, NameColor c, ToBinding binding c)
  => NameHint
  -> binding n
  -> (forall l. (Immut l, Ext n l) => Name c l -> m l (e l))
  -> m n (Abs (BinderP c binding) e n)
buildAbs hint binding cont = liftImmut do
  binding' <- injectM binding
  withFreshBinder hint binding' \b -> do
    body <- cont $ binderName b
    return $ Abs (b:>binding') body

singletonBinder :: Builder m => NameHint -> Type n -> m n (EmptyAbs Binder n)
singletonBinder hint ty = buildAbs hint ty \_ -> return UnitE

singletonBinderNest :: Builder m
                    => NameHint -> Type n -> m n (EmptyAbs (Nest Binder) n)
singletonBinderNest hint ty = do
  EmptyAbs b <- singletonBinder hint ty
  return $ EmptyAbs (Nest b Empty)

buildNaryAbs
  :: (Builder m, InjectableE e, SubstE Name e, SubstE AtomSubstVal e, HoistableE e)
  => EmptyAbs (Nest Binder) n
  -> (forall l. (Immut l, Ext n l) => [AtomName l] -> m l (e l))
  -> m n (Abs (Nest Binder) e n)
buildNaryAbs (EmptyAbs Empty) body = liftImmut $ Abs Empty <$> body []
buildNaryAbs (EmptyAbs (Nest (b:>ty) bs)) body = do
  Abs b' (Abs bs' body') <-
    buildAbs (getNameHint b) ty \v -> do
      ab <- injectM $ Abs b (EmptyAbs bs)
      bs' <- applyAbs ab v
      buildNaryAbs bs' \vs -> do
        v' <- injectM v
        body $ v' : vs
  return $ Abs (Nest b' bs') body'
buildNaryAbs _ _ = error "impossible"

buildAlt
  :: Builder m
  => EmptyAbs (Nest Binder) n
  -> (forall l. (Emits l, Ext n l) => [AtomName l] -> m l (Atom l))
  -> m n (Alt n)
buildAlt bs body = do
  buildNaryAbs bs \xs -> do
    buildBlock do
      xs' <- mapM injectM xs
      body xs'

buildUnaryAlt
  :: Builder m
  => Type n
  -> (forall l. (Emits l, Ext n l) => AtomName l -> m l (Atom l))
  -> m n (Alt n)
buildUnaryAlt ty body = do
  bs <- singletonBinderNest NoHint ty
  buildAlt bs \[v] -> body v

buildNewtype :: Builder m
             => SourceName
             -> EmptyAbs (Nest Binder) n
             -> (forall l. (Immut l, Ext n l) => [AtomName l] -> m l (Type l))
             -> m n (DataDef n)
buildNewtype name paramBs body = do
  Abs paramBs' argBs <- buildNaryAbs paramBs \params -> do
    ty <- body params
    singletonBinderNest NoHint ty
  return $ DataDef name paramBs' [DataConDef ("mk" <> name) argBs]

fromNewtype :: [DataConDef n]
            -> Maybe (Type n)
fromNewtype [DataConDef _ (EmptyAbs (Nest (_:>ty) Empty))] = Just ty
fromNewtype _ = Nothing

-- TODO: consider a version with nonempty list of alternatives where we figure
-- out the result type from one of the alts rather than providing it explicitly
buildCase :: (Emits n, Builder m)
          => Atom n -> Type n
          -> (forall l. (Emits l, Ext n l) => Int -> [AtomName l] -> m l (Atom l))
          -> m n (Atom n)
buildCase scrut resultTy indexedAltBody = do
  scrutTy <- getType scrut
  altsBinderTys <- caseAltsBinderTys scrutTy
  alts <- forM (enumerate altsBinderTys) \(i, bs) -> do
    buildNaryAbs bs \xs -> do
      buildBlock do
        ListE xs' <- injectM $ ListE xs
        indexedAltBody i xs'
  liftM Var $ emit $ Case scrut alts resultTy

buildSplitCase :: (Emits n, Builder m)
               => LabeledItems (Type n) -> Atom n -> Type n
               -> (forall l. (Emits l, Ext n l) => AtomName l -> m l (Atom l))
               -> (forall l. (Emits l, Ext n l) => AtomName l -> m l (Atom l))
               -> m n (Atom n)
buildSplitCase tys scrut resultTy match fallback = do
  split <- emitOp $ VariantSplit tys scrut
  buildCase split resultTy \i [v] ->
    case i of
      0 -> match v
      1 -> fallback v
      _ -> error "should only have two cases"

-- === builder versions of common top-level emissions ===

emitDataDef :: (Mut n, TopBuilder m) => DataDef n -> m n (DataDefName n)
emitDataDef dataDef@(DataDef sourceName _ _) =
  emitBinding hint $ DataDefBinding dataDef
  where hint = getNameHint sourceName

emitClassDef :: (Mut n, TopBuilder m) => ClassDef n -> m n (Name ClassNameC n)
emitClassDef classDef@(ClassDef name _ _) =
  emitBinding (getNameHint name) $ ClassBinding classDef

emitDataConName :: (Mut n, TopBuilder m) => DataDefName n -> Int -> m n (Name DataConNameC n)
emitDataConName dataDefName conIdx = do
  DataDef _ _ dataCons <- lookupDataDef dataDefName
  let (DataConDef name _) = dataCons !! conIdx
  emitBinding (getNameHint name) $ DataConBinding dataDefName conIdx

emitSuperclass :: (Mut n ,TopBuilder m)
               => ClassName n -> Int -> m n (Name SuperclassNameC n)
emitSuperclass dataDef idx = do
  getter <- makeSuperclassGetter dataDef idx
  emitSynthCandidates $ SynthCandidates [] [getter] mempty
  emitBinding hint $ SuperclassBinding dataDef idx getter
  where hint = getNameHint $ "Proj" <> show idx <> pprint dataDef

zipNest :: (forall ii ii'. a -> b ii ii' -> b' ii ii')
        -> [a]
        -> Nest b  i i'
        -> Nest b' i i'
zipNest _ _ Empty = Empty
zipNest f (x:t) (Nest b rest) = Nest (f x b) $ zipNest f t rest
zipNest _ _ _ = error "List too short!"

zipPiBinders :: [Arrow] -> Nest Binder i i' -> Nest PiBinder i i'
zipPiBinders = zipNest \arr (b :> ty) -> PiBinder b ty arr

makeSuperclassGetter :: BindingsReader m => Name ClassNameC n -> Int -> m n (Atom n)
makeSuperclassGetter classDefName methodIdx = liftBuilder do
  classDefName' <- injectM classDefName
  ClassDef _ _ defName <- getClassDef classDefName'
  DataDef sourceName paramBs _ <- lookupDataDef defName
  buildPureNaryLam (EmptyAbs $ zipPiBinders (repeat ImplicitArrow) paramBs) \params -> do
    defName' <- injectM defName
    let tc = TypeCon sourceName defName' (map Var params)
    buildPureLam "subclassDict" PlainArrow tc \dict ->
      return $ getProjection [methodIdx] $ getProjection [0, 0] $ Var dict

emitMethodType :: (Mut n, TopBuilder m)
               => NameHint -> ClassName n -> [Bool] -> Int -> m n (Name MethodNameC n)
emitMethodType hint classDef explicit idx = do
  getter <- makeMethodGetter classDef explicit idx
  emitBinding hint $ MethodBinding classDef idx getter

makeMethodGetter :: BindingsReader m => Name ClassNameC n -> [Bool] -> Int -> m n (Atom n)
makeMethodGetter classDefName explicit methodIdx = liftBuilder do
  classDefName' <- injectM classDefName
  ClassDef _ _ defName <- getClassDef classDefName'
  DataDef sourceName paramBs _ <- lookupDataDef defName
  let arrows = explicit <&> \case True -> PlainArrow; False -> ImplicitArrow
  buildPureNaryLam (EmptyAbs $ zipPiBinders arrows paramBs) \params -> do
    defName' <- injectM defName
    buildPureLam "dict" ClassArrow (TypeCon sourceName defName' (map Var params)) \dict ->
      return $ getProjection [methodIdx] $ getProjection [1, 0] $ Var dict

emitTyConName :: (Mut n, TopBuilder m) => DataDefName n -> m n (Name TyConNameC n)
emitTyConName dataDefName =
  emitBinding (getNameHint dataDefName) $ TyConBinding dataDefName

getDataCon :: BindingsReader m => Name DataConNameC n -> m n (DataDefName n, Int)
getDataCon v = do
  ~(DataConBinding defName idx) <- lookupBindings v
  return (defName, idx)

getClassDef :: BindingsReader m => Name ClassNameC n -> m n (ClassDef n)
getClassDef classDefName = do
  ~(ClassBinding classDef) <- lookupBindings classDefName
  return classDef

-- === builder versions of common local ops ===

recGetHead :: BindingsReader m => Label -> Atom n -> m n (Atom n)
recGetHead l x = do
  ~(RecordTy (Ext r _)) <- getType x
  let i = fromJust $ elemIndex l $ map fst $ toList $ reflectLabels r
  return $ getProjection [i] x

fLitLike :: (Builder m, Emits n) => Double -> Atom n -> m n (Atom n)
fLitLike x t = do
  ty <- getType t
  case ty of
    BaseTy (Scalar Float64Type) -> return $ Con $ Lit $ Float64Lit x
    BaseTy (Scalar Float32Type) -> return $ Con $ Lit $ Float32Lit $ realToFrac x
    _ -> error "Expected a floating point scalar"

neg :: (Builder m, Emits n) => Atom n -> m n (Atom n)
neg x = emitOp $ ScalarUnOp FNeg x

add :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
add x y = emitOp $ ScalarBinOp FAdd x y

-- TODO: Implement constant folding for fixed-width integer types as well!
iadd :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
iadd (Con (Lit l)) y | getIntLit l == 0 = return y
iadd x (Con (Lit l)) | getIntLit l == 0 = return x
iadd x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntBinOp (+) x y
iadd x y = emitOp $ ScalarBinOp IAdd x y

mul :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
mul x y = emitOp $ ScalarBinOp FMul x y

imul :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
imul   (Con (Lit l)) y               | getIntLit l == 1 = return y
imul x                 (Con (Lit l)) | getIntLit l == 1 = return x
imul x@(Con (Lit _)) y@(Con (Lit _))                    = return $ applyIntBinOp (*) x y
imul x y = emitOp $ ScalarBinOp IMul x y

sub :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
sub x y = emitOp $ ScalarBinOp FSub x y

isub :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
isub x (Con (Lit l)) | getIntLit l == 0 = return x
isub x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntBinOp (-) x y
isub x y = emitOp $ ScalarBinOp ISub x y

select :: (Builder m, Emits n) => Atom n -> Atom n -> Atom n -> m n (Atom n)
select (Con (Lit (Word8Lit p))) x y = return $ if p /= 0 then x else y
select p x y = emitOp $ Select p x y

div' :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
div' x y = emitOp $ ScalarBinOp FDiv x y

idiv :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
idiv x (Con (Lit l)) | getIntLit l == 1 = return x
idiv x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntBinOp div x y
idiv x y = emitOp $ ScalarBinOp IDiv x y

irem :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
irem x y = emitOp $ ScalarBinOp IRem x y

fpow :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
fpow x y = emitOp $ ScalarBinOp FPow x y

flog :: (Builder m, Emits n) => Atom n -> m n (Atom n)
flog x = emitOp $ ScalarUnOp Log x

ilt :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
ilt x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntCmpOp (<) x y
ilt x y = emitOp $ ScalarBinOp (ICmp Less) x y

ieq :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
ieq x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntCmpOp (==) x y
ieq x y = emitOp $ ScalarBinOp (ICmp Equal) x y

fromPair :: (Builder m, Emits n) => Atom n -> m n (Atom n, Atom n)
fromPair pair = do
  ~[x, y] <- getUnpacked pair
  return (x, y)

getProj :: (Builder m, Emits n) => Int -> Atom n -> m n (Atom n)
getProj i x = do
  xs <- getUnpacked x
  return $ xs !! i

getFst :: (Builder m, Emits n) => Atom n -> m n (Atom n)
getFst p = fst <$> fromPair p

getSnd :: (Builder m, Emits n) => Atom n -> m n (Atom n)
getSnd p = snd <$> fromPair p

getProjRef :: (Builder m, Emits n) => Int -> Atom n -> m n (Atom n)
getProjRef i r = emitOp $ ProjRef i r

-- XXX: getUnpacked must reduce its argument to enforce the invariant that
-- ProjectElt atoms are always fully reduced (to avoid type errors between two
-- equivalent types spelled differently).
getUnpacked :: (Fallible1 m, BindingsReader m) => Atom n -> m n [Atom n]
getUnpacked atom = do
  atom' <- cheapReduce atom
  ty <- getType atom'
  len <- projectLength ty
  return $ map (\i -> getProjection [i] atom') [0..(len-1)]

-- TODO: should we just make all of these return names instead of atoms?
emitUnpacked :: (Builder m, Emits n) => Atom n -> m n [AtomName n]
emitUnpacked tup = do
  xs <- getUnpacked tup
  forM xs \x -> emit $ Atom x

app :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
app x i = Var <$> emit (App x i)

naryApp :: (Builder m, Emits n) => Atom n -> [Atom n] -> m n (Atom n)
naryApp f xs = foldM app f xs

indexAsInt :: (Builder m, Emits n) => Atom n -> m n (Atom n)
indexAsInt idx = emitOp $ ToOrdinal idx

ptrOffset :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
ptrOffset x i = emitOp $ PtrOffset x i

unsafePtrLoad :: (Builder m, Emits n) => Atom n -> m n (Atom n)
unsafePtrLoad x = do
  lam <- buildLam "_ign" PlainArrow UnitTy (oneEffect IOEffect) \_ ->
    ptrLoad =<< injectM x
  liftM Var $ emit $ Hof $ RunIO $ lam

ptrLoad :: (Builder m, Emits n) => Atom n -> m n (Atom n)
ptrLoad x = emitOp $ PtrLoad x

-- === index set type class ===

clampPositive :: (Builder m, Emits n) => Atom n -> m n (Atom n)
clampPositive x = do
  isNegative <- x `ilt` (IdxRepVal 0)
  select isNegative (IdxRepVal 0) x

intToIndex :: (Builder m, Emits n) => Type n -> Atom n -> m n (Atom n)
intToIndex ty i = case ty of
  TC con -> case con of
    IntRange        low high   -> return $ Con $ IntRangeVal        low high i
    IndexRange from low high   -> return $ Con $ IndexRangeVal from low high i

indexToInt :: (Builder m, Emits n) => Atom n -> m n (Atom n)
indexToInt (Con (IntRangeVal _ _ i))     = return i
indexToInt (Con (IndexRangeVal _ _ _ i)) = return i
indexToInt idx = getType idx >>= \case
  TC (IntRange _ _)     -> indexAsInt idx
  TC (IndexRange _ _ _) -> indexAsInt idx
  TC (ParIndexRange _ _ _) -> error "Int casts unsupported on ParIndexRange"

indexSetSize :: (Builder m, Emits n) => Type n -> m n (Atom n)
indexSetSize (TC con) = case con of
  IntRange low high -> clampPositive =<< high `isub` low
  SumType types -> foldM iadd (IdxRepVal 0) =<< traverse indexSetSize types
  IndexRange n low high -> do
    low' <- case low of
      InclusiveLim x -> indexToInt x
      ExclusiveLim x -> indexToInt x >>= iadd (IdxRepVal 1)
      Unlimited      -> return $ IdxRepVal 0
    high' <- case high of
      InclusiveLim x -> indexToInt x >>= iadd (IdxRepVal 1)
      ExclusiveLim x -> indexToInt x
      Unlimited      -> indexSetSize n
    clampPositive =<< high' `isub` low'
  ProdType tys -> foldM imul (IdxRepVal 1) =<< traverse indexSetSize tys
  ParIndexRange _ _ _ -> error "Shouldn't be querying the size of a ParIndexRange"
  _ -> error $ "Not implemented " ++ pprint con
indexSetSize (RecordTy (NoExt types)) = do
  sizes <- traverse indexSetSize types
  foldM imul (IdxRepVal 1) sizes
indexSetSize (VariantTy (NoExt types)) = do
  sizes <- traverse indexSetSize types
  foldM iadd (IdxRepVal 0) sizes
indexSetSize ty = error $ "Not implemented " ++ pprint ty
