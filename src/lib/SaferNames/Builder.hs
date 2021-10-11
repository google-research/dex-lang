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

module SaferNames.Builder (
  emit, emitOp, buildLamGeneral,
  buildPureLam, BuilderT, Builder (..), Builder2, EffectsReader (..),
  emitDecl, emitBinding, buildScoped, buildScopedTop, ScopedBuilderResult (..),
  runBuilderT, buildBlock, buildBlockReduced, app, add, mul, sub, neg, div',
  iadd, imul, isub, idiv, ilt, ieq, irem,
  fpow, flog, fLitLike, recGetHead, buildPureNaryLam,
  emitMethodType, emitSuperclass,
  makeSuperclassGetter, makeMethodGetter,
  select, getUnpacked, emitUnpacked,
  fromPair, getFst, getSnd, getProj, getProjRef, naryApp,
  getDataDef, getClassDef, getDataCon, atomAsBlock,
  Emits, EmitsTop, buildPi, buildNonDepPi, buildLam, buildDepEffLam,
  buildAbs, buildNaryAbs, buildAlt, buildUnaryAlt, buildNewtype, fromNewtype,
  emitDataDef, emitClassDef, emitDataConName, emitTyConName,
  buildCase, buildSplitCase,
  emitBlock, BuilderEmissions, emitAtomToName,
  withFabricatedEmitsEvidence, withFabricatedEmitsTopEvidence,
  BuilderEmission (..), fromBuilderDecls, fromBuilderBindings,
  ) where

import Prelude hiding ((.), id)
import Control.Monad
import Data.Foldable (toList)
import Data.List (elemIndex)
import Data.Maybe (fromJust)

import Unsafe.Coerce

import SaferNames.Name
import SaferNames.Syntax
import SaferNames.Type
import SaferNames.PPrint ()
import SaferNames.CheapReduction

import LabeledItems
import Util (enumerate)
import Err

class EffectsReader (m::MonadKind1) where
  getAllowedEffects :: m n (EffectRow n)
  withAllowedEffects :: EffectRow n -> m n a -> m n a

class (BindingsReader m, EffectsReader m, Scopable m, MonadFail1 m)
      => Builder (m::MonadKind1) where
  -- This is unsafe because it doesn't require the Emits predicate. `emitDecl`
  -- and `emitBinding` wrap it safely.
  unsafeEmitBuilder :: NameColor c => NameHint -> BuilderEmission c n -> m n (Name c n)
  buildScopedGeneral
    :: ( SubstE Name e , InjectableE e
       , HasNamesE   e', InjectableE e'
       , SubstB Name b, BindsBindings b)
    => Abs b e n
    -> (forall l. (Ext n l, Distinct l) => e l -> m l (e' l))
    -> m n (ScopedBuilderResult b e' n)

data ScopedBuilderResult (b::B) (e::E) (n::S) where
  ScopedBuilderResult :: (Distinct l2, Ext l1 n)
                      => PairB b BuilderEmissions l1 l2 -> e l2
                      -> ScopedBuilderResult b e n

emitDecl :: (Builder m, Emits n) => NameHint -> LetAnn -> Expr n -> m n (AtomName n)
emitDecl hint ann expr = do
  ty <- getType expr
  unsafeEmitBuilder hint $ BuilderEmitDecl $ DeclBinding ann ty expr

emitBinding :: (Builder m, EmitsTop n, NameColor c) => NameHint -> Binding c n -> m n (Name c n)
emitBinding hint binding = unsafeEmitBuilder hint $ BuilderEmitTopDecl binding

buildScoped
  :: (HasNamesE e, InjectableE e, Builder m)
  => (forall l. (Emits l, Ext n l) => m l (e l))
  -> m n (Abs (Nest Decl) e n)
buildScoped cont = do
  scopedResult <- buildScopedGeneral (Abs UnitB UnitE) \UnitE ->
      withFabricatedEmitsEvidence cont
  ScopedBuilderResult (PairB UnitB emissions) result <- return scopedResult
  injectM $ Abs (fromBuilderDecls emissions) result

buildScopedTop
  :: (HasNamesE e, InjectableE e, Builder m)
  => (forall l. (EmitsTop l, Ext n l) => m l (e l))
  -> m n (Abs (RecEnvFrag Binding) e n)
buildScopedTop cont = do
  scopedResult <- buildScopedGeneral (Abs UnitB UnitE) \UnitE ->
    withFabricatedEmitsTopEvidence cont
  ScopedBuilderResult (PairB UnitB emissions) result <- return scopedResult
  injectM $ Abs (fromBuilderBindings emissions) result

type Builder2       (m :: MonadKind2) = forall i. Builder (m i)

emit :: (Builder m, Emits n) => Expr n -> m n (AtomName n)
emit expr = emitDecl NoHint PlainLet expr

emitOp :: (Builder m, Emits n) => Op n -> m n (Atom n)
emitOp op = Var <$> emit (Op op)

emitBlock :: (Builder m, Emits n) => Block n -> m n (Atom n)
emitBlock (Block _ Empty (Atom result)) = return result
emitBlock _ = undefined

emitAtomToName :: (Builder m, Emits n) => Atom n -> m n (AtomName n)
emitAtomToName (Var v) = return v
emitAtomToName x = emit (Atom x)

-- === BuilderT ===

-- newtype just for the different OutMap instance
newtype BuilderBindings n = BuilderBindings (Bindings n)
type BuilderEmissions = Nest (SomeDecl BuilderEmission)

data BuilderEmission c n where
  BuilderEmitDecl    :: DeclBinding n -> BuilderEmission AtomNameC n
  BuilderEmitTopDecl :: Binding c n   -> BuilderEmission c         n

instance HasScope BuilderBindings where
  toScope (BuilderBindings bindings) = toScope bindings

instance OutMap BuilderBindings BuilderEmissions where
  emptyOutMap = BuilderBindings emptyOutMap
  extendOutMap (BuilderBindings bindings) emissions =
    BuilderBindings $ bindings `extendOutMap` boundBindings emissions

instance NameColor c => GenericE (BuilderEmission c) where
  type RepE (BuilderEmission c) = EitherE DeclBinding (Binding c)
  fromE (BuilderEmitDecl    x) = LeftE  x
  fromE (BuilderEmitTopDecl x) = RightE x

  toE (LeftE x) =
    case eqNameColorRep (nameColorRep::NameColorRep c)
                        (nameColorRep::NameColorRep AtomNameC) of
      Just ColorsEqual -> BuilderEmitDecl x
      Nothing -> error "shouldn't happen"
  toE (RightE x) = BuilderEmitTopDecl x

instance NameColor c => ToBinding (BuilderEmission c) c where
  toBinding (BuilderEmitDecl declBinding) = toBinding declBinding
  toBinding (BuilderEmitTopDecl binding) = binding

instance InjectableV         BuilderEmission
instance HoistableV          BuilderEmission
instance SubstV Name         BuilderEmission
instance SubstV AtomSubstVal BuilderEmission
instance NameColor c => InjectableE         (BuilderEmission c)
instance NameColor c => HoistableE          (BuilderEmission c)
instance NameColor c => SubstE Name         (BuilderEmission c)
instance NameColor c => SubstE AtomSubstVal (BuilderEmission c)

newtype BuilderT (m::MonadKind) (n::S) (a:: *) =
  BuilderT { runBuilderT' :: InplaceT BuilderBindings BuilderEmissions m n a }
  deriving (Functor, Applicative, Monad)

runBuilderT
  :: (MonadFail m, Distinct n)
  => Distinct n => Bindings n
  -> (forall l. (Distinct l, Ext n l) => BuilderT m l (e l))
  -> m (e n)
runBuilderT bindings cont = do
  DistinctAbs decls result <- runInplaceT (BuilderBindings bindings) $ runBuilderT' cont
  case decls of
    Empty -> return result
    _ -> error "shouldn't have produced any decls"

instance MonadFail m => EffectsReader (BuilderT m) where
  getAllowedEffects = undefined
  withAllowedEffects = undefined

instance MonadFail m => Builder (BuilderT m) where
  unsafeEmitBuilder hint rhs = BuilderT $
    emitInplace hint rhs \b rhs' -> Nest (SomeDecl b rhs') Empty
  buildScopedGeneral ab cont = BuilderT do
    scopedResult <- scopedInplaceGeneral
      (\(BuilderBindings bindings) b ->
           BuilderBindings $ bindings `extendOutMap` boundBindings b)
      ab
      (\e -> runBuilderT' $ cont e)
    ScopedResult _ (PairB b emissions) result <- return scopedResult
    return $ ScopedBuilderResult (PairB b emissions) result

fromBuilderDecls :: BuilderEmissions n l -> Nest Decl n l
fromBuilderDecls emissions = fromJust $ forEachNestItem emissions fromBuilderDecl
  where
    fromBuilderDecl :: SomeDecl BuilderEmission n l -> Maybe (Decl n l)
    fromBuilderDecl (SomeDecl b emission) = case emission of
      BuilderEmitDecl declBinding -> return $ Let b declBinding
      BuilderEmitTopDecl _ -> Nothing

fromBuilderBindings :: Distinct l => BuilderEmissions n l -> BindingsFrag n l
fromBuilderBindings Empty = emptyOutFrag
fromBuilderBindings (Nest (SomeDecl b emission) rest) = case emission of
  BuilderEmitDecl _ -> error "Expected bindings fragment emission"
  BuilderEmitTopDecl binding -> withSubscopeDistinct rest $
    boundBindings (b:>binding) `catRecEnvFrags` fromBuilderBindings rest

deriving instance MonadFail m => MonadFail (BuilderT m n)
deriving instance MonadFail m => ScopeReader (BuilderT m)

instance MonadFail m => BindingsReader (BuilderT m) where
  addBindings _ = undefined

instance MonadFail m => Scopable (BuilderT m) where
  withBindings ab cont = do
    ScopedBuilderResult (PairB b Empty) result <- buildScopedGeneral ab \x -> cont x
    injectM $ Abs b result

-- === Emits predicate ===

-- We use the `Emits` predicate on scope parameters to indicate that we may emit
-- decls. This lets us ensure that a computation *doesn't* emit decls, by
-- supplying a fresh name without supplying the `Emits` predicate.

data EmitsEvidence (n::S) = FabricateEmitsEvidence

class Emits (n::S)

instance Emits UnsafeS

withFabricatedEmitsEvidence :: forall n m a. Monad1 m => (Emits n => m n a) -> m n a
withFabricatedEmitsEvidence cont = do
  evidence <- fabricateEmitsEvidenceM
  withEmitsEvidence evidence cont

withEmitsEvidence :: forall n a. EmitsEvidence n -> (Emits n => a) -> a
withEmitsEvidence _ cont = fromWrapWithEmits
 ( unsafeCoerce ( WrapWithEmits cont :: WrapWithEmits n       a
                                   ) :: WrapWithEmits UnsafeS a)

newtype WrapWithEmits n r =
  WrapWithEmits { fromWrapWithEmits :: Emits n => r }

fabricateEmitsEvidenceM :: Monad1 m => m n (EmitsEvidence n)
fabricateEmitsEvidenceM = return FabricateEmitsEvidence

-- === EmitsTop predicate ===

-- permission to emit top-level bindings

data EmitsTopEvidence (n::S) = FabricateEmitsTopEvidence

class EmitsTop (n::S)

instance EmitsTop UnsafeS

withFabricatedEmitsTopEvidence :: forall n m a. Monad1 m => (EmitsTop n => m n a) -> m n a
withFabricatedEmitsTopEvidence cont = do
  evidence <- fabricateEmitsTopEvidenceM
  withEmitsTopEvidence evidence cont

withEmitsTopEvidence :: forall n a. EmitsTopEvidence n -> (EmitsTop n => a) -> a
withEmitsTopEvidence _ cont = fromWrapWithEmitsTop
 ( unsafeCoerce ( WrapWithEmitsTop cont :: WrapWithEmitsTop n       a
                                      ) :: WrapWithEmitsTop UnsafeS a)

newtype WrapWithEmitsTop n r =
  WrapWithEmitsTop { fromWrapWithEmitsTop :: EmitsTop n => r }

fabricateEmitsTopEvidenceM :: Monad1 m => m n (EmitsTopEvidence n)
fabricateEmitsTopEvidenceM = return FabricateEmitsTopEvidence

-- === lambda-like things ===

buildBlockAux :: Builder m
           => (forall l. (Emits l, Ext n l) => m l (Atom l, a))
           -> m n (Block n, a)
buildBlockAux cont = do
  Abs decls results <- buildScoped do
    (result, aux) <- cont
    ty <- getType result
    return $ result `PairE` ty `PairE` LiftE aux
  let (result `PairE` ty `PairE` LiftE aux) = results
  ty' <- liftMaybe $ hoist decls ty
  return (Block ty' decls $ Atom result, aux)

buildBlockReduced :: Builder m
                  => (forall l. (Emits l, Ext n l) => m l (Atom l))
                  -> m n (Maybe (Atom n))
buildBlockReduced cont = do
  block <- buildBlock cont
  cheapReduceBlockToAtom block

buildBlock :: Builder m
           => (forall l. (Emits l, Ext n l) => m l (Atom l))
           -> m n (Block n)
buildBlock cont = fst <$> buildBlockAux do
  result <- cont
  return (result, ())

atomAsBlock :: BindingsReader m => Atom n -> m n (Block n)
atomAsBlock x = do
  ty <- getType x
  return $ Block ty Empty $ Atom x

buildLamGeneral
  :: Builder m
  => Arrow
  -> Type n
  -> (forall l. (         Ext n l) => AtomName l -> m l (EffectRow l))
  -> (forall l. (Emits l, Ext n l) => AtomName l -> m l (Atom l, a))
  -> m n (Atom n, a)
buildLamGeneral arr ty fEff fBody = do
  ext1 <- idExt
  ab <- withFreshBinder NoHint (LamBinding arr ty) \v -> do
    ext2 <- injectExt ext1
    effs <- fEff v
    withAllowedEffects effs do
      (body, aux) <- buildBlockAux do
        ExtW <- injectExt ext2
        v' <- injectM v
        fBody v'
      return $ effs `PairE` body `PairE` LiftE aux
  Abs b (effs `PairE` body `PairE` LiftE aux) <- return ab
  return (Lam $ LamExpr b effs body, aux)

buildPureLam :: Builder m
             => Arrow
             -> Type n
             -> (forall l. (Emits l, Ext n l) => AtomName l -> m l (Atom l))
             -> m n (Atom n)
buildPureLam arr ty body =
  fst <$> buildLamGeneral arr ty (const $ return Pure) \x ->
    withAllowedEffects Pure do
      result <- body x
      return (result, ())

buildLam
  :: Builder m
  => Arrow
  -> Type n
  -> EffectRow n
  -> (forall l. (Emits l, Ext n l) => AtomName l -> m l (Atom l))
  -> m n (Atom n)
buildLam arr ty eff body = buildDepEffLam arr ty (const $ injectM eff) body

buildDepEffLam
  :: Builder m
  => Arrow
  -> Type n
  -> (forall l. (         Ext n l) => AtomName l -> m l (EffectRow l))
  -> (forall l. (Emits l, Ext n l) => AtomName l -> m l (Atom l))
  -> m n (Atom n)
buildDepEffLam arr ty effBuilder body =
  fst <$> buildLamGeneral arr ty effBuilder (\v -> (,()) <$> body v)

-- Body must be an Atom because otherwise the nullary case would require
-- emitting decls into the enclosing scope.
buildPureNaryLam :: Builder m
                 => Arrow
                 -> EmptyAbs (Nest Binder) n
                 -> (forall l. Ext n l => [AtomName l] -> m l (Atom l))
                 -> m n (Atom n)
buildPureNaryLam _ (EmptyAbs Empty) cont = cont []
buildPureNaryLam arr (EmptyAbs (Nest (b:>ty) rest)) cont = do
  ext1 <- idExt
  buildPureLam arr ty \x -> do
    ext2 <- injectExt ext1
    restAbs <- injectM $ Abs b $ EmptyAbs rest
    rest' <- applyAbs restAbs x
    buildPureNaryLam arr rest' \xs -> do
      ExtW <- injectExt ext2
      x' <- injectM x
      cont (x':xs)
buildPureNaryLam _ _ _ = error "impossible"

buildPi :: (Fallible1 m, Builder m)
        => Arrow -> Type n
        -> (forall l. Ext n l => AtomName l -> m l (EffectRow l, Type l))
        -> m n (Type n)
buildPi arr ty body = do
  ab <- withFreshBinder NoHint ty \v -> do
    withAllowedEffects Pure do
      (effs, resultTy) <- body v
      return $ PairE effs resultTy
  Abs b (PairE effs resultTy) <- return ab
  return $ Pi $ PiType arr b effs resultTy

buildNonDepPi :: (Fallible1 m, Builder m)
              => Arrow -> Type n -> EffectRow n -> Type n -> m n (Type n)
buildNonDepPi arr argTy effs resultTy = buildPi arr argTy \_ -> do
  resultTy' <- injectM resultTy
  effs'     <- injectM effs
  return (effs', resultTy')

buildAbs
  :: ( Builder m, InjectableE e, HasNamesE e, HoistableE e
     , NameColor c, ToBinding binding c)
  => binding n
  -> (forall l. Ext n l => Name c l -> m l (e l))
  -> m n (Abs (BinderP c binding) e n)
buildAbs binding body = withFreshBinder NoHint binding body

singletonBinder :: Builder m => Type n -> m n (EmptyAbs Binder n)
singletonBinder ty = buildAbs ty \_ -> return UnitE

singletonBinderNest :: Builder m => Type n -> m n (EmptyAbs (Nest Binder) n)
singletonBinderNest ty = do
  EmptyAbs b <- singletonBinder ty
  return $ EmptyAbs (Nest b Empty)

buildNaryAbs
  :: (Builder m, InjectableE e, HasNamesE e)
  => EmptyAbs (Nest Binder) n
  -> (forall l. Ext n l => [AtomName l] -> m l (e l))
  -> m n (Abs (Nest Binder) e n)
buildNaryAbs (EmptyAbs Empty) body = Abs Empty <$> body []
buildNaryAbs (EmptyAbs (Nest (b:>ty) bs)) body = do
  ext1 <- idExt
  Abs b' (Abs bs' body') <-
    buildAbs ty \v -> do
      ext2 <- injectExt ext1
      ab <- injectM $ Abs b (EmptyAbs bs)
      bs' <- applyAbs ab v
      buildNaryAbs bs' \vs -> do
        ExtW <- injectExt ext2
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
  ext1 <- idExt
  buildNaryAbs bs \xs -> do
    ext2 <- injectExt ext1
    buildBlock do
      ExtW <- injectExt ext2
      xs' <- mapM injectM xs
      body xs'

buildUnaryAlt
  :: Builder m
  => Type n
  -> (forall l. (Emits l, Ext n l) => AtomName l -> m l (Atom l))
  -> m n (Alt n)
buildUnaryAlt ty body = do
  bs <- singletonBinderNest ty
  buildAlt bs \[v] -> body v

buildNewtype :: Builder m
             => SourceName
             -> EmptyAbs (Nest Binder) n
             -> (forall l. Ext n l => [AtomName l] -> m l (Type l))
             -> m n (DataDef n)
buildNewtype name paramBs body = do
  Abs paramBs' argBs <- buildNaryAbs paramBs \params -> do
    ty <- body params
    singletonBinderNest ty
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
  ext1 <- idExt
  scrutTy <- getType scrut
  altsBinderTys <- caseAltsBinderTys scrutTy
  alts <- forM (enumerate altsBinderTys) \(i, bs) -> do
    buildNaryAbs bs \xs -> do
      ext2 <- injectExt ext1
      buildBlock do
        ExtW <- injectExt ext2
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

-- === builder versions of common ops ===

emitDataDef :: (EmitsTop n, Builder m) => DataDef n -> m n (DataDefName n)
emitDataDef dataDef =
  emitBinding NoHint $ DataDefBinding dataDef

emitClassDef :: (EmitsTop n, Builder m) => ClassDef n -> m n (Name ClassNameC n)
emitClassDef classDef@(ClassDef name _ _) =
  emitBinding (getNameHint name) $ ClassBinding classDef

emitDataConName :: (EmitsTop n, Builder m) => DataDefName n -> Int -> m n (Name DataConNameC n)
emitDataConName dataDefName conIdx = do
  DataDef _ _ dataCons <- getDataDef dataDefName
  let (DataConDef name _) = dataCons !! conIdx
  emitBinding (getNameHint name) $ DataConBinding dataDefName conIdx

emitSuperclass :: (EmitsTop n, Builder m)
               => ClassName n -> Int -> m n (Name SuperclassNameC n)
emitSuperclass dataDef idx = do
  getter <- makeSuperclassGetter dataDef idx
  emitBinding NoHint $ SuperclassBinding dataDef idx getter

makeSuperclassGetter :: Builder m => Name ClassNameC n -> Int -> m n (Atom n)
makeSuperclassGetter classDefName methodIdx = do
  ClassDef _ _ (defName, def@(DataDef _ paramBs _)) <- getClassDef classDefName
  buildPureNaryLam ImplicitArrow (EmptyAbs paramBs) \params -> do
    defName' <- injectM defName
    def'     <- injectM def
    buildPureLam PlainArrow (TypeCon (defName', def') (map Var params)) \dict ->
      return $ getProjection [methodIdx] $ getProjection [0, 0] $ Var dict

emitMethodType :: (EmitsTop n, Builder m)
               => NameHint -> ClassName n -> Int -> m n (Name MethodNameC n)
emitMethodType hint classDef idx = do
  getter <- makeMethodGetter classDef idx
  emitBinding hint $ MethodBinding classDef idx getter

makeMethodGetter :: Builder m => Name ClassNameC n -> Int -> m n (Atom n)
makeMethodGetter classDefName methodIdx = do
  ClassDef _ _ (defName, def@(DataDef _ paramBs _)) <- getClassDef classDefName
  buildPureNaryLam ImplicitArrow (EmptyAbs paramBs) \params -> do
    defName' <- injectM defName
    def'     <- injectM def
    buildPureLam ClassArrow (TypeCon (defName', def') (map Var params)) \dict ->
      return $ getProjection [methodIdx] $ getProjection [1, 0] $ Var dict

emitTyConName :: (EmitsTop n, Builder m) => DataDefName n -> m n (Name TyConNameC n)
emitTyConName dataDefName =
  emitBinding (getNameHint dataDefName) $ TyConBinding dataDefName

getDataDef :: Builder m => DataDefName n -> m n (DataDef n)
getDataDef v = do
  DataDefBinding def <- lookupBindings v
  return def

getDataCon :: Builder m => Name DataConNameC n -> m n (DataDefName n, Int)
getDataCon v = do
  DataConBinding defName idx <- lookupBindings v
  return (defName, idx)

getClassDef :: BindingsReader m => Name ClassNameC n -> m n (ClassDef n)
getClassDef classDefName = do
  ~(ClassBinding classDef) <- lookupBindings classDefName
  return classDef

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
getUnpacked :: (Builder m, Emits n) => Atom n -> m n [Atom n]
getUnpacked = undefined
-- getUnpacked (ProdVal xs) = return xs
-- getUnpacked atom = do
--   scope <- getScope
--   let len = projectLength $ getType atom
--       atom' = typeReduceAtom scope atom
--       res = map (\i -> getProjection [i] atom') [0..(len-1)]
--   return res

-- TODO: should we just make all of these return names instead of atoms?
emitUnpacked :: (Builder m, Emits n) => Atom n -> m n [AtomName n]
emitUnpacked =  undefined

app :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
app x i = Var <$> emit (App x i)

naryApp :: (Builder m, Emits n) => Atom n -> [Atom n] -> m n (Atom n)
naryApp f xs = foldM app f xs
