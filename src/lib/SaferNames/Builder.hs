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
  buildPureLam, BuilderT, Builder (..), Builder2,
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
  emitBlock, BuilderEmissions (..), emitAtomToName,
  withEmitsEvidence, fabricateEmitsEvidenceM,
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

import LabeledItems
import Util (enumerate)

class (BindingsReader m, Scopable m, MonadFail1 m)
      => Builder (m::MonadKind1) where
  emitDecl :: Emits n => NameHint -> LetAnn -> Expr n -> m n (AtomName n)
  emitBinding :: (EmitsTop n, NameColor c) => NameHint -> Binding c n -> m n (Name c n)
  buildScoped :: HasNamesE e
              => (forall l. (Emits l, Ext n l) => m l (e l))
              -> m n (Abs (Nest Decl) e n)

  buildScopedTop :: HasNamesE e
                 => (forall l. (EmitsTop l, Ext n l) => m l (e l))
                 -> m n (Abs (RecEnvFrag Binding) e n)
  getAllowedEffects :: m n (EffectRow n)
  withAllowedEffects :: EffectRow n -> m n a -> m n a

type Builder2       (m :: MonadKind2) = forall i. Builder (m i)

emit :: (Builder m, Emits n) => Expr n -> m n (AtomName n)
emit expr = emitDecl NoHint PlainLet expr

emitOp :: (Builder m, Emits n) => Op n -> m n (Atom n)
emitOp op = Var <$> emit (Op op)

emitBlock :: (Builder m, Emits n) => Block n -> m n (Atom n)
emitBlock = undefined

emitAtomToName :: (Builder m, Emits n) => Atom n -> m n (AtomName n)
emitAtomToName (Var v) = return v
emitAtomToName x = emit (Atom x)

-- === BuilderT ===

-- newtype just for the different OutMap instance
newtype BuilderBindings n = BuilderBindings (Bindings n)
-- newtype because we have a slightly different OutFrag instance
newtype BuilderEmissions n l =
  BuilderEmissions (Nest (EitherB Decl BindingsFrag) n l)
  deriving (InjectableB, SubstB Name, ProvesExt, BindsNames, BindsBindings)
instance OutFrag BuilderEmissions where
  emptyOutFrag = BuilderEmissions Empty
  -- TODO: this is a hack. It would be better to somehow avoid losing the
  -- `Distinct l` constraint. It's just hard to make it safe.
  -- We merge/inject bindings fragments here rather than later because later we
  -- won't have access to `Distinct l` later. We could still do a renaming subst
  -- would get expensive with deeply nested scopes.
  catOutFrags (BuilderEmissions (Nest (RightB frag) Empty))
              (BuilderEmissions (Nest (RightB frag') rest)) =
    withSubscopeDistinct (toExtEvidence rest) $
      BuilderEmissions $ Nest (RightB (catOutFrags frag frag')) rest
  catOutFrags (BuilderEmissions nest) (BuilderEmissions nest') =
    BuilderEmissions $ catOutFrags nest nest'

instance HasScope BuilderBindings where
  toScope = undefined

instance OutMap BuilderBindings BuilderEmissions where
  emptyOutMap = BuilderBindings emptyOutMap
  extendOutMap (BuilderBindings bindings) emissions =
    BuilderBindings $ bindings `extendOutMap` boundBindings emissions

newtype BuilderT (m::MonadKind) (n::S) (a:: *) =
  BuilderT { runBuilderT' :: InplaceT BuilderBindings BuilderEmissions m n a }
  deriving (Functor, Applicative, Monad)

runBuilderT
  :: (MonadFail m, Distinct n)
  => Distinct n => Bindings n
  -> (forall l. (Distinct l, Ext n l) => BuilderT m l (e l))
  -> m (e n)
runBuilderT bindings cont = do
  Abs decls result <- runInplaceT (BuilderBindings bindings) $ runBuilderT' cont
  case decls of
    BuilderEmissions Empty -> return result
    _ -> error "shouldn't have produced any decls"

instance MonadFail m => Builder (BuilderT m) where
  emitDecl hint ann expr = do
    ty <- getType expr
    BuilderT $
      emitInplace hint (PairE expr ty) \b (PairE expr' ty') -> do
        let decl = Let ann (b:>ty') expr'
        BuilderEmissions $ Nest (LeftB decl) Empty

  emitBinding hint binding = BuilderT do
    emitInplace hint binding \b binding' -> do
      let frag = RecEnvFrag $ b @> inject binding'
      BuilderEmissions $ Nest (RightB frag) Empty

  buildScoped cont = BuilderT do
    Abs emissions result <- scopedInplace do
      evidence <- fabricateEmitsEvidenceM
      withEmitsEvidence evidence $ runBuilderT' cont
    Just decls <- return $ fromBuilderDecls emissions
    return (Abs decls result)

  buildScopedTop cont = BuilderT do
    Abs emissions result <- scopedInplace do
      evidence <- fabricateEmitsTopEvidenceM
      withEmitsTopEvidence evidence $ runBuilderT' cont
    Just decls <- return $ fromBuilderBindings emissions
    return (Abs decls result)

  getAllowedEffects = undefined
  withAllowedEffects _ _ = undefined

fromBuilderDecls :: BuilderEmissions n l -> Maybe (Nest Decl n l)
fromBuilderDecls (BuilderEmissions nest) = case nest of
  Nest builderDecl rest -> case builderDecl of
    LeftB decl -> Nest decl <$> fromBuilderDecls (BuilderEmissions rest)
    RightB _ -> Nothing
  Empty -> return Empty

fromBuilderBindings :: BuilderEmissions n l -> Maybe (BindingsFrag n l)
-- Expect a singleton nest, because of the special case we handle in
-- the OutFrag instance for BuilderEmissions
fromBuilderBindings (BuilderEmissions (Nest (RightB frag) Empty)) = return frag
fromBuilderBindings _ = Nothing

deriving instance MonadFail m => MonadFail (BuilderT m n)
deriving instance MonadFail m => ScopeReader (BuilderT m)

instance MonadFail m => BindingsReader (BuilderT m) where
  addBindings _ = undefined

instance MonadFail m => Scopable (BuilderT m) where
  withBindings _ _ = undefined

-- === Emits predicate ===

-- We use the `Emits` predicate on scope parameters to indicate that we may emit
-- decls. This lets us ensure that a computation *doesn't* emit decls, by
-- supplying a fresh name without supplying the `Emits` predicate.

data EmitsEvidence (n::S) = FabricateEmitsEvidence

class Emits (n::S)

instance Emits UnsafeS

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
  Abs decls (result `PairE` ty `PairE` LiftE aux) <- buildScoped do
    (result, aux) <- cont
    ty <- getType result
    return $ result `PairE` ty `PairE` LiftE aux
  ty' <- fromConstAbsM $ Abs decls ty
  return (Block ty' decls $ Atom result, aux)

buildBlockReduced :: Builder m
                  => (forall l. (Emits l, Ext n l) => m l (Atom l))
                  -> m n (Maybe (Atom n))
buildBlockReduced cont = do
  block <- buildBlock cont
  tryReduceBlock block

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

data BinderWithInfo n l =
  BinderWithInfo (Binder n l) (AtomBinderInfo n)

instance GenericB BinderWithInfo where
  type RepB BinderWithInfo = BinderP Binder AtomBinderInfo
  fromB (BinderWithInfo b info) = b:>info
  toB   (b:>info) = BinderWithInfo b info

instance ProvesExt   BinderWithInfo
instance BindsNames  BinderWithInfo
instance InjectableB BinderWithInfo
instance SubstB Name BinderWithInfo
instance BindsBindings BinderWithInfo where
  boundBindings (BinderWithInfo (b:>ty) info) =
    withExtEvidence b $
      RecEnvFrag $ b @> inject (AtomNameBinding ty info)

withFreshAtomBinder :: (Scopable m, SubstE Name e)
                    => NameHint -> Type n -> AtomBinderInfo n
                    -> (forall l. Ext n l => AtomName l -> m l (e l))
                    -> m n (Abs Binder e n)
withFreshAtomBinder hint ty info cont = do
  Abs b name <- freshBinderNamePair hint
  Abs (BinderWithInfo b' _) body <-
    withBindings (Abs (BinderWithInfo (b:>ty) info) name) cont
  return $ Abs b' body

buildLamGeneral
  :: Builder m
  => Arrow
  -> Type n
  -> (forall l. (         Ext n l) => AtomName l -> m l (EffectRow l))
  -> (forall l. (Emits l, Ext n l) => AtomName l -> m l (Atom l, a))
  -> m n (Atom n, a)
buildLamGeneral arr ty fEff fBody = do
  ext1 <- idExt
  ab <- withFreshAtomBinder NoHint ty (LamBound arr) \v -> do
    ext2 <- injectExt ext1
    effs <- fEff v
    withAllowedEffects effs do
      (body, aux) <- buildBlockAux do
        ExtW <- injectExt ext2
        v' <- injectM v
        fBody v'
      return $ effs `PairE` body `PairE` LiftE aux
  Abs b (effs `PairE` body `PairE` LiftE aux) <- return ab
  return (Lam $ LamExpr arr b effs body, aux)

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
  ab <- withFreshAtomBinder NoHint ty PiBound \v -> do
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
  :: (Builder m, HasNamesE e)
  => Type n
  -> (forall l. Ext n l => AtomName l -> m l (e l))
  -> m n (Abs Binder e n)
buildAbs ty body = do
  withFreshAtomBinder NoHint ty MiscBound \v -> do
    body v

singletonBinder :: Builder m => Type n -> m n (EmptyAbs Binder n)
singletonBinder ty = buildAbs ty \_ -> return UnitE

singletonBinderNest :: Builder m => Type n -> m n (EmptyAbs (Nest Binder) n)
singletonBinderNest ty = do
  EmptyAbs b <- singletonBinder ty
  return $ EmptyAbs (Nest b Empty)

buildNaryAbs
  :: (Builder m, HasNamesE e)
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
