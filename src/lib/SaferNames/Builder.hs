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
  buildScoped, buildScopedReduceDecls,
  runBuilderT, buildBlock, buildBlockReduced, app, add, mul, sub, neg, div',
  iadd, imul, isub, idiv, ilt, ieq, irem,
  fpow, flog, fLitLike, recGetHead, buildPureNaryLam,
  emitMethodType, emitSuperclass,
  makeSuperclassGetter, makeMethodGetter,
  select, getUnpacked, emitUnpacked,
  fromPair, getFst, getSnd, getProj, getProjRef, naryApp,
  getDataDef, getClassDef, getDataCon, atomAsBlock,
  Emits, buildPi, buildNonDepPi, buildLam, buildDepEffLam,
  buildAbs, buildNaryAbs, buildAlt, buildUnaryAlt, buildNewtype, fromNewtype,
  emitDataDef, emitClassDef, emitDataConName, emitTyConName,
  buildCase, buildSplitCase,
  emitBlock, BuilderEmissions, emitAtomToName,
  withFabricatedEmitsEvidence, BuilderEmission (..),
  TopBuilder (..), TopBuilderT (..), runTopBuilderT, TopBuilder2,
  ) where

import Control.Monad
import Control.Monad.Trans
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

-- === Ordinary (local) builder class ===

class (BindingsReader m, Scopable m, MonadFail1 m)
      => Builder (m::MonadKind1) where
  -- This is unsafe because it doesn't require the Emits predicate. `emitDecl`
  -- and `emitBinding` wrap it safely.
  emitDecl
    :: (Builder m, Emits n)
    => NameHint -> LetAnn -> Expr n -> m n (AtomName n)
  buildScopedGeneral
    :: ( SubstE Name e , InjectableE e
       , HasNamesE   e', InjectableE e', SubstE AtomSubstVal e'
       , SubstB Name b, BindsBindings b)
    => Abs b e n
    -> (forall l. (Ext n l, Distinct l, Emits l) => e l -> m l (e' l))
    -> m n (Abs b (Abs (Nest Decl) e') n)

type Builder2 (m :: MonadKind2) = forall i. Builder (m i)

emit :: (Builder m, Emits n) => Expr n -> m n (AtomName n)
emit expr = emitDecl NoHint PlainLet expr

emitOp :: (Builder m, Emits n) => Op n -> m n (Atom n)
emitOp op = Var <$> emit (Op op)

emitBlock :: (Builder m, Emits n) => Block n -> m n (Atom n)
emitBlock (Block _ Empty (Atom result)) = return result
emitBlock (Block _ decls result) = runEnvReaderT idEnv $ emitBlock' decls result

emitBlock' :: (Builder m, Emits o)
           => Nest Decl i i' -> Expr i' -> EnvReaderT Name m i o (Atom o)
emitBlock' Empty expr = do
  v <- substM expr >>= emit
  return $ Var v
emitBlock' (Nest (Let b (DeclBinding ann _ expr)) rest) result = do
  expr' <- substM expr
  v <- emitDecl (getNameHint b) ann expr'
  extendEnv (b @> v) $ emitBlock' rest result

emitAtomToName :: (Builder m, Emits n) => Atom n -> m n (AtomName n)
emitAtomToName (Var v) = return v
emitAtomToName x = emit (Atom x)

buildScoped
  :: (HasNamesE e, InjectableE e, SubstE AtomSubstVal e, Builder m)
  => (forall l. (Emits l, Ext n l) => m l (e l))
  -> m n (Abs (Nest Decl) e n)
buildScoped cont = do
  Abs UnitB declsAndResult <- buildScopedGeneral (Abs UnitB UnitE) \UnitE ->
    withFabricatedEmitsEvidence cont
  return declsAndResult

buildScopedReduceDecls
  :: ( Builder m
     , CheaplyReducible e, HoistableE e, InjectableE e, SubstE Name e
     , SubstE AtomSubstVal e)
  => (forall l. (Emits l, Ext n l) => m l (e l))
  -> m n (e n)
buildScopedReduceDecls cont = buildScoped cont >>= cheapReduceDecls


-- === Top-level builder class ===

class (BindingsReader m, MonadFail1 m)
      => TopBuilder (m::MonadKind1) where
  emitBinding :: NameColor c => NameHint -> Binding c n -> m n (Name c n)
  liftLocalBuilder :: BuilderT FallibleM n a -> m n a


newtype TopBuilderT (m::MonadKind) (n::S) (a:: *) =
  TopBuilderT { runTopBuilderT' :: InplaceT Bindings BindingsFrag m n a }
  deriving ( Functor, Applicative, Monad, MonadFail, Fallible
           , CtxReader, ScopeReader)

instance Fallible m => BindingsReader (TopBuilderT m) where
  addBindings e = TopBuilderT $
    withInplaceOutEnv e \bindings e' -> WithBindings bindings e'

instance Fallible m => TopBuilder (TopBuilderT m) where
  emitBinding hint binding = TopBuilderT $
    emitInplace hint binding \b binding' -> boundBindings (b:>binding')
  liftLocalBuilder m = TopBuilderT $
    liftBetweenInplaceTs
      liftFallibleM
      id
      (\Empty -> emptyOutFrag)
      (runBuilderT' m)

instance TopBuilder m => TopBuilder (EnvReaderT v m i) where
  emitBinding hint binding = EnvReaderT $ lift $ emitBinding hint binding
  liftLocalBuilder m = EnvReaderT $ lift $ liftLocalBuilder m

runTopBuilderT
  :: (Fallible m, Distinct n)
  => Bindings n
  -> (forall l. (Distinct l, Ext n l) => TopBuilderT m l (e l))
  -> m (DistinctAbs BindingsFrag e n)
runTopBuilderT bindings cont =
  runInplaceT bindings $ runTopBuilderT' $ cont

type TopBuilder2 (m :: MonadKind2) = forall i. TopBuilder (m i)

-- === BuilderT ===

-- Only one element of the pair should be populated. We could have used
-- `EitherB` instead but its monoid instance is more awkward.
type BuilderEmissions = Nest Decl

data BuilderEmission c n where
  BuilderEmitDecl    :: DeclBinding n -> BuilderEmission AtomNameC n
  BuilderEmitTopDecl :: Binding c n   -> BuilderEmission c         n

instance ExtOutMap Bindings BuilderEmissions where
  extendOutMap bindings emissions =
    bindings `extendOutMap` boundBindings emissions

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
  BuilderT { runBuilderT' :: InplaceT Bindings BuilderEmissions m n a }
  deriving ( Functor, Applicative, Monad, MonadFail, Fallible
           , CtxReader, ScopeReader)

runBuilderT
  :: (MonadFail m, Distinct n)
  => Bindings n
  -> (forall l. (Distinct l, Ext n l) => BuilderT m l (e l))
  -> m (e n)
runBuilderT bindings cont = do
  DistinctAbs decls result <- runInplaceT bindings $ runBuilderT' cont
  case decls of
    Empty -> return result
    _ -> error "shouldn't have produced any decls"

instance MonadFail m => Builder (BuilderT m) where
  buildScopedGeneral ab cont = BuilderT do
    scopedResult <- scopedInplaceGeneral
      (\bindings b -> bindings `extendOutMap` boundBindings b)
      ab
      (\e -> runBuilderT' $ withFabricatedEmitsEvidence $ cont e)
    ScopedResult _ (PairB b emissions) result <- return scopedResult
    injectM $ Abs b $ Abs emissions result
  emitDecl = undefined

instance MonadFail m => BindingsReader (BuilderT m) where
  addBindings e = BuilderT $
    withInplaceOutEnv e \bindings e' -> WithBindings bindings e'

instance MonadFail m => Scopable (BuilderT m) where
  withBindings ab cont = do
    Abs b (Abs Empty result) <- buildScopedGeneral ab \x -> cont x
    return $ Abs b result
  extendNamelessBindings frag cont = BuilderT do
    Distinct <- getDistinct
    liftBetweenInplaceTs id (\bindings -> extendOutMap bindings frag) id $ runBuilderT' cont

instance (InjectableV v, Builder m) => Builder (EnvReaderT v m i) where
  emitDecl hint ann expr = EnvReaderT $ lift $ emitDecl hint ann expr

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

-- === lambda-like things ===

buildBlockAux
  :: Builder m
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

buildBlockReduced
  :: Builder m
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
  => NameHint
  -> Arrow
  -> Type n
  -> (forall l. (         Ext n l) => AtomName l -> m l (EffectRow l))
  -> (forall l. (Emits l, Ext n l) => AtomName l -> m l (Atom l, a))
  -> m n (Atom n, a)
buildLamGeneral hint arr ty fEff fBody = do
  effAbs <- withFreshBinder hint ty fEff
  ab <- withFreshLamBinder hint (LamBinding arr ty) effAbs \v -> do
    (body, aux) <- buildBlockAux do
      v' <- injectM v
      fBody v'
    return $ body `PairE` LiftE aux
  Abs b (body `PairE` LiftE aux) <- return ab
  return (Lam $ LamExpr b body, aux)

buildPureLam :: Builder m
             => NameHint
             -> Arrow
             -> Type n
             -> (forall l. (Emits l, Ext n l) => AtomName l -> m l (Atom l))
             -> m n (Atom n)
buildPureLam hint arr ty body = do
  fst <$> buildLamGeneral hint arr ty (const $ return Pure) \x ->
    withAllowedEffects Pure do
      result <- body x
      return (result, ())

buildLam
  :: Builder m
  => NameHint
  -> Arrow
  -> Type n
  -> EffectRow n
  -> (forall l. (Emits l, Ext n l) => AtomName l -> m l (Atom l))
  -> m n (Atom n)
buildLam hint arr ty eff body = buildDepEffLam hint arr ty (const $ injectM eff) body

buildDepEffLam
  :: Builder m
  => NameHint
  -> Arrow
  -> Type n
  -> (forall l. (         Ext n l) => AtomName l -> m l (EffectRow l))
  -> (forall l. (Emits l, Ext n l) => AtomName l -> m l (Atom l))
  -> m n (Atom n)
buildDepEffLam hint arr ty effBuilder body =
  fst <$> buildLamGeneral hint arr ty effBuilder (\v -> (,()) <$> body v)

-- Body must be an Atom because otherwise the nullary case would require
-- emitting decls into the enclosing scope.
buildPureNaryLam :: Builder m
                 => Arrow
                 -> EmptyAbs (Nest Binder) n
                 -> (forall l. Ext n l => [AtomName l] -> m l (Atom l))
                 -> m n (Atom n)
buildPureNaryLam _ (EmptyAbs Empty) cont = cont []
buildPureNaryLam arr (EmptyAbs (Nest (b:>ty) rest)) cont = do
  buildPureLam (getNameHint b) arr ty \x -> do
    restAbs <- injectM $ Abs b $ EmptyAbs rest
    rest' <- applyAbs restAbs x
    buildPureNaryLam arr rest' \xs -> do
      x' <- injectM x
      cont (x':xs)
buildPureNaryLam _ _ _ = error "impossible"

buildPi :: (Fallible1 m, Builder m)
        => NameHint -> Arrow -> Type n
        -> (forall l. Ext n l => AtomName l -> m l (EffectRow l, Type l))
        -> m n (PiType n)
buildPi hint arr ty body = do
  ab <- withFreshBinder hint ty \v -> do
      (effs, resultTy) <- body v
      return $ PairE effs resultTy
  Abs b (PairE effs resultTy) <- return ab
  return $ PiType arr b effs resultTy

buildNonDepPi :: (Fallible1 m, Builder m)
              => NameHint -> Arrow -> Type n -> EffectRow n -> Type n
              -> m n (PiType n)
buildNonDepPi hint arr argTy effs resultTy = buildPi hint arr argTy \_ -> do
  resultTy' <- injectM resultTy
  effs'     <- injectM effs
  return (effs', resultTy')

buildAbs
  :: ( Builder m, InjectableE e, HasNamesE e, SubstE AtomSubstVal e, HoistableE e
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
  :: (Builder m, InjectableE e, HasNamesE e, SubstE AtomSubstVal e)
  => EmptyAbs (Nest Binder) n
  -> (forall l. Ext n l => [AtomName l] -> m l (e l))
  -> m n (Abs (Nest Binder) e n)
buildNaryAbs (EmptyAbs Empty) body = Abs Empty <$> body []
buildNaryAbs (EmptyAbs (Nest (b:>ty) bs)) body = do
  Abs b' (Abs bs' body') <-
    buildAbs ty \v -> do
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

emitDataDef :: TopBuilder m => DataDef n -> m n (DataDefName n)
emitDataDef dataDef@(DataDef sourceName _ _) =
  emitBinding hint $ DataDefBinding dataDef
  where hint = getNameHint sourceName

emitClassDef :: TopBuilder m => ClassDef n -> m n (Name ClassNameC n)
emitClassDef classDef@(ClassDef name _ _) =
  emitBinding (getNameHint name) $ ClassBinding classDef

emitDataConName :: TopBuilder m => DataDefName n -> Int -> m n (Name DataConNameC n)
emitDataConName dataDefName conIdx = do
  DataDef _ _ dataCons <- getDataDef dataDefName
  let (DataConDef name _) = dataCons !! conIdx
  emitBinding (getNameHint name) $ DataConBinding dataDefName conIdx

emitSuperclass :: TopBuilder m
               => ClassName n -> Int -> m n (Name SuperclassNameC n)
emitSuperclass dataDef idx = do
  getter <- makeSuperclassGetter dataDef idx
  emitBinding hint $ SuperclassBinding dataDef idx getter
  where hint = getNameHint $ "Proj" <> show idx <> pprint dataDef

makeSuperclassGetter :: TopBuilder m => Name ClassNameC n -> Int -> m n (Atom n)
makeSuperclassGetter classDefName methodIdx = do
  ClassDef _ _ (defName, def@(DataDef _ paramBs _)) <- getClassDef classDefName
  liftLocalBuilder do
    buildPureNaryLam ImplicitArrow (EmptyAbs paramBs) \params -> do
      defName' <- injectM defName
      def'     <- injectM def
      buildPureLam "subclassDict" PlainArrow (TypeCon (defName', def') (map Var params)) \dict ->
        return $ getProjection [methodIdx] $ getProjection [0, 0] $ Var dict

emitMethodType :: TopBuilder m
               => NameHint -> ClassName n -> Int -> m n (Name MethodNameC n)
emitMethodType hint classDef idx = do
  getter <- makeMethodGetter classDef idx
  emitBinding hint $ MethodBinding classDef idx getter

makeMethodGetter :: TopBuilder m => Name ClassNameC n -> Int -> m n (Atom n)
makeMethodGetter classDefName methodIdx = do
  ClassDef _ _ (defName, def@(DataDef _ paramBs _)) <- getClassDef classDefName
  liftLocalBuilder do
    buildPureNaryLam ImplicitArrow (EmptyAbs paramBs) \params -> do
      defName' <- injectM defName
      def'     <- injectM def
      buildPureLam "dict" ClassArrow (TypeCon (defName', def') (map Var params)) \dict ->
        return $ getProjection [methodIdx] $ getProjection [1, 0] $ Var dict

emitTyConName :: TopBuilder m => DataDefName n -> m n (Name TyConNameC n)
emitTyConName dataDefName =
  emitBinding (getNameHint dataDefName) $ TyConBinding dataDefName

getDataDef :: BindingsReader m => DataDefName n -> m n (DataDef n)
getDataDef v = do
  ~(DataDefBinding def) <- lookupBindings v
  return def

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
getUnpacked :: (Builder m, Emits n) => Atom n -> m n [Atom n]
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
