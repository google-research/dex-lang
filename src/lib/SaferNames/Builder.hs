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

module SaferNames.Builder (
  emit, emitOp, buildLamGeneral,
  buildPureLam, BuilderT, Builder (..), Builder2, EffectsReader2,
  runBuilderT, buildBlock,
  EffectsReader (..), EffectsReaderT (..),
  runEffectsReaderT, liftEffectsReaderT,
  liftBuilder, app, add, mul, sub, neg, div',
  iadd, imul, isub, idiv, ilt, ieq, irem,
  fpow, flog, fLitLike, recGetHead, buildPureNaryLam,
  makeSuperclassGetter, makeMethodGetter,
  select, getUnpacked,
  fromPair, getFst, getSnd, getProj, getProjRef, naryApp,
  getClassDef, liftBuilderNameGenT,
  ) where

import Prelude hiding ((.), id)
import Control.Category
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Reader
import Data.Foldable (toList)
import Data.List (elemIndex)
import Data.Maybe (fromJust)

import SaferNames.NameCore
import SaferNames.Name
import SaferNames.Syntax
import SaferNames.Type
import SaferNames.PPrint ()

import LabeledItems

class BindingsReader m => Builder (m::MonadKind1) where
  emitDecl :: NameHint -> LetAnn -> Expr n -> m n (AtomName n)

-- Everything but the decls
type LocalBuilder m = (BindingsReader m, EffectsReader m, Scopable m)

type Builder2       (m :: MonadKind2) = forall i. Builder (m i)
type EffectsReader2 (m :: MonadKind2) = forall i. EffectsReader (m i)

emit :: Builder m => Expr n -> m n (AtomName n)
emit expr = emitDecl NoHint PlainLet expr

emitOp :: Builder m => Op n -> m n (Atom n)
emitOp op = Var <$> emit (Op op)

-- === BuilderNameGenT ===

newtype BuilderNameGenT (decl::B) (m::MonadKind1) (e::E) (n::S) =
  BuilderNameGenT { runBuilderNameGenT :: m n (DistinctAbs (Nest decl) e n) }

instance (BindingsReader m, BindingsExtender m, Monad1 m, BindsBindings decl)
         => NameGen (BuilderNameGenT decl m) where
  returnG e = BuilderNameGenT $ do
    Distinct <- getDistinct
    return (DistinctAbs Empty e)
  bindG (BuilderNameGenT m) f = BuilderNameGenT do
    DistinctAbs decls  e  <- m
    DistinctAbs decls' e' <- extendBindings (boundBindings decls) $ runBuilderNameGenT $ f e
    return $ DistinctAbs (decls >>> decls') e'
  getDistinctEvidenceG = BuilderNameGenT do
    Distinct <- getDistinct
    return $ DistinctAbs Empty getDistinctEvidence

liftBuilderNameGenT :: ScopeReader m => m n (e n) -> BuilderNameGenT decl m e n
liftBuilderNameGenT m = BuilderNameGenT do
  Distinct <- getDistinct
  result <- m
  return $ DistinctAbs Empty result

-- === BuilderT ===

newtype BuilderT (m::MonadKind1) (n::S) (l::S) (a:: *) =
  BuilderT { runBuilderT' :: Inplace (BuilderNameGenT Decl m) n l a }
  deriving (Functor, Applicative, Monad)

runBuilderT :: (BindingsReader m, BindingsExtender m, InjectableE e)
            => (forall l. (Distinct l, Ext n l) => BuilderT m n l (e l))
            -> m n (DistinctAbs (Nest Decl) e n)
runBuilderT cont = runBuilderNameGenT $ runInplace $ runBuilderT' cont

-- TODO: should be able to get away with `Scopable m` instead of `BindingsExtender m`
instance (BindingsReader m, BindingsGetter m, BindingsExtender m)
         => Builder (BuilderT m n) where
  emitDecl hint ann expr = BuilderT $
    liftInplace expr \expr' -> BuilderNameGenT do
      ty <- getType expr'
      let binderInfo = LetBound ann expr'
      withFreshBinder hint ty binderInfo \b -> do
        return $ DistinctAbs (Nest (Let ann b expr') Empty) (binderName b)

instance (BindingsReader m, BindingsGetter m, BindingsExtender m)
         => ScopeReader (BuilderT m n) where
  getDistinctEvidenceM = BuilderT $
    liftInplace UnitE \UnitE ->
      liftBuilderNameGenT getDistinctEvidenceM
  addScope e = BuilderT $
    liftInplace e \e' ->
      liftBuilderNameGenT $ addScope e'

instance (BindingsReader m, BindingsGetter m, BindingsExtender m)
         => BindingsReader (BuilderT m n) where
  addBindings e = BuilderT $
    liftInplace e \e' ->
      liftBuilderNameGenT $ addBindings e'

apBuilder :: ( Monad1 m, BindingsReader m, BindingsExtender m
             , InjectableE e, InjectableE e')
          => (forall l'. e l' -> m l' (e' l'))
          -> e l
          -> BuilderT m n l (e' l)
apBuilder cont x = liftBuilder x cont

liftBuilder :: ( Monad1 m, BindingsReader m, BindingsExtender m
               , InjectableE e, InjectableE e')
            => e l
            -> (forall l'. e l' -> m l' (e' l'))
            -> BuilderT m n l (e' l)
liftBuilder x cont = BuilderT $
  liftInplace x \x' ->
    BuilderNameGenT do
      Distinct <- getDistinct
      DistinctAbs Empty <$> cont x'

liftLocalBuilder
  :: (EffectsReader m, BindingsReader m, InjectableE e, InjectableE e')
  => e n
  -> (forall l. e l -> EffectsReaderT (BindingsReaderT Identity) l (e' l))
  -> m n (e' n)
liftLocalBuilder x cont = do
  effs <- getAllowedEffects
  WithBindings bindings scope (PairE x' effs') <- addBindings (PairE x effs)
  injectM $ runIdentity $ runBindingsReaderT (scope, bindings) $
    runEffectsReaderT effs' (cont x')

-- === effects monad ===

class Monad1 m => EffectsReader m where
  getAllowedEffects :: m n (EffectRow n)
  withAllowedEffects :: EffectRow n -> m n a -> m n a

newtype EffectsReaderT (m::MonadKind1) (n::S) (a:: *) =
  EffectsReaderT { runEffectsReaderT' :: ReaderT (EffectRow n) (m n) a }
  deriving (Functor, Applicative, Monad)

instance ScopeGetter m => (ScopeGetter (EffectsReaderT m)) where
  getScope = EffectsReaderT $ lift $ getScope

instance ScopeReader m => (ScopeReader (EffectsReaderT m)) where
  addScope e = EffectsReaderT $ lift $ addScope e
  getDistinctEvidenceM = EffectsReaderT $ lift getDistinctEvidenceM

instance BindingsReader m => (BindingsReader (EffectsReaderT m)) where
  addBindings e = EffectsReaderT $ lift $ addBindings e

instance Scopable m => (Scopable (EffectsReaderT m)) where
  withBindings ab cont = EffectsReaderT $ ReaderT \effs ->
    withBindings ab \e -> do
      effs' <- injectM effs
      runReaderT (runEffectsReaderT' $ cont e) effs'

instance BindingsGetter m => (BindingsGetter (EffectsReaderT m)) where
  getBindings = EffectsReaderT $ lift $ getBindings

instance BindingsExtender m => (BindingsExtender (EffectsReaderT m)) where
  extendBindings frag cont =
    EffectsReaderT $ ReaderT \effs ->
      extendBindings frag do
        effs' <- injectM effs
        runReaderT (runEffectsReaderT' cont) effs'

instance Monad1 m => EffectsReader (EffectsReaderT m) where
  getAllowedEffects = EffectsReaderT ask
  withAllowedEffects effs (EffectsReaderT cont) =
    EffectsReaderT $ local (const effs) cont

runEffectsReaderT :: EffectRow n -> EffectsReaderT m n a -> m n a
runEffectsReaderT effs cont = runReaderT (runEffectsReaderT' cont) effs

liftEffectsReaderT :: m n a -> EffectsReaderT m n a
liftEffectsReaderT cont = EffectsReaderT $ ReaderT $ const cont

-- === lambda-like things ===


buildBlock :: (BindingsReader m, BindingsExtender m, MonadFail1 m)
            => (forall l. (Distinct l, Ext n l) => BuilderT m n l (Atom l))
            -> m n (Block n)
buildBlock cont = do
  DistinctAbs decls (PairE result ty) <- runBuilderT do
    result <- cont
    ty <- getType `apBuilder` result
    return $ PairE result ty
  ty' <- fromConstAbs $ Abs decls ty
  return $ Block ty' decls $ Atom result

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
      b @> inject (AtomNameBinding ty info)

withFreshAtomBinder :: (Scopable m, SubstE Name e, InjectableE e)
                    => NameHint -> Type n -> AtomBinderInfo n
                    -> (forall l. Ext n l => AtomName l -> m l (e l))
                    -> m n (Abs Binder e n)
withFreshAtomBinder hint ty info cont = do
  Abs b name <- freshBinderNamePair hint
  Abs (BinderWithInfo b' _) body <-
    withBindings (Abs (BinderWithInfo (b:>ty) info) name) cont
  return $ Abs b' body

buildLamGeneral
  :: LocalBuilder m
  => Arrow
  -> Type n
  -> (forall l. Ext n l => AtomName l -> m l (EffectRow l))
  -> (forall l. Ext n l => AtomName l -> m l (Block l, a))
  -> m n (Atom n, a)
buildLamGeneral arr ty fEff fBody = do
  ab <- withFreshAtomBinder NoHint ty (LamBound arr) \v -> do
    effs <- fEff v
    withAllowedEffects effs do
      (body, aux) <- fBody v
      return $ effs `PairE` body `PairE` LiftE aux
  Abs b (effs `PairE` body `PairE` LiftE aux) <- return ab
  return (Lam $ LamExpr arr b effs body, aux)

buildPureLam :: LocalBuilder m
             => Arrow
             -> Type n
             -> (forall l. Ext n l => AtomName l -> m l (Block l))
             -> m n (Atom n)
buildPureLam arr ty body =
  fst <$> buildLamGeneral arr ty (const $ return Pure) \x ->
    withAllowedEffects Pure do
      result <- body x
      return (result, ())

buildPureNaryLam :: LocalBuilder m
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
    atomAsBlock =<< buildPureNaryLam arr rest' \xs -> do
      ExtW <- injectExt ext2
      x' <- injectM x
      cont (x':xs)
buildPureNaryLam _ _ _ = error "impossible"

-- === builder versions of common ops ===

getClassDef :: BindingsReader m => Name ClassNameC n -> m n (ClassDef n)
getClassDef classDefName = do
  ~(ClassBinding classDef) <- lookupBindings classDefName
  return classDef

makeMethodGetter :: BindingsReader m => Name ClassNameC n -> Int -> m n (Atom n)
makeMethodGetter classDefName methodIdx = runEffectsReaderT Pure do
  liftLocalBuilder classDefName \classDefName' -> do
    ClassDef _ _ (defName, def@(DataDef _ paramBs _)) <- getClassDef classDefName'
    buildPureNaryLam ImplicitArrow (EmptyAbs paramBs) \params -> do
      defName' <- injectM defName
      def'     <- injectM def
      buildPureLam ClassArrow (TypeCon (defName', def') (map Var params)) \dict ->
        atomAsBlock $ getProjection [methodIdx] $ getProjection [1, 0] $ Var dict

makeSuperclassGetter :: BindingsReader m => Name ClassNameC n -> Int -> m n (Atom n)
makeSuperclassGetter classDefName methodIdx = runEffectsReaderT Pure do
  liftLocalBuilder classDefName \classDefName' -> do
    ClassDef _ _ (defName, def@(DataDef _ paramBs _)) <- getClassDef classDefName'
    buildPureNaryLam ImplicitArrow (EmptyAbs paramBs) \params -> do
      defName' <- injectM defName
      def'     <- injectM def
      buildPureLam PlainArrow (TypeCon (defName', def') (map Var params)) \dict ->
        atomAsBlock $ getProjection [methodIdx] $ getProjection [0, 0] $ Var dict

recGetHead :: BindingsReader m => Label -> Atom n -> m n (Atom n)
recGetHead l x = do
  ~(RecordTy (Ext r _)) <- getType x
  let i = fromJust $ elemIndex l $ map fst $ toList $ reflectLabels r
  return $ getProjection [i] x

fLitLike :: Builder m => Double -> Atom n -> m n (Atom n)
fLitLike x t = do
  ty <- getType t
  case ty of
    BaseTy (Scalar Float64Type) -> return $ Con $ Lit $ Float64Lit x
    BaseTy (Scalar Float32Type) -> return $ Con $ Lit $ Float32Lit $ realToFrac x
    _ -> error "Expected a floating point scalar"

neg :: Builder m => Atom n -> m n (Atom n)
neg x = emitOp $ ScalarUnOp FNeg x

add :: Builder m => Atom n -> Atom n -> m n (Atom n)
add x y = emitOp $ ScalarBinOp FAdd x y

-- TODO: Implement constant folding for fixed-width integer types as well!
iadd :: Builder m => Atom n -> Atom n -> m n (Atom n)
iadd (Con (Lit l)) y | getIntLit l == 0 = return y
iadd x (Con (Lit l)) | getIntLit l == 0 = return x
iadd x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntBinOp (+) x y
iadd x y = emitOp $ ScalarBinOp IAdd x y

mul :: Builder m => Atom n -> Atom n -> m n (Atom n)
mul x y = emitOp $ ScalarBinOp FMul x y

imul :: Builder m => Atom n -> Atom n -> m n (Atom n)
imul   (Con (Lit l)) y               | getIntLit l == 1 = return y
imul x                 (Con (Lit l)) | getIntLit l == 1 = return x
imul x@(Con (Lit _)) y@(Con (Lit _))                    = return $ applyIntBinOp (*) x y
imul x y = emitOp $ ScalarBinOp IMul x y

sub :: Builder m => Atom n -> Atom n -> m n (Atom n)
sub x y = emitOp $ ScalarBinOp FSub x y

isub :: Builder m => Atom n -> Atom n -> m n (Atom n)
isub x (Con (Lit l)) | getIntLit l == 0 = return x
isub x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntBinOp (-) x y
isub x y = emitOp $ ScalarBinOp ISub x y

select :: Builder m => Atom n -> Atom n -> Atom n -> m n (Atom n)
select (Con (Lit (Word8Lit p))) x y = return $ if p /= 0 then x else y
select p x y = emitOp $ Select p x y

div' :: Builder m => Atom n -> Atom n -> m n (Atom n)
div' x y = emitOp $ ScalarBinOp FDiv x y

idiv :: Builder m => Atom n -> Atom n -> m n (Atom n)
idiv x (Con (Lit l)) | getIntLit l == 1 = return x
idiv x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntBinOp div x y
idiv x y = emitOp $ ScalarBinOp IDiv x y

irem :: Builder m => Atom n -> Atom n -> m n (Atom n)
irem x y = emitOp $ ScalarBinOp IRem x y

fpow :: Builder m => Atom n -> Atom n -> m n (Atom n)
fpow x y = emitOp $ ScalarBinOp FPow x y

flog :: Builder m => Atom n -> m n (Atom n)
flog x = emitOp $ ScalarUnOp Log x

ilt :: Builder m => Atom n -> Atom n -> m n (Atom n)
ilt x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntCmpOp (<) x y
ilt x y = emitOp $ ScalarBinOp (ICmp Less) x y

ieq :: Builder m => Atom n -> Atom n -> m n (Atom n)
ieq x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntCmpOp (==) x y
ieq x y = emitOp $ ScalarBinOp (ICmp Equal) x y

fromPair :: Builder m => Atom n -> m n (Atom n, Atom n)
fromPair pair = do
  ~[x, y] <- getUnpacked pair
  return (x, y)

getProj :: Builder m => Int -> Atom n -> m n (Atom n)
getProj i x = do
  xs <- getUnpacked x
  return $ xs !! i

getFst :: Builder m => Atom n -> m n (Atom n)
getFst p = fst <$> fromPair p

getSnd :: Builder m => Atom n -> m n (Atom n)
getSnd p = snd <$> fromPair p

getProjRef :: Builder m => Int -> Atom n -> m n (Atom n)
getProjRef i r = emitOp $ ProjRef i r

-- XXX: getUnpacked must reduce its argument to enforce the invariant that
-- ProjectElt atoms are always fully reduced (to avoid type errors between two
-- equivalent types spelled differently).
getUnpacked :: Builder m => Atom n -> m n [Atom n]
getUnpacked = undefined
-- getUnpacked (ProdVal xs) = return xs
-- getUnpacked atom = do
--   scope <- getScope
--   let len = projectLength $ getType atom
--       atom' = typeReduceAtom scope atom
--       res = map (\i -> getProjection [i] atom') [0..(len-1)]
--   return res

app :: Builder m => Atom n -> Atom n -> m n (Atom n)
app x i = Var <$> emit (App x i)

naryApp :: Builder m => Atom n -> [Atom n] -> m n (Atom n)
naryApp f xs = foldM app f xs
