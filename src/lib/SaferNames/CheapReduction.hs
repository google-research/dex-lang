-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module SaferNames.CheapReduction (
  CheaplyReducibleE (..), cheapReduce, cheapReduceWithDecls, cheapReduceToAtom) where

import Data.Functor.Identity
import Control.Applicative
import Control.Monad.Trans
import Control.Monad.Writer.Strict

import SaferNames.MTL1
import SaferNames.Name
import SaferNames.Syntax
import SaferNames.PPrint ()
import {-# SOURCE #-} SaferNames.Inference (trySynthDictBlock)
import Err

-- === api ===

cheapReduce :: (BindingsReader m, SubstE AtomSubstVal e, InjectableE e)
            => e n -> m n (e n)
cheapReduce e = liftImmut do
  DB bindings <- getDB
  e' <- injectM e
  return $ runBindingsReaderM bindings $
    runEnvReaderT idEnv $ cheapReduceFromSubst e'

cheapReduceWithDecls
  :: ( BindingsReader m
     , HoistableE e, InjectableE e, SubstE AtomSubstVal e, SubstE Name e)
  => Nest Decl n l -> e l -> m n (Maybe (e n), Maybe [Type n])
cheapReduceWithDecls decls result = publicResultFromE <$> liftImmut do
  Abs decls' result' <- injectM $ Abs decls result
  DB bindings <- getDB
  return $ resultToE $ runCheapReducerM idEnv bindings $
    cheapReduceWithDeclsB decls' $
      cheapReduceFromSubst result'

cheapReduceToAtom :: (BindingsReader m, CheaplyReducibleE e, InjectableE e)
                  => e n -> m n (Maybe (Atom n), Maybe [Type n])
cheapReduceToAtom e = publicResultFromE <$> liftImmut do
  DB bindings <- getDB
  e' <- injectM e
  return $ resultToE $ runCheapReducerM idEnv bindings $ cheapReduceE e'

-- === internal ===

resultToE :: (Maybe (e n), FailedDictTypes n) -> (PairE (MaybeE e) (MaybeE (ListE Type))) n
resultToE (l, FailedDictTypes r) = PairE (toMaybeE l) r

publicResultFromE :: (PairE (MaybeE e) (MaybeE (ListE Type))) n -> (Maybe (e n), Maybe [Type n])
publicResultFromE (PairE l r) = (fromMaybeE l, fromListE <$> fromMaybeE r)

newtype CheapReducerM (i :: S) (o :: S) (a :: *) =
  CheapReducerM
    (EnvReaderT AtomSubstVal
      (MaybeT1
        (WriterT1 FailedDictTypes
          (BindingsReaderT Identity))) i o a)
  deriving ( Functor, Applicative, Monad, Alternative
           , BindingsReader, ScopeReader, BindingsExtender
           , EnvReader AtomSubstVal, AlwaysImmut )

newtype FailedDictTypes (n::S) = FailedDictTypes ((MaybeE (ListE Type)) n)
                                 deriving (InjectableE, HoistableE)

instance Semigroup (FailedDictTypes n) where
  FailedDictTypes (JustE l) <> FailedDictTypes (JustE r) =
    FailedDictTypes $ JustE $ l <> r
  _ <> _ = FailedDictTypes $ NothingE
instance Monoid (FailedDictTypes n) where
  mempty = FailedDictTypes $ JustE mempty
instance FallibleMonoid1 FailedDictTypes where
  mfail = FailedDictTypes $ NothingE

class ( Alternative2 m, EnvReader AtomSubstVal m, AlwaysImmut2 m
      , BindingsReader2 m, BindingsExtender2 m) => CheapReducer m where
  reportSynthesisFail :: Type o -> m i o ()

instance CheapReducer CheapReducerM where
  reportSynthesisFail ty = CheapReducerM $ EnvReaderT $ lift $ lift11 $
    WriterT1 $ tell $ FailedDictTypes $ JustE $ ListE [ty]

runCheapReducerM :: Distinct o
                 => Env AtomSubstVal i o -> Bindings o -> CheapReducerM i o a
                 -> (Maybe a, FailedDictTypes o)
runCheapReducerM env bindings (CheapReducerM m) =
  runIdentity $ runBindingsReaderT bindings $
    runWriterT1 $ runMaybeT1 $ runEnvReaderT env m

cheapReduceFromSubst
  :: ( EnvReader AtomSubstVal m, BindingsReader2 m
     , AlwaysImmut2 m, InjectableE e, SubstE AtomSubstVal e)
  => e i -> m i o (e o)
cheapReduceFromSubst e = do
  e' <- substM e
  Immut <- getImmut
  DB bindings <- getDB
  return $ fmapNames (toScope bindings) (cheapReduceName bindings) e'

cheapReduceName :: Distinct n
                => Bindings n -> Name c n -> AtomSubstVal c n
cheapReduceName bindings v =
  runBindingsReaderM bindings $ withNameColorRep (getNameColor v) do
    lookupBindings v >>= \case
      AtomNameBinding (LetBound (DeclBinding _ _ (Atom x))) ->
        SubstVal <$> cheapReduce x
      _ -> return $ Rename v

cheapReduceWithDeclsB
  :: ( CheapReducer m
     , HoistableE e, InjectableE e, SubstE AtomSubstVal e, SubstE Name e)
  => Nest Decl i i'
  -> (forall o'. Ext o o' => m i' o' (e o'))
  -> m i o (e o)
cheapReduceWithDeclsB decls cont = do
  Abs irreducibleDecls result <- cheapReduceWithDeclsRec decls cont
  case hoist irreducibleDecls result of
    HoistSuccess result' -> return result'
    HoistFailure _       -> empty

cheapReduceWithDeclsRec
  :: ( CheapReducer m
     , HoistableE e, InjectableE e, SubstE AtomSubstVal e, SubstE Name e)
  => Nest Decl i i'
  -> (forall o'. Ext o o' => m i' o' (e o'))
  -> m i o (Abs (Nest Decl) e o)
cheapReduceWithDeclsRec decls cont = case decls of
  Empty -> Abs Empty <$> cont
  Nest (Let b binding@(DeclBinding _ _ expr)) rest -> do
    optional (cheapReduceE expr) >>= \case
      Nothing -> do
        binding' <- substM binding
        Immut <- getImmut
        withFreshBinder (getNameHint b) binding' \b' ->
          extendEnv (b@>Rename (binderName b')) do
            Abs decls' result <- cheapReduceWithDeclsRec rest cont
            return $ Abs (Nest (Let b' binding') decls') result
      Just x ->
        extendEnv (b@>SubstVal x) $
          cheapReduceWithDeclsRec rest cont

class CheaplyReducibleE (e::E) where
  cheapReduceE :: CheapReducer m => e i -> m i o (Atom o)

instance CheaplyReducibleE e => CheaplyReducibleE (Abs (Nest Decl) e) where
  cheapReduceE (Abs decls result) = cheapReduceWithDeclsB decls $ cheapReduceE result

instance CheaplyReducibleE Block where
  cheapReduceE (Block _ decls result) = cheapReduceE $ Abs decls result

instance CheaplyReducibleE Expr where
  cheapReduceE expr = cheapReduceFromSubst expr >>= \case
    Atom atom -> return atom
    App f x -> do
      case f of
        Lam (LamExpr (LamBinder b _ arr Pure) body)
          | arr == PlainArrow || arr == ImplicitArrow || arr == ClassArrow -> do
              dropSubst $ extendEnv (b@>SubstVal x) $ cheapReduceE body
        TypeCon con xs -> return $ TypeCon con $ xs ++ [x]
        _ -> empty
    Op (SynthesizeDict _ ty) -> do
      runFallibleT1 (trySynthDictBlock ty) >>= \case
        Success (Block _ Empty (Atom d)) -> return d
        _ -> reportSynthesisFail ty >> empty
    -- TODO: Make sure that this wraps correctly
    -- TODO: Other casts?
    Op (CastOp (BaseTy (Scalar Int32Type)) (Con (Lit (Int64Lit v)))) ->
      return $ Con $ Lit $ Int32Lit $ fromIntegral v
    _ -> empty
