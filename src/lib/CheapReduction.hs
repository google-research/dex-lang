-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module CheapReduction (
  CheaplyReducibleE (..), cheapReduce, cheapReduceWithDecls, cheapNormalize) where

import qualified Data.Map.Strict as M
import Data.Maybe
import Data.Functor.Identity
import Control.Applicative
import Control.Monad.Trans
import Control.Monad.Writer.Strict
import Control.Monad.State.Strict

import MTL1
import Name
import Syntax
import PPrint ()
import {-# SOURCE #-} Inference (trySynthDictBlock)
import Err

-- === api ===

type NiceE e = (HoistableE e, SinkableE e, SubstE AtomSubstVal e, SubstE Name e)

cheapReduce :: forall e' e m n
             . (EnvReader m, CheaplyReducibleE e e', NiceE e, NiceE e')
            => e n -> m n (Maybe (e' n), Maybe (ESet Type n))
cheapReduce e = liftCheapReducerM idSubst $ cheapReduceE e

-- Second result contains the set of dictionary types that failed to synthesize
-- during traversal of the supplied decls.
cheapReduceWithDecls
  :: forall e' e m n l
   . ( CheaplyReducibleE e e', NiceE e', NiceE e, EnvReader m )
  => Nest Decl n l -> e l -> m n (Maybe (e' n), Maybe (ESet Type n))
cheapReduceWithDecls decls result = do
  Abs decls' result' <- sinkM $ Abs decls result
  liftCheapReducerM idSubst $
    cheapReduceWithDeclsB decls' $
      cheapReduceE result'

cheapNormalize :: (EnvReader m, CheaplyReducibleE e e, NiceE e) => e n -> m n (e n)
cheapNormalize a = fromJust . fst <$> cheapReduce a

-- === internal ===

newtype CheapReducerM (i :: S) (o :: S) (a :: *) =
  CheapReducerM
    (SubstReaderT AtomSubstVal
      (MaybeT1
        (WriterT1 FailedDictTypes
          (ScopedT1 (MapE AtomName (MaybeE Atom))
            (EnvReaderT Identity)))) i o a)
  deriving ( Functor, Applicative, Monad, Alternative
           , EnvReader, ScopeReader, EnvExtender
           , SubstReader AtomSubstVal)

newtype FailedDictTypes (n::S) = FailedDictTypes (MaybeE (ESet Type) n)
                                 deriving (SinkableE, HoistableE)

instance Semigroup (FailedDictTypes n) where
  FailedDictTypes (JustE l) <> FailedDictTypes (JustE r) =
    FailedDictTypes $ JustE $ l <> r
  _ <> _ = FailedDictTypes $ NothingE
instance Monoid (FailedDictTypes n) where
  mempty = FailedDictTypes $ JustE mempty
instance FallibleMonoid1 FailedDictTypes where
  mfail = FailedDictTypes $ NothingE

class ( Alternative2 m, SubstReader AtomSubstVal m
      , EnvReader2 m, EnvExtender2 m) => CheapReducer m where
  reportSynthesisFail :: Type o -> m i o ()
  updateCache :: AtomName o -> Maybe (Atom o) -> m i o ()
  lookupCache :: AtomName o -> m i o (Maybe (Maybe (Atom o)))

instance CheapReducer CheapReducerM where
  reportSynthesisFail ty = CheapReducerM $ SubstReaderT $ lift $ lift11 $
    WriterT1 $ tell $ FailedDictTypes $ JustE $ eSetSingleton ty
  updateCache v u = CheapReducerM $ SubstReaderT $ lift $ lift11 $ lift11 $
    modify (MapE . M.insert v (toMaybeE u) . fromMapE)
  lookupCache v = CheapReducerM $ SubstReaderT $ lift $ lift11 $ lift11 $
    fmap fromMaybeE <$> gets (M.lookup v . fromMapE)

liftCheapReducerM :: EnvReader m
                  => Subst AtomSubstVal i o -> CheapReducerM i o a
                  -> m o (Maybe a, Maybe (ESet Type o))
liftCheapReducerM subst (CheapReducerM m) = do
  (result, FailedDictTypes tys) <-
    liftM runIdentity $ liftEnvReaderT $ runScopedT1
      (runWriterT1 $ runMaybeT1 $ runSubstReaderT subst m) mempty
  return $ (result, fromMaybeE tys)

cheapReduceFromSubst
  :: forall e m i o .
     ( SubstReader AtomSubstVal m, EnvReader2 m
     , SinkableE e, SubstE AtomSubstVal e, HoistableE e)
  => e i -> m i o (e o)
cheapReduceFromSubst e = traverseNames cheapSubstName =<< substM e
  where
    cheapSubstName :: Color c => Name c o -> m i o (AtomSubstVal c o)
    cheapSubstName v = lookupEnv v >>= \case
      AtomNameBinding (LetBound (DeclBinding _ _ (Atom x))) ->
        liftM SubstVal $ dropSubst $ cheapReduceFromSubst x
      _ -> return $ Rename v

cheapReduceWithDeclsB
  :: ( CheapReducer m
     , HoistableE e, SinkableE e, SubstE AtomSubstVal e, SubstE Name e)
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
     , HoistableE e, SinkableE e, SubstE AtomSubstVal e, SubstE Name e)
  => Nest Decl i i'
  -> (forall o'. Ext o o' => m i' o' (e o'))
  -> m i o (Abs (Nest Decl) e o)
cheapReduceWithDeclsRec decls cont = case decls of
  Empty -> Abs Empty <$> cont
  Nest (Let b binding@(DeclBinding _ _ expr)) rest -> do
    optional (cheapReduceE expr) >>= \case
      Nothing -> do
        binding' <- substM binding
        withFreshBinder (getNameHint b) binding' \b' -> do
          updateCache (binderName b') Nothing
          extendSubst (b@>Rename (binderName b')) do
            Abs decls' result <- cheapReduceWithDeclsRec rest cont
            return $ Abs (Nest (Let b' binding') decls') result
      Just x ->
        extendSubst (b@>SubstVal x) $
          cheapReduceWithDeclsRec rest cont

cheapReduceName :: (Color c, CheapReducer m) => Name c o -> m i o (AtomSubstVal c o)
cheapReduceName v =
  lookupEnv v >>= \case
    AtomNameBinding (LetBound (DeclBinding _ _ e)) -> case e of
      -- We avoid synthesizing the dictionaries during the traversal
      -- and only do that when cheap reduction is performed on the expr directly.
      Op (SynthesizeDict _ _) -> stuck
      _ -> do
        cachedVal <- lookupCache v >>= \case
          Nothing -> do
            result <- optional (dropSubst $ cheapReduceE e)
            updateCache v result
            return result
          Just result -> return result
        case cachedVal of
          Nothing  -> stuck
          Just ans -> return $ SubstVal ans
    _ -> stuck
  where stuck = return $ Rename v

class CheaplyReducibleE (e::E) (e'::E) where
  cheapReduceE :: CheapReducer m => e i -> m i o (e' o)

instance CheaplyReducibleE Atom Atom where
  cheapReduceE :: forall m i o. CheapReducer m => Atom i -> m i o (Atom o)
  cheapReduceE a = case a of
    -- Don't try to eagerly reduce lambda bodies. We might get stuck long before
    -- we have a chance to apply tham. Also, recursive traversal of those bodies
    -- means that we will follow the full call chain, so it's really expensive!
    Lam _   -> substM a
    -- We traverse the Atom constructors that might contain lambda expressions
    -- explicitly, to make sure that we can skip normalizing free vars inside those.
    Con con -> Con <$> mapM cheapReduceE con
    DataCon sourceName dataDefName params con args ->
      DataCon sourceName <$> substM dataDefName <*> mapM cheapReduceE params <*> pure con <*> mapM cheapReduceE args
    Record items -> Record <$> mapM cheapReduceE items
    Variant ty l c p -> do
      ExtLabeledItemsE ty' <- substM $ ExtLabeledItemsE ty
      Variant ty' <$> pure l <*> pure c <*> cheapReduceE p
    -- Do recursive reduction via substitution
    _ -> do
      a' <- substM a
      dropSubst $ traverseNames cheapReduceName a'

instance (CheaplyReducibleE e e', NiceE e') => CheaplyReducibleE (Abs (Nest Decl) e) e' where
  cheapReduceE (Abs decls result) = cheapReduceWithDeclsB decls $ cheapReduceE result

instance (CheaplyReducibleE Expr e', NiceE e') => CheaplyReducibleE Block e' where
  cheapReduceE (Block _ decls result) = cheapReduceE $ Abs decls result

instance CheaplyReducibleE Expr Atom where
  cheapReduceE = \case
    Atom atom -> cheapReduceE atom
    App f' xs' -> do
      f <- cheapReduceE f'
      case fromNaryLam (length xs') f of
        Just (NaryLamExpr bs _ body) -> do
          xs <- mapM cheapReduceE xs'
          let subst = bs @@> fmap SubstVal xs
          dropSubst $ extendSubst subst $ cheapReduceE body
        _ -> empty
    Op (SynthesizeDict _ ty') -> do
      ty <- cheapReduceE ty'
      runFallibleT1 (trySynthDictBlock ty) >>= \case
        Success block -> dropSubst $ cheapReduceE block
        Failure _     -> reportSynthesisFail ty >> empty
    -- TODO: Make sure that this wraps correctly
    -- TODO: Other casts?
    Op (CastOp ty' val') -> do
      ty <- cheapReduceE ty'
      case ty of
        BaseTy (Scalar Int32Type) -> do
          val <- cheapReduceE val'
          case val of
            Con (Lit (Int64Lit v)) -> return $ Con $ Lit $ Int32Lit $ fromIntegral v
            _ -> empty
        _ -> empty
    _ -> empty

instance (CheaplyReducibleE e1 e1', CheaplyReducibleE e2 e2')
  => CheaplyReducibleE (PairE e1 e2) (PairE e1' e2') where
    cheapReduceE (PairE e1 e2) = PairE <$> cheapReduceE e1 <*> cheapReduceE e2

instance CheaplyReducibleE EffectRow EffectRow where
  cheapReduceE row = cheapReduceFromSubst row

instance CheaplyReducibleE FieldRowElems FieldRowElems where
  cheapReduceE elems = cheapReduceFromSubst elems
