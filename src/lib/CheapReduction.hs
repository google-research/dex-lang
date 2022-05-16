-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module CheapReduction
  ( CheaplyReducibleE (..), cheapReduce, cheapReduceWithDecls
  , cheapNormalize, DictTypeHoistStatus (..))
  where

import Data.Functor.Identity
import Data.Foldable (toList)
import Control.Applicative
import Control.Monad
import GHC.Exts (inline)

import MTL1
import Name
import Syntax
import PPrint ()
import {-# SOURCE #-} Inference (trySynthTerm)
import Err
import Types.Primitives

-- === api ===

type NiceE e = (HoistableE e, SinkableE e, SubstE AtomSubstVal e, SubstE Name e)

type Phantoms n = [Atom n] -- Atoms whose purpose is to possibly carry phantom dict holes

cheapReduce :: forall e' e m n
             . (EnvReader m, CheaplyReducibleE e e', NiceE e, NiceE e')
            => e n -> m n (Maybe (e' n))
cheapReduce e = liftCheapReducerM idSubst $ cheapReduceE e
{-# INLINE cheapReduce #-}
{-# SCC cheapReduce #-}

cheapReduceWithDecls
  :: ( CheaplyReducibleE e e', NiceE e', NiceE e, EnvReader m )
  => Nest Decl n l -> e l -> m n (Maybe (Phantoms n, e' n))
cheapReduceWithDecls decls result = do
  Abs decls' result' <- sinkM $ Abs decls result
  liftCheapReducerM idSubst $
    cheapReduceWithDeclsB decls' $
      cheapReduceE result'
{-# INLINE cheapReduceWithDecls #-}
{-# SCC cheapReduceWithDecls #-}

cheapNormalize :: (EnvReader m, CheaplyReducibleE e e, NiceE e) => e n -> m n (e n)
cheapNormalize a = cheapReduce a >>= \case
  Just ans -> return ans
  _ -> error "couldn't normalize expression"
{-# INLINE cheapNormalize #-}

-- === internal ===

newtype CheapReducerM (i :: S) (o :: S) (a :: *) =
  CheapReducerM
    (SubstReaderT AtomSubstVal
      (MaybeT1
         (EnvReaderT Identity)) i o a)
  deriving ( Functor, Applicative, Monad, Alternative
           , EnvReader, ScopeReader, EnvExtender
           , SubstReader AtomSubstVal)

data DictTypeHoistStatus = DictTypeHoistFailure | DictTypeHoistSuccess

instance Semigroup DictTypeHoistStatus where
  DictTypeHoistSuccess <> DictTypeHoistSuccess = DictTypeHoistSuccess
  _ <> _ = DictTypeHoistFailure

instance Monoid DictTypeHoistStatus where
  mempty = DictTypeHoistSuccess

class ( Alternative2 m, SubstReader AtomSubstVal m
      , EnvReader2 m, EnvExtender2 m) => CheapReducer m

instance CheapReducer CheapReducerM

liftCheapReducerM :: EnvReader m
                  => Subst AtomSubstVal i o -> CheapReducerM i o a
                  -> m o (Maybe a)
liftCheapReducerM subst (CheapReducerM m) = do
  liftM runIdentity $ liftEnvReaderT $ runMaybeT1 $ runSubstReaderT subst m
{-# INLINE liftCheapReducerM #-}

cheapReduceFromSubst
  :: forall e i o .
     ( SinkableE e, SubstE AtomSubstVal e, HoistableE e)
  => e i -> CheapReducerM i o (e o)
cheapReduceFromSubst e = traverseNames cheapSubstName =<< substM e
  where
    cheapSubstName :: Color c => Name c o -> CheapReducerM i o (AtomSubstVal c o)
    cheapSubstName v = lookupEnv v >>= \case
      AtomNameBinding (LetBound (DeclBinding _ _ (Atom x))) ->
        liftM SubstVal $ dropSubst $ cheapReduceFromSubst x
      _ -> return $ Rename v

cheapReduceWithDeclsB
  :: ( HoistableE e, SinkableE e, SubstE AtomSubstVal e, SubstE Name e)
  => Nest Decl i i'
  -> (forall o'. Ext o o' => CheapReducerM i' o' (e o'))
  -> CheapReducerM i o (Phantoms o, e o)
cheapReduceWithDeclsB Empty cont = ([],) <$> cont
cheapReduceWithDeclsB (Nest (Let b (DeclBinding _ _ expr)) rest) cont = do
  x <- cheapReduceE expr
  (phantoms, result) <- extendSubst (b@>SubstVal x) $ cheapReduceWithDeclsB rest cont
  return (x:phantoms, result)

class CheaplyReducibleE (e::E) (e'::E) where
  cheapReduceE :: e i -> CheapReducerM i o (e' o)

instance CheaplyReducibleE Atom Atom where
  cheapReduceE :: forall i o. Atom i -> CheapReducerM i o (Atom o)
  cheapReduceE a = confuseGHC >>=  \_ -> case a of
    Var v -> do
      subst <- getSubst
      case subst ! v of
        SubstVal x -> return x
        Rename v' -> do
          lookupAtomName v' >>= \case
            LetBound (DeclBinding _ _ (Atom x)) -> dropSubst $ cheapReduceE x
            _ -> return $ Var v'
    -- Don't try to eagerly reduce lambda bodies. We might get stuck long before
    -- we have a chance to apply tham. Also, recursive traversal of those bodies
    -- means that we will follow the full call chain, so it's really expensive!
    Lam _   -> substM a
    Pi  _   -> substM a
    TabPi _ -> substM a
    DepPairTy _ -> substM a
    Con (DictHole ctx ty') -> do
      ty <- cheapReduceE ty'
      runFallibleT1 (trySynthTerm ty) >>= \case
        Success d -> return d
        Failure _ -> return $ Con $ DictHole ctx ty
    Con con -> Con <$> (inline traversePrimCon) cheapReduceE con
    TC tc   -> TC  <$> (inline traversePrimTC)  cheapReduceE tc
    DataCon sourceName dataDefName params con args ->
      DataCon sourceName <$> substM dataDefName <*> mapM cheapReduceE params <*> pure con <*> mapM cheapReduceE args
    Record items -> Record <$> mapM cheapReduceE items
    Variant ty l c p -> do
      ExtLabeledItemsE ty' <- substM $ ExtLabeledItemsE ty
      Variant ty' l c <$> cheapReduceE p
    DictCon d -> cheapReduceE d
    DictTy  t -> DictTy  <$> substM t
    IxTy ixTy -> IxTy    <$> substM ixTy
    _ -> error $ "not implemented " ++ pprint a

instance CheaplyReducibleE DictExpr Atom where
  cheapReduceE d = case d of
    SuperclassProj child superclassIx -> do
      cheapReduceE child >>= \case
        DictCon (InstanceDict instanceName args) -> dropSubst do
          args' <- mapM (cheapReduceE @Atom @Atom) args
          InstanceDef _ bs _ body <- lookupInstanceDef instanceName
          let InstanceBody superclasses _ = body
          applySubst (bs@@>(SubstVal <$> args')) (superclasses !! superclassIx)
        child' -> return $ DictCon $ SuperclassProj child' superclassIx
    InstantiatedGiven f xs -> do
      cheapReduceE (App f xs) <|> justSubst
    InstanceDict _ _ -> justSubst
    where justSubst = DictCon <$> substM d

instance CheaplyReducibleE Block Atom where
  cheapReduceE (Block _ decls result) = do
    (phantoms, result') <- cheapReduceWithDeclsB decls $ cheapReduceE result
    return $ withPhantoms phantoms result'

instance CheaplyReducibleE Expr Atom where
  cheapReduceE expr = confuseGHC >>= \_ -> case expr of
    Atom atom -> cheapReduceE atom
    App f' xs' -> do
      f <- cheapReduceE f'
      case fromNaryLamExact (length xs') f of
        Just (NaryLamExpr bs _ body) -> do
          xs <- mapM cheapReduceE xs'
          let subst = bs @@> fmap SubstVal xs
          liftM (withPhantoms (toList xs)) $
            dropSubst $ extendSubst subst $ cheapReduceE body
        _ -> empty
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
    Op (ProjMethod dict i) -> do
      cheapReduceE dict >>= \case
        DictCon (InstanceDict instanceName args) -> dropSubst do
          args' <- mapM cheapReduceE args
          InstanceDef _ bs _ (InstanceBody _ methods) <- lookupInstanceDef instanceName
          let method = methods !! i
          extendSubst (bs@@>(SubstVal <$> args')) $
            cheapReduceE method
        _ -> empty
    _ -> empty

instance (CheaplyReducibleE e1 e1', CheaplyReducibleE e2 e2')
  => CheaplyReducibleE (PairE e1 e2) (PairE e1' e2') where
    cheapReduceE (PairE e1 e2) = PairE <$> cheapReduceE e1 <*> cheapReduceE e2

instance CheaplyReducibleE EffectRow EffectRow where
  cheapReduceE row = cheapReduceFromSubst row

instance CheaplyReducibleE FieldRowElems FieldRowElems where
  cheapReduceE elems = cheapReduceFromSubst elems

-- See Note [Confuse GHC] from Simplify.hs
confuseGHC :: CheapReducerM i n (DistinctEvidence n)
confuseGHC = getDistinct
{-# INLINE confuseGHC #-}
