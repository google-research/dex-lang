-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module CheapReduction
  ( CheaplyReducibleE (..), cheapReduce, cheapReduceWithDecls, cheapNormalize
  , DictTypeHoistStatus (..))
  where

import Control.Applicative
import Control.Monad.Trans
import Control.Monad.Writer.Strict
import Control.Monad.State.Strict
import Data.Functor.Identity
import qualified Data.Map.Strict as M
import Data.Maybe
import GHC.Exts (inline)

import MTL1
import Name
import Syntax
import PPrint ()
import {-# SOURCE #-} Inference (trySynthTerm)
import Err
import Types.Primitives
import Util (for)

-- Carry out the reductions we are willing to carry out during type
-- inference.  The goal is to support type aliases like `Int = Int32`
-- and type-level functions like `def Fin (n:Int) : Type = Range 0 n`.
-- The reductions in question are mostly inlining and beta-reducing
-- functions.  There's also a bunch of stuff to do with synthesizing
-- class dictionaries, because types often contain polymorphic
-- literals (e.g., `Fin 10`).

-- === api ===

type NiceE e = (HoistableE e, SinkableE e, SubstE AtomSubstVal e, SubstE Name e)

cheapReduce :: forall e' e m n
             . (EnvReader m, CheaplyReducibleE e e', NiceE e, NiceE e')
            => e n -> m n (Maybe (e' n), DictTypeHoistStatus, [Type n])
cheapReduce e = liftCheapReducerM idSubst $ cheapReduceE e
{-# INLINE cheapReduce #-}
{-# SCC cheapReduce #-}

-- Third result contains the set of dictionary types that failed to synthesize
-- during traversal of the supplied decls.
cheapReduceWithDecls
  :: forall e' e m n l
   . ( CheaplyReducibleE e e', NiceE e', NiceE e, EnvReader m )
  => Nest Decl n l -> e l -> m n (Maybe (e' n), DictTypeHoistStatus, [Type n])
cheapReduceWithDecls decls result = do
  Abs decls' result' <- sinkM $ Abs decls result
  liftCheapReducerM idSubst $
    cheapReduceWithDeclsB decls' $
      cheapReduceE result'
{-# INLINE cheapReduceWithDecls #-}
{-# SCC cheapReduceWithDecls #-}

cheapNormalize :: (EnvReader m, CheaplyReducibleE e e, NiceE e) => e n -> m n (e n)
cheapNormalize a = cheapReduce a >>= \case
  (Just ans, _, _) -> return ans
  _ -> error "couldn't normalize expression"
{-# INLINE cheapNormalize #-}

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

-- The `NothingE` case indicates dictionaries couldn't be hoisted
newtype FailedDictTypes (n::S) = FailedDictTypes (ESet (MaybeE Type) n)
        deriving (SinkableE, HoistableE, Semigroup, Monoid)
data DictTypeHoistStatus = DictTypeHoistFailure | DictTypeHoistSuccess

instance HoistableState FailedDictTypes where
  hoistState _ b (FailedDictTypes ds) =
    FailedDictTypes $ eSetFromList $
      for (eSetToList ds) \d -> case hoist b d of
        HoistSuccess d' -> d'
        HoistFailure _  -> NothingE

class ( Alternative2 m, SubstReader AtomSubstVal m
      , EnvReader2 m, EnvExtender2 m) => CheapReducer m where
  reportSynthesisFail :: Type o -> m i o ()
  updateCache :: AtomName o -> Maybe (Atom o) -> m i o ()
  lookupCache :: AtomName o -> m i o (Maybe (Maybe (Atom o)))

instance CheapReducer CheapReducerM where
  reportSynthesisFail ty = CheapReducerM $ SubstReaderT $ lift $ lift11 $
    tell $ FailedDictTypes $ eSetSingleton (JustE ty)
  updateCache v u = CheapReducerM $ SubstReaderT $ lift $ lift11 $ lift11 $
    modify (MapE . M.insert v (toMaybeE u) . fromMapE)
  lookupCache v = CheapReducerM $ SubstReaderT $ lift $ lift11 $ lift11 $
    fmap fromMaybeE <$> gets (M.lookup v . fromMapE)

liftCheapReducerM :: EnvReader m
                  => Subst AtomSubstVal i o -> CheapReducerM i o a
                  -> m o (Maybe a, DictTypeHoistStatus, [Type o])
liftCheapReducerM subst (CheapReducerM m) = do
  (result, FailedDictTypes tySet) <-
    liftM runIdentity $ liftEnvReaderT $ runScopedT1
      (runWriterT1 $ runMaybeT1 $ runSubstReaderT subst m) mempty
  let maybeTys = eSetToList tySet
  let tys = catMaybes $ map fromMaybeE maybeTys
  let hoistStatus = if any (\case NothingE -> True; _ -> False) maybeTys
                      then DictTypeHoistFailure
                      else DictTypeHoistSuccess
  return (result, hoistStatus, tys)
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
  -> CheapReducerM i o (e o)
cheapReduceWithDeclsB decls cont = do
  Abs irreducibleDecls result <- cheapReduceWithDeclsRec decls cont
  case hoist irreducibleDecls result of
    HoistSuccess result' -> return result'
    HoistFailure _       -> empty

cheapReduceWithDeclsRec
  :: ( HoistableE e, SinkableE e, SubstE AtomSubstVal e, SubstE Name e)
  => Nest Decl i i'
  -> (forall o'. Ext o o' => CheapReducerM i' o' (e o'))
  -> CheapReducerM i o (Abs (Nest Decl) e o)
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

cheapReduceName :: Color c => Name c o -> CheapReducerM i o (AtomSubstVal c o)
cheapReduceName v =
  lookupEnv v >>= \case
    AtomNameBinding (LetBound (DeclBinding _ _ e)) -> case e of
      -- We avoid synthesizing the dictionaries during the traversal
      -- and only do that when cheap reduction is performed on the expr directly.
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
  cheapReduceE :: e i -> CheapReducerM i o (e' o)

instance CheaplyReducibleE Atom Atom where
  cheapReduceE :: forall i o. Atom i -> CheapReducerM i o (Atom o)
  cheapReduceE a = confuseGHC >>=  \_ -> case a of
    -- Don't try to eagerly reduce lambda bodies. We might get stuck long before
    -- we have a chance to apply tham. Also, recursive traversal of those bodies
    -- means that we will follow the full call chain, so it's really expensive!
    -- TODO: we don't collect the dict holes here, so there's a danger of
    -- dropping them if they turn out to be phantom.
    Lam _   -> substM a
    Con (DictHole ctx ty') -> do
      ty <- cheapReduceE ty'
      runFallibleT1 (trySynthTerm ty) >>= \case
        Success d -> return d
        Failure _ -> do
          reportSynthesisFail ty
          return $ Con $ DictHole ctx ty
    TabPi (TabPiType (b:>IxType ixTy dict) resultTy) -> do
      ixTy' <- cheapReduceE ixTy
      dict' <- cheapReduceE dict
      withFreshBinder (getNameHint b) (IxType ixTy' dict') \b' -> do
        resultTy' <- extendSubst (b@>Rename (binderName b')) $ cheapReduceE resultTy
        return $ TabPi $ TabPiType (b':>IxType ixTy' dict') resultTy'
    -- We traverse the Atom constructors that might contain lambda expressions
    -- explicitly, to make sure that we can skip normalizing free vars inside those.
    Con con -> Con <$> (inline traversePrimCon) cheapReduceE con
    DataCon sourceName dataDefName params con args ->
      DataCon sourceName <$> substM dataDefName <*> cheapReduceE params
                         <*> pure con <*> mapM cheapReduceE args
    Record items -> Record <$> mapM cheapReduceE items
    Variant ty l c p -> do
      ExtLabeledItemsE ty' <- substM $ ExtLabeledItemsE ty
      Variant ty' l c <$> cheapReduceE p
    DictCon d -> cheapReduceE d
    -- Do recursive reduction via substitution
    -- TODO: we don't collect the dict holes here, so there's a danger of
    -- dropping them if they turn out to be phantom.
    _ -> do
      a' <- substM a
      dropSubst $ traverseNames cheapReduceName a'

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
    IxFin _          -> justSubst
    where justSubst = DictCon <$> substM d

instance CheaplyReducibleE DataDefParams DataDefParams where
  cheapReduceE (DataDefParams ps ds) =
    DataDefParams <$> mapM cheapReduceE ps
                  <*> mapM cheapReduceE ds

instance (CheaplyReducibleE e e', NiceE e') => CheaplyReducibleE (Abs (Nest Decl) e) e' where
  cheapReduceE (Abs decls result) = cheapReduceWithDeclsB decls $ cheapReduceE result

instance (CheaplyReducibleE Atom e', NiceE e') => CheaplyReducibleE Block e' where
  cheapReduceE (Block _ decls result) = cheapReduceE $ Abs decls result

instance CheaplyReducibleE Expr Atom where
  cheapReduceE expr = confuseGHC >>= \_ -> case expr of
    Atom atom -> cheapReduceE atom
    App f' xs' -> do
      f <- cheapReduceE f'
      case fromNaryLamExact (length xs') f of
        Just (NaryLamExpr bs _ body) -> do
          xs <- mapM cheapReduceE xs'
          let subst = bs @@> fmap SubstVal xs
          dropSubst $ extendSubst subst $ cheapReduceE body
        _ -> empty
    -- TODO: Make sure that this wraps correctly
    -- TODO: Other casts?
    Op (CastOp ty' val') -> do
      ty <- cheapReduceE ty'
      case ty of
        BaseTy (Scalar Word32Type) -> do
          val <- cheapReduceE val'
          case val of
            Con (Lit (Word64Lit v)) -> return $ Con $ Lit $ Word32Lit $ fromIntegral v
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
