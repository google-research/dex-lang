-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module CheapReduction
  ( CheaplyReducibleE (..), cheapReduce, cheapReduceWithDecls, cheapNormalize
  , DictTypeHoistStatus (..), normalizeProj, asNaryProj, normalizeNaryProj
  , depPairLeftTy, instantiateDataDef, applyDataConAbs
  , dataDefRep, instantiateDepPairTy, projType, unwrapNewtypeType, repValAtom
  , unwrapLeadingNewtypesType, wrapNewtypesData, liftSimpAtom, liftSimpType
  , liftSimpFun)
  where

import Control.Applicative
import Control.Monad.Trans
import Control.Monad.Writer.Strict
import Control.Monad.State.Strict
import Data.Foldable (toList)
import Data.Functor.Identity
import Data.Functor ((<&>))
import qualified Data.List.NonEmpty    as NE
import qualified Data.Map.Strict as M
import Data.Maybe
import GHC.Exts (inline)

import Subst
import Core
import Err
import IRVariants
import MTL1
import Name
import LabeledItems
import PPrint ()
import Types.Core
import Types.Imp
import Types.Primitives
import Util
import {-# SOURCE #-} Inference (trySynthTerm)

-- Carry out the reductions we are willing to carry out during type
-- inference.  The goal is to support type aliases like `Int = Int32`
-- and type-level functions like `def Fin (n:Int) : Type = Range 0 n`.
-- The reductions in question are mostly inlining and beta-reducing
-- functions.  There's also a bunch of stuff to do with synthesizing
-- class dictionaries, because types often contain polymorphic
-- literals (e.g., `Fin 10`).

-- === api ===

type NiceE r e = (HoistableE e, SinkableE e, SubstE AtomSubstVal e, RenameE e, IRRep r)

cheapReduce :: forall r e' e m n
             . (EnvReader m, CheaplyReducibleE r e e', NiceE r e, NiceE r e')
            => e n -> m n (Maybe (e' n), DictTypeHoistStatus, [Type r n])
cheapReduce e = liftCheapReducerM idSubst $ cheapReduceE e
{-# INLINE cheapReduce #-}
{-# SCC cheapReduce #-}

-- Third result contains the set of dictionary types that failed to synthesize
-- during traversal of the supplied decls.
cheapReduceWithDecls
  :: forall r e' e m n l
   . ( CheaplyReducibleE r e e', NiceE r e', NiceE r e, EnvReader m )
  => Nest (Decl r) n l -> e l -> m n (Maybe (e' n), DictTypeHoistStatus, [Type r n])
cheapReduceWithDecls decls result = do
  Abs decls' result' <- sinkM $ Abs decls result
  liftCheapReducerM idSubst $
    cheapReduceWithDeclsB decls' $
      cheapReduceE result'
{-# INLINE cheapReduceWithDecls #-}
{-# SCC cheapReduceWithDecls #-}

cheapNormalize :: (EnvReader m, CheaplyReducibleE r e e, NiceE r e) => e n -> m n (e n)
cheapNormalize a = cheapReduce a >>= \case
  (Just ans, _, _) -> return ans
  _ -> error "couldn't normalize expression"
{-# INLINE cheapNormalize #-}

-- === internal ===

newtype CheapReducerM (r::IR) (i :: S) (o :: S) (a :: *) =
  CheapReducerM
    (SubstReaderT AtomSubstVal
      (MaybeT1
        (WriterT1 (FailedDictTypes r)
          (ScopedT1 (MapE (AtomName r) (MaybeE (Atom r)))
            (EnvReaderT Identity)))) i o a)
  deriving (Functor, Applicative, Monad, Alternative)

deriving instance IRRep r => ScopeReader (CheapReducerM r i)
deriving instance IRRep r => EnvReader (CheapReducerM r i)
deriving instance IRRep r => EnvExtender (CheapReducerM r i)
deriving instance IRRep r => SubstReader AtomSubstVal (CheapReducerM r)

-- The `NothingE` case indicates dictionaries couldn't be hoisted
newtype FailedDictTypes (r::IR) (n::S) = FailedDictTypes (ESet (MaybeE (Type r)) n)
        deriving (SinkableE, HoistableE, Semigroup, Monoid)
data DictTypeHoistStatus = DictTypeHoistFailure | DictTypeHoistSuccess

instance IRRep r => HoistableState (FailedDictTypes r) where
  hoistState _ b (FailedDictTypes ds) =
    FailedDictTypes $ eSetFromList $
      for (eSetToList ds) \d -> case hoist b d of
        HoistSuccess d' -> d'
        HoistFailure _  -> NothingE

class ( Alternative2 m, SubstReader AtomSubstVal m
      , EnvReader2 m, EnvExtender2 m) => CheapReducer m r | m -> r where
  reportSynthesisFail :: Type r o -> m i o ()
  updateCache :: AtomName r o -> Maybe (Atom r o) -> m i o ()
  lookupCache :: AtomName r o -> m i o (Maybe (Maybe (Atom r o)))

instance IRRep r => CheapReducer (CheapReducerM r) r where
  reportSynthesisFail ty = CheapReducerM $ SubstReaderT $ lift $ lift11 $
    tell $ FailedDictTypes $ eSetSingleton (JustE ty)
  updateCache v u = CheapReducerM $ SubstReaderT $ lift $ lift11 $ lift11 $
    modify (MapE . M.insert v (toMaybeE u) . fromMapE)
  lookupCache v = CheapReducerM $ SubstReaderT $ lift $ lift11 $ lift11 $
    fmap fromMaybeE <$> gets (M.lookup v . fromMapE)

liftCheapReducerM :: (EnvReader m, IRRep r)
                  => Subst AtomSubstVal i o -> CheapReducerM r i o a
                  -> m o (Maybe a, DictTypeHoistStatus, [Type r o])
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

cheapReduceFromSubst :: NiceE CoreIR e => e i -> CheapReducerM CoreIR i o (e o)
cheapReduceFromSubst e = traverseNames cheapSubstName =<< substM e
  where
    cheapSubstName :: forall c i o . Color c => Name c o -> CheapReducerM CoreIR i o (AtomSubstVal c o)
    cheapSubstName v =
      case eqColorRep @c @(AtomNameC CoreIR) of
        Just ColorsEqual -> lookupEnv v >>= \case
          AtomNameBinding (LetBound (DeclBinding _ _ (Atom x))) ->
            liftM SubstVal $ dropSubst $ cheapReduceFromSubst x
          _ -> return $ Rename v
        Nothing -> return $ Rename v

cheapReduceWithDeclsB
  :: NiceE r e
  => Nest (Decl r) i i'
  -> (forall o'. Ext o o' => CheapReducerM r i' o' (e o'))
  -> CheapReducerM r i o (e o)
cheapReduceWithDeclsB decls cont = do
  Abs irreducibleDecls result <- cheapReduceWithDeclsRec decls cont
  case hoist irreducibleDecls result of
    HoistSuccess result' -> return result'
    HoistFailure _       -> empty

cheapReduceWithDeclsRec
  :: NiceE r e
  => Nest (Decl r) i i'
  -> (forall o'. Ext o o' => CheapReducerM r i' o' (e o'))
  -> CheapReducerM r i o (Abs (Nest (Decl r)) e o)
cheapReduceWithDeclsRec decls cont = case decls of
  Empty -> Abs Empty <$> cont
  Nest (Let b binding@(DeclBinding _ _ expr)) rest -> do
    optional (cheapReduceE expr) >>= \case
      Nothing -> do
        binding' <- substM binding
        withFreshBinder (getNameHint b) binding' \(b':>_) -> do
          updateCache (binderName b') Nothing
          extendSubst (b@>Rename (binderName b')) do
            Abs decls' result <- cheapReduceWithDeclsRec rest cont
            return $ Abs (Nest (Let b' binding') decls') result
      Just x ->
        extendSubst (b@>SubstVal x) $
          cheapReduceWithDeclsRec rest cont

cheapReduceName :: forall c r i o . (IRRep r, Color c) => Name c o -> CheapReducerM r i o (AtomSubstVal c o)
cheapReduceName v =
  case eqColorRep @c @(AtomNameC r) of
    Just ColorsEqual ->
      lookupEnv v >>= \case
      AtomNameBinding binding -> cheapReduceAtomBinding v binding
    Nothing -> stuck
  where stuck = return $ Rename v

cheapReduceAtomBinding
  :: forall r i o. IRRep r
  => AtomName r o -> AtomBinding r o -> CheapReducerM r i o (AtomSubstVal (AtomNameC r) o)
cheapReduceAtomBinding v = \case
  LetBound (DeclBinding _ _ e) -> do
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

class CheaplyReducibleE (r::IR) (e::E) (e'::E) | e -> e', e -> r where
  cheapReduceE :: e i -> CheapReducerM r i o (e' o)

instance IRRep r => CheaplyReducibleE r (Atom r) (Atom r) where
  cheapReduceE :: forall i o. Atom r i -> CheapReducerM r i o (Atom r o)
  cheapReduceE a = confuseGHC >>=  \_ -> case a of
    -- Don't try to eagerly reduce lambda bodies. We might get stuck long before
    -- we have a chance to apply tham. Also, recursive traversal of those bodies
    -- means that we will follow the full call chain, so it's really expensive!
    -- TODO: we don't collect the dict holes here, so there's a danger of
    -- dropping them if they turn out to be phantom.
    Lam _ _ _ -> substM a
    DictHole ctx ty' -> do
      ty <- cheapReduceE ty'
      runFallibleT1 (trySynthTerm ty) >>= \case
        Success d -> return d
        Failure _ -> do
          reportSynthesisFail ty
          return $ DictHole ctx ty
    TabPi (TabPiType (b:>ixTy) resultTy) -> do
      ixTy' <- cheapReduceE ixTy
      withFreshBinder (getNameHint b) ixTy' \b' -> do
        resultTy' <- extendSubst (b@>Rename (binderName b')) $ cheapReduceE resultTy
        return $ TabPi $ TabPiType b' resultTy'
    -- We traverse the Atom constructors that might contain lambda expressions
    -- explicitly, to make sure that we can skip normalizing free vars inside those.
    Con con -> Con <$> (inline traversePrimCon) cheapReduceE con
    DictCon d -> cheapReduceE d
    SimpInCore (LiftSimp t x) -> do
      t' <- cheapReduceE t
      x' <- substM x
      liftSimpAtom t' x'
    -- These two are a special-case hack. TODO(dougalm): write a traversal over
    -- the NewtypeTyCon (or types generally)
    NewtypeCon NatCon n -> NewtypeCon NatCon <$> cheapReduceE n
    NewtypeTyCon (Fin n) -> NewtypeTyCon . Fin <$> cheapReduceE n
    -- Do recursive reduction via substitution
    -- TODO: we don't collect the dict holes here, so there's a danger of
    -- dropping them if they turn out to be phantom.
    _ -> do
      a' <- substM a
      dropSubst $ traverseNames cheapReduceName a'

instance CheaplyReducibleE CoreIR DictExpr CAtom where
  cheapReduceE d = case d of
    SuperclassProj child superclassIx -> do
      cheapReduceE child >>= \case
        DictCon (InstanceDict instanceName args) -> dropSubst do
          args' <- mapM cheapReduceE args
          InstanceDef _ bs _ body <- lookupInstanceDef instanceName
          let InstanceBody superclasses _ = body
          applySubst (bs@@>(SubstVal <$> args')) (superclasses !! superclassIx)
        child' -> return $ DictCon $ SuperclassProj child' superclassIx
    InstantiatedGiven f xs -> do
      cheapReduceE (App f xs) <|> justSubst
    InstanceDict _ _ -> justSubst
    IxFin _          -> justSubst
    DataData ty      -> DictCon . DataData <$> cheapReduceE ty
    where justSubst = DictCon <$> substM d

instance CheaplyReducibleE CoreIR DataDefParams DataDefParams where
  cheapReduceE (DataDefParams ps) =
    DataDefParams <$> mapM (onSndM cheapReduceE) ps

instance (CheaplyReducibleE r e e', NiceE r e') => CheaplyReducibleE r (Abs (Nest (Decl r)) e) e' where
  cheapReduceE (Abs decls result) = cheapReduceWithDeclsB decls $ cheapReduceE result

instance (CheaplyReducibleE r (Atom r) e', NiceE r e') => CheaplyReducibleE r (Block r) e' where
  cheapReduceE (Block _ decls result) = cheapReduceE $ Abs decls result

instance IRRep r => CheaplyReducibleE r (Expr r) (Atom r) where
  cheapReduceE expr = confuseGHC >>= \_ -> case expr of
    Atom atom -> cheapReduceE atom
    App f' xs' -> do
      f <- cheapReduceE f'
      case fromNaryLamExact (length xs') f of
        Just (LamExpr bs body) -> do
          xs <- mapM cheapReduceE xs'
          let subst = bs @@> fmap SubstVal xs
          dropSubst $ extendSubst subst $ cheapReduceE body
        _ -> empty
    -- TODO: Make sure that this wraps correctly
    -- TODO: Other casts?
    PrimOp (MiscOp (CastOp ty' val')) -> do
      ty <- cheapReduceE ty'
      case ty of
        BaseTy (Scalar Word32Type) -> do
          val <- cheapReduceE val'
          case val of
            Con (Lit (Word64Lit v)) -> return $ Con $ Lit $ Word32Lit $ fromIntegral v
            _ -> empty
        _ -> empty
    ProjMethod dict i -> do
      cheapReduceE dict >>= \case
        DictCon (InstanceDict instanceName args) -> dropSubst do
          args' <- mapM cheapReduceE args
          InstanceDef _ bs _ (InstanceBody _ methods) <- lookupInstanceDef instanceName
          let method = methods !! i
          extendSubst (bs@@>(SubstVal <$> args')) $ cheapReduceE method
        _ -> empty
    _ -> empty

instance IRRep r => CheaplyReducibleE r (IxType r) (IxType r) where
  cheapReduceE (IxType t d) = IxType <$> cheapReduceE t <*> cheapReduceE d

instance IRRep r => CheaplyReducibleE r (IxDict r) (IxDict r) where
  cheapReduceE = \case
    IxDictAtom x -> IxDictAtom <$> cheapReduceE x
    IxDictRawFin n -> IxDictRawFin <$> cheapReduceE n
    IxDictSpecialized t d xs ->
      IxDictSpecialized <$> cheapReduceE t <*> substM d <*> mapM cheapReduceE xs

instance (CheaplyReducibleE r e1 e1', CheaplyReducibleE r e2 e2')
  => CheaplyReducibleE r (PairE e1 e2) (PairE e1' e2') where
    cheapReduceE (PairE e1 e2) = PairE <$> cheapReduceE e1 <*> cheapReduceE e2

instance (CheaplyReducibleE r e1 e1', CheaplyReducibleE r e2 e2')
  => CheaplyReducibleE r (EitherE e1 e2) (EitherE e1' e2') where
    cheapReduceE (LeftE e) = LeftE <$> cheapReduceE e
    cheapReduceE (RightE e) = RightE <$> cheapReduceE e

instance CheaplyReducibleE CoreIR FieldRowElems FieldRowElems where
  cheapReduceE elems = cheapReduceFromSubst elems

-- XXX: TODO: figure out exactly what our normalization invariants are. We
-- shouldn't have to choose `normalizeProj` or `asNaryProj` on a
-- case-by-case basis. This is here for now because it makes it easier to switch
-- to the new version of `ProjectElt`.
asNaryProj :: IRRep r => Projection -> Atom r n -> (NE.NonEmpty Projection, AtomName r n)
asNaryProj p (Var v) = (p NE.:| [], v)
asNaryProj p1 (ProjectElt p2 x) = do
  let (p2' NE.:| ps, v) = asNaryProj p2 x
  (p1 NE.:| (p2':ps), v)
asNaryProj p x = error $ "Can't normalize projection: " ++ pprint (ProjectElt p x)

-- assumes the atom is already normalized
normalizeNaryProj :: EnvReader m => [Projection] -> Atom r n -> m n (Atom r n)
normalizeNaryProj [] x = return x
normalizeNaryProj (i:is) x = normalizeProj i =<< normalizeNaryProj is x

-- assumes the atom itself is already normalized
normalizeProj :: EnvReader m => Projection -> Atom r n -> m n (Atom r n)
normalizeProj UnwrapNewtype atom = case atom of
   NewtypeCon  _ x -> return x
   SimpInCore (LiftSimp (NewtypeTyCon t) x) -> do
     t' <- snd <$> unwrapNewtypeType t
     return $ SimpInCore $ LiftSimp t' x
   x -> return $ ProjectElt UnwrapNewtype x
normalizeProj (ProjectProduct i) atom = case atom of
  Con (ProdCon xs) -> return $ xs !! i
  DepPair l _ _ | i == 0 -> return l
  DepPair _ r _ | i == 1 -> return r
  SimpInCore (LiftSimp ty x) -> do
    ty' <- projType i ty atom
    x' <- normalizeProj (ProjectProduct i) x
    return $ SimpInCore $ LiftSimp ty' x'
  RepValAtom (RepVal t tree) -> do
    t' <- projType i t =<< repValAtom (RepVal t tree)
    case tree of
      Branch trees -> repValAtom $ RepVal t' (trees!!i)
      Leaf _ -> error "unexpected leaf"
  x -> return $ ProjectElt (ProjectProduct i) x
{-# INLINE normalizeProj #-}

-- === lifting imp to simp and simp to core ===

repValAtom :: EnvReader m => SRepVal n -> m n (SAtom n)
repValAtom (RepVal ty tree) = case ty of
  ProdTy ts -> case tree of
    Branch trees -> ProdVal <$> mapM repValAtom (zipWith RepVal ts trees)
    _ -> malformed
  BaseTy _ -> case tree of
    Leaf x -> case x of
      ILit l -> return $ Con $ Lit l
      _ -> fallback
    _ -> malformed
  _ -> fallback
  where fallback = return $ RepValAtom $ RepVal ty tree
        malformed = error "malformed repval"
{-# INLINE repValAtom #-}

liftSimpType :: EnvReader m => SType n -> m n (CType n)
liftSimpType = \case
  BaseTy t -> return $ BaseTy t
  ProdTy ts -> ProdTy <$> mapM rec ts
  SumTy  ts -> SumTy  <$> mapM rec ts
  t -> error $ "not implemented: " ++ pprint t
  where rec = liftSimpType
{-# INLINE liftSimpType #-}

liftSimpAtom :: EnvReader m => Type CoreIR n -> SAtom n -> m n (CAtom n)
liftSimpAtom ty simpAtom = case simpAtom of
  Var _          -> justLift
  ProjectElt _ _ -> justLift
  RepValAtom _   -> justLift -- TODO(dougalm): should we make more effort to pull out products etc?
  _ -> do
    (cons , ty') <- unwrapLeadingNewtypesType ty
    atom <- case (ty', simpAtom) of
      (BaseTy _  , Con (Lit v))      -> return $ Con $ Lit v
      (ProdTy tys, Con (ProdCon xs))   -> Con . ProdCon <$> zipWithM rec tys xs
      (SumTy  tys, Con (SumCon _ i x)) -> Con . SumCon tys i <$> rec (tys!!i) x
      (DepPairTy dpt@(DepPairType (b:>t1) t2), DepPair x1 x2 _) -> do
        x1' <- rec t1 x1
        t2' <- applySubst (b@>SubstVal x1') t2
        x2' <- rec t2' x2
        return $ DepPair x1' x2' dpt
      _ -> error $ "can't lift " <> pprint simpAtom <> " to " <> pprint ty'
    return $ wrapNewtypesData cons atom
  where
    rec = liftSimpAtom
    justLift = return $ SimpInCore $ LiftSimp ty simpAtom
{-# INLINE liftSimpAtom #-}

liftSimpFun :: EnvReader m => Type CoreIR n -> LamExpr SimpIR n -> m n (CAtom n)
liftSimpFun (Pi piTy) f = return $ SimpInCore $ LiftSimpFun piTy f
liftSimpFun _ _ = error "not a pi type"

-- See Note [Confuse GHC] from Simplify.hs
confuseGHC :: IRRep r => CheapReducerM r i n (DistinctEvidence n)
confuseGHC = getDistinct
{-# INLINE confuseGHC #-}

-- === Type-querying helpers ===

-- TODO: These used to live in QueryType. Think about a better way to organize
-- them. Maybe a common set of low-level type-querying utils that both
-- CheapReduction and QueryType import?

depPairLeftTy :: DepPairType r n -> Type r n
depPairLeftTy (DepPairType (_:>ty) _) = ty
{-# INLINE depPairLeftTy #-}

unwrapNewtypeType :: EnvReader m => NewtypeTyCon n -> m n (NewtypeCon n, Type CoreIR n)
unwrapNewtypeType = \case
  Nat                   -> return (NatCon, IdxRepTy)
  Fin n                 -> return (FinCon n, NatTy)
  StaticRecordTyCon tys    -> return (RecordCon  (void tys), ProdTy (toList tys))
  UserADTType _ defName params -> do
    def <- lookupDataDef defName
    ty' <- dataDefRep <$> instantiateDataDef def params
    return (UserADTData defName params, ty')
  ty -> error $ "Shouldn't be projecting: " ++ pprint ty
{-# INLINE unwrapNewtypeType #-}

unwrapLeadingNewtypesType :: EnvReader m => CType n -> m n ([NewtypeCon n], CType n)
unwrapLeadingNewtypesType = \case
  NewtypeTyCon tyCon -> do
    (dataCon, ty) <- unwrapNewtypeType tyCon
    (dataCons, ty') <- unwrapLeadingNewtypesType ty
    return (dataCon:dataCons, ty')
  ty -> return ([], ty)

wrapNewtypesData :: [NewtypeCon n] -> CAtom n-> CAtom n
wrapNewtypesData [] x = x
wrapNewtypesData (c:cs) x = NewtypeCon c $ wrapNewtypesData cs x

instantiateDataDef :: EnvReader m => DataDef n -> DataDefParams n -> m n [DataConDef n]
instantiateDataDef (DataDef _ bs cons) params = do
  fromListE <$> applyDataConAbs (Abs bs $ ListE cons) params
{-# INLINE instantiateDataDef #-}

applyDataConAbs :: (SubstE AtomSubstVal e, SinkableE e, EnvReader m)
                => Abs (Nest RolePiBinder) e n -> DataDefParams n -> m n (e n)
applyDataConAbs (Abs bs e) (DataDefParams xs) =
  applySubst (bs @@> (SubstVal <$> map snd xs)) e
{-# INLINE applyDataConAbs #-}

-- Returns a representation type (type of an TypeCon-typed Newtype payload)
-- given a list of instantiated DataConDefs.
dataDefRep :: [DataConDef n] -> CType n
dataDefRep = \case
  [] -> error "unreachable"  -- There's no representation for a void type
  [DataConDef _ _ ty _] -> ty
  tys -> SumTy $ tys <&> \(DataConDef _ _ ty _) -> ty

instantiateDepPairTy :: (IRRep r, EnvReader m) => DepPairType r n -> Atom r n -> m n (Type r n)
instantiateDepPairTy (DepPairType b rhsTy) x = applyAbs (Abs b rhsTy) (SubstVal x)
{-# INLINE instantiateDepPairTy #-}

projType :: (IRRep r, EnvReader m) => Int -> Type r n -> Atom r n -> m n (Type r n)
projType i ty x = case ty of
  ProdTy xs -> return $ xs !! i
  DepPairTy t | i == 0 -> return $ depPairLeftTy t
  DepPairTy t | i == 1 -> do
    xFst <- normalizeProj (ProjectProduct 0) x
    instantiateDepPairTy t xFst
  _ -> error $ "Can't project type: " ++ pprint ty

-- === SubstE/SubstB instances ===
-- These live here, as orphan instances, because we normalize as we substitute.

instance Color c => SubstE AtomSubstVal (AtomSubstVal c) where
  substE (_, env) (Rename name) = env ! name
  substE env (SubstVal val) = SubstVal $ substE env val

instance SubstV (SubstVal Atom) (SubstVal Atom) where

instance IRRep r => SubstE AtomSubstVal (Atom r) where
  substE (env, subst) atom = case fromE atom of
    Case0 specialCase -> case specialCase of
      -- Var
      Case0 v -> do
        case subst ! v of
          Rename v' -> Var v'
          SubstVal x -> x
      -- ProjectElt
      Case1 (PairE (LiftE i) x) -> do
        let x' = substE (env, subst) x
        runEnvReaderM env $ normalizeProj i x'
      _ -> error "impossible"
    Case1 rest -> (toE . Case1) $ substE (env, subst) rest
    Case2 rest -> (toE . Case2) $ substE (env, subst) rest
    Case3 rest -> (toE . Case3) $ substE (env, subst) rest
    Case4 rest -> (toE . Case4) $ substE (env, subst) rest
    _ -> error "impossible"

instance SubstE AtomSubstVal SimpInCore

instance IRRep r => SubstE AtomSubstVal (EffectRow r) where
  substE env (EffectRow effs tailVar) = do
    let effs' = eSetFromList $ map (substE env) (eSetToList effs)
    let tailEffRow = case tailVar of
          NoTail -> EffectRow mempty NoTail
          EffectRowTail v -> case snd env ! v of
            Rename        v'  -> EffectRow mempty (EffectRowTail v')
            SubstVal (Var v') -> EffectRow mempty (EffectRowTail v')
            SubstVal (Eff r)  -> r
            _ -> error "Not a valid effect substitution"
    extendEffRow effs' tailEffRow

instance IRRep r => SubstE AtomSubstVal (Effect r)

instance SubstE AtomSubstVal SpecializationSpec where
  substE env (AppSpecialization f ab) = do
    let f' = case snd env ! f of
               Rename v -> v
               SubstVal (Var v) -> v
               _ -> error "bad substitution"
    AppSpecialization f' (substE env ab)

instance IRRep r => SubstE AtomSubstVal (ExtLabeledItemsE (Atom r) (AtomName r)) where
  substE (scope, env) (ExtLabeledItemsE (Ext items maybeExt)) = do
    let items' = fmap (substE (scope, env)) items
    let ext = case maybeExt of
                Nothing -> NoExt NoLabeledItems
                Just v -> case env ! v of
                  Rename        v'  -> Ext NoLabeledItems $ Just v'
                  SubstVal (Var v') -> Ext NoLabeledItems $ Just v'
                  SubstVal (NewtypeTyCon (LabeledRowCon row)) -> case fieldRowElemsAsExtRow row of
                    Just row' -> row'
                    Nothing -> error "Not implemented: unrepresentable subst of ExtLabeledItems"
                  _ -> error "Not a valid labeled row substitution"
    ExtLabeledItemsE $ prefixExtLabeledItems items' ext

instance SubstE AtomSubstVal FieldRowElems where
  substE :: forall i o. Distinct o => (Env o, Subst AtomSubstVal i o) -> FieldRowElems i -> FieldRowElems o
  substE env (UnsafeFieldRowElems els) = fieldRowElemsFromList $ foldMap substItem els
    where
      substItem = \case
        DynField v ty -> case snd env ! v of
          SubstVal (NewtypeTyCon (LabelCon l)) -> [StaticFields $ labeledSingleton l ty']
          SubstVal (Var v') -> [DynField v' ty']
          Rename v'         -> [DynField v' ty']
          _ -> error "ill-typed substitution"
          where ty' = substE env ty
        DynFields v -> case snd env ! v of
          SubstVal (NewtypeTyCon (LabeledRowCon items)) -> fromFieldRowElems items
          SubstVal (Var v') -> [DynFields v']
          Rename v'         -> [DynFields v']
          _ -> error "ill-typed substitution"
        StaticFields items -> [StaticFields items']
          where ExtLabeledItemsE (NoExt items') = substE env
                  (ExtLabeledItemsE (NoExt items) :: ExtLabeledItemsE CAtom CAtomName i)

instance SubstE AtomSubstVal EffectDef
instance SubstE AtomSubstVal EffectOpType
instance SubstE AtomSubstVal IExpr
instance IRRep r => SubstE AtomSubstVal (RepVal r)
instance SubstE AtomSubstVal DataDefParams
instance SubstE AtomSubstVal DataConDef
instance IRRep r => SubstE AtomSubstVal (BaseMonoid r)
instance SubstE AtomSubstVal UserEffectOp
instance IRRep r => SubstE AtomSubstVal (DAMOp r)
instance IRRep r => SubstE AtomSubstVal (Hof r)
instance IRRep r => SubstE AtomSubstVal (RefOp r)
instance IRRep r => SubstE AtomSubstVal (Expr r)
instance IRRep r => SubstE AtomSubstVal (Block r)
instance SubstE AtomSubstVal InstanceBody
instance SubstE AtomSubstVal MethodType
instance SubstE AtomSubstVal DictType
instance SubstE AtomSubstVal DictExpr
instance IRRep r => SubstE AtomSubstVal (LamExpr r)
instance IRRep r => SubstE AtomSubstVal (DestBlock r)
instance SubstE AtomSubstVal PiType
instance IRRep r => SubstE AtomSubstVal (TabPiType r)
instance IRRep r => SubstE AtomSubstVal (NaryPiType r)
instance IRRep r => SubstE AtomSubstVal (DepPairType r)
instance SubstE AtomSubstVal SolverBinding
instance IRRep r => SubstE AtomSubstVal (DeclBinding r)
instance IRRep r => SubstB AtomSubstVal (Decl r)
instance SubstE AtomSubstVal NewtypeTyCon
instance SubstE AtomSubstVal NewtypeCon
instance IRRep r => SubstE AtomSubstVal (IxDict r)
instance IRRep r => SubstE AtomSubstVal (IxType r)

instance SubstB AtomSubstVal RolePiBinder where
  substB env (RolePiBinder b ty arr role) cont =
    substB env (b:>ty) \env' (b':>ty') -> cont env' $ RolePiBinder b' ty' arr role

-- XXX: we need a special instance here because `SuperclassBinder` have all
-- their types at the level of the top binder, rather than interleaving them
-- with the binders. We should make a `BindersNest` type for that pattern
-- instead.
instance SubstB AtomSubstVal SuperclassBinders where
  substB envSubst (SuperclassBinders bsTop tsTop) contTop = do
    let tsTop' = map (substE envSubst) tsTop
    go envSubst bsTop tsTop' \envSubst' bsTop' -> contTop envSubst' $ SuperclassBinders bsTop' tsTop'
    where
      go :: (Distinct o, FromName v, SinkableV v)
         => (Env o, Subst v i o)
         -> Nest (AtomNameBinder CoreIR) i i' -> [Type CoreIR o]
         -> (forall o'. Distinct o' => (Env o', Subst v i' o') -> Nest (AtomNameBinder CoreIR) o o' -> a)
         -> a
      go (env, subst) Empty [] cont = cont (env, subst) Empty
      go (env, subst) (Nest b bs) (t:ts) cont = do
        withFresh (getNameHint b) (toScope env) \b' -> do
          let env' = env `extendOutMap` toEnvFrag (b':>t)
          let subst' = sink subst <>> b @> (fromName $ binderName b')
          go (env', subst') bs (map sink ts) \envSubst'' bs' -> cont envSubst'' (Nest b' bs')
      go _ _ _ _ = error "zip error"
