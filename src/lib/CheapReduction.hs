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
  , depPairLeftTy, projectNewtype, instantiateDataDef, applyDataConAbs
  , dataDefRep, instantiateDepPairTy, projType, isNewtype )
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
import qualified Data.Set        as S
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

type NiceE r e = (HoistableE e, SinkableE e, SubstE (AtomSubstVal r) e, RenameE e)

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
    (SubstReaderT (AtomSubstVal r)
      (MaybeT1
        (WriterT1 (FailedDictTypes r)
          (ScopedT1 (MapE (AtomName r) (MaybeE (Atom r)))
            (EnvReaderT Identity)))) i o a)
  deriving ( Functor, Applicative, Monad, Alternative
           , EnvReader, ScopeReader, EnvExtender
           , SubstReader (AtomSubstVal r))

-- The `NothingE` case indicates dictionaries couldn't be hoisted
newtype FailedDictTypes (r::IR) (n::S) = FailedDictTypes (ESet (MaybeE (Type r)) n)
        deriving (SinkableE, HoistableE, Semigroup, Monoid)
data DictTypeHoistStatus = DictTypeHoistFailure | DictTypeHoistSuccess

instance HoistableState (FailedDictTypes r) where
  hoistState _ b (FailedDictTypes ds) =
    FailedDictTypes $ eSetFromList $
      for (eSetToList ds) \d -> case hoist b d of
        HoistSuccess d' -> d'
        HoistFailure _  -> NothingE

class ( Alternative2 m, SubstReader (AtomSubstVal r) m
      , EnvReader2 m, EnvExtender2 m) => CheapReducer m r | m -> r where
  reportSynthesisFail :: Type r o -> m i o ()
  updateCache :: AtomName r o -> Maybe (Atom r o) -> m i o ()
  lookupCache :: AtomName r o -> m i o (Maybe (Maybe (Atom r o)))

instance CheapReducer (CheapReducerM r) r where
  reportSynthesisFail ty = CheapReducerM $ SubstReaderT $ lift $ lift11 $
    tell $ FailedDictTypes $ eSetSingleton (JustE ty)
  updateCache v u = CheapReducerM $ SubstReaderT $ lift $ lift11 $ lift11 $
    modify (MapE . M.insert v (toMaybeE u) . fromMapE)
  lookupCache v = CheapReducerM $ SubstReaderT $ lift $ lift11 $ lift11 $
    fmap fromMaybeE <$> gets (M.lookup v . fromMapE)

liftCheapReducerM :: EnvReader m
                  => Subst (AtomSubstVal r) i o -> CheapReducerM r i o a
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

cheapReduceFromSubst
  :: forall r e i o . NiceE r e
  => e i -> CheapReducerM r i o (e o)
cheapReduceFromSubst e = traverseNames cheapSubstName =<< substM e
  where
    cheapSubstName :: Color c => Name c o -> CheapReducerM r i o (AtomSubstVal r c o)
    cheapSubstName v = lookupEnv v >>= \case
      AtomNameBinding (LetBound (DeclBinding _ _ (Atom x))) ->
        liftM SubstVal $ dropSubst $ cheapReduceFromSubst $ unsafeCoerceIRE x
      _ -> return $ Rename v

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
        withFreshBinder (getNameHint b) binding' \b' -> do
          updateCache (binderName b') Nothing
          extendSubst (b@>Rename (binderName b')) do
            Abs decls' result <- cheapReduceWithDeclsRec rest cont
            return $ Abs (Nest (Let b' binding') decls') result
      Just x ->
        extendSubst (b@>SubstVal x) $
          cheapReduceWithDeclsRec rest cont

cheapReduceName :: Color c => Name c o -> CheapReducerM r i o (AtomSubstVal r c o)
cheapReduceName v =
  lookupEnv v >>= \case
    AtomNameBinding (LetBound (DeclBinding _ _ e)) -> case e of
      -- We avoid synthesizing the dictionaries during the traversal
      -- and only do that when cheap reduction is performed on the expr directly.
      _ -> do
        cachedVal <- lookupCache v >>= \case
          Nothing -> do
            result <- optional (dropSubst $ cheapReduceE $ unsafeCoerceIRE e)
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

instance CheaplyReducibleE r (Atom r) (Atom r) where
  cheapReduceE :: forall i o. Atom r i -> CheapReducerM r i o (Atom r o)
  cheapReduceE a = confuseGHC >>=  \_ -> case a of
    -- Don't try to eagerly reduce lambda bodies. We might get stuck long before
    -- we have a chance to apply tham. Also, recursive traversal of those bodies
    -- means that we will follow the full call chain, so it's really expensive!
    -- TODO: we don't collect the dict holes here, so there's a danger of
    -- dropping them if they turn out to be phantom.
    Lam _ _ _ -> substM a
    Con (DictHole ctx ty') -> do
      ty <- cheapReduceE ty'
      runFallibleT1 (trySynthTerm $ unsafeCoerceIRE ty) >>= \case
        Success d -> return $ unsafeCoerceIRE d
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
    DictCon d -> cheapReduceE d
    -- Do recursive reduction via substitution
    -- TODO: we don't collect the dict holes here, so there's a danger of
    -- dropping them if they turn out to be phantom.
    _ -> do
      a' <- substM a
      dropSubst $ traverseNames cheapReduceName a'

instance CheaplyReducibleE r (DictExpr r) (Atom r) where
  cheapReduceE d = case d of
    SuperclassProj child superclassIx -> do
      cheapReduceE child >>= \case
        DictCon (InstanceDict instanceName args) -> dropSubst do
          args' <- mapM cheapReduceE args
          InstanceDef _ bs _ body <- lookupInstanceDef instanceName
          let InstanceBody superclasses _ = body
          applySubst (bs@@>(SubstVal <$> args')) (unsafeCoerceIRE $ superclasses !! superclassIx)
        child' -> return $ DictCon $ SuperclassProj child' superclassIx
    InstantiatedGiven f xs -> do
      cheapReduceE (App f xs) <|> justSubst
    InstanceDict _ _ -> justSubst
    IxFin _          -> justSubst
    ExplicitMethods _ _ -> justSubst
    where justSubst = DictCon <$> substM d

instance CheaplyReducibleE r (DataDefParams r) (DataDefParams r) where
  cheapReduceE (DataDefParams ps) =
    DataDefParams <$> mapM (onSndM cheapReduceE) ps

instance (CheaplyReducibleE r e e', NiceE r e') => CheaplyReducibleE r (Abs (Nest (Decl r)) e) e' where
  cheapReduceE (Abs decls result) = cheapReduceWithDeclsB decls $ cheapReduceE result

instance (CheaplyReducibleE r (Atom r) e', NiceE r e') => CheaplyReducibleE r (Block r) e' where
  cheapReduceE (Block _ decls result) = cheapReduceE $ Abs decls result

instance CheaplyReducibleE r (Expr r) (Atom r) where
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
          extendSubst (bs@@>(SubstVal <$> args')) $
            cheapReduceE $ unsafeCoerceIRE method
        _ -> empty
    _ -> empty

instance (CheaplyReducibleE r e1 e1', CheaplyReducibleE r e2 e2')
  => CheaplyReducibleE r (PairE e1 e2) (PairE e1' e2') where
    cheapReduceE (PairE e1 e2) = PairE <$> cheapReduceE e1 <*> cheapReduceE e2

instance (CheaplyReducibleE r e1 e1', CheaplyReducibleE r e2 e2')
  => CheaplyReducibleE r (EitherE e1 e2) (EitherE e1' e2') where
    cheapReduceE (LeftE e) = LeftE <$> cheapReduceE e
    cheapReduceE (RightE e) = RightE <$> cheapReduceE e

instance CheaplyReducibleE r (FieldRowElems r) (FieldRowElems r) where
  cheapReduceE elems = cheapReduceFromSubst elems

-- XXX: TODO: figure out exactly what our normalization invariants are. We
-- shouldn't have to choose `normalizeProj` or `asNaryProj` on a
-- case-by-case basis. This is here for now because it makes it easier to switch
-- to the new version of `ProjectElt`.
asNaryProj :: Projection -> Atom r n -> (NE.NonEmpty Projection, AtomName r n)
asNaryProj p (Var v) = (p NE.:| [], v)
asNaryProj p1 (ProjectElt p2 x) = do
  let (p2' NE.:| ps, v) = asNaryProj p2 x
  (p1 NE.:| (p2':ps), v)
asNaryProj p x = error $ "Can't normalize projection: " ++ pprint (ProjectElt p x)

-- assumes the atom is already normalized
normalizeNaryProj :: EnvReader m => [Projection] -> Atom r n -> m n (Atom r n)
normalizeNaryProj [] x = return x
normalizeNaryProj (i:is) x = normalizeProj i =<< normalizeNaryProj is x

-- assumes the atom is already normalized
normalizeProj :: EnvReader m => Projection -> Atom r n -> m n (Atom r n)
normalizeProj i pTop = liftEnvReaderM $ go pTop where
  go :: Atom r n -> EnvReaderM n (Atom r n)
  go = \case
    Con (ProdCon xs) -> return $ xs !! iProd
    Con (Newtype _ x) | (i ==  UnwrapBaseNewtype) || (i == UnwrapCompoundNewtype) -> return x
    DepPair l _ _ | iProd == 0 -> return l
    DepPair _ r _ | iProd == 1 -> return r
    RepValAtom repVal -> normalizeProjRepVal i repVal
    x@(ACase scrut alts resultTy) -> do
      alts' <- forM alts \ab ->
        refreshAbs ab \bs body ->
          Abs bs <$> normalizeProj i body
      resultTy' <- projType i resultTy x
      return $ ACase scrut alts' resultTy'
    x -> return $ ProjectElt i x
  iProd = case i of
    ProjectProduct i' -> i'
    _ -> error $ "Not a product projection"
{-# INLINE normalizeProj #-}

-- assumes the atom is already normalized
normalizeProjRepVal :: (r `Sat` Is SimpToImpIR, EnvReader m) => Projection -> RepVal r n -> m n (Atom r n)
normalizeProjRepVal projection (RepVal ty tree) = case projection of
  ProjectProduct i -> do
    case ty of
      ProdTy tys -> do
        ~(Branch trees) <- return tree
        return $ RepValAtom $ RepVal (tys!!i) (trees!!i)
      DepPairTy t -> do
        ~(Branch [leftTree, rightTree]) <- return tree
        let leftVal = RepValAtom $ RepVal (depPairLeftTy t) leftTree
        case i of
          0 -> return leftVal
          1 -> do
            rightTy <- instantiateDepPairTy t leftVal
            return $ RepValAtom $ RepVal rightTy rightTree
          _ -> error "bad dependent pair projection index"
      _ -> error $ "not a product type: " ++ pprint ty
  UnwrapCompoundNewtype -> RepValAtom <$> (RepVal <$> projectNewtype ty <*> pure tree)
  UnwrapBaseNewtype     -> RepValAtom <$> (RepVal <$> projectNewtype ty <*> pure tree)

-- See Note [Confuse GHC] from Simplify.hs
confuseGHC :: CheapReducerM r i n (DistinctEvidence n)
confuseGHC = getDistinct
{-# INLINE confuseGHC #-}


-- === Type-querying helpers ===

-- TODO: These used to live in QueryType. Think about a better way to organize
-- them. Maybe a common set of low-level type-querying utils that both
-- CheapReduction and QueryType import?

depPairLeftTy :: DepPairType r n -> Type r n
depPairLeftTy (DepPairType (_:>ty) _) = ty
{-# INLINE depPairLeftTy #-}

projectNewtype :: EnvReader m => Type r n -> m n (Type r n)
projectNewtype ty = case ty of
  TC Nat     -> return IdxRepTy
  TC (Fin _) -> return NatTy
  TypeCon _ defName params -> do
    def <- lookupDataDef defName
    dataDefRep <$> instantiateDataDef def params
  StaticRecordTy types -> return $ ProdTy $ toList types
  RecordTy _ -> error "Can't project partially-known records"
  _ -> error $ "not a newtype: " ++ pprint ty

instantiateDataDef :: EnvReader m => DataDef n -> DataDefParams r n -> m n [DataConDef n]
instantiateDataDef (DataDef _ bs cons) (DataDefParams params) = do
  let dataDefParams' = DataDefParams [(arr, unsafeCoerceIRE x) | (arr, x) <- params]
  fromListE <$> applyDataConAbs (Abs bs $ ListE cons) dataDefParams'
{-# INLINE instantiateDataDef #-}

applyDataConAbs :: (SubstE (AtomSubstVal r) e, SinkableE e, EnvReader m)
                => Abs (Nest (RolePiBinder r)) e n -> DataDefParams r n -> m n (e n)
applyDataConAbs (Abs bs e) (DataDefParams xs) =
  applySubst (bs @@> (SubstVal <$> map snd xs)) e
{-# INLINE applyDataConAbs #-}

-- Returns a representation type (type of an TypeCon-typed Newtype payload)
-- given a list of instantiated DataConDefs.
dataDefRep :: [DataConDef n] -> Type r n
dataDefRep = \case
  [] -> error "unreachable"  -- There's no representation for a void type
  [DataConDef _ ty _] -> unsafeCoerceIRE ty
  tys -> SumTy $ tys <&> \(DataConDef _ ty _) -> unsafeCoerceIRE ty

instantiateDepPairTy :: EnvReader m => DepPairType r n -> Atom r n -> m n (Type r n)
instantiateDepPairTy (DepPairType b rhsTy) x = applyAbs (Abs b rhsTy) (SubstVal x)
{-# INLINE instantiateDepPairTy #-}

projType :: EnvReader m => Projection -> Type r n -> Atom r n -> m n (Type r n)
projType i ty x = case ty of
  ProdTy xs -> return $ xs !! iProj
  DepPairTy t | iProj == 0 -> return $ depPairLeftTy t
  DepPairTy t | iProj == 1 -> do
    xFst <- normalizeProj (ProjectProduct 0) x
    instantiateDepPairTy t xFst
  _ | isNewtype ty -> projectNewtype ty
  Var v -> error $ "Tried to project value of unreduced type " <> pprint (Var v)
  _ -> error $ "Only single-member ADTs and record types can be projected. Got " <> pprint ty
  where
    iProj = case i of
      ProjectProduct i' -> i'
      _ -> error "Not a product projection"

isNewtype :: Type r n -> Bool
isNewtype ty = case ty of
  TC Nat        -> True
  TC (Fin _)    -> True
  TypeCon _ _ _ -> True
  RecordTy _    -> True
  VariantTy _   -> True
  _ -> False

-- === SubstE/SubstB instances ===
-- These live here, as orphan instances, because we normalize as we substitute.

instance SubstE (AtomSubstVal r) (Atom r) where
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
    Case5 rest -> (toE . Case5) $ substE (env, subst) rest
    Case6 rest -> (toE . Case6) $ substE (env, subst) rest
    Case7 rest -> (toE . Case7) $ substE (env, subst) rest

instance SubstE (AtomSubstVal r) (EffectRowP Name) where
  substE env (EffectRow effs tailVar) = do
    let effs' = S.fromList $ map (substE env) (S.toList effs)
    let tailEffRow = case tailVar of
          Nothing -> EffectRow mempty Nothing
          Just v -> case snd env ! v of
            Rename        v'  -> EffectRow mempty (Just v')
            SubstVal (Var v') -> EffectRow mempty (Just v')
            SubstVal (Eff r)  -> r
            _ -> error "Not a valid effect substitution"
    extendEffRow effs' tailEffRow

instance SubstE (AtomSubstVal r) (EffectP Name) where
  substE (_, env) eff = case eff of
    RWSEffect rws Nothing -> RWSEffect rws Nothing
    RWSEffect rws (Just v) -> do
      let v' = case env ! v of
                 Rename   v''           -> Just v''
                 SubstVal (Con HeapVal) -> Nothing
                 SubstVal (Var v'')     -> Just v''
                 SubstVal _ -> error "Heap parameter must be a name"
      RWSEffect rws v'
    ExceptionEffect -> ExceptionEffect
    IOEffect        -> IOEffect
    UserEffect v    ->
      case env ! v of
        Rename v' -> UserEffect v'
        -- other cases are proven unreachable by type system
        -- v' is an EffectNameC but other cases apply only to
        -- AtomNameC
    InitEffect -> InitEffect

instance SubstE (AtomSubstVal CoreIR) SpecializationSpec where
  substE env (AppSpecialization f ab) = do
    let f' = case snd env ! f of
               Rename v -> v
               SubstVal (Var v) -> v
               _ -> error "bad substitution"
    AppSpecialization f' (substE env ab)

instance SubstE (AtomSubstVal r) (ExtLabeledItemsE (Atom r) (AtomName r)) where
  substE (scope, env) (ExtLabeledItemsE (Ext items maybeExt)) = do
    let items' = fmap (substE (scope, env)) items
    let ext = case maybeExt of
                Nothing -> NoExt NoLabeledItems
                Just v -> case env ! v of
                  Rename        v'  -> Ext NoLabeledItems $ Just v'
                  SubstVal (Var v') -> Ext NoLabeledItems $ Just v'
                  SubstVal (LabeledRow row) -> case fieldRowElemsAsExtRow row of
                    Just row' -> row'
                    Nothing -> error "Not implemented: unrepresentable subst of ExtLabeledItems"
                  _ -> error "Not a valid labeled row substitution"
    ExtLabeledItemsE $ prefixExtLabeledItems items' ext

instance SubstE (AtomSubstVal r) (FieldRowElems r) where
  substE :: forall i o. Distinct o => (Env o, Subst (AtomSubstVal r) i o) -> FieldRowElems r i -> FieldRowElems r o
  substE env (UnsafeFieldRowElems els) = fieldRowElemsFromList $ foldMap substItem els
    where
      substItem = \case
        DynField v ty -> case snd env ! v of
          SubstVal (Con (LabelCon l)) -> [StaticFields $ labeledSingleton l ty']
          SubstVal (Var v') -> [DynField v' ty']
          Rename v'         -> [DynField v' ty']
          _ -> error "ill-typed substitution"
          where ty' = substE env ty
        DynFields v -> case snd env ! v of
          SubstVal (LabeledRow items) -> fromFieldRowElems items
          SubstVal (Var v') -> [DynFields v']
          Rename v'         -> [DynFields v']
          _ -> error "ill-typed substitution"
        StaticFields items -> [StaticFields items']
          where ExtLabeledItemsE (NoExt items') = substE env
                  (ExtLabeledItemsE (NoExt items) :: ExtLabeledItemsE (Atom r) (AtomName r) i)

instance SubstE (AtomSubstVal CoreIR) EffectDef
instance SubstE (AtomSubstVal CoreIR) EffectOpType
instance SubstE (AtomSubstVal r) IExpr
instance SubstE (AtomSubstVal r) (RepVal r)
instance SubstE (AtomSubstVal r) (DataDefParams r)
instance SubstE (AtomSubstVal CoreIR) DataDef
instance SubstE (AtomSubstVal CoreIR) DataConDef
instance SubstE (AtomSubstVal r) (BaseMonoid r)
instance SubstE (AtomSubstVal r) (UserEffectOp r)
instance SubstE (AtomSubstVal r) (DAMOp r)
instance SubstE (AtomSubstVal r) (Hof r)
instance SubstE (AtomSubstVal r) (RefOp r)
instance SubstE (AtomSubstVal r) (Expr r)
instance SubstE (AtomSubstVal r) (Block r)
instance SubstE (AtomSubstVal CoreIR) InstanceDef
instance SubstE (AtomSubstVal CoreIR) InstanceBody
instance SubstE (AtomSubstVal CoreIR) MethodType
instance SubstE (AtomSubstVal r) (DictType r)
instance SubstE (AtomSubstVal r) (DictExpr r)
instance SubstE (AtomSubstVal r) (LamBinding r)
instance SubstE (AtomSubstVal r) (LamExpr r)
instance SubstE (AtomSubstVal r) (TabLamExpr r)
instance SubstE (AtomSubstVal r) (PiBinding r)
instance SubstB (AtomSubstVal r) (PiBinder r)
instance SubstE (AtomSubstVal r) (PiType r)
instance SubstB (AtomSubstVal r) (RolePiBinder r)
instance SubstE (AtomSubstVal r) (IxType r)
instance SubstE (AtomSubstVal r) (TabPiType r)
instance SubstE (AtomSubstVal r) (NaryPiType r)
instance SubstE (AtomSubstVal r) (DepPairType r)
instance SubstE (AtomSubstVal r) (SolverBinding r)
instance SubstE (AtomSubstVal r) (DeclBinding r)
instance SubstB (AtomSubstVal r) (Decl r)

-- XXX: we need a special instance here because `SuperclassBinder` have all
-- their types at the level of the top binder, rather than interleaving them
-- with the binders. We should make a `BindersNest` type for that pattern
-- instead.
instance SubstB (AtomSubstVal CoreIR) (SuperclassBinders) where
  substB envSubst (SuperclassBinders bsTop tsTop) contTop = do
    let tsTop' = map (substE envSubst) tsTop
    go envSubst bsTop tsTop' \envSubst' bsTop' -> contTop envSubst' $ SuperclassBinders bsTop' tsTop'
    where
      go :: (Distinct o, FromName v, SinkableV v)
         => (Env o, Subst v i o)
         -> Nest AtomNameBinder i i' -> [Type CoreIR o]
         -> (forall o'. Distinct o' => (Env o', Subst v i' o') -> Nest (AtomNameBinder) o o' -> a)
         -> a
      go (env, subst) Empty [] cont = cont (env, subst) Empty
      go (env, subst) (Nest b bs) (t:ts) cont = do
        withFresh (getNameHint b) (toScope env) \b' -> do
          let env' = env `extendOutMap` toEnvFrag (b':>t)
          let subst' = sink subst <>> b @> (fromName $ binderName b')
          go (env', subst') bs (map sink ts) \envSubst'' bs' -> cont envSubst'' (Nest b' bs')
      go _ _ _ _ = error "zip error"
