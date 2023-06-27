-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module CheapReduction
  ( CheaplyReducibleE (..), cheapReduce, cheapReduceWithDecls, cheapNormalize
  , normalizeProj, asNaryProj, normalizeNaryProj
  , depPairLeftTy, instantiateTyConDef
  , dataDefRep, unwrapNewtypeType, repValAtom
  , unwrapLeadingNewtypesType, wrapNewtypesData, liftSimpAtom, liftSimpType
  , liftSimpFun, makeStructRepVal, NonAtomRenamer (..), Visitor (..), VisitGeneric (..)
  , visitAtomPartial, visitTypePartial, visitAtomDefault, visitTypeDefault, Visitor2
  , visitBinders, visitPiDefault, visitAlt, toAtomVar, instantiate, withInstantiated
  , bindersToVars, bindersToAtoms, instantiateNames, withInstantiatedNames, assumeConst)
  where

import Control.Applicative
import Control.Monad.Trans
import Control.Monad.Writer.Strict  hiding (Alt)
import Control.Monad.State.Strict
import Control.Monad.Reader
import Data.Foldable (toList)
import Data.Functor.Identity
import Data.Functor ((<&>))
import qualified Data.List.NonEmpty    as NE
import qualified Data.Map.Strict as M

import Subst
import Core
import Err
import IRVariants
import MTL1
import Name
import PPrint ()
import QueryTypePure
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
            => e n -> m n (Maybe (e' n))
cheapReduce e = liftCheapReducerM idSubst $ cheapReduceE e
{-# INLINE cheapReduce #-}
{-# SCC cheapReduce #-}

cheapReduceWithDecls
  :: forall r e' e m n l
   . ( CheaplyReducibleE r e e', NiceE r e', NiceE r e, EnvReader m )
  => Nest (Decl r) n l -> e l -> m n (Maybe (e' n))
cheapReduceWithDecls decls result = do
  Abs decls' result' <- sinkM $ Abs decls result
  liftCheapReducerM idSubst $
    cheapReduceWithDeclsB decls' $
      cheapReduceE result'
{-# INLINE cheapReduceWithDecls #-}
{-# SCC cheapReduceWithDecls #-}

cheapNormalize :: (EnvReader m, CheaplyReducibleE r e e, NiceE r e) => e n -> m n (e n)
cheapNormalize a = cheapReduce a >>= \case
  Just ans -> return ans
  _ -> error "couldn't normalize expression"
{-# INLINE cheapNormalize #-}

-- === internal ===

newtype CheapReducerM (r::IR) (i :: S) (o :: S) (a :: *) =
  CheapReducerM
    (SubstReaderT AtomSubstVal
      (MaybeT1
        (ScopedT1 (MapE (AtomName r) (MaybeE (Atom r)))
          (EnvReaderT Identity))) i o a)
  deriving (Functor, Applicative, Monad, Alternative)

deriving instance IRRep r => ScopeReader (CheapReducerM r i)
deriving instance IRRep r => EnvReader (CheapReducerM r i)
deriving instance IRRep r => EnvExtender (CheapReducerM r i)
deriving instance IRRep r => SubstReader AtomSubstVal (CheapReducerM r)

class ( Alternative2 m, SubstReader AtomSubstVal m
      , EnvReader2 m, EnvExtender2 m) => CheapReducer m r | m -> r where
  updateCache :: AtomName r o -> Maybe (Atom r o) -> m i o ()
  lookupCache :: AtomName r o -> m i o (Maybe (Maybe (Atom r o)))

instance IRRep r => CheapReducer (CheapReducerM r) r where
  updateCache v u = CheapReducerM $ SubstReaderT $ lift $ lift11 $
    modify (MapE . M.insert v (toMaybeE u) . fromMapE)
  lookupCache v = CheapReducerM $ SubstReaderT $ lift $ lift11 $
    fmap fromMaybeE <$> gets (M.lookup v . fromMapE)

liftCheapReducerM
  :: (EnvReader m, IRRep r)
  => Subst AtomSubstVal i o -> CheapReducerM r i o a
  -> m o (Maybe a)
liftCheapReducerM subst (CheapReducerM m) = do
  liftM runIdentity $ liftEnvReaderT $ runScopedT1
    (runMaybeT1 $ runSubstReaderT subst m) mempty
{-# INLINE liftCheapReducerM #-}

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
  Nest (Let b binding@(DeclBinding _ expr)) rest -> do
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
  LetBound (DeclBinding _ e) -> do
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
    Lam _ -> substM a
    DictHole ctx ty' access -> do
      ty <- cheapReduceE ty'
      runFallibleT1 (trySynthTerm ty access) >>= \case
        Success d -> return d
        Failure _ -> return $ DictHole ctx ty access
    -- We traverse the Atom constructors that might contain lambda expressions
    -- explicitly, to make sure that we can skip normalizing free vars inside those.
    Con con -> Con <$> traverseOp con cheapReduceE cheapReduceE (error "unexpected lambda")
    DictCon t d -> do
      t' <- cheapReduceE t
      cheapReduceDictExpr t' d
    SimpInCore (LiftSimp t x) -> do
      t' <- cheapReduceE t
      x' <- substM x
      liftSimpAtom t' x'
    -- These two are a special-case hack. TODO(dougalm): write a traversal over
    -- the NewtypeTyCon (or types generally)
    NewtypeCon NatCon n -> NewtypeCon NatCon <$> cheapReduceE n
    -- Do recursive reduction via substitution
    -- TODO: we don't collect the dict holes here, so there's a danger of
    -- dropping them if they turn out to be phantom.
    _ -> do
      a' <- substM a
      dropSubst $ traverseNames cheapReduceName a'

instance IRRep r => CheaplyReducibleE r (Type r) (Type r) where
  cheapReduceE :: forall i o. Type r i -> CheapReducerM r i o (Type r o)
  cheapReduceE a = case a of
    -- Don't try to eagerly reduce lambda bodies. We might get stuck long before
    -- we have a chance to apply tham. Also, recursive traversal of those bodies
    -- means that we will follow the full call chain, so it's really expensive!
    -- TODO: we don't collect the dict holes here, so there's a danger of
    -- dropping them if they turn out to be phantom.
    TabPi (TabPiType d (b:>t) resultTy) -> do
      t' <- cheapReduceE t
      d' <- cheapReduceE d
      withFreshBinder (getNameHint b) t' \b' -> do
        resultTy' <- extendSubst (b@>Rename (binderName b')) $ cheapReduceE resultTy
        return $ TabPi $ TabPiType d' b' resultTy'
    -- We traverse the Atom constructors that might contain lambda expressions
    -- explicitly, to make sure that we can skip normalizing free vars inside those.
    NewtypeTyCon (Fin n) -> NewtypeTyCon . Fin <$> cheapReduceE n
    -- Do recursive reduction via substitution
    -- TODO: we don't collect the dict holes here, so there's a danger of
    -- dropping them if they turn out to be phantom.
    _ -> do
      a' <- substM a
      dropSubst $ traverseNames cheapReduceName a'

cheapReduceDictExpr :: CType o -> DictExpr i -> CheapReducerM CoreIR i o (CAtom o)
cheapReduceDictExpr resultTy d = case d of
  SuperclassProj child superclassIx -> do
    cheapReduceE child >>= \case
      DictCon _ (InstanceDict instanceName args) -> dropSubst do
        args' <- mapM cheapReduceE args
        InstanceDef _ _ bs _ body <- lookupInstanceDef instanceName
        let InstanceBody superclasses _ = body
        instantiate (Abs bs (superclasses !! superclassIx)) args'
      child' -> return $ DictCon resultTy $ SuperclassProj child' superclassIx
  InstantiatedGiven f xs ->
    reduceApp <|> justSubst
    where reduceApp = do
            f' <- cheapReduceE f
            xs' <- mapM cheapReduceE (toList xs)
            cheapReduceApp f' xs'
  InstanceDict _ _ -> justSubst
  IxFin _          -> justSubst
  DataData ty      -> DictCon resultTy . DataData <$> cheapReduceE ty
  where justSubst = DictCon resultTy <$> substM d

instance CheaplyReducibleE CoreIR TyConParams TyConParams where
  cheapReduceE (TyConParams infs ps) =
    TyConParams infs <$> mapM cheapReduceE ps

instance (CheaplyReducibleE r e e', NiceE r e') => CheaplyReducibleE r (Abs (Nest (Decl r)) e) e' where
  cheapReduceE (Abs decls result) = cheapReduceWithDeclsB decls $ cheapReduceE result

instance IRRep r => CheaplyReducibleE r (Expr r) (Atom r) where
  cheapReduceE expr = confuseGHC >>= \_ -> case expr of
    Atom atom -> cheapReduceE atom
    App _ f' xs' -> do
      xs <- mapM cheapReduceE xs'
      f <- cheapReduceE f'
      cheapReduceApp f xs
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
    ApplyMethod _ dict i explicitArgs -> do
      explicitArgs' <- mapM cheapReduceE explicitArgs
      cheapReduceE dict >>= \case
        DictCon _ (InstanceDict instanceName args) -> dropSubst do
          args' <- mapM cheapReduceE args
          def <- lookupInstanceDef instanceName
          withInstantiated def args' \(PairE _ (InstanceBody _ methods)) -> do
            method' <- cheapReduceE $ methods !! i
            cheapReduceApp method' explicitArgs'
        _ -> empty
    _ -> empty

cheapReduceApp :: CAtom o -> [CAtom o] -> CheapReducerM CoreIR i o (CAtom o)
cheapReduceApp f xs = case f of
  Lam lam -> dropSubst $ withInstantiated lam xs \body -> cheapReduceE body
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

-- XXX: TODO: figure out exactly what our normalization invariants are. We
-- shouldn't have to choose `normalizeProj` or `asNaryProj` on a
-- case-by-case basis. This is here for now because it makes it easier to switch
-- to the new version of `ProjectElt`.
asNaryProj :: IRRep r => Projection -> Atom r n -> (NE.NonEmpty Projection, AtomVar r n)
asNaryProj p (Var v) = (p NE.:| [], v)
asNaryProj p1 (ProjectElt _ p2 x) = do
  let (p2' NE.:| ps, v) = asNaryProj p2 x
  (p1 NE.:| (p2':ps), v)
asNaryProj p x = error $ "Can't normalize projection: " ++ pprint p ++ " " ++ pprint x

-- assumes the atom is already normalized
normalizeNaryProj :: IRRep r => EnvReader m => [Projection] -> Atom r n -> m n (Atom r n)
normalizeNaryProj [] x = return x
normalizeNaryProj (i:is) x = normalizeProj i =<< normalizeNaryProj is x

-- assumes the atom itself is already normalized
normalizeProj :: IRRep r => EnvReader m => Projection -> Atom r n -> m n (Atom r n)
normalizeProj UnwrapNewtype atom = case atom of
  NewtypeCon  _ x -> return x
  SimpInCore (LiftSimp (NewtypeTyCon t) x) -> do
    t' <- snd <$> unwrapNewtypeType t
    return $ SimpInCore $ LiftSimp t' x
  x -> case getType x of
    NewtypeTyCon t -> do
      t' <- snd <$> unwrapNewtypeType t
      return $ ProjectElt t' UnwrapNewtype x
    _ -> error "expected a newtype"
normalizeProj (ProjectProduct i) atom = case atom of
  Con (ProdCon xs) -> return $ xs !! i
  DepPair l _ _ | i == 0 -> return l
  DepPair _ r _ | i == 1 -> return r
  SimpInCore (LiftSimp _ x) -> do
    x' <- normalizeProj (ProjectProduct i) x
    resultTy <- getResultTy
    return $ SimpInCore $ LiftSimp resultTy x'
  RepValAtom (RepVal _ tree) -> case tree of
    Branch trees -> do
      resultTy <- getResultTy
      repValAtom $ RepVal resultTy (trees!!i)
    Leaf _ -> error "unexpected leaf"
  _ -> do
    resultTy <- getResultTy
    return $ ProjectElt resultTy (ProjectProduct i) atom
  where
    getResultTy = projType i (getType atom) atom
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
  ProjectElt _ _ _ -> justLift
  RepValAtom _   -> justLift -- TODO(dougalm): should we make more effort to pull out products etc?
  _ -> do
    (cons , ty') <- unwrapLeadingNewtypesType ty
    atom <- case (ty', simpAtom) of
      (BaseTy _  , Con (Lit v))      -> return $ Con $ Lit v
      (ProdTy tys, Con (ProdCon xs))   -> Con . ProdCon <$> zipWithM rec tys xs
      (SumTy  tys, Con (SumCon _ i x)) -> Con . SumCon tys i <$> rec (tys!!i) x
      (DepPairTy dpt@(DepPairType _ (b:>t1) t2), DepPair x1 x2 _) -> do
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

-- TODO: These used to live in QueryType. Think about a better way to organize
-- them. Maybe a common set of low-level type-querying utils that both
-- CheapReduction and QueryType import?

depPairLeftTy :: DepPairType r n -> Type r n
depPairLeftTy (DepPairType _ (_:>ty) _) = ty
{-# INLINE depPairLeftTy #-}

unwrapNewtypeType :: EnvReader m => NewtypeTyCon n -> m n (NewtypeCon n, Type CoreIR n)
unwrapNewtypeType = \case
  Nat                   -> return (NatCon, IdxRepTy)
  Fin n                 -> return (FinCon n, NatTy)
  UserADTType sn defName params -> do
    def <- lookupTyCon defName
    ty' <- dataDefRep <$> instantiateTyConDef def params
    return (UserADTData sn defName params, ty')
  ty -> error $ "Shouldn't be projecting: " ++ pprint ty
{-# INLINE unwrapNewtypeType #-}

projType :: (IRRep r, EnvReader m) => Int -> Type r n -> Atom r n -> m n (Type r n)
projType i ty x = case ty of
  ProdTy xs -> return $ xs !! i
  DepPairTy t | i == 0 -> return $ depPairLeftTy t
  DepPairTy t | i == 1 -> do
    xFst <- normalizeProj (ProjectProduct 0) x
    instantiate t [xFst]
  _ -> error $ "Can't project type: " ++ pprint ty

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

instantiateTyConDef :: EnvReader m => TyConDef n -> TyConParams n -> m n (DataConDefs n)
instantiateTyConDef (TyConDef _ _ bs conDefs) (TyConParams _ xs) = do
  applySubst (bs @@> (SubstVal <$> xs)) conDefs
{-# INLINE instantiateTyConDef #-}

assumeConst
  :: (IRRep r, HoistableE body, SinkableE body, ToBindersAbs e body r) => e n -> body n
assumeConst e = case toAbs e of Abs bs body -> ignoreHoistFailure $ hoist bs body

instantiate
  :: (EnvReader m, IRRep r, SubstE (SubstVal Atom) body, SinkableE body, ToBindersAbs e body r)
  => e n -> [Atom r n] -> m n (body n)
instantiate e xs = case toAbs e of
  Abs bs body -> applySubst (bs @@> (SubstVal <$> xs)) body

-- "lazy" subst-extending version of `instantiate`
withInstantiated
  :: (SubstReader AtomSubstVal m, IRRep r, SubstE (SubstVal Atom) body, SinkableE body, ToBindersAbs e body r)
  => e i -> [Atom r o]
  -> (forall i'. body i' -> m i' o a)
  -> m i o a
withInstantiated e xs cont = case toAbs e of
  Abs bs body -> extendSubst (bs @@> (SubstVal <$> xs)) $ cont body

instantiateNames
  :: (EnvReader m, IRRep r, RenameE body, SinkableE body, ToBindersAbs e body r)
  => e n -> [AtomName r n] -> m n (body n)
instantiateNames e vs = case toAbs e of
  Abs bs body -> applyRename (bs @@> vs) body

-- "lazy" subst-extending version of `instantiateNames`
withInstantiatedNames
  :: (SubstReader Name m, IRRep r, RenameE body, SinkableE body, ToBindersAbs e body r)
  => e i -> [AtomName r o]
  -> (forall i'. body i' -> m i' o a)
  -> m i o a
withInstantiatedNames e vs cont = case toAbs e of
  Abs bs body -> extendRenamer (bs @@> vs) $ cont body

-- Returns a representation type (type of an TypeCon-typed Newtype payload)
-- given a list of instantiated DataConDefs.
dataDefRep :: DataConDefs n -> CType n
dataDefRep (ADTCons cons) = case cons of
  [] -> error "unreachable"  -- There's no representation for a void type
  [DataConDef _ _ ty _] -> ty
  tys -> SumTy $ tys <&> \(DataConDef _ _ ty _) -> ty
dataDefRep (StructFields fields) = case map snd fields of
  [ty] -> ty
  tys  -> ProdTy tys

makeStructRepVal :: (Fallible1 m, EnvReader m) => TyConName n -> [CAtom n] -> m n (CAtom n)
makeStructRepVal tyConName args = do
  TyConDef _ _ _ (StructFields fields) <- lookupTyCon tyConName
  case fields of
    [_] -> case args of
      [arg] -> return arg
      _ -> error "wrong number of args"
    _ -> return $ ProdVal args

-- === traversable terms ===

class Monad m => NonAtomRenamer m i o | m -> i, m -> o where
  renameN :: (IsAtomName c ~ False, Color c) => Name c i -> m (Name c o)

class NonAtomRenamer m i o => Visitor m r i o | m -> i, m -> o where
  visitType :: Type r i -> m (Type r o)
  visitAtom :: Atom r i -> m (Atom r o)
  visitLam  :: LamExpr r i -> m (LamExpr r o)
  visitPi   :: PiType  r i -> m (PiType  r o)

class VisitGeneric (e:: E) (r::IR) | e -> r where
  visitGeneric :: Visitor m r i o => e i -> m (e o)

type Visitor2 (m::MonadKind2) r = forall i o . Visitor (m i o) r i o

instance VisitGeneric (Atom    r) r where visitGeneric = visitAtom
instance VisitGeneric (Type    r) r where visitGeneric = visitType
instance VisitGeneric (LamExpr r) r where visitGeneric = visitLam
instance VisitGeneric (PiType  r) r where visitGeneric = visitPi

visitBlock :: Visitor m r i o => Block r i -> m (Block r o)
visitBlock b = visitGeneric (LamExpr Empty b) >>= \case
  LamExpr Empty b' -> return b'
  _ -> error "not a block"

visitAlt :: Visitor m r i o => Alt r i -> m (Alt r o)
visitAlt (Abs b body) = do
  visitGeneric (LamExpr (UnaryNest b) body) >>= \case
    LamExpr (UnaryNest b') body' -> return $ Abs b' body'
    _ -> error "not an alt"

traverseOpTerm
  :: (GenericOp e, Visitor m r i o, OpConst e r ~ OpConst e r)
  => e r i -> m (e r o)
traverseOpTerm e = traverseOp e visitGeneric visitGeneric visitGeneric

visitAtomDefault
  :: (IRRep r, Visitor (m i o) r i o, AtomSubstReader v m, EnvReader2 m)
  => Atom r i -> m i o (Atom r o)
visitAtomDefault atom = case atom of
  Var _          -> atomSubstM atom
  SimpInCore _   -> atomSubstM atom
  ProjectElt t i x -> ProjectElt <$> visitType t <*> pure i <*> visitGeneric x
  _ -> visitAtomPartial atom

visitTypeDefault
  :: (IRRep r, Visitor (m i o) r i o, AtomSubstReader v m, EnvReader2 m)
  => Type r i -> m i o (Type r o)
visitTypeDefault = \case
  TyVar v          -> atomSubstM $ TyVar v
  ProjectEltTy t i x -> ProjectEltTy <$> visitType t <*> pure i <*> visitGeneric x
  x -> visitTypePartial x

visitPiDefault
  :: (Visitor2 m r, IRRep r, FromName v, AtomSubstReader v m, EnvExtender2 m)
  => PiType r i -> m i o (PiType r o)
visitPiDefault (PiType bs effty) = do
  visitBinders bs \bs' -> do
    effty' <- visitGeneric effty
    return $ PiType bs' effty'

visitBinders
  :: (Visitor2 m r, IRRep r, FromName v, AtomSubstReader v m, EnvExtender2 m)
  => Nest (Binder r) i i'
  -> (forall o'. DExt o o' => Nest (Binder r) o o' -> m i' o' a)
  -> m i o a
visitBinders Empty cont = getDistinct >>= \Distinct -> cont Empty
visitBinders (Nest (b:>ty) bs) cont = do
  ty' <- visitType ty
  withFreshBinder (getNameHint b) ty' \b' -> do
    extendRenamer (b@>binderName b') do
      visitBinders bs \bs' ->
        cont $ Nest b' bs'

-- XXX: This doesn't handle the `Var`, `ProjectElt`, `SimpInCore` cases. These
-- should be handled explicitly beforehand. TODO: split out these cases under a
-- separate constructor, perhaps even a `hole` paremeter to `Atom` or part of
-- `IR`.
visitAtomPartial :: (IRRep r, Visitor m r i o) => Atom r i -> m (Atom r o)
visitAtomPartial = \case
  Var _          -> error "Not handled generically"
  SimpInCore _   -> error "Not handled generically"
  ProjectElt _ _ _ -> error "Not handled generically"
  Con con -> Con <$> visitGeneric con
  PtrVar t v -> PtrVar t <$> renameN v
  DepPair x y t -> do
    x' <- visitGeneric x
    y' <- visitGeneric y
    ~(DepPairTy t') <- visitGeneric $ DepPairTy t
    return $ DepPair x' y' t'
  Lam lam   -> Lam     <$> visitGeneric lam
  Eff eff   -> Eff     <$> visitGeneric eff
  DictCon t d -> DictCon <$> visitType t <*> visitGeneric d
  NewtypeCon con x -> NewtypeCon <$> visitGeneric con <*> visitGeneric x
  DictHole ctx ty access -> DictHole ctx <$> visitGeneric ty <*> pure access
  TypeAsAtom t -> TypeAsAtom <$> visitGeneric t
  RepValAtom repVal -> RepValAtom <$> visitGeneric repVal

-- XXX: This doesn't handle the `TyVar` or `ProjectEltTy` cases. These should be
-- handled explicitly beforehand.
visitTypePartial :: (IRRep r, Visitor m r i o) => Type r i -> m (Type r o)
visitTypePartial = \case
  TyVar _          -> error "Not handled generically"
  ProjectEltTy _ _ _ -> error "Not handled generically"
  NewtypeTyCon t -> NewtypeTyCon <$> visitGeneric t
  Pi           t -> Pi           <$> visitGeneric t
  TabPi        t -> TabPi        <$> visitGeneric t
  TC           t -> TC           <$> visitGeneric t
  DepPairTy    t -> DepPairTy    <$> visitGeneric t
  DictTy       t -> DictTy       <$> visitGeneric t

instance IRRep r => VisitGeneric (Expr r) r where
  visitGeneric = \case
    TopApp et v xs -> TopApp <$> visitGeneric et <*> renameN v <*> mapM visitGeneric xs
    TabApp t tab xs -> TabApp <$> visitType t <*> visitGeneric tab <*> mapM visitGeneric xs
    -- TODO: should we reuse the original effects? Whether it's valid depends on
    -- the type-preservation requirements for a visitor. We should clarify what
    -- those are.
    Case x alts effTy -> do
      x' <- visitGeneric x
      alts' <- mapM visitAlt alts
      effTy' <- visitGeneric effTy
      return $ Case x' alts' effTy'
    Atom x -> Atom <$> visitGeneric x
    TabCon Nothing t xs -> TabCon Nothing <$> visitGeneric t <*> mapM visitGeneric xs
    TabCon (Just (WhenIRE d)) t xs -> TabCon <$> (Just . WhenIRE <$> visitGeneric d) <*> visitGeneric t <*> mapM visitGeneric xs
    PrimOp op -> PrimOp <$> visitGeneric op
    App et fAtom xs -> App <$> visitGeneric et <*> visitGeneric fAtom <*> mapM visitGeneric xs
    ApplyMethod et m i xs -> ApplyMethod <$> visitGeneric et <*> visitGeneric m <*> pure i <*> mapM visitGeneric xs

instance IRRep r => VisitGeneric (PrimOp r) r where
  visitGeneric = \case
    UnOp     op x   -> UnOp  op <$> visitGeneric x
    BinOp    op x y -> BinOp op <$> visitGeneric x <*> visitGeneric y
    MemOp        op -> MemOp    <$> visitGeneric op
    VectorOp     op -> VectorOp     <$> visitGeneric op
    MiscOp       op -> MiscOp       <$> visitGeneric op
    Hof          op -> Hof          <$> visitGeneric op
    DAMOp        op -> DAMOp        <$> visitGeneric op
    RefOp r op  -> RefOp <$> visitGeneric r <*> traverseOp op visitGeneric visitGeneric visitGeneric

instance IRRep r => VisitGeneric (TypedHof r) r where
  visitGeneric (TypedHof eff hof) = TypedHof <$> visitGeneric eff <*> visitGeneric hof

instance IRRep r => VisitGeneric (Hof r) r where
  visitGeneric = \case
    For ann d lam -> For ann <$> visitGeneric d <*> visitGeneric lam
    RunReader x body -> RunReader <$> visitGeneric x <*> visitGeneric body
    RunWriter dest bm body -> RunWriter <$> mapM visitGeneric dest <*> visitGeneric bm <*> visitGeneric body
    RunState  dest s body ->  RunState  <$> mapM visitGeneric dest <*> visitGeneric s <*> visitGeneric body
    While          b -> While          <$> visitBlock b
    RunIO          b -> RunIO          <$> visitBlock b
    RunInit        b -> RunInit        <$> visitBlock b
    CatchException t b -> CatchException <$> visitType t <*> visitBlock b
    Linearize      lam x -> Linearize <$> visitGeneric lam <*> visitGeneric x
    Transpose      lam x -> Transpose <$> visitGeneric lam <*> visitGeneric x

instance IRRep r => VisitGeneric (BaseMonoid r) r where
  visitGeneric (BaseMonoid x lam) = BaseMonoid <$> visitGeneric x <*> visitGeneric lam

instance IRRep r => VisitGeneric (DAMOp r) r where
  visitGeneric = \case
    Seq eff dir d x lam -> Seq <$> visitGeneric eff <*> pure dir <*> visitGeneric d <*> visitGeneric x <*> visitGeneric lam
    RememberDest eff x lam -> RememberDest <$> visitGeneric eff <*> visitGeneric x <*> visitGeneric lam
    AllocDest t -> AllocDest <$> visitGeneric t
    Place x y -> Place  <$> visitGeneric x <*> visitGeneric y
    Freeze x  -> Freeze <$> visitGeneric x

instance IRRep r => VisitGeneric (Effect r) r where
  visitGeneric = \case
    RWSEffect rws h    -> RWSEffect rws <$> visitGeneric h
    ExceptionEffect    -> pure ExceptionEffect
    IOEffect           -> pure IOEffect
    InitEffect         -> pure InitEffect

instance IRRep r => VisitGeneric (EffectRow r) r where
  visitGeneric (EffectRow effs tailVar) = do
    effs' <- eSetFromList <$> mapM visitGeneric (eSetToList effs)
    tailEffRow <- case tailVar of
      NoTail -> return $ EffectRow mempty NoTail
      EffectRowTail v -> visitGeneric (Var v) <&> \case
        Var v' -> EffectRow mempty (EffectRowTail v')
        Eff r  -> r
        _ -> error "Not a valid effect substitution"
    return $ extendEffRow effs' tailEffRow

instance VisitGeneric DictExpr CoreIR where
  visitGeneric = \case
    InstantiatedGiven x xs -> InstantiatedGiven <$> visitGeneric x <*> mapM visitGeneric xs
    SuperclassProj x i     -> SuperclassProj <$> visitGeneric x <*> pure i
    InstanceDict v xs      -> InstanceDict <$> renameN v <*> mapM visitGeneric xs
    IxFin x                -> IxFin <$> visitGeneric x
    DataData t             -> DataData <$> visitGeneric t

instance VisitGeneric NewtypeCon CoreIR where
  visitGeneric = \case
    UserADTData sn t params -> UserADTData sn <$> renameN t <*> visitGeneric params
    NatCon -> return NatCon
    FinCon x -> FinCon <$> visitGeneric x

instance VisitGeneric NewtypeTyCon CoreIR where
  visitGeneric = \case
    Nat -> return Nat
    Fin x -> Fin <$> visitGeneric x
    EffectRowKind -> return EffectRowKind
    UserADTType n v params -> UserADTType n <$> renameN v <*> visitGeneric params

instance VisitGeneric TyConParams CoreIR where
  visitGeneric (TyConParams expls xs) = TyConParams expls <$> mapM visitGeneric xs

instance IRRep r => VisitGeneric (IxDict r) r where
  visitGeneric = \case
    IxDictAtom   x -> IxDictAtom   <$> visitGeneric x
    IxDictRawFin x -> IxDictRawFin <$> visitGeneric x
    IxDictSpecialized t v xs -> IxDictSpecialized <$> visitGeneric t <*> renameN v <*> mapM visitGeneric xs

instance IRRep r => VisitGeneric (IxType r) r where
  visitGeneric (IxType t d) = IxType <$> visitType t <*> visitGeneric d

instance VisitGeneric DictType CoreIR where
  visitGeneric (DictType n v xs) = DictType n <$> renameN v <*> mapM visitGeneric xs

instance VisitGeneric CoreLamExpr CoreIR where
  visitGeneric (CoreLamExpr t lam) = CoreLamExpr <$> visitGeneric t <*> visitGeneric lam

instance VisitGeneric CorePiType CoreIR where
  visitGeneric (CorePiType app expl bs effty) = do
    PiType bs' effty' <- visitGeneric $ PiType bs effty
    return $ CorePiType app expl bs' effty'

instance IRRep r => VisitGeneric (TabPiType r) r where
  visitGeneric (TabPiType d b eltTy) = do
    d' <- visitGeneric d
    visitGeneric (PiType (UnaryNest b) (EffTy Pure eltTy)) <&> \case
      PiType (UnaryNest b') (EffTy Pure eltTy') -> TabPiType d' b' eltTy'
      _ -> error "not a table pi type"

instance IRRep r => VisitGeneric (DepPairType r) r where
  visitGeneric (DepPairType expl b ty) = do
    visitGeneric (PiType (UnaryNest b) (EffTy Pure ty)) <&> \case
      PiType (UnaryNest b') (EffTy Pure ty') -> DepPairType expl b' ty'
      _ -> error "not a dependent pair type"

instance VisitGeneric (RepVal SimpIR) SimpIR where
  visitGeneric (RepVal ty tree) = RepVal <$> visitGeneric ty <*> mapM renameIExpr tree
    where renameIExpr = \case
            ILit l -> return $ ILit l
            IVar    v t -> IVar    <$> renameN v <*> pure t
            IPtrVar v t -> IPtrVar <$> renameN v <*> pure t

instance IRRep r => VisitGeneric (DeclBinding r) r where
  visitGeneric (DeclBinding ann expr) = DeclBinding ann <$> visitGeneric expr

instance IRRep r => VisitGeneric (EffTy r) r where
  visitGeneric (EffTy eff ty) =
    EffTy <$> visitGeneric eff <*> visitGeneric ty

instance VisitGeneric DataConDefs CoreIR where
  visitGeneric = \case
    ADTCons cons -> ADTCons <$> mapM visitGeneric cons
    StructFields defs -> do
      let (names, tys) = unzip defs
      tys' <- mapM visitGeneric tys
      return $ StructFields $ zip names tys'

instance VisitGeneric DataConDef CoreIR where
  visitGeneric (DataConDef sn (Abs bs UnitE) repTy ps) = do
    PiType bs' _  <- visitGeneric $ PiType bs $ EffTy Pure UnitTy
    repTy' <- visitGeneric repTy
    return $ DataConDef sn (Abs bs' UnitE) repTy' ps

instance VisitGeneric (Con      r) r where visitGeneric = traverseOpTerm
instance VisitGeneric (TC       r) r where visitGeneric = traverseOpTerm
instance VisitGeneric (MiscOp   r) r where visitGeneric = traverseOpTerm
instance VisitGeneric (VectorOp r) r where visitGeneric = traverseOpTerm
instance VisitGeneric (MemOp    r) r where visitGeneric = traverseOpTerm

-- === SubstE/SubstB instances ===
-- These live here, as orphan instances, because we normalize as we substitute.

toAtomVar :: (EnvReader m,  IRRep r) => AtomName r n -> m n (AtomVar r n)
toAtomVar v = do
  ty <- getType <$> lookupAtomName v
  return $ AtomVar v ty

bindersToVars :: (EnvReader m,  IRRep r) => Nest (Binder r) n' n -> m n [AtomVar r n]
bindersToVars bs = do
  withExtEvidence bs do
    Distinct <- getDistinct
    mapM toAtomVar $ nestToNames bs

bindersToAtoms :: (EnvReader m,  IRRep r) => Nest (Binder r) n' n -> m n [Atom r n]
bindersToAtoms bs = liftM (Var <$>) $ bindersToVars bs

newtype SubstVisitor i o a = SubstVisitor { runSubstVisitor :: Reader (Env o, Subst AtomSubstVal i o) a }
        deriving (Functor, Applicative, Monad, MonadReader (Env o, Subst AtomSubstVal i o))

substV :: (Distinct o, SubstE AtomSubstVal e) => e i -> SubstVisitor i o (e o)
substV x = ask <&> \env -> substE env x

instance Distinct o => NonAtomRenamer (SubstVisitor i o) i o where
  renameN = substV

instance (Distinct o, IRRep r) => Visitor (SubstVisitor i o) r i o where
  visitType = substV
  visitAtom = substV
  visitLam  = substV
  visitPi   = substV

instance Color c => SubstE AtomSubstVal (AtomSubstVal c) where
  substE (_, env) (Rename name) = env ! name
  substE env (SubstVal val) = SubstVal $ substE env val

instance SubstV (SubstVal Atom) (SubstVal Atom) where

instance IRRep r => SubstE AtomSubstVal (Atom r) where
  substE es@(env, subst) = \case
    Var (AtomVar v ty) -> case subst!v of
      Rename v' -> Var $ AtomVar v' (substE es ty)
      SubstVal x -> x
    SimpInCore x   -> SimpInCore (substE es x)
    ProjectElt _ i x -> do
     let x' = substE es x
     runEnvReaderM env $ normalizeProj i x'
    atom -> runReader (runSubstVisitor $ visitAtomPartial atom) es

instance IRRep r => SubstE AtomSubstVal (Type r) where
  substE es@(env, subst) = \case
    TyVar (AtomVar v ty) -> case subst ! v of
      Rename v' -> TyVar $ AtomVar v' (substE es ty)
      SubstVal (Type t) -> t
      SubstVal atom -> error $ "bad substitution: " ++ pprint v ++ " -> " ++ pprint atom
    ProjectEltTy _ i x -> do
     let x' = substE es x
     case runEnvReaderM env $ normalizeProj i x' of
       Type t   -> t
       _ -> error "bad substitution"
    ty -> runReader (runSubstVisitor $ visitTypePartial ty) es

instance SubstE AtomSubstVal SimpInCore

instance IRRep r => SubstE AtomSubstVal (EffectRow r) where
  substE env (EffectRow effs tailVar) = do
    let effs' = eSetFromList $ map (substE env) (eSetToList effs)
    let tailEffRow = case tailVar of
          NoTail -> EffectRow mempty NoTail
          EffectRowTail (AtomVar v _) -> case snd env ! v of
            Rename        v'  -> do
              let v'' = runEnvReaderM (fst env) $ toAtomVar v'
              EffectRow mempty (EffectRowTail v'')
            SubstVal (Var v') -> EffectRow mempty (EffectRowTail v')
            SubstVal (Eff r)  -> r
            _ -> error "Not a valid effect substitution"
    extendEffRow effs' tailEffRow

instance IRRep r => SubstE AtomSubstVal (Effect r)

instance SubstE AtomSubstVal SpecializationSpec where
  substE env (AppSpecialization (AtomVar f _) ab) = do
    let f' = case snd env ! f of
               Rename v -> runEnvReaderM (fst env) $ toAtomVar v
               SubstVal (Var v) -> v
               _ -> error "bad substitution"
    AppSpecialization f' (substE env ab)

instance SubstE AtomSubstVal EffectDef
instance SubstE AtomSubstVal EffectOpType
instance SubstE AtomSubstVal IExpr
instance IRRep r => SubstE AtomSubstVal (RepVal r)
instance SubstE AtomSubstVal TyConParams
instance SubstE AtomSubstVal DataConDef
instance IRRep r => SubstE AtomSubstVal (BaseMonoid r)
instance IRRep r => SubstE AtomSubstVal (DAMOp r)
instance IRRep r => SubstE AtomSubstVal (TypedHof r)
instance IRRep r => SubstE AtomSubstVal (Hof r)
instance IRRep r => SubstE AtomSubstVal (TC r)
instance IRRep r => SubstE AtomSubstVal (Con r)
instance IRRep r => SubstE AtomSubstVal (MiscOp r)
instance IRRep r => SubstE AtomSubstVal (VectorOp r)
instance IRRep r => SubstE AtomSubstVal (MemOp r)
instance IRRep r => SubstE AtomSubstVal (PrimOp r)
instance IRRep r => SubstE AtomSubstVal (RefOp r)
instance IRRep r => SubstE AtomSubstVal (EffTy r)
instance IRRep r => SubstE AtomSubstVal (Expr r)
instance IRRep r => SubstE AtomSubstVal (GenericOpRep const r)
instance SubstE AtomSubstVal InstanceBody
instance SubstE AtomSubstVal DictType
instance SubstE AtomSubstVal DictExpr
instance IRRep r => SubstE AtomSubstVal (LamExpr r)
instance SubstE AtomSubstVal CorePiType
instance SubstE AtomSubstVal CoreLamExpr
instance IRRep r => SubstE AtomSubstVal (TabPiType r)
instance IRRep r => SubstE AtomSubstVal (PiType r)
instance IRRep r => SubstE AtomSubstVal (DepPairType r)
instance SubstE AtomSubstVal SolverBinding
instance IRRep r => SubstE AtomSubstVal (DeclBinding r)
instance IRRep r => SubstB AtomSubstVal (Decl r)
instance SubstE AtomSubstVal NewtypeTyCon
instance SubstE AtomSubstVal NewtypeCon
instance IRRep r => SubstE AtomSubstVal (IxDict r)
instance IRRep r => SubstE AtomSubstVal (IxType r)
instance SubstE AtomSubstVal DataConDefs
