-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module CheapReduction
  ( reduceWithDecls, reduceExpr
  , instantiateTyConDef, dataDefRep, unwrapNewtypeType, projType
  , Visitor (..), VisitGeneric (..)
  , visitAtomDefault, visitTypeDefault, Visitor2, mkStuck
  , visitBinders, visitPiDefault, visitAlt, toAtomVar, instantiate, withInstantiated
  , bindersToVars, bindersToAtoms, instantiateNames, withInstantiatedNames, assumeConst
  , repValAtom, reduceUnwrap, reduceProj, reduceSuperclassProj, typeOfApp
  , reduceInstantiateGiven, queryStuckType, substMStuck, reduceTabApp, substStuck)
  where

import Control.Applicative
import Control.Monad.Writer.Strict  hiding (Alt)
import Data.Functor ((<&>))
import Data.Maybe (fromJust)

import Subst
import Core
import Err
import Name
import PPrint
import QueryTypePure
import Types.Core
import Types.Top
import Types.Imp
import Types.Primitives
import Util
import GHC.Stack

-- Carry out the reductions we are willing to carry out during type
-- inference.  The goal is to support type aliases like `Int = Int32`
-- and type-level functions like `def Fin (n:Int) : Type = Range 0 n`.
-- The reductions in question are mostly inlining and beta-reducing
-- functions.  There's also a bunch of stuff to do with synthesizing
-- class dictionaries, because types often contain polymorphic
-- literals (e.g., `Fin 10`).

-- === api ===

reduceWithDecls
  :: (HasNamesE e, SubstE AtomSubstVal e, EnvReader m)
  => WithDecls e n -> m n (Maybe (e n))
reduceWithDecls (Abs decls e) =
  liftReducerM $ reduceWithDeclsM decls $ substM e

reduceExpr :: EnvReader m => Expr n -> m n (Maybe (Atom n))
reduceExpr e = liftReducerM $ reduceExprM e
{-# INLINE reduceExpr #-}

-- TODO: just let the caller use `liftReducerM` themselves directly?

reduceProj :: EnvReader m => Int -> Atom n -> m n (Atom n)
reduceProj i x = liftM fromJust $ liftReducerM $ reduceProjM i x
{-# INLINE reduceProj #-}

reduceUnwrap :: EnvReader m => CAtom n -> m n (CAtom n)
reduceUnwrap x = liftM fromJust $ liftReducerM $ reduceUnwrapM x
{-# INLINE reduceUnwrap #-}

reduceSuperclassProj :: EnvReader m => Int -> CDict n -> m n (CAtom n)
reduceSuperclassProj i x = liftM fromJust $ liftReducerM $ reduceSuperclassProjM i x
{-# INLINE reduceSuperclassProj #-}

reduceInstantiateGiven :: EnvReader m => CAtom n -> [CAtom n] -> m n (CAtom n)
reduceInstantiateGiven f xs = liftM fromJust $ liftReducerM $ reduceInstantiateGivenM f xs
{-# INLINE reduceInstantiateGiven #-}

reduceTabApp :: EnvReader m => Atom n -> Atom n -> m n (Atom n)
reduceTabApp f x = liftM fromJust $ liftReducerM $ reduceTabAppM f x
{-# INLINE reduceTabApp #-}

-- === internal ===

type ReducerM = SubstReaderT AtomSubstVal (EnvReaderT Except)

liftReducerM :: EnvReader m => ReducerM n n a -> m n (Maybe a)
liftReducerM cont = do
  liftM ignoreExcept $ liftEnvReaderT $ runSubstReaderT idSubst do
    (Just <$> cont) <|> return Nothing

reduceWithDeclsM :: Nest Decl i i' -> ReducerM i' o a -> ReducerM i o a
reduceWithDeclsM Empty cont = cont
reduceWithDeclsM (Nest (Let b (DeclBinding _ expr)) rest) cont = do
  x <- reduceExprM expr
  extendSubst (b@>SubstVal x) $ reduceWithDeclsM rest cont

reduceExprM :: Expr i -> ReducerM i o (Atom o)
reduceExprM = \case
 Atom x -> substM x
 Block _ (Abs decls result) -> reduceWithDeclsM decls $ reduceExprM result
 App _ f xs -> mapM substM xs >>= reduceApp f
 Unwrap _ x -> substM x >>= reduceUnwrapM
 Project _ i x -> substM x >>= reduceProjM i
 ApplyMethod _ dict i explicitArgs -> do
   explicitArgs' <- mapM substM explicitArgs
   dict' <- substM dict
   case dict' of
     Con (DictConAtom (InstanceDict _ instanceName args)) -> dropSubst do
       def <- lookupInstanceDef instanceName
       withInstantiated def args \(PairE _ (InstanceBody _ methods)) -> do
         reduceApp (methods !! i) explicitArgs'
     _ -> empty
 PrimOp ty' (MiscOp (CastOp val')) -> do
   ty  <- substM ty'
   val <- substM val'
   case (ty, val) of
     (TyCon (BaseType (Scalar Word32Type)), Con (Lit (Word64Lit v))) ->
       return $ Con $ Lit $ Word32Lit $ fromIntegral v
     _ -> empty
 TabApp _ tab x -> do
   x'   <- substM x
   tab' <- substM tab
   reduceTabAppM tab' x'
 TopApp _ _ _ -> empty
 Case _ _ _   -> empty
 TabCon _ _   -> empty
 PrimOp _ _   -> empty

reduceApp :: CAtom i -> [CAtom o] -> ReducerM i o (CAtom o)
reduceApp f xs = do
  f' <- substM f  -- TODO: avoid double-subst
  case f' of
    Con (Lam lam) -> dropSubst $ withInstantiated lam xs \body -> reduceExprM body
    _ -> empty

reduceProjM :: Int -> Atom o -> ReducerM i o (Atom o)
reduceProjM i x = case x of
  Con con -> case con of
    ProdCon xs -> return $ xs !! i
    DepPair l _ _ | i == 0 -> return l
    DepPair _ r _ | i == 1 -> return r
    _ -> error "not a product"
  Stuck _ e -> mkStuck $ StuckProject i e

reduceSuperclassProjM :: Int -> CDict o -> ReducerM i o (CAtom o)
reduceSuperclassProjM superclassIx dict = case dict of
  DictCon (InstanceDict _ instanceName args) -> dropSubst do
    args' <- mapM substM args
    InstanceDef _ _ bs _ body <- lookupInstanceDef instanceName
    let InstanceBody superclasses _ = body
    instantiate (Abs bs (superclasses !! superclassIx)) args'
  StuckDict _ child -> mkStuck $ SuperclassProj superclassIx child
  _ -> error "invalid superclass projection"

reduceInstantiateGivenM :: CAtom o -> [CAtom o] -> ReducerM i o (CAtom o)
reduceInstantiateGivenM f xs = case f of
  Con (Lam lam) -> dropSubst $ withInstantiated lam xs \body -> reduceExprM body
  Stuck _ f' -> mkStuck $ InstantiatedGiven f' xs
  _ -> error "bad instantiation"

mkStuck:: EnvReader m => Stuck n -> m n (Atom n)
mkStuck x = do
  ty <- queryStuckType x
  return $ Stuck ty x

queryStuckType :: EnvReader m => Stuck n -> m n (Type n)
queryStuckType = \case
  Var v -> return $ getType v
  StuckProject i s -> projType i =<< mkStuck s
  StuckTabApp f x -> do
    fTy <- queryStuckType f
    typeOfTabApp fTy x
  PtrVar t _ -> return $ PtrTy t
  RepValAtom repVal -> return $ getType repVal
  StuckUnwrap s -> queryStuckType s >>= \case
    TyCon (NewtypeTyCon con) -> snd <$> unwrapNewtypeType con
    _ -> error "not a newtype"
  InstantiatedGiven f xs -> do
    fTy <- queryStuckType f
    typeOfApp fTy xs
  SuperclassProj i s -> superclassProjType i =<< queryStuckType s

projType :: EnvReader m => Int -> Atom n -> m n (Type n)
projType i x = case getType x of
  TyCon con -> case con of
    ProdType xs -> return $ xs !! i
    DepPairTy t | i == 0 -> return $ depPairLeftTy t
    DepPairTy t | i == 1 -> do
      liftReducerM (reduceProjM 0 x) >>= \case
        Just xFst -> instantiate t [xFst]
        Nothing -> err
    _ -> err
  _ -> err
  where err = error $ "Can't project type: " ++ pprint (getType x)

superclassProjType :: EnvReader m => Int -> CType n -> m n (CType n)
superclassProjType i (TyCon (DictTy dictTy)) = case dictTy of
  DictType _ className params -> do
    ClassDef _ _ _ _ _ bs superclasses _ <- lookupClassDef className
    instantiate (Abs bs $ getSuperclassType REmpty superclasses i) params
  _ -> error "bad superclass projection"
superclassProjType _ _ = error "bad superclass projection"

typeOfTabApp  :: EnvReader m => Type n -> Atom n -> m n (Type n)
typeOfTabApp (TyCon (TabPi piTy)) x = withSubstReaderT $
  withInstantiated piTy [x] \ty -> substM ty
typeOfTabApp _ _ = error "expected a TabPi type"

typeOfApp  :: EnvReader m => Type n -> [Atom n] -> m n (Type n)
typeOfApp (TyCon (Pi piTy)) xs = withSubstReaderT $
  withInstantiated piTy xs \ty -> substM ty
typeOfApp _ _ = error "expected a pi type"

repValAtom :: EnvReader m => RepVal n -> m n (Atom n)
repValAtom (RepVal ty tree) = case ty of
  TyCon (ProdType ts) -> case tree of
    Branch trees -> toAtom <$> ProdCon <$> mapM repValAtom (zipWith RepVal ts trees)
    _ -> malformed
  TyCon (BaseType _) -> case tree of
    Leaf x -> case x of
      ILit l -> return $ toAtom $ Lit l
      _ -> fallback
    _ -> malformed
  -- TODO: make sure this covers all the cases. Maybe only TabPi should hit the
  -- fallback? This could be a place where we accidentally violate the `Stuck`
  -- assumption
  _ -> fallback
  where fallback = return $ Stuck ty $ RepValAtom $ RepVal ty tree
        malformed = error "malformed repval"
{-# INLINE repValAtom #-}

depPairLeftTy :: DepPairType n -> Type n
depPairLeftTy (DepPairType _ (_:>ty) _) = ty
{-# INLINE depPairLeftTy #-}

reduceUnwrapM :: CAtom o -> ReducerM i o (CAtom o)
reduceUnwrapM = \case
  Con con -> case con of
    NewtypeCon _ x -> return x
    _ -> error "not a newtype"
  Stuck _ e -> mkStuck $ StuckUnwrap e

reduceTabAppM :: Atom o -> Atom o -> ReducerM i o (Atom o)
reduceTabAppM tab x = case tab of
  Stuck _ tab' -> mkStuck (StuckTabApp tab' x)
  _ -> error $ "not a table" ++ pprint tab

unwrapNewtypeType :: EnvReader m => NewtypeTyCon n -> m n (NewtypeCon n, Type n)
unwrapNewtypeType = \case
  Nat                   -> return (NatCon, IdxRepTy)
  Fin n                 -> return (FinCon n, NatTy)
  UserADTType sn defName params -> do
    def <- lookupTyCon defName
    ty' <- dataDefRep <$> instantiateTyConDef def params
    return (UserADTData sn defName params, ty')
{-# INLINE unwrapNewtypeType #-}

instantiateTyConDef :: EnvReader m => TyConDef n -> TyConParams n -> m n (DataConDefs n)
instantiateTyConDef (TyConDef _ _ bs conDefs) (TyConParams _ xs) = do
  applySubst (bs @@> (SubstVal <$> xs)) conDefs
{-# INLINE instantiateTyConDef #-}

assumeConst
  :: (HoistableE body, SinkableE body, ToBindersAbs e body) => e n -> body n
assumeConst e = case toAbs e of Abs bs body -> ignoreHoistFailure $ hoist bs body

instantiate
  :: (EnvReader m, SubstE (SubstVal Atom) body, SinkableE body, ToBindersAbs e body)
  => e n -> [Atom n] -> m n (body n)
instantiate e xs = case toAbs e of
  Abs bs body -> applySubst (bs @@> (SubstVal <$> xs)) body

-- "lazy" subst-extending version of `instantiate`
withInstantiated
  :: (SubstReader (SubstVal val) m, SinkableE body, ToBindersAbs e body)
  => e i -> [val o]
  -> (forall i'. body i' -> m i' o a)
  -> m i o a
withInstantiated e xs cont = case toAbs e of
  Abs bs body -> extendSubst (bs @@> (SubstVal <$> xs)) $ cont body

instantiateNames
  :: (EnvReader m, RenameE body, SinkableE body, ToBindersAbs e body)
  => e n -> [AtomName n] -> m n (body n)
instantiateNames e vs = case toAbs e of
  Abs bs body -> applyRename (bs @@> vs) body

-- "lazy" subst-extending version of `instantiateNames`
withInstantiatedNames
  :: (SubstReader Name m, RenameE body, SinkableE body, ToBindersAbs e body)
  => e i -> [AtomName o]
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
  tys -> toType $ SumType $ tys <&> \(DataConDef _ _ ty _) -> ty
dataDefRep (StructFields fields) = case map snd fields of
  [ty] -> ty
  tys  -> toType (ProdType tys)

-- === traversable terms ===

class VisitGeneric (e:: E) where
  visitGeneric :: HasCallStack => Visitor m i o => e i -> m (e o)

class Monad m => Visitor m i o | m -> i, m -> o where
  visitType :: Type i -> m (Type o)
  visitAtom :: Atom i -> m (Atom o)
  visitLam  :: LamExpr i -> m (LamExpr o)
  visitPi   :: PiType  i -> m (PiType  o)
  -- only applied to non-atom names
  renameN :: Name i -> m (Name o)

type Visitor2 (m::MonadKind2) = forall i o . Visitor (m i o) i o

instance VisitGeneric (Atom   ) where visitGeneric = visitAtom
instance VisitGeneric (Type   ) where visitGeneric = visitType
instance VisitGeneric (LamExpr) where visitGeneric = visitLam
instance VisitGeneric (PiType ) where visitGeneric = visitPi

visitBlock :: Visitor m i o => Expr i -> m (Expr o)
visitBlock b = visitGeneric (LamExpr Empty b) >>= \case
  LamExpr Empty b' -> return b'
  _ -> error "not a block"

visitAlt :: Visitor m i o => Alt i -> m (Alt o)
visitAlt (Abs b body) = do
  visitGeneric (LamExpr (UnaryNest b) body) >>= \case
    LamExpr (UnaryNest b') body' -> return $ Abs b' body'
    _ -> error "not an alt"

visitTypeDefault
  :: (Visitor (m i o) i o, AtomSubstReader v m, EnvReader2 m)
  => Type i -> m i o (Type o)
visitTypeDefault ty = case ty of
  StuckTy _ _ -> atomSubstM ty
  TyCon con -> TyCon <$> visitGeneric con

visitAtomDefault
  :: (Visitor (m i o) i o, AtomSubstReader v m, EnvReader2 m)
  => Atom i -> m i o (Atom o)
visitAtomDefault ty = case ty of
  Stuck _ _ -> atomSubstM ty
  Con con -> Con <$> visitGeneric con

visitPiDefault
  :: (Visitor2 m, FromName v, AtomSubstReader v m, EnvExtender2 m)
  => PiType i -> m i o (PiType o)
visitPiDefault (PiType bs effty) = do
  visitBinders bs \bs' -> do
    effty' <- visitGeneric effty
    return $ PiType bs' effty'

visitBinders
  :: (Visitor2 m, FromName v, AtomSubstReader v m, EnvExtender2 m)
  => Nest Binder i i'
  -> (forall o'. DExt o o' => Nest Binder o o' -> m i' o' a)
  -> m i o a
visitBinders Empty cont = getDistinct >>= \Distinct -> cont Empty
visitBinders (Nest (b:>ty) bs) cont = do
  ty' <- visitType ty
  withFreshBinder (getNameHint b) ty' \b' -> do
    extendRenamer (b@>binderName b') do
      visitBinders bs \bs' ->
        cont $ Nest b' bs'

instance VisitGeneric Expr where
  visitGeneric = \case
    Block _ _ -> error "not handled generically"
    TopApp et v xs -> TopApp <$> visitGeneric et <*> renameN v <*> mapM visitGeneric xs
    TabApp t tab x -> TabApp <$> visitType t <*> visitGeneric tab <*> visitGeneric x
    -- TODO: should we reuse the original effects? Whether it's valid depends on
    -- the type-preservation requirements for a visitor. We should clarify what
    -- those are.
    Case x alts effTy -> do
      x' <- visitGeneric x
      alts' <- mapM visitAlt alts
      effTy' <- visitGeneric effTy
      return $ Case x' alts' effTy'
    Atom x -> Atom <$> visitGeneric x
    TabCon t xs -> TabCon <$> visitGeneric t <*> mapM visitGeneric xs
    PrimOp t op -> PrimOp <$> visitGeneric t <*> mapM visitGeneric op
    App et fAtom xs -> App <$> visitGeneric et <*> visitGeneric fAtom <*> mapM visitGeneric xs
    ApplyMethod et m i xs -> ApplyMethod <$> visitGeneric et <*> visitGeneric m <*> pure i <*> mapM visitGeneric xs
    Project t i x -> Project <$> visitGeneric t <*> pure i <*> visitGeneric x
    Unwrap t x -> Unwrap <$> visitGeneric t <*> visitGeneric x
    Hof op -> Hof <$> visitGeneric op

instance VisitGeneric TypedHof where
  visitGeneric (TypedHof eff hof) = TypedHof <$> visitGeneric eff <*> visitGeneric hof

instance VisitGeneric Hof where
  visitGeneric = \case
    For ann d lam -> For ann <$> visitGeneric d <*> visitGeneric lam
    While          b -> While          <$> visitBlock b
    Linearize      lam x -> Linearize <$> visitGeneric lam <*> visitGeneric x
    Transpose      lam x -> Transpose <$> visitGeneric lam <*> visitGeneric x

instance VisitGeneric Effects where
  visitGeneric = \case
    Pure      -> return Pure
    Effectful -> return Effectful

instance VisitGeneric DictCon where
  visitGeneric = \case
    InstanceDict t v xs  -> InstanceDict  <$> visitGeneric t <*> renameN v <*> mapM visitGeneric xs
    IxFin x              -> IxFin         <$> visitGeneric x
    IxRawFin x           -> IxRawFin      <$> visitGeneric x
    IxSpecialized v xs   -> IxSpecialized <$> renameN v <*> mapM visitGeneric xs

instance VisitGeneric Con where
  visitGeneric = \case
    Lit l -> return $ Lit l
    ProdCon xs -> ProdCon <$> mapM visitGeneric xs
    SumCon ty con arg -> SumCon <$> mapM visitGeneric ty <*> return con <*> visitGeneric arg
    DepPair x y t -> do
      x' <- visitGeneric x
      y' <- visitGeneric y
      ~(DepPairTy t') <- visitGeneric $ DepPairTy t
      return $ DepPair x' y' t'
    Lam lam          -> Lam         <$> visitGeneric lam
    DictConAtom d    -> DictConAtom <$> visitGeneric d
    TyConAtom   t    -> TyConAtom   <$> visitGeneric t
    NewtypeCon con x -> NewtypeCon  <$> visitGeneric con <*> visitGeneric x

instance VisitGeneric NewtypeCon where
  visitGeneric = \case
    UserADTData sn t params -> UserADTData sn <$> renameN t <*> visitGeneric params
    NatCon -> return NatCon
    FinCon x -> FinCon <$> visitGeneric x

instance VisitGeneric NewtypeTyCon where
  visitGeneric = \case
    Nat -> return Nat
    Fin x -> Fin <$> visitGeneric x
    UserADTType n v params -> UserADTType n <$> renameN v <*> visitGeneric params

instance VisitGeneric TyConParams where
  visitGeneric (TyConParams expls xs) = TyConParams expls <$> mapM visitGeneric xs


instance VisitGeneric IxType where
  visitGeneric (IxType t d) = IxType <$> visitType t <*> visitGeneric d

instance VisitGeneric DictType where
  visitGeneric = \case
    DictType n v xs -> DictType n <$> renameN v <*> mapM visitGeneric xs
    IxDictType   t -> IxDictType   <$> visitGeneric t

instance VisitGeneric CoreLamExpr where
  visitGeneric (CoreLamExpr t lam) = CoreLamExpr <$> visitGeneric t <*> visitGeneric lam

instance VisitGeneric CorePiType where
  visitGeneric (CorePiType app expl bs effty) = do
    PiType bs' effty' <- visitGeneric $ PiType bs effty
    return $ CorePiType app expl bs' effty'

instance VisitGeneric TabPiType where
  visitGeneric (TabPiType d b eltTy) = do
    d' <- visitGeneric d
    visitGeneric (PiType (UnaryNest b) eltTy) <&> \case
      PiType (UnaryNest b') eltTy' -> TabPiType d' b' eltTy'
      _ -> error "not a table pi type"

instance VisitGeneric DepPairType where
  visitGeneric (DepPairType expl b ty) = do
    visitGeneric (PiType (UnaryNest b) ty) <&> \case
      PiType (UnaryNest b') ty' -> DepPairType expl b' ty'
      _ -> error "not a dependent pair type"

instance VisitGeneric RepVal where
  visitGeneric (RepVal ty tree) = RepVal <$> visitGeneric ty <*> mapM renameIExpr tree
    where renameIExpr = \case
            ILit l -> return $ ILit l
            IVar    v t -> IVar    <$> renameN v <*> pure t
            IPtrVar v t -> IPtrVar <$> renameN v <*> pure t

instance VisitGeneric DeclBinding where
  visitGeneric (DeclBinding ann expr) = DeclBinding ann <$> visitGeneric expr

instance VisitGeneric EffTy where
  visitGeneric (EffTy eff ty) =
    EffTy <$> visitGeneric eff <*> visitGeneric ty

instance VisitGeneric DataConDefs where
  visitGeneric = \case
    ADTCons cons -> ADTCons <$> mapM visitGeneric cons
    StructFields defs -> do
      let (names, tys) = unzip defs
      tys' <- mapM visitGeneric tys
      return $ StructFields $ zip names tys'

instance VisitGeneric DataConDef where
  visitGeneric (DataConDef sn (Abs bs UnitE) repTy ps) = do
    PiType bs' _  <- visitGeneric $ PiType bs UnitTy
    repTy' <- visitGeneric repTy
    return $ DataConDef sn (Abs bs' UnitE) repTy' ps

instance VisitGeneric TyCon where
  visitGeneric = \case
    BaseType bt    -> return $ BaseType bt
    ProdType tys   -> ProdType <$> mapM visitGeneric tys
    SumType  tys   -> SumType  <$> mapM visitGeneric tys
    RefType t      -> RefType  <$> visitGeneric t
    TabPi t        -> TabPi     <$> visitGeneric t
    DepPairTy t    -> DepPairTy <$> visitGeneric t
    Kind k         -> return $ Kind k
    DictTy t       -> DictTy <$> visitGeneric t
    Pi t           -> Pi <$> visitGeneric t
    NewtypeTyCon t -> NewtypeTyCon <$> visitGeneric t

instance VisitGeneric Dict where
  visitGeneric = \case
    StuckDict ty s -> fromJust <$> toMaybeDict <$> visitGeneric (Stuck ty s)
    DictCon con -> DictCon <$> visitGeneric con

-- === SubstE/SubstB instances ===
-- These live here, as orphan instances, because we normalize as we substitute.

bindersToVars :: EnvReader m => Nest Binder n' n -> m n [AtomVar n]
bindersToVars bs = do
  withExtEvidence bs do
    Distinct <- getDistinct
    mapM toAtomVar $ nestToNames bs

bindersToAtoms :: EnvReader m => Nest Binder n' n -> m n [Atom n]
bindersToAtoms bs = liftM (toAtom <$>) $ bindersToVars bs

instance SubstE AtomSubstVal Name where
  substE (_, env) name = case env ! name of
    Rename name' -> name'
    _ -> error "can only substitute names with names"

instance SubstE AtomSubstVal AtomSubstVal where
  substE (_, env) (Rename name) = env ! name
  substE env (SubstVal val) = SubstVal $ substE env val

instance SubstE AtomSubstVal IxDict where
  substE es = \case
    StuckDict _ e -> fromJust $ toMaybeDict $ substStuck es e
    DictCon con -> DictCon $ substE es con

instance SubstE AtomSubstVal Atom where
  substE es = \case
    Stuck _ e -> substStuck es e
    Con con -> Con $ substE es con

instance SubstE AtomSubstVal Type where
  substE es = \case
    StuckTy _ e -> fromJust $ toMaybeType $ substStuck es e
    TyCon con -> TyCon $ substE es con

substMStuck :: (SubstReader AtomSubstVal m, EnvReader2 m) => Stuck i -> m i o (Atom o)
substMStuck stuck = do
  subst <- getSubst
  env <- unsafeGetEnv
  withDistinct $ return $ substStuck (env, subst) stuck

substStuck :: Distinct o => (Env o, Subst AtomSubstVal i o) -> Stuck i -> Atom o
substStuck (env, subst) stuck =
  ignoreExcept $ runEnvReaderT env $ runSubstReaderT subst $ reduceStuck stuck

reduceStuck :: Distinct o => Stuck i -> ReducerM i o (Atom o)
reduceStuck = \case
  Var (AtomVar v ty) -> do
    lookupSubstM v >>= \case
      Rename v' -> toAtom . AtomVar v' <$> substM ty
      SubstVal x -> return x
  StuckProject i x -> do
    x' <- reduceStuck x
    dropSubst $ reduceProjM i x'
  StuckUnwrap x -> do
    x' <- reduceStuck x
    dropSubst $ reduceUnwrapM x'
  StuckTabApp f x -> do
    f' <- reduceStuck f
    x' <- substM x
    dropSubst $ reduceTabAppM f' x'
  InstantiatedGiven f xs -> do
    xs' <- mapM substM xs
    f' <- reduceStuck f
    reduceInstantiateGivenM f' xs'
  SuperclassProj superclassIx child -> do
    Just child' <- toMaybeDict <$> reduceStuck child
    reduceSuperclassProjM superclassIx child'
  PtrVar ptrTy ptr -> mkStuck =<< PtrVar ptrTy <$> substM ptr
  RepValAtom repVal -> mkStuck =<< RepValAtom <$> substM repVal

instance SubstE AtomSubstVal SpecializationSpec where
  substE env (AppSpecialization (AtomVar f _) ab) = do
    let f' = case snd env ! f of
               Rename v -> runEnvReaderM (fst env) $ toAtomVar v
               SubstVal (Stuck _ (Var v)) -> v
               _ -> error "bad substitution"
    AppSpecialization f' (substE env ab)

instance SubstE AtomSubstVal Effects where
  substE _ = \case
    Pure -> Pure
    Effectful -> Effectful

instance SubstE AtomSubstVal IExpr
instance SubstE AtomSubstVal RepVal
instance SubstE AtomSubstVal TyConParams
instance SubstE AtomSubstVal DataConDef
instance SubstE AtomSubstVal TypedHof
instance SubstE AtomSubstVal Hof
instance SubstE AtomSubstVal TyCon
instance SubstE AtomSubstVal DictCon
instance SubstE AtomSubstVal Con
instance SubstE AtomSubstVal EffTy
instance SubstE AtomSubstVal Expr
instance SubstE AtomSubstVal InstanceBody
instance SubstE AtomSubstVal DictType
instance SubstE AtomSubstVal LamExpr
instance SubstE AtomSubstVal CorePiType
instance SubstE AtomSubstVal CoreLamExpr
instance SubstE AtomSubstVal TabPiType
instance SubstE AtomSubstVal PiType
instance SubstE AtomSubstVal DepPairType
instance SubstE AtomSubstVal SolverBinding
instance SubstE AtomSubstVal DeclBinding
instance SubstB AtomSubstVal Decl
instance SubstE AtomSubstVal NewtypeTyCon
instance SubstE AtomSubstVal NewtypeCon
instance SubstE AtomSubstVal IxType
instance SubstE AtomSubstVal DataConDefs
