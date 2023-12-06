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
  , NonAtomRenamer (..), Visitor (..), VisitGeneric (..)
  , visitAtomDefault, visitTypeDefault, Visitor2, mkStuck, mkStuckTy
  , visitBinders, visitPiDefault, visitAlt, toAtomVar, instantiate, withInstantiated
  , bindersToVars, bindersToAtoms, instantiateNames, withInstantiatedNames, assumeConst
  , repValAtom, reduceUnwrap, reduceProj, reduceSuperclassProj, typeOfApp
  , reduceInstantiateGiven, queryStuckType, substMStuck, reduceTabApp, substStuck
  , liftSimpAtom, reduceACase)
  where

import Control.Applicative
import Control.Monad.Writer.Strict  hiding (Alt)
import Data.Functor ((<&>))
import Data.Maybe (fromJust)

import Subst
import Core
import Err
import IRVariants
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
  :: (IRRep r, HasNamesE e, SubstE AtomSubstVal e, EnvReader m)
  => WithDecls r e n -> m n (Maybe (e n))
reduceWithDecls (Abs decls e) =
  liftReducerM $ reduceWithDeclsM decls $ substM e

reduceExpr :: (IRRep r, EnvReader m) => Expr r n -> m n (Maybe (Atom r n))
reduceExpr e = liftReducerM $ reduceExprM e
{-# INLINE reduceExpr #-}

-- TODO: just let the caller use `liftReducerM` themselves directly?

reduceProj :: (IRRep r, EnvReader m) => Int -> Atom r n -> m n (Atom r n)
reduceProj i x = liftM fromJust $ liftReducerM $ reduceProjM i x
{-# INLINE reduceProj #-}

reduceACase :: EnvReader m => SAtom n -> [Abs SBinder CAtom n] -> CType n -> m n (CAtom n)
reduceACase scrut alts resultTy = liftM fromJust $ liftReducerM $ reduceACaseM scrut alts resultTy
{-# INLINE reduceACase #-}

reduceUnwrap :: EnvReader m => CAtom n -> m n (CAtom n)
reduceUnwrap x = liftM fromJust $ liftReducerM $ reduceUnwrapM x
{-# INLINE reduceUnwrap #-}

reduceSuperclassProj :: EnvReader m => Int -> CDict n -> m n (CAtom n)
reduceSuperclassProj i x = liftM fromJust $ liftReducerM $ reduceSuperclassProjM i x
{-# INLINE reduceSuperclassProj #-}

reduceInstantiateGiven :: EnvReader m => CAtom n -> [CAtom n] -> m n (CAtom n)
reduceInstantiateGiven f xs = liftM fromJust $ liftReducerM $ reduceInstantiateGivenM f xs
{-# INLINE reduceInstantiateGiven #-}

reduceTabApp :: (IRRep r, EnvReader m) => Atom r n -> Atom r n -> m n (Atom r n)
reduceTabApp f x = liftM fromJust $ liftReducerM $ reduceTabAppM f x
{-# INLINE reduceTabApp #-}

-- === internal ===

type ReducerM = SubstReaderT AtomSubstVal (EnvReaderT Except)

liftReducerM :: EnvReader m => ReducerM n n a -> m n (Maybe a)
liftReducerM cont = do
  liftM ignoreExcept $ liftEnvReaderT $ runSubstReaderT idSubst do
    (Just <$> cont) <|> return Nothing

reduceWithDeclsM :: IRRep r => Nest (Decl r) i i' -> ReducerM i' o a -> ReducerM i o a
reduceWithDeclsM Empty cont = cont
reduceWithDeclsM (Nest (Let b (DeclBinding _ expr)) rest) cont = do
  x <- reduceExprM expr
  extendSubst (b@>SubstVal x) $ reduceWithDeclsM rest cont

reduceExprM :: IRRep r => Expr r i -> ReducerM i o (Atom r o)
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
 PrimOp (MiscOp (CastOp ty' val')) -> do
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
 TabCon _ _ _ -> empty
 PrimOp _     -> empty

reduceApp :: CAtom i -> [CAtom o] -> ReducerM i o (CAtom o)
reduceApp f xs = do
  f' <- substM f  -- TODO: avoid double-subst
  case f' of
    Con (Lam lam) -> dropSubst $ withInstantiated lam xs \body -> reduceExprM body
    _ -> empty

reduceACaseM :: SAtom n -> [Abs SBinder CAtom n] -> CType n -> ReducerM i n (CAtom n)
reduceACaseM scrut alts resultTy = case scrut of
  Con (SumCon _ i arg) -> do
    Abs b body <- return $ alts !! i
    applySubst (b@>SubstVal arg) body
  Con _ -> error "not a sum type"
  Stuck _ scrut' -> mkStuck $ ACase scrut' alts resultTy

reduceProjM :: IRRep r => Int -> Atom r o -> ReducerM i o (Atom r o)
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

mkStuck:: (IRRep r, EnvReader m) => Stuck r n -> m n (Atom r n)
mkStuck x = do
  ty <- queryStuckType x
  return $ Stuck ty x

mkStuckTy :: EnvReader m => CStuck n -> m n (CType n)
mkStuckTy x = do
  ty <- queryStuckType x
  return $ StuckTy ty x

queryStuckType :: (IRRep r, EnvReader m) => Stuck r n -> m n (Type r n)
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
  LiftSimp t _ -> return t
  LiftSimpFun t _ -> return $ toType t
  -- TabLam and ACase are just defunctionalization tools. The result type
  -- in both cases should *not* be `Data`.
  TabLam (PairE t _) -> return $ toType t
  ACase _ _ resultTy -> return resultTy

projType :: (IRRep r, EnvReader m) => Int -> Atom r n -> m n (Type r n)
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
  IxDictType t | i == 0 -> return $ toType $ DataDictType t
  _ -> error "bad superclass projection"
superclassProjType _ _ = error "bad superclass projection"

typeOfTabApp  :: (IRRep r, EnvReader m) => Type r n -> Atom r n -> m n (Type r n)
typeOfTabApp (TyCon (TabPi piTy)) x = withSubstReaderT $
  withInstantiated piTy [x] \ty -> substM ty
typeOfTabApp _ _ = error "expected a TabPi type"

typeOfApp  :: (IRRep r, EnvReader m) => Type r n -> [Atom r n] -> m n (Type r n)
typeOfApp (TyCon (Pi piTy)) xs = withSubstReaderT $
  withInstantiated piTy xs \(EffTy _ ty) -> substM ty
typeOfApp _ _ = error "expected a pi type"

repValAtom :: EnvReader m => RepVal n -> m n (SAtom n)
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

depPairLeftTy :: DepPairType r n -> Type r n
depPairLeftTy (DepPairType _ (_:>ty) _) = ty
{-# INLINE depPairLeftTy #-}

reduceUnwrapM :: CAtom o -> ReducerM i o (CAtom o)
reduceUnwrapM = \case
  Con con -> case con of
    NewtypeCon _ x -> return x
    _ -> error "not a newtype"
  Stuck _ e -> mkStuck $ StuckUnwrap e

reduceTabAppM :: IRRep r => Atom r o -> Atom r o -> ReducerM i o (Atom r o)
reduceTabAppM tab x = case tab of
  Stuck _ tab' -> mkStuck (StuckTabApp tab' x)
  _ -> error $ "not a table" ++ pprint tab

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
  tys -> toType $ SumType $ tys <&> \(DataConDef _ _ ty _) -> ty
dataDefRep (StructFields fields) = case map snd fields of
  [ty] -> ty
  tys  -> toType (ProdType tys)

-- === traversable terms ===

class Monad m => NonAtomRenamer m i o | m -> i, m -> o where
  renameN :: (IsAtomName c ~ False, Color c) => Name c i -> m (Name c o)

class NonAtomRenamer m i o => Visitor m r i o | m -> i, m -> o where
  visitType :: Type r i -> m (Type r o)
  visitAtom :: Atom r i -> m (Atom r o)
  visitLam  :: LamExpr r i -> m (LamExpr r o)
  visitPi   :: PiType  r i -> m (PiType  r o)

class VisitGeneric (e:: E) (r::IR) | e -> r where
  visitGeneric :: HasCallStack => Visitor m r i o => e i -> m (e o)

type Visitor2 (m::MonadKind2) r = forall i o . Visitor (m i o) r i o

instance VisitGeneric (Atom    r) r where visitGeneric = visitAtom
instance VisitGeneric (Type    r) r where visitGeneric = visitType
instance VisitGeneric (LamExpr r) r where visitGeneric = visitLam
instance VisitGeneric (PiType  r) r where visitGeneric = visitPi

visitBlock :: Visitor m r i o => Expr r i -> m (Expr r o)
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

visitTypeDefault
  :: (IRRep r, Visitor (m i o) r i o, AtomSubstReader v m, EnvReader2 m)
  => Type r i -> m i o (Type r o)
visitTypeDefault ty = case ty of
  StuckTy _ _ -> atomSubstM ty
  TyCon con -> TyCon <$> visitGeneric con

visitAtomDefault
  :: (IRRep r, Visitor (m i o) r i o, AtomSubstReader v m, EnvReader2 m)
  => Atom r i -> m i o (Atom r o)
visitAtomDefault ty = case ty of
  Stuck _ _ -> atomSubstM ty
  Con con -> Con <$> visitGeneric con

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

instance IRRep r => VisitGeneric (Expr r) r where
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
    TabCon Nothing t xs -> TabCon Nothing <$> visitGeneric t <*> mapM visitGeneric xs
    TabCon (Just (WhenIRE d)) t xs -> TabCon <$> (Just . WhenIRE <$> visitGeneric d) <*> visitGeneric t <*> mapM visitGeneric xs
    PrimOp op -> PrimOp <$> visitGeneric op
    App et fAtom xs -> App <$> visitGeneric et <*> visitGeneric fAtom <*> mapM visitGeneric xs
    ApplyMethod et m i xs -> ApplyMethod <$> visitGeneric et <*> visitGeneric m <*> pure i <*> mapM visitGeneric xs
    Project t i x -> Project <$> visitGeneric t <*> pure i <*> visitGeneric x
    Unwrap t x -> Unwrap <$> visitGeneric t <*> visitGeneric x

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
      EffectRowTail v -> visitGeneric (toAtom v) <&> \case
        Stuck _ (Var v') -> EffectRow mempty (EffectRowTail v')
        Con (Eff r)  -> r
        _ -> error "Not a valid effect substitution"
    return $ extendEffRow effs' tailEffRow

instance IRRep r => VisitGeneric (DictCon r) r where
  visitGeneric = \case
    InstanceDict t v xs  -> InstanceDict  <$> visitGeneric t <*> renameN v <*> mapM visitGeneric xs
    IxFin x              -> IxFin         <$> visitGeneric x
    DataData dataTy      -> DataData      <$> visitGeneric dataTy
    IxRawFin x           -> IxRawFin      <$> visitGeneric x
    IxSpecialized v xs   -> IxSpecialized <$> renameN v <*> mapM visitGeneric xs

instance IRRep r => VisitGeneric (Con r) r where
  visitGeneric = \case
    Lit l -> return $ Lit l
    ProdCon xs -> ProdCon <$> mapM visitGeneric xs
    SumCon ty con arg -> SumCon <$> mapM visitGeneric ty <*> return con <*> visitGeneric arg
    HeapVal -> return HeapVal
    DepPair x y t -> do
      x' <- visitGeneric x
      y' <- visitGeneric y
      ~(DepPairTy t') <- visitGeneric $ DepPairTy t
      return $ DepPair x' y' t'
    Lam lam          -> Lam         <$> visitGeneric lam
    Eff eff          -> Eff         <$> visitGeneric eff
    DictConAtom d    -> DictConAtom <$> visitGeneric d
    TyConAtom   t    -> TyConAtom   <$> visitGeneric t
    NewtypeCon con x -> NewtypeCon  <$> visitGeneric con <*> visitGeneric x

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


instance IRRep r => VisitGeneric (IxType r) r where
  visitGeneric (IxType t d) = IxType <$> visitType t <*> visitGeneric d

instance VisitGeneric DictType CoreIR where
  visitGeneric = \case
    DictType n v xs -> DictType n <$> renameN v <*> mapM visitGeneric xs
    IxDictType   t -> IxDictType   <$> visitGeneric t
    DataDictType t -> DataDictType <$> visitGeneric t

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

instance VisitGeneric RepVal SimpIR where
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

instance IRRep r => VisitGeneric (TyCon r) r where
  visitGeneric = \case
    BaseType bt    -> return $ BaseType bt
    ProdType tys   -> ProdType <$> mapM visitGeneric tys
    SumType  tys   -> SumType  <$> mapM visitGeneric tys
    RefType h t    -> RefType  <$> visitGeneric h <*> visitGeneric t
    HeapType       -> return HeapType
    TabPi t        -> TabPi     <$> visitGeneric t
    DepPairTy t    -> DepPairTy <$> visitGeneric t
    TypeKind       -> return TypeKind
    DictTy t       -> DictTy <$> visitGeneric t
    Pi t           -> Pi <$> visitGeneric t
    NewtypeTyCon t -> NewtypeTyCon <$> visitGeneric t

instance IRRep r => VisitGeneric (Dict r) r where
  visitGeneric = \case
    StuckDict ty s -> fromJust <$> toMaybeDict <$> visitGeneric (Stuck ty s)
    DictCon con -> DictCon <$> visitGeneric con

instance VisitGeneric (MiscOp   r) r where visitGeneric = traverseOpTerm
instance VisitGeneric (VectorOp r) r where visitGeneric = traverseOpTerm
instance VisitGeneric (MemOp    r) r where visitGeneric = traverseOpTerm

-- === SubstE/SubstB instances ===
-- These live here, as orphan instances, because we normalize as we substitute.

bindersToVars :: (EnvReader m,  IRRep r) => Nest (Binder r) n' n -> m n [AtomVar r n]
bindersToVars bs = do
  withExtEvidence bs do
    Distinct <- getDistinct
    mapM toAtomVar $ nestToNames bs

bindersToAtoms :: (EnvReader m,  IRRep r) => Nest (Binder r) n' n -> m n [Atom r n]
bindersToAtoms bs = liftM (toAtom <$>) $ bindersToVars bs

instance Color c => SubstE AtomSubstVal (AtomSubstVal c) where
  substE (_, env) (Rename name) = env ! name
  substE env (SubstVal val) = SubstVal $ substE env val

instance SubstV (SubstVal Atom) (SubstVal Atom) where

instance IRRep r => SubstE AtomSubstVal (IxDict r) where
  substE es = \case
    StuckDict _ e -> fromJust $ toMaybeDict $ substStuck es e
    DictCon con -> DictCon $ substE es con

instance IRRep r => SubstE AtomSubstVal (Atom r) where
  substE es = \case
    Stuck _ e -> substStuck es e
    Con con -> Con $ substE es con

instance IRRep r => SubstE AtomSubstVal (Type r) where
  substE es = \case
    StuckTy _ e -> fromJust $ toMaybeType $ substStuck es e
    TyCon con -> TyCon $ substE es con

substMStuck :: (SubstReader AtomSubstVal m, EnvReader2 m, IRRep r) => Stuck r i -> m i o (Atom r o)
substMStuck stuck = do
  subst <- getSubst
  env <- unsafeGetEnv
  withDistinct $ return $ substStuck (env, subst) stuck

substStuck :: (IRRep r, Distinct o) => (Env o, Subst AtomSubstVal i o) -> Stuck r i -> Atom r o
substStuck (env, subst) stuck =
  ignoreExcept $ runEnvReaderT env $ runSubstReaderT subst $ reduceStuck stuck

reduceStuck :: (IRRep r, Distinct o) => Stuck r i -> ReducerM i o (Atom r o)
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
  LiftSimp t s -> do
    t' <- substM t
    s' <- reduceStuck s
    liftSimpAtom t' s'
  LiftSimpFun t f -> mkStuck =<< (LiftSimpFun <$> substM t <*> substM f)
  TabLam lam -> mkStuck =<< (TabLam <$> substM lam)
  ACase scrut alts resultTy -> do
    scrut' <- reduceStuck scrut
    resultTy' <- substM resultTy
    alts' <- mapM substM alts
    reduceACaseM scrut' alts' resultTy'

liftSimpAtom :: EnvReader m => Type CoreIR n -> SAtom n -> m n (CAtom n)
liftSimpAtom (StuckTy _ _) _ = error "Can't lift stuck type"
liftSimpAtom ty@(TyCon tyCon) simpAtom = case simpAtom of
  Stuck _ stuck -> return $ Stuck ty $ LiftSimp ty stuck
  Con con -> Con <$> case (tyCon, con) of
    (NewtypeTyCon newtypeCon, _) -> do
      (dataCon, repTy) <- unwrapNewtypeType newtypeCon
      cAtom <- rec repTy (Con con)
      return $ NewtypeCon dataCon cAtom
    (BaseType _  , Lit v)      -> return $ Lit v
    (ProdType tys, ProdCon xs)   -> ProdCon <$> zipWithM rec tys xs
    (SumType  tys, SumCon _ i x) -> SumCon tys i <$> rec (tys!!i) x
    (DepPairTy dpt@(DepPairType _ (b:>t1) t2), DepPair x1 x2 _) -> do
      x1' <- rec t1 x1
      t2' <- applySubst (b@>SubstVal x1') t2
      x2' <- rec t2' x2
      return $ DepPair x1' x2' dpt
    _ -> error $ "can't lift " <> pprint simpAtom <> " to " <> pprint ty
  where
    rec = liftSimpAtom
{-# INLINE liftSimpAtom #-}

instance IRRep r => SubstE AtomSubstVal (EffectRow r) where
  substE env (EffectRow effs tailVar) = do
    let effs' = eSetFromList $ map (substE env) (eSetToList effs)
    let tailEffRow = case tailVar of
          NoTail -> EffectRow mempty NoTail
          EffectRowTail (AtomVar v _) -> case snd env ! v of
            Rename        v'  -> do
              let v'' = runEnvReaderM (fst env) $ toAtomVar v'
              EffectRow mempty (EffectRowTail v'')
            SubstVal (Stuck _ (Var v')) -> EffectRow mempty (EffectRowTail v')
            SubstVal (Con (Eff r))  -> r
            _ -> error "Not a valid effect substitution"
    extendEffRow effs' tailEffRow

instance IRRep r => SubstE AtomSubstVal (Effect r)

instance SubstE AtomSubstVal SpecializationSpec where
  substE env (AppSpecialization (AtomVar f _) ab) = do
    let f' = case snd env ! f of
               Rename v -> runEnvReaderM (fst env) $ toAtomVar v
               SubstVal (Stuck _ (Var v)) -> v
               _ -> error "bad substitution"
    AppSpecialization f' (substE env ab)

instance SubstE AtomSubstVal EffectDef
instance SubstE AtomSubstVal EffectOpType
instance SubstE AtomSubstVal IExpr
instance SubstE AtomSubstVal RepVal
instance SubstE AtomSubstVal TyConParams
instance SubstE AtomSubstVal DataConDef
instance IRRep r => SubstE AtomSubstVal (BaseMonoid r)
instance IRRep r => SubstE AtomSubstVal (DAMOp r)
instance IRRep r => SubstE AtomSubstVal (TypedHof r)
instance IRRep r => SubstE AtomSubstVal (Hof r)
instance IRRep r => SubstE AtomSubstVal (TyCon r)
instance IRRep r => SubstE AtomSubstVal (DictCon r)
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
instance IRRep r => SubstE AtomSubstVal (IxType r)
instance SubstE AtomSubstVal DataConDefs
