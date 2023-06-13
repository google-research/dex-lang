-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module Visit
  ( NonAtomRenamer (..), Visitor (..), VisitGeneric (..)
  , visitAtomPartial, visitTypePartial, Visitor2, visitAlt
  , IsAtomName)
  where

import Data.Functor ((<&>))

import IRVariants
import Name
import PPrint ()
import Types.Core
import Types.Imp
import Types.Primitives

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

type family IsAtomName (c::C) where
  IsAtomName (AtomNameC r) = True
  IsAtomName _             = False

instance VisitGeneric (Atom    r) r where visitGeneric = visitAtom
instance VisitGeneric (Type    r) r where visitGeneric = visitType
instance VisitGeneric (LamExpr r) r where visitGeneric = visitLam
instance VisitGeneric (PiType  r) r where visitGeneric = visitPi

instance VisitGeneric (Block r) r where
  visitGeneric b = visitGeneric (LamExpr Empty b) >>= \case
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

-- XXX: This doesn't handle the `Var`, `ProjectElt`, `SimpInCore` cases. These
-- should be handled explicitly beforehand. TODO: split out these cases under a
-- separate constructor, perhaps even a `hole` paremeter to `Atom` or part of
-- `IR`.
visitAtomPartial :: (IRRep r, Visitor m r i o) => Atom r i -> m (Atom r o)
visitAtomPartial = \case
  Var _          -> error "Not handled generically"
  SimpInCore _   -> error "Not handled generically"
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
    -- Case x alts (EffTy _ t) -> do
    --   x' <- visitGeneric x
    --   t' <- visitGeneric t
    --   alts' <- mapM visitAlt alts
    --   let effs' = foldMap altEffects alts'
    --   return $ Case x' alts' $ EffTy effs' t'
    --   where
    --     altEffects :: Alt r n -> EffectRow r n
    --     altEffects (Abs bs (Block ann _ _)) = case ann of
    --       NoBlockAnn -> Pure
    --       BlockAnn (EffTy effs _) -> ignoreHoistFailure $ hoist bs effs
    Atom x -> Atom <$> visitGeneric x
    TabCon Nothing t xs -> TabCon Nothing <$> visitGeneric t <*> mapM visitGeneric xs
    TabCon (Just (WhenIRE d)) t xs -> TabCon <$> (Just . WhenIRE <$> visitGeneric d) <*> visitGeneric t <*> mapM visitGeneric xs
    PrimOp op -> PrimOp <$> visitGeneric op
    App et fAtom xs -> App <$> visitGeneric et <*> visitGeneric fAtom <*> mapM visitGeneric xs
    ApplyMethod et m i xs -> ApplyMethod <$> visitGeneric et <*> visitGeneric m <*> pure i <*> mapM visitGeneric xs
    ProjectElt t p x -> ProjectElt <$> visitType t <*> pure p <*> visitAtom x

instance IRRep r => VisitGeneric (PrimOp r) r where
  visitGeneric = \case
    UnOp     op x   -> UnOp  op <$> visitGeneric x
    BinOp    op x y -> BinOp op <$> visitGeneric x <*> visitGeneric y
    MemOp        op -> MemOp    <$> visitGeneric op
    VectorOp     op -> VectorOp     <$> visitGeneric op
    MiscOp       op -> MiscOp       <$> visitGeneric op
    Hof          op -> Hof          <$> visitGeneric op
    DAMOp        op -> DAMOp        <$> visitGeneric op
    UserEffectOp op -> UserEffectOp <$> visitGeneric op
    RefOp r op  -> RefOp <$> visitGeneric r <*> traverseOp op visitGeneric visitGeneric visitGeneric

instance IRRep r => VisitGeneric (TypedHof r) r where
  visitGeneric (TypedHof eff hof) = TypedHof <$> visitGeneric eff <*> visitGeneric hof

instance IRRep r => VisitGeneric (Hof r) r where
  visitGeneric = \case
    For ann d lam -> For ann <$> visitGeneric d <*> visitGeneric lam
    RunReader x body -> RunReader <$> visitGeneric x <*> visitGeneric body
    RunWriter dest bm body -> RunWriter <$> mapM visitGeneric dest <*> visitGeneric bm <*> visitGeneric body
    RunState  dest s body ->  RunState  <$> mapM visitGeneric dest <*> visitGeneric s <*> visitGeneric body
    While          b -> While          <$> visitGeneric b
    RunIO          b -> RunIO          <$> visitGeneric b
    RunInit        b -> RunInit        <$> visitGeneric b
    CatchException t b -> CatchException <$> visitType t <*> visitGeneric b
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

instance VisitGeneric UserEffectOp CoreIR where
  visitGeneric = \case
    Handle name xs body -> Handle <$> renameN name <*> mapM visitGeneric xs <*> visitGeneric body
    Resume t x -> Resume <$> visitGeneric t <*> visitGeneric x
    Perform x i -> Perform <$> visitGeneric x <*> pure i

instance IRRep r => VisitGeneric (Effect r) r where
  visitGeneric = \case
    RWSEffect rws h    -> RWSEffect rws <$> visitGeneric h
    ExceptionEffect    -> pure ExceptionEffect
    IOEffect           -> pure IOEffect
    UserEffect name    -> UserEffect <$> renameN name
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
  visitGeneric (CorePiType app bsExpl effty) = do
    let (expls, bs) = unzipExpls bsExpl
    PiType bs' effty' <- visitGeneric $ PiType bs effty
    let bsExpl' = zipExpls expls bs'
    return $ CorePiType app bsExpl' effty'

instance IRRep r => VisitGeneric (TabPiType r) r where
  visitGeneric (TabPiType d b (WithDecls ds eltTy)) = do
    d' <- visitGeneric d
    visitGeneric (PiType (UnaryNest b) (WithDecls ds (EffTy Pure eltTy))) <&> \case
      PiType (UnaryNest b') (WithDecls ds' (EffTy Pure eltTy')) ->
        TabPiType d' b' (WithDecls ds' eltTy')
      _ -> error "not a table pi type"

instance IRRep r => VisitGeneric (DepPairType r) r where
  visitGeneric (DepPairType expl b (WithDecls ds ty)) = do
    visitGeneric (PiType (UnaryNest b) (WithDecls ds (EffTy Pure ty))) <&> \case
      PiType (UnaryNest b') (WithDecls ds' (EffTy Pure ty')) -> DepPairType expl b' (WithDecls ds' ty')
      _ -> error "not a dependent pair type"

instance VisitGeneric (RepVal SimpIR) SimpIR where
  visitGeneric (RepVal ty tree) = RepVal <$> visitGeneric ty <*> mapM renameIExpr tree
    where renameIExpr = \case
            ILit l -> return $ ILit l
            IVar    v t -> IVar    <$> renameN v <*> pure t
            IPtrVar v t -> IPtrVar <$> renameN v <*> pure t

instance IRRep r => VisitGeneric (DeclBinding r) r where
  visitGeneric (DeclBinding ann expr) = DeclBinding ann <$> visitGeneric expr

instance (IRRep r, VisitGeneric e r) => VisitGeneric (WithDecls r e) r where
  visitGeneric = undefined

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
    PiType bs' _  <- visitGeneric $ PiType bs $ WithoutDecls $ EffTy Pure UnitTy
    repTy' <- visitGeneric repTy
    return $ DataConDef sn (Abs bs' UnitE) repTy' ps

instance VisitGeneric (Con      r) r where visitGeneric = traverseOpTerm
instance VisitGeneric (TC       r) r where visitGeneric = traverseOpTerm
instance VisitGeneric (MiscOp   r) r where visitGeneric = traverseOpTerm
instance VisitGeneric (VectorOp r) r where visitGeneric = traverseOpTerm
instance VisitGeneric (MemOp    r) r where visitGeneric = traverseOpTerm

