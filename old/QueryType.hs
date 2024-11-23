-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module QueryType (module QueryType, module QueryTypePure, toAtomVar) where

import Control.Category ((>>>))
import Control.Monad
import Control.Applicative
import Data.List (elemIndex)
import Data.Maybe (fromJust)
import Data.Functor ((<&>))

import Types.Primitives
import Types.Complicated
import Types.Simple
import Types.Source hiding (TCName (..))
import Types.Top2
import Types.Imp
import Name hiding (withFreshM)
-- import Subst
import Util
import PPrint
import QueryTypePure

-- === Exposed helpers for querying types and effects ===

caseAltsBinderTys :: ScopeReader m => Type n -> m n [Type n]
caseAltsBinderTys ty = case ty of
  TyCon (SumType types) -> return types -- need this case?
  TyCon (NewtypeTyCon t) -> case t of
    UserADTType _ defName params -> do
      def <- lookupTyCon defName
      ~(ADTCons cons) <- instantiateTyConDef def params
      return [repTy | DataConDef _ _ repTy _ <- cons]
    _ -> error msg
  _ -> error msg
  where msg = "Case analysis only supported on ADTs, not on " ++ pprint ty

piTypeWithoutDest :: PiType n -> PiType n
piTypeWithoutDest (PiType bsRefB _) =
  case popNest bsRefB of
    Just (PairB bs (_:>RefTy ansTy)) -> PiType bs ansTy
    _ -> error "expected trailing dest binder"

typeOfTabApp :: ScopeReader m => Type n -> Atom n -> m n (Type n)
typeOfTabApp (TyCon (TabPi tabTy)) i = instantiate tabTy [i]
typeOfTabApp ty _ = error $ "expected a table type. Got: " ++ pprint ty

typeOfApplyMethod :: ScopeReader m => CDict n -> Int -> [CAtom n] -> m n (EffTy n)
typeOfApplyMethod d i args = do
  ty <- toType <$> getMethodType d i
  appEffTy ty args

typeOfTopApp :: ScopeReader m => TopFunName n -> [SAtom n] -> m n (EffTy n)
typeOfTopApp f xs = do
  piTy <- getTypeTopFun f
  ty <- instantiate piTy xs
  return $ EffTy undefined ty  -- TODO

typeOfIndexRef :: (ScopeReader m, Fallible1 m) => Type n -> Atom n -> m n (Type n)
typeOfIndexRef (TyCon (RefType s)) i = do
  TyCon (TabPi tabPi) <- return s
  eltTy <- instantiate tabPi [i]
  return $ toType $ RefType eltTy
typeOfIndexRef _ _ = error "expected a ref type"

typeOfProjRef :: ScopeReader m => Type n -> Projection -> m n (Type n)
typeOfProjRef (TyCon (RefType s)) p = do
  toType . RefType <$> case p of
    ProjectProduct i -> do
      ~(TyCon (ProdType tys)) <- return s
      return $ tys !! i
    UnwrapNewtype -> do
      case s of
        TyCon (NewtypeTyCon tc) -> snd <$> unwrapNewtypeType tc
        _ -> error "expected a newtype"
typeOfProjRef _ _ = error "expected a reference"

appEffTy  :: ScopeReader m => Type n -> [Atom n] -> m n (EffTy n)
appEffTy (TyCon (Pi piTy)) xs = do
  ty <- instantiate piTy xs
  return $ EffTy Effectful ty  -- TODO: don't assume Effectful
appEffTy t _ = error $ "expected a pi type, got: " ++ pprint t

partialAppType  :: ScopeReader m => Type n -> [Atom n] -> m n (Type n)
partialAppType (TyCon (Pi (CorePiType appExpl expls bs effTy))) xs = do
  (_, expls2) <- return $ splitAt (length xs) expls
  PairB bs1 bs2 <- return $ splitNestAt (length xs) bs
  instantiate (Abs bs1 (toType $ CorePiType appExpl expls2 bs2 effTy)) xs
partialAppType _ _ = error "expected a pi type"

typeOfHof :: ScopeReader m => Hof n -> m n (Type n)
typeOfHof = \case
  For _ ixTy f -> getLamExprType f >>= \case
    Abs (UnaryNest b) eltTy -> return $ TabTy (ixTypeDict ixTy) b eltTy
    _ -> error "expected a unary pi type"
  While _ -> return UnitTy

getMethodIndex :: ScopeReader m => ClassName n -> SourceName -> m n Int
getMethodIndex className methodSourceName = do
  ClassDef _ _ methodNames _ _ _ _ _ <- lookupClassDef className
  case elemIndex methodSourceName methodNames of
    Nothing -> error $ pprint methodSourceName ++ " is not a method of " ++ pprint className
    Just i -> return i
{-# INLINE getMethodIndex #-}

getMethodNameType :: ScopeReader m => TopName -> m n (CType n)
getMethodNameType v = undefined -- liftScopeReaderM $ lookupEnv v >>= \case
-- getMethodNameType v = liftScopeReaderM $ lookupEnv v >>= \case
--   MethodBinding className i -> do
--     ClassDef _ _ _ paramNames _ paramBs scBinders methodTys <- lookupClassDef className
--     refreshAbs (Abs paramBs $ Abs scBinders (methodTys !! i)) \paramBs' absPiTy -> do
--       let params = toAtom <$> bindersVars paramBs'
--       dictTy <- toType <$> dictType (sink className) params
--       withFreshBinder noHint dictTy \dictB -> do
--         scDicts <- getSuperclassDicts (toDict $ binderVar dictB)
--         CorePiType appExpl methodExpls methodBs effTy <- instantiate (sink absPiTy) scDicts
--         let paramExpls = paramNames <&> \name -> Inferred name Unify
--         let expls = paramExpls <> [Inferred Nothing (Synth $ Partial $ succ i)] <> methodExpls
--         return $ toType $ CorePiType appExpl expls (paramBs' >>> UnaryNest dictB >>> methodBs) effTy

getMethodType :: ScopeReader m => Dict n -> Int -> m n (CorePiType n)
getMethodType dict i = undefined
-- getMethodType dict i = do
--   ~(TyCon (DictTy dictTy)) <- return $ getType dict
--   case dictTy of
--     DictType _ className params -> liftScopeReaderM $ withSubstReaderT do
--       superclassDicts <- getSuperclassDicts dict
--       classDef <- lookupClassDef className
--       withInstantiated classDef params \ab -> do
--         withInstantiated ab superclassDicts \(ListE methodTys) ->
--           substM $ methodTys !! i
--     IxDictType ixTy -> liftScopeReaderM case i of
--       0 -> mkCorePiType []      NatTy -- size' : () -> Nat
--       1 -> mkCorePiType [ixTy]  NatTy -- ordinal : (n) -> Nat
--       2 -> mkCorePiType [NatTy] ixTy  -- unsafe_from_ordinal : (Nat) -> n
--       _ -> error "Ix only has three methods"

mkCorePiType :: ScopeReader m => [CType n] -> CType n -> m n (CorePiType n)
mkCorePiType argTys resultTy = liftScopeReaderM $ withFreshBinders argTys \bs _ -> do
  expls <- return $ nestToList (const Explicit) bs
  return $ CorePiType ExplicitApp expls bs (sink resultTy)

getTyConNameType :: ScopeReader m => TyConName n -> m n (Type n)
getTyConNameType v = do
  TyConDef _ expls bs _ <- lookupTyCon v
  case bs of
    Empty -> return $ toType $ Kind TypeKind
    _ -> return $ toType $ CorePiType ExplicitApp expls bs $ toType $ Kind TypeKind

type DataConName = TopName
getDataConNameType :: ScopeReader m => DataConName -> m n (Type VoidS)
getDataConNameType dataCon = liftScopeReaderM $ withSubstReaderT do
  (tyCon, i) <- lookupDataCon dataCon
  tyConDef <- lookupTyCon tyCon
  buildDataConType tyConDef \expls paramBs' paramVs params -> do
    withInstantiatedNames tyConDef paramVs \(ADTCons dataCons) -> do
      DataConDef _ ab _ _ <- renameM (dataCons !! i)
      refreshAbs ab \dataBs UnitE -> do
        let appExpl = case dataBs of Empty -> ImplicitApp
                                     _     -> ExplicitApp
        let resultTy = toType $ UserADTType (getSourceName tyConDef) (sink tyCon) (sink params)
        let dataExpls = nestToList (const $ Explicit) dataBs
        return $ toType $ CorePiType appExpl (expls <> dataExpls) (paramBs' >>> dataBs) resultTy

getStructDataConType :: ScopeReader m => TyConName n -> m n (CType n)
getStructDataConType tyCon = liftScopeReaderM $ withSubstReaderT do
  tyConDef <- lookupTyCon tyCon
  buildDataConType tyConDef \expls paramBs' paramVs params -> do
    withInstantiatedNames tyConDef paramVs \(StructFields fields) -> do
      fieldTys <- forM fields \(_, t) -> renameM t
      let resultTy = toType $ UserADTType (getSourceName tyConDef) (sink tyCon) params
      Abs dataBs resultTy' <- return $ typesAsBinderNest fieldTys resultTy
      let dataExpls = nestToList (const Explicit) dataBs
      return $ toType $ CorePiType ExplicitApp (expls <> dataExpls) (paramBs' >>> dataBs) resultTy'

buildDataConType
  :: (ScopeReader m)
  => TyConDef n
  -> (forall l. DExt n l => [Explicitness] -> Nest CBinder n l -> [Name l] -> TyConParams l -> m l a)
  -> m n a
buildDataConType (TyConDef _ expls bs _) cont = undefined
-- buildDataConType (TyConDef _ expls bs _) cont = do
--   expls' <- forM expls \case
--     Explicit -> return $ Inferred Nothing Unify
--     expl     -> return $ expl
--   refreshAbs (Abs bs UnitE) \bs' UnitE -> do
--     let vs = nestToNames bs'
--     vs' <- mapM toAtomVar vs
--     cont expls' bs' vs $ TyConParams expls (toAtom <$> vs')

makeTyConParams :: ScopeReader m => TyConName n -> [CExpr n] -> m n (TyConParams n)
makeTyConParams tc params = do
  TyConDef _ expls _ _ <- lookupTyCon tc
  return $ TyConParams expls params

getSuperclassDicts :: ScopeReader m => CExpr n -> m n ([CExpr n])
getSuperclassDicts dict = undefined
-- getSuperclassDicts dict = do
--   case getType dict of
--     TyCon (DictTy dTy) -> do
--       ts <- getSuperclassTys dTy
--       forM (enumerate ts) \(i, _) -> reduceSuperclassProj i dict
--     _ -> error "expected a dict type"

getSuperclassTys :: ScopeReader m => DictType n -> m n [CType n]
getSuperclassTys = \case
  DictType _ className params -> do
    ClassDef _ _ _ _ _ bs superclasses _ <- lookupClassDef className
    forM [0 .. nestLength superclasses - 1] \i -> do
      instantiate (Abs bs $ getSuperclassType REmpty superclasses i) params
  IxDictType _ -> return []

asTopLam :: ScopeReader m => LamExpr n -> m n (TopLam n)
asTopLam lam = do
  piTy <- getLamExprType lam
  return $ TopLam False piTy lam
