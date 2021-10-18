-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}

module Inference (inferModule, synthModule) where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State.Strict
import Control.Monad.Writer.Strict hiding (Alt)
import Data.Maybe (fromJust, maybeToList)
import Data.Foldable (fold, toList)
import Data.Functor
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.String (fromString)
import Data.Text.Prettyprint.Doc
import Data.List (nubBy, partition, sortOn)

import LabeledItems
import Syntax
import Interpreter (indicesNoIO)
import Builder  hiding (sub)
import Env
import Type
import PPrint
import Cat
import Util
import Err

data UInferEnv = UInferEnv
  { inferSubst        :: SubstEnv
  , srcCtx            :: SrcPosCtx
  , protoludeScope    :: ProtoludeScope
  }
type UInferM = ReaderT UInferEnv (BuilderT (SolverT Except))

type SigmaType = Type  -- may     start with an implicit lambda
type RhoType   = Type  -- doesn't start with an implicit lambda
data RequiredTy a = Concrete a | Suggest a | Infer deriving (Show, Functor, Foldable, Traversable)

pattern Check :: a -> RequiredTy a
pattern Check t <-
  ((\case Concrete t -> Just t
          Suggest  t -> Just t
          Infer      -> Nothing) -> Just t)
  where Check t = Suggest t

{-# COMPLETE Infer, Check #-}

inferModule :: Bindings -> SynthCandidates -> UModule -> ProtoludeScope -> Except Module
inferModule scope scs (UModule uDecl sourceMap) protolude = do
  (evaluated, ((bindings, synthCandidates), decls)) <- runUInferM mempty scope scs protolude do
    substEnv <- inferUDecl uDecl
    substBuilder substEnv $ EvaluatedModule mempty mempty sourceMap
  let evaluated' = addSynthCandidates evaluated synthCandidates
  if requiresEvaluation
    then return $ Module Typed decls evaluated'
    else do
      unless (null decls) $ throw CompilerErr $ "Unexpected decls: " ++ pprint decls
      return $ Module Typed Empty $ prependBindings bindings evaluated'
  where
    requiresEvaluation = case uDecl of
      ULet         _ _ _     -> True
      UInstance    _ _ _ _ _ -> True
      UDataDefDecl _ _ _     -> False
      UInterface   _ _ _ _ _ -> False

-- TODO: bindings' might shadow names in bindings, so we should do this more
-- carefully. But the way we use it here is probably ok, and we're about to swap
-- it out for the type-checked naming system which will force us to do the right
-- thing anyway.
prependBindings :: Bindings -> EvaluatedModule -> EvaluatedModule
prependBindings bindings (EvaluatedModule bindings' scs sourceMap) =
  EvaluatedModule (bindings <> bindings') scs sourceMap

-- TODO: sinking the synth candidates underneath the bindings is sketchy
-- shadowing-wise but, as above it seems ok here. The safer-names system will
-- fix it up.
addSynthCandidates :: EvaluatedModule -> SynthCandidates -> EvaluatedModule
addSynthCandidates (EvaluatedModule bindings scsPrev sourceMap) scs =
  EvaluatedModule bindings (scs <> scsPrev) sourceMap

runUInferM :: (HasVars a, Subst a, Pretty a)
           => SubstEnv -> Scope -> SynthCandidates -> ProtoludeScope
           -> UInferM a -> Except (a, ((Scope, SynthCandidates), Nest Decl))
runUInferM env scope scs protolude m = runSolverT $ do
  runBuilderT scope scs $ runReaderT m $ UInferEnv env Nothing protolude

checkSigma :: UExpr -> (Type -> RequiredTy Type) -> SigmaType -> UInferM Atom
checkSigma expr reqCon sTy = case sTy of
  Pi piTy@(Abs _ (arrow, _))
    | arrow `elem` [ImplicitArrow, ClassArrow] -> case expr of
        WithSrc _ (ULam b arrow' body) | arrow' == void arrow ->
          checkULam b body piTy
        _ -> do
          buildLam (Bind ("a":> absArgType piTy)) arrow \x@(Var v) ->
            checkLeaks [v] $ checkSigma expr reqCon $ snd $ applyAbs piTy x
  _ -> checkOrInferRho expr (reqCon sTy)

inferSigma :: UExpr -> UInferM Atom
inferSigma (WithSrc pos expr) = case expr of
  ULam pat ImplicitArrow body -> addSrcContext' pos $
    inferULam pat ImplicitArrow body
  _ ->
    inferRho (WithSrc pos expr)

checkRho :: UExpr -> RhoType -> UInferM Atom
checkRho expr ty = checkOrInferRho expr (Check ty)

inferRho :: UExpr -> UInferM Atom
inferRho expr = checkOrInferRho expr Infer

instantiateSigma :: Atom -> UInferM Atom
instantiateSigma f = do
  ty <- tryGetType f
  case ty of
    Pi (Abs b (ImplicitArrow, _)) -> do
      x <- freshType $ binderType b
      ans <- emitZonked $ App f x
      instantiateSigma ans
    Pi (Abs b (ClassArrow, _)) -> do
      ctx <- getSrcCtx
      instantiateSigma =<< emitZonked (App f (Con $ ClassDictHole ctx $ binderType b))
    _ -> return f

checkOrInferRho :: UExpr -> RequiredTy RhoType -> UInferM Atom
checkOrInferRho (WithSrc pos expr) reqTy = do
 addSrcContext' pos $ case expr of
  UVar v -> lookupUVar v >>= instantiateSigma >>= matchRequirement
  ULam (UPatAnn p ann) ImplicitArrow body -> do
    argTy <- checkAnn ann
    Var v <- freshType argTy
    withBindPat p v $ checkOrInferRho body reqTy
  ULam b arr body -> do
    let infer = inferULam b (fmap (const Pure) arr) body
    case reqTy of
      Check (Pi piTy@(Abs _ (arrReq, _))) -> do
        checkArrow arrReq arr
        checkULam b body piTy
      Check _ -> infer >>= matchRequirement
      Infer   -> infer
  UFor dir b body -> do
    let infer = do
          allowedEff <- getAllowedEffects
          lam <- inferULam b (PlainArrow allowedEff) body
          emitZonked $ Hof $ For (RegularFor dir) lam
    case reqTy of
      Check (Pi (Abs n (arr, a))) -> do
        unless (arr == TabArrow) $
          throw TypeErr $ "Not an table arrow type: " ++ pprint arr
        allowedEff <- getAllowedEffects
        lam <- checkULam b body $ Abs n (PlainArrow allowedEff, a)
        emitZonked $ Hof $ For (RegularFor dir) lam
      Check _ -> infer >>= matchRequirement
      Infer   -> infer
  UApp arr f x@(WithSrc xPos _) -> do
    fVal <- inferRho f
    -- NB: We never infer dependent function types, but we accept them, provided they
    --     come with annotations. So, unless we already know that the function is
    --     dependent here (i.e. the type of the zonk comes as a dependent Pi type),
    --     then nothing in the remainder of the program can convince us that the type
    --     is dependent. Also, the Pi binder is never considered to be in scope for
    --     inference variables, so they cannot get unified with it. Hence, this zonk
    --     is safe and doesn't make the type checking depend on the program order.
    infTy <- getType <$> zonk fVal
    piTy  <- addSrcContext' (srcPos f) $ fromPiType True arr infTy
    (xVal, builderEnv@(_, xDecls)) <- builderScoped $ checkSigma x Suggest (absArgType piTy)
    (xVal', arr') <- case piTy of
      Abs b rhs@(arr', _) -> case b `isin` freeVars rhs of
        False -> builderExtend builderEnv $> (xVal, arr')
        True  -> do
          let msg = "Dependent functions can only be applied to fully " ++
                    "evaluated expressions. Bind the argument to a name " ++
                    "before you apply the function."
          xValRed <- typeReductionAsAtom xPos msg =<<
            (getScope <&> \s -> typeReduceBlock s (Block xDecls (Atom xVal)))
          return (xValRed, fst $ applyAbs piTy xValRed)
    addEffects $ arrowEff arr'
    appVal <- emitZonked $ App fVal xVal'
    instantiateSigma appVal >>= matchRequirement
  UPi (UPatAnn (WithSrc pos' pat) ann) arr ty -> do
    -- TODO: make sure there's no effect if it's an implicit or table arrow
    -- TODO: check leaks
    ann' <- checkAnn ann
    piTy <- addSrcContext' pos' case pat of
      UPatBinder UIgnore -> buildPi (Ignore ann') $ const $
                          (,) <$> mapM checkUEffRow arr <*> checkUType ty
      _ -> withNameHint ("pat" :: Name) $ buildPi b \(Var v) ->
        withBindPat (WithSrc pos' pat) v $ (,) <$> mapM checkUEffRow arr <*> checkUType ty
        where b = case pat of
                    -- Note: The binder name becomes part of the type, so we
                    -- need to keep the same name used in the pattern.
                    UPatBinder (UBind v) -> Bind (v:>ann')
                    _ -> Ignore ann'
    matchRequirement piTy
  UDecl decl body -> do
    env <- inferUDecl decl
    extInferSubst env $ checkOrInferRho body reqTy
  UCase scrut alts -> do
    scrut' <- inferRho scrut
    let scrutTy = getType scrut'
    reqTy' <- case reqTy of
      Infer -> freshType TyKind
      Check req -> return req
    alts' <- mapM (checkCaseAlt reqTy' scrutTy) alts
    scrutTy' <- zonk scrutTy
    scrut'' <- zonk scrut'
    case scrutTy' of
      TypeCon (_, def) params -> do
        let conDefs = applyDataDefParams def params
        altsSorted <- forM (enumerate conDefs) \(i, DataConDef _ bs) -> do
          case lookup (ConAlt i) alts' of
            Nothing  -> return $ Abs (fmap (Ignore . binderType) bs) $
                                  Block Empty $ Op $ ThrowError reqTy'
            Just alt -> return alt
        emit $ Case scrut'' altsSorted reqTy'
      VariantTy (Ext types@(LabeledItems tyItems) tailName) -> do
        let unhandledCase :: Type -> Alt
            unhandledCase ty = Abs (toNest [Ignore ty]) $
                              Block Empty $ Op $ ThrowError reqTy'
        let buildMonomorphicCase :: LabeledItems Type -> Atom -> UInferM Atom
            buildMonomorphicCase monoTypes monoScrut = do
              altsSorted <- forM (toList (withLabels monoTypes)) $
                \(l, i, ty) -> case lookup (VariantAlt l i) alts' of
                    Nothing  -> return $ unhandledCase ty
                    Just alt -> return alt
              emit $ Case monoScrut altsSorted reqTy'
        let isVariantTailAlt (VariantTailAlt _) = True
            isVariantTailAlt _ = False
        case filter (isVariantTailAlt . fst) alts' of
          [] -> case tailName of
            Nothing ->
              -- We already know the type exactly, so just emit a case.
              buildMonomorphicCase types scrut''
            Just _ -> do
              -- Split off the types we don't know about, mapping them to a
              -- runtime error.
              split <- emit $ Op $ VariantSplit types scrut''
              VariantTy (NoExt (Unlabeled [leftTy, rightTy])) <-
                return $ getType split
              leftCase <- buildNAbs (toNest [Ignore leftTy])
                                    (\[v] -> buildMonomorphicCase types v)
              emit $ Case split [leftCase, unhandledCase rightTy] reqTy'
          [(VariantTailAlt (LabeledItems skippedItems), tailAlt)] -> do
            -- Split off the types skipped by the tail pattern.
            let splitLeft fvs ltys = NE.fromList $ NE.take (length ltys) fvs
                left = M.intersectionWith splitLeft tyItems skippedItems
            -- Make sure all of the alternatives are exclusive with the tail
            -- pattern (could technically allow overlap but this is simpler).
            let overlapErr = throw TypeErr
                  "Variant explicit alternatives overlap with tail pattern."
            let checkAltAgainstTail :: CaseAltIndex -> UInferM ()
                checkAltAgainstTail (VariantAlt label i) =
                  case M.lookup label left of
                    Just tys -> if i <= length tys
                                then return ()
                                else overlapErr
                    Nothing -> overlapErr
                checkAltAgainstTail _ = return ()
            mapM_ (checkAltAgainstTail . fst) alts'
            -- Split based on the tail pattern's skipped types.
            split <- emit $ Op $ VariantSplit (LabeledItems left) scrut''
            let leftTy = VariantTy $ NoExt $ LabeledItems left
            leftCase <-
              buildNAbs (toNest [Ignore leftTy])
                (\[v] -> buildMonomorphicCase (LabeledItems left) v)
            emit $ Case split [leftCase, tailAlt] reqTy'
          _ -> throw TypeErr "Can't specify more than one variant tail pattern."
      _ -> fail $ "Unexpected case expression type: " <> pprint scrutTy'
  UTabCon xs -> inferTabCon pos xs reqTy >>= matchRequirement
  UIndexRange low high -> do
    n <- freshType TyKind
    low'  <- mapM (flip checkRho n) low
    high' <- mapM (flip checkRho n) high
    matchRequirement $ TC $ IndexRange n low' high'
  UHole -> case reqTy of
    Infer -> throw MiscErr "Can't infer type of hole"
    Check ty -> freshType ty
  UTypeAnn val ty -> do
    ty' <- zonk =<< checkUType ty
    let reqCon = if null (toList $ freeVars ty') then Concrete else Suggest
    val' <- checkSigma val reqCon ty'
    matchRequirement val'
  UPrimExpr prim -> do
    prim' <- forM prim \e -> do
      e' <- inferRho e
      scope <- getScope
      return $ typeReduceAtom scope e'
    val <- case prim' of
      TCExpr  e -> return $ TC e
      ConExpr e -> return $ Con e
      OpExpr  e -> emitZonked $ Op e
      HofExpr e -> emitZonked $ Hof e
    matchRequirement val
  URecord (Ext items Nothing) -> do
    items' <- mapM inferRho items
    matchRequirement $ Record items'
  URecord (Ext items (Just ext)) -> do
    items' <- mapM inferRho items
    restTy <- freshInferenceName LabeledRowKind
    ext' <- zonk =<< (checkRho ext $ RecordTy $ Ext NoLabeledItems $ Just restTy)
    matchRequirement =<< emit (Op $ RecordCons items' ext')
  UVariant labels@(LabeledItems lmap) label value -> do
    value' <- inferRho value
    prevTys <- mapM (const $ freshType TyKind) labels
    rest <- freshInferenceName LabeledRowKind
    let items = prevTys <> labeledSingleton label (getType value')
    let extItems = Ext items $ Just rest
    let i = case M.lookup label lmap of
              Just prev -> length prev
              Nothing -> 0
    matchRequirement $ Variant extItems label i value'
  URecordTy row -> matchRequirement =<< RecordTy <$> checkExtLabeledRow row
  UVariantTy row -> matchRequirement =<< VariantTy <$> checkExtLabeledRow row
  UVariantLift labels value -> do
    row <- freshInferenceName LabeledRowKind
    value' <- zonk =<< (checkRho value $ VariantTy $ Ext NoLabeledItems $ Just row)
    prev <- mapM (\() -> freshType TyKind) labels
    matchRequirement =<< emit (Op $ VariantLift prev value')
  UIntLit  x  -> do
    fromIntegerName <- protoludeFromIntegerMethod <$> asks protoludeScope
    fromIntegerFunc <- inferRho $ WithSrc Nothing $ UVar $ UInternalVar fromIntegerName
    let FunTy _ _ a = getType fromIntegerFunc
    registerDefault a Int32Ty
    matchRequirement =<< app fromIntegerFunc (Con $ Lit  $ Int64Lit $ fromIntegral x)
  UFloatLit x -> matchRequirement $ Con $ Lit  $ Float32Lit $ realToFrac x
  -- TODO: Make sure that this conversion is not lossy!
  where
    matchRequirement :: Atom -> UInferM Atom
    matchRequirement x = return x <*
      case reqTy of
        Infer -> return ()
        Check req -> constrainEq req (getType x)

lookupUVar :: UVar -> UInferM Atom
lookupUVar (USourceVar _) = error "Shouldn't have source names left"
lookupUVar (UInternalVar v) = do
  substEnv <- getInferSubst
  scope <- getScope
  case envLookup substEnv v of
    Nothing -> return $ fromJust $ nameToAtom scope v
    Just (Rename  v') -> return $ fromJust $ nameToAtom scope v'
    Just (SubstVal x) -> return x

inferUDecl ::  UDecl -> UInferM SubstEnv
inferUDecl (ULet letAnn (UPatAnn p ann) rhs) = do
  val <- withPatHint p case ann of
    Nothing -> inferSigma rhs
    Just ty -> do
      ty' <- zonk =<< checkUType ty
      let reqCon = if null (toList $ freeVars ty') then Concrete else Suggest
      checkSigma rhs reqCon ty'
  expr <- zonk $ Atom val
  var <- withPatHint p $ emitAnn letAnn expr
  bindPat p var
inferUDecl (UDataDefDecl def tc dcs) = do
  def' <- inferDataDef def >>= emitDataDef
  tc' <- emitTyConName def'
  dcs' <- mapM (emitDataConName def') [0..(length dcs - 1)]
  return $ tc @> Rename tc' <> newEnv dcs (map Rename dcs')
inferUDecl (UInterface paramBs superclasses methodTys className methodNames) = do
  let classPrettyName = pprint className
  let methodPrettyNames = map pprint $ toList methodNames
  classDef <- inferInterfaceDataDef classPrettyName methodPrettyNames
                paramBs superclasses methodTys
  className' <- withNameHint className $ emitClassDef classDef
  mapM_ (emitSuperclass className') [0..(length superclasses - 1)]
  methodNames' <- forM (enumerate $ zip (toList methodNames) methodTys) \(i, (name, ty)) -> do
    paramVs <- forM (toList paramBs) \(UAnnBinder v _) -> case v of
      UBind n -> return $ UInternalVar n
      _       -> throw CompilerErr "Unexpected interface binder. Please open a bug report!"
    explicits <- case uMethodExplicitBs ty of
      []               -> return $ replicate (length paramBs) False
      e | e == paramVs -> return $ replicate (length paramBs) True
      e -> case unexpected of
        []    -> throw CompilerErr "Permuted or incomplete explicit type binders are not supported yet."
        (h:_) -> throw TypeErr $ "Explicit type binder `" ++ pprint h ++ "` in method " ++
                                 pprint name ++ " is not a type parameter of its interface"
        where unexpected = filter (not . (`elem` paramVs)) e
    withNameHint name $ emitMethodType explicits className' i
  return $  className @> Rename className'
         <> newEnv methodNames (map Rename methodNames')
inferUDecl (UInstance argBinders ~(UInternalVar className) params methods maybeName) = do
  instanceDict <- checkInstance argBinders className params methods
  case maybeName of
    Nothing -> do
      _ <- withNameHint hint $ emitAnn InstanceLet (Atom instanceDict)
      return mempty
      where hint = Name TypeClassGenName "instance" 0
    Just instanceName -> do
      instanceVal <- withNameHint instanceName $ emitAnn PlainLet (Atom instanceDict)
      return $ instanceName @> SubstVal instanceVal

inferDataDef :: UDataDef -> UInferM DataDef
inferDataDef (UDataDef (tyConName, paramBs) dataCons) =
  withNestedBinders paramBs \paramBs' -> do
    dataCons' <- forM dataCons \(dataConName, argBs) ->
                   withNestedBinders argBs \argBs' ->
                     return $ DataConDef dataConName argBs'
    return $ DataDef tyConName paramBs' dataCons'

inferInterfaceDataDef :: SourceName -> [SourceName] -> Nest UAnnBinder
                      -> [UType] -> [UMethodType] -> UInferM ClassDef
inferInterfaceDataDef className methodNames paramBs superclasses methods = do
  dictDef <- withNestedBinders paramBs \paramBs' -> do
    superclasses' <- mapM checkUType superclasses
    methods'      <- mapM checkUType $ uMethodType <$> methods
    return $ makeClassDataDef className paramBs' superclasses' methods'
  defName <- emitDataDef dictDef
  return $ ClassDef (defName, dictDef) methodNames

withNestedBinders :: Nest UAnnBinder -> (Nest Binder -> UInferM a) -> UInferM a
withNestedBinders Empty cont = cont Empty
withNestedBinders (Nest (UAnnBinder b ty) rest) cont = do
  ty' <- checkUType ty
  withFreshName b ty' \x@(Var v) ->
    extInferSubst (b@>SubstVal x) $
      withNestedBinders rest \rest' ->
        cont $ Nest (Bind v) rest'

withFreshName :: NameHint hint => MonadFail m => MonadBuilder m
              => hint -> Type -> (Atom -> m a) -> m a
withFreshName hint ty cont = do
  (ans, decls) <- scopedDecls do
     v <- withNameHint hint $ freshVarE UnknownBinder ty
     cont $ Var v
  Empty <- return decls
  return ans

inferULam :: UPatAnn -> Arrow -> UExpr -> UInferM Atom
inferULam (UPatAnn p ann) arr body = do
  argTy <- checkAnn ann
  -- TODO: worry about binder appearing in arrow?
  buildLam (Bind $ patNameHint p :> argTy) arr
    \(Var v) -> checkLeaks [v] $ withBindPat p v $ inferSigma body

checkULam :: UPatAnn -> UExpr -> PiType -> UInferM Atom
checkULam (UPatAnn p ann) body piTy = do
  let argTy = absArgType piTy
  checkAnn ann >>= constrainEq argTy
  buildDepEffLam (Bind $ patNameHint p :> argTy)
    ( \x -> return $ fst $ applyAbs piTy x)
    \x@(Var v) -> checkLeaks [v] $ withBindPat p v $
                      checkSigma body Suggest $ snd $ applyAbs piTy x

checkInstance :: Nest UPatAnnArrow -> Name -> [UType] -> [UMethodDef] -> UInferM Atom
checkInstance (Nest (UPatAnnArrow (UPatAnn p ann) arrow) rest) className params methods = do
  case arrow of
    ImplicitArrow -> return ()
    ClassArrow    -> return ()
    _ -> throw TypeErr $ "Not a valid arrow for an instance: " ++ pprint arrow
  argTy <- checkAnn ann
  buildLam (Bind $ patNameHint p :> argTy) (fromUArrow arrow) \(Var v) ->
    checkLeaks [v] $ withBindPat p v $ checkInstance rest className params methods
checkInstance Empty className params methods = do
  substEnv <- getInferSubst
  className' <- case envLookup substEnv className of
    Nothing -> return className
    Just (Rename className') -> return className'
    Just (SubstVal _) -> throw TypeErr $ "Not a valid class: " ++ pprint className
  params' <- mapM checkUType params
  ClassDef def methodNames <- getClassDef className'
  [ClassDictCon superclassTys methodTys] <- return $ applyDataDefParams (snd def) params'
  let superclassHoles = fmap (Con . ClassDictHole Nothing) superclassTys
  methodsChecked <- mapM (checkMethodDef className' methodTys) methods
  let (idxs, methods') = unzip $ sortOn fst $ methodsChecked
  forM_ (repeated idxs) \i ->
    throw TypeErr $ "Duplicate method: " ++ pprint (methodNames!!i)
  forM_ ([0..(length methodTys - 1)] `listDiff` idxs) \i ->
    throw TypeErr $ "Missing method: " ++ pprint (methodNames!!i)
  return $ DataCon def params' 0 [PairVal (ProdVal superclassHoles)
                                          (ProdVal methods')]

checkMethodDef :: ClassDefName -> [Type] -> UMethodDef -> UInferM (Int, Atom)
checkMethodDef className methodTys (UMethodDef ~(UInternalVar v) rhs) = do
  scope <- getScope
  ClassDef (_, DataDef classSourceName _ _ ) _ <- getClassDef className
  case scope ! v of
    MethodName className' i _ | className == className' -> do
      let methodTy = methodTys !! i
      rhs' <- checkSigma rhs Suggest methodTy
      return (i, rhs')
    _ -> throw TypeErr $ pprint v ++ " is not a method of " ++ pprint classSourceName

checkUEffRow :: UEffectRow -> UInferM EffectRow
checkUEffRow (EffectRow effs t) = do
   effs' <- liftM S.fromList $ mapM checkUEff $ toList effs
   t'    <- forM t \tv -> lookupVarName EffKind tv
   return $ EffectRow effs' t'
   where
     lookupVarName :: Type -> UVar -> UInferM Name
     lookupVarName ty ~(UInternalVar v) = do
       -- TODO: more graceful errors on error
       SubstVal (Var (v':>ty')) <- (!v) <$> getInferSubst
       constrainEq ty ty'
       return v'

checkUEff :: UEffect -> UInferM Effect
checkUEff eff = case eff of
  RWSEffect rws region -> do
    Var (v:>ty) <- lookupUVar region
    constrainEq TyKind ty
    return $ RWSEffect rws v
  ExceptionEffect -> return ExceptionEffect
  IOEffect        -> return IOEffect

data CaseAltIndex = ConAlt Int
                  | VariantAlt Label Int
                  | VariantTailAlt (LabeledItems ())
  deriving (Eq, Show)

checkCaseAlt :: RhoType -> Type -> UAlt -> UInferM (CaseAltIndex, Alt)
checkCaseAlt reqTy scrutineeTy (UAlt pat body) = do
  (conIdx, patTys) <- checkCasePat pat scrutineeTy
  let (subPats, subPatTys) = unzip patTys
  let bs = zipWith (\p ty -> Bind $ patNameHint p :> ty) subPats subPatTys
  alt <- buildNAbs (toNest bs) \xs ->
           let vs = map (\(Var v) -> v) xs
           in withBindPats (zip subPats vs) $ checkRho body reqTy
  return (conIdx, alt)

lookupDataCon :: Name -> UInferM (NamedDataDef, Int)
lookupDataCon conName = do
  substEnv <- getInferSubst
  conName' <- case envLookup substEnv conName of
    Nothing         -> return conName
    Just (Rename v) -> return v
    _ -> throw TypeErr $ "Not a data constructor: " ++ pprint conName
  scope <- getScope
  case envLookup scope conName' of
    Just (DataConName dataDefName con) -> do
      let DataDefName def = scope ! dataDefName
      return ((dataDefName, def), con)
    Just _  -> throw CompilerErr $ "Not a data constructor: " ++ pprint conName
    Nothing -> throw CompilerErr $ pprint conName

checkCasePat :: UPat -> Type -> UInferM (CaseAltIndex, [(UPat, Type)])
checkCasePat (WithSrc pos pat) scrutineeTy = addSrcContext' pos $ case pat of
  UPatCon ~(UInternalVar conName) ps -> do
    (def@(_, DataDef _ paramBs cons), con) <- lookupDataCon conName
    let (DataConDef _ argBs) = cons !! con
    when (length argBs /= length ps) $ throw TypeErr $
     "Unexpected number of pattern binders. Expected " ++ show (length argBs)
                                            ++ " got " ++ show (length ps)
    params <- mapM (freshType . binderType) $ toList paramBs
    let argTys = applyNaryAbs (Abs paramBs $ map binderType $ toList argBs) params
    constrainEq scrutineeTy (TypeCon def params)
    return (ConAlt con, zip (toList ps) argTys)
  UPatVariant labels@(LabeledItems lmap) label subpat -> do
    subty <- freshType TyKind
    prevTys <- mapM (const $ freshType TyKind) labels
    Var (rest:>_) <- freshType LabeledRowKind
    let patTypes = prevTys <> labeledSingleton label subty
    let extPatTypes = Ext patTypes $ Just rest
    constrainEq scrutineeTy $ VariantTy extPatTypes
    let i = case M.lookup label lmap of
              Just prev -> length prev
              Nothing -> 0
    return (VariantAlt label i, [(subpat, subty)])
  UPatVariantLift labels subpat -> do
    prevTys <- mapM (const $ freshType TyKind) labels
    Var (rest:>_) <- freshType LabeledRowKind
    let extPatTypes = Ext prevTys $ Just rest
    constrainEq scrutineeTy $ VariantTy extPatTypes
    let subty = VariantTy $ Ext NoLabeledItems $ Just rest
    return (VariantTailAlt labels, [(subpat, subty)])
  _ -> throw TypeErr $ "Case patterns must start with a data constructor or variant pattern"

withBindPats :: [(UPat, Var)] -> UInferM a -> UInferM a
withBindPats pats body = foldr (uncurry withBindPat) body pats

withBindPat :: UPat -> Var -> UInferM a -> UInferM a
withBindPat pat var m = do
  env <- bindPat pat $ Var var
  extInferSubst env m

bindPat :: UPat -> Atom -> UInferM SubstEnv
bindPat (WithSrc pos pat) val = addSrcContext pos $ case pat of
  UPatBinder b -> do
    return (b @> SubstVal val)
  UPatUnit -> do
    constrainEq UnitTy (getType val)
    return mempty
  UPatPair p1 p2 -> do
    _    <- fromPairType (getType val)
    val' <- zonk val  -- ensure it has a pair type before unpacking
    x1   <- getFst val' >>= zonk
    x2   <- getSnd val' >>= zonk
    env1 <- bindPat p1 x1
    env2 <- bindPat p2 x2
    return $ env1 <> env2
  UPatCon ~(UInternalVar conName) ps -> do
    (def@(_, DataDef _ paramBs cons), con) <- lookupDataCon conName
    when (length cons /= 1) $ throw TypeErr $
      "sum type constructor in can't-fail pattern"
    let (DataConDef _ argBs) = cons !! con
    when (length argBs /= length ps) $ throw TypeErr $
      "Unexpected number of pattern binders. Expected " ++ show (length argBs)
                                             ++ " got " ++ show (length ps)
    params <- mapM (freshType . binderType) $ toList paramBs
    constrainEq (TypeCon def params) (getType val)
    xs <- zonk (Atom $ val) >>= emitUnpack >>= mapM zonk
    fold <$> zipWithM bindPat (toList ps) xs
  UPatRecord (Ext pats Nothing) -> do
    expectedTypes <- mapM (const $ freshType TyKind) pats
    constrainEq (RecordTy (NoExt expectedTypes)) (getType val)
    xs <- zonk (Atom $ val) >>= emitUnpack >>= mapM zonk
    fold <$> zipWithM bindPat (toList pats) xs
  UPatRecord (Ext pats (Just tailPat)) -> do
    wantedTypes <- mapM (const $ freshType TyKind) pats
    restType <- freshInferenceName LabeledRowKind
    let vty = getType val
    constrainEq (RecordTy $ Ext wantedTypes $ Just restType) vty
    -- Split the record.
    wantedTypes' <- zonk wantedTypes
    val' <- zonk val
    split <- emit $ Op $ RecordSplit wantedTypes' val'
    [left, right] <- getUnpacked split
    leftVals <- getUnpacked left
    env1 <- fold <$> zipWithM bindPat (toList pats) leftVals
    env2 <- bindPat tailPat right
    return $ env1 <> env2
  UPatVariant _ _ _ -> throw TypeErr "Variant not allowed in can't-fail pattern"
  UPatVariantLift _ _ -> throw TypeErr "Variant not allowed in can't-fail pattern"
  UPatTable ps -> do
    elemTy <- freshType TyKind
    let idxTy = FixedIntRange 0 (fromIntegral $ length ps)
    constrainEq (getType val) (idxTy ==> elemTy)
    let idxs = indicesNoIO idxTy
    unless (length idxs == length ps) $
      throw TypeErr $ "Incorrect length of table pattern: table index set has "
                      <> pprint (length idxs) <> " elements but there are "
                      <> pprint (length ps) <> " patterns."
    flip foldMapM (zip ps idxs) \(p, i) -> do
      v <- emitZonked $ App val i
      bindPat p v

-- TODO (BUG!): this should just be a hint but something goes wrong if we don't have it
patNameHint :: UPat -> Name
patNameHint (WithSrc _ (UPatBinder (UBind v))) = v
patNameHint _ = "pat"

withPatHint :: UPat -> UInferM a -> UInferM a
withPatHint p m = withNameHint (patNameHint p) m

checkAnn :: Maybe UType -> UInferM Type
checkAnn ann = case ann of
  Just ty -> checkUType ty
  Nothing -> freshType TyKind

checkUType :: UType -> UInferM Type
checkUType ty@(WithSrc ctx _) =
  typeReduceScoped (withEffects Pure $ checkRho ty TyKind) >>=
  typeReductionAsAtom ctx "Failed to reduce type annotation"

-- Delayed unification task. When performing its solve, it tries to perform
-- dictionary synthesis within the inner scope and normalize eafResult such
-- that it contains no free vars from the eafInner scope (while it can refer
-- to eafOuter scope). If the evaluation succeeds, the result is unified
-- with eafExpected.
data EvalAndUnif = EvalAndUnif
  { eafOuter :: Scope
  , eafInner :: Scope
  , eafResult :: Atom
  , eafScs :: SynthCandidates
  , eafExpected :: Atom
  , eafErr :: Err
  }
-- XXX: Those assume no shadowing between outer and local scopes
instance HasVars EvalAndUnif where
  freeVars EvalAndUnif{..} = allFree `envDiff` eafInner
    where allFree = freeVars eafResult <> foldMap freeVars eafInner <> freeVars eafExpected
-- XXX: This is incorrect if the subst is not scopeless
instance Subst EvalAndUnif where
  subst env EvalAndUnif{..} =
    EvalAndUnif (subst env eafOuter) (subst env eafInner) (subst env eafResult)
                (subst env eafScs) (subst env eafExpected) eafErr
instance IsDelayedSolve EvalAndUnif where
  performDelayedSolve EvalAndUnif{..} = do
    innerNoDict <- zonk eafInner >>= traverse \case
      (AtomBinderInfo ty (LetBound ann expr)) -> AtomBinderInfo ty . LetBound ann <$> expr'
        where
          comp = traverseExpr (traverseHoles synthDictTop) expr
          expr' = case runSubstBuilderT eafOuter eafScs comp of
            Failure  errs    -> throwErrs errs
            Success (ans, _) -> return ans
      info -> return info
    case typeReduceLocals eafOuter innerNoDict (Atom eafResult) of
      Right ans -> do
        -- We don't do leak checks on delayed solves, so make sure we don't
        -- introduce more free vars than were present in the atom we returned
        -- in places of the delayed evaluation (which was subject to leak checking).
        unless (null $ freeVars ans `envDiff` freeVars eafExpected) $
          throw CompilerErr $ "Inference failed due to scoping issues"
        constrainEq ans eafExpected
      Left  _   -> throwErr eafErr

typeReductionAsAtom :: SrcPosCtx -> String -> Either (Scope, Atom) Atom -> UInferM Atom
typeReductionAsAtom ctx msg reduced =
  case reduced of
    Right ty'         -> return $ ty'
    Left (localScope, ty') -> do
      outerScope <- getScope
      env <- forM (localScope `envIntersect` freeVars ty') \(AtomBinderInfo ty _) ->
        freshInferenceName ty <&> (:> ty)
      resTy <- substBuilder (env <&> Rename . varName) ty'
      scs <- getSynthCandidates
      delaySolve $ EvalAndUnif outerScope localScope ty' scs resTy $
        Err TypeErr (ErrCtx Nothing ctx []) msg
      return resTy

checkArrow :: Arrow -> UArrow -> UInferM ()
checkArrow ahReq ahOff = case (ahReq, ahOff) of
  (PlainArrow _, PlainArrow ()) -> return ()
  (LinArrow    , PlainArrow ()) -> return ()
  (LinArrow    , LinArrow     ) -> return ()
  (TabArrow  , TabArrow  ) -> return ()
  (ClassArrow, ClassArrow) -> return ()
  _ -> throw TypeErr $  " Wrong arrow type:" ++
                       "\nExpected: " ++ pprint ahReq ++
                       "\nActual:   " ++ pprint (fmap (const Pure) ahOff :: Arrow)

checkExtLabeledRow :: ExtLabeledItems UExpr UExpr -> UInferM (ExtLabeledItems Type Name)
checkExtLabeledRow (Ext types Nothing) = do
  types' <- mapM checkUType types
  return $ Ext types' Nothing
checkExtLabeledRow (Ext types (Just ext)) = do
  types' <- mapM checkUType types
  -- Only variables can have kind LabeledRowKind at the moment.
  Var (ext':>_) <- checkRho ext LabeledRowKind
  return $ Ext types' $ Just ext'

data DelayedTabCon = DelayedTabCon
  { dtcPi           :: PiType
  , dtcExpectedSize :: Int
  , dtcCheckIndices :: Maybe [Atom]
  , dtcSrcCtx       :: SrcPosCtx
  }
instance HasVars DelayedTabCon where
  freeVars (DelayedTabCon p _ indices _) = freeVars p <> foldMap (foldMap freeVars) indices
instance Subst DelayedTabCon where
  subst env (DelayedTabCon p si idxs ctx) = DelayedTabCon (subst env p) si (fmap (fmap (subst env)) idxs) ctx
instance IsDelayedSolve DelayedTabCon where
  performDelayedSolve DelayedTabCon{..} = do
    uns <- looks unsolved
    finalPi <- zonk dtcPi
    case null $ freeVars finalPi `envIntersect` uns of
      False -> throwErr $ Err TypeErr (ErrCtx Nothing dtcSrcCtx [])
        "Failed to infer the index set of an array literal. Please try adding a type annotation."
      True  -> return ()
    let indices = indicesNoIO $ absArgType finalPi
    unless (length indices == dtcExpectedSize) $ throwErr $ Err TypeErr (ErrCtx Nothing dtcSrcCtx []) $
      "Table literal has " ++ show dtcExpectedSize ++ " elements, but its inferred index set " ++
      "(" ++ pprint (Pi finalPi) ++ ") has a size of " ++ show (length indices)
    case dtcCheckIndices of
      Nothing      -> return ()
      Just idxVars -> forM_ (zip indices idxVars) (uncurry constrainEq)

inferTabCon :: SrcPosCtx -> [UExpr] -> RequiredTy RhoType -> UInferM Atom
inferTabCon pos xs reqTy = do
  p@(Abs n (_, a)) <- case reqTy of
    Check ty -> fromPiType True TabArrow ty
    Infer    -> fromPiType True TabArrow =<< freshType TyKind
  registerDefault (binderType n) $ Fin $ IdxRepVal $ fromIntegral $ length xs
  xs' <- case n `isin` freeVars a of
    False -> do
      delaySolve $ DelayedTabCon p (length xs) Nothing pos
      mapM (flip checkRho a) xs
    True  -> do
      -- TODO: We could check if we can already create indices at this point
      -- and avoid delaying the checks. But this might get difficult once we
      -- make index set a type class.
      (idxs, xs') <- unzip <$> forM xs \x -> do
        idx <- freshType $ binderType n
        (idx,) <$> checkRho x (snd $ applyAbs p idx)
      delaySolve $ DelayedTabCon p (length xs) (Just idxs) pos
      return xs'
  emitZonked $ Op $ TabCon (Pi p) xs'

fromUArrow :: UArrow -> Arrow
fromUArrow arr = fmap (const Pure) arr

-- Bool flag is just to tweak the reported error message
fromPiType :: Bool -> UArrow -> Type -> UInferM PiType
fromPiType _ _ (Pi piTy) = return piTy -- TODO: check arrow
fromPiType expectPi arr ty = do
  a <- freshType TyKind
  b <- freshType TyKind
  let piTy = Abs (Ignore a) (fromUArrow arr, b)
  if expectPi then  constrainEq (Pi piTy) ty
              else  constrainEq ty (Pi piTy)
  return piTy

fromPairType :: Type -> UInferM (Type, Type)
fromPairType (PairTy t1 t2) = return (t1, t2)
fromPairType ty = do
  a <- freshType TyKind
  b <- freshType TyKind
  constrainEq (PairTy a b) ty
  return (a, b)

emitZonked :: Expr -> UInferM Atom
emitZonked expr = zonk expr >>= emit

addEffects :: EffectRow -> UInferM ()
addEffects eff = do
  allowed <- checkAllowedUnconditionally eff
  unless allowed $ do
    allowedEffects <- getAllowedEffects
    eff' <- openEffectRow eff
    constrainEq (Eff allowedEffects) (Eff eff')

checkAllowedUnconditionally :: EffectRow -> UInferM Bool
checkAllowedUnconditionally Pure = return True
checkAllowedUnconditionally eff = do
  eff' <- zonk eff
  effAllowed <- getAllowedEffects >>= zonk
  return $ case checkExtends effAllowed eff' of
    Failure _  -> False
    Success () -> True

openEffectRow :: EffectRow -> UInferM EffectRow
openEffectRow (EffectRow effs Nothing) = extendEffRow effs <$> freshEff
openEffectRow effRow = return effRow

addSrcContext' :: SrcPosCtx -> UInferM a -> UInferM a
addSrcContext' pos = addSrcContext pos . local (\e -> e { srcCtx = pos })

getSrcCtx :: UInferM SrcPosCtx
getSrcCtx = asks srcCtx

getInferSubst :: UInferM SubstEnv
getInferSubst = asks inferSubst

extInferSubst :: SubstEnv -> UInferM a -> UInferM a
extInferSubst ext = local (\e -> e { inferSubst = inferSubst e <> ext })

-- === typeclass dictionary synthesizer ===

-- We have two variants here because at the top level we want error messages and
-- internally we want to consider all alternatives.
type SynthPassM = SubstBuilderT Except
type SynthDictM = SubstBuilderT (ReaderT NormalizedGivens (WriterT DerivationKind []))

type SuperclassProjection = Atom  -- A function projecting a superclass from a dictionary
type Given = Block  -- A block that can produce a given of the corresponding type

newtype NormalizedGivens = NormalizedGivens [Given]
instance Semigroup NormalizedGivens where
  (NormalizedGivens a) <> (NormalizedGivens b) = NormalizedGivens $ uniqGivens $ a ++ b
instance Monoid NormalizedGivens where
  mempty = NormalizedGivens []

data DerivationKind = OnlyGivens | UsedInstance deriving Eq
instance Semigroup DerivationKind where
  OnlyGivens <> OnlyGivens = OnlyGivens
  _          <> _          = UsedInstance
instance Monoid DerivationKind where
  mempty = OnlyGivens

synthModule :: Scope -> SynthCandidates -> Module -> Except Module
synthModule scope scs (Module Typed decls result) = do
  (result', (_, decls')) <- runSubstBuilderT scope scs do
              env <- traverseDeclsOpen (traverseHoles synthDictTop) decls
              extendR env $ substBuilderR result
  -- TODO: put the InstanceLet decls in the result bindings (eventually should
  -- be a separate thing but not necessary now)
  return $ Module Core decls' result'
synthModule _ _ _ = error $ "Unexpected IR variant"

synthDictTop :: SrcPosCtx -> Type -> SynthPassM Atom
synthDictTop ctx ty = do
  scope <- getScope
  scs <- getSynthCandidates
  let baseGivens = foldMap (normalizeGiven scope scs (superclassGetters scs)) $
        Block Empty . Atom <$> lambdaDicts scs
  let (solutionsGivens, solutionsInstance) = partition ((== OnlyGivens) . snd) $
        runWriterT $ runReaderT (runSubstBuilderT scope scs $ synthDict ty) baseGivens
  addSrcContext ctx $ do
    unless (length solutionsInstance <= 1) $
      throw TypeErr $ "Multiple candidate class dictionaries for: " ++ pprint ty
    case solutionsGivens ++ solutionsInstance of
      [] -> throw TypeErr $ "Couldn't synthesize a class dictionary for: " ++ pprint ty
      ((ans, env), _):_ -> builderExtend env $> ans

normalizeGiven :: Scope -> SynthCandidates -> [SuperclassProjection] -> Given -> NormalizedGivens
normalizeGiven scope scs projs initGivens = NormalizedGivens $ superclassClosure [initGivens]
  where
    superclassClosure :: [Given] -> [Given]
    superclassClosure givens = case length givens == length nextGivens of
      True  -> givens
      False -> superclassClosure nextGivens
      where nextGivens = uniqGivens $ givens ++ superclassStep givens

    superclassStep :: [Given] -> [Given]
    superclassStep givens = do
      p <- projs
      g <- givens
      maybeToList $ tryApply p g

    tryApply :: Atom -> Block -> Maybe Block
    tryApply f xb = case res of
      Failure _      -> Nothing
      Success (b, _) -> Just b
      where
        res = runUInferM mempty scope scs (error "Shouldn't need protolude here") $ do
          buildScoped $ do
            f' <- instantiateSigma f
            Pi (Abs b _) <- return $ getType f'
            constrainEq (binderType b) (getType xb)
            x <- emitBlock xb
            emitZonked $ App f' x

uniqGivens :: [Given] -> [Given]
uniqGivens = nubBy (\x y -> getType x == getType y)

traverseHoles :: (MonadReader SubstEnv m, MonadBuilder m)
              => (SrcPosCtx -> Type -> m Atom) -> TraversalDef m
traverseHoles fillHole = (traverseDecl recur, traverseExpr recur, synthPassAtom)
  where
    synthPassAtom atom = case atom of
      Con (ClassDictHole ctx ty) -> fillHole ctx =<< substBuilderR ty
      _ -> traverseAtom recur atom
    recur = traverseHoles fillHole

synthDict :: Type -> SynthDictM Atom
synthDict ty = case ty of
  PiTy b arr body -> synthesizeNow <|> introFirst
    where
      introFirst = do
        buildDepEffLam b
          (\x -> extendR (b @> SubstVal x) $ substBuilderR arr)
          (\x -> extendR (b @> SubstVal x) $ do
            givens         <- lift $ lift $ ask
            superclassProj <- superclassGetters <$> getSynthCandidates
            scope <- getScope
            scs <- getSynthCandidates
            let newGivens = case arr of
                  ClassArrow -> givens <> normalizeGiven scope scs superclassProj (Block Empty $ Atom x)
                  _          -> givens
            withGivens newGivens $ substBuilderR body >>= synthDict)
  _ -> synthesizeNow
  where
    synthesizeNow = (getGiven <|> getInstance) >>= trySynth
    trySynth step = do
      block <- buildScoped $ inferToSynth $ instantiateAndCheck ty step
      -- NOTE: It's ok to emit unconditionally here. It will only ever emit
      --       blocks that fully resolved without any holes, and if we ever
      --       end up with two results, we don't use the duplicate code because
      --       it's an error!
      traverseBlock (traverseHoles (const synthDict)) block >>= emitBlock

tryEachCandidate :: [a] -> SynthDictM a
tryEachCandidate = lift . lift . lift . lift

getInstance :: SynthDictM Atom
getInstance = do
  tell UsedInstance
  (instanceDicts <$> getSynthCandidates) >>= tryEachCandidate

getGiven :: SynthDictM Atom
getGiven = do
  NormalizedGivens givens <- lift $ lift $ ask
  tryEachCandidate givens >>= emitBlock

withGivens :: NormalizedGivens -> SynthDictM a -> SynthDictM a
withGivens givens m = do
  buildC <- builderLook
  buildR <- builderAsk
  scope <- ask
  (ans, ext) <- lift $ lift $ local (const givens) $ runBuilderT' (runReaderT m scope) (buildR, buildC)
  builderExtend ext
  return ans

inferToSynth :: (Pretty a, HasVars a, Subst a) => UInferM a -> SynthDictM a
inferToSynth m = do
  scope <- getScope
  scs <- getSynthCandidates
  case runUInferM mempty scope scs (error "Shouldn't need protolude here") m of
    Failure _ -> empty
    Success (x, (_, decls)) -> do
      mapM_ emitDecl decls
      return x

instantiateAndCheck :: Type -> Atom -> UInferM Atom
instantiateAndCheck ty x = do
  x' <- instantiateSigma x
  constrainEq ty (getType x')
  return x'

-- === constraint solver ===




data DelayedSolve = forall a. (IsDelayedSolve a, HasVars a, Subst a) => DelayedSolve a
instance HasVars DelayedSolve where
  freeVars (DelayedSolve s) = freeVars s
instance Subst DelayedSolve where
  subst env (DelayedSolve s) = DelayedSolve $ subst env s

class IsDelayedSolve a where
  performDelayedSolve :: (MonadSolver m, Fallible m) => a -> m ()
instance IsDelayedSolve DelayedSolve where
  performDelayedSolve (DelayedSolve s) = performDelayedSolve s

data SolverEnv = SolverEnv
  { solverVars        :: Env Kind
  , solverSub         :: Env (SubstVal Type)
  , solverDefaults    :: [(Atom, Atom)]  -- Optional unifications
  , solverDelayed     :: [DelayedSolve]
  }
type SolverT m = CatT SolverEnv m
type MonadSolver m = MonadCat SolverEnv m

runSolverT :: (Fallible m, HasVars a, Subst a, Pretty a)
           => CatT SolverEnv m a -> m a
runSolverT m = liftM fst $ flip runCatT mempty $ do
  ans <- m >>= zonk
  unsolvedDelayedBeforeDefaults <- trySolveDelayed =<< looks solverDelayed
  applyDefaults
  failedDelayed <- trySolveDelayed unsolvedDelayedBeforeDefaults
  forM_ failedDelayed performDelayedSolve  -- TODO: Applicative errors!
  ans' <- zonk ans
  vs <- looks $ envNames . unsolved
  throwIf (not (null vs)) TypeErr $ "Ambiguous type variables: "
                                  ++ pprint vs ++ "\n\n" ++ pprint ans'
  return ans'

data SolveProgress = Progressed | NoChange deriving Show

trySolveDelayed :: forall m. MonadSolver m => [DelayedSolve] -> m [DelayedSolve]
trySolveDelayed solves = go solves
  where
    go :: [DelayedSolve] -> m [DelayedSolve]
    go todos = do
      (remaining, progress) <- flip runStateT NoChange $
        flip filterM todos \s -> do
          result <- catchSolver $ performDelayedSolve s
          case result of
            Failure _  -> return True
            Success () -> put Progressed $> False
      case progress of
        Progressed -> go remaining
        NoChange   -> return remaining

catchSolver :: MonadSolver n => (forall m. (MonadSolver m, Fallible m) => m a) -> n (Except a)
catchSolver m = (runCatT m <$> look) >>= \case
  Failure errs            -> return $ Failure errs
  Success (ans, finalEnv) -> extend finalEnv $> Success ans

applyDefaults :: (MonadSolver m, Fallible m) => m ()
applyDefaults = do
  vs       <- looks unsolved
  defaults <- looks solverDefaults
  forM_ (envPairs vs) \case
    (v, EffKind)                     -> addSub v $ Eff Pure
    _                                -> return ()
  -- Apply all defaults that don't cause unification errors
  forM_ defaults \(lhs, rhs) -> void $ tryConstrainEq lhs rhs
  where addSub v ty = extend $ SolverEnv mempty (v@>SubstVal ty) mempty mempty

solveLocal :: (HasVars a, Subst a) => UInferM a -> UInferM a
solveLocal m = do
  (ans, env@(SolverEnv freshVars sub defaults delayed)) <- scoped $ do
    -- This might get expensive. TODO: revisit once we can measure performance.
    (ans, builderEnv) <- zonk =<< builderScoped m
    builderExtend builderEnv
    return ans
  extend $ SolverEnv (unsolved env) (sub `envDiff` freshVars) (scopelessSubst sub defaults) (scopelessSubst sub delayed)
  return ans

checkLeaks :: (HasType a, HasVars a, Subst a) => [Var] -> UInferM a -> UInferM a
checkLeaks tvs m = do
  scope <- getScope
  (ans, env) <- scoped $ solveLocal $ m
  let resultTypeLeaks = filter (\case (Name InferenceName _ _) -> False; _ -> True) $
                          envNames $ freeVars (getType ans) `envDiff` scope
  unless (null $ resultTypeLeaks) $
    throw TypeErr $ "Leaked local variable `" ++ pprint (head resultTypeLeaks) ++
                    "` in result type " ++ pprint (getType ans)
  forM_ (solverSub env) \ty ->
    forM_ tvs \tv ->
      throwIf (tv `occursIn` ty) TypeErr $ "Leaked type variable: " ++ pprint tv
  extend env
  return ans

unsolved :: SolverEnv -> Env Kind
unsolved (SolverEnv vs sub _ _) = vs `envDiff` sub

freshInferenceName :: (Fallible m, MonadSolver m) => Kind -> m Name
freshInferenceName k = do
  env <- look
  let v = genFresh (rawName InferenceName "?") $ solverVars env
  extend $ SolverEnv (v@>k) mempty mempty mempty
  return v

freshType ::  (Fallible m, MonadSolver m) => Kind -> m Type
freshType EffKind = Eff <$> freshEff
freshType k = Var . (:>k) <$> freshInferenceName k

freshEff :: (Fallible m, MonadSolver m) => m EffectRow
freshEff = EffectRow mempty . Just <$> freshInferenceName EffKind

registerDefault :: MonadSolver m => Atom -> Atom -> m ()
registerDefault lhs rhs = do
  extend $ SolverEnv mempty mempty [(lhs, rhs)] mempty

delaySolve :: (MonadSolver m, IsDelayedSolve a, HasVars a, Subst a) => a -> m ()
delaySolve todo = do
  -- Try to eagerly perform the solve to improve performance
  result <- catchSolver $ performDelayedSolve todo
  case result of
    Success () -> return ()
    Failure _  -> extend $ SolverEnv mempty mempty mempty [DelayedSolve todo]

tryConstrainEq :: MonadSolver m => Type -> Type -> m (Except ())
tryConstrainEq t1 t2 = catchSolver $ constrainEq t1 t2

constrainEq :: (Fallible m, MonadSolver m) => Type -> Type -> m ()
constrainEq t1 t2 = do
  t1' <- zonk t1
  t2' <- zonk t2
  let ((t1Pretty, t2Pretty), infVars) = renameForPrinting (t1', t2')
  let msg =   "Expected: " ++ pprint t1Pretty
         ++ "\n  Actual: " ++ pprint t2Pretty
         ++ (if null infVars then "" else
               "\n(Solving for: " ++ pprint infVars ++ ")")
  addContext msg $ unify t1' t2'

zonk :: (HasVars a, Subst a, MonadSolver m) => a -> m a
zonk x = do
  s <- looks solverSub
  return $ scopelessSubst s x

unify :: (Fallible m, MonadSolver m) => Type -> Type -> m ()
unify t1 t2 = do
  t1' <- zonk t1
  t2' <- zonk t2
  vs <- looks solverVars
  case (t1', t2') of
    _ | t1' == t2' -> return ()
    (t, Var v) | v `isin` vs -> bindQ v t
    (Var v, t) | v `isin` vs -> bindQ v t
    (Pi piTy, Pi piTy') -> do
       unify (absArgType piTy) (absArgType piTy')
       let v = Var $ freshSkolemVar (piTy, piTy') (absArgType piTy)
       -- TODO: think very hard about the leak checks we need to add here
       let (arr , resultTy ) = applyAbs piTy  v
       let (arr', resultTy') = applyAbs piTy' v
       when (void arr /= void arr') $ throw TypeErr ""
       unify resultTy resultTy'
       unifyEff (arrowEff arr) (arrowEff arr')
    (RecordTy  items, RecordTy  items') ->
      unifyExtLabeledItems items items'
    (VariantTy items, VariantTy items') ->
      unifyExtLabeledItems items items'
    (TypeCon f xs, TypeCon f' xs')
      | f == f' && length xs == length xs' -> zipWithM_ unify xs xs'
    (TC con, TC con') | void con == void con' ->
      zipWithM_ unify (toList con) (toList con')
    (Eff eff, Eff eff') -> unifyEff eff eff'
    _ -> throw TypeErr ""

unifyExtLabeledItems :: (MonadSolver m, Fallible m)
  => ExtLabeledItems Type Name -> ExtLabeledItems Type Name -> m ()
unifyExtLabeledItems r1 r2 = do
  r1' <- zonk r1
  r2' <- zonk r2
  vs <- looks solverVars
  case (r1', r2') of
    _ | r1' == r2' -> return ()
    (r, Ext NoLabeledItems (Just v)) | v `isin` vs ->
      bindQ (v:>LabeledRowKind) (LabeledRow r)
    (Ext NoLabeledItems (Just v), r) | v `isin` vs ->
      bindQ (v:>LabeledRowKind) (LabeledRow r)
    (_, Ext NoLabeledItems _) -> throw TypeErr ""
    (Ext NoLabeledItems _, _) -> throw TypeErr ""
    (Ext (LabeledItems items1) t1, Ext (LabeledItems items2) t2) -> do
      let unifyPrefixes tys1 tys2 = mapM (uncurry unify) $ NE.zip tys1 tys2
      sequence_ $ M.intersectionWith unifyPrefixes items1 items2
      let diffDrop xs ys = NE.nonEmpty $ NE.drop (length ys) xs
      let extras1 = M.differenceWith diffDrop items1 items2
      let extras2 = M.differenceWith diffDrop items2 items1
      newTail <- freshInferenceName LabeledRowKind
      unifyExtLabeledItems (Ext NoLabeledItems t1)
                           (Ext (LabeledItems extras2) (Just newTail))
      unifyExtLabeledItems (Ext NoLabeledItems t2)
                           (Ext (LabeledItems extras1) (Just newTail))

unifyEff :: (MonadSolver m, Fallible m) => EffectRow -> EffectRow -> m ()
unifyEff r1 r2 = do
  r1' <- zonk r1
  r2' <- zonk r2
  vs <- looks solverVars
  case (r1', r2') of
    _ | r1' == r2' -> return ()
    (r, EffectRow effs (Just v)) | S.null effs && v `isin` vs -> bindQ (v:>EffKind) (Eff r)
    (EffectRow effs (Just v), r) | S.null effs && v `isin` vs -> bindQ (v:>EffKind) (Eff r)
    (EffectRow effs1 t1, EffectRow effs2 t2) | not (S.null effs1 || S.null effs2) -> do
      let extras1 = effs1 `S.difference` effs2
      let extras2 = effs2 `S.difference` effs1
      newRow <- freshEff
      unifyEff (EffectRow mempty t1) (extendEffRow extras2 newRow)
      unifyEff (extendEffRow extras1 newRow) (EffectRow mempty t2)
    _ -> throw TypeErr ""

bindQ :: (MonadSolver m, Fallible m) => Var -> Type -> m ()
bindQ v t | v `occursIn` t = throw TypeErr $ "Occurs check failure: " ++ pprint (v, t)
          | hasSkolems t = throw TypeErr "Can't unify with skolem vars"
          | otherwise = extend $ mempty { solverSub = v@>SubstVal t }

hasSkolems :: HasVars a => a -> Bool
hasSkolems x = not $ null [() | Name Skolem _ _ <- envNames $ freeVars x]

occursIn :: HasVars a => Var -> a -> Bool
occursIn v t = v `isin` freeVars t

renameForPrinting :: HasVars a => Subst a => a -> (a, [Var])
renameForPrinting x = (scopelessSubst substEnv x, newNames)
  where
    fvs = freeVars x
    infVars = filter ((== InferenceName) . nameSpace . varName) $ envAsVars fvs
    newNames = [ genFresh (fromString name) fvs :> ty
               | (~(_ :> AtomBinderInfo ty _ ), name) <- zip infVars nameList]
    substEnv = fold $ zipWith (\v v' -> v@> SubstVal (Var v')) infVars newNames
    nameList = map (:[]) ['a'..'z'] ++ map show [(0::Int)..]

instance Semigroup SolverEnv where
  -- TODO: as an optimization, don't do the subst when sub2 is empty
  -- TODO: make concatenation more efficient by maintaining a reverse-lookup map
  SolverEnv scope1 sub1 def1 del1 <> SolverEnv scope2 sub2 def2 del2 =
    SolverEnv (scope1' <> scope2) (sub1' <> sub2) (def1' <> def2) (del1' <> del2)
    where
      scope1' = fmap (scopelessSubst sub2) scope1
      sub1' = fmap (scopelessSubst sub2) sub1
      def1' = fmap (scopelessSubst sub2) def1
      del1' = fmap (scopelessSubst sub2) del1

instance Monoid SolverEnv where
  mempty = SolverEnv mempty mempty mempty mempty
  mappend = (<>)

typeReduceScoped :: MonadBuilder m => m Atom -> m (Either (Scope, Atom) Atom)
typeReduceScoped m = do
  block <- buildScoped m
  scope <- getScope
  return $ typeReduceBlock scope block
