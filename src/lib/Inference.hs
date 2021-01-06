-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Inference (inferModule, synthModule) where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Except hiding (Except)
import Data.Foldable (fold, toList, asum)
import Data.Functor
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import Data.String (fromString)
import qualified Data.Set as S
import Data.Text.Prettyprint.Doc

import Syntax
import Interpreter (indicesNoIO)
import Embed  hiding (sub)
import Env
import Type
import PPrint
import Cat
import Util

type UInferM = ReaderT SubstEnv (ReaderT SrcCtx ((EmbedT (SolverT (Either Err)))))

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

inferModule :: TopEnv -> UModule -> Except Module
inferModule scope (UModule decls) = do
  ((), (bindings, decls')) <- runUInferM mempty scope $
                                mapM_ (inferUDecl True) decls
  let bindings' = envFilter bindings \(_, b) -> case b of
                    DataBoundTypeCon _   -> True
                    DataBoundDataCon _ _ -> True
                    _ -> False
  return $ Module Typed decls' bindings'

runUInferM :: (Subst a, Pretty a)
           => SubstEnv -> Scope -> UInferM a -> Except (a, (Scope, Nest Decl))
runUInferM env scope m = runSolverT $
  runEmbedT (runReaderT (runReaderT m env) Nothing) scope

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
instantiateSigma f = case getType f of
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
  UVar v -> lookupSourceVar v >>= instantiateSigma >>= matchRequirement
  ULam (p, ann) ImplicitArrow body -> do
    argTy <- checkAnn ann
    x <- freshType argTy
    withBindPat p x $ checkOrInferRho body reqTy
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
    (xVal, embedEnv@(_, xDecls)) <- embedScoped $ checkSigma x Suggest (absArgType piTy)
    (xVal', arr') <- case piTy of
      Abs b rhs@(arr', _) -> case b `isin` freeVars rhs of
        False -> embedExtend embedEnv $> (xVal, arr')
        True  -> do
          xValMaybeRed <- flip typeReduceBlock (Block xDecls (Atom xVal)) <$> getScope
          case xValMaybeRed of
            Just xValRed -> return (xValRed, fst $ applyAbs piTy xValRed)
            Nothing      -> addSrcContext' xPos $ do
              throw TypeErr $ "Dependent functions can only be applied to fully " ++
                              "evaluated expressions. Bind the argument to a name " ++
                              "before you apply the function."
    addEffects $ arrowEff arr'
    appVal <- emitZonked $ App fVal xVal'
    instantiateSigma appVal >>= matchRequirement
  UPi (pat, ann) arr ty -> do
    -- TODO: make sure there's no effect if it's an implicit or table arrow
    -- TODO: check leaks
    ann' <- checkAnn ann
    piTy <- case pat of
      UnderscoreUPat -> buildPi (Ignore ann') $ const $
                          (,) <$> mapM checkUEffRow arr <*> checkUType ty
      _ -> withNameHint ("pat" :: Name) $ buildPi b \x ->
        withBindPat pat x $ (,) <$> mapM checkUEffRow arr <*> checkUType ty
        where b = case pat of
                    -- Note: The binder name becomes part of the type, so we
                    -- need to keep the same name used in the pattern.
                    WithSrc _ (UPatBinder (Bind (v:>()))) -> Bind (v:>ann')
                    _ -> Ignore ann'
    matchRequirement piTy
  UDecl decl body -> do
    env <- inferUDecl False decl
    extendR env $ checkOrInferRho body reqTy
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
      TypeCon def params -> do
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
  UTabCon xs -> inferTabCon xs reqTy >>= matchRequirement
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
  UIntLit  x  -> matchRequirement $ Con $ Lit  $ Int32Lit $ fromIntegral x
  UFloatLit x -> matchRequirement $ Con $ Lit  $ Float32Lit $ realToFrac x
  -- TODO: Make sure that this conversion is not lossy!
  where
    matchRequirement :: Atom -> UInferM Atom
    matchRequirement x = return x <*
      case reqTy of
        Infer -> return ()
        Check req -> constrainEq req (getType x)

lookupSourceVar :: UVar -> UInferM Atom
lookupSourceVar v = do
  substEnv <- ask
  case envLookup substEnv v of
    Just x -> return x
    Nothing -> do
      scope <- getScope
      let v' = asGlobal $ varName v
      case envLookup scope v' of
        Just (_, DataBoundTypeCon def    ) -> return $ TypeCon def []
        Just (_, DataBoundDataCon def con) -> return $ DataCon def [] con []
        Just (ty, _) -> return $ Var $ v':>ty
        Nothing -> throw UnboundVarErr $ pprint $ asGlobal $ varName v

unpackTopPat :: LetAnn -> UPat -> Expr -> UInferM ()
unpackTopPat letAnn pat expr = do
  atom <- emit expr
  bindings <- bindPat pat atom
  void $ flip traverseNames bindings \name val -> do
    let name' = asGlobal name
    checkNotInScope name'
    emitTo name' letAnn $ Atom val

inferUDecl :: Bool -> UDecl -> UInferM SubstEnv
inferUDecl topLevel (ULet letAnn (p, ann) rhs) = do
  -- We don't display global names in any visually distinct way from local names
  -- so avoid giving the name hint for top-level declarations. Otherwise we might
  -- end up with x = x decls in the module (with left x being global and right being local).
  let nameHint = if topLevel then liftM id else withPatHint p
  val <- nameHint $ case ann of
    Nothing -> inferSigma rhs
    Just ty -> do
      ty' <- zonk =<< checkUType ty
      let reqCon = if null (toList $ freeVars ty') then Concrete else Suggest
      checkSigma rhs reqCon ty'
  expr <- zonk $ Atom val
  if topLevel
    then unpackTopPat letAnn p expr $> mempty
    else bindPat p val
inferUDecl True (UData tc dcs) = do
  (tc', paramBs) <- inferUConDef tc
  dataDef <- buildDataDef tc' paramBs \params -> do
    extendR (newEnv paramBs params) $ forM dcs \dc ->
      uncurry DataConDef <$> inferUConDef dc
  checkDataDefShadows dataDef
  emitConstructors dataDef
  return mempty
inferUDecl True (UInterface superclasses tc methods) = do
  (tc', paramBs) <- inferUConDef tc
  dataDef <- buildDataDef tc' paramBs \params -> do
    extendR (newEnv paramBs params) $ do
      conName <- freshClassGenName
      superclasses' <- mkLabeledItems <$> mapM mkSuperclass superclasses
      methods'      <- mkLabeledItems <$> mapM mkMethod     methods
      return $ ClassDictDef conName superclasses' methods'
  checkDataDefShadows dataDef
  emitConstructors      dataDef
  emitSuperclassGetters dataDef
  emitMethodGetters     dataDef
  return mempty
inferUDecl True (UInstance argBinders instanceTy methods) = do
   instanceDict <- checkInstance argBinders instanceTy methods
   let instanceName = Name TypeClassGenName "instance" 0
   void $ emitTo instanceName InstanceLet $ Atom instanceDict
   return mempty
inferUDecl False (UData      _ _  ) = error "data definitions should be top-level"
inferUDecl False (UInterface _ _ _) = error "interface definitions should be top-level"
inferUDecl False (UInstance  _ _ _) = error "instance definitions should be top-level"

freshClassGenName :: MonadEmbed m => m Name
freshClassGenName = do
  scope <- getScope
  let v' = genFresh (Name TypeClassGenName "classgen" 0) scope
  embedExtend $ asFst $ v' @> (UnitTy, UnknownBinder)
  return v'

mkMethod :: UAnnBinder -> UInferM (Label, Type)
mkMethod (Ignore _) = error "Methods must have names"
mkMethod (Bind (v:>ty)) = do
  ty' <- checkUType ty
  return (nameToLabel v, ty')

mkSuperclass :: UType -> UInferM (Label, Type)
mkSuperclass ty = do
  ty' <- checkUType ty
  -- TODO: think about the scope of these names
  l <- freshClassGenName
  return (nameToLabel l, ty')

-- TODO: just make Name and Label the same thing
nameToLabel :: Name -> Label
nameToLabel = pprint

mkLabeledItems :: [(Label, a)] -> LabeledItems a
mkLabeledItems items = foldMap (uncurry labeledSingleton) items

emitConstructors :: DataDef -> UInferM ()
emitConstructors def@(DataDef tyConName _ dataConDefs) = do
  let tyConTy = getType $ TypeCon def []
  checkNotInScope tyConName
  extendScope $ tyConName @> (tyConTy, DataBoundTypeCon def)
  forM_ (zip [0..] dataConDefs) \(i, DataConDef dataConName _) -> do
    let dataConTy = getType $ DataCon def [] i []
    checkNotInScope dataConName
    extendScope $ dataConName @> (dataConTy, DataBoundDataCon def i)

emitMethodGetters :: DataDef -> UInferM ()
emitMethodGetters def@(DataDef _ paramBs (ClassDictDef _ _ methodTys)) = do
  forM_ (getLabels methodTys) \l -> do
    f <- buildImplicitNaryLam paramBs \params -> do
      buildLam (Bind ("d":> TypeCon def params)) ClassArrow \dict -> do
        return $ recGetHead l $ getProjection [1] dict
    let methodName = GlobalName $ fromString l
    checkNotInScope methodName
    emitTo methodName PlainLet $ Atom f
emitMethodGetters (DataDef _ _ _) = error "Not a class dictionary"

emitSuperclassGetters :: MonadEmbed m => DataDef -> m ()
emitSuperclassGetters def@(DataDef _ paramBs (ClassDictDef _ superclassTys _)) = do
  forM_ (getLabels superclassTys) \l -> do
    f <- buildImplicitNaryLam paramBs \params -> do
      buildLam (Bind ("d":> TypeCon def params)) PureArrow \dict -> do
        return $ recGetHead l $ getProjection [0] dict
    getterName <- freshClassGenName
    emitTo getterName SuperclassLet $ Atom f
emitSuperclassGetters (DataDef _ _ _) = error "Not a class dictionary"

checkNotInScope :: Name -> UInferM ()
checkNotInScope v = do
  scope <- getScope
  when (v `isin` scope) $ throw RepeatedVarErr $ pprint v

checkDataDefShadows :: DataDef -> UInferM ()
checkDataDefShadows (DataDef tc _ dataCons) = do
  checkShadows $ tc:dcs
  where dcs = [dc | DataConDef dc _ <- dataCons]

checkShadows :: [Name] -> UInferM ()
checkShadows vs = do
  mapM_ checkNotInScope vs
  case repeated vs of
    [] -> return ()
    (v:_) -> throw RepeatedVarErr $ pprint v

inferUConDef :: UConDef -> UInferM (Name, Nest Binder)
inferUConDef (UConDef v bs) = do
  (bs', _) <- embedScoped $ checkNestedBinders bs
  let v' = asGlobal v
  checkNotInScope v'
  return (v', bs')

checkNestedBinders :: Nest UAnnBinder -> UInferM (Nest Binder)
checkNestedBinders Empty = return Empty
checkNestedBinders (Nest b bs) = do
  b' <- mapM checkUType b
  extendScope (boundVars b')
  let env = case b' of Bind v   -> b' @> Var v
                       Ignore _ -> mempty
  bs' <- extendR env $ checkNestedBinders bs
  return $ Nest b' bs'

inferULam :: UPatAnn -> Arrow -> UExpr -> UInferM Atom
inferULam (p, ann) arr body = do
  argTy <- checkAnn ann
  -- TODO: worry about binder appearing in arrow?
  buildLam (Bind $ patNameHint p :> argTy) arr
    \x@(Var v) -> checkLeaks [v] $ withBindPat p x $ inferSigma body

checkULam :: UPatAnn -> UExpr -> PiType -> UInferM Atom
checkULam (p, ann) body piTy = do
  let argTy = absArgType piTy
  checkAnn ann >>= constrainEq argTy
  buildDepEffLam (Bind $ patNameHint p :> argTy)
    ( \x -> return $ fst $ applyAbs piTy x)
    \x@(Var v) -> checkLeaks [v] $ withBindPat p x $
                      checkSigma body Suggest $ snd $ applyAbs piTy x

checkInstance :: Nest UPatAnnArrow -> UType -> [UMethodDef] -> UInferM Atom
checkInstance Empty ty methods = do
  ty' <- checkUType ty
  case ty' of
    TypeCon def@(DataDef className _ _) params ->
      case applyDataDefParams def params of
        ClassDictDef _ superclassTys methodTys -> do
          let superclassHoles = fmap (Con . ClassDictHole Nothing) superclassTys
          methods' <- checkMethodDefs className methodTys methods
          return $ ClassDictCon def params superclassHoles methods'
        _ -> throw TypeErr $ "Not a valid instance type: " ++ pprint ty
    _     -> throw TypeErr $ "Not a valid instance type: " ++ pprint ty
checkInstance (Nest ((p, ann), arrow) rest) ty methods = do
  case arrow of
    ImplicitArrow -> return ()
    ClassArrow    -> return ()
    _ -> throw TypeErr $ "Not a valid arrow for an instance: " ++ pprint arrow
  argTy <- checkAnn ann
  buildLam (Bind $ patNameHint p :> argTy) (fromUArrow arrow) \x@(Var v) ->
    checkLeaks [v] $ withBindPat p x $ checkInstance rest ty methods


checkMethodDefs :: Name ->  LabeledItems Type -> [UMethodDef]
                -> UInferM (LabeledItems Atom)
checkMethodDefs className methodTys methods = do
  methods' <- liftM mkLabeledItems $ forM methods \(UMethodDef (v:>()) rhs) -> do
    let v' = nameToLabel v
    case lookupLabelHead methodTys v' of
      Nothing -> throw TypeErr $
        pprint v ++ " is not a method of " ++ pprint className
      Just methodTy -> do
        rhs' <- checkSigma rhs Suggest methodTy
        return (v', rhs')
  forM_ (reflectLabels methods') \(l,i) ->
    when (i > 0) $ throw TypeErr $ "Duplicate method: " ++ pprint l
  forM_ (reflectLabels methodTys) \(l,_) ->
    case lookupLabelHead methods' l of
      Nothing -> throw TypeErr $ "Missing method: " ++ pprint l
      Just _  -> return ()
  return methods'

checkUEffRow :: EffectRow -> UInferM EffectRow
checkUEffRow (EffectRow effs t) = do
   effs' <- liftM S.fromList $ mapM checkUEff $ toList effs
   t'    <- forM t \tv -> lookupVarName EffKind tv
   return $ EffectRow effs' t'
   where
     lookupVarName :: Type -> Name -> UInferM Name
     lookupVarName ty v = do
       -- TODO: more graceful errors on error
       Var (v':>ty') <- asks (!(v:>()))
       constrainEq ty ty'
       return v'

checkUEff :: Effect -> UInferM Effect
checkUEff eff = case eff of
  RWSEffect rws region -> do
    (Var (v:>ty)) <- lookupSourceVar (region:>())
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
           withBindPats (zip subPats xs) $ checkRho body reqTy
  return (conIdx, alt)

lookupDataCon :: Name -> UInferM (DataDef, Int)
lookupDataCon conName = do
  let conName' = asGlobal conName
  scope <- getScope
  case envLookup scope (conName':>()) of
    Just (_, DataBoundDataCon def con) -> return (def, con)
    Just _  -> throw TypeErr $ "Not a data constructor: " ++ pprint conName'
    Nothing -> throw UnboundVarErr $ pprint conName'

checkCasePat :: UPat -> Type -> UInferM (CaseAltIndex, [(UPat, Type)])
checkCasePat (WithSrc pos pat) scrutineeTy = addSrcContext' pos $ case pat of
  UPatCon conName ps -> do
    (def@(DataDef _ paramBs cons), con) <- lookupDataCon conName
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

withBindPats :: [(UPat, Atom)] -> UInferM a -> UInferM a
withBindPats pats body = foldr (uncurry withBindPat) body pats

withBindPat :: UPat -> Atom -> UInferM a -> UInferM a
withBindPat pat val m = do
  env <- bindPat pat val
  extendR env m

bindPat :: UPat -> Atom -> UInferM SubstEnv
bindPat pat val = evalCatT $ bindPat' pat val

-- CatT wrapper is used to prevent duplicate bindings within the same pattern,
-- e.g. (a, a) = (1, 2) should throw RepeatedVarErr
bindPat' :: UPat -> Atom -> CatT (Env ()) UInferM SubstEnv
bindPat' (WithSrc pos pat) val = addSrcContext pos $ case pat of
  UPatBinder b -> do
    usedVars <- look
    when (b `isin` usedVars) $ throw RepeatedVarErr $ pprint $ getName b
    extend (b @> ())
    return (b @> val)
  UPatUnit -> do
    lift $ constrainEq UnitTy (getType val)
    return mempty
  UPatPair p1 p2 -> do
    _    <- lift $ fromPairType (getType val)
    val' <- lift $ zonk val  -- ensure it has a pair type before unpacking
    x1   <- lift $ getFst val'
    x2   <- lift $ getSnd val'
    env1 <- bindPat' p1 x1
    env2 <- bindPat' p2 x2
    return $ env1 <> env2
  UPatCon conName ps -> do
    (def@(DataDef _ paramBs cons), con) <- lift $ lookupDataCon conName
    when (length cons /= 1) $ throw TypeErr $
      "sum type constructor in can't-fail pattern"
    let (DataConDef _ argBs) = cons !! con
    when (length argBs /= length ps) $ throw TypeErr $
      "Unexpected number of pattern binders. Expected " ++ show (length argBs)
                                             ++ " got " ++ show (length ps)
    params <- lift $ mapM (freshType . binderType) $ toList paramBs
    lift $ constrainEq (TypeCon def params) (getType val)
    xs <- lift $ zonk (Atom val) >>= emitUnpack
    fold <$> zipWithM bindPat' (toList ps) xs
  UPatRecord (Ext pats Nothing) -> do
    expectedTypes <- lift $ mapM (const $ freshType TyKind) pats
    lift $ constrainEq (RecordTy (NoExt expectedTypes)) (getType val)
    xs <- lift $ zonk (Atom val) >>= emitUnpack
    fold <$> zipWithM bindPat' (toList pats) xs
  UPatRecord (Ext pats (Just tailPat)) -> do
    wantedTypes <- lift $ mapM (const $ freshType TyKind) pats
    restType <- lift $ freshInferenceName LabeledRowKind
    let vty = getType val
    lift $ constrainEq (RecordTy $ Ext wantedTypes $ Just restType) vty
    -- Split the record.
    wantedTypes' <- lift $ zonk wantedTypes
    val' <- lift $ zonk val
    split <- lift $ emit $ Op $ RecordSplit wantedTypes' val'
    [left, right] <- lift $ getUnpacked split
    leftVals <- lift $ getUnpacked left
    env1 <- fold <$> zipWithM bindPat' (toList pats) leftVals
    env2 <- bindPat' tailPat right
    return $ env1 <> env2
  UPatVariant _ _ _ -> throw TypeErr "Variant not allowed in can't-fail pattern"
  UPatVariantLift _ _ -> throw TypeErr "Variant not allowed in can't-fail pattern"
  UPatTable ps -> do
    elemTy <- lift $ freshType TyKind
    let idxTy = FixedIntRange 0 (fromIntegral $ length ps)
    lift $ constrainEq (getType val) (idxTy ==> elemTy)
    let idxs = indicesNoIO idxTy
    unless (length idxs == length ps) $
      throw TypeErr $ "Incorrect length of table pattern: table index set has "
                      <> pprint (length idxs) <> " elements but there are "
                      <> pprint (length ps) <> " patterns."
    flip foldMapM (zip ps idxs) \(p, i) -> do
      v <- lift $ emitZonked $ App val i
      bindPat' p v

-- TODO (BUG!): this should just be a hint but something goes wrong if we don't have it
patNameHint :: UPat -> Name
patNameHint (WithSrc _ (UPatBinder (Bind (v:>())))) = v
patNameHint _ = "pat"

withPatHint :: UPat -> UInferM a -> UInferM a
withPatHint p m = withNameHint (patNameHint p) m

checkAnn :: Maybe UType -> UInferM Type
checkAnn ann = case ann of
  Just ty -> checkUType ty
  Nothing -> freshType TyKind

checkUType :: UType -> UInferM Type
checkUType ty = do
  reduced <- typeReduceScoped $ withEffects Pure $ checkRho ty TyKind
  case reduced of
    Just ty' -> return $ ty'
    Nothing  -> throw TypeErr $ "Can't reduce type expression: " ++ pprint ty

checkArrow :: Arrow -> UArrow -> UInferM ()
checkArrow ahReq ahOff = case (ahReq, ahOff) of
  (PlainArrow _, PlainArrow ()) -> return ()
  (LinArrow    , PlainArrow ()) -> return ()
  (LinArrow    , LinArrow     ) -> return ()
  (TabArrow  , TabArrow  ) -> return ()
  (ClassArrow, ClassArrow) -> return ()
  _ -> throw TypeErr $  " Wrong arrow type:" ++
                       "\nExpected: " ++ pprint ahReq ++
                       "\nActual:   " ++ pprint (fmap (const Pure) ahOff)

checkExtLabeledRow :: ExtLabeledItems UExpr UExpr -> UInferM (ExtLabeledItems Type Name)
checkExtLabeledRow (Ext types Nothing) = do
  types' <- mapM checkUType types
  return $ Ext types' Nothing
checkExtLabeledRow (Ext types (Just ext)) = do
  types' <- mapM checkUType types
  -- Only variables can have kind LabeledRowKind at the moment.
  Var (ext':>_) <- checkRho ext LabeledRowKind
  return $ Ext types' $ Just ext'

inferTabCon :: [UExpr] -> RequiredTy RhoType -> UInferM Atom
inferTabCon xs reqTy = do
  (tabTy, xs') <- case reqTy of
    Concrete tabTy@(TabTyAbs a) -> do
      let idx = indicesNoIO $ absArgType a
      -- TODO: Check length!!
      unless (length idx == length xs) $
        throw TypeErr "Table type doesn't match annotation"
      xs' <- mapM (\(x, i) -> checkOrInferRho x $ Concrete $ snd $ applyAbs a i) $ zip xs idx
      return (tabTy, xs')
    _ -> do
      elemTy <- case xs of
        []    -> freshType TyKind
        (x:_) -> getType <$> inferRho x
      let tabTy = (FixedIntRange 0 (fromIntegral $ length xs)) ==> elemTy
      case reqTy of
        Suggest sTy -> addContext context $ constrainEq sTy tabTy
          where context = "If attempting to construct a fixed-size table not " <>
                          "indexed by 'Fin n' for some n, this error may " <>
                          "indicate there was not enough information to infer " <>
                          "a concrete index set; try adding an explicit " <>
                          "annotation."
        Infer       -> return ()
        _           -> error "Missing case"
      xs' <- mapM (flip checkRho elemTy) xs
      return (tabTy, xs')
  emitZonked $ Op $ TabCon tabTy xs'

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
    Left _   -> False
    Right () -> True

openEffectRow :: EffectRow -> UInferM EffectRow
openEffectRow (EffectRow effs Nothing) = extendEffRow effs <$> freshEff
openEffectRow effRow = return effRow

addSrcContext' :: SrcCtx -> UInferM a -> UInferM a
addSrcContext' pos m = do
  env <- ask
  addSrcContext pos $ lift $
    local (const pos) $ runReaderT m env

getSrcCtx :: UInferM SrcCtx
getSrcCtx = lift ask

-- === typeclass dictionary synthesizer ===

-- We have two variants here because at the top level we want error messages and
-- internally we want to consider all alternatives.
type SynthPassM = SubstEmbedT (Either Err)
type SynthDictM = SubstEmbedT []

synthModule :: Scope -> Module -> Except Module
synthModule scope (Module Typed decls bindings) = do
  decls' <- fst . fst <$> runSubstEmbedT
              (traverseDecls (traverseHoles synthDictTop) decls) scope
  return $ Module Core decls' bindings
synthModule _ _ = error $ "Unexpected IR variant"

synthDictTop :: SrcCtx -> Type -> SynthPassM Atom
synthDictTop ctx ty = do
  scope <- getScope
  let solutions = runSubstEmbedT (synthDict ty) scope
  addSrcContext ctx $ case solutions of
    [] -> throw TypeErr $ "Couldn't synthesize a class dictionary for: " ++ pprint ty
    [(ans, env)] -> embedExtend env $> ans
    _ -> throw TypeErr $ "Multiple candidate class dictionaries for: " ++ pprint ty
           ++ "\n" ++ pprint solutions

traverseHoles :: (MonadReader SubstEnv m, MonadEmbed m)
              => (SrcCtx -> Type -> m Atom) -> TraversalDef m
traverseHoles fillHole = (traverseDecl recur, traverseExpr recur, synthPassAtom)
  where
    synthPassAtom atom = case atom of
      Con (ClassDictHole ctx ty) -> fillHole ctx =<< substEmbedR ty
      _ -> traverseAtom recur atom
    recur = traverseHoles fillHole

synthDict :: Type -> SynthDictM Atom
synthDict ty = do
  (d, bindingInfo) <- getBinding
  case bindingInfo of
    LetBound InstanceLet _ -> do
      block <- buildScoped $ inferToSynth $ instantiateAndCheck ty d
      traverseBlock (traverseHoles (const synthDict)) block >>= emitBlock
    LamBound ClassArrow -> do
      d' <- superclass d
      inferToSynth $ instantiateAndCheck ty d'
    _ -> empty

-- TODO: this doesn't de-dup, so we'll get multiple results if we have a
-- diamond-shaped hierarchy.
superclass :: Atom -> SynthDictM Atom
superclass dict = return dict <|> do
  (f, LetBound SuperclassLet _) <- getBinding
  inferToSynth $ tryApply f dict

getBinding :: SynthDictM (Atom, BinderInfo)
getBinding = do
  scope <- getScope
  (v, (ty, bindingInfo)) <- asum $ map return $ envPairs scope
  return (Var (v:>ty), bindingInfo)

inferToSynth :: (Pretty a, Subst a) => UInferM a -> SynthDictM a
inferToSynth m = do
  scope <- getScope
  case runUInferM mempty scope m of
    Left _ -> empty
    Right (x, (_, decls)) -> do
      mapM_ emitDecl decls
      return x

tryApply :: Atom -> Atom -> UInferM Atom
tryApply f x = do
  f' <- instantiateSigma f
  Pi (Abs b _) <- return $ getType f'
  constrainEq (binderType b) (getType x)
  emitZonked $ App f' x

instantiateAndCheck :: Type -> Atom -> UInferM Atom
instantiateAndCheck ty x = do
  x' <- instantiateSigma x
  constrainEq ty (getType x')
  return x'

-- === constraint solver ===

data SolverEnv = SolverEnv { solverVars :: Env Kind
                           , solverSub  :: Env Type }
type SolverT m = CatT SolverEnv m

runSolverT :: (MonadError Err m, Subst a, Pretty a)
           => CatT SolverEnv m a -> m a
runSolverT m = liftM fst $ flip runCatT mempty $ do
   ans <- m >>= zonk
   applyDefaults
   ans' <- zonk ans
   vs <- looks $ envNames . unsolved
   throwIf (not (null vs)) TypeErr $ "Ambiguous type variables: "
                                   ++ pprint vs ++ "\n\n" ++ pprint ans'
   return ans'

applyDefaults :: MonadCat SolverEnv m => m ()
applyDefaults = do
  vs <- looks unsolved
  forM_ (envPairs vs) \(v, k) -> case k of
    EffKind -> addSub v $ Eff Pure
    _ -> return ()
  where addSub v ty = extend $ SolverEnv mempty (v@>ty)

solveLocal :: Subst a => UInferM a -> UInferM a
solveLocal m = do
  (ans, env@(SolverEnv freshVars sub)) <- scoped $ do
    -- This might get expensive. TODO: revisit once we can measure performance.
    (ans, embedEnv) <- zonk =<< embedScoped m
    embedExtend embedEnv
    return ans
  extend $ SolverEnv (unsolved env) (sub `envDiff` freshVars)
  return ans

checkLeaks :: (HasType a, Subst a) => [Var] -> UInferM a -> UInferM a
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
unsolved (SolverEnv vs sub) = vs `envDiff` sub

freshInferenceName :: (MonadError Err m, MonadCat SolverEnv m) => Kind -> m Name
freshInferenceName k = do
  env <- look
  let v = genFresh (rawName InferenceName "?") $ solverVars env
  extend $ SolverEnv (v@>k) mempty
  return v

freshType ::  (MonadError Err m, MonadCat SolverEnv m) => Kind -> m Type
freshType EffKind = Eff <$> freshEff
freshType k = Var . (:>k) <$> freshInferenceName k

freshEff :: (MonadError Err m, MonadCat SolverEnv m) => m EffectRow
freshEff = EffectRow mempty . Just <$> freshInferenceName EffKind

constrainEq :: (MonadCat SolverEnv m, MonadError Err m)
             => Type -> Type -> m ()
constrainEq t1 t2 = do
  t1' <- zonk t1
  t2' <- zonk t2
  let ((t1Pretty, t2Pretty), infVars) = renameForPrinting (t1', t2')
  let msg =   "Expected: " ++ pprint t1Pretty
         ++ "\n  Actual: " ++ pprint t2Pretty
         ++ (if null infVars then "" else
               "\n(Solving for: " ++ pprint infVars ++ ")")
  addContext msg $ unify t1' t2'

zonk :: (Subst a, MonadCat SolverEnv m) => a -> m a
zonk x = do
  s <- looks solverSub
  return $ scopelessSubst s x

unify :: (MonadCat SolverEnv m, MonadError Err m)
       => Type -> Type -> m ()
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

unifyExtLabeledItems :: (MonadCat SolverEnv m, MonadError Err m)
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

unifyEff :: (MonadCat SolverEnv m, MonadError Err m)
         => EffectRow -> EffectRow -> m ()
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

bindQ :: (MonadCat SolverEnv m, MonadError Err m) => Var -> Type -> m ()
bindQ v t | v `occursIn` t = throw TypeErr $ "Occurs check failure: " ++ pprint (v, t)
          | hasSkolems t = throw TypeErr "Can't unify with skolem vars"
          | otherwise = extend $ mempty { solverSub = v@>t }

hasSkolems :: Subst a => a -> Bool
hasSkolems x = not $ null [() | Name Skolem _ _ <- envNames $ freeVars x]

occursIn :: Subst a => Var -> a -> Bool
occursIn v t = v `isin` freeVars t

renameForPrinting :: Subst a => a -> (a, [Var])
renameForPrinting x = (scopelessSubst substEnv x, newNames)
  where
    fvs = freeVars x
    infVars = filter ((== Just InferenceName) . nameSpace . varName) $ envAsVars fvs
    newNames = [ genFresh (fromString name) fvs :> fst (varAnn v)
               | (v, name) <- zip infVars nameList]
    substEnv = fold $ zipWith (\v v' -> v@>Var v') infVars newNames
    nameList = map (:[]) ['a'..'z'] ++ map show [(0::Int)..]

instance Semigroup SolverEnv where
  -- TODO: as an optimization, don't do the subst when sub2 is empty
  -- TODO: make concatenation more efficient by maintaining a reverse-lookup map
  SolverEnv scope1 sub1 <> SolverEnv scope2 sub2 =
    SolverEnv (scope1 <> scope2) (sub1' <> sub2)
    where sub1' = fmap (scopelessSubst sub2) sub1

instance Monoid SolverEnv where
  mempty = SolverEnv mempty mempty
  mappend = (<>)

typeReduceScoped :: MonadEmbed m => m Atom -> m (Maybe Atom)
typeReduceScoped m = do
  block <- buildScoped m
  scope <- getScope
  return $ typeReduceBlock scope block
