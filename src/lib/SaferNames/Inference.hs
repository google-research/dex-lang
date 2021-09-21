-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE ViewPatterns #-}

module SaferNames.Inference (inferModule) where

import Prelude hiding ((.), id)
import Control.Category
import Control.Applicative
import Control.Monad
import Data.Foldable (toList)
import Data.List (sortOn)
import Data.String (fromString)
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import SaferNames.NameCore
import SaferNames.Name
import SaferNames.Builder
import SaferNames.Syntax
import SaferNames.Type
import SaferNames.PPrint ()

import LabeledItems
import Err
import Util

inferModule :: Bindings n -> UModule n -> Except (Module n)
inferModule bindings uModule = runInfererM bindings do
  UModule decl sourceMap <- injectM uModule
  if isTopDecl decl
    then do
      Abs (RecEnvFrag bindingsFrag) sourceMap' <-
        buildScopedTop $ inferUDeclTop decl $ substM sourceMap
      return $ Module Typed id $
        EvaluatedModule bindingsFrag mempty sourceMap'
    else do
      Abs decls sourceMap' <-
        buildScoped $ inferUDeclLocal decl $ substM sourceMap
      return $ Module Typed decls $
        EvaluatedModule emptyEnv mempty sourceMap'

isTopDecl :: UDecl n l -> Bool
isTopDecl decl = case decl of
  ULet         _ _ _     -> False
  UDataDefDecl _ _ _     -> True
  UInterface   _ _ _ _ _ -> True
  UInstance    _ _ _ _ _ -> False

-- === Inferer monad ===

class (MonadFail2 m, Fallible2 m, Builder2 m, EnvReader Name m)
      => Inferer (m::MonadKind2)

data InfererM (i::S) (o::S) (a:: *)

runInfererM :: Bindings n
            -> (forall l. Ext n l => InfererM l l (e l))
            -> Except (e n)
runInfererM _ _ = undefined

instance Functor (InfererM i o) where
  fmap = undefined

instance Applicative (InfererM i o) where
  pure = undefined
  liftA2 = undefined

instance Monad (InfererM i o) where
  return = undefined
  (>>=) = undefined

instance MonadFail (InfererM i o) where
  fail = undefined

instance Fallible (InfererM i o) where
  throwErrs = undefined
  addErrCtx = undefined

instance Builder (InfererM i) where
  buildScoped _ = undefined
  buildScopedTop _ = undefined
  getAllowedEffects = undefined
  withAllowedEffects = undefined
  emitDecl = undefined
  emitBinding = undefined

instance BindingsReader (InfererM i) where
  addBindings = undefined

instance ScopeReader (InfererM i) where
  getDistinctEvidenceM = undefined
  addScope = undefined

instance Scopable (InfererM i) where
  withBindings _ _ = undefined

instance (EnvReader Name) InfererM where
  getEnv  = undefined
  withEnv = undefined

instance Inferer InfererM

constrainEq :: Inferer m => Type o -> Type o -> m i o ()
constrainEq = undefined

freshInferenceName :: Inferer m => Kind o -> m i o (AtomName o)
freshInferenceName = undefined

zonk :: (Inferer m, SubstE Name e) => e o -> m i o (e o)
zonk = undefined

freshType :: Inferer m => Kind o -> m i o (Type o)
freshType k = Var <$> freshInferenceName k

freshEff :: Inferer m => m i o (EffectRow o)
freshEff = EffectRow mempty . Just <$> freshInferenceName EffKind

typeReduceAtom :: Inferer m => Atom o -> m i o (Atom o)
typeReduceAtom = undefined

tryGetType :: (Inferer m, HasType e) => e o -> m i o (Type o)
tryGetType = undefined

getSrcCtx :: Inferer m => m i o SrcPosCtx
getSrcCtx = undefined

addSrcContext' :: Inferer m => SrcPosCtx -> m i o a -> m i o a
addSrcContext' = undefined

makeReqCon :: Inferer m => Type o -> m i o SuggestionStrength
makeReqCon = undefined

-- === actual inference pass ===

type SigmaType = Type  -- may     start with an implicit lambda
type RhoType   = Type  -- doesn't start with an implicit lambda
data SuggestionStrength = Suggest | Concrete  deriving Show
data RequiredTy (e::E) (n::S) = Check SuggestionStrength (e n)
                              | Infer
                                deriving Show

checkSigma :: (Emits o, Inferer m) => UExpr i
           -> SuggestionStrength
           -> SigmaType o -> m i o (Atom o)
checkSigma expr reqCon sTy = case sTy of
  Pi piTy@(PiType arrow _ _ _)
    | arrow `elem` [ImplicitArrow, ClassArrow] -> case expr of
        WithSrcE _ (ULam lam@(ULamExpr arrow' _ _))
          | arrow == arrow' ->
            -- is this even reachable? we don't have syntax for implicit/class lambda
            checkULam lam piTy
        -- we have to add the lambda argument corresponding to the implicit pi
        -- type argument
        _ -> do
          buildPureLam arrow (piArgType piTy) \x -> do
            piTy' <- injectM piTy
            (Pure, bodyTy) <- instantiatePi piTy' (Var x)
            checkSigma expr reqCon bodyTy
  _ -> checkOrInferRho expr (Check reqCon sTy)

inferSigma :: (Emits o, Inferer m) => UExpr i -> m i o (Atom o)
inferSigma (WithSrcE pos expr) = case expr of
  ULam lam@(ULamExpr ImplicitArrow _ _) ->
    addSrcContext' pos $ inferULam Pure lam
  _ -> inferRho (WithSrcE pos expr)

checkRho :: (Emits o, Inferer m) => UExpr i -> RhoType o -> m i o (Atom o)
checkRho expr ty = checkOrInferRho expr (Check Suggest ty)

inferRho :: (Emits o, Inferer m) => UExpr i -> m i o (Atom o)
inferRho expr = checkOrInferRho expr Infer

instantiateSigma :: (Emits o, Inferer m) => Atom o -> m i o (Atom o)
instantiateSigma f = do
  ty <- tryGetType f
  case ty of
    Pi (PiType ImplicitArrow b _ _) -> do
      x <- freshType $ binderType b
      ans <- emitZonked $ App f x
      instantiateSigma $ Var ans
    Pi (PiType ClassArrow b _ _) -> do
      ctx <- getSrcCtx
      ans <- emitZonked $ App f (Con $ ClassDictHole ctx $ binderType b)
      instantiateSigma $ Var ans
    _ -> return f

checkOrInferRho :: forall m i o.
                   (Emits o, Inferer m)
                => UExpr i -> RequiredTy RhoType o -> m i o (Atom o)
checkOrInferRho (WithSrcE pos expr) reqTy = do
 addSrcContext' pos $ case expr of
  UVar ~(InternalName v) -> do
    substM v >>= inferUVar >>= instantiateSigma >>= matchRequirement
  ULam (ULamExpr ImplicitArrow (UPatAnn p ann) body) -> do
    argTy <- checkAnn ann
    v <- freshInferenceName argTy
    bindLamPat p v $ checkOrInferRho body reqTy
  ULam lamExpr ->
    case reqTy of
      Check _ (Pi piTy) -> checkULam lamExpr piTy
      Check _ _ -> inferULam Pure lamExpr >>= matchRequirement
      Infer   -> inferULam Pure lamExpr
  UFor dir (UForExpr b body) -> do
    allowedEff <- getAllowedEffects
    let uLamExpr = ULamExpr TabArrow b body
    lam <- case reqTy of
      Check _ (Pi piType) -> checkULam uLamExpr piType
      Check _ _ -> inferULam allowedEff uLamExpr
      Infer   -> inferULam allowedEff uLamExpr
    result <- liftM Var $ emitZonked $ Hof $ For (RegularFor dir) lam
    matchRequirement result
  UApp arr f x@(WithSrcE xPos _) -> do
    f' <- inferRho f
    -- NB: We never infer dependent function types, but we accept them, provided they
    --     come with annotations. So, unless we already know that the function is
    --     dependent here (i.e. the type of the zonk comes as a dependent Pi type),
    --     then nothing in the remainder of the program can convince us that the type
    --     is dependent. Also, the Pi binder is never considered to be in scope for
    --     inference variables, so they cannot get unified with it. Hence, this zonk
    --     is safe and doesn't make the type checking depend on the program order.
    infTy <- getType =<< zonk f'
    piTy  <- addSrcContext' (srcPos f) $ fromPiType True arr infTy
    considerNonDepPiType piTy >>= \case
      Just (_, argTy, effs, _) -> do
        x' <- checkSigma x Suggest argTy
        addEffects effs
        appVal <- emitZonked $ App f' x'
        instantiateSigma (Var appVal) >>= matchRequirement
      Nothing -> do
        maybeX <- buildBlockReduced do
          argTy' <- injectM $ piArgType piTy
          checkSigma x Suggest argTy'
        case maybeX of
          Nothing -> addSrcContext' xPos $ do
            throw TypeErr $ "Dependent functions can only be applied to fully " ++
                            "evaluated expressions. Bind the argument to a name " ++
                            "before you apply the function."
          Just x' -> do
            (effs, _) <- instantiatePi piTy x'
            addEffects effs
            appVal <- emitZonked $ App f' x'
            instantiateSigma (Var appVal) >>= matchRequirement
  UPi (UPiExpr arr (UPatAnn (WithSrcB pos' pat) ann) effs ty) -> do
    -- TODO: make sure there's no effect if it's an implicit or table arrow
    ann' <- checkAnn ann
    piTy <- addSrcContext' pos' case pat of
      UPatBinder UIgnore -> do
        effs' <- checkUEffRow effs
        ty' <- checkUType ty
        buildNonDepPi arr ann' effs' ty'
      _ -> buildPi arr ann' \v -> do
        Abs decls (PairE effs' ty') <- buildScoped do
          v' <- injectM v
          bindLamPat (WithSrcB pos' pat) v' do
            effs' <- checkUEffRow effs
            ty'   <- checkUType   ty
            return $ PairE effs' ty'
        case decls of
          Empty -> return (effs', ty')
          -- TODO: make an acceptable user-facing error
          _ -> error "pi type shouldn't require decls to normalize"
    matchRequirement piTy
  UDecl (UDeclExpr decl body) -> do
    inferUDeclLocal decl $ checkOrInferRho body reqTy
  UCase scrut alts -> do
    scrut' <- inferRho scrut
    scrutTy <- getType scrut'
    reqTy' <- case reqTy of
      Infer -> freshType TyKind
      Check _ req -> return req
    alts' <- mapM (checkCaseAlt reqTy' scrutTy) alts
    scrut'' <- zonk scrut'
    buildSortedCase scrut'' alts' reqTy'
  UTabCon xs -> inferTabCon xs reqTy >>= matchRequirement
  UIndexRange low high -> do
    n <- freshType TyKind
    low'  <- mapM (flip checkRho n) low
    high' <- mapM (flip checkRho n) high
    matchRequirement $ TC $ IndexRange n low' high'
  UHole -> case reqTy of
    Infer -> throw MiscErr "Can't infer type of hole"
    Check _ ty -> freshType ty
  UTypeAnn val ty -> do
    ty' <- zonk =<< checkUType ty
    reqCon <- makeReqCon ty'
    val' <- checkSigma val reqCon ty'
    matchRequirement val'
  UPrimExpr prim -> do
    prim' <- forM prim $ inferRho >=> typeReduceAtom
    val <- case prim' of
      TCExpr  e -> return $ TC e
      ConExpr e -> return $ Con e
      OpExpr  e -> Var <$> emitZonked (Op e)
      HofExpr e -> Var <$> emitZonked (Hof e)
    matchRequirement val
  URecord (Ext items Nothing) -> do
    items' <- mapM inferRho items
    matchRequirement $ Record items'
  URecord (Ext items (Just ext)) -> do
    items' <- mapM inferRho items
    restTy <- freshInferenceName LabeledRowKind
    ext' <- zonk =<< (checkRho ext $ RecordTy $ Ext NoLabeledItems $ Just restTy)
    matchRequirement =<< emitOp (RecordCons items' ext')
  UVariant labels@(LabeledItems lmap) label value -> do
    value' <- inferRho value
    prevTys <- mapM (const $ freshType TyKind) labels
    rest <- freshInferenceName LabeledRowKind
    ty <- getType value'
    let items = prevTys <> labeledSingleton label ty
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
    matchRequirement =<< emitOp (VariantLift prev value')
  UIntLit  x  -> matchRequirement $ Con $ Lit  $ Int32Lit $ fromIntegral x
  UFloatLit x -> matchRequirement $ Con $ Lit  $ Float32Lit $ realToFrac x
  -- TODO: Make sure that this conversion is not lossy!
  where
    matchRequirement :: Atom o -> m i o (Atom o)
    matchRequirement x = return x <*
      case reqTy of
        Infer -> return ()
        Check _ req -> do
          ty <- getType x
          constrainEq req ty

-- === sorting case alternatives ===

data IndexedAlt n = IndexedAlt CaseAltIndex (Alt n)

instance InjectableE IndexedAlt where
  injectionProofE = undefined

buildNthOrderedAlt :: (Emits n, Builder m)
                   => [IndexedAlt n] -> Type n -> Type n -> Int -> [AtomName n]
                   -> m n (Atom n)
buildNthOrderedAlt alts scrutTy resultTy i vs = do
  case lookup (nthCaseAltIdx scrutTy i) [(idx, alt) | IndexedAlt idx alt <- alts] of
    Nothing -> do
      resultTy' <- injectM resultTy
      emitOp $ ThrowError resultTy'
    Just alt -> applyNaryAbs alt vs >>= emitBlock

-- converts from the ordinal index used in the core IR to the more complicated
-- `CaseAltIndex` used in the surface IR.
nthCaseAltIdx :: Type n -> Int -> CaseAltIndex
nthCaseAltIdx ty i = case ty of
  TypeCon _ _ -> ConAlt i
  VariantTy (NoExt types) -> case lookup i pairedIndices of
    Just idx -> idx
    Nothing -> error "alt index out of range"
    where
      pairedIndices :: [(Int, CaseAltIndex)]
      pairedIndices = enumerate $ [VariantAlt l idx | (l, idx, _) <- toList (withLabels types)]
  _ -> error $ "can't pattern-match on: " <> pprint ty

buildMonomorphicCase :: (Emits n, Builder m) => [IndexedAlt n] -> Atom n -> Type n -> m n (Atom n)
buildMonomorphicCase alts scrut resultTy = do
  scrutTy <- getType scrut
  buildCase scrut resultTy \i vs -> do
    ListE alts' <- injectM $ ListE alts
    scrutTy'    <- injectM scrutTy
    resultTy'   <- injectM resultTy
    buildNthOrderedAlt alts' scrutTy' resultTy' i vs

buildSortedCase :: (Fallible1 m, Builder m, Emits n)
                 => Atom n -> [IndexedAlt n] -> Type n
                 -> m n (Atom n)
buildSortedCase scrut alts resultTy = do
  scrutTy <- getType scrut
  case scrutTy of
    TypeCon _ _ -> buildMonomorphicCase alts scrut resultTy
    VariantTy (Ext types tailName) -> do
      case filter isVariantTailAlt alts of
        [] -> case tailName of
          Nothing ->
            -- We already know the type exactly, so just emit a case.
            buildMonomorphicCase alts scrut resultTy
          Just _ -> do
            -- Split off the types we don't know about, mapping them to a
            -- runtime error.
            buildSplitCase types scrut resultTy
              (\v -> do ListE alts' <- injectM $ ListE alts
                        resultTy'   <- injectM resultTy
                        buildMonomorphicCase alts' (Var v) resultTy')
              (\_ -> do resultTy' <- injectM resultTy
                        emitOp $ ThrowError resultTy')
        [IndexedAlt (VariantTailAlt (LabeledItems skippedItems)) tailAlt] -> do
            -- Split off the types skipped by the tail pattern.
            let splitLeft fvs ltys = NE.fromList $ NE.take (length ltys) fvs
            let left = LabeledItems $ M.intersectionWith splitLeft
                        (fromLabeledItems types) skippedItems
            checkNoTailOverlaps alts left
            buildSplitCase left scrut resultTy
              (\v -> do ListE alts' <- injectM $ ListE alts
                        resultTy'   <- injectM resultTy
                        buildMonomorphicCase alts' (Var v) resultTy')
              (\v -> do tailAlt' <- injectM tailAlt
                        applyNaryAbs tailAlt' [v] >>= emitBlock )
        _ -> throw TypeErr "Can't specify more than one variant tail pattern."
    _ -> fail $ "Unexpected case expression type: " <> pprint scrutTy

-- Make sure all of the alternatives are exclusive with the tail pattern (could
-- technically allow overlap but this is simpler). Split based on the tail
-- pattern's skipped types.
checkNoTailOverlaps :: Fallible1 m => [IndexedAlt n] -> LabeledItems (Type n) ->  m n ()
checkNoTailOverlaps alts (LabeledItems tys) = do
  forM_ alts \(IndexedAlt (VariantAlt label i) _) ->
    case M.lookup label tys of
      Just tys' | i <= length tys' -> return ()
      _ -> throw TypeErr "Variant explicit alternatives overlap with tail pattern."

isVariantTailAlt :: IndexedAlt n -> Bool
isVariantTailAlt (IndexedAlt (VariantTailAlt _) _) = True
isVariantTailAlt _ = False

-- ===

inferUVar :: Inferer m => UVar o -> m i o (Atom o)
inferUVar = \case
  UAtomVar v ->
    return $ Var v
  UTyConVar v -> do
    -- TODO: we shouldn't need these tildes because it's the only valid case
    ~(TyConBinding   dataDefName) <- lookupBindings v
    ~(DataDefBinding dataDef)     <- lookupBindings dataDefName
    return $ TypeCon (dataDefName, dataDef) []
  UDataConVar v -> do
   -- TODO: we shouldn't need these tildes because it's the only valid case
    ~(DataConBinding dataDefName idx) <- lookupBindings v
    ~(DataDefBinding dataDef)         <- lookupBindings dataDefName
    return $ DataCon (pprint v) (dataDefName, dataDef) [] idx []
  UClassVar v -> do
    ~(ClassBinding (ClassDef _ _ dataDef)) <- lookupBindings v
    return $ TypeCon dataDef []
  UMethodVar v -> do
    ~(MethodBinding _ _ getter) <- lookupBindings v
    return getter

inferUDeclLocal ::  (Emits o, Inferer m) => UDecl i i' -> m i' o a -> m i o a
inferUDeclLocal (ULet letAnn (UPatAnn p ann) rhs) cont = do
  val <- case ann of
    Nothing -> inferSigma rhs
    Just ty -> do
      ty' <- zonk =<< checkUType ty
      reqCon <- makeReqCon ty'
      checkSigma rhs reqCon ty'
  expr <- zonk $ Atom val
  var <- emitDecl (getNameHint p) letAnn expr
  bindLamPat p var cont
inferUDeclLocal (UInstance ~(InternalName className) argBinders params methods maybeName) cont = do
  className' <- substM className
  instanceDict <- checkInstanceArgs argBinders do
                    className'' <- injectM className'
                    checkInstanceBody className'' params methods
  case maybeName of
    RightB UnitB  -> do
      void $ emitDecl "instance" InstanceLet $ Atom instanceDict
      cont
    JustB instanceName -> do
      instanceVal <- emitDecl (getNameHint instanceName) PlainLet (Atom instanceDict)
      extendEnv (instanceName @> instanceVal) cont
    _ -> error "impossible"
inferUDeclLocal _ _ = error "not a local decl"

inferUDeclTop ::  (EmitsTop o, Inferer m) => UDecl i i' -> m i' o a -> m i o a
inferUDeclTop (UDataDefDecl def tc dcs) cont = do
  def' <- inferDataDef def >>= emitDataDef
  tc' <- emitTyConName def'
  dcs' <- mapM (emitDataConName def') [0..(nestLength dcs - 1)]
  extendEnv (tc @> tc' <.> dcs @@> dcs') cont
inferUDeclTop (UInterface paramBs superclasses methodTys className methodNames) cont = do
  let classPrettyName   = fromString (pprint className) :: SourceName
  let methodPrettyNames = map fromString (nestToList pprint methodNames) :: [SourceName]
  classDef <- inferInterfaceDataDef classPrettyName methodPrettyNames
                paramBs superclasses methodTys
  className' <- emitClassDef classDef
  mapM_ (emitSuperclass className') [0..(length superclasses - 1)]
  methodNames' <- forM (enumerate methodPrettyNames) \(i, prettyName) ->
                    emitMethodType (getNameHint prettyName) className' i
  extendEnv (className @> className' <.> methodNames @@> methodNames') cont
inferUDeclTop _ _ = error "not a top decl"

inferDataDef :: Inferer m => UDataDef i -> m i o (DataDef o)
inferDataDef (UDataDef (tyConName, paramBs) dataCons) = do
  Abs paramBs' (ListE dataCons') <-
    withNestedUBinders paramBs \_ -> do
      dataCons' <- mapM inferDataCon dataCons
      return $ ListE dataCons'
  return $ DataDef tyConName paramBs' dataCons'

inferDataCon :: Inferer m => (SourceName, UDataDefTrail i) -> m i o (DataConDef o)
inferDataCon (sourceName, UDataDefTrail argBs) = do
  argBs' <- checkUBinders (EmptyAbs argBs)
  return $ DataConDef sourceName argBs'

inferInterfaceDataDef :: (EmitsTop o, Inferer m)
                      => SourceName -> [SourceName]
                      -> Nest (UAnnBinder AtomNameC) i i'
                      -> [UType i'] -> [UType i']
                      -> m i o (ClassDef o)
inferInterfaceDataDef className methodNames paramBs superclasses methods = do
  paramBs' <- checkUBinders $ EmptyAbs paramBs
  dictDef <- buildNewtype className paramBs' \params -> do
    extendEnv (paramBs @@> params) do
      superclasses' <- mapM checkUType superclasses
      methods'      <- mapM checkUType methods
      return $ PairTy (ProdTy superclasses') (ProdTy methods')
  defName <- emitDataDef dictDef
  return $ ClassDef className methodNames (defName, dictDef)

withNestedUBinders :: (Inferer m, HasNamesE e)
                  => Nest (UAnnBinder AtomNameC) i i'
                  -> (forall o'. Ext o o' => [AtomName o'] -> m i' o' (e o'))
                  -> m i o (Abs (Nest Binder) e o)
withNestedUBinders bs cont = case bs of
  Empty -> Abs Empty <$> cont []
  Nest b rest -> do
    ext1 <- idExt
    Abs b' (Abs rest' body) <- withUBinder b \name -> do
      ext2 <- injectExt ext1
      withNestedUBinders rest \names -> do
        ExtW <- injectExt ext2
        name' <- injectM name
        cont (name':names)
    return $ Abs (Nest b' rest') body

withUBinder :: (Inferer m, HasNamesE e)
            => UAnnBinder AtomNameC i i'
            -> (forall o'. Ext o o' => AtomName o' -> m i' o' (e o'))
            -> m i o (Abs Binder e o)
withUBinder (UAnnBinder b ann) cont = do
  ann' <- checkUType ann
  buildAbs ann' \name -> extendEnv (b @> name) $ cont name

checkUBinders :: Inferer m
              => EmptyAbs (Nest (UAnnBinder AtomNameC)) i
              -> m i o (EmptyAbs (Nest Binder) o)
checkUBinders (EmptyAbs bs) = withNestedUBinders bs \_ -> return UnitE
checkUBinders _ = error "impossible"

inferULam :: Inferer m => EffectRow o -> ULamExpr i -> m i o (Atom o)
inferULam effs (ULamExpr arrow (UPatAnn p ann) body) = do
  argTy <- checkAnn ann
  buildLam arrow argTy effs \v ->
    bindLamPat p v $ inferSigma body

checkULam :: Inferer m => ULamExpr i -> PiType o -> m i o (Atom o)
checkULam (ULamExpr _ (UPatAnn p ann) body) piTy = do
  let argTy = piArgType piTy
  checkAnn ann >>= constrainEq argTy
  -- XXX: we're ignoring the ULam arrow here. Should we be checking that it's
  -- consistent with the arrow supplied by the pi type?
  buildDepEffLam (piArrow piTy) argTy
    (\v -> do
        piTy' <- injectM piTy
        fst <$> instantiatePi piTy' (Var v) )
     \v -> bindLamPat p v do
        piTy' <- injectM piTy
        (_, resultTy) <- instantiatePi piTy' (Var v)
        checkSigma body Suggest resultTy

checkInstanceArgs
  :: (Emits o, Inferer m)
  => Nest UPatAnnArrow i i'
  -> (forall o'. (Emits o', Ext o o') =>  m i' o' (Atom o'))
  -> m i o (Atom o)
checkInstanceArgs Empty cont = cont
checkInstanceArgs (Nest (UPatAnnArrow (UPatAnn p ann) arrow) rest) cont = do
  case arrow of
    ImplicitArrow -> return ()
    ClassArrow    -> return ()
    _ -> throw TypeErr $ "Not a valid arrow for an instance: " ++ pprint arrow
  argTy <- checkAnn ann
  ext1 <- idExt
  buildLam arrow argTy Pure \v -> do
    ext2 <- injectExt ext1
    bindLamPat p v $
      checkInstanceArgs rest do
        ExtW <- injectExt ext2
        cont

checkInstanceBody :: (Emits o, Inferer m)
                  => ClassName o
                  -> [UType i]
                  -> [UMethodDef i]
                  -> m i o (Atom o)
checkInstanceBody className params methods = do
  ClassDef _ methodNames def <- getClassDef className
  params' <- mapM checkUType params
  Just dictTy <- fromNewtype <$> applyDataDefParams (snd def) params'
  PairTy (ProdTy superclassTys) (ProdTy methodTys) <- return dictTy
  let superclassHoles = fmap (Con . ClassDictHole Nothing) superclassTys
  methodsChecked <- mapM (checkMethodDef className methodTys) methods
  let (idxs, methods') = unzip $ sortOn fst $ methodsChecked
  forM_ (repeated idxs) \i ->
    throw TypeErr $ "Duplicate method: " ++ pprint (methodNames!!i)
  forM_ ([0..(length methodTys - 1)] `listDiff` idxs) \i ->
    throw TypeErr $ "Missing method: " ++ pprint (methodNames!!i)
  return $ DataCon "instance-dict" def params' 0 [PairVal (ProdVal superclassHoles)
                                                          (ProdVal methods')]

checkMethodDef :: (Emits o, Inferer m)
               => ClassName o -> [Type o] -> UMethodDef i -> m i o (Int, Atom o)
checkMethodDef className methodTys (UMethodDef ~(InternalName v) rhs) = do
  MethodBinding className' i _ <- substM v >>= lookupBindings
  when (className /= className') $
    throw TypeErr $ pprint v ++ " is not a method of " ++ pprint className
  let methodTy = methodTys !! i
  rhs' <- checkSigma rhs Suggest methodTy
  return (i, rhs')

checkUEffRow :: Inferer m => UEffectRow i -> m i o (EffectRow o)
checkUEffRow (EffectRow effs t) = do
   effs' <- liftM S.fromList $ mapM checkUEff $ toList effs
   t' <- forM t \(InternalName v) -> do
            v' <- substM v
            constrainVarTy v' EffKind
            return v'
   return $ EffectRow effs' t'

checkUEff :: Inferer m => UEffect i -> m i o (Effect o)
checkUEff eff = case eff of
  RWSEffect rws ~(InternalName region) -> do
    region' <- substM region
    constrainVarTy region' TyKind
    return $ RWSEffect rws region'
  ExceptionEffect -> return ExceptionEffect
  IOEffect        -> return IOEffect

constrainVarTy :: Inferer m => AtomName o -> Type o -> m i o ()
constrainVarTy v tyReq = do
  varTy <- getType $ Var v
  constrainEq tyReq varTy

data CaseAltIndex = ConAlt Int
                  | VariantAlt Label Int
                  | VariantTailAlt (LabeledItems ())
  deriving (Eq, Show)

checkCaseAlt :: Inferer m => RhoType o -> Type o -> UAlt i -> m i o (IndexedAlt o)
checkCaseAlt reqTy scrutineeTy (UAlt pat body) = do
  alt <- checkCasePat pat scrutineeTy do
    reqTy' <- injectM reqTy
    checkRho body reqTy'
  idx <- getCaseAltIndex pat
  return $ IndexedAlt idx alt

getCaseAltIndex :: Inferer m => UPat i i' -> m i o CaseAltIndex
getCaseAltIndex (WithSrcB _ pat) = case pat of
  UPatCon ~(InternalName conName) _ -> do
    (_, con) <- substM conName >>= getDataCon
    return $ ConAlt con
  UPatVariant (LabeledItems lmap) label _ -> do
    let i = case M.lookup label lmap of
              Just prev -> length prev
              Nothing -> 0
    return (VariantAlt label i)
  UPatVariantLift labels _ -> do
    return (VariantTailAlt labels)
  _ -> throw TypeErr $ "Case patterns must start with a data constructor or variant pattern"

checkCasePat :: Inferer m
             => UPat i i'
             -> Type o
             -> (forall o'. (Emits o', Ext o o') => m i' o' (Atom o'))
             -> m i o (Alt o)
checkCasePat (WithSrcB pos pat) scrutineeTy cont = addSrcContext' pos $ case pat of
  UPatCon ~(InternalName conName) ps -> do
    (dataDefName, con) <- substM conName >>= getDataCon
    dataDef@(DataDef _ paramBs cons) <- getDataDef dataDefName
    DataConDef _ (EmptyAbs argBs) <- return $ cons !! con
    when (nestLength argBs /= nestLength ps) $ throw TypeErr $
      "Unexpected number of pattern binders. Expected " ++ show (nestLength argBs)
                                             ++ " got " ++ show (nestLength ps)
    (params, argBs') <- inferParams (Abs paramBs $ EmptyAbs argBs)
    constrainEq scrutineeTy $ TypeCon (dataDefName, dataDef) params
    buildAlt argBs' \args ->
      bindLamPats ps args $ cont
  UPatVariant labels label p -> do
    ty <- freshType TyKind
    prevTys <- mapM (const $ freshType TyKind) labels
    rest <- freshInferenceName LabeledRowKind
    let patTypes = prevTys <> labeledSingleton label ty
    let extPatTypes = Ext patTypes $ Just rest
    constrainEq scrutineeTy $ VariantTy extPatTypes
    buildUnaryAlt ty \x ->
      bindLamPat p x cont
  UPatVariantLift labels p -> do
    prevTys <- mapM (const $ freshType TyKind) labels
    rest <- freshInferenceName LabeledRowKind
    let extPatTypes = Ext prevTys $ Just rest
    constrainEq scrutineeTy $ VariantTy extPatTypes
    let ty = VariantTy $ Ext NoLabeledItems $ Just rest
    buildUnaryAlt ty \x ->
      bindLamPat p x cont
  _ -> throw TypeErr $ "Case patterns must start with a data constructor or variant pattern"

inferParams :: (Inferer m, HasNamesE e)
            => Abs (Nest Binder) e o -> m i o ([Type o], e o)
inferParams (Abs Empty body) = return ([], body)
inferParams (Abs (Nest (b:>ty) bs) body) = do
  x <- freshInferenceName ty
  rest <- applyAbs (Abs b (Abs bs body)) x
  (xs, body') <- inferParams rest
  return (Var x : xs, body')

bindLamPats :: (Emits o, Inferer m)
            => Nest UPat i i' -> [AtomName o] -> m i' o a -> m i o a
bindLamPats Empty [] cont = cont
bindLamPats (Nest p ps) (x:xs) cont = bindLamPat p x $ bindLamPats ps xs cont
bindLamPats _ _ _ = error "mismatched number of args"

bindLamPat :: (Emits o, Inferer m) => UPat i i' -> AtomName o -> m i' o a -> m i o a
bindLamPat (WithSrcB pos pat) v cont = addSrcContext pos $ case pat of
  UPatBinder b -> extendEnv (b @> v) cont
  UPatUnit UnitB -> do
    constrainVarTy v UnitTy
    cont
  UPatPair (PairB p1 p2) -> do
    ty <- getType $ Var v
    _  <- fromPairType ty
    v' <- zonk v  -- ensure it has a pair type before unpacking
    x1 <- emit (Atom $ ProjectElt (NE.fromList [0]) v') >>= zonk
    bindLamPat p1 x1 do
      x2  <- emit (Atom $ ProjectElt (NE.fromList [1]) v') >>= zonk
      bindLamPat p2 x2 do
        cont
  UPatCon ~(InternalName conName) ps -> do
    (dataDefName, _) <- getDataCon =<< substM conName
    dataDef@(DataDef _ paramBs cons) <- getDataDef dataDefName
    case cons of
      [DataConDef _ (EmptyAbs argBs)] -> do
        when (nestLength argBs /= nestLength ps) $ throw TypeErr $
          "Unexpected number of pattern binders. Expected " ++ show (nestLength argBs)
                                                 ++ " got " ++ show (nestLength ps)
        (params, UnitE) <- inferParams (Abs paramBs UnitE)
        constrainVarTy v $ TypeCon (dataDefName, dataDef) params
        xs <- zonk (Var v) >>= emitUnpacked >>= mapM zonk
        bindLamPats ps xs cont
      _ -> throw TypeErr $ "sum type constructor in can't-fail pattern"
  UPatRecord (Ext labels Nothing) (PairB pats (RightB UnitB)) -> do
    expectedTypes <- mapM (const $ freshType TyKind) labels
    constrainVarTy v (RecordTy (NoExt expectedTypes))
    xs <- zonk (Var v) >>= emitUnpacked >>= mapM zonk
    bindLamPats pats xs cont
  UPatRecord (Ext labels (Just ())) (PairB pats (LeftB tailPat)) -> do
    wantedTypes <- mapM (const $ freshType TyKind) labels
    restType <- freshInferenceName LabeledRowKind
    constrainVarTy v (RecordTy $ Ext wantedTypes $ Just restType)
    -- Split the record.
    wantedTypes' <- mapM zonk wantedTypes
    v' <- zonk $ Var v
    split <- emit $ Op $ RecordSplit wantedTypes' v'
    [left, right] <- emitUnpacked $ Var split
    leftVals <- emitUnpacked $ Var left
    bindLamPats pats leftVals $
      bindLamPat tailPat right $
        cont
  UPatRecord _ _ -> error "mismatched labels and patterns (should be ruled out by the parser)"
  UPatVariant _ _ _   -> throw TypeErr "Variant not allowed in can't-fail pattern"
  UPatVariantLift _ _ -> throw TypeErr "Variant not allowed in can't-fail pattern"
  UPatTable ps -> do
    elemTy <- freshType TyKind
    let idxTy = FixedIntRange 0 (fromIntegral $ nestLength ps)
    ty <- getType $ Var v
    tabTy <- idxTy ==> elemTy
    constrainEq ty tabTy
    idxs <- indices idxTy
    unless (length idxs == nestLength ps) $
      throw TypeErr $ "Incorrect length of table pattern: table index set has "
                      <> pprint (length idxs) <> " elements but there are "
                      <> pprint (nestLength ps) <> " patterns."
    xs <- forM idxs \i -> emitZonked $ App (Var v) i
    bindLamPats ps xs cont

checkAnn :: Inferer m => Maybe (UType i) -> m i o (Type o)
checkAnn ann = case ann of
  Just ty -> checkUType ty
  Nothing -> freshType TyKind

checkUType :: Inferer m => UType i -> m i o (Type o)
checkUType ty = do
  reduced <- buildBlockReduced $ withAllowedEffects Pure $ checkRho ty TyKind
  case reduced of
    Just ty' -> return $ ty'
    Nothing  -> throw TypeErr $ "Can't reduce type expression: " ++ pprint ty

checkExtLabeledRow :: (Emits o, Inferer m)
                   => ExtLabeledItems (UExpr i) (UExpr i)
                   -> m i o (ExtLabeledItems (Type o) (AtomName o))
checkExtLabeledRow (Ext types Nothing) = do
  types' <- mapM checkUType types
  return $ Ext types' Nothing
checkExtLabeledRow (Ext types (Just ext)) = do
  types' <- mapM checkUType types
  -- Only variables can have kind LabeledRowKind at the moment.
  Var ext' <- checkRho ext LabeledRowKind
  return $ Ext types' $ Just ext'

inferTabCon :: (Emits o, Inferer m) => [UExpr i] -> RequiredTy RhoType o -> m i o (Atom o)
inferTabCon xs reqTy = do
  (tabTy, xs') <- case reqTy of
    Check Concrete tabTy@(TabTyAbs piTy) -> do
      idx <- indices $ piArgType piTy
      -- TODO: Check length!!
      unless (length idx == length xs) $
        throw TypeErr "Table type doesn't match annotation"
      xs' <- forM (zip xs idx) \(x, i) -> do
        (_, xTy) <- instantiatePi piTy i
        checkOrInferRho x $ Check Concrete xTy
      return (tabTy, xs')
    _ -> do
      elemTy <- case xs of
        []    -> freshType TyKind
        (x:_) -> getType =<< inferRho x
      tabTy <- FixedIntRange 0 (fromIntegral $ length xs) ==> elemTy
      case reqTy of
        Check Suggest sTy -> addContext context $ constrainEq sTy tabTy
          where context = "If attempting to construct a fixed-size table not " <>
                          "indexed by 'Fin n' for some n, this error may " <>
                          "indicate there was not enough information to infer " <>
                          "a concrete index set; try adding an explicit " <>
                          "annotation."
        Infer       -> return ()
        _           -> error "Missing case"
      xs' <- mapM (flip checkRho elemTy) xs
      return (tabTy, xs')
  liftM Var $ emitZonked $ Op $ TabCon tabTy xs'

-- Bool flag is just to tweak the reported error message
fromPiType :: Inferer m => Bool -> Arrow -> Type o -> m i o (PiType o)
fromPiType _ _ (Pi piTy) = return piTy -- TODO: check arrow
fromPiType expectPi arr ty = do
  a <- freshType TyKind
  b <- freshType TyKind
  piTy <- nonDepPiType arr a Pure b
  if expectPi then  constrainEq (Pi piTy) ty
              else  constrainEq ty (Pi piTy)
  return piTy

fromPairType :: Inferer m => Type o -> m i o (Type o, Type o)
fromPairType (PairTy t1 t2) = return (t1, t2)
fromPairType ty = do
  a <- freshType TyKind
  b <- freshType TyKind
  constrainEq (PairTy a b) ty
  return (a, b)

emitZonked :: (Emits o, Inferer m) => Expr o -> m i o (AtomName o)
emitZonked expr = zonk expr >>= emit

addEffects :: Inferer m => EffectRow o -> m i o ()
addEffects eff = do
  allowed <- checkAllowedUnconditionally eff
  unless allowed $ do
    allowedEffects <- getAllowedEffects
    eff' <- openEffectRow eff
    constrainEq (Eff allowedEffects) (Eff eff')

checkAllowedUnconditionally :: Inferer m => EffectRow o -> m i o Bool
checkAllowedUnconditionally Pure = return True
checkAllowedUnconditionally eff = do
  eff' <- zonk eff
  effAllowed <- getAllowedEffects >>= zonk
  return $ case checkExtends effAllowed eff' of
    Failure _  -> False
    Success () -> True

openEffectRow :: Inferer m => EffectRow o -> m i o (EffectRow o)
openEffectRow (EffectRow effs Nothing) = extendEffRow effs <$> freshEff
openEffectRow effRow = return effRow
