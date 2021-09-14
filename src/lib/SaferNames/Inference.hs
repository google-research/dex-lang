-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE ViewPatterns #-}

module SaferNames.Inference (inferModule) where

import Prelude hiding ((.), id)
import Control.Category
import Control.Monad
import Control.Monad.Except hiding (Except)
import Control.Monad.Reader
import Data.Foldable (toList)
import Data.List (elemIndex)
import Data.Maybe (fromJust)
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M

import SaferNames.NameCore
import SaferNames.Name
import SaferNames.Builder
import SaferNames.Syntax
import SaferNames.Type
import SaferNames.PPrint ()

import LabeledItems
import Err
import Util (enumerate)

inferModule :: Bindings n -> UModule n -> Except (Module n)
inferModule bindings uModule = runInfererM bindings do
  UModule decl sourceMap <- injectM uModule
  case decl of
    ULet _ _ _ -> do
      Abs decls sourceMap' <-
        buildScoped $ inferUDeclLocal decl $ substM sourceMap
      return $ Module Typed decls $
        EvaluatedModule emptyEnv mempty sourceMap'
    _ -> do
      Abs (RecEnvFrag bindingsFrag) sourceMap' <-
        buildScopedTop $ inferUDeclTop decl $ substM sourceMap
      return $ Module Typed id $
        EvaluatedModule bindingsFrag mempty sourceMap'

-- === Inferer monad ===

class (MonadErr2 m, Builder2 m, EnvGetter Name m)
      => Inferer (m::MonadKind2)

data InfererM (i::S) (o::S) (a:: *) = InfererM

runInfererM :: Bindings n
            -> (forall l. Ext n l => InfererM l l (e l))
            -> Except (e n)
runInfererM _ _ = undefined

instance Functor (InfererM i o)
instance Applicative (InfererM i o)
instance Monad (InfererM i o)
instance MonadFail (InfererM i o)
instance MonadError Err (InfererM i o)
instance Builder (InfererM i)
instance BindingsReader (InfererM i)
instance ScopeReader (InfererM i)
instance Scopable (InfererM i)
instance (EnvReader Name) InfererM
instance (EnvGetter Name) InfererM
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

getSrcCtx :: Inferer m => m i o SrcCtx
getSrcCtx = undefined -- lift ask

addSrcContext' :: Inferer m => SrcCtx -> m i o a -> m i o a
addSrcContext' pos m = undefined

makeReqCon :: Inferer m => Type o -> m i o SuggestionStrength
makeReqCon _ = undefined

buildAndReduceScoped :: Inferer m
                     => (forall l. (Emits l, Ext n l) => m i l (Atom l))
                     -> m i n (Maybe (Atom n))
buildAndReduceScoped _ = undefined

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
  ULam lam@(ULamExpr ImplicitArrow pat body) ->
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
      Just (arr, argTy, effs, resultTy) -> do
        x' <- checkSigma x Suggest argTy
        addEffects effs
        appVal <- emitZonked $ App f' x'
        instantiateSigma (Var appVal) >>= matchRequirement
      Nothing -> do
        maybeX <- buildAndReduceScoped do
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
        buildNonDepPi ann' effs' ty'
      -- TODO: won't type check unless we check no decls are produced
      -- _ -> buildPi ann' \v ->
      --   bindLamPat (WithSrcB pos' pat) v do
      --     effs' <- checkUEffRow effs
      --     ty' <- checkUType ty
      --     return (effs', ty')
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
      pairedIndices = enumerate $ [VariantAlt l i | (l, i, _) <- toList (withLabels types)]
  _ -> error $ "can't pattern-match on: " <> pprint ty

buildMonomorphicCase :: (Emits n, Builder m) => [IndexedAlt n] -> Atom n -> Type n -> m n (Atom n)
buildMonomorphicCase alts scrut resultTy = do
  scrutTy <- getType scrut
  buildCase scrut resultTy \i vs -> do
    ListE alts' <- injectM $ ListE alts
    scrutTy'    <- injectM scrutTy
    resultTy'   <- injectM resultTy
    buildNthOrderedAlt alts' scrutTy' resultTy' i vs

buildSortedCase :: (MonadErr1 m, Builder m, Emits n)
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
checkNoTailOverlaps :: MonadErr1 m => [IndexedAlt n] -> LabeledItems (Type n) ->  m n ()
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
    ~(ClassBinding (ClassDef classSoruceName _ dataDef)) <- lookupBindings v
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
inferUDeclLocal _ _ = error "not a local decl"

inferUDeclTop ::  (EmitsTop o, Inferer m) => UDecl i i' -> m i' o a -> m i o a
inferUDeclTop = undefined

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

withNestedUBinders :: (Inferer m, InjectableE e, HasNamesE e)
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

withUBinder :: (Inferer m, InjectableE e, HasNamesE e)
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

checkUEffRow :: Inferer m => UEffectRow i -> m i o (EffectRow o)
checkUEffRow = undefined

checkUEff :: Inferer m => UEffect i -> m i o (Effect o)
checkUEff = undefined

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
getCaseAltIndex = undefined

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
  UPatVariant labels@(LabeledItems lmap) label p -> do
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

inferParams
  :: Inferer m
  => Abs (Nest Binder) e o
  -> m i o ([Type o], e o)
inferParams _ = undefined

bindLamPats :: (Emits o, Inferer m)
            => Nest UPat i i' -> [AtomName o] -> m i' o a -> m i o a
bindLamPats _ _ _ = undefined

bindLamPat :: (Emits o, Inferer m) => UPat i i' -> AtomName o -> m i' o a -> m i o a
bindLamPat (WithSrcB pos pat) v cont = addSrcContext pos $ case pat of
  UPatBinder b -> extendEnv (b @> v) cont
  UPatUnit UnitB -> do
    ty <- getType $ Var v
    constrainEq UnitTy ty
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

checkAnn :: Inferer m => Maybe (UType i) -> m i o (Type o)
checkAnn ann = case ann of
  Just ty -> checkUType ty
  Nothing -> freshType TyKind

checkUType :: Inferer m => UType i -> m i o (Type o)
checkUType = undefined

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
    Left _   -> False
    Right () -> True

openEffectRow :: Inferer m => EffectRow o -> m i o (EffectRow o)
openEffectRow (EffectRow effs Nothing) = extendEffRow effs <$> freshEff
openEffectRow effRow = return effRow
