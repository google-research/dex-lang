-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Inference (inferModule) where

import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import Data.Maybe (isJust)
import Data.String (fromString)
import qualified Data.Set as S

import Preamble
import Base
import Core

-- === API to inference monad ===

type Inferer n m = Builder n m

freshInfName :: Inferer n m => Type n -> m (Name n)
freshInfName = undefined

addSubst :: Inferer n m => Name n -> Type n -> m ()
addSubst = undefined

zonk :: (Inferer n m, MaySubstAtoms e) => e n -> m (e n)
zonk = undefined

-- should it be more like `inferAbs` instead?
inferBlock :: Inferer n m => m (Atom n) -> m (Block n)
inferBlock = undefined

constrainEq :: Inferer n m => Type n -> m ()
constrainEq = undefined

-- -----------------------------------------------------------------------------

type SigmaType = Type  -- may     start with an implicit lambda
type RhoType   = Type  -- doesn't start with an implicit lambda
data RequiredTy a = Concrete a  | Suggest a | Infer
     deriving (Show, Functor, Foldable, Traversable)

pattern Check :: t -> RequiredTy t
pattern Check t <-
  ((\case Concrete t -> Just t
          Suggest  t -> Just t
          Infer      -> Nothing) -> Just t)
  where Check t = Suggest t

{-# COMPLETE Infer, Check #-}

inferModule :: (DefReader n m, MonadErr m) => UModule n -> m (Module n)
inferModule (UModule decls) = undefined
--   liftM (Module Typed) $ runUInferM env $
--     ModuleSourceSubst <$> execWriterT (inferTopUDecls decls)

-- runUInferM :: (Subst e, PrettyH e)
--            => TopEnv n
--            -> UInferM n (e n)
--            -> Except (WithBindings e n)
-- runUInferM env m = runSolverT $ runBuilderT (runReaderT m Nothing) env

-- inferTopUDecls :: UNest UDecl -> WriterT (SourceSubst n) (UInferM n) ()
-- inferTopUDecls UEmpty = return ()
-- inferTopUDecls (UNest decl rest) = do
--   sourceSubst <- lift $ inferTopUDecl decl
--   extendSourceSubst sourceSubst $ inferTopUDecls rest

-- checkSigma :: UExpr -> (Type n -> RequiredTy (Type n) )
--            -> SigmaType n -> UInferM n (Atom n)
-- checkSigma = undefined
-- checkSigma expr reqCon sTy = case sTy of
--   Pi arrow _ argTy abs
--     | arrow `elem` [ImplicitArrow, ClassArrow] -> case expr of
--         WithSrc _ (ULam b arrow' body) | arrow' == voidH arrow ->
--           checkULam b body (NoAbs UnitH arrow) argTy abs piTy
--         _ -> do
--           buildLam argTy arrow \x ->
--             checkLeaks x $ checkSigma expr reqCon $ applyAbs abs x
--   _ -> checkOrInferRho expr (reqCon sTy)

inferSigma :: Inferer n m => UExpr n -> m (Atom n)
inferSigma = undefined
-- inferSigma exprSrc = withCtx exprSrc \case
--   ULam pat ImplicitArrow body -> inferULam pat ImplicitArrow body
--   _ -> inferRho exprSrc

-- checkRho :: UExpr -> RhoType n -> UInferM n (Atom n)
-- checkRho expr ty = checkOrInferRho expr (Check ty)

-- inferRho :: UExpr -> UInferM n (Atom n)
-- inferRho expr = checkOrInferRho expr Infer

-- instantiateSigma :: Atom n -> UInferM n (Atom n)
-- instantiateSigma f = do
--   fTy <- getTypeE f
--   case fTy of
--     Pi ImplicitArrow _ argTy _ -> do
--       x <- freshType argTy
--       ans <- emitZonked $ App f x
--       instantiateSigma ans
--     Pi ClassArrow _ argTy _ -> do
--       ctx <- getSrcCtx
--       result <- emitZonked $ App f (Con $ ClassDictHole ctx argTy)
--       instantiateSigma result
--     _ -> return f

-- checkOrInferRho :: forall n. UExpr n -> RequiredTy (RhoType n) -> UInferM n (Atom n)
-- checkOrInferRho exprSrc reqTy = withCtx exprSrc \case
--   UVar v -> lookupSourceSubst v >>= instantiateSigma >>= matchRequirement
--   ULam (p, ann) ImplicitArrow body -> do
--     argTy <- checkAnn ann
--     x <- freshType argTy
--     withBindPat p x $ checkOrInferRho body reqTy
  -- ULam b arr body -> do
  --   let infer = inferULam b (fmapH (const Pure) arr) body
  --   case reqTy of
  --     Check (Pi absArr@(NoAbs _ arrReq) piTy) -> do
  --       checkArrow arrReq arr
  --       checkULam b body absArr piTy
  --     Check _ -> infer >>= matchRequirement
  --     Infer   -> infer
  -- UFor dir b body -> do
  --   let infer = do
  --         allowedEff <- getAllowedEffects
  --         lam <- inferULam b (PlainArrow allowedEff) body
  --         emitZonked $ Hof $ For (RegularFor dir) lam
  --   case reqTy of
  --     Check (Pi (UnsafeMakeAbs ty i (WithArrow arr a))) -> do
  --       unless (arr == TabArrow) $
  --         throw TypeErr $ "Not an table arrow type: " ++ pprint arr
  --       allowedEff <- getAllowedEffects
  --       lam <- checkULam b body $ UnsafeMakeAbs ty i $ WithArrow (PlainArrow allowedEff) a
  --       emitZonked $ Hof $ For (RegularFor dir) lam
  --     Check _ -> infer >>= matchRequirement
  --     Infer   -> infer
  -- UApp arr f x -> do
  --   fVal <- inferRho f
  --   -- NB: We never infer dependent function types, but we accept them, provided they
  --   --     come with annotations. So, unless we already know that the function is
  --   --     dependent here (i.e. the type of the zonk comes as a dependent Pi type),
  --   --     then nothing in the remainder of the program can convince us that the type
  --   --     is dependent. Also, the Pi binder is never considered to be in scope for
  --   --     inference variables, so they cannot get unified with it. Hence, this zonk
  --   --     is safe and doesn't make the type checking depend on the program order.
  --   infTy <- getTypeE =<< zonk fVal
  --   (absArr, piTy)  <- fromPiType True arr infTy
  --   let inferXVal = checkSigma x Suggest (absTy piTy)
  --   xVal <- case piTy of
  --     NoAbs _ _ -> inferXVal
  --     _ -> do
  --       xValBlock <- buildScopedBlock inferXVal
  --       xValMaybeRed <- flip typeReduceBlock xValBlock <$> getBindings
  --       case xValMaybeRed of
  --         Just xValRed -> return xValRed
  --         Nothing -> throw TypeErr $
  --           "Dependent functions can only be applied to fully evaluated " ++
  --           "expressions. Bind the argument to a name before you apply the function."
  --   addEffects $ arrowEff $ applyAbsArr absArr xVal
  --   appVal <- emitZonked $ App fVal xVal
  --   instantiateSigma appVal >>= matchRequirement
  -- UPi (pat, ann) arr ty -> do
  --   -- TODO: make sure there's no effect if it's an implicit or table arrow
  --   -- TODO: check leaks
  --   ann' <- checkAnn ann
  --   piTy <- buildPi ann' \x -> withBindPat pat x $
  --             (,) <$> mapMH checkUEffRow arr <*> checkUType ty
  --   matchRequirement piTy
  -- UDecl decl body -> do
  --   env <- inferLocalUDecl decl
  --   extendSourceSubst env $ checkOrInferRho body reqTy
  -- UCase scrut alts -> do
  --   scrut' <- inferRho scrut
  --   scrutTy <- getTypeE scrut'
  --   reqTy' <- case reqTy of
  --     Infer -> freshType TyKind
  --     Check req -> return req
  --   alts' <- mapM (checkCaseAlt reqTy' scrutTy) alts
  --   scrutTy' <- zonk scrutTy
  --   scrut'' <- zonk scrut'
  --   case scrutTy' of
  --     -- TypeCon def params -> do
  --     --   let conDefs = applyTypeDefParams def params
  --     --   altsSorted <- forM (enumerate conDefs) \(i, DataConDef _ bs) -> do
  --     --     case lookup (ConAlt i) alts' of
  --     --       Nothing  -> return $ Abs (fmapH (Ignore . binderType) bs) $
  --     --                     Block Empty $ Op $ ThrowError reqTy'
  --     --       Just alt -> return alt
  --     --   emit $ Case scrut'' altsSorted reqTy'
  --     VariantTy (Ext types@(LabeledItems tyItems) tailName) -> do
  --       let unhandledCase :: Type n -> Alt n
  --           unhandledCase ty = undefined
  --             -- NAbs $ NoAbs ty $ Block reqTy' $ Op $ ThrowError reqTy'
  --       let buildMonomorphicCase :: LabeledItems (Type n) -> Atom n -> UInferM n (Atom n)
  --           buildMonomorphicCase monoTypes monoScrut = do
  --             altsSorted <- forM (toList (withLabels monoTypes)) $
  --               \(l, i, ty) -> case lookup (VariantAlt l i) alts' of
  --                   Nothing  -> return $ unhandledCase ty
  --                   Just alt -> return alt
  --             emit $ Case monoScrut altsSorted reqTy'
  --       let isVariantTailAlt (VariantTailAlt _) = True
  --           isVariantTailAlt _ = False
  --       case filter (isVariantTailAlt . fst) alts' of
  --         [] -> case tailName of
  --           Nothing ->
  --             -- We already know the type exactly, so just emit a case.
  --             buildMonomorphicCase types scrut''
  --           Just _ -> do
  --             -- Split off the types we don't know about, mapping them to a
  --             -- runtime error.
  --             split <- emit $ Op $ VariantSplit types scrut''
  --             VariantTy (NoExt (Unlabeled [leftTy, rightTy])) <- getTypeE split
  --             leftCase <- buildNAbs (NestOne leftTy) \[v] ->
  --                           buildMonomorphicCase types v
  --             emit $ Case split [leftCase, unhandledCase rightTy] reqTy'
  --         [(VariantTailAlt (LabeledItems skippedItems), tailAlt)] -> do
  --           -- Split off the types skipped by the tail pattern.
  --           let splitLeft fvs ltys = NE.fromList $ NE.take (length ltys) fvs
  --               left = M.intersectionWith splitLeft tyItems skippedItems
  --           -- Make sure all of the alternatives are exclusive with the tail
  --           -- pattern (could technically allow overlap but this is simpler).
  --           let overlapErr = throw TypeErr
  --                 "Variant explicit alternatives overlap with tail pattern."
  --           let checkAltAgainstTail :: CaseAltIndex -> UInferM n ()
  --               checkAltAgainstTail (VariantAlt label i) =
  --                 case M.lookup label left of
  --                   Just tys -> when (i > length tys) overlapErr
  --                   Nothing -> overlapErr
  --               checkAltAgainstTail _ = return ()
  --           mapM_ (checkAltAgainstTail . fst) alts'
  --           -- Split based on the tail pattern's skipped types.
  --           split <- emit $ Op $ VariantSplit (LabeledItems left) scrut''
  --           let leftTy = VariantTy $ NoExt $ LabeledItems left
  --           leftCase <- buildNAbs (NestOne leftTy) \[v] ->
  --                         buildMonomorphicCase (LabeledItems left) v
  --           emit $ Case split [leftCase, tailAlt] reqTy'
  --         _ -> throw TypeErr "Can't specify more than one variant tail pattern."
  --     _ -> fail $ "Unexpected case expression type: " <> pprint scrutTy'
  -- UTabCon xs -> inferTabCon xs reqTy >>= matchRequirement
  -- UIndexRange low high -> do
  --   n <- freshType TyKind
  --   low'  <- mapM (flip checkRho n) low
  --   high' <- mapM (flip checkRho n) high
  --   matchRequirement $ TC $ IndexRange n low' high'
  -- UHole -> case reqTy of
  --   Infer -> throw MiscErr "Can't infer type of hole"
  --   Check ty -> freshType ty
  -- UTypeAnn val ty -> do
  --   ty' <- zonk =<< checkUType ty
  --   let reqCon = if nullH (freeVars ty') then Concrete else Suggest
  --   val' <- checkSigma val reqCon ty'
  --   matchRequirement val'
  -- UPrimExpr prim -> do
  --   prim' <- forM prim \e -> do
  --     e' <- inferRho e
  --     bindings <- getBindings
  --     return $ typeReduceAtom bindings e'
  --   val <- case prim' of
  --     TCExpr  e -> return $ TC e
  --     ConExpr e -> return $ Con e
  --     OpExpr  e -> emitZonked $ Op e
  --     HofExpr e -> emitZonked $ Hof e
  --   matchRequirement val
  -- URecord (Ext items Nothing) -> do
  --   items' <- mapM inferRho items
  --   matchRequirement $ Record items'
  -- URecord (Ext items (Just ext)) -> do
  --   items' <- mapM inferRho items
  --   restTy <- freshInferenceName LabeledRowKind
  --   ext' <- zonk =<< (checkRho ext $ RecordTy $ Ext NoLabeledItems $ Just restTy)
  --   matchRequirement =<< emit (Op $ RecordCons items' ext')
  -- UVariant labels@(LabeledItems lmap) label value -> do
  --   value' <- inferRho value
  --   prevTys <- mapM (const $ freshType TyKind) labels
  --   rest <- freshInferenceName LabeledRowKind
  --   valueTy' <- getTypeE value'
  --   let items = prevTys <> labeledSingleton label valueTy'
  --   let extItems = Ext items $ Just rest
  --   let i = case M.lookup label lmap of
  --             Just prev -> length prev
  --             Nothing -> 0
  --   matchRequirement $ Variant extItems label i value'
  -- URecordTy row -> matchRequirement =<< RecordTy <$> checkExtLabeledRow row
  -- UVariantTy row -> matchRequirement =<< VariantTy <$> checkExtLabeledRow row
  -- UVariantLift labels value -> do
  --   row <- freshInferenceName LabeledRowKind
  --   value' <- zonk =<< (checkRho value $ VariantTy $ Ext NoLabeledItems $ Just row)
  --   prev <- mapM (\() -> freshType TyKind) labels
  --   matchRequirement =<< emit (Op $ VariantLift prev value')
  -- UIntLit  x  -> matchRequirement $ Con $ Lit  $ Int32Lit $ fromIntegral x
  -- UFloatLit x -> matchRequirement $ Con $ Lit  $ Float32Lit $ realToFrac x
  -- -- TODO: Make sure that this conversion is not lossy!
  -- where
  --   matchRequirement :: Atom n -> UInferM n (Atom n)
  --   matchRequirement x = return x <*
  --     case reqTy of
  --       Infer -> return ()
  --       Check req -> constrainEq req =<< getTypeE x

-- inferTopUDecl :: UDecl -> UInferM n (SourceSubst n)
-- inferTopUDecl (UData tcDef dcDefs) = do
--   -- TODO: check data con and type con names not in scope
--   (tc, dcs) <- inferTypeDef tcDef dcDefs
--   return $  uConName tcDef @> tc
--          <> fold [uConName def @> dc | (def, dc) <- zip dcDefs dcs]
-- -- inferTopUDecl (UInterface superclasses tcDef methods) = do
-- --   -- TODO: check class and method names not in scope
-- --   let dcDef = makeClassDictUDataCon superclasses methods
-- --   (tc, [dc]) <- inferTypeDef tcDef [dcDef]
-- --   methodSubst <- emitClassProjections dc
-- --   return $ uConName tcDef @> tc <> methodSubst
-- inferTopUDecl decl = inferLocalUDecl decl

-- makeClassDictUDataCon :: [UType] -> [UAnnBinder] -> UConDef
-- makeClassDictUDataCon = undefined

-- emitClassProjections :: Atom n -> UInferM n (SourceSubst n)
-- emitClassProjections = undefined

-- uConName :: UConDef -> Maybe SourceName
-- uConName (UConDef name _) = name

-- inferTypeDef :: UConDef -> [UConDef] -> UInferM n (Atom n, [Atom n])
-- inferTypeDef tcDef dcDefs = do
--   let ((tcSourceName, tcTy), dcs) = dataDefType tcDef dcDefs
--   let (dcSourceNames, dcTys) = unzip dcs
--   tcType <- checkUType tcTy
--   buildTypeDef (getNameStr tcSourceName)
--      (map getNameStr dcSourceNames) tcType \tc ->
--         extendSourceSubst (tcSourceName@>tc) $
--           mapM checkUType dcTys

-- TODO: should probably just replace `UConDef` with this
-- type UConDef' = (SourceName, UType)
-- dataDefType :: UConDef -> [UConDef] -> (UConDef', [UConDef'])
-- dataDefType = undefined
        -- tyKind = WithSrc Nothing $ UPrimExpr $ TCExpr TypeKind

-- inferLocalUDecl :: UDecl -> UInferM n (SourceSubst n)
-- inferLocalUDecl = undefined
-- inferLocalUDecl (ULet letAnn (p, ann) rhs) = do
--   val <- case ann of
--     Nothing -> inferSigma rhs
--     Just ty -> do
--       ty' <- zonk =<< checkUType ty
--       let reqCon = if nullH (freeVars ty') then Concrete else Suggest
--       checkSigma rhs reqCon ty'
--   env <- bindPat p val
--   flip traverseNames env \name val -> do
--     checkNotInScope name
--     withNameHint name $ emitAnn letAnn $ Atom val
-- inferLocalUDecl (UInstance maybeName argBinders instanceTy methods) = do
--   instanceDict <- checkInstance argBinders instanceTy methods
--   case maybeName of
--     Nothing -> do
--       emitAnn InstanceLet $ Atom instanceDict
--       return mempty
--     Just n -> do
--       checkNotInScope n
--       x <- emitAnn PlainLet $ Atom instanceDict
--       return $ n @> x
-- inferLocalUDecl (UData      _ _  ) = error "data definitions should be top-level"
-- inferLocalUDecl (UInterface _ _ _) = error "interface definitions should be top-level"

-- TODO: just make Name and Label the same thing?
-- nameToLabel :: Name n -> Label
-- nameToLabel = pprint

-- mkLabeledItems :: [(Label, a)] -> LabeledItems a
-- mkLabeledItems items = foldMap (uncurry labeledSingleton) items

-- checkNotInScope :: SourceName -> UInferM n ()
-- checkNotInScope _ = return ()
-- checkNotInScope v = do
--   alreadyDefined <- isJust <$> lookupSourceSubst v
--   when alreadyDefined $ throw RepeatedVarErr $ pprint v

-- inferULam :: UPatAnn -> Arrow n -> UExpr -> UInferM n (Atom n)
-- inferULam = undefined
-- inferULam (p, ann) arr body = do
--   argTy <- checkAnn ann
--   -- TODO: worry about binder appearing in arrow?
--   buildLam argTy arr \x -> checkLeaks x $ withBindPat p x $ inferSigma body

-- checkULam :: UPatAnn -> UExpr -> AbsArrow n -> PiType n -> UInferM n (Atom n)
-- checkULam (p, ann) body absArr piTy = do
--   let argTy = absTy piTy
--   checkAnn ann >>= constrainEq argTy
--   buildDepEffLam argTy
--     ( \x -> return $ applyAbsArr absArr x) $
--       \x -> checkLeaks x $ withBindPat p x $
--               checkSigma body Suggest $ applyAbs piTy x

-- checkInstance :: UNest UPatAnnArrow -> UType -> [UMethodDef] -> UInferM n (Atom n)
-- -- checkInstance UEmpty ty methods = do
-- --   ty' <- checkUType ty
-- --   case ty' of
-- --     TypeCon def@(TypeDef className _) params ->
-- --       case applyTypeDefParams def params of
-- --         ClassDictDef _ superclassTys methodTys -> do
-- --           let superclassHoles = fmap (Con . ClassDictHole Nothing) superclassTys
-- --           methods' <- checkMethodDefs className methodTys methods
-- --           return $ ClassDictCon def params superclassHoles methods'
-- --         _ -> throw TypeErr $ "Not a valid instance type: " ++ pprint ty
-- --     _     -> throw TypeErr $ "Not a valid instance type: " ++ pprint ty
-- checkInstance (UNest ((p, ann), arrow) rest) ty methods = do
--   case arrow of
--     ImplicitArrow -> return ()
--     ClassArrow    -> return ()
--     _ -> throw TypeErr $ "Not a valid arrow for an instance: " ++ pprint arrow
--   argTy <- checkAnn ann
--   buildLam argTy (fromArrow arrow) \x ->
--     checkLeaks x $ withBindPat p x $ checkInstance rest ty methods

-- checkMethodDefs :: Name n ->  LabeledItems (Type n) -> [UMethodDef]
--                 -> UInferM n (LabeledItems (Atom n))
-- checkMethodDefs className methodTys methods = do
--   methods' <- liftM mkLabeledItems $ forM methods \(UMethodDef v rhs) -> do
--     let v' = nameToLabel v
--     case lookupLabelHead methodTys v' of
--       Nothing -> throw TypeErr $
--         pprint v ++ " is not a method of " ++ pprint className
--       Just methodTy -> do
--         rhs' <- checkSigma rhs Suggest methodTy
--         return (v', rhs')
--   forM_ (reflectLabels methods') \(l,i) ->
--     when (i > 0) $ throw TypeErr $ "Duplicate method: " ++ pprint l
--   forM_ (reflectLabels methodTys) \(l,_) ->
--     case lookupLabelHead methods' l of
--       Nothing -> throw TypeErr $ "Missing method: " ++ pprint l
--       Just _  -> return ()
--   return methods'

-- checkUEffRow :: forall n. EffectRow SourceNS -> UInferM n (EffectRow n)
-- checkUEffRow (EffectRow effs t) = do
--    effs' <- liftM S.fromList $ mapM checkUEff $ toList effs
--    EffectRow effs' <$> forM t \tv -> do
--      -- TODO: more graceful errors on error
--      Var t' <- lookupSourceSubst tv
--      return t'

-- checkUEff :: Effect SourceNS -> UInferM n (Effect n)
-- checkUEff eff = case eff of
--   RWSEffect rws region -> do
--     Var v <- lookupSourceSubst region
--     return $ RWSEffect rws v
--   ExceptionEffect -> return ExceptionEffect
--   IOEffect        -> return IOEffect

-- data CaseAltIndex = ConAlt Int
--                   | VariantAlt Label Int
--                   | VariantTailAlt (LabeledItems ())
--   deriving (Eq, Show)

-- -- checkCaseAlt :: RhoType n -> Type n -> UAlt -> UInferM n (CaseAltIndex, Alt n)
-- -- checkCaseAlt reqTy scrutineeTy (UAlt pat body) = do
-- --   (conIdx, subPats, argTys) <- checkCasePat pat scrutineeTy
-- --   alt <- buildNAbs argTys \xs -> withBindPats subPats xs $ checkRho body reqTy
-- --   return (conIdx, alt)

-- withBindPats :: [UPat] -> [Atom n] -> UInferM n a -> UInferM n a
-- withBindPats pats xs body = foldr (uncurry withBindPat) body $ zip pats xs

-- lookupDataCon :: SourceName -> UInferM n (Name n)
-- lookupDataCon conName = do
--   conVal <- lookupSourceSubst conName
--   case conVal of
--     DataCon con [] [] -> return con
--     _ -> throw TypeErr $ "Not a data constructor: " ++ pprint conName

-- checkPatternArity :: MonadError Err m => DataConType n -> Int -> m ()
-- checkPatternArity dataConTy numPatterns =
--   when (numExpected /= numPatterns) $ throw TypeErr $
--       "Unexpected number of pattern binders. Expected " ++ show numExpected
--                                              ++ " got " ++ show numPatterns
--   where numExpected = numDataConArgs dataConTy

-- -- applyNonDepNAbs :: DataConType n -> [Atom n] -> Nest Type n
-- -- applyNonDepNAbs = undefined

-- -- checkCasePat :: UPat -> Type n -> UInferM n (CaseAltIndex, [UPat], Nest Type n)
-- -- checkCasePat patSrc scrutineeTy = withCtx patSrc \case
-- --   UPatCon sourceConName ps -> do
-- --     conName <- lookupDataCon sourceConName
-- --     DataConDef dataConTy tyConName con <- lookupBinding conName
-- --     TypeConDef tyConTy dataConNames  <- lookupBinding tyConName
-- --     checkPatternArity dataConTy (length ps)
-- --     params <- lift $ mapMH freshType $ nonDepNAbsBindings dataConTy
-- --     let dataConArgBinders = applyNonDepNAbs dataConTy params
-- --     constrainEq scrutineeTy (TypeCon tyConName params)
-- --     return (ConAlt con, fromUNest ps, dataConArgBinders)
-- --   UPatVariant labels@(LabeledItems lmap) label subpat -> do
-- --     subty <- freshType TyKind
-- --     prevTys <- mapM (const $ freshType TyKind) labels
-- --     Var rest <- freshType LabeledRowKind
-- --     let patTypes = prevTys <> labeledSingleton label subty
-- --     let extPatTypes = Ext patTypes $ Just rest
-- --     constrainEq scrutineeTy $ VariantTy extPatTypes
-- --     let i = case M.lookup label lmap of
-- --               Just prev -> length prev
-- --               Nothing -> 0
-- --     return (VariantAlt label i, [subpat], NestOne subty)
-- --   UPatVariantLift labels subpat -> do
-- --     prevTys <- mapM (const $ freshType TyKind) labels
-- --     Var rest <- freshType LabeledRowKind
-- --     let extPatTypes = Ext prevTys $ Just rest
-- --     constrainEq scrutineeTy $ VariantTy extPatTypes
-- --     let subty = VariantTy $ Ext NoLabeledItems $ Just rest
-- --     return (VariantTailAlt labels, [subpat], NestOne subty)
-- --   _ -> throw TypeErr $ "Case patterns must start with a data constructor or variant pattern"

-- -- withBindPat :: UPat -> Atom n -> UInferM n a -> UInferM n a
-- -- withBindPat = undefined
-- -- withBindPat pat val m = do
-- --   env <- bindPat pat val
-- --   extendSourceSubst env m

-- -- bindPat :: UPat -> Atom n -> UInferM n (SourceSubst n)
-- -- bindPat pat val = evalCatT $ bindPat' pat val

-- -- -- CatT wrapper is used to prevent duplicate bindings within the same pattern,
-- -- -- e.g. (a, a) = (1, 2) should throw RepeatedVarErr
-- -- bindPat' :: UPat -> Atom n -> CatT (Scope SourceNS) (UInferM n) (SourceSubst n)
-- -- bindPat' (WithSrc pos pat) val = addSrcContext pos do
-- --  valTy <- getTypeE val
-- --  case pat of
-- --   UPatBinder b -> do
-- --     usedVars <- look
-- --     when (b `isin` usedVars) $ throw RepeatedVarErr $ pprint b
-- --     extend (b @> UnitH)
-- --     return $ b @> val
-- --   UPatUnit -> do
-- --     lift $ constrainEq UnitTy valTy
-- --     return mempty
-- --   UPatPair p1 p2 -> do
-- --     _    <- lift $ fromPairType valTy
-- --     val' <- lift $ zonk val  -- ensure it has a pair type before unpacking
-- --     x1   <- lift $ getFst val'
-- --     x2   <- lift $ getSnd val'
-- --     env1 <- bindPat' p1 x1
-- --     env2 <- bindPat' p2 x2
-- --     return $ env1 <> env2
-- --   UPatCon sourceConName ps -> do
-- --     conName <- lift $ lookupDataCon sourceConName
-- --     DataConDef dataConTy tyConName _ <- lookupBinding conName
-- --     TypeConDef tyConTy dataConNames  <- lookupBinding tyConName
-- --     when (length dataConNames /= 1) $ throw TypeErr $
-- --       "sum type constructor in can't-fail pattern"
-- --     checkPatternArity dataConTy (length ps)
-- --     params <- lift $ mapM freshType $ nonDepNAbsBindings dataConTy
-- --     lift $ constrainEq (TypeCon tyConName params) valTy
-- --     xs <- lift $ zonk (Atom val) >>= emitUnpack
-- --     fold <$> zipWithM bindPat' (toList ps) xs
-- --   UPatRecord (Ext pats Nothing) -> do
-- --     expectedTypes <- lift $ mapM (const $ freshType TyKind) pats
-- --     lift $ constrainEq (RecordTy (NoExt expectedTypes)) valTy
-- --     xs <- lift $ zonk (Atom val) >>= emitUnpack
-- --     fold <$> zipWithM bindPat' (toList pats) xs
-- --   UPatRecord (Ext pats (Just tailPat)) -> do
-- --     wantedTypes <- lift $ mapM (const $ freshType TyKind) pats
-- --     restType <- lift $ freshInferenceName LabeledRowKind
-- --     lift $ constrainEq (RecordTy $ Ext wantedTypes $ Just restType) valTy
-- --     -- Split the record.
-- --     wantedTypes' <- lift $ mapM zonk wantedTypes
-- --     val' <- lift $ zonk val
-- --     split <- lift $ emit $ Op $ RecordSplit wantedTypes' val'
-- --     [left, right] <- lift $ getUnpacked split
-- --     leftVals <- lift $ getUnpacked left
-- --     env1 <- fold <$> zipWithM bindPat' (toList pats) leftVals
-- --     env2 <- bindPat' tailPat right
-- --     return $ env1 <> env2
-- --   UPatVariant _ _ _ -> throw TypeErr "Variant not allowed in can't-fail pattern"
-- --   UPatVariantLift _ _ -> throw TypeErr "Variant not allowed in can't-fail pattern"
-- --   UPatTable ps -> do
-- --     elemTy <- lift $ freshType TyKind
-- --     let idxTy = FixedIntRange 0 (fromIntegral $ length ps)
-- --     valTy <- getTypeE val
-- --     lift $ constrainEq valTy (idxTy :==> elemTy)
-- --     let idxs = indicesNoIO idxTy
-- --     unless (length idxs == length ps) $
-- --       throw TypeErr $ "Incorrect length of table pattern: table index set has "
-- --                       <> pprint (length idxs) <> " elements but there are "
-- --                       <> pprint (length ps) <> " patterns."
-- --     flip foldMapM (zip ps idxs) \(p, i) -> do
-- --       v <- lift $ emitZonked $ App val i
-- --       bindPat' p v

-- checkAnn :: Maybe (UType n) -> UInferM n (Type n)
-- checkAnn ann = case ann of
--   Just ty -> checkUType ty
--   Nothing -> freshType TyKind

-- checkUType :: UType n -> UInferM n (Type n)
-- checkUType ty = do
--   reduced <- typeReduceScoped $ withEffects Pure $ checkRho ty TyKind
--   case reduced of
--     Just ty' -> return $ ty'
--     Nothing  -> throw TypeErr $ "Can't reduce type expression: " ++ pprint ty

-- -- checkArrow :: Arrow -> Arrow -> UInferM n ()
-- -- checkArrow ahReq ahOff = case (ahReq, ahOff) of
-- --   (PlainArrow _, PlainArrow UnitH) -> return ()
-- --   (LinArrow    , PlainArrow UnitH) -> return ()
-- --   (LinArrow    , LinArrow     ) -> return ()
-- --   (TabArrow  , TabArrow  ) -> return ()
-- --   (ClassArrow, ClassArrow) -> return ()
-- --   _ -> throw TypeErr $  " Wrong arrow type:" ++
-- --                        "\nExpected: " ++ pprint ahReq ++
-- --                        "\nActual:   " ++ pprint (fmapH (const Pure) ahOff)

-- -- checkExtLabeledRow :: ExtLabeledItems UExpr UExpr
-- --                    -> UInferM n (ExtLabeledItems (Type n) (Name n))
-- -- checkExtLabeledRow (Ext types Nothing) = do
-- --   types' <- mapM checkUType types
-- --   return $ Ext types' Nothing
-- -- checkExtLabeledRow (Ext types (Just ext)) = do
-- --   types' <- mapM checkUType types
-- --   -- Only variables can have kind LabeledRowKind at the moment.
-- --   Var ext' <- checkRho ext LabeledRowKind
-- --   return $ Ext types' $ Just ext'

-- -- inferTabCon :: [UExpr n] -> RequiredTy (RhoType n) -> UInferM n (Atom (U n inf))
-- -- inferTabCon xs reqTy = do
-- --   (tabTy, xs') <- case reqTy of
-- --     Concrete tabTy@(TabTy idxTy abs) -> do
-- --       let idx = indicesNoIO idxTy
-- --       unless (length idx == length xs) $
-- --         throw TypeErr "Table type doesn't match annotation"
-- --       xs' <- forM (zip xs idx) \(x, i) ->
-- --                checkOrInferRho x $ Concrete $ applyAbs abs i
-- --       return (tabTy, xs')
-- --     _ -> do
-- --       elemTy <- case xs of
-- --         []    -> freshType TyKind
-- --         (x:_) -> inferRho x >>= getTypeE
-- --       let tabTy = (FixedIntRange 0 (fromIntegral $ length xs)) :==> elemTy
-- --       case reqTy of
-- --         Suggest sTy -> addContext context $ constrainEq sTy tabTy
-- --           where context = "If attempting to construct a fixed-size table not " <>
-- --                           "indexed by 'Fin n' for some n, this error may " <>
-- --                           "indicate there was not enough information to infer " <>
-- --                           "a concrete index set; try adding an explicit " <>
-- --                           "annotation."
-- --         Infer       -> return ()
-- --         _           -> error "Missing case"
-- --       xs' <- mapM (flip checkRho elemTy) xs
-- --       return (tabTy, xs')
-- --   emitZonked $ Op $ TabCon tabTy xs'

-- -- fromArrow :: Arrow -> Arrow n
-- -- fromArrow arr = undefined -- fmap (const Pure) arr

-- -- -- Bool flag is just to tweak the reported error message
-- -- fromPiType :: Bool -> Arrow -> Type n -> UInferM n (AbsArrow n, PiType n)
-- -- fromPiType _ _ (Pi absArr piTy) = return (absArr, piTy) -- TODO: check arrow
-- -- fromPiType expectPi arr ty = do
-- --   a <- freshType TyKind
-- --   b <- freshType TyKind
-- --   let absArr = NoAbs UnitH (fromArrow arr)
-- --   let piTy   = NoAbs a b
-- --   if expectPi then constrainEq (Pi absArr piTy) ty
-- --               else constrainEq ty (Pi absArr piTy)
-- --   return (absArr, piTy)

-- fromPairType :: Type n -> UInferM n (Type n, Type n)
-- fromPairType (PairTy t1 t2) = return (t1, t2)
-- fromPairType ty = do
--   a <- freshType TyKind
--   b <- freshType TyKind
--   constrainEq (PairTy a b) ty
--   return (a, b)

-- emitZonked :: Expr n -> UInferM n (Atom n)
-- emitZonked expr = zonk expr >>= emit

-- addEffects :: EffectRow n -> UInferM n ()
-- addEffects eff = do
--   allowed <- checkAllowedUnconditionally eff
--   unless allowed $ do
--     allowedEffects <- getAllowedEffects
--     eff' <- openEffectRow eff
--     constrainEq (Eff allowedEffects) (Eff eff')

-- checkAllowedUnconditionally :: EffectRow n -> UInferM n Bool
-- checkAllowedUnconditionally Pure = return True
-- checkAllowedUnconditionally eff = do
--   eff' <- zonk eff
--   effAllowed <- getAllowedEffects >>= zonk
--   return $ case checkExtends effAllowed eff' of
--     Left _   -> False
--     Right () -> True

-- openEffectRow :: EffectRow n -> UInferM n (EffectRow n)
-- openEffectRow (EffectRow effs Nothing) = extendEffRow effs <$> freshEff
-- openEffectRow effRow = return effRow


-- withCtx :: WithSrc a -> (a -> UInferM n b) -> UInferM n b
-- withCtx (WithSrc pos x) f = undefined --   addSrcContext pos $ local (const pos) $ f x

-- getSrcCtx :: UInferM n SrcCtx
-- getSrcCtx = undefined -- lift ask

-- === typeclass dictionary synthesizer ===

-- -- We have two variants here because at the top level we want error messages and
-- -- internally we want to consider all alternatives.
-- type SynthPassM i n = SubstBuilderT i n (Either Err)
-- type SynthDictM i n = SubstBuilderT i n []

-- synthModule :: TopEnv n -> Module i -> Except (Module n)
-- synthModule = undefined
-- -- synthModule bindings (Module Typed decls bindings) = do
-- --   decls' <- fst . fst <$> runSubstBuilderT
-- --               (traverseDecls (traverseHoles synthDictTop) decls) bindings
-- --   return $ Module Core decls' bindings
-- -- synthModule _ _ = error $ "Unexpected IR variant"

-- synthDictTop :: SrcCtx -> Type i -> SynthPassM i n (Atom n)
-- synthDictTop = undefined
-- -- synthDictTop ctx ty = do
-- --   bindings <- getBindings
-- --   let solutions = runSubstBuilderT (synthDict ty) bindings
-- --   addSrcContext ctx $ case solutions of
-- --     [] -> throw TypeErr $ "Couldn't synthesize a class dictionary for: " ++ pprint ty
-- --     [(ans, env)] -> builderExtend env $> ans
-- --     _ -> throw TypeErr $ "Multiple candidate class dictionaries for: " ++ pprint ty
-- --            ++ "\n" ++ pprint solutions

-- traverseHoles :: (MonadReader (Subst i n) m, MonadBuilder n m)
--               => (SrcCtx -> Type i -> m (Atom n)) -> TraversalDef i n m
-- traverseHoles = undefined
-- -- traverseHoles fillHole = (traverseDecl recur, traverseExpr recur, synthPassAtom)
-- --   where
-- --     synthPassAtom atom = case atom of
-- --       Con (ClassDictHole ctx ty) -> fillHole ctx =<< substBuilderR ty
-- --       _ -> traverseAtom recur atom
-- --     recur = traverseHoles fillHole

-- synthDict :: Type i -> SynthDictM i o (Atom o)
-- synthDict = undefined
-- -- synthDict dictTy = case dictTy of
-- --   PiTy (v:>ty) arr body -> do
-- --     ty' <- substBuilderR ty
-- --     synthesizeNow <|> introfirst
-- --     where
-- --       introfirst = buildDepEffLam ty'
-- --                       (\x -> extendR (b @> x) $ substBuilderR arr)
-- --                       (\x -> extendR (b @> x) $ substBuilderR body >>= synthDict)
-- --   _ -> synthesizeNow
-- --   where
-- --     synthesizeNow = do
-- --       (d, bindingInfo) <- getBinding
-- --       case bindingInfo of
-- --         LetBound InstanceLet _ -> trySynth d
-- --         LamBound ClassArrow    -> withSuperclasses d >>= trySynth
-- --         _                      -> empty
-- --     trySynth step = do
-- --       block <- buildScoped $ inferToSynth $ instantiateAndCheck dictTy step
-- --       -- NOTE: It's ok to emit unconditionally here. It will only ever emit
-- --       --       blocks that fully resolved without any holes, and if we ever
-- --       --       end up with two results, we don't use the duplicate code because
-- --       --       it's an error!
-- --       traverseBlock (traverseHoles (const synthDict)) block >>= emitBlock

-- -- TODO: this doesn't de-dup, so we'll get multiple results if we have a
-- -- diamond-shaped hierarchy.
-- withSuperclasses :: Atom n -> SynthDictM i n (Atom n)
-- withSuperclasses dict = return dict <|> do
--   (f, Let _ (SuperclassLet,_) _) <- getBinding
--   inferToSynth $ tryApply f dict

-- getBinding :: SynthDictM i n (Atom n, Binding n)
-- getBinding = do
--   bindings <- getBindings
--   (v, binding) <- lift $ lift $ envPairs $ dropEnvOrder bindings
--   return (Var v, binding)

-- inferToSynth :: (PrettyH e, Subst e)
--              => UInferM n (e n) -> SynthDictM i n (e n)
-- inferToSynth = undefined
-- -- inferToSynth m = do
-- --   bindings <- getBindings
-- --   case runUInferM bindings m of
-- --     Left _ -> empty
-- --     Right (x, (_, decls)) -> do
-- --       mapMH_ emitDecl decls
-- --       return x

-- tryApply :: Atom n -> Atom n -> UInferM n (Atom n)
-- tryApply f x = do
--   f' <- instantiateSigma f
--   Pi _ piTy <- getTypeE f'
--   constrainEq (absTy piTy) =<< getTypeE x
--   emitZonked $ App f' x

-- instantiateAndCheck :: Type n -> Atom n -> UInferM n (Atom n)
-- instantiateAndCheck ty x = do
--   x' <- instantiateSigma x
--   constrainEq ty =<< getTypeE x'
--   return x'

-- === constraint solver ===

-- data SolverEnv n = SolverEnv { solverVars :: Env n (Kind n)
--                              , solverSub  :: Env n (Type n) }
-- type SolverT n m = CatT (SolverEnv n) m

-- runSolverT :: (MonadError Err m, Subst e, PrettyH e)
--            => CatT (SolverEnv n) m (e n) -> m (e n)
-- runSolverT m = liftM fst $ flip runCatT mempty $ do
--    ans <- m >>= zonk
--    applyDefaults
--    ans' <- zonk ans
--    vs <- looks $ envNames . unsolved
--    throwIf (not (null vs)) TypeErr $ "Ambiguous type variables: "
--                                    ++ pprint vs ++ "\n\n" ++ pprint ans'
--    return ans'

-- applyDefaults :: MonadCat (SolverEnv n) m => m ()
-- applyDefaults = do
--   vs <- looks unsolved
--   forM_ (envPairs vs) \(v, k) -> case k of
--     EffKind -> addSub v $ Eff Pure
--     _ -> return ()
--   where addSub v ty = extend $ SolverEnv mempty (v@>ty)

-- solveLocal :: Subst e => UInferM n (e n) -> UInferM n (e n)
-- solveLocal m = do
--   (ans, env@(SolverEnv freshVars sub)) <- scoped $
--     -- This might get expensive. TODO: revisit once we can measure performance.
--     buildScoped m >>= zonk >>= emitWithBindings
--   extend $ SolverEnv (unsolved env) (sub `envDiff` freshVars)
--   return ans

-- checkLeaks :: (Subst eIn, HasType e, PrettyH e)
--            => eIn n -> UInferM n (e n) -> UInferM n (e n)
-- checkLeaks = undefined
-- TODO: builder should be able to tell us about leaked vars in a scope. but how
-- do we handle inference vars, which have a large scope. (or do they?)
-- checkLeaks x m = do
--   bindings <- getBindings
--   (ans, env) <- scoped $ solveLocal $ m
--   let resultTypeLeaks = filter (\n -> getNameSpace n /= InferenceName) $
--                           envNames $ freeVars (getType ans) `envDiff` bindings
--   unless (null $ resultTypeLeaks) $
--     throw TypeErr $ "Leaked local variable `" ++ pprint (head resultTypeLeaks) ++
--                     "` in result type " ++ pprint (getType ans)
--   forM_ (solverSub env) \ty ->
--     forM_ (envNames $ freeVars x) \tv ->
--       throwIf (tv `occursIn` ty) TypeErr $ "Leaked type variable: " ++ pprint tv
--   extend env
--   return ans

-- unsolved :: SolverEnv n -> Env n Kind n
-- unsolved (SolverEnv vs sub) = vs `envDiff` sub

-- freshInferenceName :: (MonadError Err m, MonadCat (SolverEnv n) m)
--                    => Kind n -> m (Name n)
-- freshInferenceName k = do
--   env <- look
--   let v = genFresh InferenceName "?" $ solverVars env
--   extend $ SolverEnv (v@>k) mempty
--   return v

-- freshType ::  (MonadError Err m, MonadCat (SolverEnv n) m)
--           => Kind n -> m (Type n)
-- freshType EffKind = Eff <$> freshEff
-- freshType k = Var <$> freshInferenceName k

-- freshEff :: (MonadError Err m, MonadCat (SolverEnv n) m) => m (EffectRow n)
-- freshEff = EffectRow mempty . Just <$> freshInferenceName EffKind

-- constrainEq :: (MonadCat (SolverEnv n) m, MonadError Err m)
--              => Type n -> Type n -> m ()
-- constrainEq t1 t2 = do
--   t1' <- zonk t1
--   t2' <- zonk t2
--   let (PairH t1Pretty t2Pretty, infVars) = renameForPrinting $ PairH t1' t2'
--   let msg =   "Expected: " ++ pprint t1Pretty
--          ++ "\n  Actual: " ++ pprint t2Pretty
--          ++ (if null infVars then "" else
--                "\n(Solving for: " ++ pprint infVars ++ ")")
--   addContext msg $ unify t1' t2'

-- zonk :: (Subst e, MonadCat (SolverEnv n) m) => e n -> m (e n)
-- zonk x = do
--   s <- looks solverSub
--   return $ scopelessSubst s x

-- unify :: (MonadCat (SolverEnv n) m, MonadError Err m)
--       => Type n -> Type n -> m ()
-- unify t1 t2 = do
--   t1' <- zonk t1
--   t2' <- zonk t2
--   vs <- looks solverVars
--   case (t1', t2') of
--     _ | t1' == t2' -> return ()
--     (t, Var v) | v `isin` vs -> bindQ v t
--     (Var v, t) | v `isin` vs -> bindQ v t
-- -- NEEDS: update to new Pi, with absArrow
--     -- (Pi piTy, Pi piTy') -> do
--     --    unify (absArgType piTy) (absArgType piTy')
--     --    let v = Var $ freshSkolemVar (PairH piTy piTy') (absArgType piTy)
--     --    -- TODO: think very hard about the leak checks we need to add here
--     --    let PairH arr  resultTy  = applyAbs piTy  v
--     --    let PairH arr' resultTy' = applyAbs piTy' v
--     --    when (voidH arr /= voidH arr') $ throw TypeErr ""
--     --    unify resultTy resultTy'
--     --    unifyEff (arrowEff arr) (arrowEff arr')
--     (RecordTy  items, RecordTy  items') ->
--       unifyExtLabeledItems items items'
--     (VariantTy items, VariantTy items') ->
--       unifyExtLabeledItems items items'
--     (TypeCon f xs, TypeCon f' xs')
--       | f == f' && length xs == length xs' -> zipWithM_ unify xs xs'
--     (TC con, TC con') | void con == void con' ->
--       zipWithM_ unify (toList con) (toList con')
--     (Eff eff, Eff eff') -> unifyEff eff eff'
--     _ -> throw TypeErr ""

-- unifyExtLabeledItems :: (MonadCat (SolverEnv n) m, MonadError Err m)
--                      => ExtLabeledItems (Type n) (Name n)
--                      -> ExtLabeledItems (Type n) (Name n) -> m ()
-- unifyExtLabeledItems r1 r2 = do
--   r1' <- zonk r1
--   r2' <- zonk r2
--   vs <- looks solverVars
--   case (r1', r2') of
--     _ | r1' == r2' -> return ()
--     (r, Ext NoLabeledItems (Just v)) | v `isin` vs ->
--       bindQ v (LabeledRow r)
--     (Ext NoLabeledItems (Just v), r) | v `isin` vs ->
--       bindQ v (LabeledRow r)
--     (_, Ext NoLabeledItems _) -> throw TypeErr ""
--     (Ext NoLabeledItems _, _) -> throw TypeErr ""
--     (Ext (LabeledItems items1) t1, Ext (LabeledItems items2) t2) -> do
--       let unifyPrefixes tys1 tys2 = mapM (uncurry unify) $ NE.zip tys1 tys2
--       sequence_ $ M.intersectionWith unifyPrefixes items1 items2
--       let diffDrop xs ys = NE.nonEmpty $ NE.drop (length ys) xs
--       let extras1 = M.differenceWith diffDrop items1 items2
--       let extras2 = M.differenceWith diffDrop items2 items1
--       newTail <- freshInferenceName LabeledRowKind
--       unifyExtLabeledItems (Ext NoLabeledItems t1)
--                            (Ext (LabeledItems extras2) (Just newTail))
--       unifyExtLabeledItems (Ext NoLabeledItems t2)
--                            (Ext (LabeledItems extras1) (Just newTail))

-- unifyEff :: (MonadCat (SolverEnv n) m, MonadError Err m)
--          => EffectRow n -> EffectRow n -> m ()
-- unifyEff r1 r2 = do
--   r1' <- zonk r1
--   r2' <- zonk r2
--   vs <- looks solverVars
--   case (r1', r2') of
--     _ | r1' == r2' -> return ()
--     (r, EffectRow effs (Just v)) | S.null effs && v `isin` vs -> bindQ v (Eff r)
--     (EffectRow effs (Just v), r) | S.null effs && v `isin` vs -> bindQ v (Eff r)
--     (EffectRow effs1 t1, EffectRow effs2 t2) | not (S.null effs1 || S.null effs2) -> do
--       let extras1 = effs1 `S.difference` effs2
--       let extras2 = effs2 `S.difference` effs1
--       newRow <- freshEff
--       unifyEff (EffectRow mempty t1) (extendEffRow extras2 newRow)
--       unifyEff (extendEffRow extras1 newRow) (EffectRow mempty t2)
--     _ -> throw TypeErr ""

-- bindQ :: (MonadCat (SolverEnv n) m, MonadError Err m) => Name n -> Type n -> m ()
-- bindQ v t | v `occursIn` t = throw TypeErr $ "Occurs check failure: " ++ pprint (v, t)
--           | hasSkolems t = throw TypeErr "Can't unify with skolem vars"
--           | otherwise = extend $ mempty { solverSub = v@>t }

-- hasSkolems :: Subst e => e n -> Bool
-- hasSkolems x = not $ any (\n -> getNameSpace n == Skolem) $ envNames $ freeVars x

-- occursIn :: Subst e => Name n -> e n -> Bool
-- occursIn v t = v `isin` freeVars t

-- renameForPrinting :: Subst e => e n -> (e n, [Name n])
-- renameForPrinting x = (scopelessSubst substEnv x, newNames)
--   where
--     fvs = freeVars x
--     infNames = filter ((== InferenceName) . getNameSpace) $ envNames fvs
--     newNames = [ genFresh NormalName (fromString name) fvs
--                | (v, name) <- zip infNames nameList]
--     substEnv = fold $ zipWith (\v v' -> v@>Var v') infNames newNames
--     nameList = map (:[]) ['a'..'z'] ++ map show [(0::Int)..]

-- instance Semigroup (SolverEnv n) where
--   -- TODO: as an optimization, don't do the subst when sub2 is empty
--   -- TODO: make concatenation more efficient by maintaining a reverse-lookup map
--   SolverEnv scope1 sub1 <> SolverEnv scope2 sub2 =
--     SolverEnv (scope1 <> scope2) (sub1' <> sub2)
--     where sub1' = fmapH (scopelessSubst sub2) sub1

-- instance Monoid (SolverEnv n) where
--   mempty = SolverEnv mempty mempty
--   mappend = (<>)

-- typeReduceScoped :: MonadBuilder n m => m (Atom n) -> m (Maybe (Atom n))
-- typeReduceScoped m = do
--   block <- buildScopedBlock m
--   bindings <- getBindings
--   return $ typeReduceBlock bindings block
