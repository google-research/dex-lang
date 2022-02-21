-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Simplify ( simplifyTopBlock, simplifyTopFunction, SimplifiedBlock (..)
                , simplifyBlock, liftSimplifyM, buildBlockSimplified
                , IxCache, MonadIxCache1, SimpleIxInstance (..)
                , simplifiedIxInstance, appSimplifiedIxMethod ) where

import Control.Category ((>>>))
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State.Class
import Data.Foldable (toList)
import Data.Text.Prettyprint.Doc (Pretty (..), hardline)
import qualified Data.Map.Strict as M
import qualified Data.HashMap.Strict as HM
import qualified Data.List.NonEmpty as NE
import qualified Data.Set as S

import Err

import Name
import MTL1
import Builder
import Syntax
import Type
import Util (enumerate)
import CheapReduction
import Linearize
import Transpose
import LabeledItems
import Util (restructure)

-- === simplification monad ===

class (ScopableBuilder2 m, SubstReader AtomSubstVal m) => Simplifier m

newtype SimplifyM (i::S) (o::S) (a:: *) = SimplifyM
  { runSimplifyM' :: SubstReaderT AtomSubstVal (BuilderT HardFailM) i o a }
  deriving ( Functor, Applicative, Monad, ScopeReader, EnvExtender
           , Builder, EnvReader, SubstReader AtomSubstVal, MonadFail)

liftSimplifyM :: (SinkableE e, EnvReader m) => SimplifyM n n (e n) -> m n (e n)
liftSimplifyM cont = do
  liftBuilder $ runSubstReaderT idSubst $ runSimplifyM' cont

buildBlockSimplified
  :: (Builder m)
  => (forall l. (Emits l, DExt n l) => BuilderM l (Atom l))
  -> m n (Block n)
buildBlockSimplified m =
  liftSimplifyM do
    block <- liftBuilder $ buildBlock m
    buildBlock $ simplifyBlock block

instance Simplifier SimplifyM

instance Fallible (SimplifyM i o) where
  throwErrs _ = undefined
  addErrCtx _ _ = undefined

-- TODO: figure out why we can't derive this one (here and elsewhere)
instance ScopableBuilder (SimplifyM i) where
  buildScoped cont = SimplifyM $ SubstReaderT $ ReaderT \env ->
    buildScoped $ runSubstReaderT (sink env) (runSimplifyM' cont)

-- === Top-level API ===

data SimplifiedBlock n = SimplifiedBlock (Block n) (ReconstructAtom n)

-- TODO: extend this to work on functions instead of blocks (with blocks still
-- accessible as nullary functions)
simplifyTopBlock :: EnvReader m => Block n -> m n (SimplifiedBlock n)
simplifyTopBlock block = liftSimplifyM do
  (Abs UnitB block', recon) <- simplifyAbs $ Abs UnitB block
  return $ SimplifiedBlock block' recon

simplifyTopFunction :: EnvReader m => NaryPiType n -> Atom n -> m n (NaryLamExpr n)
simplifyTopFunction ty f = liftSimplifyM do
  buildNaryLamExpr ty \xs -> do
    dropSubst $ simplifyExpr $ App (sink f) $ fmap Var xs

instance GenericE SimplifiedBlock where
  type RepE SimplifiedBlock = PairE Block ReconstructAtom
  fromE (SimplifiedBlock block recon) = PairE block recon
  toE   (PairE block recon) = SimplifiedBlock block recon

instance SinkableE SimplifiedBlock
instance SubstE Name SimplifiedBlock
instance CheckableE SimplifiedBlock where
  checkE (SimplifiedBlock block recon) =
    -- TODO: CheckableE instance for the recon too
    SimplifiedBlock <$> checkE block <*> substM recon

instance Pretty (SimplifiedBlock n) where
  pretty (SimplifiedBlock block recon) =
    pretty block <> hardline <> pretty recon

-- === All the bits of IR  ===

simplifyDecl ::  (Emits o, Simplifier m) => Decl i i' -> m i' o a -> m i o a
simplifyDecl (Let b (DeclBinding _ _ expr)) cont = do
  x <- simplifyExpr expr
  extendSubst (b@>SubstVal x) cont

simplifyDecls ::  (Emits o, Simplifier m) => Nest Decl i i' -> m i' o a -> m i o a
simplifyDecls Empty cont = cont
simplifyDecls (Nest decl rest) cont = simplifyDecl decl $ simplifyDecls rest cont

_simplifyStandalone :: Simplifier m => Expr i -> m i o (Atom o)
_simplifyStandalone (Atom (Lam (LamExpr (LamBinder b argTy arr Pure) body))) = do
  argTy' <- substM argTy
  buildPureLam (getNameHint b) arr argTy' \v ->
    extendSubst (b@>Rename v) $ simplifyBlock body
_simplifyStandalone block =
  error $ "@noinline decorator applied to non-pure-function" ++ pprint block

simplifyExpr :: (Emits o, Simplifier m) => Expr i -> m i o (Atom o)
simplifyExpr expr = case expr of
  App f xs -> do
    xs' <- mapM simplifyAtom xs
    f' <- simplifyAtom f
    simplifyApp f' xs'
  Atom x -> simplifyAtom x
  Op  op  -> mapM simplifyAtom op >>= simplifyOp
  Hof hof -> simplifyHof hof
  Case e alts resultTy eff -> do
    e' <- simplifyAtom e
    eff' <- substM eff
    resultTy' <- substM resultTy
    case trySelectBranch e' of
      Just (i, args) -> do
        Abs bs body <- return $ alts !! i
        extendSubst (bs @@> map SubstVal args) $ simplifyBlock body
      Nothing -> do
        substM resultTy >>= isData >>= \case
          True -> do
            alts' <- forM alts \(Abs bs body) -> do
              bs' <- substM $ EmptyAbs bs
              buildNaryAbs bs' \xs ->
                extendSubst (bs @@> map Rename xs) $
                  buildBlock $ simplifyBlock body
            liftM Var $ emit $ Case e' alts' resultTy' eff'
          False -> defuncCase e' alts resultTy'

defuncCase :: (Emits o, Simplifier m) => Atom o -> [Alt i] -> Type o -> m i o (Atom o)
defuncCase scrut alts resultTy = do
  split <- splitDataComponents resultTy
  (alts', recons) <- unzip <$> mapM (simplifyAlt split) alts
  closureTys <- mapM getAltNonDataTy alts'
  let closureSumTy = SumTy closureTys
  let newNonDataTy = nonDataTy split
  alts'' <- forM (enumerate alts') \(i, alt) -> injectAltResult closureSumTy i alt
  eff <- getAllowedEffects -- TODO: more precise effects
  caseResult <- liftM Var $ emit $
                  Case scrut alts'' (PairTy (dataTy split) closureSumTy) eff
  (dataVal, sumVal) <- fromPair caseResult
  reconAlts <- forM (zip closureTys recons) \(ty, recon) -> do
    buildUnaryAtomAlt ty \v -> applyRecon (sink recon) (Var v)
  let nonDataVal = ACase sumVal reconAlts newNonDataTy
  Distinct <- getDistinct
  fromSplit split dataVal nonDataVal
  where
    getAltNonDataTy :: EnvReader m => Alt n -> m n (Type n)
    getAltNonDataTy (Abs bs body) = liftSubstEnvReaderM do
      substBinders bs \bs' -> do
        ~(PairTy _ ty) <- getTypeSubst body
        -- Result types of simplified abs should be hoistable past binder
        return $ ignoreHoistFailure $ hoist bs' ty

    injectAltResult :: EnvReader m => Type n -> Int -> Alt n -> m n (Alt n)
    injectAltResult sumTy con (Abs bs body) = liftBuilder do
      buildAlt (EmptyAbs bs) \vs -> do
        originalResult <- emitBlock =<< applySubst (bs@@>vs) body
        (dataResult, nonDataResult) <- fromPair originalResult
        return $ PairVal dataResult $ Con $ SumCon (sink sumTy) con nonDataResult

    -- similar to `simplifyAbs` but assumes that the result is a pair whose
    -- first component is data. The reconstruction returned only applies to the
    -- second component.
    simplifyAlt
      :: (Simplifier m, BindsEnv b, SubstB Name b, SubstB AtomSubstVal b)
      => SplitDataNonData n -> Abs b Block i -> m i o (Abs b Block o, ReconstructAtom o)
    simplifyAlt split (Abs bs body) = fromPairE <$> do
      substBinders bs \bs' -> do
        ab <- buildScoped $ simplifyBlock body
        refreshAbs ab \decls result -> do
          let locals = toScopeFrag bs' >>> toScopeFrag decls
          -- TODO: this might be too cautious. The type only needs to be hoistable
          -- above the decls. In principle it can still mention vars from the lambda
          -- binders.
          Distinct <- getDistinct
          (resultData, resultNonData) <- toSplit split result
          (newResult, newResultTy, reconAbs) <- telescopicCapture locals resultNonData
          resultDataTy <- (ignoreHoistFailure . hoist decls) <$> getType resultData
          let block = Block (BlockAnn $ PairTy (sink resultDataTy) (sink newResultTy))
                            decls
                            (Atom (PairVal resultData newResult))
          return $ PairE (Abs bs' block) (LamRecon reconAbs)

simplifyApp :: (Emits o, Simplifier m) => Atom o -> NonEmpty (Atom o) -> m i o (Atom o)
simplifyApp f xs = case f of
  Lam (LamExpr b body) -> do
    let x:|rest = xs
    case nonEmpty rest of
      Nothing -> dropSubst $ extendSubst (b@>SubstVal x) $ simplifyBlock body
      Just rest' -> do
       ans <- dropSubst $ extendSubst (b@>SubstVal x) $ simplifyBlock body
       simplifyApp ans rest'
  ACase e alts ty -> do
    resultTy <- getAppType ty $ toList xs
    alts' <- forM alts \(Abs bs a) -> do
      buildAlt (EmptyAbs bs) \vs -> do
        a' <- applySubst (bs@@>vs) a
        naryApp a' (map sink $ toList xs)
    eff <- getAllowedEffects -- TODO: more precise effects
    dropSubst $ simplifyExpr $ Case e alts' resultTy eff
  _ -> naryApp f $ toList xs

simplifyAtom :: Simplifier m => Atom i -> m i o (Atom o)
simplifyAtom atom = case atom of
  Var v -> simplifyVar v
  -- Tables that only contain data aren't necessarily getting inlined,
  -- so this might be the last chance to simplify them.
  TabVal _ _ -> do
    substM atom >>= getType >>= isData >>= \case
      True -> do
        ~(tab, IdentityRecon) <- simplifyLam atom
        return tab
      False -> substM atom
  -- We don't simplify body of lam because we'll beta-reduce it soon.
  Lam _ -> substM atom
  Pi  _ -> substM atom
  DepPairTy _ -> substM atom
  DepPair x y ty -> DepPair <$> simplifyAtom x <*> simplifyAtom y <*> substM ty
  Con con -> Con <$> mapM simplifyAtom con
  TC tc -> TC <$> mapM simplifyAtom tc
  Eff eff -> Eff <$> substM eff
  TypeCon name def params ->
    TypeCon name <$>  substM def <*> mapM simplifyAtom params
  DataCon name def params con args ->
    DataCon name <$> substM def <*> mapM simplifyAtom params
                 <*> pure con <*> mapM simplifyAtom args
  Record items -> Record <$> mapM simplifyAtom items
  RecordTy _ -> substM atom >>= cheapNormalize >>= \atom' -> case atom' of
    StaticRecordTy items -> StaticRecordTy <$> dropSubst (mapM simplifyAtom items)
    _ -> error $ "Failed to simplify a record with a dynamic label: " ++ pprint atom'
  Variant types label i value -> do
    types' <- fromExtLabeledItemsE <$> substM (ExtLabeledItemsE types)
    value' <- simplifyAtom value
    return $ Variant types' label i value'
  VariantTy items -> VariantTy <$> simplifyExtLabeledItems items
  LabeledRow elems -> substM elems >>= \elems' -> case fromFieldRowElems elems' of
    [StaticFields items] -> do
      items' <- dropSubst $ mapM simplifyAtom items
      return $ LabeledRow $ fieldRowElemsFromList [StaticFields items']
    []                   -> return $ LabeledRow $ fieldRowElemsFromList []
    _ -> error "Failed to simplify a labeled row"
  ACase e alts rTy   -> do
    e' <- simplifyAtom e
    case trySelectBranch e' of
      Just (i, args) -> do
        Abs bs body <- return $ alts !! i
        extendSubst (bs @@> map SubstVal args) $ simplifyAtom body
      Nothing -> do
        rTy' <- substM rTy
        alts' <- forM alts \(Abs bs body) -> do
          bs' <- substM $ EmptyAbs bs
          buildNaryAbs bs' \xs ->
            extendSubst (bs @@> map Rename xs) $
              simplifyAtom body
        return $ ACase e' alts' rTy'
  DataConRef _ _ _ -> error "Should only occur in Imp lowering"
  BoxedRef _ _     -> error "Should only occur in Imp lowering"
  DepPairRef _ _ _ -> error "Should only occur in Imp lowering"
  ProjectElt idxs v -> getProjection (toList idxs) <$> simplifyAtom (Var v)

simplifyExtLabeledItems
  :: Simplifier m
  => ExtLabeledItems (Atom i) (AtomName i)
  -> m i o (ExtLabeledItems (Atom o) (AtomName o))
simplifyExtLabeledItems (Ext items ext) = do
    items' <- mapM simplifyAtom items
    ext' <- liftM fromExtLabeledItemsE $ substM $ ExtLabeledItemsE $ Ext NoLabeledItems ext
    return $ prefixExtLabeledItems items' ext'

simplifyVar :: Simplifier m => AtomName i -> m i o (Atom o)
simplifyVar v = do
  env <- getSubst
  case env ! v of
    SubstVal x -> return x
    Rename v' -> do
      AtomNameBinding bindingInfo <- lookupEnv v'
      case bindingInfo of
        LetBound (DeclBinding _ _ (Atom x)) -> dropSubst $ simplifyAtom x
        _ -> return $ Var v'

simplifyLam :: (Simplifier m) => Atom i -> m i o (Atom o, ReconstructAtom o)
simplifyLam lam = do
  Lam (LamExpr b body) <- substM lam
  (Abs (Nest b' Empty) body', recon) <- dropSubst $ simplifyAbs $ Abs (Nest b Empty) body
  return (Lam $ LamExpr b' body', recon)

simplifyBinaryLam :: (Emits o, Simplifier m) => Atom i -> m i o (Atom o, ReconstructAtom o)
simplifyBinaryLam binaryLam = do
  Lam (LamExpr b1 (AtomicBlock (Lam (LamExpr b2 body)))) <- substM binaryLam
  (Abs (Nest b1' (Nest b2' Empty)) body', recon) <-
      dropSubst $ simplifyAbs $ Abs (Nest b1 (Nest b2 Empty)) body
  let binaryLam' = Lam $ LamExpr b1' $ AtomicBlock $ Lam $ LamExpr b2' body'
  return (binaryLam', recon)

data SplitDataNonData n = SplitDataNonData
  { dataTy    :: Type n
  , nonDataTy :: Type n
  , toSplit   :: forall m l . (Fallible1 m, EnvReader m) => Atom l -> m l (Atom l, Atom l)
  , fromSplit :: forall m l . (Fallible1 m, EnvReader m) => Atom l -> Atom l -> m l (Atom l) }

-- bijection between that type and a (data, non-data) pair type.
splitDataComponents :: EnvReader m => Type n -> m n (SplitDataNonData n)
splitDataComponents = \case
  ProdTy tys -> do
    splits <- mapM splitDataComponents tys
    return $ SplitDataNonData
      { dataTy    = ProdTy $ map dataTy    splits
      , nonDataTy = ProdTy $ map nonDataTy splits
      , toSplit = \xProd -> do
          xs <- getUnpacked xProd
          (ys, zs) <- unzip <$> forM (zip xs splits) \(x, split) -> toSplit split x
          return (ProdVal ys, ProdVal zs)
      , fromSplit = \xsProd ysProd -> do
          xs <- getUnpacked xsProd
          ys <- getUnpacked ysProd
          zs <- forM (zip (zip xs ys) splits) \((x, y), split) -> fromSplit split x y
          return $ ProdVal zs }
  ty -> isData ty >>= \case
    True -> return $ SplitDataNonData
      { dataTy = ty
      , nonDataTy = UnitTy
      , toSplit = \x -> return (x, UnitVal)
      , fromSplit = \x _ -> return x }
    False -> return $ SplitDataNonData
      { dataTy = UnitTy
      , nonDataTy = ty
      , toSplit = \x -> return (UnitVal, x)
      , fromSplit = \_ x -> return x }

simplifyAbs
  :: (Simplifier m, BindsEnv b, SubstB Name b, SubstB AtomSubstVal b)
  => Abs b Block i -> m i o (Abs b Block o, ReconstructAtom o)
simplifyAbs (Abs bs body) = fromPairE <$> do
  substBinders bs \bs' -> do
    ab <- buildScoped $ simplifyBlock body
    refreshAbs ab \decls result -> do
      getType result >>= isData >>= \case
        True -> do
          block <- makeBlock decls $ Atom result
          return $ PairE (Abs bs' block) IdentityRecon
        False -> do
          let locals = toScopeFrag bs' >>> toScopeFrag decls
          -- TODO: this might be too cautious. The type only needs to be hoistable
          -- above the delcs. In principle it can still mention vars from the lambda
          -- binders.
          (newResult, newResultTy, reconAbs) <- telescopicCapture locals result
          let block = Block (BlockAnn $ sink newResultTy) decls (Atom newResult)
          return $ PairE (Abs bs' block) (LamRecon reconAbs)

-- TODO: come up with a coherent strategy for ordering these various reductions
simplifyOp :: (Emits o, Simplifier m) => Op o -> m i o (Atom o)
simplifyOp op = case op of
  RecordCons left right -> getType left >>= \case
    StaticRecordTy leftTys -> getType right >>= \case
      StaticRecordTy rightTys -> do
        -- Unpack, then repack with new arguments (possibly in the middle).
        leftList <- getUnpacked left
        let leftItems = restructure leftList leftTys
        rightList <- getUnpacked right
        let rightItems = restructure rightList rightTys
        return $ Record $ leftItems <> rightItems
      _ -> error "not a record"
    _ -> error "not a record"
  RecordConsDynamic (Con (LabelCon l)) val rec ->
    getType rec >>= \case
      StaticRecordTy itemTys -> do
        itemList <- getUnpacked rec
        let items = restructure itemList itemTys
        return $ Record $ labeledSingleton l val <> items
      _ -> error "not a record"
  RecordSplit f full -> getType full >>= \case
    StaticRecordTy fullTys -> case f of
      LabeledRow f' | [StaticFields fields] <- fromFieldRowElems f' -> do
        -- Unpack, then repack into two pieces.
        fullList <- getUnpacked full
        let fullItems = restructure fullList fullTys
        let (left, right) = splitLabeledItems fields fullItems
        return $ Record $ Unlabeled [Record left, Record right]
      _ -> error "failed to simplifiy a field row"
    _ -> error "not a record"
  RecordSplitDynamic (Con (LabelCon l)) rec ->
    getType rec >>= \case
      StaticRecordTy itemTys -> do
        itemList <- getUnpacked rec
        let items = restructure itemList itemTys
        let (val, rest) = splitLabeledItems (labeledSingleton l ()) items
        return $ PairVal (head $ toList val) $ Record rest
      _ -> error "not a record"
  VariantLift leftTys@(LabeledItems litems) right -> getType right >>= \case
    VariantTy (NoExt rightTys) -> do
      let fullRow = NoExt $ leftTys <> rightTys
      let labels = toList $ reflectLabels rightTys
      -- Emit a case statement (ordered by the arg type) that lifts the type.
      buildCase right (VariantTy fullRow) \caseIdx [v] -> do
          let (label, i) = labels !! caseIdx
          let idx = case M.lookup label litems of Nothing  -> i
                                                  Just tys -> i + length tys
          let fullRow' = fromExtLabeledItemsE $ sink $ ExtLabeledItemsE fullRow
          return $ Variant fullRow' label idx (Var v)
    _ -> error "not a variant"
  VariantSplit leftTys@(LabeledItems litems) full -> getType full >>= \case
    VariantTy (NoExt fullTys@(LabeledItems fullItems)) -> do
      -- Emit a case statement (ordered by the arg type) that splits into the
      -- appropriate piece, changing indices as needed.
      VariantTy resultRow <- getType $ Op op
      let splitRight ftys ltys = NE.nonEmpty $ NE.drop (length ltys) ftys
      let rightTys = LabeledItems $ M.differenceWith splitRight fullItems litems
      let labels = toList $ reflectLabels fullTys
      buildCase full (VariantTy resultRow) \caseIdx [v] -> do
        let (label, i) = labels !! caseIdx
        let resultRow' = fromExtLabeledItemsE $ sink $ ExtLabeledItemsE resultRow
        case M.lookup label litems of
          Just tys -> if i < length tys
            then return $ Variant resultRow' InternalSingletonLabel 0 $
              Variant (NoExt $ fmap sink leftTys) label i (Var v)
            else return $ Variant resultRow' InternalSingletonLabel 1 $
              Variant (NoExt $ fmap sink rightTys) label (i - length tys) $ Var v
          Nothing -> return $ Variant resultRow' InternalSingletonLabel 1 $
            Variant (NoExt $ fmap sink rightTys) label i $ Var v
    _ -> error "Not a variant type"
  CastOp (BaseTy (Scalar Int32Type)) (Con (Lit (Int64Lit val))) ->
    return $ Con $ Lit $ Int32Lit $ fromIntegral val
  _ -> emitOp op

simplifyHof :: (Emits o, Simplifier m) => Hof i -> m i o (Atom o)
simplifyHof hof = case hof of
  For d lam@(Lam lamExpr) -> do
    ixTy <- substM $ lamArgType lamExpr
    (lam', recon) <- simplifyLam lam
    ans <- liftM Var $ emit $ Hof $ For d lam'
    case recon of
      IdentityRecon -> return ans
      LamRecon reconAbs ->
        buildPureLam "i" TabArrow ixTy \i' -> do
          elt <- app (sink ans) $ Var i'
          applyReconAbs (sink reconAbs) elt
  While body -> do
    (lam', IdentityRecon) <- simplifyLam body
    liftM Var $ emit $ Hof $ While lam'
  RunReader r lam -> do
    r' <- simplifyAtom r
    (lam', recon) <- simplifyBinaryLam lam
    ans <- emit $ Hof $ RunReader r' lam'
    applyRecon recon $ Var ans
  RunWriter (BaseMonoid e combine) lam -> do
    e' <- simplifyAtom e
    (combine', IdentityRecon) <- simplifyBinaryLam combine
    (lam', recon) <- simplifyBinaryLam lam
    let hof' = Hof $ RunWriter (BaseMonoid e' combine') lam'
    (ans, w) <- fromPair =<< liftM Var (emit hof')
    ans' <- applyRecon recon ans
    return $ PairVal ans' w
  RunState s lam -> do
    s' <- simplifyAtom s
    (lam', recon) <- simplifyBinaryLam lam
    resultPair <- emit $ Hof $ RunState s' lam'
    (ans, sOut) <- fromPair $ Var resultPair
    ans' <- applyRecon recon ans
    return $ PairVal ans' sOut
  RunIO lam -> do
    (lam', recon) <- simplifyLam lam
    ans <- emit $ Hof $ RunIO lam'
    applyRecon recon $ Var ans
  Linearize lam -> do
    ~(lam', IdentityRecon) <- simplifyLam lam
    linearize lam'
  Transpose lam -> do
    ~(lam', IdentityRecon) <- simplifyLam lam
    transpose lam'
  CatchException lam -> do
    (Lam (LamExpr b body), IdentityRecon) <- simplifyLam lam
    dropSubst $ extendSubst (b@>SubstVal UnitVal) $ exceptToMaybeBlock $ body
  _ -> error $ "not implemented: " ++ pprint hof

simplifyBlock :: (Emits o, Simplifier m) => Block i -> m i o (Atom o)
simplifyBlock (Block _ decls result) = simplifyDecls decls $ simplifyExpr result

exceptToMaybeBlock :: (Emits o, Simplifier m) => Block i -> m i o (Atom o)
exceptToMaybeBlock (Block (BlockAnn ty) decls result) = do
  ty' <- substM ty
  exceptToMaybeDecls ty' decls result
exceptToMaybeBlock (Block NoBlockAnn Empty result) = exceptToMaybeExpr result
exceptToMaybeBlock _ = error "impossible"

exceptToMaybeDecls :: (Emits o, Simplifier m) => Type o -> Nest Decl i i' -> Expr i' -> m i o (Atom o)
exceptToMaybeDecls _ Empty result = exceptToMaybeExpr result
exceptToMaybeDecls resultTy (Nest (Let b (DeclBinding _ _ rhs)) decls) finalResult = do
  maybeResult <- exceptToMaybeExpr rhs
  case maybeResult of
    -- This case is just an optimization (but an important one!)
    JustAtom _ x  ->
      extendSubst (b@> SubstVal x) $ exceptToMaybeDecls resultTy decls finalResult
    _ -> emitMaybeCase maybeResult (MaybeTy resultTy)
          (return $ NothingAtom $ sink resultTy)
          (\v -> extendSubst (b@> Rename v) $
                   exceptToMaybeDecls (sink resultTy) decls finalResult)

exceptToMaybeExpr :: (Emits o, Simplifier m) => Expr i -> m i o (Atom o)
exceptToMaybeExpr expr = case expr of
  Case e alts resultTy _ -> do
    e' <- substM e
    resultTy' <- substM $ MaybeTy resultTy
    buildCase e' resultTy' \i vs -> do
      Abs bs body <- return $ alts !! i
      extendSubst (bs @@> map Rename vs) $ exceptToMaybeBlock body
  Atom x -> do
    x' <- substM x
    ty <- getType x'
    return $ JustAtom ty x'
  Op (ThrowException _) -> do
    ty <- substM expr >>= getType
    return $ NothingAtom ty
  Hof (For ann (Lam (LamExpr b body))) -> do
    ty <- substM $ binderType b
    maybes <- buildForAnn (getNameHint b) ann ty \i ->
      extendSubst (b@>Rename i) $ exceptToMaybeBlock body
    catMaybesE maybes
  Hof (RunState s lam) -> do
    s' <- substM s
    Lam (BinaryLamExpr h ref body) <- return lam
    result  <- emitRunState "ref" s' \h' ref' ->
      extendSubst (h @> Rename h' <.> ref @> Rename ref') do
        exceptToMaybeBlock body
    (maybeAns, newState) <- fromPair result
    -- TODO: figure out the return type (or have `emitMaybeCase` do it) rather
    -- than do the whole subsitution here. Similarly in the RunWriter case.
    a <- getType =<< substM expr
    emitMaybeCase maybeAns (MaybeTy a)
       (return $ NothingAtom $ sink a)
       (\ans -> return $ JustAtom (sink a) $ PairVal (Var ans) (sink newState))
  Hof (RunWriter monoid (Lam (BinaryLamExpr h ref body))) -> do
    monoid' <- mapM substM monoid
    accumTy <- substM =<< (getReferentTy $ EmptyAbs $ PairB h ref)
    result <- emitRunWriter "ref" accumTy monoid' \h' ref' ->
      extendSubst (h @> Rename h' <.> ref @> Rename ref') $
        exceptToMaybeBlock body
    (maybeAns, accumResult) <- fromPair result
    a <- getType =<< substM expr
    emitMaybeCase maybeAns (MaybeTy a)
      (return $ NothingAtom $ sink a)
      (\ans -> return $ JustAtom (sink a) $ PairVal (Var ans) (sink accumResult))
  Hof (While (Lam (LamExpr b body))) ->
    runMaybeWhile $ extendSubst (b@>SubstVal UnitVal) $ exceptToMaybeBlock body
  _ -> do
    expr' <- substM expr
    hasExceptions expr' >>= \case
      True -> error $ "Unexpected exception-throwing expression: " ++ pprint expr
      False -> do
        v <- emit expr'
        ty <- getType v
        return $ JustAtom ty (Var v)

hasExceptions :: (EnvReader m, MonadFail1 m) => Expr n -> m n Bool
hasExceptions expr = do
  (EffectRow effs t) <- exprEffects expr
  case t of
    Nothing -> return $ ExceptionEffect `S.member` effs
    Just _  -> error "Shouldn't have tail left"

-- === Ix simplification ===

data SimpleIxInstance (n::S) =
  SimpleIxInstance
    { simpleIxSize            :: (Abs (Nest Decl) LamExpr n)
    , simpleToOrdinal         :: (Abs (Nest Decl) LamExpr n)
    , simpleUnsafeFromOrdinal :: (Abs (Nest Decl) LamExpr n)
    }

instance GenericE SimpleIxInstance where
  type RepE SimpleIxInstance = (PairE (Abs (Nest Decl) LamExpr)
                                 (PairE (Abs (Nest Decl) LamExpr)
                                        (Abs (Nest Decl) LamExpr)))
  fromE (SimpleIxInstance a b c) = PairE a (PairE b c)
  toE (PairE a (PairE b c)) = SimpleIxInstance a b c

instance SubstE Name SimpleIxInstance
instance SinkableE SimpleIxInstance
instance HoistableE SimpleIxInstance

type IxCache = HashMapE (EKey Type) SimpleIxInstance

type MonadIxCache1 (m::MonadKind1) = forall n. MonadState (IxCache n) (m n)

instance Monad1 m => HoistableState IxCache m where
  -- TODO: I think we can do hoisting only based on the free vars in keys.
  -- Instances should only be added at the top-level so it's not like they
  -- can refer to any local vars that could prevent the values from being hoistable.
  hoistState s b s' = case hoist b s' of
    HoistSuccess s'' -> return s''
    HoistFailure _   -> return s

simplifiedIxInstance
  :: (EnvReader m, MonadIxCache1 m)
  => Type n -> m n (SimpleIxInstance n)
simplifiedIxInstance ty = do
  let key = EKey ty
  gets (HM.lookup key . fromHashMapE) >>= \case
    Just a -> return a
    Nothing -> do
      a <- simplifyInstance
      modify (<> (HashMapE $ HM.singleton key a))
      return a
  where
    simplifyInstance = liftSimplifyM do
      Block _ decls expr <- liftBuilder $ buildBlock $ do
        impl <- getIxImpl $ sink ty
        return $ ProdVal [ixSize impl, toOrdinal impl, unsafeFromOrdinal impl]
      simpBlock <- buildBlock $ simplifyDecls decls $
        simplifyExpr expr >>= \case
          ProdVal [size, toOrd, fromOrd] -> dropSubst do
            (size'   , IdentityRecon) <- simplifyLam size
            (toOrd'  , IdentityRecon) <- simplifyLam toOrd
            (fromOrd', IdentityRecon) <- simplifyLam fromOrd
            return $ ProdVal [size', toOrd', fromOrd']
          _ -> error "Failed to simplify Ix methods"
      case simpBlock of
        Block _ simpDecls (Atom (ProdVal [Lam size, Lam toOrd, Lam fromOrd])) -> do
          return $ SimpleIxInstance (Abs simpDecls size) (Abs simpDecls toOrd) (Abs simpDecls fromOrd)
        _ -> error "Failed to simplify Ix methods"

appSimplifiedIxMethod
  :: (Emits n, Builder m, MonadIxCache1 m)
  => Type n -> (SimpleIxInstance n -> Abs (Nest Decl) LamExpr n)
  -> Atom n -> m n (Atom n)
appSimplifiedIxMethod ty method x = do
  Abs decls f <- method <$> simplifiedIxInstance ty
  f' <- emitDecls decls f
  Distinct <- getDistinct
  case f' of
    LamExpr fx' fb' -> emitBlock =<< applySubst (fx' @> SubstVal x) fb'
