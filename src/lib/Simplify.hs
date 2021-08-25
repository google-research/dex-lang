-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}

module Simplify (simplifyModule, splitSimpModule) where

import Control.Monad
import Control.Monad.Reader
import Data.Maybe
import Data.Foldable (toList)
import Data.Functor
import Data.List (partition, elemIndex)
import Data.Graph (graphFromEdges, topSort)
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import GHC.Stack

import Autodiff
import Env
import LabeledItems
import Syntax
import Cat
import Builder
import Type
import PPrint
import Util

type SimplifyM = SubstBuilder

simplifyModule :: Bindings -> Module -> Module
simplifyModule scope (Module Core decls result) = do
  let (result', (_, decls')) = runSubstBuilder scope mempty do
                                 env <- simplifyDecls decls
                                 extendR env $ substBuilderR result
  let isAtomDecl decl = case decl of Let _ _ (Atom _) -> True; _ -> False
  -- XXX: this is very iffy. There's no guarantee that the scoping works out,
  --      since the atoms' names might be used in later non-atom decls.
  let (declsDone, declsNotDone) = partition isAtomDecl $ toList decls'
  let bindings = foldMap boundVars declsDone
  let result'' = prependBindings bindings result'
  Module Simp (toNest declsNotDone) result''
simplifyModule _ (Module ir _ _) = error $ "Expected Core, got: " ++ show ir

-- XXX: copied from Inference. It's sketchy both here and there
prependBindings :: Bindings -> EvaluatedModule -> EvaluatedModule
prependBindings bindings (EvaluatedModule bindings' scs sourceMap) =
  EvaluatedModule (bindings <> bindings') scs sourceMap

splitSimpModule :: Bindings -> Module -> (Block, Abs Binder Module)
splitSimpModule scope (Module _ decls bindings) = do
  let localScope = boundVars decls
  let localVars = bindingsAsVars $ freeVars bindings `envIntersect` localScope
  let (blockResult, recon) = fst $ runBuilder (scope <> boundVars decls) mempty $
        mkTelescope localScope $ Var <$> localVars
  let block = Block decls $ Atom blockResult
  let (Abs b (decls', bindings')) =
        fst $ runBuilder scope mempty $ buildAbs (Bind ("result":>getType block)) $
          \result -> do
             results <- recon result
             substBuilder (newEnv localVars $ map SubstVal results) bindings
  (block, Abs b (Module Evaluated decls' bindings'))

mkTelescope :: forall m. MonadBuilder m => Scope -> [Atom] -> m (Atom, Atom -> m [Atom])
mkTelescope localScope atoms = do
  let xs = bindingsAsVars $ foldMap localFVs atoms
  -- XXX: This is valid iff our IR satisfies the property that the type of an atom
  -- never has more free vars than the atom itself.
  let varsInTypes = foldMap (localFVs . varType) xs
  let xsNoType = filter (not . (`isin` varsInTypes)) xs
  let (graph, nodeFromVertex, _) = graphFromEdges $ (bindingsAsVars varsInTypes) <&> \v ->
        (v, varName v, varName <$> (bindingsAsVars $ localFVs $ varType v))
  let orderedVars = fst3 . nodeFromVertex <$> topSort graph
  (packedXs, recon) <- flip runReaderT mempty $ buildDepPairs orderedVars xsNoType
  -- TODO: Don't put everything under all the binders
  return (packedXs, \p -> do
    env <- recon p
    substBuilder env atoms)
  where
    localFVs a = freeVars a `envIntersect` localScope

    buildDepPairs :: [Var] -> [Var] -> ReaderT SubstEnv m (Atom, Atom -> m SubstEnv)
    buildDepPairs vs xs = case vs of
      []  -> return (ProdVal $ Var <$> xs, \p -> do newEnv xs <$> (map SubstVal <$> getUnpacked p))
      v:t -> do
        (tp, recon) <- buildDepPairs t xs
        a <- buildAAbs (Bind v) \vb -> extendR (v@> SubstVal vb) $ substBuilderR $ getType tp
        return (DepPair (Var v) tp a, \p -> do
          ~[rv, rc] <- getUnpacked p
          env <- recon rc
          return $ env <> v @> SubstVal rv)

    fst3 (a, _, _) = a

simplifyDecls :: Nest Decl -> SimplifyM SubstEnv
simplifyDecls Empty = return mempty
simplifyDecls (Nest decl rest) = do
  substEnv <- simplifyDecl decl
  substEnv' <- extendR substEnv $ simplifyDecls rest
  return (substEnv <> substEnv')

simplifyDecl :: Decl -> SimplifyM SubstEnv
simplifyDecl (Let NoInlineLet (Bind (name:>_)) expr) = do
  x <- simplifyStandalone expr
  withNameHint name $ emitAnn NoInlineLet (Atom x) $> mempty
simplifyDecl (Let _ b expr) = do
  x <- simplifyExpr expr
  return $ b @> SubstVal  x

simplifyStandalone :: Expr -> SimplifyM Atom
simplifyStandalone (Atom (LamVal b body)) = do
  b' <- mapM substBuilderR b
  buildLam b' PureArrow \x ->
    extendR (b@> SubstVal x) $ simplifyBlock body
simplifyStandalone block =
  error $ "@noinline decorator applied to non-function" ++ pprint block

simplifyBlock :: Block -> SimplifyM Atom
simplifyBlock (Block decls result) = do
  substEnv <- simplifyDecls decls
  extendR substEnv $ simplifyExpr result

simplifyAtom :: Atom -> SimplifyM Atom
simplifyAtom atom = case atom of
  Var v -> do
    substEnv <- ask
    scope <- getScope
    case envLookup substEnv v of
      Just (SubstVal x) -> return x
      Just (Rename v') -> do
        ty <- substBuilderR $ varAnn v
        return $ Var $ v' :> ty
      Nothing -> case envLookup scope v of
        Just (AtomBinderInfo _ info) -> case info of
          LetBound ann (Atom x) | ann /= NoInlineLet -> dropSub $ simplifyAtom x
          _ -> substBuilderR atom
        _   -> substBuilderR atom
  -- Tables that only contain data aren't necessarily getting inlined,
  -- so this might be the last chance to simplify them.
  TabVal _ _ -> do
    case isData (getType atom) of
      True -> do
        ~(tab', Nothing) <- simplifyLam atom
        return tab'
      False -> substBuilderR atom
  -- We don't simplify body of lam because we'll beta-reduce it soon.
  Lam _ -> substBuilderR atom
  Pi  _ -> substBuilderR atom
  DepPairTy _ -> substBuilderR atom
  DepPair x y at -> do
    DepPair <$> simplifyAtom x <*> simplifyAtom y <*> substBuilderR at
  Con con -> Con <$> mapM simplifyAtom con
  TC tc -> TC <$> mapM simplifyAtom tc
  Eff eff -> Eff <$> substBuilderR eff
  TypeCon def params          -> TypeCon def <$> mapM simplifyAtom params
  DataCon def params con args -> DataCon def <$> mapM simplifyAtom params
                                             <*> pure con <*> mapM simplifyAtom args
  Record items -> Record <$> mapM simplifyAtom items
  RecordTy items -> RecordTy <$> simplifyExtLabeledItems items
  Variant types label i value -> Variant <$>
    substBuilderR types <*> pure label <*> pure i <*> simplifyAtom value
  VariantTy items -> VariantTy <$> simplifyExtLabeledItems items
  LabeledRow items -> LabeledRow <$> simplifyExtLabeledItems items
  ACase e alts rty   -> do
    e' <- substBuilderR e
    case simplifyCase e' alts of
      Just (env, result) -> extendR env $ simplifyAtom result
      Nothing -> do
        alts' <- forM alts \(Abs bs a) -> do
          bs' <- mapM (mapM substBuilderR) bs
          (Abs bs'' b) <- buildNAbs bs' \xs -> extendR (newEnv bs' (map SubstVal xs)) $ simplifyAtom a
          case b of
            Block Empty (Atom r) -> return $ Abs bs'' r
            _                    -> error $ "Nontrivial block in ACase simplification"
        ACase e' alts' <$> (substBuilderR rty)
  DataConRef _ _ _ -> error "Should only occur in Imp lowering"
  BoxedRef _ _ _ _ -> error "Should only occur in Imp lowering"
  DepPairRef _ _ _ -> error "Should only occur in Imp lowering"
  ProjectElt idxs v -> getProjection (toList idxs) <$> simplifyAtom (Var v)

simplifyExtLabeledItems :: ExtLabeledItems Atom Name -> SimplifyM (ExtLabeledItems Atom Name)
simplifyExtLabeledItems (Ext items ext) = do
    items' <- mapM simplifyAtom items
    ext' <- substBuilderR (Ext NoLabeledItems ext)
    return $ prefixExtLabeledItems items' ext'

-- `Nothing` is equivalent to `Just return` but we can pattern-match on it
type Reconstruct m a = Maybe (a -> m a)

simplifyLam :: HasCallStack => Atom -> SimplifyM (Atom, Reconstruct SimplifyM Atom)
simplifyLam = simplifyLams 1

simplifyBinaryLam :: HasCallStack => Atom -> SimplifyM (Atom, Reconstruct SimplifyM Atom)
simplifyBinaryLam = simplifyLams 2

-- Unlike `substBuilderR`, this simplifies under the binder too.
simplifyLams :: HasCallStack => Int -> Atom -> SimplifyM (Atom, Reconstruct SimplifyM Atom)
simplifyLams numArgs lam = do
  lam' <- substBuilderR lam
  dropSub $ go numArgs mempty $ Block Empty $ Atom lam'
  where
    go 0 scope block = do
      result <- defunBlock scope block
      return $ case result of
        Left  res -> (res, Nothing)
        Right (dat, (ctx, recon), atomf) ->
          ( ProdVal $ (toList dat) ++ (toList ctx)
          , Just \vals -> do
             (datEls', ctxEls') <- splitAt (length dat) <$> getUnpacked vals
             let dat' = restructure datEls' dat
             let ctx' = restructure ctxEls' ctx
             atomf dat' <$> recon dat' ctx'
          )
    go n scope (Block Empty (Atom (Lam (Abs b (arr, body))))) = do
      b' <- mapM substBuilderR b
      buildLamAux b' (\x -> extendR (b@> SubstVal x) $ substBuilderR arr) \x@(Var v) -> do
        let scope' = scope <> v @> AtomBinderInfo (varType v) (LamBound (void arr))
        extendR (b@> SubstVal x) $ go (n-1) scope' body
    go n _ lam' = error $
      "Expected " <> show n <> "-arg lambda, got: " <> pprint lam'

defunBlock :: Scope -> Block -> SimplifyM (Either Atom (AtomFac SimplifyM))
defunBlock localScope block = do
  if isData (getType block)
    then Left <$> simplifyBlock block
    else do
      (result, ((localScope',_), decls)) <- builderScoped $ simplifyBlock block
      mapM_ emitDecl decls
      Right <$> separateDataComponent (localScope <> localScope') result

data RTree a = RNode [RTree a] | RLeaf a
               deriving (Functor, Foldable, Traversable)

pattern RNil :: RTree a
pattern RNil = RNode []

-- Factorization of the atom into data and non-data components
-- TODO: Make the non-data reconstruction take the scope instead of being monadic
type DataA = Atom
type NonDataA = Atom
type CtxA = Atom
type AtomFac m =
  ( RTree DataA    -- data components
  , ( RTree CtxA   -- data necessary to reconstruct non-data atoms
    , RTree DataA -> RTree CtxA -> m (RTree NonDataA) )  -- non-data reconstruction
  , RTree DataA -> RTree NonDataA -> Atom )              -- original atom reconstruction

-- TODO: Records
-- Guarantees that data elements are entirely type driven (e.g. won't be deduplicated based on
-- the supplied atom). The same guarantee doesn't apply to the non-data closures.
separateDataComponent :: forall m. MonadBuilder m => Scope -> Atom -> m (AtomFac m)
separateDataComponent localVars v = do
  (dat, (ctx, recon), atomf) <- rec v
  let (ctx', ctxRec) = dedup dat ctx
  let recon' = \dat'' ctx'' -> recon $ ctxRec dat'' (toList ctx'')
  let typeVars = foldMap (freeVars . getType) dat <> foldMap (freeVars . getType) ctx'
  -- Make sure that we're not leaking any local variables in the type
  case null $ typeVars `envIntersect` localVars of
    True  -> return (dat, (RNode $ fmap RLeaf ctx', recon'), atomf)
    False -> error $ "Failed to simplify the program: packing of " ++
                     "dependent local variables not implemented"
  where
    rec atom = do
      let atomTy = getType atom
      case atomTy of
        PairTy _ _ -> do
          (x, y) <- fromPair atom
          (xdat, (xctx, xrecon), xatomf) <- rec x
          (ydat, (yctx, yrecon), yatomf) <- rec y
          let recon = \(RNode [xctx', yctx']) -> do
                xnondat' <- xrecon xctx'
                ynondat' <- yrecon yctx'
                return $ RNode [xnondat', ynondat']
          let atomf = \(RNode [xdat', ydat']) (RNode [xnondat', ynondat']) ->
                PairVal (xatomf xdat' xnondat') (yatomf ydat' ynondat')
          return (RNode [xdat, ydat], (RNode [xctx, yctx], recon), atomf)
        UnitTy            -> return (RNil      , (RNil, nilRecon), \RNil      RNil      -> UnitVal)
        _ | isData atomTy -> return (RLeaf atom, (RNil, nilRecon), \(RLeaf a) RNil      -> a)
        _                 -> return (RNil      , nonDataRecon    , \RNil      (RLeaf a) -> a)
        where
          nilRecon = \_ -> return RNil
          nonDataRecon = (RNode $ fmap (RLeaf . Var) vs, recon)
            where
              recon xs = do
                scope <- getScope
                return $ RLeaf $ subst (newEnv vs (fmap SubstVal xs), scope) atom
          vs = bindingsAsVars $ localVars `envIntersect` freeVars atom

    -- TODO: This function is really slow, but I'm not sure if we can come up with
    --       anything better that only assumes Eq. We might want to switch contexts
    --       to Vars instead, so that we can exploit their Ord instance.
    dedup :: (Foldable h, Functor f, Foldable f, Eq a)
          => h a -> f a -> ([a], h a -> [a] -> f a)
    dedup ctx ll = (result, inv)
      where
        nubCtx [] = []
        nubCtx (h:t) = case h `elem` t || h `elem` (toList ctx) of
          True  -> nubCtx t
          False -> h : (nubCtx t)
        result = nubCtx $ toList ll
        inv ctx' result' = for ll \x -> case elemIndex x (toList ctx) of
          Just i  -> (toList ctx') !! i
          Nothing -> result' !! (fromJust $ elemIndex x result)


simplifyExpr :: Expr -> SimplifyM Atom
simplifyExpr expr = case expr of
  App f x -> do
    x' <- simplifyAtom x
    f' <- simplifyAtom f
    case f' of
      Lam (Abs b (_, body)) ->
        dropSub $ extendR (b@> SubstVal x') $ simplifyBlock body
      DataCon def params con xs -> return $ DataCon def params' con xs'
         where (_, DataDef _ paramBs _) = def
               (params', xs') = splitAt (length paramBs) $ params ++ xs ++ [x']
      ACase e alts ~(Pi ab) -> do
        let rty' = snd $ applyAbs ab $ getType x'
        case all isCurriedFun alts of
          True -> return $ ACase e (fmap appAlt alts) rty'
          False -> do
            let alts' = for alts \(Abs bs a) -> Abs bs $ Block Empty (App a x')
            dropSub $ simplifyExpr $ Case e alts' rty'
        where
          isCurriedFun alt = case alt of
            Abs _ (LamVal _ (Block Empty (Atom (LamVal _ _)))) -> True
            _ -> False
          appAlt ~(Abs bs (LamVal b (Block Empty (Atom r)))) =
            Abs bs $ subst (b @> SubstVal  x', mempty) r
      TypeCon def params -> return $ TypeCon def params'
         where params' = params ++ [x']
      _ -> emit $ App f' x'
  Op  op  -> mapM simplifyAtom op >>= simplifyOp
  Hof hof -> simplifyHof hof
  Atom x  -> simplifyAtom x
  Case e alts resultTy -> do
    e' <- simplifyAtom e
    resultTy' <- substBuilderR resultTy
    case simplifyCase e' alts of
      Just (env, body) -> extendR env $ simplifyBlock body
      Nothing -> do
        if isData resultTy'
          then do
            alts' <- forM alts \(Abs bs body) -> do
              bs' <-  mapM (mapM substBuilderR) bs
              buildNAbs bs' \xs -> extendR (newEnv bs' (map SubstVal xs)) $ simplifyBlock body
            emit $ Case e' alts' resultTy'
          else do
            -- Construct the blocks of new cases. The results will only get replaced
            -- later, once we learn the closures of the non-data component of each case.
            (alts', facs) <- liftM unzip $ forM alts \(Abs bs body) -> do
              bs' <-  mapM (mapM substBuilderR) bs
              buildNAbsAux bs' \xs -> do
                ~(Right fac@(dat, (ctx, _), _)) <- extendR (newEnv bs' (map SubstVal xs)) $
                                                     defunBlock (boundVars bs') body
                -- NB: The return value here doesn't really matter as we're going to replace it afterwards.
                return (ProdVal $ toList dat ++ toList ctx, fac)
            -- Now that we know the exact set of values each case needs, ctxDef is a sum type
            -- that can encapsulate the necessary contexts.
            -- TODO: Handle dependency once separateDataComponent supports it
            let altCtxTypes = fmap (\(_, (ctx, _), _) -> fmap getType $ toList ctx) facs
            let closureTy = SumTy (map ProdTy altCtxTypes)
            -- New cases return a pair of data components, and a closure for non-data atoms
            let alts'' = for (enumerate $ zip alts' facs) $
                  \(i, (Abs bs (Block decls _), (dat, (ctx, _), _))) ->
                    Abs bs $ Block decls $ Atom $
                      PairVal (ProdVal $ toList dat) (SumVal closureTy i $ ProdVal $ toList ctx)
            -- Here, we emit the case expression and unpack the results. All the trees
            -- should be the same, so we just pick the first one.
            let (datType, datTree) = (\(dat, _, _) -> (getType $ ProdVal $ toList dat, dat)) $ head facs
            caseResult <- emit $ Case e' alts'' $ PairTy datType closureTy
            (cdat, cctx) <- fromPair caseResult
            dat <- flip restructure datTree <$> getUnpacked cdat
            -- At this point we have the data components `dat` ready to be applied to the
            -- full atom reconstruction function, but we only have the sum type for the closures
            -- and a list of potential non-data reconstruction functions. To get a list of
            -- the non-data atoms we reconstruct the individual cases using ACase.
            -- TODO: Consider splitting the contexts over multiple non-data values, so that we
            --       don't have to emit a single shared ACase for them.
            -- TODO: We're running the reconstructions multiple times, and always only selecting
            --       a single output. This can probably be made quite a bit faster.
            -- NB: All the non-data trees have the same structure, so we pick an arbitrary one.
            nondatTree <- (\(_, (ctx, rec), _) -> rec dat ctx) $ head facs
            nondat <- forM (enumerate nondatTree) \(i, _) -> do
              aalts <- forM facs \(_, (ctx, rec), _) -> do
                Abs bs' b <- buildNAbs (toNest [Ignore $ ProdTy $ toList $ fmap getType ctx]) \[ctxVal] -> do
                  ctxVals <- getUnpacked ctxVal
                  ((!! i) . toList) <$> rec dat (restructure ctxVals ctx)
                case b of
                  Block Empty (Atom r) -> return $ Abs bs' r
                  _ -> error $ "Reconstruction function emitted a nontrivial block: " ++ pprint b
              return $ ACase cctx aalts $ caseType $ head aalts
            -- We're done! Apply the full atom reconstruction function and call it a day!
            let atomf = (\(_, _, f) -> f) $ head facs
            return $ atomf dat nondat
            where caseType (Abs _ block) = getType block


-- TODO: come up with a coherent strategy for ordering these various reductions
simplifyOp :: Op -> SimplifyM Atom
simplifyOp op = case op of
  RecordCons left right -> case getType right of
    RecordTy (NoExt rightTys) -> do
      -- Unpack, then repack with new arguments (possibly in the middle).
      rightList <- getUnpacked right
      let rightItems = restructure rightList rightTys
      return $ Record $ left <> rightItems
    _ -> emitOp op
  RecordSplit (LabeledItems litems) full -> case getType full of
    RecordTy (NoExt fullTys) -> do
      -- Unpack, then repack into two pieces.
      fullList <- getUnpacked full
      let LabeledItems fullItems = restructure fullList fullTys
          splitLeft fvs ltys = NE.fromList $ NE.take (length ltys) fvs
          left = M.intersectionWith splitLeft fullItems litems
          splitRight fvs ltys = NE.nonEmpty $ NE.drop (length ltys) fvs
          right = M.differenceWith splitRight fullItems litems
      return $ Record $ Unlabeled $
        [Record (LabeledItems left), Record (LabeledItems right)]
    _ -> emitOp op
  VariantLift leftTys@(LabeledItems litems) right -> case getType right of
    VariantTy (NoExt rightTys) -> do
      -- Emit a case statement (ordered by the arg type) that lifts the type.
      let fullRow = NoExt $ leftTys <> rightTys
          buildAlt label i vty = buildNAbs (toNest [Ignore vty]) $
            \[x] -> return $ Variant fullRow label i x
          liftAlt (label, i, vty) = case M.lookup label litems of
            Just tys -> buildAlt label (i + length tys) vty
            Nothing -> buildAlt label i vty
      alts <- mapM liftAlt $ toList $ withLabels rightTys
      -- Simplify the case away if we can.
      dropSub $ simplifyExpr $ Case right alts $ VariantTy fullRow
    _ -> emitOp op
  VariantSplit leftTys@(LabeledItems litems) full -> case getType full of
    VariantTy (NoExt fullTys@(LabeledItems fullItems)) -> do
      -- Emit a case statement (ordered by the arg type) that splits into the
      -- appropriate piece, changing indices as needed.
      let splitRight ftys ltys = NE.nonEmpty $ NE.drop (length ltys) ftys
          rightTys = LabeledItems $ M.differenceWith splitRight fullItems litems
          VariantTy resultRow = getType $ Op op
          asLeft label i vty = buildNAbs (toNest [Ignore vty]) $
            \[x] -> return $ Variant resultRow InternalSingletonLabel 0
                                $ Variant (NoExt leftTys) label i x
          asRight label i vty = buildNAbs (toNest [Ignore vty]) $
            \[x] -> return $ Variant resultRow InternalSingletonLabel 1
                                $ Variant (NoExt rightTys) label i x
          splitAlt (label, i, vty) = case M.lookup label litems of
            Just tys -> if i < length tys
                        then asLeft label i vty
                        else asRight label (i - length tys) vty
            Nothing -> asRight label i vty
      alts <- mapM splitAlt $ toList $ withLabels fullTys
      -- Simplify the case away if we can.
      dropSub $ simplifyExpr $ Case full alts $ VariantTy resultRow
    _ -> emitOp op
  SumToVariant (ACase scrutinee alts _) -> do
    scrutinee' <- substBuilderR scrutinee
    alts' <- substBuilderR alts
    ~resultTy'@(VariantTy labs) <- substBuilderR $ getType $ Op op
    -- NB: Technically the alternative bodies can also be SumAsProd constructors,
    -- but that should never happen. Those are only introduced during Imp lowering
    -- and so the only way to introduce them here would via inlining of results of
    -- another compilation unit. However, the builtin sum types are always internal
    -- to the compilation units, because they are not exposed to the surface
    -- language, so they cannot get introduced via inlining!
    let variantAlts = alts' <&> \(Abs bs (SumVal _ i val)) ->
          Abs bs $ Variant labs "c" i val
    return $ ACase scrutinee' variantAlts resultTy'
  PrimEffect ref (MExtend f) -> dropSub $ do
    ~(f', Nothing) <- simplifyLam f
    emitOp $ PrimEffect ref $ MExtend f'
  _ -> emitOp op

simplifyHof :: Hof -> SimplifyM Atom
simplifyHof hof = case hof of
  For d lam -> do
    ~(lam'@(Lam (Abs i _)), recon) <- simplifyLam lam
    ans <- emit $ Hof $ For d lam'
    case recon of
      Nothing -> return ans
      Just f  -> buildLam i TabArrow \i' -> app ans i' >>= f
  Tile d fT fS -> do
    ~(fT', Nothing) <- simplifyLam fT
    ~(fS', Nothing) <- simplifyLam fS
    emit $ Hof $ Tile d fT' fS'
  PTileReduce _ _ _ -> error "Unexpected PTileReduce"
  While body -> do
    ~(body', Nothing) <- simplifyLam body
    emit $ Hof $ While body'
  Linearize lam -> do
    ~(lam', Nothing) <- simplifyLam lam
    scope <- getScope
    -- TODO: simplify the result to remove functions introduced by linearization
    return $ linearize scope lam'
  Transpose lam -> do
    ~(lam', Nothing) <- simplifyLam lam
    scope <- getScope
    return $ transpose scope lam'
  RunReader r lam -> do
    r' <- simplifyAtom r
    ~(lam', recon) <- simplifyBinaryLam lam
    applyRecon recon =<< (emit $ Hof $ RunReader r' lam')
  RunWriter (BaseMonoid e combine) lam -> do
    e' <- simplifyAtom e
    ~(combine', Nothing) <- simplifyBinaryLam combine
    ~(lam', recon) <- simplifyBinaryLam lam
    (ans, w) <- fromPair =<< (emit $ Hof $ RunWriter (BaseMonoid e' combine') lam')
    ans' <- applyRecon recon ans
    return $ PairVal ans' w
  RunState s lam -> do
    s' <- simplifyAtom s
    ~(lam', recon) <- simplifyBinaryLam lam
    (ans, sOut) <- fromPair =<< (emit $ Hof $ RunState s' lam')
    ans' <- applyRecon recon ans
    return $ PairVal ans' sOut
  RunIO lam -> do
    ~(lam', recon) <- simplifyLam lam
    ans <- emit $ Hof $ RunIO lam'
    applyRecon recon ans
  CatchException lam -> do
    ~(Lam (Abs _ (_, body)), Nothing) <- simplifyLam lam
    dropSub $ exceptToMaybeBlock body
  where
    applyRecon Nothing x = return x
    applyRecon (Just f) x = f x

exceptToMaybeBlock :: Block -> SubstBuilder Atom
exceptToMaybeBlock (Block Empty result) = exceptToMaybeExpr result
exceptToMaybeBlock (Block (Nest (Let _ b expr) decls) result) = do
  a <- substBuilderR $ getType result
  maybeResult <- exceptToMaybeExpr expr
  case maybeResult of
    -- These two cases are just an optimization
    JustAtom _ x  -> extendR (b@> SubstVal x) $ exceptToMaybeBlock $ Block decls result
    NothingAtom _ -> return $ NothingAtom a
    _ -> do
      emitMaybeCase maybeResult (return $ NothingAtom a) \x -> do
        extendR (b@> SubstVal x) $ exceptToMaybeBlock $ Block decls result

exceptToMaybeExpr :: Expr -> SubstBuilder Atom
exceptToMaybeExpr expr = do
  a <- substBuilderR $ getType expr
  case expr of
    Case e alts resultTy -> do
      e' <- substBuilderR e
      resultTy' <- substBuilderR $ MaybeTy resultTy
      alts' <- forM alts \(Abs bs body) -> do
        bs' <-  substBuilderR bs
        buildNAbs bs' \xs -> extendR (newEnv bs' (map SubstVal xs)) $ exceptToMaybeBlock body
      emit $ Case e' alts' resultTy'
    Atom x -> substBuilderR $ JustAtom (getType x) x
    Op (ThrowException _) -> return $ NothingAtom a
    Hof (For ann ~(Lam (Abs b (_, body)))) -> do
      b' <- substBuilderR b
      maybes <- buildForAnn ann b' \i -> extendR (b@> SubstVal i) $ exceptToMaybeBlock body
      simplifyBuilder $ catMaybesE maybes
    Hof (RunState s lam) -> do
      s' <- substBuilderR s
      let BinaryFunVal _ b _ body = lam
      result  <- emitRunState "ref" s' \ref ->
        extendR (b@> SubstVal ref) $ exceptToMaybeBlock body
      (maybeAns, newState) <- fromPair result
      emitMaybeCase maybeAns (return $ NothingAtom a) \ans ->
        return $ JustAtom a $ PairVal ans newState
    Hof (RunWriter baseMonoid lam) -> do
      let BinaryFunVal _ b _ body = lam
      let RefTy _ accumTy = binderAnn b
      result  <- emitRunWriter "ref" accumTy baseMonoid \ref ->
        extendR (b@>SubstVal ref) $ exceptToMaybeBlock body
      (maybeAns, accumResult) <- fromPair result
      emitMaybeCase maybeAns (return $ NothingAtom a) \ans ->
        return $ JustAtom a $ PairVal ans accumResult
    Hof (While ~(Lam (Abs _ (_, body)))) -> do
      eff <- getAllowedEffects
      lam <- buildLam (Ignore UnitTy) (PlainArrow eff) \_ ->
               exceptToMaybeBlock body
      simplifyBuilder $ runMaybeWhile lam
    _ | not (hasExceptions expr) -> do
          x <- substBuilderR expr >>= emit
          return $ JustAtom (getType x) x
      | otherwise ->
          error $ "Unexpected exception-throwing expression: " ++ pprint expr

hasExceptions :: Expr -> Bool
hasExceptions expr = case t of
  Nothing -> ExceptionEffect `S.member` effs
  Just _  -> error "Shouldn't have tail left"
  where (EffectRow effs t) = exprEffs expr

simplifyBuilder :: MonadBuilder m => m Atom -> m Atom
simplifyBuilder m = do
  block <- buildScoped m
  liftBuilder $ runReaderT (simplifyBlock block) mempty
