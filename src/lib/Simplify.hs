-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}

module Simplify (simplifyModule, simplifyCase, splitSimpModule) where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.Reader
import Data.Maybe
import Data.Foldable (toList)
import Data.Functor
import Data.List (partition, elemIndex)
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M

import Autodiff
import Env
import Syntax
import Cat
import Embed
import Type
import PPrint
import Util

type SimplifyM = SubstEmbedT Identity

simplifyModule :: TopEnv -> Module -> Module
simplifyModule scope (Module Core decls bindings) = do
  let simpDecls = snd $ snd $ runSubstEmbed (simplifyDecls decls) scope
  -- We don't have to check that the binders are global here, since all local
  -- Atom binders have been inlined as part of the simplification.
  let isAtomDecl decl = case decl of Let _ _ (Atom _) -> True; _ -> False
  let (declsDone, declsNotDone) = partition isAtomDecl $ toList simpDecls
  let bindings' = foldMap boundVars declsDone
  Module Simp (toNest declsNotDone) (bindings <> bindings')
simplifyModule _ (Module ir _ _) = error $ "Expected Core, got: " ++ show ir

splitSimpModule :: TopEnv -> Module -> (Block, Abs Binder Module)
splitSimpModule scope m = do
  let (Module Simp decls bindings) = hoistDepDataCons scope m
  let localVars = filter (not . isGlobal) $ bindingsAsVars $ freeVars bindings
  let block = Block decls $ Atom $ mkConsList $ map Var localVars
  let (Abs b (decls', bindings')) =
        fst $ flip runEmbed scope $ buildAbs (Bind ("result":>getType block)) $
          \result -> do
             results <- unpackConsList result
             substEmbed (newEnv localVars results) bindings
  (block, Abs b (Module Evaluated decls' bindings'))

-- Bundling up the free vars in a result with a dependent constructor like
-- `AsList n xs` doesn't give us a well typed term. This is a short-term
-- workaround.
hoistDepDataCons :: TopEnv -> Module -> Module
hoistDepDataCons scope (Module Simp decls bindings) =
  Module Simp decls' bindings'
  where
    (bindings', (_, decls')) = flip runEmbed scope $ do
      mapM_ emitDecl decls
      forM bindings $ \(ty, info) -> case info of
        LetBound ann x | isData ty -> do x' <- emit x
                                         return (ty, LetBound ann $ Atom x')
        _ -> return (ty, info)
hoistDepDataCons _ (Module _ _ _) =
  error "Should only be hoisting data cons on core-Simp IR"

simplifyDecls :: Nest Decl -> SimplifyM SubstEnv
simplifyDecls Empty = return mempty
simplifyDecls (Nest decl rest) = do
  substEnv <- simplifyDecl decl
  substEnv' <- extendR substEnv $ simplifyDecls rest
  return (substEnv <> substEnv')

simplifyDecl :: Decl -> SimplifyM SubstEnv
simplifyDecl (Let ann b expr) = do
  x <- simplifyExpr expr
  let name = binderNameHint b
  if isGlobalBinder b
    then emitTo name ann (Atom x) $> mempty
    else return $ b @> x
simplifyDecl (Unpack bs expr) = do
  x <- simplifyExpr expr
  xs <- case x of
    DataCon _ _ _ xs -> return xs
    Record items -> return $ toList items
    _ -> emitUnpack $ Atom x
  return $ newEnv bs xs

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
      Just x -> return $ deShadow x scope
      Nothing -> case envLookup scope v of
        Just (_, info) -> case info of
          LetBound _ (Atom x) -> dropSub $ simplifyAtom x
          _ -> substEmbedR atom
        _   -> substEmbedR atom
  -- Tables that only contain data aren't necessarily getting inlined,
  -- so this might be the last chance to simplify them.
  TabVal _ _ -> do
    case isData (getType atom) of
      True -> do
        ~(tab', Nothing) <- simplifyLam atom
        return tab'
      False -> substEmbedR atom
  -- We don't simplify body of lam because we'll beta-reduce it soon.
  Lam _ -> substEmbedR atom
  Pi  _ -> substEmbedR atom
  Con con -> Con <$> mapM simplifyAtom con
  TC tc -> TC <$> mapM substEmbedR tc
  Eff eff -> Eff <$> substEmbedR eff
  TypeCon def params          -> TypeCon def <$> substEmbedR params
  DataCon def params con args -> DataCon def <$> substEmbedR params
                                             <*> pure con <*> mapM simplifyAtom args
  Record items -> Record <$> mapM simplifyAtom items
  RecordTy items -> RecordTy <$> substEmbedR items
  Variant types label i value -> Variant <$>
    substEmbedR types <*> pure label <*> pure i <*> simplifyAtom value
  VariantTy items -> VariantTy <$> substEmbedR items
  LabeledRow items -> LabeledRow <$> substEmbedR items
  ACase e alts rty   -> do
    e' <- substEmbedR e
    case simplifyCase e' alts of
      Just (env, result) -> extendR env $ simplifyAtom result
      Nothing -> do
        alts' <- forM alts $ \(Abs bs a) -> do
          bs' <- mapM (mapM substEmbedR) bs
          (Abs bs'' b) <- buildNAbs bs' $ \xs -> extendR (newEnv bs' xs) $ simplifyAtom a
          case b of
            Block Empty (Atom r) -> return $ Abs bs'' r
            _                    -> error $ "Nontrivial block in ACase simplification"
        ACase e' alts' <$> (substEmbedR rty)
  DataConRef _ _ _ -> error "Should only occur in Imp lowering"
  BoxedRef _ _ _ _ -> error "Should only occur in Imp lowering"
  ProjectElt idxs v -> reduceProjection (toList idxs) <$> simplifyAtom (Var v)

simplifyCase :: Atom -> [AltP a] -> Maybe (SubstEnv, a)
simplifyCase e alts = case e of
  DataCon _ _ con args -> do
    let Abs bs result = alts !! con
    Just (newEnv bs args, result)
  Variant (NoExt types) label i value -> do
    let LabeledItems ixtypes = enumerate types
    let index = fst $ (ixtypes M.! label) NE.!! i
    let Abs bs result = alts !! index
    Just (newEnv bs [value], result)
  Con (SumAsProd _ (TagRepVal tag) vals) -> do
    let Abs bs result = alts !! (fromIntegral tag)
    Just (newEnv bs (vals !! fromIntegral tag), result)
  _ -> Nothing

-- `Nothing` is equivalent to `Just return` but we can pattern-match on it
type Reconstruct m a = Maybe (a -> m a)

simplifyLam :: Atom -> SimplifyM (Atom, Reconstruct SimplifyM Atom)
simplifyLam = simplifyLams 1

simplifyBinaryLam :: Atom -> SimplifyM (Atom, Reconstruct SimplifyM Atom)
simplifyBinaryLam = simplifyLams 2

-- Unlike `substEmbedR`, this simplifies under the binder too.
simplifyLams :: Int -> Atom -> SimplifyM (Atom, Reconstruct SimplifyM Atom)
simplifyLams numArgs lam = do
  lam' <- substEmbedR lam
  dropSub $ go numArgs mempty $ Block Empty $ Atom lam'
  where
    go 0 scope block = do
      result <- defunBlock scope block
      return $ case result of
        Left  res -> (res, Nothing)
        Right (dat, (ctx, recon), atomf) ->
          ( mkConsList $ (toList dat) ++ (toList ctx)
          , Just $ \vals -> do
             (datEls', ctxEls') <- splitAt (length dat) <$> unpackConsList vals
             let dat' = restructure datEls' dat
             let ctx' = restructure ctxEls' ctx
             atomf dat' <$> recon dat' ctx'
          )
    go n scope ~(Block Empty (Atom (Lam (Abs b (arr, body))))) = do
      b' <- mapM substEmbedR b
      buildLamAux b' (\x -> extendR (b@>x) $ substEmbedR arr) $ \x@(Var v) -> do
        let scope' = scope <> v @> (varType v, LamBound (void arr))
        extendR (b@>x) $ go (n-1) scope' body

defunBlock :: Scope -> Block -> SimplifyM (Either Atom (AtomFac SimplifyM))
defunBlock localScope block = do
  if isData (getType block)
    then Left <$> simplifyBlock block
    else do
      (result, (localScope', decls)) <- embedScoped $ simplifyBlock block
      mapM_ emitDecl decls
      Right <$> separateDataComponent (localScope <> localScope') result

data RTree a = RNode [RTree a] | RLeaf a
               deriving (Functor, Foldable, Traversable)

pattern RNil :: RTree a
pattern RNil = RNode []

-- Factorization of the atom into data and non-data components
-- TODO: Make the non-linear reconstruction take the scope instead of being monadic
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
separateDataComponent :: forall m. MonadEmbed m => Scope -> Atom -> m (AtomFac m)
separateDataComponent localVars v = do
  (dat, (ctx, recon), atomf) <- rec v
  let (ctx', ctxRec) = dedup dat ctx
  let recon' = \dat'' ctx'' -> recon $ ctxRec dat'' (toList ctx'')
  return (dat, (RNode $ fmap RLeaf ctx', recon'), atomf)
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
                return $ RLeaf $ subst (newEnv vs xs, scope) atom
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
        inv ctx' result' = for ll $ \x -> case elemIndex x (toList ctx) of
          Just i  -> (toList ctx') !! i
          Nothing -> result' !! (fromJust $ elemIndex x result)


simplifyExpr :: Expr -> SimplifyM Atom
simplifyExpr expr = case expr of
  App f x -> do
    x' <- simplifyAtom x
    f' <- simplifyAtom f
    case f' of
      Lam (Abs b (_, body)) ->
        dropSub $ extendR (b@>x') $ simplifyBlock body
      DataCon def params con xs -> return $ DataCon def params' con xs'
         where DataDef _ paramBs _ = def
               (params', xs') = splitAt (length paramBs) $ params ++ xs ++ [x']
      ACase e alts ~(Pi ab) -> do
        let rty' = snd $ applyAbs ab $ getType x'
        case all isCurriedFun alts of
          True -> return $ ACase e (fmap appAlt alts) rty'
          False -> do
            let alts' = for alts $ \(Abs bs a) -> Abs bs $ Block Empty (App a x')
            dropSub $ simplifyExpr $ Case e alts' rty'
        where
          isCurriedFun alt = case alt of
            Abs _ (LamVal _ (Block Empty (Atom (LamVal _ _)))) -> True
            _ -> False
          appAlt ~(Abs bs (LamVal b (Block Empty (Atom r)))) =
            Abs bs $ subst (b @> x', mempty) r
      TypeCon def params -> return $ TypeCon def params'
         where params' = params ++ [x']
      _ -> emit $ App f' x'
  Op  op  -> mapM simplifyAtom op >>= simplifyOp
  Hof hof -> simplifyHof hof
  Atom x  -> simplifyAtom x
  Case e alts resultTy -> do
    e' <- simplifyAtom e
    resultTy' <- substEmbedR resultTy
    case simplifyCase e' alts of
      Just (env, body) -> extendR env $ simplifyBlock body
      Nothing -> do
        if isData resultTy'
          then do
            alts' <- forM alts $ \(Abs bs body) -> do
              bs' <-  mapM (mapM substEmbedR) bs
              buildNAbs bs' $ \xs -> extendR (newEnv bs' xs) $ simplifyBlock body
            emit $ Case e' alts' resultTy'
          else do
            -- Construct the blocks of new cases. The results will only get replaced
            -- later, once we learn the closures of the non-data component of each case.
            (alts', facs) <- liftM unzip $ forM alts $ \(Abs bs body) -> do
              bs' <-  mapM (mapM substEmbedR) bs
              buildNAbsAux bs' $ \xs -> do
                ~(Right fac@(dat, (ctx, _), _)) <- extendR (newEnv bs' xs) $ defunBlock (boundVars bs') body
                -- NB: The return value here doesn't really matter as we're going to replace it afterwards.
                return (mkConsList $ toList dat ++ toList ctx, fac)
            -- Now that we know the exact set of values each case needs, ctxDef is a sum type
            -- that can encapsulate the necessary contexts.
            -- TODO: Handle dependency once separateDataComponent supports it
            let altCtxTypes = fmap (\(_, (ctx, _), _) -> fmap getType $ toList ctx) facs
            let ctxDef = DataDef "CaseClosure" Empty $
                  fmap (DataConDef "Closure" . toNest . fmap Ignore) altCtxTypes
            -- New cases return a pair of data components, and a closure for non-data atoms
            let alts'' = for (enumerate $ zip alts' facs) $
                  \(i, (Abs bs (Block decls _), (dat, (ctx, _), _))) ->
                    Abs bs $ Block decls $ Atom $
                      PairVal (mkConsList $ toList dat) (DataCon ctxDef [] i $ toList ctx)
            -- Here, we emit the case expression and unpack the results. All the trees
            -- should be the same, so we just pick the first one.
            let (datType, datTree) = (\(dat, _, _) -> (getType $ mkConsList $ toList dat, dat)) $ head facs
            caseResult <- emit $ Case e' alts'' $ PairTy datType (TypeCon ctxDef [])
            (cdat, cctx) <- fromPair caseResult
            dat <- flip restructure datTree <$> unpackConsList cdat
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
            nondat <- forM (enumerate nondatTree) $ \(i, _) -> do
              aalts <- forM facs $ \(_, (ctx, rec), _) -> do
                Abs bs' b <- buildNAbs (toNest $ toList $ fmap (Ignore . getType) ctx) $ \ctxVals ->
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
  Fst (PairVal x _) -> return x
  Snd (PairVal _ y) -> return y
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
  _ -> emitOp op

simplifyHof :: Hof -> SimplifyM Atom
simplifyHof hof = case hof of
  For d lam -> do
    ~(lam'@(Lam (Abs i _)), recon) <- simplifyLam lam
    ans <- emit $ Hof $ For d lam'
    case recon of
      Nothing -> return ans
      Just f  -> buildLam i TabArrow $ \i' -> app ans i' >>= f
  Tile d fT fS -> do
    ~(fT', Nothing) <- simplifyLam fT
    ~(fS', Nothing) <- simplifyLam fS
    emit $ Hof $ Tile d fT' fS'
  PTileReduce _ _ -> error "Unexpected PTileReduce"
  While cond body -> do
    ~(cond', Nothing) <- simplifyLam cond
    ~(body', Nothing) <- simplifyLam body
    emit $ Hof $ While cond' body'
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
  RunWriter lam -> do
    ~(lam', recon) <- simplifyBinaryLam lam
    (ans, w) <- fromPair =<< (emit $ Hof $ RunWriter lam')
    ans' <- applyRecon recon ans
    return $ PairVal ans' w
  RunState s lam -> do
    s' <- simplifyAtom s
    ~(lam', recon) <- simplifyBinaryLam lam
    (ans, sOut) <- fromPair =<< (emit $ Hof $ RunState s' lam')
    ans' <- applyRecon recon ans
    return $ PairVal ans' sOut
  where
    applyRecon Nothing x = return x
    applyRecon (Just f) x = f x
