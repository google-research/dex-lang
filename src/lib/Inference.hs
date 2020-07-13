-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module Inference (inferModule, synthModule) where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Except hiding (Except)
import Data.Foldable (fold, toList, asum)
import Data.Functor
import Data.String (fromString)
import Data.Text.Prettyprint.Doc

import Syntax
import Embed  hiding (sub)
import Env
import Type
import PPrint
import Cat

type UInferM = ReaderT SubstEnv (EmbedT (SolverT (Either Err)))

type SigmaType = Type  -- may     start with an implicit lambda
type RhoType   = Type  -- doesn't start with an implicit lambda
data RequiredTy a = Check a | Infer

inferModule :: TopEnv -> UModule -> Except Module
inferModule scope (UModule decls) = do
  ((), (bindings, decls')) <- runUInferM mempty scope $
                                mapM_ (inferUDecl True) decls
  let bindings' = envFilter bindings $ \(_, b) -> case b of
                    DataBoundTyCon _ -> True
                    DataBoundDataCon -> True
                    _ -> False
  return $ Module Typed decls' bindings'

runUInferM :: (HasVars a, Pretty a)
           => SubstEnv -> Scope -> UInferM a -> Except (a, (Scope, [Decl]))
runUInferM env scope m = runSolverT $ runEmbedT (runReaderT m env) scope

checkSigma :: UExpr -> SigmaType -> UInferM Atom
checkSigma expr sTy = case sTy of
  Pi piTy@(Abs _ (arrow, _))
    | arrow `elem` [ImplicitArrow, ClassArrow] -> case expr of
        WithSrc _ (ULam b arrow' body) | arrow' == void arrow ->
          checkULam b body piTy
        _ -> do
          buildLam ("a":> absArgType piTy) arrow $ \x@(Var v) ->
            checkLeaks [v] $ checkSigma expr $ snd $ applyAbs piTy x
  _ -> checkRho expr sTy

inferSigma :: UExpr -> UInferM Atom
inferSigma (WithSrc pos expr) = case expr of
  ULam pat ImplicitArrow body -> addSrcContext (Just pos) $
    inferULam pat ImplicitArrow body
  _ ->
    inferRho (WithSrc pos expr)

checkRho :: UExpr -> RhoType -> UInferM Atom
checkRho expr ty = checkOrInferRho expr (Check ty)

inferRho :: UExpr -> UInferM Atom
inferRho expr = checkOrInferRho expr Infer

instantiateSigma :: Atom -> UInferM Atom
instantiateSigma f = case getType f of
  Pi (Abs (_:>ty) (ImplicitArrow, _)) -> do
    x <- freshType ty
    ans <- emitZonked $ App f x
    instantiateSigma ans
  Pi (Abs (_:>ty) (ClassArrow, _)) ->
    instantiateSigma =<< emitZonked (App f (Con $ ClassDictHole ty))
  _ -> return f

checkOrInferRho :: UExpr -> RequiredTy RhoType -> UInferM Atom
checkOrInferRho (WithSrc pos expr) reqTy =
 addSrcContext (Just pos) $ case expr of
  UVar v -> lookupSourceVar v >>= instantiateSigma >>= matchRequirement
  ULam (p, ann) ImplicitArrow body -> do
    argTy <- checkAnn ann
    x <- freshType argTy
    withBindPat p x $ checkOrInferRho body reqTy
  ULam b arr body -> case reqTy of
    Check ty -> do
      piTy@(Abs _ (arrReq, _)) <- fromPiType False arr ty
      checkArrow arrReq arr
      checkULam b body piTy
    Infer -> inferULam b (fmap (const Pure) arr) body
  UFor dir b body -> case reqTy of
    Check ty -> do
      Abs n (arr, a) <- fromPiType False TabArrow ty
      unless (arr == TabArrow) $
        throw TypeErr $ "Not an table arrow type: " ++ pprint arr
      allowedEff <- getAllowedEffects
      lam <- checkULam b body $ Abs n (PlainArrow allowedEff, a)
      emitZonked $ Hof $ For dir lam
    Infer -> do
      allowedEff <- getAllowedEffects
      lam <- inferULam b (PlainArrow allowedEff) body
      emitZonked $ Hof $ For dir lam
  UApp arr f x -> do
    fVal <- inferRho f
    fVal' <- zonk fVal
    piTy <- addSrcContext (Just (srcPos f)) $ fromPiType True arr $ getType fVal'
    -- Zonking twice! Once for linearity and once for the embedding. Not ideal...
    fVal'' <- zonk fVal
    xVal <- checkSigma x (absArgType piTy)
    (arr', xVal') <- case piTy of
      Abs (NoName:>_) (arr', _) -> return (arr', xVal)
      _ -> do
        scope <- getScope
        let xVal' = reduceAtom scope xVal
        return (fst $ applyAbs piTy xVal', xVal')
    addEffects $ arrowEff arr'
    appVal <- emitZonked $ App fVal'' xVal'
    instantiateSigma appVal >>= matchRequirement
  UPi (v:>a) arr ty -> do
    -- TODO: make sure there's no effect if it's an implicit or table arrow
    -- TODO: check leaks
    a'  <- checkUType a
    piTy <- buildPi (v:>a') $ \x -> extendR ((v:>())@>x) $
              (,) <$> mapM checkUEff arr <*> checkUType ty
    matchRequirement piTy
  UDecl decl body -> do
    env <- inferUDecl False decl
    extendR env $ checkOrInferRho body reqTy
  UCase e ~(alt:alts) -> do
    e' <- inferRho e
    let eTy = getType e'
    alt'@(Alt _ altBody) <- checkCaseAlt reqTy eTy alt
    alts' <- mapM (checkCaseAlt (Check (getType altBody)) eTy) alts
    emit $ Case e' $ alt' : alts'
  UTabCon xs ann -> inferTabCon xs ann >>= matchRequirement
  UIndexRange low high -> do
    n <- freshType TyKind
    low'  <- mapM (flip checkRho n) low
    high' <- mapM (flip checkRho n) high
    matchRequirement $ TC $ IndexRange n low' high'
  UHole -> case reqTy of
    Infer -> throw MiscErr "Can't infer type of hole"
    Check ty -> freshType ty
  UPrimExpr prim -> do
    prim' <- traverse lookupName prim
    val <- case prim' of
      TCExpr  e -> return $ TC e
      ConExpr e -> return $ Con e
      OpExpr  e -> emitZonked $ Op e
      HofExpr e -> emitZonked $ Hof e
    matchRequirement val
    where lookupName v = asks (! (v:>()))
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
      case envLookup scope (v':>()) of
        Just (ty, DataBoundTyCon _) -> return $ ConApp (v':>ty) []
        Just (ty, DataBoundDataCon) -> return $ ConApp (v':>ty) []
        Just (ty, _) -> return $ Var $ v':>ty
        Nothing -> throw UnboundVarErr $ pprint $ asGlobal $ varName v

unpackTopPat :: LetAnn -> UPat -> Expr -> UInferM ()
unpackTopPat letAnn (WithSrc _ pat) expr = case pat of
  PatBind (v:>()) -> do
    let v' = asGlobal v
    scope <- getScope
    when ((v':>()) `isin` scope) $ throw RepeatedVarErr $ pprint v'
    void $ emitTo v' letAnn expr
  PatUnit -> return () -- TODO: change if we allow effects at the top level
  PatPair p1 p2 -> do
    val  <- emit expr
    x1   <- lift $ getFst val
    x2   <- lift $ getSnd val
    unpackTopPat letAnn p1 (Atom x1)
    unpackTopPat letAnn p2 (Atom x2)

inferUDecl :: Bool -> UDecl -> UInferM SubstEnv
inferUDecl topLevel (ULet letAnn (p, ann) rhs) = do
  val <- case ann of
    Nothing -> inferSigma rhs
    Just ty -> checkUType ty >>= checkSigma rhs
  expr <- zonk $ Atom val
  if topLevel
    then unpackTopPat letAnn p expr $> mempty
    else do
      -- TODO: non-top-level annotations?
      val' <- withPatHint p $ emitAnn PlainLet expr
      bindPat p val'
inferUDecl True (UData tc dcs) = do
  -- TODO: check that the data constructors actually produce the right type
  -- TODO: check it's not recursive
  -- TODO: check mutual shadows
  tc' <- inferCon tc
  (dcs', _) <- embedScoped $ do
                 extendScope $ varBinding tc'
                 mapM inferCon dcs
  extendScope $ tc' @> (varType tc', DataBoundTyCon dcs')
  forM_ dcs' $ \dc -> extendScope $ dc @> (varType dc, DataBoundDataCon)
  return mempty
inferUDecl False (UData _ _) = error "data definitions should be top-level"

inferCon :: UAnnBinder -> UInferM Binder
inferCon (v:>ty) = (asGlobal v :>) <$> checkUType ty

inferULam :: UBinder -> Arrow -> UExpr -> UInferM Atom
inferULam (p, ann) arr body = do
  argTy <- checkAnn ann
  -- TODO: worry about binder appearing in arrow?
  buildLam (patNameHint p :> argTy) arr
    $ \x@(Var v) -> checkLeaks [v] $ withBindPat p x $ inferSigma body

checkULam :: UBinder -> UExpr -> PiType -> UInferM Atom
checkULam (p, ann) body piTy = do
  let argTy = absArgType piTy
  checkAnn ann >>= constrainEq argTy
  buildDepEffLam (patNameHint p :> argTy)
    ( \x -> return $ fst $ applyAbs piTy x)
    $ \x@(Var v) -> checkLeaks [v] $ withBindPat p x $
                      checkSigma body $ snd $ applyAbs piTy x

checkUEff :: EffectRow -> UInferM EffectRow
checkUEff (EffectRow effs t) = do
   effs' <- forM effs $ \(effName, region) -> (effName,) <$> lookupVarName TyKind region
   t'    <- forM t $ \tv -> lookupVarName EffKind tv
   return $ EffectRow effs' t'
   where
     lookupVarName :: Type -> Name -> UInferM Name
     lookupVarName ty v = do
       -- TODO: more graceful errors on error
       Var (v':>ty') <- asks (!(v:>()))
       constrainEq ty ty'
       return v'

checkCaseAlt :: RequiredTy RhoType -> Type -> UAlt -> UInferM Alt
checkCaseAlt reqTy scrutineeTy (UAlt (conName, vs) body) = do
  let conName' = asGlobal conName
  scope <- getScope
  conTy <- case envLookup scope (conName':>()) of
    Nothing -> throw UnboundVarErr $ pprint conName'
    Just (ty, DataBoundDataCon) -> return ty
    Just _ -> throw TypeErr $ "Not a data constructor: " ++ pprint conName'
  (patTy, bs) <- addBinderTypes conTy vs
  constrainEq scrutineeTy patTy
  buildAlt (conName':>conTy) bs $ \xs ->
    extendR (newEnv bs xs) $ checkOrInferRho body reqTy

addBinderTypes :: MonadError Err m => Type -> [Name] -> m (Type, [Var])
addBinderTypes ty [] = return (ty, mempty)
-- TODO: data constructors with dependent args
-- TODO: data constructors with implicit args
addBinderTypes (Pi (Abs (NoName:>a) (PureArrow, resultTy))) (v:vs) = do
  (ty, bs) <- addBinderTypes resultTy vs
  return (ty, (v:>a) : bs)
-- TODO: better error messages
bindAltBinders _ _ = error "Not implemented"

  -- TODO:
  --   * look at scrutinee type
  --   * bind binder names against con type recursively (and dependently)
  --   * eval body


withBindPat :: UPat -> Atom -> UInferM a -> UInferM a
withBindPat pat val m = do
  env <- bindPat pat val
  extendR env m

bindPat :: UPat -> Atom -> UInferM SubstEnv
bindPat pat val = evalCatT $ bindPat' pat val

bindPat' :: UPat -> Atom -> CatT (Env ()) UInferM SubstEnv
bindPat' (WithSrc pos pat) val = addSrcContext (Just pos) $ case pat of
  PatBind b -> do
    usedVars <- look
    when (b `isin` usedVars) $ throw RepeatedVarErr $ pprint (varName b)
    extend (b@>())
    return (b @> val)
  PatUnit -> do
    lift $ constrainEq UnitTy (getType val)
    return mempty
  PatPair p1 p2 -> do
    _    <- lift $ fromPairType (getType val)
    val' <- lift $ zonk val  -- ensure it has a pair type before unpacking
    x1   <- lift $ getFst val'
    x2   <- lift $ getSnd val'
    env1 <- bindPat' p1 x1
    env2 <- bindPat' p2 x2
    return $ env1 <> env2

patNameHint :: UPat -> Name
patNameHint (WithSrc _ (PatBind (v:>()))) = v
patNameHint _ = "pat"

withPatHint :: UPat -> UInferM a -> UInferM a
withPatHint p m = withNameHint (patNameHint p) m

checkAnn :: Maybe UType -> UInferM Type
checkAnn ann = case ann of
  Just ty -> checkUType ty
  Nothing -> freshType TyKind

checkUType :: UType -> UInferM Type
checkUType ty = do
  reduced <- reduceScoped $ withEffects Pure $ checkRho ty TyKind
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

inferTabCon :: [UExpr] -> Maybe UType -> UInferM Atom
inferTabCon xs ann = do
  (n, ty) <- inferTabTy xs ann
  let tabTy = n==>ty
  xs' <- mapM (flip checkRho ty) xs
  emitZonked $ Op $ TabCon tabTy xs'

inferTabTy :: [UExpr] -> Maybe UType -> UInferM (Type, Type)
inferTabTy xs ann = case ann of
  Just ty -> do
    ty' <- checkUType ty
    case ty' of
      TabTy v a -> do
        unless (indexSetConcreteSize (varType v) == Just (length xs)) $
           throw TypeErr $ "Table size doesn't match annotation"
        return (varType v, a)
      _ -> throw TypeErr $ "Table constructor annotation must be a table type"
  Nothing -> case xs of
   [] -> throw TypeErr $ "Empty table constructor must have type annotation"
   (x:_) -> do
    ty <- getType <$> inferRho x
    return (FixedIntRange 0 (length xs), ty)

-- Bool flag is just to tweak the reported error message
fromPiType :: Bool -> UArrow -> Type -> UInferM PiType
fromPiType _ _ (Pi piTy) = return piTy -- TODO: check arrow
fromPiType expectPi arr ty = do
  a <- freshType TyKind
  b <- freshType TyKind
  let piTy = Abs (NoName:>a) (fmap (const Pure) arr, b)
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
  eff' <- openEffectRow eff
  allowedEffects <- getAllowedEffects
  constrainEq (Eff allowedEffects) (Eff eff')

openEffectRow :: EffectRow -> UInferM EffectRow
openEffectRow (EffectRow effs Nothing) = extendEffRow effs <$> freshEff
openEffectRow effRow = return effRow

-- === typeclass dictionary synthesizer ===

-- We have two variants here because at the top level we want error messages and
-- internally we want to consider all alternatives.
type SynthPassM = SubstEmbedT (Either Err)
type SynthDictM = SubstEmbedT []

synthModule :: Scope -> Module -> Except Module
synthModule scope (Module Typed decls bindings) = do
  decls' <- fst <$> runSubstEmbedT
              (traverseDecls (traverseHoles synthDictTop) decls) scope
  return $ Module Core decls' bindings
synthModule _ _ = error $ "Unexpected IR variant"

synthDictTop :: Type -> SynthPassM Atom
synthDictTop ty = do
  scope <- getScope
  let solutions = runSubstEmbedT (synthDict ty) scope
  case solutions of
    [] -> throw TypeErr $ "Couldn't synthesize a class dictionary for: " ++ pprint ty
    [(ans, env)] -> embedExtend env $> ans
    _ -> throw TypeErr $ "Multiple candidate class dictionaries for: " ++ pprint ty
           ++ "\n" ++ pprint solutions

traverseHoles :: (MonadReader SubstEnv m, MonadEmbed m)
              => (Type -> m Atom) -> TraversalDef m
traverseHoles fillHole = (traverseExpr recur, synthPassAtom)
  where
    synthPassAtom atom = case atom of
      Con (ClassDictHole ty) -> fillHole ty
      _ -> traverseAtom recur atom
    recur = traverseHoles fillHole

synthDict :: Type -> SynthDictM Atom
synthDict ty = do
  (d, bindingInfo) <- getBinding
  case bindingInfo of
    LetBound InstanceLet _ -> do
      block <- buildScoped $ inferToSynth $ instantiateAndCheck ty d
      traverseBlock (traverseHoles synthDict) block >>= emitBlock
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

inferToSynth :: (Pretty a, HasVars a) => UInferM a -> SynthDictM a
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
  Pi (Abs (_:>a) _) <- return $ getType f'
  constrainEq a (getType x)
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

runSolverT :: (MonadError Err m, HasVars a, Pretty a)
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
  forM_ (envPairs vs) $ \(v, k) -> case k of
    EffKind -> addSub v $ Eff Pure
    _ -> return ()
  where addSub v ty = extend $ SolverEnv mempty ((v:>()) @> ty)

solveLocal :: HasVars a => UInferM a -> UInferM a
solveLocal m = do
  (ans, env@(SolverEnv freshVars sub)) <- scoped $ do
    -- This might get expensive. TODO: revisit once we can measure performance.
    (ans, embedEnv) <- zonk =<< embedScoped m
    embedExtend embedEnv
    return ans
  extend $ SolverEnv (unsolved env) (sub `envDiff` freshVars)
  return ans

checkLeaks :: HasVars a => [Var] -> UInferM a -> UInferM a
checkLeaks tvs m = do
  (ans, env) <- scoped $ solveLocal $ m
  forM_ (solverSub env) $ \ty ->
    forM_ tvs $ \tv ->
      throwIf (tv `occursIn` ty) TypeErr $ "Leaked type variable: " ++ pprint tv
  extend env
  return ans

unsolved :: SolverEnv -> Env Kind
unsolved (SolverEnv vs sub) = vs `envDiff` sub

freshType :: Kind -> UInferM Type
freshType EffKind = Eff <$> freshEff
freshType k = do
  tv <- freshVar k
  extend $ SolverEnv (tv @> k) mempty
  extendScope $ tv @> (k, UnknownBinder)
  return $ Var tv

freshEff :: (MonadError Err m, MonadCat SolverEnv m) => m EffectRow
freshEff = do
  v <- freshVar ()
  extend $ SolverEnv (v@>EffKind) mempty
  return $ EffectRow [] $ Just $ varName v

freshVar :: MonadCat SolverEnv m => ann -> m (VarP ann)
freshVar ann = looks $ rename (rawName InferenceName "?" :> ann) . solverVars

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

zonk :: (HasVars a, MonadCat SolverEnv m) => a -> m a
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
    (TC con, TC con') | void con == void con' ->
      zipWithM_ unify (toList con) (toList con')
    (Eff eff, Eff eff') -> unifyEff eff eff'
    _ -> throw TypeErr ""

unifyEff :: (MonadCat SolverEnv m, MonadError Err m)
         => EffectRow -> EffectRow -> m ()
unifyEff r1 r2 = do
  r1' <- zonk r1
  r2' <- zonk r2
  vs <- looks solverVars
  case (r1', r2') of
    _ | r1 == r2 -> return ()
    (r, EffectRow [] (Just v)) | (v:>()) `isin` vs -> bindQ (v:>EffKind) (Eff r)
    (EffectRow [] (Just v), r) | (v:>()) `isin` vs -> bindQ (v:>EffKind) (Eff r)
    (EffectRow effs1@(_:_) t1, EffectRow effs2@(_:_) t2) -> do
      let extras1 = effs1 `setDiff` effs2
      let extras2 = effs2 `setDiff` effs1
      newRow <- freshEff
      unifyEff (EffectRow [] t1) (extendEffRow extras2 newRow)
      unifyEff (extendEffRow extras1 newRow) (EffectRow [] t2)
    _ -> throw TypeErr ""

setDiff :: Eq a => [a] -> [a] -> [a]
setDiff xs ys = filter (`notElem` ys) xs

bindQ :: (MonadCat SolverEnv m, MonadError Err m) => Var -> Type -> m ()
bindQ v t | v `occursIn` t = throw TypeErr $ "Occurs check failure: " ++ pprint (v, t)
          | hasSkolems t = throw TypeErr "Can't unify with skolem vars"
          | otherwise = extend $ mempty { solverSub = v @> t }

hasSkolems :: HasVars a => a -> Bool
hasSkolems x = not $ null [() | Name Skolem _ _ <- envNames $ freeVars x]

occursIn :: HasVars a => Var -> a -> Bool
occursIn v t = v `isin` freeVars t

renameForPrinting :: HasVars a => a -> (a, [Var])
renameForPrinting x = (scopelessSubst substEnv x, newNames)
  where
    fvs = freeVars x
    infVars = filter ((==InferenceName) . nameSpace . varName) $ envAsVars fvs
    newNames = [ rename (fromString name:> fst (varAnn v)) fvs
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
