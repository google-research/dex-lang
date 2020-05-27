-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

module Inference (inferModule, inferUModule) where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Except hiding (Except)
import Data.Foldable (toList, fold)
import qualified Data.Map.Strict as M
import Data.Text.Prettyprint.Doc

import Syntax
import Embed  hiding (sub)
import Env
import Record
import Type
import PPrint
import Cat
import Subst

-- TODO: consider just carrying an `Atom` (since the type is easily recovered)
type InfEnv = Env (Atom, Type)
type UInferM = ReaderT InfEnv (EmbedT (SolverT (Either Err)))

type SigmaType = Type  -- may     start with an implicit lambda
type RhoType   = Type  -- doesn't start with an implicit lambda
data RequiredTy a = Check a | Infer
data InferredTy a = Checked | Inferred a

inferUModule :: TopEnv -> UModule -> Except (Module, TopInfEnv)
inferUModule topEnv (UModule imports exports decls) = do
  let env = infEnvFromTopEnv topEnv
  (env', decls') <- runUInferM (inferUDecls noEffect decls) env
  let combinedEnv = env <> env'
  let imports' = [v :> snd (env         ! (v:>())) | v <- imports]
  let exports' = [v :> snd (combinedEnv ! (v:>())) | v <- exports]
  let resultVals = [fst    (combinedEnv ! (v:>())) | v <- exports]
  let body = wrapDecls decls' $ TupVal resultVals
  return (Module Nothing (imports', exports') body, (fmap snd env', mempty))

runUInferM :: (TySubst a, Pretty a) => UInferM a -> InfEnv -> Except (a, [Decl])
runUInferM m env = runSolverT $ runEmbedT (runReaderT m env) scope
  where scope = fmap (const ()) env

infEnvFromTopEnv :: TopEnv -> InfEnv
infEnvFromTopEnv (TopEnv (tyEnv, _) substEnv _) =
  fold [v' @> (substEnv ! v', ty) | (v, ty) <- envPairs tyEnv, let v' = v:>()]

-- TODO: think about effects
checkSigma :: UExpr -> Effect -> SigmaType -> UInferM Atom
checkSigma expr eff ty = case ty of
  ArrowType im@(ImplicitArg _) _ piTy@(Pi a _) -> do
    lamExpr <- buildLamExpr ("a":>a) $ \x ->
                 checkSigma expr eff $ snd $ applyPi piTy x
    return $ Con $ Lam im NonLin noEffect lamExpr
  _ -> checkRho expr eff ty

inferSigma :: UExpr -> Effect -> UInferM (Atom, SigmaType)
inferSigma (ULam im@(ImplicitArg _) lamExpr) _ = do
  -- TODO: effects
  (lamExpr, piTy) <- inferULam lamExpr
  let lam = Con $ Lam im NonLin noEffect lamExpr
  return (lam, ArrowType im NonLin piTy)
inferSigma expr eff = inferRho expr eff

checkRho :: UExpr -> Effect -> RhoType -> UInferM Atom
checkRho expr eff ty = do
  (val, Checked) <- checkOrInferRho expr eff (Check ty)
  return val

inferRho :: UExpr -> Effect -> UInferM (Atom, RhoType)
inferRho expr eff = do
  (val, Inferred ty) <- checkOrInferRho expr eff Infer
  return (val, ty)

-- This is necessary so that embed's `getType` doesn't get confused
-- TODO: figure out a better way. It's probably enough to just solve locally as
-- part of leak checking when we construct dependent lambdas.
emitZonked :: CExpr -> UInferM Atom
emitZonked expr = zonk expr >>= emit

instantiateSigma :: (Atom, SigmaType) -> UInferM (Atom, RhoType)
instantiateSigma (f,  ArrowType (ImplicitArg _) _ piTy@(Pi argTy _)) = do
  x <- freshInfVar argTy
  ans <- emitZonked $ App NonLin f x
  let (_, ansTy) = applyPi piTy x
  return (ans, ansTy)
instantiateSigma (x, ty) = return (x, ty)

checkOrInferRho :: UExpr -> Effect -> RequiredTy RhoType
                -> UInferM (Atom, InferredTy RhoType)
checkOrInferRho expr eff reqTy = case expr of
  UVar v -> asks (! v) >>= instantiateSigma >>= matchRequirement
  ULam (ImplicitArg _) (ULamExpr (RecLeaf b) body) -> do
    argTy <- checkAnn $ varAnn b
    x <- freshInfVar argTy
    extendR (b@>(x, argTy)) $ checkOrInferRho body eff reqTy
  ULam Expl lamExpr -> case reqTy of
    -- TODO: effects
    Check ty -> do
      piTy <- fromPiType ty
      lamExpr' <- checkULam lamExpr piTy
      let lam = Con $ Lam Expl NonLin noEffect lamExpr'
      return (lam, Checked)
    Infer -> do
      (lamExpr', piTy) <- inferULam lamExpr
      let lam = Con $ Lam Expl NonLin noEffect lamExpr'
      return (lam, Inferred $ ArrowType Expl NonLin piTy)
  UApp f x -> do
    (fVal, fTy) <- inferRho f eff
    piTy@(Pi argTy _) <- fromPiType fTy
    xVal <- checkSigma x eff argTy
    let (appEff, appTy) = applyPi piTy xVal
    checkEffect eff appEff
    appVal <- emitZonked $ App NonLin fVal xVal
    instantiateSigma (appVal, appTy) >>= matchRequirement
  UArrow im (UPi (v:>a) b) -> do
    -- TODO: make sure there's no effect if it's an implicit arrow
    a' <- checkUType a
    -- TODO: freshen as we go under the binder
    b' <- extendR ((v:>())@>(Var (v:>a'), a')) $ checkUType b
    let piTy = ArrowType im NonLin $ makePi (v:>a') (noEffect, b')
    matchRequirement (piTy, TyKind)
  UDecl decl body -> do
    env <- inferUDecl eff decl
    extendR env $ checkOrInferRho body eff reqTy
  UPrimExpr prim -> do
    prim' <- traverseExpr prim lookupName lookupName (error "not implemented")
    val <- case prim' of
      OpExpr  op  -> emitZonked op
      ConExpr con -> return $ Con con
      TyExpr  con -> return $ TC con
    matchRequirement (val, getType val)
    where lookupName v = fst <$> asks (! (v:>()))
  UAnnot e ty -> do
    ty' <- checkUType ty
    val <- checkSigma e eff ty'
    matchRequirement (val, ty')
  where
    matchRequirement :: (Atom, Type) -> UInferM (Atom, InferredTy RhoType)
    matchRequirement (x, ty) = liftM (x,) $
      case reqTy of
        Infer -> return $ Inferred ty
        Check req -> do
          constrainEq req ty ""
          return Checked

inferUDecl :: Effect -> UDecl -> UInferM InfEnv
inferUDecl eff (ULet (RecLeaf b@(_:>ann)) rhs) = case ann of
  Nothing -> do
    valAndTy <- inferSigma rhs eff
    return $ b@>valAndTy
  Just ty -> do
    ty' <- checkUType ty
    val <- checkSigma rhs eff ty'
    return $ b@>(val, ty')

inferUDecls :: Effect -> [UDecl] -> UInferM InfEnv
inferUDecls eff decls = do
  initEnv <- ask
  liftM snd $ flip runCatT initEnv $ forM_ decls $ \decl -> do
    cur <- look
    new <- lift $ local (const cur) $ inferUDecl eff decl
    extend new

inferULam :: ULamExpr -> UInferM (LamExpr, PiType EffectiveType)
inferULam (ULamExpr (RecLeaf b@(v:>ann)) body) = do
  argTy <- checkAnn ann
  buildLamExprAux (v:>argTy) $ \x@(Var v') -> do
    extendR (b @> (x, argTy)) $ do
      (resultVal, resultTy) <- inferRho body noEffect
      return (resultVal, makePi v' (noEffect, resultTy))

checkULam :: ULamExpr -> PiType EffectiveType -> UInferM LamExpr
checkULam (ULamExpr (RecLeaf b@(v:>ann)) body) piTy@(Pi argTy' _) = do
  argTy <- checkAnn ann
  constrainEq argTy' argTy "Lambda binder"
  buildLamExpr (v:>argTy) $ \x -> do
    let (lamEff, resultTy) = applyPi piTy x
    extendR (b @> (x, argTy')) $ do
      resultVal <- checkSigma body lamEff resultTy
      return resultVal

fromPiType :: Type -> UInferM (PiType EffectiveType)
fromPiType (ArrowType _ _ piTy) = return piTy
fromPiType ty = error $ "Not a pi type: " ++ pprint ty

checkAnn :: Maybe UType -> UInferM Type
checkAnn ann = case ann of
  Just ty -> checkUType ty
  Nothing -> freshInfVar TyKind

checkUType :: UType -> UInferM Type
checkUType ty = checkRho ty noEffect TyKind

checkEffect :: Effect -> Effect -> UInferM ()
checkEffect allowedEff eff = do
  eff' <- openUEffect eff
  constrainEq allowedEff eff' ""

freshInfVar :: Type -> UInferM Atom
freshInfVar ty = do
  (tv:>()) <- looks $ rename (rawName InferenceName "?" :> ()) . solverVars
  extend $ SolverEnv ((tv:>()) @> TyKind) mempty
  return $ Var $ tv:>ty

openUEffect :: Effect -> UInferM Effect
openUEffect eff = return eff -- TODO!

type InferM = ReaderT JointTypeEnv (SolverT (Either Err))

inferModule :: TopInfEnv -> FModule -> Except (FModule, TopInfEnv)
inferModule (tyEnv, tySubEnv) m = do
  let (Module bid (imports, exports) body) = m
  checkImports tyEnv m
  (body', tySubEnvOut) <- expandTyAliases tySubEnv body
  (body'', tyEnvOut) <- runInferM tyEnv $
    catTraverse (inferDecl noEffect) fromNamedEnv body' tyEnv
  let tyEnvOut' = tyEnvOut <> fmap getKind tySubEnvOut
  let imports' = [addTopVarAnn tyEnv v
                 | v <- imports, not (v `isin` tySubEnv)]
  let exports' = [addTopVarAnn (tyEnv <> tyEnvOut') v
                 | v <- exports, not (v `isin` tySubEnvOut)]
  let m' = Module bid (imports', exports') body''
  return (m', (tyEnvOut', tySubEnvOut))

runInferM :: (TySubst a, Pretty a) => TypeEnv -> InferM a -> Except a
runInferM env m = runSolverT (runReaderT m (fromNamedEnv env))

expandTyAliases :: Env Type -> [FDecl] -> Except ([FDecl], Env Type)
expandTyAliases envInit decls =
  liftM snd $ flip runCatT ([], envInit) $ forM_ decls expandTyAliasDecl

expandTyAliasDecl :: FDecl -> CatT ([FDecl], Env Type) (Either Err) ()
expandTyAliasDecl decl = do
  env <- looks snd
  case decl of
    TyDef v ty -> do
      let ty' = tySubst env ty
      -- TODO: A type alias only has a type kind if it takes no arguments. This is
      --       incorrect and it only works, because we ignore the "expected kind"
      --       argument in the case for type aliases...
      ty'' <- liftEither $ runInferKinds mempty TyKind ty'
      extend ([], v @> ty'')
    _ -> extend ([tySubst env decl], mempty)

addTopVarAnn :: TypeEnv -> Var -> Var
addTopVarAnn env v = case envLookup env v of
  Just ann -> varName v :> ann
  Nothing -> error "Lookup of interface var failed"

checkImports :: TypeEnv -> FModule -> Except ()
checkImports env m  = do
  let unboundVars = envNames $ imports `envDiff` env
  unless (null unboundVars) $ throw UnboundVarErr $ pprintList unboundVars
  let shadowedVars = envNames $ exports `envIntersect` env
  unless (null shadowedVars) $ throw RepeatedVarErr $ pprintList shadowedVars
  where (imports, exports) = moduleType m

inferDecl :: Effect -> FDecl -> InferM (FDecl, TypeEnv)
inferDecl eff decl = case decl of
  LetMono p bound -> do
    -- TOOD: better errors - infer polymorphic type to suggest annotation
    p' <- checkPat p =<< freshQ
    bound' <- check bound (eff, getType p')
    return (LetMono p' bound', foldMap bind p')
  LetPoly b@(v:>ty) tlam -> do
    constrainEq eff noEffect (pprint decl)
    ty' <- inferKinds TyKind ty
    tlam' <- checkTLam ty' tlam
    return (LetPoly (v:>ty') tlam', b @> ty')
  TyDef _ _ -> error "Shouldn't have TyDef left"

check :: FExpr -> EffectiveType -> InferM FExpr
check expr reqEffTy@(allowedEff, reqTy) = case expr of
  FDecl decl body -> do
    (decl', env') <- inferDecl allowedEff decl
    body' <- extendNamed env' $ check body reqEffTy
    return $ FDecl decl' body'
  FVar v -> do
    ty <- asks $ flip jointEnvGet v
    case ty of
      Forall _ _ _ -> check (fTyApp v []) reqEffTy
      _ -> constrainReq ty >> return (FVar (varName v :> ty))
  FPrimExpr (OpExpr (TApp (FVar v) headTyArgs)) -> do
    ty <- asks $ flip jointEnvGet v
    case ty of
      Forall tyFormals _ body -> do
        let reqKinds = map varAnn tyFormals
        headTyArgs' <- zipWithM inferKinds reqKinds headTyArgs
        tailTyArgs <- mapM freshInferenceVar (drop (length headTyArgs) reqKinds)
        let tyArgs = headTyArgs' ++ tailTyArgs
        let env = newEnv tyFormals tyArgs
        constrainReq (subst (env, mempty) body)
        return $ fTyApp (varName v :> ty) tyArgs
      _ -> throw TypeErr "Unexpected type application"
  FPrimExpr (OpExpr (App l f x)) -> do
    l'  <- inferKinds (TC MultKind) l
    piTy@(Pi a _) <- freshLamType
    f' <- checkPure f $ ArrowType Expl l' piTy
    x' <- checkPure x a
    piTy' <- zonk piTy
    (eff, b) <- maybeApplyPi piTy' (fromAtomicFExpr x')
    constrainReq b
    eff' <- openEffect eff
    constrainEq allowedEff eff' (pprint expr)
    return $ FPrimExpr $ OpExpr $ App l' f' x'
  FPrimExpr (OpExpr (Inject e)) -> do
    et <- freshQ
    e' <- checkPure e et
    et' <- zonk et
    case et' of
      TC (IndexRange ty _ _) -> do
        constrainReq ty
        return $ FPrimExpr $ OpExpr $ Inject e'
      _ -> throw TypeErr "Expected index range"
  FPrimExpr (OpExpr op) -> do
    opTy <- generateOpSubExprTypes op
    -- TODO: don't ignore explicit annotations (via `snd`)
    (eff, ansTy) <- traverseOpType
                      (fmapExpr opTy id (\(e,t)->(fromAtomicFExpr e, t)) snd)
                      (\t1 t2 -> constrainEq t1 t2 (pprint expr))
                      (\_ _ -> return ())
                      (\_ _ -> return ())
    op' <- traverseExpr opTy return (uncurry checkPure) (uncurry checkLam)
    constrainReq ansTy
    eff' <- openEffect eff
    constrainEq allowedEff eff' (pprint expr)
    return $ FPrimExpr $ OpExpr $ op'
  FPrimExpr (ConExpr con) -> do
    conTy <- generateConSubExprTypes con
    -- TODO: don't ignore explicit annotations (via `snd`)
    ansTy <- traverseConType (fmapExpr conTy id snd snd)
               (\t1 t2 -> constrainEq t1 t2 (pprint expr))
               (\_ _ -> return ())
               (\_ _ -> return ())
    constrainReq ansTy
    con' <- traverseExpr conTy return (uncurry checkPure) (uncurry checkLam)
    return $ FPrimExpr $ ConExpr con'
  Annot e annTy -> do
    -- TODO: check that the annotation is a monotype
    constrainReq annTy
    check e reqEffTy
  SrcAnnot e pos -> do
    e' <- addSrcContext (Just pos) $ check e reqEffTy
    return $ SrcAnnot e' pos
  where
    constrainReq ty = constrainEq reqTy ty (pprint expr)

checkPure :: FExpr -> Type -> InferM FExpr
checkPure expr ty = check expr (noEffect, ty)

checkTLam :: Type -> FTLam -> InferM FTLam
checkTLam ~(Forall tbs qs tyBody) (FTLam _ _ tlamBody) = do
  let env = foldMap bind tbs
  liftM (FTLam tbs qs) $ checkLeaks tbs $ extendNamed env $
    check tlamBody (noEffect, tyBody)

checkLam :: FLamExpr -> PiType EffectiveType -> InferM FLamExpr
checkLam (FLamExpr p body) piTy@(Pi a (eff, b)) = do
  p' <- checkPat p a
  case p' of
    RecLeaf v -> do  -- Potentially a dependent function
      -- TODO: This is a very hacky way for determining whether we are in checking or
      --       inference mode.
      b' <- zonk b
      noInferenceVars <- looks $ null . envIntersect (freeVars b') . solverVars
      if noInferenceVars
        then do  -- Checking
          piTy' <- zonk piTy
          effTy <- maybeApplyPi piTy' $ Just $ Var v
          body' <- extendNamed (foldMap bind p') $ check body effTy
          return $ FLamExpr p' body'
        else do  -- Inference
          bodyValTyVar <- freshQ
          bodyEffTyVar <- freshInferenceVar $ TC EffectKind
          body' <- extendNamed (foldMap bind p') $ check body (bodyEffTyVar, bodyValTyVar)
          bodyEffType <- (,) <$> zonk bodyEffTyVar <*> zonk bodyValTyVar
          let (Pi _ (effTy, resTy)) = makePi v bodyEffType
          constrainEq b   resTy (pprint body)
          constrainEq eff effTy (pprint body)
          return $ FLamExpr p' body'
    _ -> do          -- Regular function
      body' <- extendNamed (foldMap bind p') $ check body (eff, b)
      -- TODO: Make sure that the pattern variables are not leaking?
      return $ FLamExpr p' body'

checkPat :: Pat -> Type -> InferM Pat
checkPat p ty = do
  liftEither $ checkPatShadow p
  p' <- traverse annotBinder p
  constrainEq ty (getType p') (pprint p)
  return p'
  where
    annotBinder (v:>ann) = (v:>) <$> (inferKinds TyKind ann)

    checkPatShadow :: Pat -> Except ()
    checkPatShadow pat = do
      let dups = filter (/= NoName) $ findDups $ map varName $ toList pat
      unless (null dups) $ throw RepeatedVarErr $ pprintList dups

    findDups :: Eq a => [a] -> [a]
    findDups [] = []
    findDups (x:xs) | x `elem` xs = x : findDups xs
                    | otherwise   =     findDups xs

checkAtom :: Atom -> Type -> InferM Atom
checkAtom atom ty = do
  fexpr <- check (toAtomicFExpr atom) (noEffect, ty)
  case fromAtomicFExpr fexpr of
    Just atom' -> return atom'
    Nothing -> error "Shouldn't be possible to infer an atom into a non-atom"

fTyApp :: Var -> [Type] -> FExpr
fTyApp v tys = FPrimExpr $ OpExpr $ TApp (FVar v) tys

openEffect :: Effect -> InferM Effect
openEffect eff = do
  ~(Effect row tailVar) <- zonk eff
  case tailVar of
    Nothing -> liftM (Effect row . Just) $ freshInferenceVar $ TC EffectKind
    Just _  -> return $ Effect row tailVar

generateConSubExprTypes :: PrimCon Type e lam
  -> InferM (PrimCon Type (e, Type) (lam, PiType EffectiveType))
generateConSubExprTypes con = case con of
  Lam im l _ lam -> do
    l' <- inferKinds (TC MultKind) l
    lam'@(Pi _ (eff,_)) <- freshLamType
    return $ Lam im l' eff (lam, lam')
  _ -> traverseExpr con (inferKinds TyKind) (doMSnd freshQ) (doMSnd freshLamType)

generateOpSubExprTypes :: PrimOp Type FExpr FLamExpr
  -> InferM (PrimOp Type (FExpr, Type) (FLamExpr, PiType EffectiveType))
generateOpSubExprTypes op = case op of
  TabGet xs i -> do
    n <- freshQ
    a <- freshQ
    return $ TabGet (xs, n ==> a) (i, n)
  PrimEffect ref m -> do
    s  <- freshQ
    m' <- traverse (doMSnd freshQ) m
    return $ PrimEffect (ref, RefTy s) m'
  RunReader r f@(FLamExpr (RecLeaf (v:>_)) _) -> do
    r' <- freshQ
    a  <- freshQ
    tailVar <- freshInferenceVar $ TC EffectKind
    let refTy = RefTy r'
    let eff = Effect ((v:>()) @> (Reader, refTy)) (Just tailVar)
    let fTy = makePi (v:>refTy) (eff, a)
    return $ RunReader (r, r') (f, fTy)
  RunWriter f@(FLamExpr (RecLeaf (v:>_)) _) -> do
    w <- freshQ
    a <- freshQ
    tailVar <- freshInferenceVar $ TC EffectKind
    let refTy = RefTy w
    let eff = Effect ((v:>()) @> (Writer,refTy)) (Just tailVar)
    let fTy = makePi (v:>refTy) (eff, a)
    return $ RunWriter (f, fTy)
  RunState s f@(FLamExpr (RecLeaf (v:>_)) _) -> do
    s' <- freshQ
    a  <- freshQ
    tailVar <- freshInferenceVar $ TC EffectKind
    let refTy = RefTy s'
    let eff = Effect ((v:>()) @> (State, refTy)) (Just tailVar)
    let fTy = makePi (v:>refTy) (eff, a)
    return $ RunState (s, s') (f, fTy)
  IndexEff effName tabRef i f@(FLamExpr (RecLeaf (v:>_)) _) -> do
    i' <- freshQ
    x  <- freshQ
    a  <- freshQ
    let tabType = i' ==> x
    tailVar <- freshInferenceVar $ TC EffectKind
    let eff = Effect ((v:>()) @> (effName, RefTy x)) (Just tailVar)
    let fTy = makePi (v:> RefTy x) (eff, a)
    return $ IndexEff effName (tabRef, RefTy tabType) (i, i') (f, fTy)
  _ -> traverseExpr op (inferKinds TyKind) (doMSnd freshQ) (doMSnd freshLamType)

freshLamType :: InferM (PiType EffectiveType)
freshLamType = do
  a <- freshQ
  b <- freshQ
  eff <- liftM (Effect mempty . Just) $ freshInferenceVar $ TC EffectKind
  return $ Pi a (eff, b)

doMSnd :: Monad m => m b -> a -> m (a, b)
doMSnd m x = do { y <- m; return (x, y) }

-- === kind inference ===

-- TODO: The outer CatT plays a role of SolverT for kinds. It should
--       get folded into SolverT instead, so that we can keep all inference
--       in a single monad!
type InferKindM a = CatT TypeEnv InferM a

inferKinds :: Kind -> Type -> InferM Type
inferKinds kind ty = do
  env <- asks $ namedEnv
  liftM fst $ runCatT (inferKindsM kind ty) env

runInferKinds :: TypeEnv -> Kind -> Type -> Except Type
runInferKinds env kind ty = liftM fst $ runInferM env $
  runCatT (inferKindsM kind ty) env

inferKindsM :: Kind -> Type -> InferKindM Type
inferKindsM kind ty = case ty of
  NoAnn -> lift $ freshInferenceVar kind
  Var tv@(v:>_) -> do
    x <- looks $ flip envLookup tv
    case x of
      Just NoAnn -> extend (tv @> kind)
      Just k     -> checkKindEq kind k
      _          -> error "Lookup failed"
    return $ Var (v:>kind)
  Forall vs qs body -> liftM fst $ scoped $ do
    checkKindEq kind TyKind
    extend (foldMap bind vs)
    body' <- inferKindsM TyKind body
    vs' <- mapM addKindAnn vs
    let substEnv = newEnv vs (map Var vs')
    let qs' = map (subst (substEnv, mempty)) $ qs ++ impliedClasses body
    return $ Forall vs' qs' body'
  TypeAlias vs body -> liftM fst $ scoped $ do
    extend (foldMap bind vs)
    body' <- inferKindsM TyKind body
    vs' <- mapM addKindAnn vs
    -- TODO: Verify that kind is ArrowKind or TyKind. Can't uncomment this just
    --       yet, because the call site has no way of calling this in inference mode
    --       at the moment.
    -- case vs of
    --   [] -> checkKindEq kind TyKind
    --   _  -> checkKindEq kind $ ArrowKind (map varAnn vs) TyKind
    return $ TypeAlias vs' body'
  ArrowType im m (Pi a (eff, b)) -> do
    checkKindEq kind TyKind
    m' <- inferKindsM (TC MultKind) m
    a' <- inferKindsM TyKind   a
    extendDeBruijn a' $ do
      eff' <- inferKindsM (TC EffectKind) eff
      b'   <- inferKindsM TyKind     b
      return $ ArrowType im m' $ Pi a' (eff', b')
  TabType (Pi a b) -> do
    checkKindEq kind TyKind
    a' <- inferKindsM TyKind a
    extendDeBruijn a' $ do
      b' <- inferKindsM TyKind b
      return $ TabType $ Pi a' b'
  Effect row tailVar -> do
    checkKindEq kind $ TC EffectKind
    row' <- liftM fold $ forM (envPairs row) $ \(v, (eff, NoAnn)) -> do
      let v' = v:>()
      t <- asks $ flip jointEnvGet v'
      return (v' @> (eff, t))
    tailVar' <- traverse (inferKindsM $ TC EffectKind) tailVar
    return $ Effect row' tailVar'
  TC LinCon    -> checkKindEq kind (TC MultKind) >> return ty
  TC NonLinCon -> checkKindEq kind (TC MultKind) >> return ty
  TC con -> do
    checkKindEq kind TyKind
    con' <- traverseTyCon (fst $ tyConKind con)
                          (\(t,k) -> inferKindsM k t)
                          (return . fst)
    TC <$> traverseTyCon (fst $ tyConKind con')
                         (return . fst)
                         (\(x,t) -> lift $ checkAtom x t)
  _ -> error "Not a type"

addKindAnn :: Var -> InferKindM Var
addKindAnn tv@(v:>_) = do
  env <- look
  case envLookup env tv of
    Just NoAnn ->
      throw KindErr $ "Ambiguous kind for type variable: " ++ pprint tv
    Just k -> return (v:>k)
    _ -> error "Lookup failed"

-- TODO: this is quite ad-hoc
impliedClasses :: Type -> [TyQual]
impliedClasses ty =  map (flip TyQual Data  ) (dataVars   ty)
                  <> map (flip TyQual IdxSet) (idxSetVars ty)

idxSetVars :: Type -> [Var]
idxSetVars ty = case ty of
  ArrowType _ _ (Pi a (_, b)) -> recur a <> recur b
  TabTy a b -> map (:>NoAnn) (envNames (freeVars a)) <> recur b
  RecTy r   -> foldMap recur r
  _         -> []
  where recur = idxSetVars

dataVars :: Type -> [Var]
dataVars ty = case ty of
  ArrowType _ _ (Pi a (_, b)) -> recur a <> recur b
  TabTy _ b -> map (:>NoAnn) (envNames (freeVars b))
  RecTy r   -> foldMap recur r
  _         -> []
  where recur = dataVars

-- === constraint solver ===

data SolverEnv = SolverEnv { solverVars :: Env Kind
                           , solverSub  :: Env Type }
type SolverT m = CatT SolverEnv m

runSolverT :: (MonadError Err m, TySubst a, Pretty a)
           => CatT SolverEnv m a -> m a
runSolverT m = liftM fst $ flip runCatT mempty $ do
   ans <- m
   applyDefaults
   ans' <- zonk ans
   vs <- looks $ envNames . unsolved
   throwIf (not (null vs)) TypeErr $ "Ambiguous type variables: "
                                   ++ pprint vs ++ "\n\n" ++ pprint ans
   return ans'

applyDefaults :: MonadCat SolverEnv m => m ()
applyDefaults = do
  vs <- looks unsolved
  forM_ (envPairs vs) $ \(v, k) -> case k of
    TC MultKind   -> addSub v NonLin
    TC EffectKind -> addSub v noEffect
    _ -> return ()
  where addSub v ty = extend $ SolverEnv mempty ((v:>()) @> ty)

solveLocal :: (Pretty a, MonadCat SolverEnv m, MonadError Err m, TySubst a)
           => m a -> m a
solveLocal m = do
  (ans, env@(SolverEnv freshVars sub)) <- scoped (m >>= zonk)
  extend $ SolverEnv (unsolved env) (sub `envDiff` freshVars)
  return ans

checkLeaks :: (Pretty a, MonadCat SolverEnv m, MonadError Err m, TySubst a)
           => [Var] -> m a -> m a
checkLeaks tvs m = do
  (ans, env) <- scoped $ solveLocal m
  forM_ (solverSub env) $ \ty ->
    forM_ tvs $ \tv ->
      throwIf (tv `occursIn` ty) TypeErr $ "Leaked type variable: " ++ pprint tv
  extend env
  return ans

unsolved :: SolverEnv -> Env Kind
unsolved (SolverEnv vs sub) = vs `envDiff` sub

freshQ :: (MonadError Err m, MonadCat SolverEnv m) => m Type
freshQ = freshInferenceVar $ TyKind

freshInferenceVar :: (MonadError Err m, MonadCat SolverEnv m) => Kind -> m Type
freshInferenceVar k = do
  tv <- looks $ rename (rawName InferenceName "?" :> k) . solverVars
  extend $ SolverEnv (tv @> k) mempty
  return (Var tv)

constrainEq :: (MonadCat SolverEnv m, MonadError Err m)
             => Type -> Type -> String -> m ()
constrainEq t1 t2 s = do
  t1' <- zonk t1
  t2' <- zonk t2
  let msg = "\nExpected: " ++ pprint t1'
         ++ "\n  Actual: " ++ pprint t2'
         ++ "\nIn: "       ++ s
  addContext msg $ unify t1' t2'

zonk :: (TySubst a, MonadCat SolverEnv m) => a -> m a
zonk x = do
  s <- looks solverSub
  return $ tySubst s x

-- TODO: check kinds
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
    (ArrowType im l (Pi a (eff, b)), ArrowType im' l' (Pi a' (eff', b')))
      | im == im' -> do
        -- TODO: think very hard about the leak checks we need to add here
        unify l l' >> unify a a' >> unify b b' >> unify eff eff'
    (Effect r t, Effect r' t') -> do
      let shared = rowMeet r r'
      forM_ shared $ \((e, et), (e', et')) -> do
        when (e /= e') $ throw TypeErr "Effect mismatch"
        unify et et'
      newTail <- liftM Just $ freshInferenceVar $ TC EffectKind
      matchTail t  $ Effect (envDiff r' shared) newTail
      matchTail t' $ Effect (envDiff r  shared) newTail
    (TabTy a b, TabTy a' b') -> unify a a' >> unify b b'
    (TC con, TC con') -> case (con, con') of
      (RefType a, RefType a') -> unify a a'
      (RecType r, RecType r') ->
        case zipWithRecord unify r r' of
          Nothing -> throw TypeErr ""
          Just unifiers -> void $ sequence unifiers
      (SumType (l, r), SumType (l', r')) -> unify l l' >> unify r r'
      (TypeApp f xs, TypeApp f' xs') | length xs == length xs' ->
        unify f f' >> zipWithM_ unify xs xs'
      _   -> throw TypeErr ""
    _   -> throw TypeErr ""

rowMeet :: Env a -> Env b -> Env (a, b)
rowMeet (Env m) (Env m') = Env $ M.intersectionWith (,) m m'

-- TODO: can we make this less complicated?
matchTail :: (MonadCat SolverEnv m, MonadError Err m)
          => Maybe Type -> Effect -> m ()
matchTail t ~eff@(Effect row t') = do
  vs <- looks solverVars
  case (t, t') of
    _                     | t == t' && row == mempty     -> return ()
    (Just (Var v), _) | v `isin` vs                  -> zonk eff               >>= bindQ v
    (_, Just (Var v)) | v `isin` vs && row == mempty -> zonk (Effect mempty t) >>= bindQ v
    _ -> throw TypeErr ""

-- TODO: check we're not unifying with deBruijn/skolem vars
bindQ :: (MonadCat SolverEnv m, MonadError Err m) => Var -> Type -> m ()
bindQ v t | v `occursIn` t = throw TypeErr (pprint (v, t))
          | otherwise = extend $ mempty { solverSub = v @> t }

occursIn :: Var -> Type -> Bool
occursIn v t = v `isin` freeVars t

instance Semigroup SolverEnv where
  -- TODO: as an optimization, don't do the subst when sub2 is empty
  -- TODO: make concatenation more efficient by maintaining a reverse-lookup map
  SolverEnv scope1 sub1 <> SolverEnv scope2 sub2 =
    SolverEnv (scope1 <> scope2) (sub1' <> sub2)
    where sub1' = fmap (tySubst sub2) sub1

instance Monoid SolverEnv where
  mempty = SolverEnv mempty mempty
  mappend = (<>)

-- === type substitutions ===

class TySubst a where
  tySubst :: Env Type -> a -> a

instance Subst t => TySubst (PiType t) where
  tySubst env ty = subst (env, mempty) ty

instance TySubst FExpr where
  tySubst env expr = case expr of
    FDecl decl body  -> FDecl (tySubst env decl) (tySubst env body)
    FVar (v:>ty)     -> FVar (v:>tySubst env ty)
    Annot e ty       -> Annot (tySubst env e) (tySubst env ty)
    SrcAnnot e src   -> SrcAnnot (tySubst env e) src
    FPrimExpr e -> FPrimExpr $ tySubst env e

instance TySubst Atom where
  tySubst env atom = subst (env, mempty) atom

instance TySubst LamExpr where
  tySubst env expr = subst (env, mempty) expr

instance TySubst Decl where
  tySubst env expr = subst (env, mempty) expr

instance (TraversableExpr expr, TySubst ty, TySubst e, TySubst lam)
         => TySubst (expr ty e lam) where
  tySubst env expr = fmapExpr expr (tySubst env) (tySubst env) (tySubst env)

instance TySubst FLamExpr where
  tySubst env (FLamExpr p body) = FLamExpr (tySubst env p) (tySubst env body)

instance TySubst FDecl where
  tySubst env decl = case decl of
    LetMono p e -> LetMono (fmap (tySubst env) p) (tySubst env e)
    LetPoly ~(v:>Forall ks qs ty) lam ->
      LetPoly (v:>Forall ks qs (tySubst env ty)) (tySubst env lam)
    TyDef v ty -> TyDef v (tySubst env ty)

instance TySubst FTLam where
  tySubst env (FTLam bs qs body) = FTLam bs qs (tySubst env body)

instance (TySubst a, TySubst b) => TySubst (a, b) where
  tySubst env (x, y) = (tySubst env x, tySubst env y)

instance TySubst a => TySubst (VarP a) where
  tySubst env (v:>ty) = v:> tySubst env ty

instance TySubst a => TySubst (RecTree a) where
  tySubst env p = fmap (tySubst env) p

instance TySubst a => TySubst (Env a) where
  tySubst env xs = fmap (tySubst env) xs

instance TySubst a => TySubst [a] where
  tySubst env xs = map (tySubst env) xs
