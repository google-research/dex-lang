-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Type (
    getType, substEnvType, flattenType, PrimOpType, PrimConType,
    litType, traverseOpType, traverseConType, binOpType, unOpType,
    tupTy, pairTy, isData, IsModule (..), IsModuleBody (..), popRow,
    getKind, checkKindIs, checkKindEq, getEffType, getPatName) where

import Control.Monad
import Control.Monad.Except hiding (Except)
import Control.Monad.Reader
import Data.Foldable
import qualified Data.Map.Strict as M
import Data.Text.Prettyprint.Doc

import Syntax
import Env
import Record
import PPrint
import Cat
import Subst

type ClassEnv = MonMap Name [ClassName]
type TypeM a = ReaderT TypeEnv (ReaderT ClassEnv (Either Err)) a

class HasType a where
  getType :: a -> Type

runTypeM :: TypeEnv -> TypeM a -> Except a
runTypeM env m = runReaderT (runReaderT m env) mempty

-- === Module interfaces ===

class IsModule a where
  -- TODO: consider just a 'Check' typeclass
  checkModule  :: a -> Except ()
  moduleType   :: a -> ModuleType

class IsModuleBody a where
  checkModuleBody  :: TypeEnv -> a -> Except TypeEnv

instance (IsModuleBody body) => IsModule (ModuleP body) where
  checkModule (Module (imports, exports) body) = do
    exports' <- checkModuleBody imports body
    assertEq exports exports' "Module exports"
  moduleType (Module ty _) = ty

instance IsModuleBody FModBody where
  checkModuleBody env (FModBody decls tyDefs) = do
    termEnv <- runTypeM env $ catFold (checkTypeFDecl noEffect) decls
    mapM_ runCheckLinFDecl decls
    return $ termEnv <> tyDefEnv
    where tyDefEnv = fmap (T . getKind) tyDefs

instance IsModuleBody ModBody where
  -- TODO: find a better way to decide which errors are compiler errors
  checkModuleBody env (ModBody decls result) = asCompilerErr $ do
    runTypeM (env <> topTypeEnv result) $ do
      (effs, env') <- catTraverse checkDecl decls
      mapM_ checkPure effs
      void $ extendR env' $ traverse checkTyOrKind (topSubstEnv result)
    return $ topTypeEnv result

asCompilerErr :: Except a -> Except a
asCompilerErr (Left (Err _ c msg)) = Left $ Err CompilerErr c msg
asCompilerErr (Right x) = Right x

substEnvType :: SubstEnv -> TypeEnv
substEnvType env = fmap getTyOrKind env

checkTyOrKind :: LorT Atom Type -> TypeM (LorT Type Kind)
checkTyOrKind (L x ) = liftM L $ checkAtom x
checkTyOrKind (T ty) = liftM T $ checkKind ty

getTyOrKind :: LorT Atom Type -> LorT Type Kind
getTyOrKind (L x ) = L $ getType x
getTyOrKind (T ty) = T $ getKind ty

-- === kind checking ===

getKind :: Type -> Kind
getKind ty = case ty of
  TypeVar v       -> varAnn v
  TypeAlias vs rhs -> ArrowKind (map varAnn vs) (getKind rhs)
  Lin        -> MultKind
  NonLin     -> MultKind
  Effect _ _ -> EffectKind
  NoAnn      -> NoKindAnn
  _          -> TyKind

checkKind :: (MonadError Err m, MonadReader TypeEnv m)
          => Type -> m Kind
checkKind ty = case ty of
  TypeVar v@(_:>k) -> do
    x <- asks $ flip envLookup v
    case x of
      Just (T k') -> do
        assertEq k k' "Kind annotation"
      _ -> throw KindErr $ "Kind lookup failed: " ++ pprint v
    return k
  ArrowType m (Pi a (e, b)) -> do
    checkKindIs MultKind m
    checkKindIs TyKind a
    checkKindIs EffectKind e
    checkKindIs TyKind b
    return TyKind
  Forall vs _ body -> do
    extendR (foldMap tbind vs) (checkKindIs TyKind body)
    return TyKind
  TypeAlias vs body -> do
    bodyKind <- extendR (foldMap tbind vs) (checkKind body)
    return $ ArrowKind (map varAnn vs) bodyKind
  Effect eff tailVar -> do
    mapM_ (mapM_ (checkKindIs TyKind)) eff
    case tailVar of
      Nothing -> return ()
      Just tv@(TypeVar _) -> checkKindIs EffectKind tv
      _ -> throw TypeErr $ "Effect tail must be a variable " ++ pprint tailVar
    return EffectKind
  NoAnn -> error "Shouldn't have NoAnn left"
  _ -> do
    void $ traverseType (\k t -> checkKindIs k t >> return t) ty
    return $ getKind ty

checkKindIs :: (MonadError Err m, MonadReader TypeEnv m)
            => Kind -> Type -> m ()
checkKindIs k ty = do
  k' <- checkKind ty
  checkKindEq k k'

checkKindEq :: MonadError Err m => Kind -> Kind -> m ()
checkKindEq k1 k2 | k1 == k2  = return ()
                  | otherwise = throw KindErr $ "\nExpected: " ++ pprint k1
                                             ++ "\n  Actual: " ++ pprint k2

-- === type-checking pass on FExpr ===

instance HasType (RecTree Var) where
  getType (RecLeaf (_:>ty)) = ty
  getType (RecTree r) = RecType $ fmap getType r

instance HasType FExpr where
  getType expr = case expr of
    FVar (_:>annTy) -> annTy
    FDecl _ body -> getType body
    FPrimExpr e -> case e of
      ConExpr con ->       getConType $ fmapExpr con id getType getFLamType
      OpExpr  op  -> snd $ getOpType  $ fmapExpr op  id getType getFLamType
    SrcAnnot e _ -> getType e
    Annot e _    -> getType e

checkTypeFExpr :: Effect -> FExpr -> TypeM Type
checkTypeFExpr eff expr = case expr of
  FVar v@(_:>annTy) -> do
    x <- asks $ flip envLookup v
    case x of
      Just (L ty) -> do
        assertEq annTy ty "Var annotation"
        return ty
      _ -> throw CompilerErr $ "Lookup failed:" ++ pprint v
  FDecl decl body -> do
    env <- checkTypeFDecl eff decl
    extendR env (checkTypeFExpr eff body)
  FPrimExpr (ConExpr con) -> do
    eTy <- traverseExpr con return (checkTypeFExpr noEffect) checkTypeFlam
    checkConType eTy
  FPrimExpr (OpExpr con) -> do
    eTy <- traverseExpr con return (checkTypeFExpr noEffect) checkTypeFlam
    (eff', ty) <- checkOpType eTy
    checkExtends eff eff'
    return ty
  SrcAnnot e pos -> addSrcContext (Just pos) $ checkTypeFExpr eff e
  -- TODO: consider effect annotations
  Annot e _ -> do
    ty' <- checkTypeFExpr noEffect e
    return ty'

getFLamType :: FLamExpr -> PiType
getFLamType (FLamExpr p eff body) = makePi v (eff, getType body)
   where v = getPatName p :> getType p

checkTypeFlam :: FLamExpr -> TypeM PiType
checkTypeFlam (FLamExpr p eff body) = do
  void $ checkKind pTy
  bodyTy <- extendR (foldMap lbind p) $ checkTypeFExpr eff body
  return $ makePi v (eff, bodyTy)
  where pTy = getType p
        v = getPatName p :> pTy

checkTypeFDecl :: Effect -> FDecl -> TypeM TypeEnv
checkTypeFDecl eff decl = case decl of
  LetMono p rhs -> do
    ty <- checkTypeFExpr eff rhs
    assertEq (getType p) ty "LetMono"
    return $ foldMap lbind p
  LetPoly b@(_:>ty) tlam -> do
    ty' <- checkTypeFTLam tlam
    assertEq ty ty' "TLam"
    return (b @> L ty)
  FRuleDef ann annTy tlam -> do
    ty <- checkTypeFTLam tlam
    assertEq annTy ty "Rule def"
    checkRuleDefType ann ty
    return mempty
  TyDef tv _ -> return $ tbind tv

checkTypeFTLam :: FTLam -> TypeM Type
checkTypeFTLam (FTLam tbs qs body) = do
  -- TODO: check qualifiers
  body' <- extendClassEnv qs $ extendR (foldMap tbind tbs) $
             checkTypeFExpr noEffect body
  return $ Forall tbs qs body'

checkRuleDefType :: RuleAnn -> Type -> TypeM ()
checkRuleDefType (LinearizationDef v) linTy = do
  ty <- asks $ fromL . (!(v:>()))
  case ty of
    ArrowType _ (Pi a (eff, b)) | isPure eff -> do
      let linTyExpected = Forall [] [] $ a --> pairTy b (a --@ b)
      unless (linTy == linTyExpected) $ throw TypeErr $
        "Annotation should have type: " ++ pprint linTyExpected
    _ -> throw TypeErr $
           "Bad type for linearization-annotated function: " ++ pprint ty

litType :: LitVal -> BaseType
litType v = case v of
  IntLit  _ -> IntType
  RealLit _ -> RealType
  StrLit  _ -> StrType
  BoolLit _ -> BoolType

-- === Built-in typeclasses ===

checkClassConstraint :: ClassName -> Type -> TypeM ()
checkClassConstraint c ty = do
  env <- lift ask
  liftEither $ checkClassConstraint' env c ty

checkClassConstraint' :: ClassEnv -> ClassName -> Type -> Except ()
checkClassConstraint' env c ty = case c of
  VSpace -> checkVSpace env ty
  IdxSet -> checkIdxSet env ty
  Data   -> checkData   env ty

checkVSpace :: ClassEnv -> Type -> Except ()
checkVSpace env ty = case ty of
  TypeVar v         -> checkVarClass env VSpace v
  BaseType RealType -> return ()
  TabType _ a       -> recur a
  RecType r         -> mapM_ recur r
  _                 -> throw TypeErr $ " Not a vector space: " ++ pprint ty
  where recur = checkVSpace env

checkIdxSet :: ClassEnv -> Type -> Except ()
checkIdxSet env ty = case ty of
  TypeVar v   -> checkVarClass env IdxSet v
  IdxSetLit _ -> return ()
  RecType r   -> mapM_ recur r
  _           -> throw TypeErr $ " Not a valid index set: " ++ pprint ty
  where recur = checkIdxSet env

checkData :: ClassEnv -> Type -> Except ()
checkData env ty = case ty of
  TypeVar v   -> checkVarClass env IdxSet v `catchError`
                    const (checkVarClass env Data v)
  BaseType _  -> return ()
  TabType _ a -> recur a
  RecType r   -> mapM_ recur r
  IdxSetLit _ -> return ()
  _           -> throw TypeErr $ " Not serializable data: " ++ pprint ty
  where recur = checkData env

isData :: Type -> Bool
isData ty = case checkData mempty ty of Left _ -> False
                                        Right _ -> True

-- TODO: check annotation too
checkVarClass :: ClassEnv -> ClassName -> TVar -> Except ()
checkVarClass env c (v:>_) =
  unless (c `elem` cs) $ throw TypeErr $
              " Type variable \"" ++ pprint v ++ "\" not in class: " ++ pprint c
  where cs = monMapLookup env v

-- -- === Normalized IR ===

instance HasType Atom where
  getType atom = case atom of
    Var (_:>ty) -> ty
    TLam vs qs body -> Forall vs qs $ getType body
    Con con -> getConType $ fmapExpr con id getType getLamType

instance HasType Expr where
  getType expr = case expr of
    Decl _ e -> getType e
    CExpr e  -> getType e
    Atom x   -> getType x

instance HasType CExpr where
  getType op = snd $ getEffType op

getLamType :: LamExpr -> PiType
getLamType (LamExpr b eff body) = makePi b (eff, getType body)

getEffType :: CExpr -> EffectiveType
getEffType op = getOpType $ fmapExpr op id getType getLamType

checkExpr :: Effect -> Expr -> TypeM Type
checkExpr eff expr = case expr of
  Decl decl body -> do
    (declEff, env) <- checkDecl decl
    checkExtends eff declEff
    extendR env $ checkExpr eff body
  CExpr e -> do
    (eff', ty) <- checkCExpr e
    checkExtends eff eff'
    return ty
  Atom x -> checkAtom x

checkCExpr :: CExpr -> TypeM EffectiveType
checkCExpr op = traverseExpr op return checkAtom checkLam >>= checkOpType

checkAtom :: Atom -> TypeM Type
checkAtom atom = case atom of
  Var v@(_:>ty) -> do
    x <- asks $ flip envLookup v
    case x of
      Just (L ty') -> do
        assertEq ty' ty "NVar annot"
        return ty
      _ -> throw CompilerErr $ "Lookup failed:" ++ pprint v
  TLam tvs qs body -> do
    -- TODO: extend env with qstraints
    bodyTy <- extendClassEnv qs $ extendR (foldMap tbind tvs) (checkExpr noEffect body)
    return $ Forall tvs qs bodyTy
  Con con -> traverseExpr con return checkAtom checkLam >>= checkConType

checkPure :: MonadError Err m => Effect -> m ()
checkPure eff | isPure eff = return ()
              | otherwise = throw TypeErr $ "Unexpected effect " ++ pprint eff

checkExtends :: MonadError Err m => Effect -> Effect -> m ()
checkExtends (Effect row _) (Effect row' Nothing) = checkRowExtends row row'
checkExtends eff eff' | eff == eff' = return ()
                      | otherwise   = throw TypeErr $ "Effect mismatch: "
                           ++ pprint eff ++ " doesn't extend " ++ pprint eff'

checkRowExtends :: MonadError Err m => EffectRow Type -> EffectRow Type -> m ()
checkRowExtends row row' = do
  mapM_ (\(t,t') -> assertEq t t' "Effect type mismatch") $ rowMeet row row'
  let extraEffects = rowJoin row row' `envDiff` row
  when (extraEffects /= mempty) $
    throw TypeErr $ "Extra effects: " ++ pprint extraEffects

rowMeet :: Env a -> Env b -> Env (a, b)
rowMeet (Env m) (Env m') = Env $ M.intersectionWith (,) m m'

rowJoin :: Env a -> Env b -> Env ()
rowJoin (Env m) (Env m') =
  Env $ M.unionWith (\() () -> ()) (fmap (const ()) m) (fmap (const ()) m')

checkLam :: LamExpr -> TypeM PiType
checkLam (LamExpr b@(_:>a) eff body) = do
  bodyTy <- extendR (b @> L a) $ checkExpr eff body
  return $ makePi b (eff, bodyTy)

checkDecl :: Decl -> TypeM (Effect, TypeEnv)
checkDecl (Let b expr) = do
  checkBinder b
  (eff, t) <- checkCExpr expr
  assertEq (varAnn b) t "Decl"
  return (eff, binderEnv b)

binderEnv :: Var -> TypeEnv
binderEnv b@(_:>ty) = b @> L ty

checkBinder :: Var -> TypeM ()
checkBinder b = do
  kind <- checkKind (varAnn b)
  assertEq TyKind kind "kind error"
  checkShadow b

checkShadow :: Pretty b => VarP b -> TypeM ()
checkShadow v = do
  env <- ask
  if v `isin` env
    then throw CompilerErr $ pprint v ++ " shadowed"
    else return ()

pairTy :: Type -> Type -> Type
pairTy x y = tupTy [x, y]

tupTy :: [Type] -> Type
tupTy xs = RecType $ Tup xs

pureTy :: Type -> EffectiveType
pureTy ty = (noEffect, ty)

-- === primitive ops and constructors ===

type PrimOpType  = PrimOp  Type Type PiType
type PrimConType = PrimCon Type Type PiType

getOpType :: PrimOpType -> EffectiveType
getOpType e = ignoreExcept $ traverseOpType e ignoreArgs ignoreArgs ignoreArgs

getConType :: PrimConType -> Type
getConType e = ignoreExcept $ traverseConType e ignoreArgs ignoreArgs ignoreArgs

checkOpType :: PrimOpType -> TypeM EffectiveType
checkOpType e = traverseOpType e checkConstraint checkKindIs checkClassConstraint

checkConType :: PrimConType -> TypeM Type
checkConType e = traverseConType e checkConstraint checkKindIs checkClassConstraint

ignoreArgs :: Monad m => a -> b -> m ()
ignoreArgs _ _ = return ()

checkConstraint :: Type -> Type -> TypeM ()
checkConstraint ty1 ty2 | ty1 == ty2 = return ()
                        | otherwise  = throw TypeErr $
                                         pprint ty1 ++ " != " ++ pprint ty2

traverseOpType :: MonadError Err m
                     => PrimOpType
                     -> (Type      -> Type -> m ()) -- add equality constraint
                     -> (Kind      -> Type -> m ()) -- add kind constraint
                     -> (ClassName -> Type -> m ()) -- add class constraint
                     -> m EffectiveType
traverseOpType op eq kindIs inClass = case op of
  App l d (ArrowType l' piTy@(Pi a _)) a' -> do
    eq a a'
    eq l l'
    return $ applyPi piTy d
  TApp (Forall bs quals body) ts -> do
    assertEq (length bs) (length ts) "Number of type args"
    zipWithM_ (kindIs . varAnn) bs ts
    sequence_ [inClass c t | (t, b) <- zip ts bs, c <- requiredClasses b]
    let env = fold [b @> T t | (b, t) <- zip bs ts]
    return $ pureTy $ subst (env, mempty) body
    where
      requiredClasses :: TVar -> [ClassName]
      requiredClasses v = [c | TyQual v' c <- quals, v == v']
  For (Pi n (eff, a)) ->
    inClass IdxSet n >> inClass Data a >> return (eff, TabType n a)
  TabCon n ty xs ->
    inClass Data ty >> mapM_ (eq ty) xs >> eq n n' >> return (pureTy (n ==> ty))
    where n' = IdxSetLit (length xs)
  TabGet (TabType i a) i' -> eq i i' >> return (pureTy a)
  RecGet (RecType r) i    -> return $ pureTy $ recGet r i
  ArrayGep (ArrayType (_:shape) b) i -> do
    eq (BaseType IntType) i
    return $ pureTy $ ArrayType shape b
  LoadScalar (ArrayType [] b) -> return $ pureTy $ BaseType b
  ScalarBinOp binop t1 t2 -> do
    eq (BaseType t1') t1
    eq (BaseType t2') t2
    return $ pureTy $ BaseType tOut
    where (t1', t2', tOut) = binOpType binop
  -- TODO: check index set constraint
  ScalarUnOp IndexAsInt _ -> return $ pureTy $ BaseType IntType
  ScalarUnOp unop ty -> eq (BaseType ty') ty >> return (pureTy (BaseType outTy))
    where (ty', outTy) = unOpType unop
  -- TODO: check vspace constraints
  VSpaceOp ty VZero        -> inClass VSpace ty >> return (pureTy ty)
  VSpaceOp ty (VAdd e1 e2) -> inClass VSpace ty >> eq ty e1 >> eq ty e2 >> return (pureTy ty)
  Cmp _  ty   a b -> eq ty a >> eq ty b >> return (pureTy (BaseType BoolType))
  Select ty p a b -> eq ty a >> eq ty b >> eq (BaseType BoolType) p >> return (pureTy ty)
  PrimEffect ~(Dep ref) ~(Ref x) m -> case m of
    MAsk     ->            return (Effect (ref @> (Reader, Ref x)) Nothing, x)
    MTell x' -> eq x x' >> return (Effect (ref @> (Writer, Ref x)) Nothing, unitTy)
    MGet     ->            return (Effect (ref @> (State , Ref x)) Nothing, x)
    MPut  x' -> eq x x' >> return (Effect (ref @> (State , Ref x)) Nothing, unitTy)
  RunReader r ~(Pi (Ref r') (Effect row tailVar, a)) -> do
    ((effName, refTy), row') <- popRow (DeBruijn 0) row
    assertEq Reader effName "Effect"
    eq r r'
    eq (Ref r) refTy
    return (Effect row' tailVar, a)
  RunWriter ~(Pi (Ref w) (Effect row tailVar, a)) -> do
    ((effName, refTy), row') <- popRow (DeBruijn 0) row
    assertEq Writer effName "Effect"
    eq (Ref w) refTy
    return (Effect row' tailVar, pairTy a w)
  RunState s ~(Pi (Ref s') (Effect row tailVar, a)) -> do
    ((effName, refTy), row') <- popRow (DeBruijn 0) row
    assertEq State effName "Effect"
    eq s s'
    eq (Ref s) refTy
    return (Effect row' tailVar, pairTy a s)
  IndexEff eff ~(Dep ref) tabRef i ~(Pi (Ref x) (Effect row tailVar, a)) -> do
    ((eff', xRef), row') <- liftEither $ popRow (DeBruijn 0) row
    assertEq eff eff' "Effect"
    eq tabRef  (Ref (TabType i x))
    eq xRef    (Ref x)
    let row'' = row' <> (ref @> (eff, Ref (TabType i x)))
    return (Effect row'' tailVar, a)
  Linearize (Pi a (eff, b)) -> do
    eq noEffect eff
    return $ pureTy $ a --> pairTy b (a --@ b)
  Transpose (Pi a (eff, b)) -> do
    eq noEffect eff
    return $ pureTy $ b --@ a
  IntAsIndex ty i  -> eq (BaseType IntType) i >> return (pureTy ty)
  IdxSetSize _     -> return $ pureTy $ BaseType IntType
  NewtypeCast ty _ -> return $ pureTy ty
  FFICall _ argTys ansTy argTys' ->
    zipWithM_ eq argTys argTys' >> return (pureTy ansTy)
  _ -> error $ "Unexpected primitive type: " ++ pprint op

traverseConType :: MonadError Err m
                     => PrimConType
                     -> (Type      -> Type -> m ()) -- add equality constraint
                     -> (Kind      -> Type -> m ()) -- add kind constraint
                     -> (ClassName -> Type -> m ()) -- add class constraint
                     -> m Type
traverseConType con eq kindIs _ = case con of
  Lit l    -> return $ BaseType $ litType l
  Lam l p  -> return $ ArrowType l p
  RecCon r -> return $ RecType r
  AFor n a -> return $ TabType n a
  AGet (ArrayType _ b) -> return $ BaseType b  -- TODO: check shape matches AFor scope
  AsIdx n e -> eq e (BaseType IntType) >> return (IdxSetLit n)
  ArrayRef (Array shape b _) -> return $ ArrayType shape b
  Todo ty -> kindIs TyKind ty >> return ty
  _ -> error $ "Unexpected primitive type: " ++ pprint con

binOpType :: ScalarBinOp -> (BaseType, BaseType, BaseType)
binOpType op = case op of
  IAdd   -> (i, i, i);  ISub   -> (i, i, i)
  IMul   -> (i, i, i);  ICmp _ -> (i, i, b)
  Pow    -> (i, i, i);  Rem    -> (i, i, i)
  FAdd   -> (r, r, r);  FSub   -> (r, r, r)
  FMul   -> (r, r, r);  FCmp _ -> (r, r, b)
  FDiv   -> (r, r, r);  And    -> (b, b, b)
  Or     -> (b, b, b)
  where b = BoolType
        i = IntType
        r = RealType

unOpType :: ScalarUnOp -> (BaseType, BaseType)
unOpType op = case op of
  Not        -> (BoolType, BoolType)
  FNeg       -> (RealType, RealType)
  IntToReal  -> (IntType, RealType)
  BoolToInt  -> (BoolType, IntType)
  _ -> error $ show op

popRow :: (Pretty a, MonadError Err m)
       => Name -> EffectRow a -> m ((EffectName, a), EffectRow a)
popRow v env = case envLookup env (v:>()) of
  Just x -> return (x, envDelete v env)
  _      -> throw CompilerErr $
              "Row lookup failed: " ++ show v ++ " in " ++ pprint env

flattenType :: Type -> [(BaseType, [Int])]
flattenType ty = case ty of
  BaseType b  -> [(b, [])]
  RecType r -> concat $ map flattenType $ toList r
  TabType (IdxSetLit n) a -> [(b, n:shape) | (b, shape) <- flattenType a]
  IdxSetLit _ -> [(IntType, [])]
  -- temporary hack. TODO: fix
  TabType _             a -> [(b, 0:shape) | (b, shape) <- flattenType a]
  TypeVar _               -> [(IntType, [])]
  _ -> error $ "Unexpected type: " ++ show ty

extendClassEnv :: [TyQual] -> TypeM a -> TypeM a
extendClassEnv qs m = do
  r <- ask
  let classEnv = fold [monMapSingle v [c] | TyQual (v:>_) c <- qs]
  lift $ extendR classEnv $ runReaderT m r

-- === linearity ===

type Spent = Env ()
newtype LinCheckM a = LinCheckM
  { runLinCheckM :: (ReaderT (Env Spent) (Either Err)) (a, (Spent, Env Spent)) }

runCheckLinFDecl :: FDecl -> Except ()
runCheckLinFDecl decls =
  void $ runReaderT (runLinCheckM $ checkLinFDecl decls) mempty

checkLinFExpr :: FExpr -> LinCheckM ()
checkLinFExpr expr = case expr of
  FVar v -> checkLinVar v
  FDecl decl body -> do
    env <- checkLinFDecl decl
    extendR env (checkLinFExpr body)
  FPrimExpr (OpExpr  op ) -> checkLinOp op
  FPrimExpr (ConExpr con) -> checkLinCon con
  SrcAnnot e pos -> addSrcContext (Just pos) $ checkLinFExpr e
  Annot e _      -> checkLinFExpr e

checkLinFLam :: FLamExpr -> LinCheckM ()
checkLinFLam (FLamExpr _ _ body) = checkLinFExpr body

checkLinFDecl :: FDecl -> LinCheckM (Env Spent)
checkLinFDecl decl = case decl of
  LetMono p rhs -> do
    ((), spent) <- captureSpent $ checkLinFExpr rhs
    return $ foldMap (@>spent) p
  LetPoly _ (FTLam _ _ expr) -> do
    void $ checkLinFExpr expr
    return mempty
  _ -> return mempty

checkLinOp :: PrimOp Type FExpr FLamExpr -> LinCheckM ()
checkLinOp e = case e of
  ScalarUnOp  FNeg x    -> check x
  ScalarBinOp FAdd x y  -> check x >> check y
  ScalarBinOp FSub x y  -> check x >> check y
  ScalarBinOp FDiv x y  -> tensCheck (check x) (withoutLin (check y))
  ScalarBinOp FMul x y  -> tensCheck (check x) (check y)
  App Lin    _ fun x -> tensCheck (check fun) (check x)
  App NonLin _ fun x -> tensCheck (check fun) (withoutLin (check x))
  RunReader r (FLamExpr ~(RecLeaf v) _ body) -> do
    ((), spent) <- captureSpent $ checkLinFExpr r
    extendR (v @> spent) $ checkLinFExpr body
  RunWriter (FLamExpr ~(RecLeaf v) _ body) -> do
    ((), spent) <- captureEffSpent v $ checkLinFExpr body
    spend spent
  PrimEffect ~(Dep ref) _ m -> case m of
    MAsk -> checkLinVar ref
    MTell x -> do
      ((), s) <- captureSpent $ checkLinFExpr x
      spendEff ref s
    _ -> void $ withoutLin $ traverseExpr e pure check checkLinFLam
  _ -> void $ withoutLin $ traverseExpr e pure check checkLinFLam
  where check = checkLinFExpr

checkLinCon :: PrimCon Type FExpr FLamExpr -> LinCheckM ()
checkLinCon e = case e of
  Lam NonLin lam -> checkLinFLam lam
  Lam Lin (FLamExpr p _ body) -> do
    let v = getPatName p
    let s = asSpent v
    withLocalLinVar v $ extendR (foldMap (@>s) p) $ checkLinFExpr body
  RecCon r -> mapM_ check r
  _ -> void $ withoutLin $ traverseExpr e pure check checkLinFLam
  where check = checkLinFExpr

withLocalLinVar :: Name -> LinCheckM a -> LinCheckM a
withLocalLinVar v m = do
  (ans, vs) <- captureSpent m
  spend $ vs `envDiff` (v'@>())
  return ans
  where v' = v:>()

withoutLin :: LinCheckM a -> LinCheckM a
withoutLin (LinCheckM m) = LinCheckM $ do
  (ans, (vs, sEff)) <- m
  unless (null vs) $ throw LinErr $
    "nonlinear function consumed linear data: " ++ showSpent vs
  return (ans, (mempty, sEff))

tensCheck :: LinCheckM () -> LinCheckM () -> LinCheckM ()
tensCheck x y = LinCheckM $ do
  ((), (sx, sxEff)) <- runLinCheckM x
  ((), (sy, syEff)) <- runLinCheckM y
  sxy    <- liftEither $ tensCat sx sy
  return ((), (sxy, sxEff <> syEff))

checkLinVar :: VarP a -> LinCheckM ()
checkLinVar v = do
  env <- ask
  case envLookup env v of
    Nothing -> spend mempty
    Just s  -> spend s

getPatName :: RecTree Var -> Name
getPatName (RecLeaf (v:>_)) = v
getPatName p = case toList p of (v:>_):_ -> v
                                _        -> NoName

spend :: Spent -> LinCheckM ()
spend s = LinCheckM $ return ((), (s, mempty))

spendEff :: VarP a -> Spent -> LinCheckM ()
spendEff v s = LinCheckM $ return ((), (mempty, v@>s))

asSpent :: Name -> Spent
asSpent v = (v:>())@>()

tensCat :: Spent -> Spent -> Except Spent
tensCat vs vs' = do
  let overlap = envIntersect vs vs'
  unless (null overlap) $ throw LinErr $ "pattern spent twice: "
                                       ++ showSpent overlap
  return $ vs <> vs'

captureSpent :: LinCheckM a -> LinCheckM (a, Spent)
captureSpent m = LinCheckM $ do
  (x, (s, sEff)) <- runLinCheckM m
  return ((x, s), (mempty, sEff))

captureEffSpent :: VarP ann ->  LinCheckM a -> LinCheckM (a, Spent)
captureEffSpent (v:>_) m = LinCheckM $ do
  (x, (s, sEff)) <- runLinCheckM m
  let varSpent = sEff ! (v:>())
  let sEff' = envDelete v sEff
  return ((x, varSpent), (s, sEff'))

showSpent :: Spent -> String
showSpent vs = pprint $ envNames vs

instance Functor LinCheckM where
  fmap = liftM

instance Applicative LinCheckM where
  pure x = LinCheckM $ return (x, (mempty, mempty))
  (<*>) = ap

instance Monad LinCheckM where
  m >>= f = LinCheckM $ do
    (x, s1) <- runLinCheckM m
    (y, s2) <- runLinCheckM (f x)
    return (y, (s1 <> s2))

instance MonadReader (Env Spent) LinCheckM where
  ask = LinCheckM $ do
    env <- ask
    return (env, (mempty, mempty))
  local env (LinCheckM m) = LinCheckM $ local env m

instance MonadError Err LinCheckM where
  throwError err = LinCheckM $ throwError err
  catchError (LinCheckM m) f = LinCheckM $ catchError m (runLinCheckM . f)
