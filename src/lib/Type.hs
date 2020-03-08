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
    getType, instantiateTVs, abstractTVs, substEnvType,
    tangentBunType, flattenType, PrimOpType, PrimConType,
    getExprType, getCExprType,
    litType, traverseOpType, traverseConType, binOpType, unOpType,
    tupTy, pairTy, isData, IsModule (..), IsModuleBody (..)) where

import Control.Monad
import Control.Monad.Except hiding (Except)
import Control.Monad.Reader
import Data.Foldable
import Data.Text.Prettyprint.Doc

import Syntax
import Env
import Record
import PPrint
import Cat
import Subst

type TypeM a = ReaderT TypeEnv (Either Err) a

class HasType a where
  getType :: a -> Type

runTypeM :: TypeEnv -> TypeM a -> Except a
runTypeM env m = runReaderT m env

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
    (effs, termEnv) <- runTypeM env $ catTraverse checkTypeFDecl decls
    mapM_ checkPure effs
    mapM_ runCheckLinFDecl decls
    return $ termEnv <> tyDefEnv
    where tyDefEnv = fmap (const (T (TyKind []))) tyDefs

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
checkTyOrKind (L x) = liftM L $ checkAtom x
checkTyOrKind (T _) = return $ T $ TyKind []

getTyOrKind :: LorT Atom Type -> LorT Type Kind
getTyOrKind (L x) = L $ getType x
getTyOrKind (T _) = T $ TyKind []

-- === type-checking pass on FExpr ===

getFExprType :: FExpr -> EffectiveType
getFExprType expr = case expr of
  FDecl _ body -> getFExprType body
  FVar (_:>ty) -> pureTy ty
  FPrimExpr (OpExpr e) -> getOpType e'
    where e' = fmapExpr e id (snd . getFExprType) getFLamType
  FPrimExpr (ConExpr e) -> pureTy $ getConType e'
    where e' = fmapExpr e id (snd . getFExprType) getFLamType
  Annot e _    -> getFExprType e
  SrcAnnot e _ -> getFExprType e

getFLamType :: FLamExpr -> (Type, EffectiveType)
getFLamType (FLamExpr p body) = (getType p, getFExprType body)

instance HasType (RecTree Var) where
  getType (RecLeaf (_:>ty)) = ty
  getType (RecTree r) = RecType $ fmap getType r

checkTypeFExpr :: FExpr -> TypeM EffectiveType
checkTypeFExpr expr = case expr of
  FVar v@(_:>annTy) -> do
    x <- asks $ flip envLookup v
    case x of
      Just (L ty) -> do
        assertEq annTy ty "Var annotation"
        return $ pureTy ty
      _ -> throw CompilerErr $ "Lookup failed:" ++ pprint v
  FDecl decl body -> do
    (declEff, env) <- checkTypeFDecl decl
    (eff, ty ) <- extendR env (checkTypeFExpr body)
    checkEffectMatches eff declEff
    return (eff, ty)
  FPrimExpr (ConExpr con) -> do
    eTy <- traverseExpr con return (checkTypeFExpr >=> fromPure) checkTypeFlam
    liftM pureTy $ checkConType eTy
  FPrimExpr (OpExpr con) -> do
    eTy <- traverseExpr con return (checkTypeFExpr >=> fromPure) checkTypeFlam
    checkOpType eTy
  SrcAnnot e pos -> addSrcContext (Just pos) $ checkTypeFExpr e
  -- TODO: consider effect annotations
  Annot e ty -> do
    ty' <- checkTypeFExpr e
    assertEq (pureTy ty) ty' "Type annotation"
    return ty'

checkTypeFlam :: FLamExpr -> TypeM (Type, EffectiveType)
checkTypeFlam (FLamExpr p body) = do
  checkTy pTy
  bodyTy <- extendR (foldMap lbind p) $ checkTypeFExpr body
  return (pTy, bodyTy)
  where pTy = getType p

checkTypeFDecl :: FDecl -> TypeM (Effect, TypeEnv)
checkTypeFDecl decl = case decl of
  LetMono p rhs -> do
    (eff, ty) <- checkTypeFExpr rhs
    assertEq (getType p) ty "LetMono"
    return (eff, foldMap lbind p)
  LetPoly b@(_:>ty) tlam -> do
    ty' <- checkTypeFTLam tlam
    assertEq ty ty' "TLam"
    return (Pure, b @> L ty)
  FRuleDef ann annTy tlam -> do
    ty <- checkTypeFTLam tlam
    assertEq annTy ty "Rule def"
    checkRuleDefType ann ty
    return (Pure, mempty)
  TyDef tv _ -> return (Pure, tbind tv)

checkTypeFTLam :: FTLam -> TypeM Type
checkTypeFTLam (FTLam tbs body) = do
  let env = foldMap (\b -> b @> T (varAnn b)) tbs
  ty <- extendR env (checkTypeFExpr body) >>= fromPure
  return $ Forall (map varAnn tbs) (abstractTVs tbs ty)

checkRuleDefType :: RuleAnn -> Type -> TypeM ()
checkRuleDefType (LinearizationDef v) linTy = do
  ty <- asks $ fromL . (!(v:>()))
  case ty of
    ArrowType _ a (Pure, b) -> do
      let linTyExpected = Forall [] $ a --> pairTy b (a --@ b)
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
  env <- ask
  liftEither $ checkClassConstraint' env c ty

checkClassConstraint' :: TypeEnv -> ClassName -> Type -> Except ()
checkClassConstraint' env c ty = case c of
  VSpace -> checkVSpace env ty
  IdxSet -> checkIdxSet env ty
  Data   -> checkData   env ty

checkVSpace :: TypeEnv -> Type -> Except ()
checkVSpace env ty = case ty of
  TypeVar v         -> checkVarClass env VSpace v
  BaseType RealType -> return ()
  TabType _ a       -> recur a
  RecType r         -> mapM_ recur r
  _                 -> throw TypeErr $ " Not a vector space: " ++ pprint ty
  where recur = checkVSpace env

checkIdxSet :: TypeEnv -> Type -> Except ()
checkIdxSet env ty = case ty of
  TypeVar v   -> checkVarClass env IdxSet v
  IdxSetLit _ -> return ()
  RecType r   -> mapM_ recur r
  _           -> throw TypeErr $ " Not a valid index set: " ++ pprint ty
  where recur = checkIdxSet env

checkData :: TypeEnv -> Type -> Except ()
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
checkVarClass :: TypeEnv -> ClassName -> TVar -> Except ()
checkVarClass env c v = do
  case envLookup env v of
    Just (T (TyKind cs)) ->
      unless (c `elem` cs) $ throw TypeErr $ " Type variable \""  ++ pprint v ++
                                             "\" not in class: " ++ pprint c
    _ -> throw CompilerErr $ "Lookup of kind failed:" ++ pprint v

-- -- === Normalized IR ===

instance HasType Atom where
  getType atom = case atom of
    Var (_:>ty) -> ty
    TLam vs body -> do
      Forall (map varAnn vs) $ abstractTVs vs $ snd $ getExprType body
    Con con -> getConType $ fmapExpr con id getType getLamType

getExprType :: Expr -> EffectiveType
getExprType expr = case expr of
  Decl _ e -> getExprType e
  CExpr e  -> getCExprType e
  Atom x   -> pureTy $ getType x

getCExprType :: CExpr -> EffectiveType
getCExprType op = getOpType $ fmapExpr op id getType getLamType

getLamType :: LamExpr -> (Type, EffectiveType)
getLamType (LamExpr (_:>ty) body) = (ty, getExprType body)

checkExpr :: Expr -> TypeM EffectiveType
checkExpr expr = case expr of
  Decl decl body -> do
    (declEff , env) <- checkDecl decl
    (eff, ty)   <- extendR env $ checkExpr body
    checkEffectMatches eff declEff
    return (eff, ty)
  CExpr e -> checkCExpr e
  Atom x  -> liftM pureTy $ checkAtom x

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
  TLam tvs body -> do
    (eff, bodyTy) <- extendR (foldMap tbind tvs) (checkExpr body)
    checkPure eff
    return $ Forall (map varAnn tvs) (abstractTVs tvs bodyTy)
  Con con -> traverseExpr con return checkAtom checkLam >>= checkConType

fromPure :: MonadError Err m => EffectiveType -> m Type
fromPure (eff, ty) = checkPure eff >> return ty

checkPure :: MonadError Err m => Effect -> m ()
checkPure Pure = return ()
checkPure eff  = throw TypeErr $ "Unexpected effect " ++ pprint eff

checkEffectMatches :: MonadError Err m => Effect -> Effect -> m ()
checkEffectMatches _ Pure = return ()
checkEffectMatches eff eff' | eff == eff' = return ()
                            | otherwise   = throw TypeErr $ "Effect mismatch: "
                                          ++ pprint eff ++ " vs " ++ pprint eff'

checkLam :: LamExpr -> TypeM (Type, EffectiveType)
checkLam (LamExpr b@(_:>ty) body) = do
  bodyTy <- extendR (b @> L ty) $ checkExpr body
  return (ty, bodyTy)

checkDecl :: Decl -> TypeM (Effect, TypeEnv)
checkDecl (Let b expr) = do
  checkBinder b
  (eff, t) <- checkCExpr expr
  assertEq (varAnn b) t "Decl"
  return (eff, binderEnv b)

binderEnv :: Var -> TypeEnv
binderEnv b@(_:>ty) = b @> L ty

checkTy :: Type -> TypeM ()
checkTy _ = return () -- TODO: check kind and unbound type vars

checkBinder :: Var -> TypeM ()
checkBinder b = do
  checkTy (varAnn b)
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
pureTy ty = (Pure, ty)

tangentBunType :: Type -> Type
tangentBunType ty = case ty of
  BaseType b -> case b of RealType -> pairTy ty ty
                          _ -> ty
  TypeVar _ -> ty  -- can only be an index set
  ArrowType l a (Pure, b) -> ArrowType l (recur a) (Pure, recur b)
  TabType n a   -> TabType n (recur a)
  IdxSetLit _ -> ty
  BoundTVar _ -> ty
  _ -> error "Not implemented"
  where recur = tangentBunType

-- === primitive ops and constructors ===

type PrimOpType  = PrimOp  Type Type (Type, EffectiveType)
type PrimConType = PrimCon Type Type (Type, EffectiveType)

getOpType :: PrimOpType -> EffectiveType
getOpType e = ignoreExcept $ traverseOpType e ignoreConstraint ignoreClass

getConType :: PrimConType -> Type
getConType e = ignoreExcept $ traverseConType e ignoreConstraint ignoreClass

checkOpType :: PrimOpType -> TypeM EffectiveType
checkOpType e = traverseOpType e checkConstraint (flip checkClassConstraint)

checkConType :: PrimConType -> TypeM Type
checkConType e = traverseConType e checkConstraint (flip checkClassConstraint)

ignoreConstraint :: Monad m => Type -> Type -> m ()
ignoreConstraint _ _ = return ()

ignoreClass :: Monad m => Type -> ClassName -> m ()
ignoreClass _ _ = return ()

checkConstraint :: Type -> Type -> TypeM ()
checkConstraint ty1 ty2 | ty1 == ty2 = return ()
                        | otherwise  = throw TypeErr $
                                         pprint ty1 ++ " != " ++ pprint ty2

traverseOpType :: MonadError Err m
                     => PrimOpType
                     -> (Type -> Type      -> m ()) -- add equality constraint
                     -> (Type -> ClassName -> m ()) -- add class constraint
                     -> m EffectiveType
traverseOpType op eq inClass = case op of
  App l (ArrowType l' a b) a' -> do
    eq a a'
    eq l l'
    return b
  TApp (Forall kinds body) ts -> do
    assertEq (length kinds) (length ts) "Number of type args"
    sequence_ [ mapM_ (inClass t) cs | (TyKind cs, t) <- zip kinds ts]
    return $ pureTy $ instantiateTVs ts body
  For (n,(eff, a)) ->
    inClass n IdxSet >> inClass a Data >> return (eff, TabType n a)
  TabCon n ty xs ->
    inClass ty Data >> mapM_ (eq ty) xs >> eq n n' >> return (pureTy (n ==> ty))
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
  VSpaceOp ty VZero        -> inClass ty VSpace >> return (pureTy ty)
  VSpaceOp ty (VAdd e1 e2) -> inClass ty VSpace >> eq ty e1 >> eq ty e2 >> return (pureTy ty)
  Cmp _  ty   a b -> eq ty a >> eq ty b >> return (pureTy (BaseType BoolType))
  Select ty p a b -> eq ty a >> eq ty b >> eq (BaseType BoolType) p >> return (pureTy ty)
  PrimEffect ~eff@(Effect r w s) x l m -> case m of
    MAsk     -> eq (Lens r x) l            >> return (eff, x)
    MTell x' -> eq (Lens w x) l >> eq x x' >> return (eff, unitTy)
    MGet     -> eq (Lens s x) l            >> return (eff, x)
    MPut  x' -> eq (Lens s x) l >> eq x x' >> return (eff, unitTy)
  RunEffect r s (a, ~(Effect r' w s', b)) -> do
    eq a unitTy >> eq r r' >> eq s s'
    return $ pureTy $ tupTy [b, w, s]
  Return ~(Effect r w s) a -> return (Effect r w s, a)
  LensGet a (Lens a' b) -> eq a a' >> return (pureTy b)
  Linearize (a, (eff, b)) -> do
    eq Pure eff
    return $ pureTy $ a --> pairTy b (a --@ b)
  Transpose (a, (eff, b)) -> do
    eq Pure eff
    return $ pureTy $ b --@ a
  IntAsIndex ty i  -> eq (BaseType IntType) i >> return (pureTy ty)
  IdxSetSize _     -> return $ pureTy $ BaseType IntType
  NewtypeCast ty _ -> return $ pureTy ty
  FFICall _ argTys ansTy argTys' ->
    zipWithM_ eq argTys argTys' >> return (pureTy ansTy)
  _ -> error $ "Unexpected primitive type: " ++ pprint op

traverseConType :: MonadError Err m
                     => PrimConType
                     -> (Type -> Type      -> m ()) -- add equality constraint
                     -> (Type -> ClassName -> m ()) -- add class constraint
                     -> m Type
traverseConType con eq _ = case con of
  Lit l       -> return $ BaseType $ litType l
  Lam l (a,b) -> return $ ArrowType l a b
  RecCon r    -> return $ RecType r
  AFor n a                -> return $ TabType n a
  AGet (ArrayType _ b) -> return $ BaseType b  -- TODO: check shape matches AFor scope
  AsIdx n e -> eq e (BaseType IntType) >> return (IdxSetLit n)
  LensCon l -> case l of
    IdxAsLens ty n -> return $ Lens (TabType n ty) ty
    LensId ty      -> return $ Lens ty ty
    LensCompose ~(Lens a b) ~(Lens b' c) -> eq b b' >> return (Lens a c)
  ArrayRef (Array shape b _) -> return $ ArrayType shape b
  Todo ty     -> return ty
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

-- === linearity ===

data Spent = Spent (Env ()) Bool  -- flag means 'may consume any linear vars'
-- Second element of (Spent, Spent) pair is spending due to writer effect
newtype LinCheckM a = LinCheckM
  { runLinCheckM :: (ReaderT (Env Spent) (Either Err)) (a, (Spent, Spent)) }

runCheckLinFDecl :: FDecl -> Except ()
runCheckLinFDecl decls =
  void $ runReaderT (runLinCheckM $ checkLinFDecl decls) mempty

checkLinFExpr :: FExpr -> LinCheckM ()
checkLinFExpr expr = case expr of
  FVar v -> do
    env <- ask
    case envLookup env v of
      Nothing -> spend tensId
      Just s  -> spend s
  FDecl decl body -> do
    env <- checkLinFDecl decl
    extendR env (checkLinFExpr body)
  FPrimExpr (OpExpr  op ) -> checkLinOp  op
  FPrimExpr (ConExpr con) -> checkLinCon con
  SrcAnnot e pos -> addSrcContext (Just pos) $ checkLinFExpr e
  Annot e _      -> checkLinFExpr e

checkLinFLam :: FLamExpr -> LinCheckM ()
checkLinFLam (FLamExpr _ body) = checkLinFExpr body

checkLinFDecl :: FDecl -> LinCheckM (Env Spent)
checkLinFDecl decl = case decl of
  LetMono p rhs -> do
    ((), spent) <- captureSpent $ checkLinFExpr rhs
    return $ foldMap (@>spent) p
  LetPoly _ (FTLam _ expr) -> do
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
  App Lin    fun x -> tensCheck (check fun) (check x)
  App NonLin fun x -> tensCheck (check fun) (withoutLin (check x))
  _ -> void $ withoutLin $ traverseExpr e pure check checkLinFLam
  where check = checkLinFExpr

checkLinCon :: PrimCon Type FExpr FLamExpr -> LinCheckM ()
checkLinCon e = case e of
  Lam NonLin lam -> checkLinFLam lam
  Lam Lin (FLamExpr p body) -> do
    v <- getPatName p
    let s = asSpent v
    checkSpent v (pprint p) $ extendR (foldMap (@>s) p) $ checkLinFExpr body
  Lit (RealLit 0.0) -> return ()
  RecCon r -> mapM_ check r
  _ -> void $ withoutLin $ traverseExpr e pure check checkLinFLam
  where check = checkLinFExpr

withoutLin :: LinCheckM a -> LinCheckM a
withoutLin (LinCheckM m) = LinCheckM $ do
  (ans, (s@(Spent vs _), sEff)) <- m
  unless (null vs) $ throw LinErr $
    "nonlinear function consumed linear data: " ++ pprint s
  return (ans, (tensId, sEff))

tensCheck :: LinCheckM () -> LinCheckM () -> LinCheckM ()
tensCheck x y = LinCheckM $ do
  ((), (sx, sxEff)) <- runLinCheckM x
  ((), (sy, syEff)) <- runLinCheckM y
  sxy    <- liftEither $ tensCat sx    sy
  sxyEff <- liftEither $ cartCat sxEff syEff
  return ((), (sxy, sxyEff))

getPatName :: (MonadError Err m, Traversable f) => f Var -> m Name
getPatName p = case toList p of
  []  -> throw LinErr $
           "empty patterns not allowed for linear lambda (for silly reasons)"
  (v:>_):_ -> return v

spend :: Spent -> LinCheckM ()
spend s = LinCheckM $ return ((), (s, cartId))

spendEff :: Spent -> LinCheckM ()
spendEff sEff = LinCheckM $ return ((), (cartId, sEff))

checkSpent :: Name -> String -> LinCheckM a -> LinCheckM a
checkSpent v vStr m = do
  (ans, Spent vs consumes) <- captureSpent m
  unless  (consumes || v' `isin` vs) $ throw LinErr $ "pattern never spent: " ++ vStr
  spend (Spent (vs `envDiff` (v'@>())) consumes)
  return ans
   where v' = v:>()

asSpent :: Name -> Spent
asSpent v = Spent ((v:>())@>()) False

tensCat :: Spent -> Spent -> Except Spent
tensCat (Spent vs consumes) (Spent vs' consumes') = do
  let overlap = envIntersect vs vs'
  unless (null overlap) $ throw LinErr $ "pattern spent twice: "
                                       ++ pprint (Spent overlap False)
  return $ Spent (vs <> vs') (consumes || consumes')

cartCat :: Spent -> Spent -> Except Spent
cartCat s1@(Spent vs consumes) s2@(Spent vs' consumes') = do
  unless (consumes  || vs' `containedWithin` vs ) $ throw LinErr errMsg
  unless (consumes' || vs  `containedWithin` vs') $ throw LinErr errMsg
  return $ Spent (vs <> vs') (consumes && consumes')
  where containedWithin x y = null $ x `envDiff` y
        errMsg = "different consumption by Cartesian product elements: "
                  ++ pprint s1 ++ " vs " ++ pprint s2

tensId :: Spent
tensId = Spent mempty False

cartId :: Spent
cartId = Spent mempty True

captureSpent :: LinCheckM a -> LinCheckM (a, Spent)
captureSpent m = LinCheckM $ do
  (x, (s, sEff)) <- runLinCheckM m
  return ((x, s), (cartId, sEff))

captureSpentEff :: LinCheckM a -> LinCheckM (a, Spent)
captureSpentEff m = LinCheckM $ do
  (x, (s, sEff)) <- runLinCheckM m
  return ((x, sEff), (s, cartId))

-- TODO: allow multiple sources of monadic linearity
monadPat :: Name
monadPat = "mLin"

instance Pretty Spent where
  pretty (Spent vs True ) = pretty (envNames vs ++ ["*"])
  pretty (Spent vs False) = pretty (envNames vs)

instance Functor LinCheckM where
  fmap = liftM

instance Applicative LinCheckM where
  pure x = LinCheckM $ return (x, (cartId, cartId))
  (<*>) = ap

instance Monad LinCheckM where
  m >>= f = LinCheckM $ do
    (x, (s1, s1Eff)) <- runLinCheckM m
    (y, (s2, s2Eff)) <- runLinCheckM (f x)
    s    <- liftEither $ cartCat s1    s2
    sEff <- liftEither $ cartCat s1Eff s2Eff
    return (y, (s, sEff))

instance MonadReader (Env Spent) LinCheckM where
  ask = LinCheckM $ do
    env <- ask
    return (env, (cartId, cartId))
  local env (LinCheckM m) = LinCheckM $ local env m

instance MonadError Err LinCheckM where
  throwError err = LinCheckM $ throwError err
  catchError (LinCheckM m) f = LinCheckM $ catchError m (runLinCheckM . f)
