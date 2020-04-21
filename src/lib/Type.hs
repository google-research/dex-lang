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
    getKind, checkKindIs, checkKindEq, getEffType, getPatName,
    getConType, checkEffType, HasType, indexSetConcreteSize) where

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

getType :: HasType a => a -> Type
getType x = snd $ getEffType x

checkType :: HasType a => a -> TypeM Type
checkType x = liftM snd $ checkEffType x

checkPureType :: HasType a => a -> TypeM Type
checkPureType x = do
  (eff, ty) <- checkEffType x
  assertEq noEffect eff "Unexpected effect"
  return ty

class HasType a where
  checkEffType :: a -> TypeM EffectiveType
  getEffType   :: a ->       EffectiveType

runTypeM :: TypeEnv -> TypeM a -> Except a
runTypeM env m = runReaderT (runReaderT m env) mempty

checkVar :: Var -> TypeM Type
checkVar v@(_:>annTy) = do
  x <- asks $ flip envLookup v
  case x of
    Just (L ty) -> do
      assertEq annTy ty "Var annotation"
      return ty
    _ -> throw CompilerErr $ "Lookup failed:" ++ pprint v

pureType :: Type -> EffectiveType
pureType ty = (noEffect, ty)

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
    termEnv <- runTypeM env $ flip catFold decls $ \decl -> do
                 (eff, declEnv) <- checkTypeFDecl decl
                 assertEq noEffect eff $ "Unexpected top-level effect: " ++ pprint eff
                 return declEnv
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
checkTyOrKind (L x ) = liftM L $ checkType x
checkTyOrKind (T ty) = liftM T $ checkKind ty

getTyOrKind :: LorT Atom Type -> LorT Type Kind
getTyOrKind (L x ) = L $ getType x
getTyOrKind (T ty) = T $ getKind ty

-- === kind checking ===

getKind :: Type -> Kind
getKind ty = case ty of
  TypeVar v       -> varAnn v
  TypeAlias vs rhs -> ArrowKind (map varAnn vs) (getKind rhs)
  Lin          -> MultKind
  NonLin       -> MultKind
  Effect _ _   -> EffectKind
  NoAnn        -> NoKindAnn
  Dep (_ :> t) -> DepKind t
  DepLit _     -> DepKind $ BaseType IntType
  _            -> TyKind

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
  IntRange a b -> do
      checkKindIs depIntKind a
      checkKindIs depIntKind b
      return TyKind
    where
      depIntKind = DepKind $ BaseType $ IntType
  IndexRange _ _ _ _ -> do
    -- TODO: Check that a and b are types that have an instance of Idx
    return TyKind
  Dep (_ :> t) -> do
    -- TODO: Make sure this is consistent with the environment (use checkVar)
    return $ DepKind t
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
  getEffType tree = pureType $ case tree of
    RecLeaf v -> varAnn v
    RecTree r -> RecType $ fmap getType r

  checkEffType tree = liftM pureType $ case tree of
    RecLeaf v -> checkVar v
    RecTree r -> liftM RecType $ traverse checkType r

instance HasType FExpr where
  getEffType expr = case expr of
    FVar (_:>annTy) -> pureTy annTy
    FDecl decl body -> (eff, bodyTy)
      where
        (bodyEff, bodyTy) = getEffType body
        eff = ignoreExcept $ combineEffects bodyEff $ getFDeclEff decl
    FPrimExpr e -> case e of
      ConExpr con -> pureTy $ getConType $ fmapExpr con id getType getFLamType
      OpExpr  op  -> getOpType $ fmapExpr op id getType getFLamType
    SrcAnnot e _ -> getEffType e
    Annot e _    -> getEffType e

  checkEffType expr = case expr of
    FVar v -> liftM pureTy $ checkVar v
    FDecl decl body -> do
      (eff, env) <- checkTypeFDecl decl
      (eff', ty) <- extendR env $ checkEffType body
      eff'' <- combineEffects eff eff'
      return (eff'', ty)
    FPrimExpr (ConExpr con) -> do
      eTy <- traverseExpr con return checkPureType checkTypeFlam
      liftM pureTy $ checkConType eTy
    FPrimExpr (OpExpr con) -> do
      eTy <- traverseExpr con return checkPureType checkTypeFlam
      checkOpType eTy
    SrcAnnot e pos -> addSrcContext (Just pos) $ checkEffType e
    Annot e ty -> do
      ty' <- checkPureType e
      assertEq ty ty' "Annot"
      return $ pureTy ty

getFDeclEff :: FDecl -> Effect
getFDeclEff decl = case decl of
  LetMono _ rhs -> fst $ getEffType rhs
  _ -> noEffect

getFLamType :: FLamExpr -> PiType
getFLamType (FLamExpr p body) = makePi v $ getEffType body
   where v = getPatName p :> getType p

checkTypeFlam :: FLamExpr -> TypeM PiType
checkTypeFlam (FLamExpr p body) = do
  void $ checkKind pTy
  bodyTy <- extendR (foldMap lbind p) $ checkEffType body
  return $ makePi v bodyTy
  where pTy = getType p
        v = getPatName p :> pTy

checkTypeFDecl :: FDecl -> TypeM (Effect, TypeEnv)
checkTypeFDecl decl = case decl of
  LetMono p rhs -> do
    (eff, ty) <- checkEffType rhs
    assertEq (getType p) ty "LetMono"
    return (eff, foldMap lbind p)
  LetPoly b@(_:>ty) tlam -> do
    ty' <- checkTypeFTLam tlam
    assertEq ty ty' "TLam"
    return (noEffect, b @> L ty)
  FRuleDef ann annTy tlam -> do
    ty <- checkTypeFTLam tlam
    assertEq annTy ty "Rule def"
    checkRuleDefType ann ty
    return (noEffect, mempty)
  TyDef tv _ -> return (noEffect, tbind tv)

checkTypeFTLam :: FTLam -> TypeM Type
checkTypeFTLam (FTLam tbs qs body) = do
  -- TODO: check qualifiers
  body' <- extendClassEnv qs $ extendR (foldMap tbind tbs) $ checkPureType body
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
  TypeVar v          -> checkVarClass env IdxSet v
  RecType r          -> mapM_ recur r
  IntRange _ _       -> return ()
  IndexRange _ _ _ _ -> return ()
  _           -> throw TypeErr $ " Not a valid index set: " ++ pprint ty
  where recur = checkIdxSet env

checkData :: ClassEnv -> Type -> Except ()
checkData env ty = case ty of
  TypeVar v          -> checkVarClass env IdxSet v `catchError`
                           const (checkVarClass env Data v)
  BaseType _         -> return ()
  TabType _ a        -> recur a
  RecType r          -> mapM_ recur r
  IntRange _ _       -> return ()
  IndexRange _ _ _ _ -> return ()
  _ -> throw TypeErr $ " Not serializable data: " ++ pprint ty
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
  getEffType atom = pureTy $ case atom of
    Var (_:>ty) -> ty
    TLam vs qs body -> Forall vs qs $ getType body
    Con con -> getConType $ fmapExpr con id getType getLamType

  checkEffType atom = liftM pureTy $ case atom of
    Var v -> checkVar v
    TLam tvs qs body -> do
      bodyTy <- extendClassEnv qs $ extendR (foldMap tbind tvs) (checkPureType body)
      return $ Forall tvs qs bodyTy
    Con con -> traverseExpr con return checkType checkLam >>= checkConType

instance HasType Expr where
  getEffType expr = case expr of
    Decl (Let _ rhs) e -> (ignoreExcept $ combineEffects eff eff', ty)
      where (eff , ty) = getEffType e
            (eff', _ ) = getEffType rhs
    CExpr e  -> getEffType e
    Atom x   -> getEffType x

  checkEffType expr = case expr of
    Decl decl body -> do
      (declEff, env) <- checkDecl decl
      (bodyEff, ty) <- extendR env $ checkEffType body
      eff <- combineEffects declEff bodyEff
      return (eff, ty)
    CExpr e -> checkEffType e
    Atom x  -> checkEffType x

instance HasType CExpr where
  getEffType   op = getOpType $ fmapExpr op id getType getLamType
  checkEffType op = traverseExpr op return checkType checkLam >>= checkOpType

getLamType :: LamExpr -> PiType
getLamType (LamExpr b body) = makePi b $ getEffType body

combineEffects :: MonadError Err m => Effect -> Effect -> m Effect
combineEffects ~eff@(Effect row t) ~eff'@(Effect row' t') = case (t, t') of
  (Nothing, Nothing) -> do
    row'' <- rowUnion row row'
    return $ Effect row'' Nothing
  (Just _ , Nothing) -> checkRowExtends row  row' >> return eff
  (Nothing, Just _ ) -> checkRowExtends row' row  >> return eff'
  (Just _ , Just _)
    | eff == eff' -> return eff
    | otherwise -> throw TypeErr $ "Effect mismatch "
                                 ++ pprint eff ++ " != " ++ pprint eff'

checkPure :: MonadError Err m => Effect -> m ()
checkPure eff | isPure eff = return ()
              | otherwise = throw TypeErr $ "Unexpected effect " ++ pprint eff


checkExtends :: MonadError Err m => Effect -> Effect -> m ()
checkExtends (Effect row _) (Effect row' Nothing) = checkRowExtends row row'
checkExtends eff eff' | eff == eff' = return ()
                      | otherwise   = throw TypeErr $ "Effect mismatch: "
                           ++ pprint eff ++ " doesn't extend " ++ pprint eff'

checkRowExtends :: MonadError Err m => EffectRow Type -> EffectRow Type -> m ()
checkRowExtends superRow row = do
  mapM_ (\(t,t') -> assertEq t t' "Effect type mismatch") $ rowMeet superRow row
  let extraEffects = rowJoin superRow row `envDiff` superRow
  when (extraEffects /= mempty) $
    throw TypeErr $ "Extra effects: " ++ pprint extraEffects

rowUnion :: MonadError Err m
         => EffectRow Type -> EffectRow Type -> m (EffectRow Type)
rowUnion (Env m) (Env m') = liftM Env $ sequence $
  M.unionWith consensusValsErr (fmap return m) (fmap return m')

consensusValsErr :: (Eq a, Pretty a, MonadError Err m) => m a -> m a -> m a
consensusValsErr x y = do
  x' <- x
  y' <- y
  assertEq x' y' "Map merge"
  return x'

rowMeet :: Env a -> Env b -> Env (a, b)
rowMeet (Env m) (Env m') = Env $ M.intersectionWith (,) m m'

rowJoin :: Env a -> Env b -> Env ()
rowJoin (Env m) (Env m') =
  Env $ M.unionWith (\() () -> ()) (fmap (const ()) m) (fmap (const ()) m')

checkLam :: LamExpr -> TypeM PiType
checkLam (LamExpr b@(_:>a) body) = do
  bodyTy <- extendR (b @> L a) $ checkEffType body
  return $ makePi b bodyTy

checkDecl :: Decl -> TypeM (Effect, TypeEnv)
checkDecl (Let b expr) = do
  checkBinder b
  (eff, t) <- checkEffType expr
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
    return $ pureTy $ subst (newTEnv bs ts, mempty) body
    where
      requiredClasses :: TVar -> [ClassName]
      requiredClasses v = [c | TyQual v' c <- quals, v == v']
  For (Pi n (eff, a)) ->
    inClass IdxSet n >> inClass Data a >> return (eff, TabType n a)
  TabCon n ty xs -> do
    case indexSetConcreteSize n of
      Nothing -> throw TypeErr $
         "Literal table must have a concrete index set.\nGot: " ++ pprint n
      Just n' | n' == length xs -> do inClass Data ty >> mapM_ (eq ty) xs
                                      return (pureTy (n ==> ty))
              | otherwise -> throw TypeErr $
                  "Index set size mismatch: " ++
                     show n' ++ " != " ++ show (length xs)
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
    row' <- popRow eq row (Reader, (Ref r))
    eq r r'
    return (Effect row' tailVar, a)
  RunWriter ~(Pi (Ref w) (Effect row tailVar, a)) -> do
    row' <- popRow eq row (Writer, Ref w)
    return (Effect row' tailVar, pairTy a w)
  RunState s ~(Pi (Ref s') (Effect row tailVar, a)) -> do
    row' <- popRow eq row (State, Ref s)
    eq s s'
    return (Effect row' tailVar, pairTy a s)
  IndexEff eff ~(Dep ref) tabRef i ~(Pi (Ref x) (Effect row tailVar, a)) -> do
    row' <- popRow eq row (eff, Ref x)
    eq tabRef  (Ref (TabType i x))
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
  Inject (IndexRange (Dep low) _ (Dep high) _) -> do
    eq (varAnn low) (varAnn high)
    return $ pureTy $ (varAnn low)
  _ -> error $ "Unexpected primitive type: " ++ pprint op

traverseConType :: MonadError Err m
                     => PrimConType
                     -> (Type      -> Type -> m ()) -- add equality constraint
                     -> (Kind      -> Type -> m ()) -- add kind constraint
                     -> (ClassName -> Type -> m ()) -- add class constraint
                     -> m Type
traverseConType con eq kindIs _ = case con of
  Lit l    -> return $ BaseType $ litType l
  Lam l eff (Pi a (eff', b)) -> do
    checkExtends eff eff'
    return $ ArrowType l (Pi a (eff, b))
  RecCon r -> return $ RecType r
  AFor n a -> return $ TabType n a
  AGet (ArrayType _ b) -> return $ BaseType b  -- TODO: check shape matches AFor scope
  AsIdx n e -> eq e (BaseType IntType) >> return n
  ArrayRef (Array shape b _) -> return $ ArrayType shape b
  Todo ty -> kindIs TyKind ty >> return ty
  _ -> error $ "Unexpected primitive type: " ++ pprint con

binOpType :: ScalarBinOp -> (BaseType, BaseType, BaseType)
binOpType op = case op of
  IAdd   -> (i, i, i);  ISub   -> (i, i, i)
  IMul   -> (i, i, i);  ICmp _ -> (i, i, b)
  IDiv   -> (i, i, i)
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

popRow :: MonadError Err m
       => (a -> a -> m ())
       -> EffectRow a -> (EffectName, a) -> m (EffectRow a)
popRow eq env (eff, x) = case envLookup env (v:>()) of
  Nothing -> return env'
  Just (eff', x') -> do
    assertEq eff eff' "Effect"
    eq x x'
    return env'
  where v = DeBruijn 0
        env' = envDelete v env

flattenType :: Type -> [(BaseType, [Int])]
flattenType ty = case ty of
  BaseType b  -> [(b, [])]
  RecType r -> concat $ map flattenType $ toList r
  TabType (FixedIntRange low high) a -> [(b, (high - low):shape) | (b, shape) <- flattenType a]
  FixedIntRange _ _ -> [(IntType, [])]
  -- temporary hack. TODO: fix
  TabType _             a -> [(b, 0:shape) | (b, shape) <- flattenType a]
  TypeVar _               -> [(IntType, [])]
  _ -> error $ "Unexpected type: " ++ show ty

extendClassEnv :: [TyQual] -> TypeM a -> TypeM a
extendClassEnv qs m = do
  r <- ask
  let classEnv = fold [monMapSingle v [c] | TyQual (v:>_) c <- qs]
  lift $ extendR classEnv $ runReaderT m r

indexSetConcreteSize :: Type -> Maybe Int
indexSetConcreteSize ty = case ty of
  FixedIntRange low high -> Just $ high - low
  RecType r -> liftM product $ mapM indexSetConcreteSize $ toList r
  _ -> Nothing

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
checkLinFLam (FLamExpr _ body) = checkLinFExpr body

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
  For (FLamExpr _ body) -> checkLinFExpr body
  TabGet x i -> tensCheck (check x) (withoutLin (check i))
  RunReader r (FLamExpr ~(RecLeaf v) body) -> do
    ((), spent) <- captureSpent $ checkLinFExpr r
    extendR (v @> spent) $ checkLinFExpr body
  RunWriter (FLamExpr ~(RecLeaf v) body) -> do
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
  Lam NonLin _ lam -> checkLinFLam lam
  Lam Lin _ (FLamExpr p body) -> do
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
