-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Type (
    getType, substEnvType, flattenType, PrimOpType, PrimConType,
    litType, traverseOpType, traverseConType, binOpType, unOpType,
    isData, Checkable (..), popRow, getTyOrKind, moduleType,
    getKind, checkKindEq, getEffType, getPatName, tyConKind,
    checkRuleDefType, getConType, checkEffType, HasType, indexSetConcreteSize,
    maybeApplyPi, makePi, applyPi, isDependentType, PiAbstractable,
    checkNoShadow, checkNoMutualShadows) where

import Control.Monad
import Control.Monad.Except hiding (Except)
import Control.Monad.Reader
import Data.Foldable
import qualified Data.Map.Strict as M
import Data.Text.Prettyprint.Doc

import Array
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

checkTypeIs :: HasType a => Type -> a -> TypeM ()
checkTypeIs ty x = do
  ty' <- checkType x
  checkConstraint ty ty'

-- === Module interfaces ===

moduleType :: ModuleP body -> (TypeEnv, TypeEnv)
moduleType (Module _ (imports, exports) _) = ( foldMap varAsEnv imports
                                             , foldMap varAsEnv exports )

class Checkable a where
  checkValid :: a -> Except ()

instance Checkable FModule where
  checkValid m@(Module _ _ decls) = do
    let expr = wrapFDecls decls $ FPrimExpr $ ConExpr $ RecCon $ Tup []
    void $ runTypeM imports $ checkPureType expr
    void $ runLinCheck $ checkLinFExpr expr
    where (imports, _) = moduleType m

instance Checkable Module where
  checkValid m@(Module _ _ expr) = asCompilerErr $
    void $ runTypeM imports $ checkPureType expr
    where (imports, _) = moduleType m

asCompilerErr :: Except a -> Except a
asCompilerErr (Left (Err _ c msg)) = Left $ Err CompilerErr c msg
asCompilerErr (Right x) = Right x

substEnvType :: SubstEnv -> TypeEnv
substEnvType env = fmap getTyOrKind env

getTyOrKind :: LorT Atom Type -> LorT Type Kind
getTyOrKind (L x ) = L $ getType x
getTyOrKind (T ty) = T $ getKind ty

-- === kind checking ===

getKind :: Type -> Kind
getKind ty = case ty of
  TypeVar v        -> varAnn v
  ArrowType _ _    -> TyKind
  TabType _        -> TyKind
  Forall _ _ _     -> TyKind
  TypeAlias vs rhs -> ArrowKind (map varAnn vs) (getKind rhs)
  Effect _ _       -> EffectKind
  NoAnn            -> NoKindAnn
  TC con           -> snd $ tyConKind con

-- TODO: add class constraints
tyConKind :: TyCon Type e -> (TyCon (Type, Kind) (e, Type), Kind)
tyConKind con = case con of
  BaseType b        -> (BaseType b, TyKind)
  IntRange a b      -> (IntRange (a, IntTy) (b, IntTy), TyKind)
  -- This forces us to specialize to `TyCon Type e` instead of `TyCon ty e`
  IndexRange t a b  -> (IndexRange (t, TyKind) (fmap (,t) a)
                                               (fmap (,t) b), TyKind)
  ArrayType t       -> (ArrayType t, TyKind)
  SumType (l, r)    -> (SumType ((l, TyKind), (r, TyKind)), TyKind)
  RecType r         -> (RecType (fmap (,TyKind) r), TyKind)
  RefType t         -> (RefType (t, TyKind), TyKind)
  TypeApp t xs      -> (TypeApp (t, tk) (map (,TyKind) xs), TyKind)
    where tk = ArrowKind (map (const TyKind) xs) TyKind
  LinCon            -> (LinCon   , MultKind)
  NonLinCon         -> (NonLinCon, MultKind)

checkKind :: Type -> TypeM Kind
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
  TabType (Pi a b) -> do
    checkKindIs TyKind a
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
  TC con -> do
    let (conKind, resultKind) = tyConKind con
    void $ traverseTyCon conKind (\(t,k) -> checkKindIs k t)
                                 (\(e,t) -> checkTypeIs t e)
    return resultKind

checkKindIs :: Kind -> Type -> TypeM ()
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
    RecTree r -> RecTy $ fmap getType r

  checkEffType tree = liftM pureType $ case tree of
    RecLeaf v -> checkVar v
    RecTree r -> liftM RecTy $ traverse checkType r

instance HasType FExpr where
  getEffType expr = case expr of
    FVar (_:>annTy) -> pureTy annTy
    FDecl decl body -> (eff, bodyTy)
      where
        (bodyEff, bodyTy) = getEffType body
        eff = ignoreExcept $ combineEffects bodyEff $ getFDeclEff decl
    FPrimExpr e -> case e of
      ConExpr con -> pureTy $ getConType $ fmapExpr con id getType getFLamType
      OpExpr  op  -> getOpType $ fmapExpr op id addType getFLamType
        where addType x = (fromAtomicFExpr x, getType x)
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
      eTy <- traverseExpr con return addType checkTypeFlam
      checkOpType eTy
      where addType x = liftM (fromAtomicFExpr x,) (checkPureType x)
    SrcAnnot e pos -> addSrcContext (Just pos) $ checkEffType e
    Annot e ty -> do
      ty' <- checkPureType e
      assertEq ty ty' "Annot"
      return $ pureTy ty

getFDeclEff :: FDecl -> Effect
getFDeclEff decl = case decl of
  LetMono _ rhs -> fst $ getEffType rhs
  _ -> noEffect

getFLamType :: FLamExpr -> PiType EffectiveType
getFLamType (FLamExpr p body) = makePi v $ getEffType body
   where v = getPatName p :> getType p

checkTypeFlam :: FLamExpr -> TypeM (PiType EffectiveType)
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
      let linTyExpected = Forall [] [] $ a --> PairTy b (a --@ b)
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
  TypeVar v -> checkVarClass env VSpace v
  RealTy    -> return ()
  TabTy _ b -> recur b
  RecTy r   -> mapM_ recur r
  _ -> throw TypeErr $ " Not a vector space: " ++ pprint ty
  where recur = checkVSpace env

checkIdxSet :: ClassEnv -> Type -> Except ()
checkIdxSet env ty = case ty of
  TypeVar v             -> checkVarClass env IdxSet v
  RecTy r               -> mapM_ recur r
  SumTy l r             -> recur l >> recur r
  TC (BaseType BoolType) -> return ()
  TC (IntRange _ _)     -> return ()
  TC (IndexRange _ _ _) -> return ()
  _ -> throw TypeErr $ " Not a valid index set: " ++ pprint ty
  where recur = checkIdxSet env

checkData :: ClassEnv -> Type -> Except ()
checkData env ty = case ty of
  TypeVar v          -> checkVarClass env IdxSet v `catchError`
                           const (checkVarClass env Data v)
  TabTy _ b        -> recur b
  TC con -> case con of
    BaseType _       -> return ()
    RecType r        -> mapM_ recur r
    IntRange _ _     -> return ()
    IndexRange _ _ _ -> return ()
    _ -> throw TypeErr $ " Not serializable data: " ++ pprint ty
  _   -> throw TypeErr $ " Not serializable data: " ++ pprint ty
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
  getEffType   op = getOpType $ fmapExpr op id addType getLamType
    where addType x = (Just x, getType x)
  checkEffType op = do
    op' <- traverseExpr op return addType checkLam
    checkOpType op'
    where addType x = liftM (Just x,) (checkType x)

getLamType :: LamExpr -> PiType EffectiveType
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

checkLam :: LamExpr -> TypeM (PiType EffectiveType)
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
  env <- ask
  checkNoShadow env b

checkNoShadow :: (MonadError Err m, Pretty b) => Env a -> VarP b -> m ()
checkNoShadow env v = do
  if v `isin` env
    then throw CompilerErr $ pprint v ++ " shadowed"
    else return ()

checkNoMutualShadows :: (MonadError Err m, Pretty b, Traversable f)
                    => f (VarP b) -> m ()
checkNoMutualShadows bs =
  void $ flip runCatT mempty $ forM bs $ \b -> do
    env <- look
    checkNoShadow env b
    extend (b@>())

pureTy :: Type -> EffectiveType
pureTy ty = (noEffect, ty)

-- === primitive ops and constructors ===

type PrimOpType  = PrimOp  Type (Maybe Atom, Type) (PiType EffectiveType)
type PrimConType = PrimCon Type Type (PiType EffectiveType)

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

isDependentOp :: PrimOp ty e lam -> Bool
isDependentOp op = case op of
  App _ _ _        -> True
  PrimEffect _ _   -> True
  IndexEff _ _ _ _ -> True
  TabGet _ _       -> True
  _                -> False

traverseOpType :: MonadError Err m
               => PrimOpType
               -> (Type      -> Type -> m ()) -- add equality constraint
               -> (Kind      -> Type -> m ()) -- add kind constraint
               -> (ClassName -> Type -> m ()) -- add class constraint
               -> m EffectiveType
traverseOpType op eq _ _ | isDependentOp op = case op of
  App l (_, ArrowType l' piTy@(Pi a _)) (x, a') -> do
    eq a a'
    eq l l'
    maybeApplyPi piTy x
  TabGet (_, TabType piTy@(Pi i _)) (x, i') -> eq i i' >> maybeApplyPi piTy x >>= return . pureType
  PrimEffect ~(Just val, ty) m -> do
    let (ref, x) = case (val, ty) of
          (Var ref', RefTy x') -> (ref', x')
          -- This case is a hack for the Imp lowering, which does a dodgy substitution here
          -- TODO: something better!
          _ -> ("###":>UnitTy, ty)
    case m of
      MAsk         ->            return (Effect (ref @> (Reader, RefTy x)) Nothing, x)
      MTell (_,x') -> eq x x' >> return (Effect (ref @> (Writer, RefTy x)) Nothing, UnitTy)
      MGet         ->            return (Effect (ref @> (State , RefTy x)) Nothing, x)
      MPut  (_,x') -> eq x x' >> return (Effect (ref @> (State , RefTy x)) Nothing, UnitTy)
  IndexEff eff ~(Just (Var ref), tabRef) (_, i) ~(Pi (RefTy x) (Effect row tailVar, a)) -> do
    row' <- popRow eq row (eff, RefTy x)
    eq tabRef (RefTy (TabTy i x))
    let row'' = row' <> (ref @> (eff, RefTy (TabTy i x)))
    return (Effect row'' tailVar, a)
  _ -> error $ "Unexpected primitive type: " ++ pprint op

traverseOpType op eq kindIs inClass = case fmapExpr op id snd id of
  TApp (Forall bs quals body) ts -> do
    assertEq (length bs) (length ts) "Number of type args"
    zipWithM_ (kindIs . varAnn) bs ts
    sequence_ [inClass c t | (t, b) <- zip ts bs, c <- requiredClasses b]
    return $ pureTy $ subst (newTEnv bs ts, mempty) body
    where
      requiredClasses :: TVar -> [ClassName]
      requiredClasses v = [c | TyQual v' c <- quals, v == v']
  For _ (Pi n (eff, a)) ->
    inClass IdxSet n >> inClass Data a >> return (eff, TabTy n a)
  TabCon n ty xs -> do
    case indexSetConcreteSize n of
      Nothing -> throw TypeErr $
         "Literal table must have a concrete index set.\nGot: " ++ pprint n
      Just n' | n' == length xs -> do inClass Data ty >> mapM_ (eq ty) xs
                                      return (pureTy (n ==> ty))
              | otherwise -> throw TypeErr $
                  "Index set size mismatch: " ++
                     show n' ++ " != " ++ show (length xs)
  SumCase st lp@(Pi la (leff, lb)) lr@(Pi ra (reff, rb)) -> do
    unless (not $ any isDependentType [lp, lr]) $ throw TypeErr $
        "Return type of cases cannot depend on the matched value"
    eq st (SumTy la ra)
    inClass Data la
    inClass Data ra
    eq leff noEffect
    eq reff noEffect
    eq lb rb
    return $ pureType $ lb
  RecGet (RecTy r) i    -> return $ pureTy $ recGet r i
  ArrayGep (ArrayTy (_:shape) b) i -> do
    eq IntTy i
    return $ pureTy $ ArrayTy shape b
  LoadScalar (ArrayTy [] b) -> return $ pureTy $ BaseTy b
  ScalarBinOp binop t1 t2 -> do
    eq (BaseTy t1') t1
    eq (BaseTy t2') t2
    return $ pureTy $ BaseTy tOut
    where (t1', t2', tOut) = binOpType binop
  -- TODO: check index set constraint
  ScalarUnOp IndexAsInt _ -> return $ pureTy IntTy
  ScalarUnOp unop ty -> eq (BaseTy ty') ty >> return (pureTy (BaseTy outTy))
    where (ty', outTy) = unOpType unop
  -- -- TODO: check vspace constraints
  VSpaceOp ty VZero        -> inClass VSpace ty >> return (pureTy ty)
  VSpaceOp ty (VAdd e1 e2) -> inClass VSpace ty >> eq ty e1 >> eq ty e2 >> return (pureTy ty)
  Cmp _  ty   a b -> eq ty a >> eq ty b >> return (pureTy BoolTy)
  Select ty p a b -> eq ty a >> eq ty b >> eq BoolTy p >> return (pureTy ty)
  RunReader r ~(Pi (RefTy r') (Effect row tailVar, a)) -> do
    row' <- popRow eq row (Reader, RefTy r)
    eq r r'
    return (Effect row' tailVar, a)
  RunWriter ~(Pi (RefTy w) (Effect row tailVar, a)) -> do
    row' <- popRow eq row (Writer, RefTy w)
    return (Effect row' tailVar, PairTy a w)
  RunState s ~(Pi (RefTy s') (Effect row tailVar, a)) -> do
    row' <- popRow eq row (State, RefTy s)
    eq s s'
    return (Effect row' tailVar, PairTy a s)
  Linearize (Pi a (eff, b)) -> do
    eq noEffect eff
    return $ pureTy $ a --> PairTy b (a --@ b)
  Transpose (Pi a (eff, b)) -> do
    eq noEffect eff
    return $ pureTy $ b --@ a
  IntAsIndex ty i  -> eq IntTy i >> return (pureTy ty)
  IdxSetSize _     -> return $ pureTy IntTy
  NewtypeCast ty _ -> return $ pureTy ty
  FFICall _ argTys ansTy argTys' ->
    zipWithM_ eq argTys argTys' >> return (pureTy ansTy)
  Inject (TC (IndexRange ty _ _)) -> return $ pureTy ty
  _ -> error $ "Unexpected primitive type: " ++ pprint op

traverseConType :: MonadError Err m
                     => PrimConType
                     -> (Type      -> Type -> m ()) -- add equality constraint
                     -> (Kind      -> Type -> m ()) -- add kind constraint
                     -> (ClassName -> Type -> m ()) -- add class constraint
                     -> m Type
traverseConType con eq kindIs _ = case con of
  Lit l    -> return $ BaseTy $ litType l
  ArrayLit (Array (shape, b) _) -> return $ ArrayTy shape b
  Lam l eff (Pi a (eff', b)) -> do
    checkExtends eff eff'
    return $ ArrowType l (Pi a (eff, b))
  SumCon t' t s -> case s of
    Left _  -> return $ TC $ SumType (t, t')
    Right _ -> return $ TC $ SumType (t', t)
  RecCon r -> return $ RecTy r
  AFor n a -> return $ TabTy n a
  AGet (ArrayTy _ b) -> return $ BaseTy b  -- TODO: check shape matches AFor scope
  AsIdx n e -> eq e (BaseTy IntType) >> return n
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
  Not             -> (BoolType, BoolType)
  FNeg            -> (RealType, RealType)
  IntToReal       -> (IntType, RealType)
  BoolToInt       -> (BoolType, IntType)
  UnsafeIntToBool -> (IntType, BoolType)
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
flattenType (FixedIntRange _ _) = [(IntType, [])]
flattenType (TabTy (FixedIntRange low high) a) =
    [(b, (high - low):shape) | (b, shape) <- flattenType a]
-- temporary hack. TODO: fix
flattenType (TabTy _ a) = [(b, 0:shape) | (b, shape) <- flattenType a]
flattenType (TC con) = case con of
  BaseType b  -> [(b, [])]
  RecType r -> concat $ map flattenType $ toList r
  _ -> error $ "Unexpected type: " ++ show con
flattenType ty = error $ "Unexpected type: " ++ show ty

extendClassEnv :: [TyQual] -> TypeM a -> TypeM a
extendClassEnv qs m = do
  r <- ask
  let classEnv = fold [monMapSingle v [c] | TyQual (v:>_) c <- qs]
  lift $ extendR classEnv $ runReaderT m r

indexSetConcreteSize :: Type -> Maybe Int
indexSetConcreteSize ty = case ty of
  FixedIntRange low high -> Just $ high - low
  TC (BaseType BoolType) -> Just 2
  RecTy r -> liftM product $ mapM indexSetConcreteSize $ toList r
  _ -> Nothing

maybeApplyPi :: (HasVars t, PiAbstractable t, MonadError Err m) => (PiType t) -> Maybe Atom -> m t
maybeApplyPi piTy maybeAtom
  | isDependentType piTy = do
      case maybeAtom of
        Just atom -> return $ applyPi piTy atom
        Nothing -> throw TypeErr $ "Dependent argument must be fully-reduced"
  | otherwise = return b  where (Pi _ b) = piTy


makePi :: PiAbstractable t => Var -> t -> PiType t
makePi v@(_:>a) b = Pi a $ abstractDepType v 0 b

applyPi :: PiAbstractable t => PiType t -> Atom -> t
applyPi (Pi _ b) x = instantiateDepType 0 x b

isDependentType :: (HasVars t, PiAbstractable t) => PiType t -> Bool
isDependentType (Pi _ b) = usesPiVar b
  where
    usesPiVar t = dummyVar `isin` freeVars (instantiateDepType 0 (Var dummyVar) t)
    dummyVar ="__dummy_type_variable_that_should_be_unused!" :> UnitTy

class PiAbstractable t where
  instantiateDepType :: Int -> Atom -> t -> t
  abstractDepType :: Var -> Int -> t -> t

instance PiAbstractable Type where
  instantiateDepType d x ty = case ty of
    TypeVar _ -> ty
    ArrowType m (Pi a (e, b)) -> ArrowType (recur m) $
      Pi (recur a) (instantiateDepType (d+1) x e, instantiateDepType (d+1) x b)
    TabType (Pi a b) -> TabType $ Pi (recur a) (instantiateDepType (d+1) x b)
    Forall tbs cs body -> Forall tbs cs $ recur body
    Effect row tailVar -> Effect row' tailVar
      where row' = fold [ (lookupDBVar v :>()) @> (eff, recur ann)
                        | (v, (eff, ann)) <- envPairs row]
    TC con -> TC $ fmapTyCon con recur (subst (env, mempty))
      where env = (DeBruijn d :>()) @> L x
    NoAnn -> NoAnn
    TypeAlias _ _ -> error "Shouldn't have type alias left"
    where
      recur ::Type -> Type
      recur = instantiateDepType d x

      lookupDBVar :: Name -> Name
      lookupDBVar v = case v of
        DeBruijn i | i == d -> v'  where (Var (v':>_)) = x
        _                   -> v

  abstractDepType v d ty = case ty of
    TypeVar _ -> ty
    ArrowType m (Pi a (e, b)) -> ArrowType (recur m) $
      Pi (recur a) (abstractDepType v (d+1) e, abstractDepType v (d+1) b)
    TabType (Pi a b) -> TabType $ Pi (recur a) (abstractDepType v (d+1) b)
    Forall tbs cs body -> Forall tbs cs $ recur body
    Effect row tailVar -> Effect row' tailVar
      where row' = fold [ (substWithDBVar v' :>()) @> (eff, recur ann)
                        | (v', (eff, ann)) <- envPairs row]
    TC con -> TC $ fmapTyCon con recur (subst (env, mempty))
      where env = v @> L (Var (DeBruijn d :> varAnn v))
    NoAnn -> NoAnn
    TypeAlias _ _ -> error "Shouldn't have type alias left"
    where
      recur ::Type -> Type
      recur = abstractDepType v d

      substWithDBVar :: Name -> Name
      substWithDBVar v' | varName v == v' = DeBruijn d
                        | otherwise       = v'

instance PiAbstractable EffectiveType where
  instantiateDepType d x (eff, b) = ( instantiateDepType d x eff
                                    , instantiateDepType d x b)
  abstractDepType v d (eff, b) = ( abstractDepType v d eff
                                 , abstractDepType v d b)

-- === linearity ===

type Spent = Env ()
newtype LinCheckM a = LinCheckM
  { runLinCheckM :: (ReaderT (Env Spent) (Either Err)) (a, (Spent, Env Spent)) }

runLinCheck :: LinCheckM a -> Except ()
runLinCheck m = void $ runReaderT (runLinCheckM m) mempty

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
  App Lin    fun x -> tensCheck (check fun) (check x)
  App NonLin fun x -> tensCheck (check fun) (withoutLin (check x))
  For _ (FLamExpr _ body) -> checkLinFExpr body
  TabGet x i -> tensCheck (check x) (withoutLin (check i))
  RunReader r (FLamExpr ~(RecLeaf v) body) -> do
    ((), spent) <- captureSpent $ checkLinFExpr r
    extendR (v @> spent) $ checkLinFExpr body
  RunWriter (FLamExpr ~(RecLeaf v) body) -> do
    ((), spent) <- captureEffSpent v $ checkLinFExpr body
    spend spent
  PrimEffect ref m -> case m of
    MAsk -> checkLinVar ref'
    MTell x -> do
      ((), s) <- captureSpent $ checkLinFExpr x
      spendEff ref' s
    _ -> void $ withoutLin $ traverseExpr e pure check checkLinFLam
    where (Just (Var ref')) = fromAtomicFExpr ref
  _ -> void $ withoutLin $ traverseExpr e pure check checkLinFLam
  where check = checkLinFExpr

checkLinCon :: PrimCon Type FExpr FLamExpr -> LinCheckM ()
checkLinCon e = case e of
  Lam NonLin _ lam -> checkLinFLam lam
  Lam Lin    _ (FLamExpr p body) -> do
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

getPatName :: Pat -> Name
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
