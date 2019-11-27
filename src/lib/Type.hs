-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module Type (TypeEnv, checkTyped, getType, getAtomType, litType, unpackExists,
             builtinType, BuiltinType (..), instantiateTVs, abstractTVs,
             checkNExpr, patType, tangentBunType, tangentBunNType, isPrintable,
             getNExprType) where
import Control.Monad
import Control.Monad.Except hiding (Except)
import Control.Monad.Reader
import Data.List (elemIndex)
import Data.Foldable

import Syntax
import Env
import Record
import Pass
import PPrint
import Cat

-- TODO: consider making linearity checking a separate pass?
type TypeEnv = FullEnv SigmaType Kind
type TypeCheckEnv = FullEnv (SigmaType, Spent) Kind
type Spent = Env ()
type TypeM a = ReaderT TypeCheckEnv (CatT Spent (Either Err)) a

checkTyped :: TopPass TopDecl TopDecl
checkTyped = TopPass $ \decl -> decl <$ case decl of
  TopDecl decl' -> do
    env <- liftTop (pprint decl') (getTypeDecl decl')
    extend env
  EvalCmd (Command TypeCheckInternal expr) -> do
    ty <- liftTop (pprint expr) (getType' expr)
    emitOutput $ TextOut $ pprint ty
  EvalCmd (Command _ expr) ->
    void $ liftTop (pprint expr) (getType' expr)

liftTop :: String -> TypeM a -> TopPassM TypeCheckEnv a
liftTop ctx m = do
  env <- look
  liftExceptTop $ addContext ctx $ evalTypeM env m

getType :: TypeEnv -> Expr -> Type
getType env expr = ignoreExcept $ addContext (pprint expr) $ evalTypeM env' $ getType' expr
  where
    env' = fmap addEmptySpent env
    addEmptySpent val = case val of L ty -> L (ty, mempty)
                                    T k  -> T k

evalTypeM :: TypeCheckEnv -> TypeM a -> Except a
evalTypeM env m = liftM fst $ runCatT (runReaderT m env) mempty

getType' :: Expr -> TypeM Type
getType' expr = case expr of
    Lit c -> return $ BaseType (litType c)
    Var v ts -> do
      mapM_ checkTy ts
      x <- asks $ flip envLookup v
      case x of
        Just (L (Forall kinds body, s)) -> do
          mapM_ spendVar (envNames s)
          zipWithM_ checkClassConstraints kinds ts
          return $ instantiateTVs ts body
        _ -> throw CompilerErr $ "Lookup failed:" ++ pprint v
    PrimOp b ts args -> do
      mapM_ checkTy ts
      zipWithM_ checkClassConstraints kinds ts
      argTys'' <- liftM2 (++) (checkNothingSpent $ traverse recur nlArgs)
                              (traverseProd k recur linArgs)
      assertEq argTys' argTys'' "Builtin"
      return ansTy'
      where
        BuiltinType kinds (numLin, k) argTys ansTy = builtinType b
        (ansTy':argTys') = map (instantiateTVs ts) (ansTy:argTys)
        (linArgs, nlArgs) = splitAt numLin args
    Decl decl body -> do
      env <- getTypeDecl decl
      extendR env (recur body)
    Lam NonLin p body -> do
      checkTy (patType p)
      checkShadowPat p
      liftM (ArrType NonLin (patType p)) (recurWithP mempty p body)
    Lam Lin p body -> do
      checkTy (patType p)
      checkShadowPat p
      v <- getPatName p
      bodyTy <- checkSpent v (pprint p) $ recurWithP (v@>()) p body
      return $ ArrType Lin (patType p) bodyTy
    For p body -> do
      checkIdxSet (patType p)
      checkTy (patType p)
      checkShadowPat p
      liftM (TabType (patType p)) (recurWithP mempty p body)
    App e arg  -> do
      ~(ArrType l a b) <- recur e
      a' <- case l of Lin    ->                     recur arg
                      NonLin -> checkNothingSpent $ recur arg
      assertEq a a' "App"
      return b
    Get e ie   -> do
      ~(TabType a b) <- recur e
      a' <- recur ie
      assertEq a a' "Get"
      return b
    RecCon k r -> liftM (RecType k) (traverseProd k recur r)
    TabCon ty xs -> do
      case ty of
        TabType _ bodyTy -> do
          xTys <- mapM recur xs
          mapM_ (\t -> assertEq bodyTy t "table")  xTys  -- TODO: check length too
          return ty
        _ -> throw CompilerErr $ "Expected a table type: " ++ pprint ty
    Pack e ty exTy -> do
      let (Exists exBody) = exTy
      rhsTy <- recur e
      assertEq (instantiateTVs [ty] exBody) rhsTy "Pack"
      return exTy
    IdxLit n i | 0 <= i && i < n -> return $ IdxSetLit n
               | otherwise -> throw TypeErr $ "Index out of bounds: "
                                ++ pprint i ++ " of " ++ pprint n
    Annot _ _    -> error $ "Annot not implemented"    -- TODO
    SrcAnnot _ _ -> error $ "SrcAnnot not implemented" -- TODO
  where
    recur = getType'
    recurWithP s p  = extendR (foldMap (asEnv s) p) . recur

getTypeDecl :: Decl -> TypeM TypeCheckEnv
getTypeDecl decl = case decl of
  LetMono p rhs -> do
    checkShadowPat p
    (ty, spent) <- scoped $ recur rhs
    assertEq (patType p) ty "LetMono"
    return (foldMap (asEnv spent) p)
  LetPoly b@(v:>ty) tlam -> do
    checkShadow b
    (ty', spent) <- scoped $ getTypeTLam tlam
    assertEq ty ty' "TLam"
    return $ v @> L (ty, spent)
  Unpack b tv _ -> do  -- TODO: check bound expression!
    -- TODO: check leaks
    let tb = tv :> idxSet
    checkShadow b
    checkShadow tb
    extendR (tbind tb) $ checkTy (binderAnn b)
    return (tbind tb <> asEnv mempty b)
  TAlias _ _ -> error "Shouldn't have TAlias left"
  where
    recur = getType'

getTypeTLam :: TLam -> TypeM SigmaType
getTypeTLam (TLam tbs body) = do
  mapM_ checkShadow tbs
  ty <- extendR (foldMap tbind tbs) (getType' body)
  let (vs, kinds) = unzip [(v, k) | v :> k <- tbs]
  return $ Forall kinds (abstractTVs vs ty)

checkTy :: Type -> TypeM ()
checkTy _ = return () -- TODO: check kind and unbound type vars

checkShadow :: (MonadError Err m, MonadReader (Env a) m) => BinderP b -> m ()
checkShadow (v :> _) = do
  env <- ask
  if v `isin` env
    then throw CompilerErr $ pprint v ++ " shadowed"
    else return ()

checkShadowPat :: Traversable f => f (BinderP b) -> TypeM ()
checkShadowPat pat = mapM_ checkShadow pat -- TODO: check mutual shadows!

asEnv :: Spent -> Binder -> TypeCheckEnv
asEnv s (v:>ty) = v @> L (asSigma ty, s)

unpackExists :: Type -> Name -> Except Type
unpackExists (Exists body) v = return $ instantiateTVs [TypeVar v] body
unpackExists ty _ = throw CompilerErr $ "Can't unpack " ++ pprint ty

patType :: RecTree Binder -> Type
patType (RecLeaf (_:>ty)) = ty
patType (RecTree r) = RecType Cart $ fmap patType r

litType :: LitVal -> BaseType
litType v = case v of
  IntLit  _ -> IntType
  RealLit _ -> RealType
  StrLit  _ -> StrType
  BoolLit _ -> BoolType

-- BuiltinType represents types of the form
--     forall [_, _]. (_, _, _) --o (_,_,_) -> _
--  or forall [_, _]. (_: _: _) --o (_,_,_) -> _
type LinSpec = (Int, ProdKind)  -- Int is number of linear args
data BuiltinType = BuiltinType [Kind] LinSpec [Type] Type

noCon :: Kind
noCon = Kind []

idxSet :: Kind
idxSet = Kind [IdxSet]

vspace :: Kind
vspace = Kind [VSpace]

builtinType :: Builtin -> BuiltinType
builtinType builtin = case builtin of
  IAdd     -> ibinOpType
  ISub     -> ibinOpType
  IMul     -> ibinOpType
  Mod      -> ibinOpType
  ILT      -> nonLinBuiltin [] [int, int] bool
  IGT      -> nonLinBuiltin [] [int, int] bool
  Pow      -> ibinOpType
  FAdd     -> BuiltinType [] (2, Cart) [real, real] real
  FSub     -> fbinOpType
  FMul     -> BuiltinType [] (2, Tens) [real, real] real
  FDiv     -> fbinOpType
  FLT      -> nonLinBuiltin [] [real, real] bool
  FGT      -> nonLinBuiltin [] [real, real] bool
  Todo     -> nonLinBuiltin [noCon] [] a
  Copy     -> nonLinBuiltin [noCon] [a] a
  Scan     -> nonLinBuiltin [noCon, noCon, idxSet]
                          [a, k ==> (a --> pair a b)] (pair a (k==>b))
  IndexAsInt -> nonLinBuiltin [idxSet] [i] int
  IntAsIndex -> nonLinBuiltin [idxSet] [int] i
  Range    -> nonLinBuiltin [] [int] (Exists unitTy)
  BoolToInt -> nonLinBuiltin [] [bool] int
  IntToReal -> nonLinBuiltin [] [int] real
  -- TODO: this breaks for tuple or non-reals
  Linearize   -> nonLinBuiltin [vspace, vspace] [a --> b, a] (pair b (a --@ b))
  Transpose   -> BuiltinType [vspace, vspace] (2, Tens) [a --@ b, b] a
  VZero   -> nonLinBuiltin [vspace] [] a
  VAdd    -> nonLinBuiltin [vspace] [a, a] a
  VSingle -> nonLinBuiltin [vspace, idxSet] [j, a] (j ==> a)
  VSum    -> nonLinBuiltin [vspace, idxSet] [j ==> a] a
  Filter -> nonLinBuiltin [noCon, idxSet]
              [a --> bool, j ==> a] (Exists (i==>a'))
    where a' = BoundTVar 1  -- under an extra binder
  FFICall n _ -> nonLinBuiltin kinds argTys retTy
    where kinds = take (n + 1) (repeat noCon)
          retTy:argTys = take (n + 1) (map BoundTVar [0..])
  where
    ibinOpType    = nonLinBuiltin [] [int , int ] int
    fbinOpType    = nonLinBuiltin [] [real, real] real
    i = BoundTVar 0
    a = BoundTVar 0
    b = BoundTVar 1
    -- c = BoundTVar 2
    -- d = BoundTVar 3
    j = BoundTVar 1
    k = BoundTVar 2
    int  = BaseType IntType
    real = BaseType RealType
    bool = BaseType BoolType
    pair x y = RecType Cart (Tup [x, y])
    nonLinBuiltin kinds argTys ansTy = BuiltinType kinds (0, Cart) argTys ansTy

instantiateTVs :: [Type] -> Type -> Type
instantiateTVs vs x = subAtDepth 0 sub x
  where sub depth tvar =
          case tvar of
            Left v -> TypeVar v
            Right i | i >= depth -> if i' < length vs && i >= 0
                                      then vs !! i'
                                      else error $ "Bad index: "
                                             ++ show i' ++ " / " ++ pprint vs
                    | otherwise  -> BoundTVar i
              where i' = i - depth

abstractTVs :: [Name] -> Type -> Type
abstractTVs vs x = subAtDepth 0 sub x
  where sub depth tvar = case tvar of
                           Left v -> case elemIndex v vs of
                                       Nothing -> TypeVar v
                                       Just i  -> BoundTVar (depth + i)
                           Right i -> BoundTVar i

subAtDepth :: Int -> (Int -> Either Name Int -> Type) -> Type -> Type
subAtDepth d f ty = case ty of
    BaseType _    -> ty
    TypeVar v     -> f d (Left v)
    ArrType l a b -> ArrType l (recur a) (recur b)
    TabType a b   -> TabType (recur a) (recur b)
    RecType k r   -> RecType k (fmap recur r)
    Exists body   -> Exists (recurWith 1 body)
    IdxSetLit _   -> ty
    BoundTVar n   -> f d (Right n)
  where recur        = subAtDepth d f
        recurWith d' = subAtDepth (d + d') f


-- === Built-in type classes ===

checkClassConstraints :: Kind -> Type -> TypeM ()
checkClassConstraints (Kind cs) ty = mapM_ (flip checkClassConstraint ty) cs

checkClassConstraint :: ClassName -> Type -> TypeM ()
checkClassConstraint c ty = case c of
  VSpace -> checkVSpace ty
  IdxSet -> checkIdxSet ty
  _ -> error "Not implemented"

checkVSpace :: Type -> TypeM ()
checkVSpace ty = case ty of
  TypeVar v         -> checkVarClass VSpace v
  BaseType RealType -> return ()
  TabType _ a       -> checkVSpace a
  RecType _ r       -> mapM_ checkVSpace r
  _                 -> throw TypeErr $ " Not a vector space: " ++ pprint ty

checkIdxSet :: Type -> TypeM ()
checkIdxSet ty = case ty of
  TypeVar v   -> checkVarClass IdxSet v
  IdxSetLit _ -> return ()
  RecType _ r -> mapM_ checkIdxSet r
  _           -> throw TypeErr $ " Not a valid index set: " ++ pprint ty

checkVarClass :: ClassName -> Name -> TypeM ()
checkVarClass c v = do
  maybeKind <- asks $ flip envLookup v
  case maybeKind of
    Just (T (Kind cs)) ->
      unless (c `elem` cs) $ throw TypeErr $ " Type variable \""  ++ pprint v ++
                                             "\" not in class: " ++ pprint c
    _ -> throw CompilerErr $ "Lookup of kind failed:" ++ pprint v

-- === Normalized IR ===

type NTypeEnv = FullEnv (NType, Spent) ()
type NTypeM a = ReaderT NTypeEnv (CatT Spent (Either Err)) a

checkNExpr ::TopPass NTopDecl NTopDecl
checkNExpr = TopPass $ \topDecl -> topDecl <$ case topDecl of
  NTopDecl decl -> do
    env <- liftPass (pprint decl) $ checkNDecl decl
    extend env
  NEvalCmd (Command _ (_, tys, expr)) -> liftPass ctx $ do
    tys' <- getNType expr
    assertEq tys tys' "NExpr command"
    where ctx = pprint tys ++ "\n" ++ pprint expr
  where
    liftPass :: String -> NTypeM a -> TopPassM NTypeEnv a
    liftPass ctx m = do
      env <- look
      liftM fst $ liftExceptTop $ addContext ctx $
        runCatT (runReaderT m env) mempty

getNExprType :: FullEnv NType () -> NExpr -> [NType]
getNExprType env expr =
  fst $ ignoreExcept $ runCatT (runReaderT (getNType expr) env') mempty
  where
    env' = fmap addEmptySpent env
    addEmptySpent val = case val of L ty -> L (ty, mempty)
                                    T k  -> T k

getNType :: NExpr -> NTypeM [NType]
getNType expr = case expr of
  NDecl decl body -> do
    env <- checkNDecl decl
    extendR env $ getNType body
  NScan b@(_:>i) bs xs body -> do
    checkNBinder b
    let carryTys = map binderAnn bs
    xs' <- atomTypes xs
    mapM_ checkNBinder bs
    assertEq carryTys xs' "Scan arg"
    bodyTys <- extendR (nBinderEnv mempty (b:bs)) (getNType body)
    let (carryTys', outTys) = splitAt (length bs) bodyTys
    assertEq carryTys carryTys' "Scan output"
    return $ carryTys ++ map (NTabType i) outTys
  NPrimOp Todo ts _ -> do
    mapM_ checkNTy ts
    return ts
  NPrimOp b ts xs -> do
    mapM_ checkNTy ts
    argTys'' <- liftM2 (++) (traverseProd k atomType xsLin)
                            (checkNothingSpent $ mapM atomType xsNonLin)
    assertEq (map fromLeaf argTys') argTys'' (pprint b) -- TODO: handle non-leaves
    return (toList ansTy')
    where
      BuiltinType _ (numLin, k) argTys ansTy = builtinType b
      ts' = map nTypeToType ts
      (ansTy':argTys') = map (typeToNType . instantiateTVs ts') (ansTy:argTys)
      (xsLin, xsNonLin) = splitAt numLin xs
  NApp e xs -> do
    ~(NArrType l as bs) <- atomType e
    -- TODO: use cartesian/tensor information from function type
    as' <- case l of Lin    ->                     atomTypes xs
                     NonLin -> checkNothingSpent $ atomTypes xs
    assertEq as as' "App"
    return bs
  NAtoms xs -> mapM atomType xs
  NTabCon n elemTys rows -> do
    rowTys <- mapM getNType rows
    mapM_ (\ts -> assertEq elemTys ts "Tab constructor") rowTys
    return $ map (NTabType n) elemTys

checkNDecl :: NDecl -> NTypeM NTypeEnv
checkNDecl decl = case decl of
  NLet bs expr -> do
    mapM_ checkNBinder bs
    (ts, s) <- scoped $ getNType expr
    assertEq (map binderAnn bs) ts "Decl"
    return $ nBinderEnv s bs
  NUnpack bs tv _ -> do  -- TODO: check bound expression!
    checkShadow (tv :> idxSet)
    extendR (tv @> T ()) $ mapM_ checkNBinder bs
    return $ nBinderEnv mempty bs <> tv @> T ()

nBinderEnv :: Spent -> [NBinder] -> NTypeEnv
nBinderEnv s bs = foldMap (\(v:>ty) -> v @> L (ty, s)) bs

getAtomType :: FullEnv NType () -> NAtom -> NType
getAtomType env atom =
  case runCatT (runReaderT (atomType atom) env') mempty of
    Left err -> error $ pprint err
    Right (x,_) -> x
  where
    env' = fmap addSpent env
    addSpent val = case val of L ty -> L (ty, mempty)
                               T k  -> T k
atomType :: NAtom -> NTypeM NType
atomType atom = case atom of
  NLit x -> return $ NBaseType (litType x)
  NVar v -> do
    x <- asks $ flip envLookup v
    case x of
      Just (L (ty, s)) -> do
        mapM_ spendVar (envNames s)
        return ty
      _ -> throw CompilerErr $ "Lookup failed:" ++ pprint v
  NGet e i -> do
    ~(NTabType a b) <- atomType e
    a' <- atomType i
    assertEq a a' "Get"
    return b
  NAtomicFor b body -> do
    checkNBinder b
    bodyTy <- extendR (nBinderEnv mempty [b]) (atomType body)
    return $ NTabType (binderAnn b) bodyTy
  NLam NonLin bs body -> do
    mapM_ checkNBinder bs
    bodyTys <- extendR (nBinderEnv mempty bs) (getNType body)
    return $ NArrType NonLin (map binderAnn bs) bodyTys
  NLam Lin bs body -> do
    mapM_ checkNBinder bs
    v <- getPatName bs
    let env = nBinderEnv (v@>()) bs
    bodyTys <- checkSpent v (pprint bs) $ extendR env (getNType body)
    return $ NArrType Lin (map binderAnn bs) bodyTys

atomTypes :: [NAtom] -> NTypeM [NType]
atomTypes xs = traverseProd Cart atomType xs

checkNTy :: NType -> NTypeM ()
checkNTy _ = return () -- TODO!

checkNBinder :: NBinder -> NTypeM ()
checkNBinder b = do
  checkNTy (binderAnn b)
  checkShadow b

typeToNType :: Type -> RecTree NType
typeToNType ty = case ty of
  BaseType b  -> RecLeaf $ NBaseType b
  TypeVar v   -> RecLeaf $ NTypeVar v
  ArrType l a b -> RecLeaf $ NArrType l (toList (recur a)) (toList (recur b))
  TabType a b -> fmap (NTabType (fromLeaf (recur a))) (recur b)
  RecType _ r -> RecTree $ fmap recur r
  Exists body -> RecLeaf $ NExists (toList (recur body))
  BoundTVar n -> RecLeaf $ NBoundTVar n
  IdxSetLit n -> RecLeaf $ NIdxSetLit n
  where recur = typeToNType

nTypeToType :: NType -> Type
nTypeToType ty = case ty of
  NBaseType b -> BaseType b
  NTypeVar v -> TypeVar v
  NIdxSetLit n -> IdxSetLit n
  NArrType l a b -> ArrType l (RecType Cart (Tup (map recur a)))
                              (RecType Cart (Tup (map recur b)))
  NTabType a b -> TabType (recur a) (recur b)
  NExists _    -> error $ "NExists not implemented"    -- TODO
  NBoundTVar _ -> error $ "NBoundTVar not implemented" -- TODO
  where recur = nTypeToType

tangentBunNType :: NType -> [NType]
tangentBunNType ty = case ty of
  NBaseType b -> case b of RealType -> [ty, ty]
                           _ -> [ty]
  NTypeVar _ -> [ty]  -- can only be an index set
  NArrType l as bs -> [NArrType l (foldMap recur as) (foldMap recur bs)]
  NTabType n a -> map (NTabType n) (recur a)
  NExists ts -> [NExists $ foldMap recur ts]
  NIdxSetLit _ -> [ty]
  NBoundTVar _ -> [ty]
  where recur = tangentBunNType

tangentBunType :: Type -> Type
tangentBunType ty = case ty of
  BaseType b -> case b of RealType -> pair ty ty
                          _ -> ty
  ArrType l a b -> ArrType l (recur a) (recur b)
  _ -> error $ "Don't know bundle type for: " ++ pprint ty
  where
    recur = tangentBunType
    pair x y = RecType Cart $ Tup [x, y]

-- TODO: replace with a more general typeclass-like system
isPrintable :: Type -> Bool
isPrintable ty = case ty of
  BaseType _    -> True
  TypeVar _     -> True -- TODO: lookup var and check
  ArrType _ _ _ -> False
  TabType a b   -> recur a && recur b
  RecType _ r   -> all recur (toList r)
  Exists _      -> True
  IdxSetLit _   -> True
  BoundTVar _   -> error "Type should be closed"
  where recur = isPrintable

-- === utils for working with linearity ===

spendVar :: (MonadError Err m, MonadCat Spent m) => Name -> m ()
spendVar v = do
  spent <- look
  when (v `isin` spent) $ throw LinErr $ "Variable already spent: " ++ pprint v
  extend (v @> ())

checkSpent :: (MonadError Err m, MonadCat Spent m) =>
                Name -> String -> m a -> m a
checkSpent v vStr m = do
  (ans, spent) <- scoped m
  unless  (v `isin` spent) $ throw LinErr $ "Variables never spent: " ++ vStr
  extend $ spent `envDiff` (v@>())
  return ans

checkNothingSpent :: (MonadError Err m, MonadCat Spent m) => m a -> m a
checkNothingSpent m = do
  (ans, spent) <- scoped m
  unless (null spent) $ throw LinErr $
    "Nonlinear function consuming linear data: " ++ pprint (envNames spent)
  return ans

getPatName :: (MonadError Err m, Traversable f) => f (BinderP b) -> m Name
getPatName p = case toList p of
  []  -> throw LinErr $
           "Empty patterns not allowed for linear lambda (for silly reasons)"
  (v:>_):_ -> return v

traverseProd :: (MonadError Err m, MonadCat Spent m, Traversable f) =>
                  ProdKind -> (a -> m b) -> f a -> m (f b)
traverseProd k f xs = case k of
  Cart -> shareLinear $ fmap f xs
  Tens -> traverse f xs

shareLinear :: (MonadError Err m, MonadCat Spent m, Traversable f) =>
                 f (m a) -> m (f a)
shareLinear actions = do
  (ys, spents) <- liftM unzip' $ traverse scoped actions
  case getConsensus spents of
    Right Nothing -> return ()
    Right (Just spent) -> extend spent
    Left (s1, s2) -> throw LinErr $
      "Different vars consumed by product: " ++ pprint (envNames s1)
                                   ++ " vs " ++ pprint (envNames s2)
  return ys
  where
    unzip' x = (fmap fst x, fmap snd x)

getConsensus :: (Eq a, Traversable f) => f a -> Either (a,a) (Maybe a)
getConsensus xs = foldr foldBody (Right Nothing) xs
  where
    foldBody x state = case state of
      Left e -> Left e
      Right Nothing -> Right (Just x)
      Right (Just x') | x == x' -> Right (Just x')
                      | otherwise -> Left (x, x')
