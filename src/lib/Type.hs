-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module Type (TypeEnv, checkTyped, getType, getAtomType, litType, unpackExists,
             builtinType, BuiltinType (..), instantiateTVs, abstractTVs,
             checkNExpr, patType, tangentBunType, tangentBunNType) where
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
type LinInfo = Either Lin Spent
type TypeCheckEnv = FullEnv (SigmaType, LinInfo) Kind
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

getType :: FullEnv SigmaType a -> Expr -> Type
getType env expr =
  ignoreExcept $ addContext (pprint expr) $
     evalTypeM (fmap (L . (\ty -> (ty, Left NonLin)) . fromL) env) $ getType' expr

evalTypeM :: TypeCheckEnv -> TypeM a -> Except a
evalTypeM env m = liftM fst $ runCatT (runReaderT m env) mempty

getType' :: Expr -> TypeM Type
getType' expr = case expr of
    Lit c -> return $ BaseType (litType c)
    Var v ts -> do
      mapM_ checkTy ts
      x <- asks $ flip envLookup v
      case x of
        Just (L (Forall _ body, l)) -> do
          case l of
            Right s     -> mapM_ spendVar (envNames s)
            Left Lin    -> spendVar v
            Left NonLin -> return ()
          return $ instantiateTVs ts body
        _ -> throw CompilerErr $ "Lookup failed:" ++ pprint v
    PrimOp b ts args -> do
      mapM_ checkTy ts
      let BuiltinType _ (numLin, k) argTys ansTy = builtinType b
      let (ansTy':argTys') = map (instantiateTVs ts) (ansTy:argTys)
      let (linArgs, nlArgs) = splitAt numLin args
      argTys'' <- liftM2 (++) (traverse recur nlArgs) (checkProd k linArgs)
      assertEq argTys' argTys'' "Builtin"
      return ansTy'
    Decl decl body -> do
      env <- getTypeDecl decl
      extendR env (recur body)
    Lam NonLin p body -> do
      checkTy (patType p)
      checkShadowPat p
      liftM (ArrType NonLin (patType p)) (recurWithP NonLin p body)
    Lam Lin (RecLeaf b@(v:>ty)) body -> do
      checkTy ty
      checkShadow b
      (bodyTy, spent) <- scoped $ recurWithP Lin (RecLeaf b) body
      if v `isin` spent
        then return ()
        else throw LinErr $ "Variable never spent: " ++ pprint v
      extend $ spent `envDiff` (v@>())
      return $ ArrType Lin ty bodyTy
    Lam Lin _ _ -> throw NotImplementedErr "Linear lambda patterns"
    For p body -> do checkTy (patType p)
                     checkShadowPat p
                     liftM (TabType (patType p)) (recurWithP NonLin p body)
    App e arg  -> do
      ~(ArrType l a b) <- recur e
      a' <- do
        (a', spent) <- capture (recur arg)
        throwIf (not (isLinear l || null spent)) LinErr $
          "Nonlinear function consuming linear data: " ++ pprint (envNames spent)
        return a'
      assertEq a a' "App"
      return b
    Get e ie   -> do
      ~(TabType a b) <- recur e
      a' <- recur ie
      assertEq a a' "Get"
      return b
    RecCon k r -> liftM (RecType k) $ checkProd k r
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
    DerivAnnot e ann -> do
      ty <- recur e
      annTy <- recur ann
      assertEq (tangentBunType ty) annTy "deriv"
      return ty
    IdxLit _ _   -> error $ "IdxLit not implemented"   -- TODO
    Annot _ _    -> error $ "Annot not implemented"    -- TODO
    SrcAnnot _ _ -> error $ "SrcAnnot not implemented" -- TODO
  where
    recur = getType'
    recurWithP l p  = extendR (foldMap (asEnv (Left l)) p) . recur

    checkProd :: Traversable f => ProdKind -> f Expr -> TypeM (f Type)
    checkProd k xs = case k of
      Cart -> shareLinear recur xs
      Tens -> traverse    recur xs

spendVar :: Name -> TypeM ()
spendVar v = do
  spent <- look
  if v `isin` spent
    then throw LinErr $ "Variable already spent: " ++ pprint v
    else extend (v @> ())

isLinear :: Lin -> Bool
isLinear Lin    = True
isLinear NonLin = False

shareLinear :: Traversable f => (a -> TypeM b) -> f a -> TypeM (f b)
shareLinear f xs = do
  (ys, spents) <- liftM unzip' $ traverse (scoped . f) xs
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

getTypeDecl :: Decl -> TypeM TypeCheckEnv
getTypeDecl decl = case decl of
  LetMono p rhs -> do
    checkShadowPat p
    (ty, spent) <- scoped $ recur rhs
    assertEq (patType p) ty "LetMono"
    return (foldMap (asEnv (Right spent)) p)
  LetPoly b@(v:>ty) tlam -> do
    checkShadow b
    (ty', spent) <- scoped $ getTypeTLam tlam
    assertEq ty ty' "TLam"
    return $ v @> L (ty, Right spent)
  Unpack b tv _ -> do  -- TODO: check bound expression!
    -- TODO: check leaks
    let tb = tv :> idxSetKind
    checkShadow b
    checkShadow tb
    extendR (tbind tb) $ checkTy (binderAnn b)
    return (tbind tb <> asEnv (Left NonLin) b)
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

asEnv :: LinInfo -> Binder -> TypeCheckEnv
asEnv l (v:>ty) = v @> L (asSigma ty, l)

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
  Todo     -> nonLinBuiltin [TyKind] [] a
  Copy     -> nonLinBuiltin [TyKind] [a] a
  Scan     -> nonLinBuiltin [TyKind, TyKind, idxSetKind]
                          [a, k ==> (a --> pair a b)] (pair a (k==>b))
  IndexAsInt -> nonLinBuiltin [idxSetKind] [i] int
  IntAsIndex -> nonLinBuiltin [idxSetKind] [int] i
  Range    -> nonLinBuiltin [] [int] (Exists unitTy)
  BoolToInt -> nonLinBuiltin [] [bool] int
  IntToReal -> nonLinBuiltin [] [int] real
  -- TODO: this breaks for tuple or non-reals
  Linearize   -> nonLinBuiltin [TyKind, TyKind] [a --> b, a] (pair b (a --@ b))
  Transpose   -> nonLinBuiltin [TyKind, TyKind] [a --@ b] (b --@ a)
  VZero   -> nonLinBuiltin [TyKind] [] a
  VAdd    -> nonLinBuiltin [TyKind] [a, a] a
  VSingle -> nonLinBuiltin [TyKind, idxSetKind] [j, a] (j ==> a)
  VSum    -> nonLinBuiltin [TyKind, idxSetKind] [j ==> a] a
  Filter -> nonLinBuiltin [TyKind, idxSetKind]
              [a --> bool, j ==> a] (Exists (i==>a'))
    where a' = BoundTVar 1  -- under an extra binder
  FFICall n _ -> nonLinBuiltin kinds argTys retTy
    where kinds = take (n + 1) (repeat TyKind)
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

-- === Normalized IR ===

type NTypeEnv = FullEnv NType ()
type NTypeM a = ReaderT NTypeEnv (Either Err) a

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
    liftPass ctx m = do env <- look
                        liftExceptTop $ addContext ctx $ runReaderT m env

getNType :: NExpr -> NTypeM [NType]
getNType expr = case expr of
  NDecl decl body -> do
    env <- checkNDecl decl
    extendR env $ getNType body
  NScan b@(_:>i) bs xs body -> do
    checkNBinder b
    let carryTys = map binderAnn bs
    xs' <- mapM atomType xs
    mapM_ checkNBinder bs
    assertEq carryTys xs' "Scan arg"
    bodyTys <- extendR (nBinderEnv (b:bs)) (getNType body)
    let (carryTys', outTys) = splitAt (length bs) bodyTys
    assertEq carryTys carryTys' "Scan output"
    return $ carryTys ++ map (NTabType i) outTys
  NPrimOp Todo ts _ -> do
    mapM_ checkNTy ts
    return ts
  NPrimOp b ts xs -> do
    mapM_ checkNTy ts
    argTys'' <- mapM atomType xs
    assertEq (map fromLeaf argTys') argTys'' (pprint b) -- TODO: handle non-leaves
    return (toList ansTy')
    where
      BuiltinType _ _ argTys ansTy = builtinType b
      ts' = map nTypeToType ts
      ansTy':argTys' = map (typeToNType . instantiateTVs ts') (ansTy:argTys)
  NApp e xs -> do
    ~(NArrType as bs) <- atomType e
    as' <- mapM atomType xs
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
    ts <- getNType expr
    assertEq (map binderAnn bs) ts "Decl"
    return $ nBinderEnv bs
  NUnpack bs tv _ -> do  -- TODO: check bound expression!
    checkShadow (tv :> idxSetKind)
    extendR (tv @> T ()) $ mapM_ checkNBinder bs
    return $ nBinderEnv bs <> tv @> T ()

nBinderEnv :: [NBinder] -> NTypeEnv
nBinderEnv bs = foldMap (\(v:>ty) -> v @> L ty) bs

getAtomType :: NTypeEnv -> NAtom -> NType
getAtomType env atom = case runReaderT (atomType atom) env of
  Left err -> error $ pprint err
  Right x -> x

atomType :: NAtom -> NTypeM NType
atomType atom = case atom of
  NLit x -> return $ NBaseType (litType x)
  NVar v -> do
    x <- asks $ flip envLookup v
    case x of
      Just (L ty) -> return ty
      _ -> throw CompilerErr $ "Lookup failed:" ++ pprint v
  NGet e i -> do
    ~(NTabType a b) <- atomType e
    a' <- atomType i
    assertEq a a' "Get"
    return b
  NAtomicFor b body -> do
    checkNBinder b
    bodyTy <- extendR (nBinderEnv [b]) (atomType body)
    return $ NTabType (binderAnn b) bodyTy
  NLam bs body -> do
    mapM_ checkNBinder bs
    bodyTys <- extendR (nBinderEnv bs) (getNType body)
    return $ NArrType (map binderAnn bs) bodyTys
  NDeriv f -> do
    ty <- atomType f
    let [ty'] = tangentBunNType ty
    return ty'
  NDerivAnnot f ann -> do
    fTy <- atomType f
    annTy <- atomType ann
    assertEq (tangentBunNType fTy) [annTy] "deriv ann"
    return fTy

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
  ArrType _ a b -> RecLeaf $ NArrType (toList (recur a)) (toList (recur b))
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
  NArrType a b -> ArrType NonLin (RecType Cart (Tup (map recur a)))
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
  NArrType as bs -> [NArrType (foldMap recur as) (foldMap recur bs)]
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
