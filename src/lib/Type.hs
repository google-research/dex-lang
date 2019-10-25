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
import Data.Text.Prettyprint.Doc

import Syntax
import Env
import Record
import Pass
import PPrint
import Cat

type TypeEnv = FullEnv SigmaType Kind
type TypeM a = ReaderT TypeEnv (Either Err) a

checkTyped :: TopPass TopDecl TopDecl
checkTyped = TopPass $ \decl -> decl <$ case decl of
  TopDecl decl' -> do
    env <- liftTop (pprint decl') (getTypeDecl True decl')
    extend env
  EvalCmd (Command _ expr) -> void $ liftTop (pprint expr) (getType' True expr)

liftTop :: String -> TypeM a -> TopPassM TypeEnv a
liftTop ctx m = do
  env <- look
  liftExceptTop $ addContext ctx $ evalTypeM env m

getType :: FullEnv SigmaType a -> Expr -> Type
getType env expr =
  ignoreExcept $ addContext (pprint expr) $
     evalTypeM (fmap (L . fromL) env) $ getType' False expr

evalTypeM :: TypeEnv -> TypeM a -> Except a
evalTypeM env m = runReaderT m env

getType' :: Bool -> Expr -> TypeM Type
getType' check expr = case expr of
    Lit c -> return $ BaseType (litType c)
    Var v ts -> do
      mapM_ checkTy ts
      Forall _ body <- lookupLVar v
      return $ instantiateTVs ts body
    PrimOp b ts xs -> do
      mapM_ checkTy ts
      let BuiltinType _ argTys ansTy = builtinType b
          ansTy':argTys' = map (instantiateTVs ts) (ansTy:argTys)
      zipWithM_ (checkEq "Builtin") argTys' (map recur xs)
      return ansTy'
    Decl decl body -> do env <- getTypeDecl check decl
                         extendR env (recur body)
    Lam p body -> do checkTy (patType p)
                     checkShadowPat p
                     liftM (ArrType (patType p)) (recurWithP p body)
    For p body -> do checkTy (patType p)
                     checkShadowPat p
                     liftM (TabType (patType p)) (recurWithP p body)
    App e arg  -> do ~(ArrType a b) <- recur e
                     checkEq "App" a (recur arg)
                     return b
    Get e ie   -> do ~(TabType a b) <- recur e
                     checkEq "Get" a (recur ie)
                     return b
    RecCon r   -> liftM RecType $ traverse recur r
    TabCon ty xs -> do
      case ty of
        TabType _ bodyTy -> do
          mapM_ (checkEq "table" bodyTy . recur) xs  -- TODO: check length too
          return ty
        _ -> throw CompilerErr $ "Expected a table type: " ++ pprint ty
    Pack e ty exTy -> do
      let (Exists exBody) = exTy
      checkEq "Pack" (instantiateTVs [ty] exBody) (recur e)
      return exTy
    DerivAnnot e ann -> do
      ty <- recur e
      checkEq "deriv" (tangentBunType ty) (recur ann)
      return ty
    IdxLit _ _   -> error $ "IdxLit not implemented"   -- TODO
    Annot _ _    -> error $ "Annot not implemented"    -- TODO
    SrcAnnot _ _ -> error $ "SrcAnnot not implemented" -- TODO
  where
    checkEq = checkEq' check
    recur = getType' check
    recurWithP p  = extendR (foldMap asEnv p) . recur

    lookupLVar :: Name -> TypeM SigmaType
    lookupLVar v = do
      x <- asks $ flip envLookup v
      case x of
        Nothing -> throw CompilerErr $ "Lookup failed:" ++ pprint v
        Just x' -> return $ fromL x'

getTypeDecl :: Bool -> Decl -> TypeM TypeEnv
getTypeDecl check decl = case decl of
  LetMono p rhs -> do
    checkShadowPat p
    checkEq "LetMono" (patType p) (recur rhs)
    return (foldMap asEnv p)
  LetPoly b@(v:>ty) tlam -> do
    checkShadow b
    checkEq' check "TLam" ty $ getTypeTLam check tlam
    return $ v @> L ty
  Unpack b tv _ -> do  -- TODO: check bound expression!
    -- TODO: check leaks
    let tb = tv :> idxSetKind
    checkShadow b
    checkShadow tb
    extendR (tbind tb) $ checkTy (binderAnn b)
    return (tbind tb <> asEnv b)
  TAlias _ _ -> error "Shouldn't have TAlias left"
  where
    checkEq = checkEq' check
    recur = getType' check

getTypeTLam :: Bool -> TLam -> TypeM SigmaType
getTypeTLam check (TLam tbs body) = do
  mapM_ checkShadow tbs
  ty <- extendR (foldMap tbind tbs) (getType' check body)
  let (vs, kinds) = unzip [(v, k) | v :> k <- tbs]
  return $ Forall kinds (abstractTVs vs ty)

checkTy :: Type -> TypeM ()
checkTy _ = return () -- TODO: check kind and unbound type vars

runCheck :: Bool -> TypeM () -> TypeM ()
runCheck check m = if check then m else return ()

checkEq' :: (Pretty a, Eq a) => Bool -> String -> a -> TypeM a -> TypeM ()
checkEq' check s ty getTy = runCheck check $ do
  ty' <- getTy
  assertEq ty ty' ("Unexpected type in " ++ s)

checkShadow :: (MonadError Err m, MonadReader (Env a) m) => BinderP b -> m ()
checkShadow (v :> _) = do
  env <- ask
  if v `isin` env
    then throw CompilerErr $ pprint v ++ " shadowed"
    else return ()

checkShadowPat :: Traversable f => f (BinderP b) -> TypeM ()
checkShadowPat pat = mapM_ checkShadow pat -- TODO: check mutual shadows!

asEnv :: Binder -> TypeEnv
asEnv (v:>ty) = v @> L (asSigma ty)

unpackExists :: Type -> Name -> Except Type
unpackExists (Exists body) v = return $ instantiateTVs [TypeVar v] body
unpackExists ty _ = throw CompilerErr $ "Can't unpack " ++ pprint ty

patType :: RecTree Binder -> Type
patType (RecLeaf (_:>ty)) = ty
patType (RecTree r) = RecType $ fmap patType r

litType :: LitVal -> BaseType
litType v = case v of
  IntLit  _ -> IntType
  RealLit _ -> RealType
  StrLit  _ -> StrType
  BoolLit _ -> BoolType

data BuiltinType = BuiltinType [Kind] [Type] Type

builtinType :: Builtin -> BuiltinType
builtinType builtin = case builtin of
  IAdd     -> ibinOpType
  ISub     -> ibinOpType
  IMul     -> ibinOpType
  Mod      -> ibinOpType
  ILT      -> BuiltinType [] [int, int] bool
  IGT      -> BuiltinType [] [int, int] bool
  Pow      -> ibinOpType
  FAdd     -> fbinOpType
  FSub     -> fbinOpType
  FMul     -> fbinOpType
  FDiv     -> fbinOpType
  FLT      -> BuiltinType [] [real, real] bool
  FGT      -> BuiltinType [] [real, real] bool
  Todo     -> BuiltinType [TyKind] [] a
  Copy     -> BuiltinType [TyKind] [a] a
  Scan     -> BuiltinType [TyKind, TyKind, idxSetKind]
                          [a, k ==> (a --> pair a b)] (pair a (k==>b))
  IndexAsInt -> BuiltinType [idxSetKind] [i] int
  IntAsIndex -> BuiltinType [idxSetKind] [int] i
  Range    -> BuiltinType [] [int] (Exists unitTy)
  BoolToInt -> BuiltinType [] [bool] int
  IntToReal -> BuiltinType [] [int] real
  -- TODO: this breaks for tuple or non-reals
  Deriv       -> BuiltinType [TyKind, TyKind] [a --> b] (pair a a --> pair b b)
  PartialEval -> BuiltinType [TyKind, TyKind, TyKind, TyKind]
                   [a --> b --> pair c d] (a --> pair c (b --> d))
  Transpose   -> BuiltinType [TyKind, TyKind] [a --> b] (b --> a)
  VZero   -> BuiltinType [TyKind] [] a
  VAdd    -> BuiltinType [TyKind] [a, a] a
  VSingle -> BuiltinType [TyKind, idxSetKind] [j, a] (j ==> a)
  VSum    -> BuiltinType [TyKind, idxSetKind] [j ==> a] a
  Filter -> BuiltinType [TyKind, idxSetKind]
              [a --> bool, j ==> a] (Exists (i==>a'))
    where a' = BoundTVar 1  -- under an extra binder
  FFICall n _ -> BuiltinType kinds argTys retTy
    where kinds = take (n + 1) (repeat TyKind)
          retTy:argTys = take (n + 1) (map BoundTVar [0..])
  where
    ibinOpType    = BuiltinType [] [int , int ] int
    fbinOpType    = BuiltinType [] [real, real] real
    i = BoundTVar 0
    a = BoundTVar 0
    b = BoundTVar 1
    c = BoundTVar 2
    d = BoundTVar 3
    j = BoundTVar 1
    k = BoundTVar 2
    int  = BaseType IntType
    real = BaseType RealType
    bool = BaseType BoolType
    pair x y = RecType (Tup [x, y])


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
    ArrType a b   -> ArrType (recur a) (recur b)
    TabType a b   -> TabType (recur a) (recur b)
    RecType r     -> RecType (fmap recur r)
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
  NPrimOp b ts xs -> do
    mapM_ checkNTy ts
    argTys'' <- mapM atomType xs
    assertEq (map fromLeaf argTys') argTys'' (pprint b) -- TODO: handle non-leaves
    return (toList ansTy')
    where
      BuiltinType _ argTys ansTy = builtinType b
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
  ArrType a b -> RecLeaf $ NArrType (toList (recur a)) (toList (recur b))
  TabType a b -> fmap (NTabType (fromLeaf (recur a))) (recur b)
  RecType r   -> RecTree $ fmap recur r
  Exists body -> RecLeaf $ NExists (toList (recur body))
  BoundTVar n -> RecLeaf $ NBoundTVar n
  IdxSetLit n -> RecLeaf $ NIdxSetLit n
  where recur = typeToNType

nTypeToType :: NType -> Type
nTypeToType ty = case ty of
  NBaseType b -> BaseType b
  NTypeVar v -> TypeVar v
  NIdxSetLit n -> IdxSetLit n
  NArrType a b -> ArrType (RecType (Tup (map recur a)))
                          (RecType (Tup (map recur b)))
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
  ArrType a b -> ArrType (recur a) (recur b)
  _ -> error $ "Don't know bundle type for: " ++ pprint ty
  where
    recur = tangentBunType
    pair x y = RecType $ Tup [x, y]
