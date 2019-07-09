{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module Type (TypeEnv, checkTyped, getType, litType, unpackExists,
             builtinType, BuiltinType (..), instantiateTVs, abstractTVs,
             HasTypeVars, freeTyVars, subFreeTVs, checkNExpr) where
import Control.Monad
import Control.Monad.Except hiding (Except)
import Control.Monad.Reader
import Control.Monad.State (State, execState, modify)
import Control.Applicative (liftA, liftA2, liftA3)
import Data.List (elemIndex)
import Data.Foldable

import Syntax
import Env
import Record
import Pass
import PPrint
import Cat

type TypeEnv = FullEnv Type Kind
type TypeM a = ReaderT TypeEnv (Either Err) a

checkTyped :: TopDecl -> TopPass TypeEnv TopDecl
checkTyped decl = decl <$ case decl of
  TopDecl (Let b expr) -> do
    ty' <- check expr
    assertEq (binderAnn b) ty' ""
    putEnv $ lbind b
  TopDecl (Unpack b iv expr) -> do
    exTy <- check expr
    ty' <- liftEither $ unpackExists exTy iv
    assertEq (binderAnn b) ty' ""
    putEnv $ lbind b <> iv @> T idxSetKind
  EvalCmd NoOp -> return ()
  EvalCmd (Command _ expr) -> void $ check expr
  where
    check :: Expr -> TopPass TypeEnv Type
    check expr = do
      env <- getEnv
      liftEither $ addContext (pprint expr) $ evalTypeM env (getType' True expr)

getType :: FullEnv Type a -> Expr -> Type
getType env expr =
  ignoreExcept $ addContext (pprint expr) $
     evalTypeM (fmap (L . fromL) env) $ getType' False expr

evalTypeM :: TypeEnv -> TypeM a -> Except a
evalTypeM env m = runReaderT m env

getType' :: Bool -> Expr -> TypeM Type
getType' check expr = case expr of
    Lit c        -> return $ BaseType (litType c)
    Var v        -> lookupLVar v
    PrimOp b ts xs -> do
      mapM checkTy ts
      let BuiltinType kinds argTys ansTy = builtinType b
          ansTy':argTys' = map (instantiateTVs ts) (ansTy:argTys)
      zipWithM (checkEq "Builtin") argTys' (map recur xs)
      return ansTy'
    Decls decls body -> foldr getTypeDecl (recur body) decls
    Lam b body -> do checkTy (binderAnn b)
                     checkShadow b
                     liftM (ArrType (binderAnn b)) (recurWith b body)
    For i body -> do checkTy (binderAnn i)
                     checkShadow i
                     liftM (TabType (binderAnn i)) (recurWith i body)
    App e arg  -> do ArrType a b <- recur e
                     checkEq "App" a (recur arg)
                     return b
    Get e ie   -> do TabType a b <- recur e
                     checkEq "Get" a (recur ie)
                     return b
    RecCon r   -> liftM RecType $ traverse recur r
    RecGet e field -> do RecType r <- recur e
                         return $ recGet r field
    TabCon n ty xs -> do
      mapM_ (checkEq "table" ty . recur) xs
      return $ TabType (IdxSetLit n) ty
    TLam vks body -> do t <- recurWithT vks body
                        let (vs, kinds) = unzip [(v, k) | v :> k <- vks]
                        mapM_ checkShadow vks
                        return $ Forall kinds (abstractTVs vs t)
    TApp fexpr ts   -> do Forall _ body <- recur fexpr
                          mapM checkTy ts
                          return $ instantiateTVs ts body
  where
    getTypeDecl :: Decl -> TypeM a -> TypeM a
    getTypeDecl decl cont = case decl of
     Let b expr -> do
       checkTy (binderAnn b)
       checkShadow b
       checkEq "Let" (binderAnn b) (recur expr)
       extendR (lbind b) cont
     Unpack b tv _ -> do  -- TODO: check bound expression!
       -- TODO: check leaks
       let tb = tv :> idxSetKind
       checkShadow b
       checkShadow tb
       extendR (tbind tb) $ do
         checkTy (binderAnn b)
         extendR (lbind b) cont

    runCheck :: TypeM () -> TypeM ()
    runCheck m = if check then m else return ()

    checkEq :: String -> Type -> TypeM Type -> TypeM ()
    checkEq s ty getTy = runCheck $ do
      ty' <- getTy
      assertEq ty ty' ("Unexpected type in " ++ s)

    recur = getType' check
    recurWith  b  = extendR (lbind b) . recur
    recurWithT bs = extendR (foldMap tbind bs) . recur

    lookupLVar :: Var -> TypeM Type
    lookupLVar v = do
      x <- asks $ flip envLookup v
      case x of
        Nothing -> throw CompilerErr $ "Lookup failed:" ++ pprint v
        Just x' -> return $ fromL x'

    checkTy :: Type -> TypeM ()
    checkTy _ = return () -- TODO: check kind and unbound type vars

checkShadow :: (MonadError Err m, MonadReader (Env a) m) => BinderP b -> m ()
checkShadow (v :> _) = do
  env <- ask
  if v `isin` env
    then throw CompilerErr $ pprint v ++ " shadowed"
    else return ()

unpackExists :: Type -> Var -> Except Type
unpackExists (Exists body) v = return $ instantiateTVs [TypeVar v] body
unpackExists ty _ = throw CompilerErr $ "Can't unpack " ++ pprint ty

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
  ILT      -> BuiltinType [] [int, int] bool
  IGT      -> BuiltinType [] [int, int] bool
  Pow      -> ibinOpType
  FAdd     -> fbinOpType
  FSub     -> fbinOpType
  FMul     -> fbinOpType
  FDiv     -> fbinOpType
  FLT      -> BuiltinType [] [real, real] bool
  FGT      -> BuiltinType [] [real, real] bool
  Exp      -> realUnOpType
  Log      -> realUnOpType
  Sqrt     -> realUnOpType
  Sin      -> realUnOpType
  Cos      -> realUnOpType
  Tan      -> realUnOpType
  Scan     -> BuiltinType [TyKind, TyKind, idxSetKind]
                          [a, k ==> (a --> pair a b)] (pair a (k==>b))
  IndexAsInt -> BuiltinType [idxSetKind] [i] int
  Range    -> BuiltinType [] [int] (Exists unitTy)
  Hash     -> BuiltinType [] [int, int] int
  Randint  -> BuiltinType [] [int, int] int
  Rand     -> BuiltinType [] [int] real
  BoolToInt -> BuiltinType [] [bool] int
  IntToReal -> BuiltinType [] [int] real
  Deriv     -> BuiltinType [TyKind, TyKind] [a --> b] (a --> pair b (a --> b))
  Transpose -> BuiltinType [TyKind, TyKind] [a --> b] (b --> a)
  VZero   -> BuiltinType [TyKind] [] a
  VAdd    -> BuiltinType [TyKind] [a, a] a
  VSingle -> BuiltinType [TyKind, idxSetKind] [j, a] (j ==> a)
  VSum    -> BuiltinType [TyKind, idxSetKind] [j ==> a] a
  where
    ibinOpType    = BuiltinType [] [int , int ] int
    fbinOpType    = BuiltinType [] [real, real] real
    realUnOpType  = BuiltinType [] [real]       real
    i = BoundTVar 0
    a = BoundTVar 0
    b = BoundTVar 1
    j = BoundTVar 1
    k = BoundTVar 2
    int  = BaseType IntType
    real = BaseType RealType
    bool = BaseType BoolType
    pair x y = RecType (Tup [x, y])


-- The rest is type var manipulation (previously in Syntax.hs). Plan to remove
-- if we go to a scope-oriented zonkless system

instantiateTVs :: [Type] -> Type -> Type
instantiateTVs vs x = subAtDepth 0 sub x
  where sub depth tvar = case tvar of
                        Left v -> TypeVar v
                        Right i | i >= depth -> vs !! i
                                | otherwise -> BoundTVar i

abstractTVs :: [Var] -> Type -> Type
abstractTVs vs x = subAtDepth 0 sub x
  where sub depth tvar = case tvar of
                           Left v -> case elemIndex v vs of
                                       Nothing -> TypeVar v
                                       Just i  -> BoundTVar (depth + i)
                           Right i -> BoundTVar i

subAtDepth :: Int -> (Int -> Either Var Int -> Type) -> Type -> Type
subAtDepth d f ty = case ty of
    BaseType _    -> ty
    TypeVar v     -> f d (Left v)
    ArrType a b   -> ArrType (recur a) (recur b)
    TabType a b   -> TabType (recur a) (recur b)
    RecType r     -> RecType (fmap recur r)
    Exists body   -> Exists (recurWith 1 body)
    Forall kinds body -> (Forall kinds) (recurWith (length kinds) body)
    IdxSetLit _   -> ty
    BoundTVar n   -> f d (Right n)
  where recur        = subAtDepth d f
        recurWith d' = subAtDepth (d + d') f

freeTyVars :: HasTypeVars a => a -> [Var]
freeTyVars x = execState (subFreeTVs collectVars x) []
  where collectVars :: Var -> State [Var] Type
        collectVars v = modify (v :) >> return (TypeVar v)

subFreeTVs :: (HasTypeVars a,  Applicative f) => (Var -> f Type) -> a -> f a
subFreeTVs = subFreeTVsBVs []

class HasTypeVars a where
  subFreeTVsBVs :: Applicative f => [Var] -> (Var -> f Type) -> a -> f a

instance (HasTypeVars a, HasTypeVars b) => HasTypeVars (a,b) where
  subFreeTVsBVs bvs f (x, y) = liftA2 (,) (subFreeTVsBVs bvs f x)
                                          (subFreeTVsBVs bvs f y)

instance HasTypeVars Type where
  subFreeTVsBVs bvs f ty = case ty of
      BaseType _    -> pure ty
      TypeVar v | v `elem` bvs -> pure ty
                | otherwise    -> f v
      ArrType a b   -> liftA2 ArrType (recur a) (recur b)
      TabType a b   -> liftA2 TabType (recur a) (recur b)
      RecType r     -> liftA RecType (traverse recur r)
      Exists body   -> liftA Exists (recur body)
      Forall kinds body -> liftA (Forall kinds) (recur body)
      IdxSetLit _   -> pure ty
      BoundTVar _   -> pure ty
    where recur = subFreeTVsBVs bvs f

instance HasTypeVars Expr where
  subFreeTVsBVs bvs f expr = case expr of
      Lit c -> pure $ Lit c
      Var v -> pure $ Var v
      PrimOp b ts xs -> liftA2 (PrimOp b) (traverse recurTy ts)
                                                  (traverse recur xs)
      Decls [] final -> recur final
      Decls (decl:decls) final -> case decl of
        Let b bound ->
          liftA3 (\b' bound' body' -> wrapDecls [Let b' bound'] body')
                 (recurB b) (recur bound) (recur body)
        Unpack b tv bound ->
          liftA3 (\b' bound' body' -> wrapDecls [Unpack b' tv bound'] body')
                 (recurWithB [tv] b) (recur bound) (recurWith [tv] body)
        where body = Decls decls final
      Lam b body       -> liftA2 Lam (recurB b) (recur body)
      App fexpr arg    -> liftA2 App (recur fexpr) (recur arg)
      For b body       -> liftA2 For (recurB b) (recur body)
      Get e ie         -> liftA2 Get (recur e) (pure ie)
      RecCon r         -> liftA  RecCon (traverse recur r)
      RecGet e field   -> liftA (flip RecGet field) (recur e)
      TabCon n ty xs   -> liftA2 (TabCon n) (recurTy ty) (traverse recur xs)
      TLam bs expr      -> liftA  (TLam bs) (recurWith [v | v:>_ <- bs] expr)
      TApp expr ts      -> liftA2 TApp (recur expr) (traverse recurTy ts)
    where recur   = subFreeTVsBVs bvs f
          recurTy = subFreeTVsBVs bvs f
          recurB b = traverse recurTy b
          recurWith   vs = subFreeTVsBVs (vs ++ bvs) f
          recurWithTy vs = subFreeTVsBVs (vs ++ bvs) f
          recurWithB  vs b = traverse (recurWithTy vs) b

instance HasTypeVars Binder where
  subFreeTVsBVs bvs f b = traverse (subFreeTVsBVs bvs f) b

-- === Normalized IR ===

type NTypeEnv = FullEnv NType ()
type NTypeM a = ReaderT NTypeEnv (Either Err) a

checkNExpr :: NTopDecl -> TopPass NTypeEnv NTopDecl
checkNExpr topDecl = topDecl <$ case topDecl of
  NTopDecl decl -> do
    env <- liftPass $ checkNDecl decl
    putEnv env
  NEvalCmd NoOp -> return ()
  NEvalCmd (Command _ (_, tys, expr)) -> liftPass $ do
    tys' <- getNType expr
    assertEq tys tys' ""
  where
    liftPass :: NTypeM a -> TopPass NTypeEnv a
    liftPass m = do env <- getEnv
                    liftEither $ runReaderT m env

getNType :: NExpr -> NTypeM [NType]
getNType expr = case expr of
  NDecls [] final -> getNType final
  NDecls (decl:decls) final -> do
    env <- checkNDecl decl
    extendR env $ getNType (NDecls decls final)
  NFor b@(_:>i) body -> do
    checkNBinder b
    bodyTys <- extendR (nBinderEnv [b]) (getNType body)
    return $ map (NTabType i) bodyTys
  NPrimOp b ts xs -> do
    mapM_ checkNTy ts
    argTys'' <- mapM atomType xs
    assertEq (map fromLeaf argTys') argTys'' "" -- TODO: handle non-leaves
    return (toList ansTy')
    where
      BuiltinType _ argTys ansTy = builtinType b
      ts' = map nTypeToType ts
      ansTy':argTys' = map (typeToNType . instantiateTVs ts') (ansTy:argTys)
  NApp e xs -> do
    NArrType as bs <- atomType e
    as' <- mapM atomType xs
    assertEq as as' ""
    return bs
  NAtoms xs -> mapM atomType xs

checkNDecl :: NDecl -> NTypeM NTypeEnv
checkNDecl decl = case decl of
  NLet bs expr -> do
    mapM_ checkNBinder bs
    ts <- getNType expr
    assertEq (map binderAnn bs) ts ""
    return $ nBinderEnv bs
  NUnpack bs tv _ -> do  -- TODO: check bound expression!
    checkShadow (tv :> idxSetKind)
    extendR (tv @> T ()) $ mapM_ checkNBinder bs
    return $ nBinderEnv bs <> tv @> T ()

nBinderEnv :: [NBinder] -> NTypeEnv
nBinderEnv bs = foldMap (\(v:>ty) -> v @> L ty) bs

atomType :: NAtom -> NTypeM NType
atomType atom = case atom of
  NLit x -> return $ NBaseType (litType x)
  NVar v -> do
    x <- asks $ flip envLookup v
    case x of
      Nothing -> throw CompilerErr $ "Lookup failed:" ++ pprint v
      Just (L ty) -> return ty
  NGet e i -> do
    NTabType a b <- atomType e
    a' <- atomType i
    assertEq a a' "Get"
    return b
  -- AFor b body ->
  NLam bs body -> do
    mapM_ checkNBinder bs
    bodyTys <- extendR (nBinderEnv bs) (getNType body)
    return $ NArrType (map binderAnn bs) bodyTys

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
  TabType n ty -> fmap (NTabType (fromLeaf (recur n))) (recur ty)
  RecType r   -> RecTree $ fmap recur r
  Exists ty   -> RecLeaf $ NExists (toList (recur ty))
  BoundTVar n -> RecLeaf $ NBoundTVar n
  where recur = typeToNType

nTypeToType :: NType -> Type
nTypeToType ty = case ty of
  NBaseType b -> BaseType b
  NTypeVar v -> TypeVar v
