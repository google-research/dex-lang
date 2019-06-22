module Type (TypeEnv, checkTyped, getType, litType, unpackExists,
             builtinType, BuiltinType (..)) where

import Control.Monad
import Control.Monad.Except (liftEither)
import Control.Monad.Reader

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
                     checkEq "Get" a (recur (Var ie))
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

checkShadow :: BinderP a -> TypeM ()
checkShadow (v :> _) = do
  env <- ask
  if v `isin` env
    then throw CompilerErr $ pprint v ++ " shadowed"
    else return ()

unpackExists :: Type -> Var -> Except Type
unpackExists (Exists body) v = return $ instantiateTVs [TypeVar v] body
unpackExists ty _ = throw TypeErr $ "Can't unpack " ++ pprint ty

litType :: LitVal -> BaseType
litType v = case v of
  IntLit  _ -> IntType
  RealLit _ -> RealType
  StrLit  _ -> StrType

data BuiltinType = BuiltinType [Kind] [Type] Type

builtinType :: Builtin -> BuiltinType
builtinType builtin = case builtin of
  IAdd     -> ibinOpType
  ISub     -> ibinOpType
  IMul     -> ibinOpType
  Pow      -> ibinOpType
  FAdd     -> fbinOpType
  FSub     -> fbinOpType
  FMul     -> fbinOpType
  FDiv     -> fbinOpType
  Exp      -> realUnOpType
  Log      -> realUnOpType
  Sqrt     -> realUnOpType
  Sin      -> realUnOpType
  Cos      -> realUnOpType
  Tan      -> realUnOpType
  Fold     -> BuiltinType [TyKind, idxSetKind] [j ==> (a --> a), a] a
  Iota     -> BuiltinType [idxSetKind] [] (a ==> int)
  Range    -> BuiltinType [] [int] (Exists unitTy)
  Hash     -> BuiltinType [] [int, int] int
  Randint  -> BuiltinType [] [int, int] int
  Rand     -> BuiltinType [] [int] real
  IntToReal -> BuiltinType [] [int] real
  Deriv     -> BuiltinType [TyKind, TyKind] [a --> b] (a --> tup [b, a --> b])
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
    tup xs = RecType (Tup xs)
