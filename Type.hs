module Type (TypeEnv, checkTyped, getType, litType, unpackExists,
             builtinType) where

import Control.Monad
import Control.Monad.Except (liftEither)
import Control.Monad.Reader

import Syntax
import Env
import Record
import Pass
import PPrint

type TypeEnv = FullEnv Type Kind
type TypeM a = ReaderT TypeEnv (Either Err) a

checkTyped :: TopDecl -> TopPass TypeEnv TopDecl
checkTyped decl = decl <$ case decl of
  TopLet b expr -> do
    ty' <- check expr
    assertEq (binderAnn b) ty' ""
    putEnv $ asLEnv (bind b)
  TopUnpack b iv expr -> do
    exTy <- check expr
    ty' <- liftEither $ unpackExists exTy iv
    assertEq (binderAnn b) ty' ""
    putEnv $ FullEnv (bind b) (iv @> IdxSetKind)
  EvalCmd NoOp -> return ()
  EvalCmd (Command _ expr) -> void $ check expr
  where
    check :: Expr -> TopPass TypeEnv Type
    check expr = do
      env <- getEnv
      liftEither $ addContext (pprint expr) $ evalTypeM env (getType' True expr)

getType :: FullEnv Type a -> Expr -> Type
getType (FullEnv lenv _) expr =
  ignoreExcept $ evalTypeM (FullEnv lenv mempty) $ getType' False expr

evalTypeM :: TypeEnv -> TypeM a -> Except a
evalTypeM env m = runReaderT m env

getType' :: Bool -> Expr -> TypeM Type
getType' check expr = case expr of
    Lit c        -> return $ BaseType (litType c)
    Var v        -> lookupLVar v
    Builtin b    -> return $ builtinType b
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
       extendWith (asLEnv (bind b)) cont
     Unpack b tv _ -> do  -- TODO: check bound expression!
       -- TODO: check leaks
       let tb = tv :> IdxSetKind
       checkShadow b
       checkShadow tb
       extendWith (asTEnv (bind tb)) $ do
         checkTy (binderAnn b)
         extendWith (asLEnv (bind b)) cont

    checkEq :: String -> Type -> TypeM Type -> TypeM ()
    checkEq s ty getTy =
      if check then do ty' <- getTy
                       assertEq ty ty' ("Unexpected type in " ++ s)
               else return ()

    recur = getType' check
    recurWith  b  = extendWith (asLEnv (bind b)) . recur
    recurWithT bs = extendWith (asTEnv (bindFold bs)) . recur

    lookupLVar :: Var -> TypeM Type
    lookupLVar v = asks ((! v) . lEnv)

    checkTy :: Type -> TypeM ()
    checkTy _ = return () -- TODO: check kind and unbound type vars

checkShadow :: BinderP a -> TypeM ()
checkShadow (v :> _) = do
  env <- ask
  if v `isin` lEnv env || v `isin` tEnv env
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

builtinType :: Builtin -> Type
builtinType builtin = case builtin of
  Add      -> ibinOpType
  Sub      -> ibinOpType
  Mul      -> ibinOpType
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
  Fold     -> foldType
  Iota     -> Forall [IdxSetKind] (a ==> int)
  Range    -> int --> Exists unitTy
  Hash     -> tup [int, int] --> int
  Randint  -> tup [int, int] --> int
  Rand     -> int --> real
  IntToReal -> int --> real
  where
    ibinOpType    = tup [int, int] --> int
    fbinOpType    = tup [real, real] --> real
    realUnOpType = real --> real
    i = BoundTVar 0
    foldType = Forall [TyKind, IdxSetKind] $
                 tup [j ==> (a --> a), a] --> a
    a = BoundTVar 0
    b = BoundTVar 1
    j = BoundTVar 1
    k = BoundTVar 2
    int  = BaseType IntType
    real = BaseType RealType
    tup xs = RecType (Tup xs)
