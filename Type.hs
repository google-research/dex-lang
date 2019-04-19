module Type (TypeEnv, checkExpr, getType, litType, unpackExists,
             patType, builtinType, builtinNaryTy, nestedPairs) where

import Control.Monad
import Control.Monad.Except (throwError)
import Control.Monad.Reader
import Data.Foldable (toList)

import Syntax
import Env
import Record
import Util
import Pass
import Fresh
import PPrint

type TypeEnv = FullEnv Type Kind
type TypeM a = ReaderT TypeEnv (Either Err) a

getType :: FullEnv Type a -> Expr -> Type
getType (FullEnv lenv _) expr =
  ignoreExcept $ evalTypeM (FullEnv lenv mempty) $ getType' False expr

checkExpr :: TypeEnv -> Expr -> Except Type
checkExpr env expr = addErrMsg msg $ evalTypeM env (getType' True expr)
  where msg = "\nExpression:\n" ++ pprint expr

evalTypeM ::  TypeEnv -> TypeM a -> Except a
evalTypeM env m = runReaderT m env

getType' :: Bool -> Expr -> TypeM Type
getType' check expr = case expr of
    Lit c        -> return $ BaseType (litType c)
    Var v        -> do env <- ask
                       lookupLVar v
    Builtin b    -> return $ builtinType b
    Let p bound body -> do checkTy (patType p)
                           checkEq "Let" (patType p) (recur bound)
                           recurWith p body
    Lam p body -> do checkTy (patType p)
                     liftM (ArrType (patType p)) (recurWith p body)
    For i body -> do checkTy (snd i)
                     liftM (TabType (snd i)) (recurWith [i] body)
    App e arg  -> do ArrType a b <- recur e
                     checkEq "App" a (recur arg)
                     return b
    Get e ie   -> do TabType a b <- recur e
                     checkEq "Get" a (recur (Var ie))
                     return b
    RecCon r   -> liftM RecType $ traverse recur r
    TLam vks body -> do t <- recurWithT vks body
                        let (vs, kinds) = unzip vks
                        return $ Forall kinds (abstractTVs vs t)
    TApp fexpr ts   -> do Forall _ body <- recur fexpr
                          mapM checkTy ts
                          return $ instantiateTVs ts body
    BuiltinApp (FoldDeFunc p expr) ts arg -> return $ BaseType IntType -- TODO!
    BuiltinApp b ts arg -> case builtinType b of
      Forall _ body -> error "not implemented"
      t -> do let (a, out) = deFuncType (numArgs b) t
              checkEq "BuiltinApp" a (recur arg)
              return out
    Unpack v tv bound body -> do
        checkNoShadow tv
        let updateTEnv = setTEnv (addV (tv, IdxSetKind))
        local updateTEnv (checkTy (snd v))
        local (setLEnv (addV v) . updateTEnv) (recur body)

  where
    checkEq :: String -> Type -> TypeM Type -> TypeM ()
    checkEq s ty getTy =
      if check then do ty' <- getTy
                       liftExcept $ assertEq ty ty' ("Unexpected type in " ++ s)
               else return ()

    checkTy :: Type -> TypeM ()
    checkTy ty = return () -- TODO: check kind and unbound type vars
    recur = getType' check
    recurWith  vs = local (setLEnv (addVs vs)) . recur
    recurWithT vs = local (setTEnv (addVs vs)) . recur

    checkNoShadow :: Var -> TypeM ()
    checkNoShadow v = do
      tenv <- asks tEnv
      if v `isin` tenv then throw CompilerErr $ show v ++ " shadowed"
                       else return ()

    lookupLVar :: Var -> TypeM Type
    lookupLVar v = asks ((! v) . lEnv)

unpackExists :: Type -> Var -> Except Type
unpackExists (Exists body) v = return $ instantiateTVs [TypeVar v] body
unpackExists ty _ = throw TypeErr $ "Can't unpack " ++ pprint ty

patType :: RecTree (a, Type) -> Type
patType (RecTree r) = RecType (fmap patType r)
patType (RecLeaf (_, t)) = t

litType :: LitVal -> BaseType
litType v = case v of
  IntLit  _ -> IntType
  RealLit _ -> RealType
  StrLit  _ -> StrType

builtinType :: Builtin -> Type
builtinType builtin = case builtin of
  Add      -> binOpType
  Sub      -> binOpType
  Mul      -> binOpType
  Pow      -> binOpType
  Exp      -> realUnOpType
  Log      -> realUnOpType
  Sqrt     -> realUnOpType
  Sin      -> realUnOpType
  Cos      -> realUnOpType
  Tan      -> realUnOpType
  Fold     -> foldType
  Iota     -> iotaType
  Doubleit -> int --> int
  Hash     -> int --> int --> int
  Rand     -> int --> real
  Randint  -> int --> int --> int
  where
    binOpType    = int --> int --> int
    realUnOpType = real --> real
    foldType = Forall [TyKind, TyKind, IdxSetKind] $
                   (b --> a --> b) --> b --> (k ==> a) --> b
    iotaType = int --> Exists (i ==> int)
    a = TypeVar (BoundVar 0)
    b = TypeVar (BoundVar 1)
    i = TypeVar (BoundVar 0)
    j = TypeVar (BoundVar 1)
    k = TypeVar (BoundVar 2)
    int = BaseType IntType
    real = BaseType RealType

nestedPairs :: [Type] -> Type
nestedPairs = recur . reverse
  where recur []     = RecType (Tup [])
        recur (x:xs) = RecType (Tup [recur xs, x])


builtinNaryTy :: Builtin -> ([Type], Type)
builtinNaryTy b = naryComponents (numArgs b) (builtinType b)


deFuncType :: Int -> Type -> (Type, Type)
deFuncType n t = let (args, result) = naryComponents n t
                 in (nestedPairs args, result)

naryComponents :: Int -> Type -> ([Type], Type)
naryComponents 0 ty = ([], ty)
naryComponents n (ArrType a rhs) = let (args, result) = naryComponents (n-1) rhs
                                   in (a:args, result)
