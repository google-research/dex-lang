module Type (TypeEnv, checkTyped, getType, litType, unpackExists,
             patType, builtinType) where

import Control.Monad
import Control.Monad.Except (throwError)
import Control.Monad.Reader
import Control.Monad.State
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

checkTyped :: Decl -> TopMonadPass TypeEnv ()
checkTyped decl = case decl of
  TopLet (v,ty) expr -> do
    ty' <- check expr
    liftExcept $ assertEq ty ty' ""
    put $ newFullEnv [(v,ty)] []
  TopUnpack (v,ty) iv expr -> do
    exTy <- check expr
    ty' <- liftExcept $ unpackExists exTy iv
    liftExcept $ assertEq ty ty' ""
    put $ newFullEnv [(v,ty)] [(iv, IdxSetKind)]
  EvalCmd NoOp -> put mempty >> return ()
  EvalCmd (Command cmd expr) -> check expr >> put mempty
  where
    check :: Expr -> TopMonadPass TypeEnv Type
    check expr = do env <- get
                    liftExcept $ evalTypeM env (getType' True expr)

getType :: FullEnv Type a -> Expr -> Type
getType (FullEnv lenv _) expr =
  ignoreExcept $ evalTypeM (FullEnv lenv mempty) $ getType' False expr

evalTypeM :: TypeEnv -> TypeM a -> Except a
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
  Hash     -> tup [int, int] --> int
  Randint  -> tup [int, int] --> int
  Rand     -> int --> real
  where
    binOpType    = tup [int, int] --> int
    realUnOpType = real --> real
    iotaType = int --> Exists (i ==> int)
    i = TypeVar (BoundVar 0)
    foldType = Forall [TyKind, TyKind, IdxSetKind] $
                 tup [tup [b,a] --> b, b, k==>a] --> b
    a = TypeVar (BoundVar 0)
    b = TypeVar (BoundVar 1)
    k = TypeVar (BoundVar 2)
    int  = BaseType IntType
    real = BaseType RealType
    tup xs = RecType (Tup xs)
