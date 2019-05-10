module Type (TypeEnv, checkTyped, getType, litType, unpackExists,
             patType, builtinType) where

import Control.Monad
import Control.Monad.Except (liftEither)
import Control.Monad.Reader
import Control.Monad.State

import Syntax
import Env
import Record
import Pass
import PPrint

type TypeEnv = FullEnv Type Kind
type TypeM a = ReaderT TypeEnv (Either Err) a

checkTyped :: Decl -> TopPass TypeEnv Decl
checkTyped decl = decl <$ case decl of
  TopLet (v,ty) expr -> do
    ty' <- check expr
    liftEither $ assertEq ty ty' ""
    putEnv $ newFullEnv [(v,ty)] []
  TopUnpack (v,ty) iv expr -> do
    exTy <- check expr
    ty' <- liftEither $ unpackExists exTy iv
    liftEither $ assertEq ty ty' ""
    putEnv $ newFullEnv [(v,ty)] [(iv, IdxSetKind)]
  EvalCmd NoOp -> return ()
  EvalCmd (Command cmd expr) -> void $ check expr
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
    Let p bound body -> do checkTy (patType p)
                           mapM (checkShadowL . fst) p
                           checkEq "Let" (patType p) (recur bound)
                           recurWith p body
    Lam p body -> do checkTy (patType p)
                     mapM (checkShadowL . fst) p
                     liftM (ArrType (patType p)) (recurWith p body)
    For i body -> do checkTy (snd i)
                     checkShadowL (fst i)
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
                        mapM checkShadowT vs
                        return $ Forall kinds (abstractTVs vs t)
    TApp fexpr ts   -> do Forall _ body <- recur fexpr
                          mapM checkTy ts
                          return $ instantiateTVs ts body
    Unpack v tv bound body -> do
        checkShadowT tv
        let updateTEnv = setTEnv (addV (tv, IdxSetKind))
        local updateTEnv (checkTy (snd v))
        local (setLEnv (addV v) . updateTEnv) (recur body)

  where
    checkEq :: String -> Type -> TypeM Type -> TypeM ()
    checkEq s ty getTy =
      if check then do ty' <- getTy
                       liftEither $ assertEq ty ty' ("Unexpected type in " ++ s)
               else return ()

    checkTy :: Type -> TypeM ()
    checkTy ty = return () -- TODO: check kind and unbound type vars
    recur = getType' check
    recurWith  vs = local (setLEnv (addVs vs)) . recur
    recurWithT vs = local (setTEnv (addVs vs)) . recur

    checkShadowL = checkShadow (asks lEnv)
    checkShadowT = checkShadow (asks tEnv)

    checkShadow :: TypeM (Env a) -> Var -> TypeM ()
    checkShadow getEnv v = do
      env <- getEnv
      if v `isin` env then throw CompilerErr $ pprint v ++ " shadowed"
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
  Iota     -> iotaType
  Hash     -> tup [int, int] --> int
  Randint  -> tup [int, int] --> int
  Rand     -> int --> real
  IntToReal -> int --> real
  where
    ibinOpType    = tup [int, int] --> int
    fbinOpType    = tup [real, real] --> real
    realUnOpType = real --> real
    iotaType = int --> Exists (i ==> int)
    i = BoundTVar 0
    foldType = Forall [TyKind, TyKind, IdxSetKind] $
                 tup [tup [b,a] --> b, b, k==>a] --> b
    a = BoundTVar 0
    b = BoundTVar 1
    k = BoundTVar 2
    int  = BaseType IntType
    real = BaseType RealType
    tup xs = RecType (Tup xs)
