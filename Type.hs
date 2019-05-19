module Type (TypeEnv, checkTyped, getType, litType, unpackExists,
             patType, builtinType) where

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

checkTyped :: Decl -> TopPass TypeEnv Decl
checkTyped decl = decl <$ case decl of
  TopLet b@(Bind _ ty) expr -> do
    ty' <- check expr
    assertEq ty ty' ""
    putEnv $ asLEnv (bind b)
  TopUnpack b@(Bind _ ty) iv expr -> do
    exTy <- check expr
    ty' <- liftEither $ unpackExists exTy iv
    assertEq ty ty' ""
    putEnv $ FullEnv (bind b) (bind $ Bind iv IdxSetKind)
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
    Let p bound body -> do checkTy (patType p)
                           checkShadows p
                           checkEq "Let" (patType p) (recur bound)
                           recurWith p body
    Lam p body -> do checkTy (patType p)
                     checkShadows p
                     liftM (ArrType (patType p)) (recurWith p body)
    For i body -> do checkTy (binderVal i)
                     checkShadows [i]
                     liftM (TabType (binderVal i)) (recurWith [i] body)
    App e arg  -> do ArrType a b <- recur e
                     checkEq "App" a (recur arg)
                     return b
    Get e ie   -> do TabType a b <- recur e
                     checkEq "Get" a (recur (Var ie))
                     return b
    RecCon r   -> liftM RecType $ traverse recur r
    TLam vks body -> do t <- recurWithT vks body
                        let (vs, kinds) = unzip [(v, k) | Bind v k <- vks]
                        checkShadows vks
                        return $ Forall kinds (abstractTVs vs t)
    TApp fexpr ts   -> do Forall _ body <- recur fexpr
                          mapM checkTy ts
                          return $ instantiateTVs ts body
    Unpack b tv _ body -> do  -- TODO: check bound expression!
      let tb = Bind tv IdxSetKind
      checkShadows [b]
      checkShadows [tb]
      extendWith (asTEnv (bind tb)) $ do
        checkTy (binderVal b)
        extendWith (asLEnv (bind b)) (recur body)

  where
    checkEq :: String -> Type -> TypeM Type -> TypeM ()
    checkEq s ty getTy =
      if check then do ty' <- getTy
                       assertEq ty ty' ("Unexpected type in " ++ s)
               else return ()

    checkTy :: Type -> TypeM ()
    checkTy _ = return () -- TODO: check kind and unbound type vars
    recur = getType' check
    recurWith  bs = extendWith (asLEnv (bindFold bs)) . recur
    recurWithT bs = extendWith (asTEnv (bindFold bs)) . recur

    lookupLVar :: Var -> TypeM Type
    lookupLVar v = asks ((! v) . lEnv)

checkShadows :: Traversable f => f (GenBinder a) -> TypeM ()
checkShadows bs = mapM_ (traverse checkShadow . binderVars) bs

-- TODO: using mapM doesn't check that pattern vars don't shadow each other
checkShadow :: Var -> TypeM ()
checkShadow v = do
    env <- ask
    if v `isin` lEnv env || v `isin` tEnv env
      then throw CompilerErr $ pprint v ++ " shadowed"
      else return ()

unpackExists :: Type -> Var -> Except Type
unpackExists (Exists body) v = return $ instantiateTVs [TypeVar v] body
unpackExists ty _ = throw TypeErr $ "Can't unpack " ++ pprint ty

patType :: RecTree Binder -> Type
patType (RecTree r) = RecType (fmap patType r)
patType (RecLeaf (Bind _ t)) = t

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
  Range    -> int --> Exists (i ==> unitTy)
  Hash     -> tup [int, int] --> int
  Randint  -> tup [int, int] --> int
  Rand     -> int --> real
  IntToReal -> int --> real
  where
    ibinOpType    = tup [int, int] --> int
    fbinOpType    = tup [real, real] --> real
    realUnOpType = real --> real
    i = BoundTVar 0
    foldType = Forall [TyKind, TyKind, IdxSetKind] $
                 tup [tup [b,a] --> b, b, k==>a] --> b
    a = BoundTVar 0
    b = BoundTVar 1
    k = BoundTVar 2
    int  = BaseType IntType
    real = BaseType RealType
    tup xs = RecType (Tup xs)
