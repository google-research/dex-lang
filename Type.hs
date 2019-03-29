module Type (checkExpr, getType, litType, builtinType, recTreeAsType) where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Data.Foldable (toList)

import Syntax
import Env
import Record
import Util

type TempVar = Int
type TypeEnv = FullEnv Type VarName
type TypeM a = ReaderT TypeEnv (StateT TempVar (Either Err)) a

-- TODO: avoid temp namespace collisions with tag
getType :: FullEnv Type a -> Expr -> Type
getType env expr =
  ignoreExcept $ evalTypeM (asTypeEnv env) $ getType' False expr

checkExpr :: FullEnv Type a -> Expr -> Type -> Except ()
checkExpr env expr reqTy = do
  ty <- evalTypeM (asTypeEnv env) (getType' True expr)
  assertEq reqTy ty ("Unexpected type of expression " ++ show expr)

evalTypeM ::  TypeEnv -> TypeM a -> Except a
evalTypeM env m = evalStateT (runReaderT m env) 0

asTypeEnv :: FullEnv Type a -> TypeEnv
asTypeEnv (FullEnv lenv tenv) = FullEnv lenv mempty


getType' :: Bool -> Expr -> TypeM Type
getType' check expr = case expr of
    Lit c        -> return $ litType c
    Var v        -> lookupLVar v
    Builtin b    -> return $ builtinType b
    Let p bound body -> do p' <- traverse subTyBVs p
                           checkEq (recTreeAsType p') (recur bound)
                           recurWith (toList p') body
    Lam p body -> do p' <- traverse subTyBVs p
                     let a' = recTreeAsType p'
                     liftM (ArrType a') (recurWith (toList p') body)
    For a body -> do { a' <- subTyBVs a; liftM (TabType a') (recurWith [a'] body) }
    App e arg  -> do ArrType a b <- recur e
                     checkEq a (recur arg)
                     return b
    Get e ie   -> do TabType a b <- recur e
                     checkEq a (recur (Var ie))
                     return b
    RecCon r   -> liftM RecType $ traverse recur r
    TLam kinds body -> do vs <- mapM (const fresh) kinds
                          t <- recurWithT vs body
                          return $ Forall kinds $ abstractTVs vs t
    TApp fexpr ts   -> do Forall _ body <- recur fexpr
                          ts' <- mapM subTyBVs ts
                          return $ instantiateTVs ts' body
    BuiltinApp FoldDeFunc ts expr -> error "fold"
    BuiltinApp b _ [arg] -> case builtinType b of
      Forall _ body -> error "not implemented"
      t -> do t' <- subTyBVs t
              let (a, out) = deFuncType (numArgs b) t'
              checkEq a (recur arg)
              return out
    Unpack t bound body -> do
        v <- fresh
        let updateT = setTEnv (addBVar v)
        t' <- local updateT (subTyBVs t)
        let updateL = setLEnv (addBVar t')
        local (updateL . updateT) (recur body)

  where
    checkEq :: Type -> TypeM Type -> TypeM ()
    checkEq ty getTy =
      if check then do ty' <- getTy
                       liftExcept $ assertEq ty ty' "Unexpected type"
               else return ()

    recur = getType' check
    recurWith  ts = local (setLEnv (addBVars ts)) . recur
    recurWithT vs = local (setTEnv (addBVars vs)) . recur

    lookupLVar :: Var -> TypeM Type
    lookupLVar v = asks ((! v) . lEnv)

    subTyBVs :: Type -> TypeM Type
    subTyBVs ty = do bvNames <- asks (bVars . tEnv)
                     return $ instantiateTVs (map (TypeVar . FV) bvNames) ty

    fresh :: TypeM VarName
    fresh = do i <- get
               put (i + 1)
               return (TempVar i)

recTreeAsType :: RecTree Type -> Type
recTreeAsType (RecTree r) = RecType (fmap recTreeAsType r)
recTreeAsType (RecLeaf t) = t

litType :: LitVal -> Type
litType v = BaseType $ case v of
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
    a = TypeVar (BV 0)
    b = TypeVar (BV 1)
    i = TypeVar (BV 0)
    j = TypeVar (BV 1)
    k = TypeVar (BV 2)
    int = BaseType IntType
    real = BaseType RealType

nestedPairs :: [Type] -> Type
nestedPairs [] = unitTy
nestedPairs (x:xs) = RecType $ posRecord [x, nestedPairs xs]

unitTy = RecType $ posRecord []

deFuncType :: Int -> Type -> (Type, Type)
deFuncType n t = let (args, result) = naryComponents n t
                 in (nestedPairs (reverse args), result)

naryComponents :: Int -> Type -> ([Type], Type)
naryComponents 0 ty = ([], ty)
naryComponents n (ArrType a rhs) = let (args, result) = naryComponents (n-1) rhs
                                   in (a:args, result)
