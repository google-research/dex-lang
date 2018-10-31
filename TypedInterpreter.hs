{-# LANGUAGE GADTs #-}
-- module TypedInterpreter where

import Prelude hiding (lookup)
import qualified Data.Map.Strict as M

type Table a b = M.Map a b

data Term = Lit Int
          | Var Int
          | Lam RawType Term
          | App Term Term
               deriving (Show)

data RawType = RIntType
             | RArrType RawType RawType
                 deriving (Show)

data TTerm e t where
  TLit :: Int -> TTerm e Int
  TVar :: TIdx e t -> TTerm e t
  TLam :: Ty a -> TTerm (a,e) b -> TTerm e (a -> b)
  TApp :: TTerm e (a -> b) -> TTerm e a -> TTerm e b

data Ty t where
  IntType :: Ty Int
  ArrType :: Ty a -> Ty b -> Ty (a -> b)
  TabType :: Ty a -> Ty b -> Ty (Table a b)

data Typed a where
  Typed :: Ty t -> a t -> Typed a

data SomeType where
  SomeType :: Ty t -> SomeType


data TIdx xs x where
  Z ::              TIdx (x , xs) x
  S :: TIdx xs x -> TIdx (x', xs) x

data TList c xs where
  Nil  :: TList c ()
  Cons :: c x -> TList c xs -> TList c (x, xs)

type Env = TList Ty
type ValEnv = TList Id
newtype Id a = Id a

lookup :: TIdx xs x -> TList c xs -> c x
lookup Z (Cons x _) = x
lookup (S n) (Cons _ xs) = lookup n xs

lookupVal :: TIdx xs x -> ValEnv xs -> x
lookupVal i xs = let Id ans = lookup i xs in ans

lookupType :: Int -> Env e -> Typed (TIdx e)
lookupType 0 (Cons t _) = Typed t Z
lookupType n (Cons _ env) = case lookupType (n-1) env of
                              Typed t v -> Typed t (S v)

typeType :: RawType -> SomeType
typeType rt = case rt of
  RIntType -> SomeType IntType
  RArrType a b -> case (typeType a, typeType b) of
    (SomeType a', SomeType b') -> SomeType $ ArrType a' b'

data Equal a b where
  Equal :: Equal a a


typesEqual :: Ty a -> Ty b -> Maybe (Equal a b)
typesEqual IntType IntType = Just Equal
typesEqual (ArrType a b) (ArrType a' b') = do
  Equal <- typesEqual a a'
  Equal <- typesEqual b b'
  return Equal

typeExpr :: Term -> Env e -> Maybe (Typed (TTerm e))
typeExpr expr env =
  case expr of
  Lit x -> return $ Typed IntType (TLit x)
  Var v -> return $ case lookupType v env of
                       Typed t v -> Typed t (TVar v)
  Lam t body -> case typeType t of
    SomeType a -> case typeExpr body (Cons a env) of
      Just (Typed b tbody) -> Just $ Typed (ArrType a b) (TLam a tbody)
  App e1 e2 -> case (typeExpr e1 env, typeExpr e2 env) of
    (Just (Typed (ArrType a b) e1'), Just (Typed a' e2')) ->
       case typesEqual a a' of
         Nothing -> Nothing
         Just Equal -> Just $ Typed b (TApp e1' e2')

eval :: TTerm e t -> ValEnv e -> t
eval expr env = case expr of
  TVar v -> lookupVal v env
  TLit x -> x
  TLam _ body -> \x -> eval body (Cons (Id x) env)
  TApp e1 e2 -> (eval e1 env) (eval e2 env)

evalt :: Typed (TTerm e) -> ValEnv e-> String
evalt (Typed t expr) env =
  let v = eval expr env
  in case t of
    IntType -> show v
    ArrType _ _  -> "<lambda>"

tenv = Cons IntType Nil
venv = Cons (Id 5) Nil

expr = App (Lam RIntType (Var 0)) (Var 0)
texpr = case typeExpr expr tenv of
          Just e -> e
val = evalt texpr venv

main :: IO ()
main = do
  print $ val
