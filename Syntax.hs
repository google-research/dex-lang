module Syntax (Expr (..), Pat (..), IdxExpr (..), IdxPat, LitVal (..),
               Type (..), BaseType (..), SigmaType (..),
               MetaVar (..), IdxType) where

import Data.List (intersperse)
import qualified Data.Map.Strict as M
import Record

data Expr = Lit LitVal
          | Var Int
          | Let Pat Expr Expr
          | Lam Pat Expr
          | App Expr Expr
          | For IdxPat Expr
          | Get Expr IdxExpr
          | RecCon (Record Expr)
              deriving (Show, Eq, Ord)

data LitVal = IntLit  Int
            | RealLit Float
            | StrLit  String
                 deriving (Show, Eq, Ord)

data IdxExpr = IdxVar Int
             | IdxRecCon (Record IdxExpr)
                 deriving (Show, Eq, Ord)

type IdxPat = Pat
data Pat = VarPat
         | RecPat (Record Pat)  deriving (Show, Eq, Ord)

data Type = BaseType BaseType
          | ArrType Type Type
          | TabType IdxType Type
          | RecType (Record Type)
          | TypeVar Int
          | MetaTypeVar MetaVar
            deriving (Eq, Ord)

type IdxType = Type
data SigmaType = Forall Int Type  deriving (Eq, Ord)

newtype MetaVar = MetaVar Int  deriving (Eq, Ord, Show)

data BaseType = IntType | BoolType | RealType | StrType deriving (Eq, Ord)

varName :: Int -> String
varName n | n < 26    = [['a'..'z'] !! n]
          | otherwise = varName (mod n 26) ++ show (div n 26)

instance Show SigmaType where
  show (Forall 0 t) = show t
  show (Forall n t) = let vs = concat $ intersperse " " $ map varName [0..n-1]
                      in "A " ++ vs ++ ". " ++ show t

instance Show Type where
  show t = case t of
    ArrType a b -> "(" ++ show a ++ " -> " ++ show b ++ ")"
    TabType a b -> show a ++ "=>" ++ show b
    BaseType b  -> show b
    RecType m   -> printRecord show (RecordPrintSpec ", " ":" "," Nothing) m
    TypeVar v   -> varName v
    MetaTypeVar (MetaVar v) -> varName v

instance Show BaseType where
  show b = case b of
             IntType -> "Int"
             StrType -> "Str"
             BoolType -> "Bool"
             RealType -> "Real"
