module Syntax (Expr (..), Pat (..), IdxExpr (..), IdxPat, LitVal (..),
               Type (..), BaseType (..), SigmaType,
               MetaVar (..), IdxType, LetVar, IdxVar, TypeVar,
               TopDecl (..), Command (..)) where

import Data.List (intersperse)
import qualified Data.Map.Strict as M
import qualified Prelude as P
import Prelude hiding ((!!))
import Record
import Env

data Expr = Lit LitVal
          | Var LetVar
          | Let Pat Expr Expr
          | Lam Pat Expr
          | App Expr Expr
          | For IdxPat Expr
          | Get Expr IdxExpr
          | RecCon (Record Expr)
          | TLam Int Expr
          | TApp Expr [Type]
          | Unpack Expr
          | Pack IdxType Expr Type
              deriving (Show, Eq, Ord)

data LitVal = IntLit  Int
            | RealLit Float
            | StrLit  String
                 deriving (Show, Eq, Ord)

data IdxExpr = IdxVar IdxVar
             | IdxRecCon (Record IdxExpr)
                 deriving (Show, Eq, Ord)

type IdxPat = Pat
data Pat = VarPat Type
         | RecPat (Record Pat)  deriving (Show, Eq, Ord)

data Type = BaseType BaseType
          | ArrType Type Type
          | TabType IdxType Type
          | RecType (Record Type)
          | TypeVar TypeVar
          | MetaTypeVar MetaVar
          | Forall Int Type
          | Exists Type
              deriving (Eq, Ord)

data TopDecl expr = EvalDecl String expr
                  | EvalCmd Command expr   deriving (Show, Eq, Ord)

data Command = EvalExpr | GetType | GetTyped | GetParse | GetLowered
             | GetLLVM  | EvalJit   deriving (Show, Eq, Ord)

type IdxType = Type
type SigmaType = Type
newtype MetaVar = MetaVar Int  deriving (Eq, Ord, Show)

data LetUniq  = LetUniq  deriving (Show, Eq, Ord); type LetVar  = Var LetUniq
data IdxUniq  = IdxUniq  deriving (Show, Eq, Ord); type TypeVar = Var TypeUniq
data TypeUniq = TypeUniq deriving (Show, Eq, Ord); type IdxVar  = Var IdxUniq

data BaseType = IntType | BoolType | RealType | StrType  deriving (Eq, Ord)

varName :: Int -> String
varName n | n < 26    = [['a'..'z'] P.!! n]
          | otherwise = varName (mod n 26) ++ show (div n 26)

instance Show Type where
  show t = case t of
    ArrType a b -> "(" ++ show a ++ " -> " ++ show b ++ ")"
    TabType a b -> show a ++ "=>" ++ show b
    BaseType b  -> show b
    RecType m   -> printRecord show (RecordPrintSpec ", " ":" "," Nothing) m
    TypeVar v   -> show v -- TODO
    MetaTypeVar (MetaVar v) -> varName v
    Forall 0 t -> "A . " ++ show t
    Forall n t -> let vs = concat $ intersperse " " $ map varName [0..n-1]
                  in "A " ++ vs ++ ". " ++ show t


instance Show BaseType where
  show b = case b of
             IntType -> "Int"
             StrType -> "Str"
             BoolType -> "Bool"
             RealType -> "Real"
