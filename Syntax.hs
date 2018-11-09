module Syntax (Expr (..), Pat (..)) where

import qualified Data.Map.Strict as M
import Record

data Expr = Lit Int
          | Var Int
          | Let Pat Expr Expr
          | Lam Pat Expr
          | App Expr Expr
          | For IdxPat Expr
          | Get Expr IdxExpr
          | RecCon (Record Expr)
              deriving (Show, Eq)

data IdxExpr = IdxVar Int
             | IdxRecCon (Record IdxExpr)
                 deriving (Show, Eq)

type IdxPat = Pat
data Pat = VarPat
         | RecPat (Record Pat)  deriving (Show, Eq)
