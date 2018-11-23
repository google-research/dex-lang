module Syntax (Expr (..), Pat (..), IdxExpr (..), IdxPat) where

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
              deriving (Show, Eq, Ord)

data IdxExpr = IdxVar Int
             | IdxRecCon (Record IdxExpr)
                 deriving (Show, Eq, Ord)

type IdxPat = Pat
data Pat = VarPat
         | RecPat (Record Pat)  deriving (Show, Eq, Ord)
