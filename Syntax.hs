module Syntax (Expr (..)) where

data Expr = Lit Int
          | Var Int
          | Let Expr Expr
          | Lam Expr
          | App Expr Expr
          | For Expr
          | Get Expr Int
              deriving (Show)
