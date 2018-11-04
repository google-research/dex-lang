module Syntax (Expr (..), Pat (..)) where

data Expr = Lit Int
          | Var Int
          | Let Pat Expr Expr
          | Lam Pat Expr
          | App Expr Expr
          | For Expr
          | Get Expr Int
              deriving (Show, Eq)

data Pat = VarPat  deriving (Show, Eq)
      -- | RecPat [(String, Pattern)]
