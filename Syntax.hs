module Syntax (Expr (..), Pat (..)) where

import qualified Data.Map.Strict as M
import Record

data Expr = Lit Int
          | Var Int
          | Let Pat Expr Expr
          | Lam Pat Expr
          | App Expr Expr
          | For Expr
          | Get Expr Int
          | RecCon (Record Expr)
              deriving (Show, Eq)

data Pat = VarPat  deriving (Show, Eq)
      -- | RecPat [(String, Pattern)]
