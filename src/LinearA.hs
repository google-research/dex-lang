module LinearA where

type Var = String
type FuncName = String
data MixedType = MixedType [Type] [Type]
data Type = FloatType | TupleType [Type]
data Expr = Ret [Var] [Var]
          | LetMixed     [Var] [Var] Expr Expr
          | LetUnpack    [Var]       Expr Expr
          | LetUnpackLin [Var]       Expr Expr
          | App FuncName [Var] [Var]
          -- Additional non-linear expressions
          | Var Var
          | Lit Float
          | Tuple [Expr]
          | UnOp  UnOp  Expr
          | BinOp BinOp Expr Expr
          -- Additional linear expressions
          | LVar Var
          | LTuple [Expr]
          | LAdd   Expr Expr
          | LScale Expr Expr
          | LZero  [Var]
          | Dup  Expr
          | Drop Expr
data UnOp  = Sin | Cos | Expr
data BinOp = Add | Mul

data Definition = Def FuncName [Var] [Var] MixedType Expr
data Program = Program [Definition]
