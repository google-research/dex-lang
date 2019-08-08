module Expand (expandPass) where

import Syntax
import Pass
import PPrint

expandPass :: TopDecl -> TopPass () TopDecl
expandPass topDecl = return $ case topDecl of
  TopDecl decl -> TopDecl $ expandDecl decl
  EvalCmd NoOp -> EvalCmd NoOp
  EvalCmd (Command cmd expr) -> EvalCmd (Command cmd (expandExpr expr))

expandDecl :: Decl -> Decl
expandDecl decl = case decl of
  Let    b   bound -> Let    b   (expandExpr bound)
  Unpack b n bound -> Unpack b n (expandExpr bound)

expandExpr :: Expr -> Expr
expandExpr expr = case expr of
  Lit _ -> expr
  Var _ -> expr
  PrimOp b ts xs -> expandBuiltin b ts (map recur xs)
  Decls decls body -> Decls (map expandDecl decls) (recur body)
  Lam x body -> Lam x (recur body)
  App f x -> App (recur f) (recur x)
  TApp f ts -> TApp (recur f) ts
  TLam ts body -> TLam ts (recur body)
  Get x i -> Get (recur x) i
  For i body -> For i (recur body)
  RecCon r -> RecCon $ fmap recur r
  RecGet e field -> RecGet (recur e) field
  TabCon n ty xs -> TabCon n ty (map recur xs)
  _ -> error $ "Unexpected expression in expansion: " ++ pprint expr
  where recur = expandExpr

expandBuiltin :: Builtin -> [Type] -> [Expr] -> Expr
expandBuiltin b = case b of
  VSum -> preludeApp "vsumImpl"
  _ -> PrimOp b
