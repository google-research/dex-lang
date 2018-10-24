

parse :: String -> Either ParseError RawExpr
lower :: RawExpr -> ParseEnv -> Either LowerError Expr
gettype :: Expr -> TypeEnv -> Either TypeError Type
eval :: Expr -> EvalEnv -> Val

String -> (State -> (State, String))
