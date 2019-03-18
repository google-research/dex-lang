module DeFunc (deFuncPass) where

import Syntax
import Env
import Record
import Util

deFuncPass :: Pass Expr Expr () ()
deFuncPass = undefined

-- type DeFuncM a = ReaderT DeFuncEnv (
--                           WriterT Constraints (
--                             SupplyT (Either Err))) a

data DeFuncVal = NoVal
               | LamVal (Pat ()) Expr

deFuncExpr :: Expr -> DeFuncM (Expr, DeFuncVal)
deFuncExpr expr = case expr of
  Lit c -> (expr, NoVal)
  Var v -> do x <- asks $ (! v) . lEnv
              return (expr, x)
  Builtin b -> (expr, NoVal)
  -- Let t bound body -> Let (recurTy t) (recur bound) (recur body)
  -- TODO: only capture vars actually used
  Lam p body       -> let vs = map (Var . BV) [0..length (bVars env) - 1]
                      in (RecCon $ posRecord vs, LamVal p body)
  App fexpr arg    ->     App (recur fexpr) (recur arg)



  -- For t body       -> For (recurTy t) (recur body)
  -- Get e ie         -> Get (recur e) ie
  -- RecCon r         -> RecCon (fmap recur r)
  -- Unpack bound body -> Unpack (recur bound) (recurWith 1 body)
  -- TLam kinds expr     -> TLam kinds (recurWith (length kinds) expr)
  -- TApp expr ts        -> TApp (recur expr) (map recurTy ts)


