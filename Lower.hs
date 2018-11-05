module Lower (VarName, VarEnv, initVarEnv, lowerExpr) where
import Prelude hiding (lookup)
import qualified Data.Map.Strict as M
import Util
import Record
import Control.Monad
import Control.Monad.Reader (ReaderT (..), runReaderT, local, ask)
import Syntax
import qualified Parser as P
import Parser (VarName, IdxVarName)

data LowerErr = UnboundVarErr VarName
              | UnboundIdxVarErr IdxVarName

type Except a = Either LowerErr a
type VarEnv = [VarName]
type IdxVarEnv = [IdxVarName]
type Env = (VarEnv, IdxVarEnv)
type Lower a = ReaderT Env (Either LowerErr) a

lowerExpr :: P.Expr -> VarEnv -> Except Expr
lowerExpr expr env = runReaderT (lower expr) (env, [])

initVarEnv :: VarEnv
initVarEnv = ["iota", "reduce", "add", "sub", "mul", "div"]

lower :: P.Expr -> Lower Expr
lower expr = case expr of
  P.Lit c         -> return $ Lit c
  P.Var v         -> liftM  Var $ lookupEnv v
  P.Let p e body  -> do (p', vs)  <- lowerPat p
                        e' <- lower e
                        body' <- local (updateEnv vs) (lower body)
                        return $ Let p' e' body'
  P.Lam p body    -> do (p', vs) <- lowerPat p
                        body' <- local (updateEnv vs) (lower body)
                        return $ Lam p' body'
  P.App fexpr arg -> liftM2 App (lower fexpr) (lower arg)
  P.For iv body   -> liftM  For $ local (updateIEnv iv) (lower body)
  P.Get e iv      -> liftM2 Get (lower e) (lookupIEnv iv)
  P.RecCon exprs  -> liftM RecCon $ sequenceRecord $ mapRecord lower exprs

lowerPat :: P.Pat -> Lower (Pat, [VarName])
lowerPat p = case p of
  P.VarPat v -> return (VarPat, [v])
  P.RecPat r -> do
    ps_vs <- sequenceRecord $ mapRecord lowerPat r
    let ps = mapRecord fst ps_vs
    let vs = concat . recordElems . mapRecord snd $ ps_vs
    return (RecPat ps, vs)


updateEnv :: [VarName] -> Env -> Env
updateEnv vs (env,ienv) = (vs ++ env,ienv)

updateIEnv :: IdxVarName -> Env -> Env
updateIEnv i (env,ienv) = (env,i:ienv)

lookupEnv :: VarName -> Lower Int
lookupEnv v = do
    (env,_) <- ask
    maybeReturn (lookup v env) $ UnboundVarErr v

lookupIEnv :: IdxVarName -> Lower Int
lookupIEnv iv = do
    (_,ienv) <- ask
    maybeReturn (lookup iv ienv) $ UnboundIdxVarErr iv

maybeReturn :: Maybe a -> LowerErr -> Lower a
maybeReturn (Just x) _ = return x
maybeReturn Nothing  e = ReaderT $ \_ -> Left e

instance Show LowerErr where
  show e = "Error: " ++
    case e of
      UnboundVarErr    v -> "unbound variable: " ++  v
      UnboundIdxVarErr v -> "unbound index variable: " ++ v
