module Lower (VarName, VarEnv, initVarEnv, lowerExpr, lowerPat) where
import Prelude hiding (lookup)
import qualified Data.Map.Strict as M
import Util
import Data.Foldable (toList)
import Record
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader (ReaderT (..), runReaderT, local, ask)
import Syntax
import qualified Parser as P
import Parser (VarName, IdxVarName)

data LowerErr = UnboundVarErr VarName
              | UnboundIdxVarErr IdxVarName
              | RepVarPatternErr P.Pat [VarName]

type VarEnv = [VarName]
type IdxVarEnv = [IdxVarName]
type Env = (VarEnv, IdxVarEnv)
type Lower a = ReaderT Env (Either LowerErr) a

lowerExpr :: P.Expr -> VarEnv -> Either LowerErr Expr
lowerExpr expr env = runReaderT (lower expr) (env, [])

lowerPat :: P.Pat -> Either LowerErr (Pat, [VarName])
lowerPat p = let p' = lowerPat' p
                 vs = patVars p
             in case repeated vs of
               [] -> return (p', vs)
               vs -> throwError $ RepVarPatternErr p vs

initVarEnv :: VarEnv
initVarEnv = ["iota", "reduce", "add", "sub", "mul", "div"]

lower :: P.Expr -> Lower Expr
lower expr = case expr of
  P.Lit c         -> return $ Lit c
  P.Var v         -> liftM  Var $ lookupEnv v
  P.Let p e body  -> do (p', vs)  <- lift $ lowerPat p
                        e' <- lower e
                        body' <- local (updateEnv vs) (lower body)
                        return $ Let p' e' body'
  P.Lam p body    -> do (p', vs) <- lift $ lowerPat p
                        body' <- local (updateEnv vs) (lower body)
                        return $ Lam p' body'
  P.App fexpr arg -> liftM2 App (lower fexpr) (lower arg)
  P.For p body    -> liftM  For $ local (updateIEnv p) (lower body)
  P.Get e ie      -> liftM2 Get (lower e) (lookupIEnv ie)
  P.RecCon exprs  -> liftM RecCon $ mapM lower exprs


lowerPat' :: P.Pat -> Pat
lowerPat' p = case p of
  P.VarPat v -> VarPat
  P.RecPat r -> RecPat $ fmap lowerPat' r

patVars :: P.Pat -> [VarName]
patVars p = case p of
  P.VarPat v -> [v]
  P.RecPat r -> concat $ fmap patVars r

updateEnv :: [VarName] -> Env -> Env
updateEnv vs (env,ienv) = (vs ++ env,ienv)

updateIEnv :: IdxVarName -> Env -> Env
updateIEnv i (env,ienv) = (env,i:ienv)

lookupEnv :: VarName -> Lower Int
lookupEnv v = do
    (env,_) <- ask
    case lookup v env of
      Just x -> return x
      Nothing -> throwError $ UnboundVarErr v

lookupIEnv :: IdxVarName -> Lower Int
lookupIEnv iv = do
    (_,ienv) <- ask
    case lookup iv ienv of
      Just x -> return x
      Nothing -> throwError $ UnboundIdxVarErr iv

instance Show LowerErr where
  show e = "Error: " ++
    case e of
      UnboundVarErr    v -> "unbound variable: " ++  v
      UnboundIdxVarErr v -> "unbound index variable: " ++ v
      RepVarPatternErr  p vs -> "Repeated variables " ++ show vs ++ " in " ++ show p
