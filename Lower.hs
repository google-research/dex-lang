module Lower (VarName, VarEnv, initVarEnv, lowerExpr, lowerPat,
              Expr (..), Pat (..), IdxPat, IdxExpr (..)) where
import Prelude hiding (lookup)
import qualified Data.Map.Strict as M
import Util
import Data.Foldable (toList)
import Record
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader (ReaderT (..), runReaderT, local, ask)
import qualified Syntax as S
import qualified Parser as P
import Parser (VarName, IdxVarName)

data LowerErr = UnboundVarErr VarName
              | UnboundIdxVarErr IdxVarName
              | RepVarPatternErr P.Pat [VarName]

type VarEnv = [VarName]
type IdxVarEnv = [IdxVarName]
type Env = (VarEnv, IdxVarEnv)
type Lower a = ReaderT Env (Either LowerErr) a

data Expr = Lit S.LitVal
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
  P.Var v         -> liftM Var $ lookupEnv v
  P.Let p e body  -> do (p', vs)  <- lift $ lowerPat p
                        e' <- lower e
                        body' <- local (updateEnv vs) (lower body)
                        return $ Let p' e' body'
  P.Lam p body    -> do (p', vs) <- lift $ lowerPat p
                        body' <- local (updateEnv vs) (lower body)
                        return $ Lam p' body'
  P.App fexpr arg -> liftM2 App (lower fexpr) (lower arg)
  P.For p body    -> do (p', vs) <- lift $ lowerIdxPat p
                        body' <- local (updateIEnv vs) (lower body)
                        return $ For p' body'
  P.Get e ie      -> liftM2 Get (lower e) (lowerIdxExpr ie)
  P.RecCon exprs  -> liftM RecCon $ mapM lower exprs


lowerPat' :: P.Pat -> Pat
lowerPat' p = case p of
  P.VarPat v -> VarPat
  P.RecPat r -> RecPat $ fmap lowerPat' r

lowerIdxPat :: P.IdxPat -> Either LowerErr (IdxPat, [IdxVarName])
lowerIdxPat = lowerPat

lowerIdxExpr :: P.IdxExpr -> Lower IdxExpr
lowerIdxExpr expr = case expr of
  P.IdxVar v    -> liftM IdxVar $ lookupIEnv v
  P.IdxRecCon r -> liftM IdxRecCon $ mapM lowerIdxExpr r

patVars :: P.Pat -> [VarName]
patVars p = case p of
  P.VarPat v -> [v]
  P.RecPat r -> concat $ fmap patVars r

updateEnv :: [VarName] -> Env -> Env
updateEnv vs (env,ienv) = (vs ++ env,ienv)

updateIEnv :: [IdxVarName] -> Env -> Env
updateIEnv is (env,ienv) = (env, is ++ ienv)

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
