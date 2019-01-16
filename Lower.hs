module Lower (lowerPass, LowerErr,
              lowerExpr, Expr (..), Pat (..), IdxPat, IdxExpr (..)) where

import Prelude hiding (lookup)
import qualified Data.Set as Set
import Util
import Env hiding (Env)
import Data.Foldable (toList)
import Record
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader (ReaderT (..), runReaderT, local, ask)
import Syntax (IdxExpr (..))
import qualified Syntax as S
import qualified Parser as P
import Parser (IdxVarName)

data LowerErr = UnboundVarErr VarName
              | UnboundIdxVarErr IdxVarName
              | RepVarPatternErr P.Pat [VarName]

type VarEnv = [VarName]
type IdxVarEnv = [IdxVarName]
type Env = (Set.Set VarName, VarEnv, IdxVarEnv)
type Lower a = ReaderT Env (Either LowerErr) a

data Expr = Lit S.LitVal
          | Var S.LetVar
          | Let Pat Expr Expr
          | Lam Pat Expr
          | App Expr Expr
          | For IdxPat Expr
          | Get Expr IdxExpr
          | RecCon (Record Expr)
              deriving (Show, Eq, Ord)

type IdxPat = Pat
data Pat = VarPat
         | RecPat (Record Pat)  deriving (Show, Eq, Ord)

lowerPass :: S.Pass () P.Expr Expr
lowerPass = S.Pass applyPass evalCmd
  where applyPass expr env = case lowerExpr expr env of
                               Left e -> Left $ show e
                               Right expr' -> Right ((), expr')
        evalCmd cmd () expr = case cmd of
                                S.GetLowered -> Just $ show expr
                                _ -> Nothing

lowerExpr :: P.Expr -> FreeEnv () -> Either LowerErr Expr
lowerExpr expr fenv = runReaderT (lower expr) (freeVarSet, [], [])
  where freeVarSet = Set.fromList $ map fst (freeEnvToList fenv) ++ builtinVars

builtinVars =
  ["add", "sub", "mul", "pow", "exp", "log", "sqrt",
   "sin", "cos", "tan", "reduce", "iota" ]

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

lowerPat :: P.Pat -> Either LowerErr (Pat, [VarName])
lowerPat p = let p' = lowerPat' p
                 vs = patVars p
             in case repeated vs of
               [] -> return (p', vs)
               vs -> throwError $ RepVarPatternErr p vs

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
updateEnv vs (fenv, env,ienv) = (fenv, vs ++ env,ienv)

updateIEnv :: [IdxVarName] -> Env -> Env
updateIEnv is (fenv, env,ienv) = (fenv, env, is ++ ienv)

lookupEnv :: VarName -> Lower S.LetVar
lookupEnv v = do
    (freeVars, env,_) <- ask
    case lookup v env of
      Just x -> return (BV x)
      Nothing -> if v `Set.member` freeVars
                   then return $ FV v
                   else throwError $ UnboundVarErr v

lookupIEnv :: IdxVarName -> Lower S.IdxVar
lookupIEnv iv = do
    (_, _, ienv) <- ask
    case lookup iv ienv of
      Just x -> return (BV x)
      Nothing -> throwError $ UnboundIdxVarErr iv

instance Show LowerErr where
  show e = "Error: " ++
    case e of
      UnboundVarErr    v -> "unbound variable: " ++  v
      UnboundIdxVarErr v -> "unbound index variable: " ++ v
      RepVarPatternErr  p vs -> "Repeated variables " ++ show vs ++ " in " ++ show p
