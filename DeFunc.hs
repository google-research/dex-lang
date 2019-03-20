module DeFunc (deFuncPass, DFVal (..), TypedDFVal) where

import Syntax
import Env
import Record
import Util

import Data.Foldable (toList)
import Control.Monad.Reader (ReaderT, runReaderT, local, ask, asks)
import Control.Monad.State (State, evalState, put, get)

type TopDFEnv = FullEnv DFVal ()
type Uniq = Int
type MType   = GenType Uniq
type MExpr   = GenExpr Uniq
type MPat    = Pat  Uniq

deFuncPass :: Pass Expr Expr DFVal ()
deFuncPass = Pass
  { lowerExpr   = \expr env   -> return $ deFuncExprTop env expr
  , lowerUnpack = \v expr env -> return $ deFuncUnpack v expr env
  , lowerCmd    = \cmd  env   -> return $ deFuncCmd cmd env }

deFuncCmd :: Command Expr -> TopDFEnv -> Command Expr
deFuncCmd (Command cmdName expr) env = case cmdName of
    DeFunc -> CmdResult $ TextOut $ show expr'
    _ -> Command cmdName expr'
  where (_, expr') = deFuncExprTop env expr
deFuncCmd (CmdResult s) _ = CmdResult s
deFuncCmd (CmdErr e)    _ = CmdErr e

deFuncUnpack :: VarName -> Expr -> TopDFEnv -> (DFVal, (), Expr)
deFuncUnpack _ expr env = let (val, expr') = deFuncExprTop env expr
                              in (val, (), expr')

localEnv :: TopDFEnv -> DFEnv
localEnv (FullEnv lenv tenv) = FullEnv lenv' tenv'
  where lenv' = fmap (\v -> (v, Nothing)) lenv
        tenv' = fmap (\v -> TypeVar (FV v)) (asIDMap tenv)

type DFEnv = FullEnv TypedDFVal MType
type TypedDFVal = (DFVal, Maybe MType)

data DFVal = DFNil
           | LamVal MPat DFEnv Expr
           | TLamVal DFEnv Expr
           | RecVal (Record DFVal)

unitLit :: Expr
unitLit = RecCon emptyRecord

deFuncExprTop :: TopDFEnv -> Expr -> (DFVal, Expr)
deFuncExprTop env expr =
  let (val, expr') = evalState (runReaderT (deFuncExpr expr) (localEnv env)) 0
  in (val, noLeaves expr')

type DeFuncM a = ReaderT DFEnv (State Int) a


deFuncExpr :: Expr -> DeFuncM (DFVal, MExpr)
deFuncExpr expr = case expr of
  Var v     -> do val <- asks $ fst . (! v) . lEnv
                  return (val, Var v)
  Lit l     -> return (DFNil, Lit l)
  Builtin b -> return (DFNil, Builtin b)
  Let p bound body -> do (x,  bound') <- recur bound
                         p' <- deFuncPat p
                         (ans, body') <- recurWithPat p' x body
                         return (ans, Let p' bound' body')
  -- TODO: only capture vars needed instead of full env
  Lam p body -> do p' <- deFuncPat p
                   env <- ask
                   return (LamVal p' env body,  envBVars env)
  App fexpr arg -> do
      (fVal, fexpr') <- recur fexpr
      (argVal, arg') <- recur arg
      case fVal of
        DFNil -> return (DFNil, App fexpr' arg')
        LamVal p env body -> do
          let env' = setLEnv (addBVars $ bindPat p argVal) env
          (ans, body') <- local (const env') (deFuncExpr body)
          return (ans, Let (lhsPair p (envPat env)) (rhsPair arg' fexpr') body')
  For a body -> do a' <- deFuncType a
                   let update = setLEnv (addBVar (DFNil, Just a'))
                   (ans, body') <- local update (recur body)
                   return (ans, For a' body')
  Get e ie -> do (ans, e') <- recur e
                 return (ans, Get e' ie)
  RecCon r -> do r' <- traverse recur r
                 return (RecVal (fmap fst r'), RecCon (fmap snd r'))
  TLam _ body -> do env <- ask
                    return (TLamVal env body, envBVars env)
  TApp fexpr ts -> do
    (tLamVal, fexpr') <- recur fexpr
    ts' <- traverse deFuncType ts
    case tLamVal of
      DFNil -> return (DFNil, TApp fexpr' ts')
      TLamVal env body -> do
          let env' = setTEnv (addBVars ts') env
          (ans, body') <- local (const env') (deFuncExpr body)
          return (ans, Let (envPat env) fexpr' body')
  Unpack bound body -> do
    (val, bound') <- recur bound
    -- TODO: maybe change unpack to have a type annotation)
    i <- inc
    let update = setLEnv (addBVar (val, Nothing)) . setTEnv (addBVar (Meta i))
    (ans, body') <- local update (deFuncExpr body)
    let body'' = bindMetaExpr [i] body'
    return (ans, Unpack bound' body'')

  where recur = deFuncExpr
        recurWithPat p x e = local (setLEnv (addBVars $ bindPat p x)) (recur e)
        envBVars env = let n = length (bVars (lEnv env))
                       in RecCon $ posRecord $ map (Var . BV) [0..n - 1]
        lhsPair x y = RecTree (posRecord [x, y])
        rhsPair x y = RecCon  (posRecord [x, y])
        envPat env = RecTree $ posRecord $ map (RecLeaf . unJust . snd) (bVars (lEnv env))

inc :: DeFuncM Int
inc = do i <- get
         put $ i + 1
         return i

deFuncPat :: Pat () -> DeFuncM MPat
deFuncPat p = traverse deFuncType p

bindPat :: MPat -> DFVal -> [TypedDFVal]
bindPat (RecTree r) (RecVal r') = concat $ zipWith bindPat (toList r) (toList r')
bindPat (RecLeaf t) x = [(x, Just t)]

deFuncType :: Type -> DeFuncM MType
deFuncType ty =
  do env <- ask
     return $ instantiateBodyFVs (fmap Just (tEnv env)) (noLeaves ty)

asIDMap :: Env i a -> Env i VarName
asIDMap env = newEnv [(v,v) | v <- fVars env]
