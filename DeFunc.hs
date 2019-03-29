module DeFunc (deFuncPass, DFVal (..), TypedDFVal) where

import Syntax
import Env
import Record
import Util
import Type

import Data.Foldable (toList)
import Control.Monad
import Control.Monad.Reader (ReaderT, runReaderT, local, ask, asks)
import Control.Monad.State (State, evalState, put, get)

type TopDFEnv = FullEnv TypedDFVal ()
type DFEnv    = FullEnv TypedDFVal Type

type TempVar = Int

type TypedDFVal = (DFVal, Type)

data DFVal = DFNil
           | LamVal Pat DFEnv Expr
           | TLamVal DFEnv Expr
           | BuiltinLam Builtin [Type] [DFVal]
           | RecVal (Record DFVal)  deriving (Show)

type DeFuncM a = ReaderT DFEnv (State Int) a

deFuncPass :: Pass Expr Expr (DFVal, Type) ()
deFuncPass = Pass
  { lowerExpr   = \expr env   -> liftErrIO $ deFuncExprTop env expr
  , lowerUnpack = \v expr env -> liftErrIO $ deFuncUnpack v expr env
  , lowerCmd    = \cmd  env   -> return $ deFuncCmd cmd env }

deFuncCmd :: Command Expr -> TopDFEnv -> Command Expr
deFuncCmd (Command cmdName expr) env = case deFuncExprTop env expr of
  Left e -> CmdErr e
  Right (_, expr') -> case cmdName of
                        DeFunc -> CmdResult $ TextOut $ show expr'
                        _ -> Command cmdName expr'
deFuncCmd (CmdResult s) _ = CmdResult s
deFuncCmd (CmdErr e)    _ = CmdErr e

deFuncUnpack :: VarName -> Expr -> TopDFEnv -> Except ((DFVal, Type), (), Expr)
deFuncUnpack _ expr env = do (valTy, expr') <- deFuncExprTop env expr
                             return (valTy, (), expr')

localEnv :: TopDFEnv -> DFEnv
localEnv (FullEnv lenv tenv) = FullEnv lenv mempty

unitLit = RecCon emptyRecord

deFuncExprTop :: TopDFEnv -> Expr -> Except ((DFVal, Type), Expr)
deFuncExprTop env expr = do
  let (val, expr') = evalDeFuncM (localEnv env) (deFuncExpr expr)
      ty' = deFuncType val (getType typingEnv expr')
  checkExpr typingEnv expr' ty'
  return ((val, ty'), expr')
  where typingEnv = setLEnv (fmap snd) env

evalDeFuncM :: DFEnv -> DeFuncM a -> a
evalDeFuncM env m = evalState (runReaderT m env) 0

deFuncExpr :: Expr -> DeFuncM (DFVal, Expr)
deFuncExpr expr = case expr of
  Var v     -> do val <- asks $ fst . (! v) . lEnv
                  return (val, Var v)
  Lit l     -> return (DFNil, Lit l)
  Builtin b -> return (BuiltinLam b [] [], unitLit)
  -- need to think harder about this. Defunctionalization can change the type,
  -- so we can't just reuse the old pattern
  Let p bound body -> do (x,  bound') <- recur bound
                         (p', xs) <- bindPat p x
                         let update = setLEnv (addBVars xs)
                         (ans, body') <- local update (recur body)
                         return (ans, Let p' bound' body')
  -- TODO: only capture vars needed instead of full env
  Lam p body -> do env <- ask
                   return (LamVal p env body,  envBVars env)
  App fexpr arg -> do fexpr' <- recur fexpr
                      arg'   <- recur arg
                      deFuncApp fexpr' arg'
  For a body -> do a' <- evalType a
                   let update = setLEnv (addBVar (DFNil, a'))
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
    ts' <- traverse evalType ts
    case tLamVal of
      BuiltinLam b [] [] -> deFuncBuiltin (BuiltinLam b ts' []) unitLit
      TLamVal env body -> do
          let env' = setTEnv (addBVars ts') env
          (ans, body') <- local (const env') (deFuncExpr body)
          return (ans, Let (envPat env) fexpr' body')
  Unpack t bound body -> do
    (val, bound') <- recur bound
    v <- fresh
    let updateT = setTEnv (addBVar (TypeVar (FV v)))
    t' <- local updateT (evalType (Exists t))
    let updateL = setLEnv (addBVar (val, t'))
    (ans, body') <- local (updateL . updateT) (deFuncExpr body)
    let body'' = abstractTVs [v] body'
        t''    = abstractTVs [v] t'
    return (ans, Unpack t'' bound' body'')

  where recur = deFuncExpr
        envBVars env = let n = length (bVars (lEnv env))
                       in RecCon $ posRecord $ map var [0..n - 1]


evalType :: Type -> DeFuncM Type
evalType ty =
  do env <- ask
     return $ instantiateTVs (bVars (tEnv env)) ty

bindPat :: Pat -> DFVal -> DeFuncM (Pat, [TypedDFVal])
bindPat pat val = do
  tree <- traverse processLeaf (zipPatVal pat val)
  return (fmap snd tree, toList tree)

  where processLeaf :: (Type, DFVal) -> DeFuncM (DFVal, Type)
        processLeaf (t, v) = do t' <- evalType t
                                return (v, deFuncType v t')


zipPatVal :: RecTree a -> DFVal -> RecTree (a, DFVal)
zipPatVal (RecTree r) (RecVal r') = RecTree (recZipWith zipPatVal r r')
zipPatVal (RecLeaf x) x' = RecLeaf (x, x')

deFuncType :: DFVal -> Type -> Type
deFuncType (RecVal r) (RecType r') = RecType $ recZipWith deFuncType r r'
deFuncType DFNil t = t
deFuncType (LamVal p env _) _ = RecType $ posRecord (envTypes env)
deFuncType (TLamVal env _)  _ = RecType $ posRecord (envTypes env)
deFuncType (BuiltinLam b ts exprs) _ = error "not implemented"

getExprType :: Expr -> DeFuncM Type
getExprType expr = undefined -- do
  -- lenv <- asks lEnv
  -- return $ getType (FullEnv (fmap snd lenv) mempty) expr

consTypeToList :: Int -> Type -> [Type]
consTypeToList 0 _ = []
consTypeToList n (RecType r) = let [head, tail] = fromPosRecord r
                               in head : consTypeToList (n-1) tail

var i = Var (BV i)
posPat = RecTree . posRecord
lhsPair x y = posPat [x, y]
rhsPair x y = RecCon  (posRecord [x, y])
envTypes = map snd . bVars . lEnv
envPat = posPat . map RecLeaf . envTypes

deFuncApp :: (DFVal, Expr) -> (DFVal, Expr) -> DeFuncM (DFVal, Expr)
deFuncApp (fVal, fexpr') (argVal, arg') =
  case fVal of
    BuiltinLam b ts vs ->
      let fVal' = BuiltinLam b ts (argVal:vs)
      in deFuncBuiltin fVal' (rhsPair arg' fexpr')
    LamVal p env body -> do
      (p', argVals) <- local (const env) (bindPat p argVal)
      let env' = setLEnv (addBVars argVals) env
      (ans, body') <- local (const env') (deFuncExpr body)
      return (ans, Let (lhsPair p' (envPat env))
                       (rhsPair arg' fexpr')
                       body')

deFuncBuiltin :: DFVal -> Expr -> DeFuncM (DFVal, Expr)
deFuncBuiltin val@(BuiltinLam b ts argVals) args =
  if length ts < numTyArgs b || length argVals < numArgs b
    then return (val, args)
    else case b of Fold -> deFuncFold ts argVals args
                   _    -> return (DFNil, BuiltinApp b ts [args])

deFuncFold :: [Type] -> [DFVal] -> Expr -> DeFuncM (DFVal, Expr)
deFuncFold ts [f, init, xs] args = do
  [fTy, initTy, TabType _ xsTy] <- builtinArgTypes 3 args
  (ans, lamExpr) <- canonicalLamExpr (f, fTy) [(init, initTy), (xs, xsTy)]
  return (ans, BuiltinApp FoldDeFunc ts [lamExpr, args])

builtinArgTypes :: Int -> Expr -> DeFuncM [Type]
builtinArgTypes n expr = do ty <- getExprType expr
                            return $ reverse $ consTypeToList n ty

canonicalLamExpr :: (TypedDFVal) -> [TypedDFVal] -> DeFuncM (DFVal, Expr)
canonicalLamExpr (fval, fType) xsTyped = do
  let (xs, xsTypes) = unzip xsTyped
  (ans, body) <- foldM deFuncApp (fval, var 0) (zip xs (map var [1..]))
  let pat = posPat $ map RecLeaf (fType:xsTypes)
  return (ans, Lam pat body)

fresh :: DeFuncM VarName
fresh = do i <- get
           put $ i + 1
           return (TempVar i)
