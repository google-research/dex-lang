module DeFunc (deFuncPass, DFVal (..), TypedDFVal) where

import Syntax
import Env
import Record
import Util
import Typer

import Data.Foldable (toList)
import Control.Monad
import Control.Monad.Reader (ReaderT, runReaderT, local, ask, asks)
import Control.Monad.State (State, evalState, put, get)

type TopDFEnv = FullEnv (DFVal, Type) ()
type Uniq = Int
type DFType   = GenType Uniq
type DFExpr   = GenExpr Uniq
type DFPat    = Pat  Uniq

type DFEnv = FullEnv TypedDFVal DFType
type TypedDFVal = (DFVal, DFType)

data DFVal = DFNil
           | LamVal (Pat ()) DFEnv Expr
           | TLamVal DFEnv Expr
           | BuiltinLam Builtin [DFType] [DFVal]
           | RecVal (Record DFVal)  deriving (Show)

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
localEnv (FullEnv lenv tenv) = FullEnv lenv' tenv'
  where lenv' = fmap (\(v,t) -> (v, noLeaves t)) lenv
        tenv' = fmap (TypeVar . FV) (asIDMap tenv)

unitLit = RecCon emptyRecord

-- TODO: put in an except monad. Since we throw out the type, we're not even checking this
deFuncExprTop :: TopDFEnv -> Expr -> Except ((DFVal, Type), Expr)
deFuncExprTop env expr = do
  ty <- checkSysF (asTypingEnv dfEnv) (noLeaves expr')
  return ((val, ty), noLeaves expr')
  where (val, expr') = evalState (runReaderT (deFuncExpr expr) dfEnv) 0
        dfEnv = localEnv env

asTypingEnv :: DFEnv -> FullEnv Type ()
asTypingEnv (FullEnv lenv tenv) = FullEnv (fmap (noLeaves . snd) lenv)
                                          (fmap (const ()) tenv)

type DeFuncM a = ReaderT DFEnv (State Int) a

deFuncExpr :: Expr -> DeFuncM (DFVal, DFExpr)
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
    -- (val, bound') <- recur bound
    (val, bound') <- recur bound
    i <- inc
    let updateT = setTEnv (addBVar (Meta i))
    t' <- local updateT (evalType (Exists t))
    let updateL = setLEnv (addBVar (val, t'))
    (ans, body') <- local (updateL . updateT) (deFuncExpr body)
    let body'' = bindMetaExpr [i] body'
        t'' = bindMetaTy [i] t'
    return (ans, Unpack t'' bound' body'')

  where recur = deFuncExpr
        envBVars env = let n = length (bVars (lEnv env))
                       in RecCon $ posRecord $ map var [0..n - 1]

bindPat :: Pat () -> DFVal -> DeFuncM (DFPat, [TypedDFVal])
bindPat pat val = do
  tree <- traverse processLeaf (zipPatVal pat val)
  return (fmap snd tree, toList tree)

  where processLeaf :: (Type, DFVal) -> DeFuncM (DFVal, DFType)
        processLeaf (t, v) = do t' <- evalType t
                                return (v, deFuncType v t')


zipPatVal :: RecTree a -> DFVal -> RecTree (a, DFVal)
zipPatVal (RecTree r) (RecVal r') = RecTree (recZipWith zipPatVal r r')
zipPatVal (RecLeaf x) x' = RecLeaf (x, x')

deFuncType :: DFVal -> DFType -> DFType
deFuncType (RecVal r) (RecType r') = RecType $ recZipWith deFuncType r r'
deFuncType DFNil t = t
deFuncType (LamVal p env _) _ = RecType $ posRecord (envTypes env)
deFuncType (TLamVal env _)  _ = RecType $ posRecord (envTypes env)
deFuncType (BuiltinLam b ts exprs) _ = error "not implemented"

getExprType :: DFExpr -> DeFuncM DFType
getExprType expr = undefined -- do
  -- lenv <- asks lEnv
  -- return $ getType (FullEnv (fmap snd lenv) mempty) expr

consTypeToList :: Int -> GenType a -> [GenType a]
consTypeToList 0 _ = []
consTypeToList n (RecType r) = let [head, tail] = fromPosRecord r
                               in head : consTypeToList (n-1) tail

var i = Var (BV i)
posPat = RecTree . posRecord
lhsPair x y = posPat [x, y]
rhsPair x y = RecCon  (posRecord [x, y])
envTypes = map snd . bVars . lEnv
envPat = posPat . map RecLeaf . envTypes

deFuncApp :: (DFVal, DFExpr) -> (DFVal, DFExpr) -> DeFuncM (DFVal, DFExpr)
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

deFuncBuiltin :: DFVal -> DFExpr -> DeFuncM (DFVal, DFExpr)
deFuncBuiltin val@(BuiltinLam b ts argVals) args =
  if length ts < numTyArgs b || length argVals < numArgs b
    then return (val, args)
    else case b of Fold -> deFuncFold ts argVals args
                   _    -> return (DFNil, BuiltinApp b ts [args])

deFuncFold :: [DFType] -> [DFVal] -> DFExpr -> DeFuncM (DFVal, DFExpr)
deFuncFold ts [f, init, xs] args = do
  [fTy, initTy, TabType _ xsTy] <- builtinArgTypes 3 args
  (ans, lamExpr) <- canonicalLamExpr (f, fTy) [(init, initTy), (xs, xsTy)]
  return (ans, BuiltinApp FoldDeFunc ts [lamExpr, args])

builtinArgTypes :: Int -> DFExpr -> DeFuncM [DFType]
builtinArgTypes n expr = do ty <- getExprType expr
                            return $ reverse $ consTypeToList n ty

canonicalLamExpr :: (TypedDFVal) -> [TypedDFVal] -> DeFuncM (DFVal, DFExpr)
canonicalLamExpr (fval, fType) xsTyped = do
  let (xs, xsTypes) = unzip xsTyped
  (ans, body) <- foldM deFuncApp (fval, var 0) (zip xs (map var [1..]))
  let pat = posPat $ map RecLeaf (fType:xsTypes)
  return (ans, Lam pat body)

inc :: DeFuncM Int
inc = do i <- get
         put $ i + 1
         return i

evalType :: Type -> DeFuncM DFType
evalType ty =
  do env <- ask
     return $ instantiateBodyFVs (fmap Just (tEnv env)) (noLeaves ty)

asIDMap :: Env i a -> Env i VarName
asIDMap env = newEnv [(v,v) | v <- fVars env]
