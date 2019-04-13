module DeFunc (deFuncPass, DFVal (..), TypedDFVal, DFEnv) where

import Syntax
import Env
import Record
import Util
import Type
import Fresh
import Pass
import PPrint

import Data.Foldable (toList)
import Control.Monad
import Control.Monad.Reader (Reader, runReader, local, ask, asks)

type DFEnv    = FullEnv TypedDFVal (Maybe Type)

type TypedDFVal = (DFVal, Type)

data DFVal = DFNil
           | LamVal Pat DFEnv Expr
           | TLamVal [TBinder] DFEnv Expr
           | BuiltinLam Builtin [Type] [DFVal]
           | RecVal (Record DFVal)  deriving (Show)

type DeFuncM a = MonadPass DFEnv () a

deFuncPass :: Pass Expr Expr (DFVal, Type) (Maybe Type)
deFuncPass = Pass
  { lowerExpr   = \expr env   -> liftErrIO $ deFuncExprTop env expr
  , lowerUnpack = \v expr env -> liftErrIO $ deFuncUnpack v expr env
  , lowerCmd    = \cmd  env   -> return $ deFuncCmd cmd env }

deFuncCmd :: Command Expr -> DFEnv -> Command Expr
deFuncCmd (Command cmdName expr) env = case deFuncExprTop env expr of
  Left e -> CmdErr e
  Right (_, expr') -> case cmdName of
                        DeFunc -> CmdResult $ TextOut $ pprint expr'
                        _ -> Command cmdName expr'
deFuncCmd (CmdResult s) _ = CmdResult s
deFuncCmd (CmdErr e)    _ = CmdErr e

deFuncUnpack :: Var -> Expr -> DFEnv -> Except (TypedDFVal, Maybe Type, Expr)
deFuncUnpack _ expr env = do (valTy, expr') <- deFuncExprTop env expr
                             return (valTy, Nothing, expr')

localEnv :: DFEnv -> DFEnv
localEnv (FullEnv lenv tenv) = FullEnv lenv mempty

deFuncExprTop :: DFEnv -> Expr -> Except (TypedDFVal, Expr)
deFuncExprTop env expr = do
  (val, expr') <- evalPass env () (rawVar "defunc") (deFuncExpr expr)
  let ty = getType typingEnv expr
  checkExpr typingEnv expr' (deFuncType val ty)
  return ((val, ty), expr')
  where typingEnv = setTEnv (fmap (const IdxSetKind)) $ setLEnv (fmap snd) env

deFuncExpr :: Expr -> DeFuncM (DFVal, Expr)
deFuncExpr expr = case expr of
  Var v     -> do val <- asks $ fst . (! v) . lEnv
                  return (val, Var v)
  Lit l     -> return (DFNil, Lit l)
  Builtin b -> return (BuiltinLam b [] [], unitLit)
  Let p bound body -> do (x,  bound') <- recur bound
                         (p', xs) <- bindPat p x
                         (ans, body') <- recurWith xs body
                         return (ans, Let p' bound' body')
  -- TODO: only capture vars needed instead of full env
  Lam p body -> do env <- ask
                   return (LamVal p env body,  envTupCon env)
  App fexpr arg -> do fexpr' <- recur fexpr
                      arg'   <- recur arg
                      deFuncApp fexpr' arg'
  For a body -> do let (v, ty) = a
                   (ans, body') <- recurWith [(v, (DFNil, ty))] body
                   return (ans, For a body')
  Get e ie -> do (ans, e') <- recur e
                 return (ans, Get e' ie)
  RecCon r -> do r' <- traverse recur r
                 return (RecVal (fmap fst r'), RecCon (fmap snd r'))
  TLam b body -> do env <- ask
                    return (TLamVal b env body, envTupCon env)
  TApp fexpr ts -> do
    ts' <- traverse subTy ts
    (tLamVal, fexpr') <- recur fexpr
    case tLamVal of
      BuiltinLam b [] [] -> deFuncBuiltin (BuiltinLam b ts' []) unitLit
      TLamVal bs env body -> do
          let env' = setTEnv (addLocals (zip (map fst bs) (map Just ts'))) env
          (ans, body') <- local (const env') (deFuncExpr body)
          return (ans, Let (envPat env) fexpr' body')
  Unpack b tv bound body -> do
    (val, bound') <- recur bound
    let updateT = setTEnv (addLocal (tv, Nothing))
    (b', valTy) <- local updateT (deFuncBinder (b,val))
    let updateL = setLEnv (addLocal valTy)
    (ans, body') <- local (updateL . updateT) (deFuncExpr body)
    return (ans, Unpack b' tv bound' body')

  where recur = deFuncExpr
        recurWith  xs = local (setLEnv $ addLocals xs) . deFuncExpr
        unitLit = RecCon (Tup [])

subTy :: Type -> DeFuncM Type
subTy ty = do { tenv <- asks tEnv; return $ maybeSub (tenv !) ty }

bindPat :: Pat -> DFVal -> DeFuncM (Pat, RecTree (Var, TypedDFVal))
bindPat pat val = do
  zipped <- traverse deFuncBinder (recTreeZip pat val)
  return (fmap fst zipped, fmap snd zipped)

deFuncBinder :: (Binder, DFVal) -> DeFuncM (Binder, (Var, TypedDFVal))
deFuncBinder ((v, ty), val) = do ty' <- subTy ty
                                 return ( (v, deFuncType val ty)
                                        , (v, (val, ty)) )

deFuncType :: DFVal -> Type -> Type
deFuncType (RecVal r) (RecType r') = RecType $ recZipWith deFuncType r r'
deFuncType DFNil t = t
deFuncType (LamVal p env _) _   = RecType $ Tup (envTypes env)
deFuncType (TLamVal _ env _)  _ = RecType $ Tup (envTypes env)
deFuncType (BuiltinLam b ts exprs) _ = error "not implemented"

getExprType :: Expr -> DeFuncM Type
getExprType expr = do
  lenv <- asks lEnv
  return $ getType (FullEnv (fmap snd lenv) mempty) expr

consTypeToList :: Int -> Type -> [Type]
consTypeToList n t = reverse $ recur n t
  where recur 0 _ = []
        recur n (RecType (Tup [xs, x])) = x : recur (n-1) xs

posPat = RecTree . Tup
lhsPair x y = posPat [x, y]
rhsPair x y = RecCon (Tup [x, y])

envTypes :: DFEnv -> [Type]
envTypes env = [ty | (_,(_,ty)) <- locals (lEnv env)]

envPat :: DFEnv -> Pat
envPat env = RecTree $ Tup [RecLeaf (v,ty) | (v,(_,ty)) <- locals (lEnv env)]

envTupCon :: DFEnv -> Expr
envTupCon env = RecCon $ Tup [Var v | (v,(_,_)) <- locals (lEnv env)]

deFuncApp :: (DFVal, Expr) -> (DFVal, Expr) -> DeFuncM (DFVal, Expr)
deFuncApp (fVal, fexpr) (argVal, arg') =
  case fVal of
    BuiltinLam b ts vs ->
      let fVal' = BuiltinLam b ts (argVal:vs)
      in deFuncBuiltin fVal' (rhsPair fexpr arg')
    LamVal p env body -> do
      (p', argVals) <- local (const env) (bindPat p argVal)
      let env' = setLEnv (addLocals argVals) env
      (ans, body') <- local (const env') (deFuncExpr body)
      return (ans, Let (lhsPair p' (envPat env))
                       (rhsPair arg' fexpr)
                       body')
    _ -> do env <- ask
            error $ "Unexpected dfval: " ++ show fVal ++ show env

deFuncBuiltin :: DFVal -> Expr -> DeFuncM (DFVal, Expr)
deFuncBuiltin val@(BuiltinLam b ts argVals) args =
  if length ts < numTyArgs b || length argVals < numArgs b
    then return (val, args)
    else case b of Fold -> deFuncFold ts (reverse argVals) args
                   _    -> return (DFNil, BuiltinApp b ts args)

deFuncFold :: [Type] -> [DFVal] -> Expr -> DeFuncM (DFVal, Expr)
deFuncFold ts [f, init, xs] args = do
  [fTy, initTy, TabType _ xsTy] <- builtinArgTypes 3 args
  (ans, p, body) <- canonicalLamExpr (f, fTy) [(init, initTy), (xs, xsTy)]
  return (ans, BuiltinApp (FoldDeFunc p body) ts args)

builtinArgTypes :: Int -> Expr -> DeFuncM [Type]
builtinArgTypes n expr = do ty <- getExprType expr
                            return $ consTypeToList n ty

canonicalLamExpr :: TypedDFVal -> [TypedDFVal] -> DeFuncM (DFVal, Pat, Expr)
canonicalLamExpr fTyped@(fval, fType) xsTyped = do
  let (xs, xsTypes) = unzip xsTyped
  freshVars <- mapM (const $ fresh "arg") (fTyped:xsTyped)
  let bindings = zip freshVars (fTyped:xsTyped)
      pat = posPat $ map RecLeaf $ zip freshVars (fType:xsTypes)
      update = setLEnv (addLocals $ bindings)
      (fExpr:xsExprs) = map (Var . fst) bindings
  (ans, body) <- local update $ foldM deFuncApp (fval, fExpr) (zip xs xsExprs)
  return (ans, pat, body)

instance RecTreeZip DFVal where
  recTreeZip (RecTree r) (RecVal r') = RecTree (recZipWith recTreeZip r r')
  recTreeZip (RecLeaf x) x' = RecLeaf (x, x')
