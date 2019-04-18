module DeFunc (deFuncPass) where

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
import Control.Monad.State (put, gets)
import Control.Monad.Writer (tell)
import Control.Monad.Reader (Reader, runReader, local, ask, asks)

type DFEnv = FullEnv TypedDFVal (Maybe Type)

type TypedDFVal = (DFVal, Type) -- type is post-defunctionalization

data DFVal = DFNil
           | LamVal Pat DFEnv Expr
           | TLamVal [TBinder] DFEnv Expr
           | BuiltinLam Builtin [Type] [DFVal]
           | RecVal (Record DFVal)

type DeFuncM a = MonadPass DFEnv () a

deFuncPass :: Decl -> TopMonadPass DFEnv Decl
deFuncPass decl = case decl of
  TopLet (v,_) expr -> do
    ((val,ty), expr') <- deFuncTop expr
    put $ newFullEnv [(v, (val,ty))] []
    return $ TopLet (v, ty) expr'
  TopUnpack (v,_) iv expr -> do
    ((val,ty), expr') <- deFuncTop expr
    ty' <- liftExcept $ unpackExists ty iv
    put $ newFullEnv [(v, (val,ty'))] [(iv,Nothing)]
    return $ TopUnpack (v, ty') iv expr'
  EvalCmd NoOp -> put mempty >> return (EvalCmd NoOp)
  EvalCmd (Command cmd expr) -> do
    ((val,ty), expr') <- deFuncTop expr
    put mempty
    case cmd of Passes  -> do tell ["\n\nDefunctionalized\n" ++ pprint expr']
                _ -> return ()
    return $ EvalCmd (Command cmd expr')

  where
    deFuncTop :: Expr -> TopMonadPass DFEnv (TypedDFVal, Expr)
    deFuncTop expr = do
      (val, expr') <- liftTopPass () (deFuncExpr expr)
      typingEnv <- gets $ asTypingEnv
      ty <- liftExcept $ checkExpr typingEnv expr'
      return ((val, ty), expr')

asTypingEnv :: DFEnv -> TypeEnv
asTypingEnv = setTEnv (fmap (const IdxSetKind)) . setLEnv (fmap snd)

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
  For (v,ty) body -> do ty' <- subTy ty
                        (ans, body') <- recurWith [(v, (DFNil, ty'))] body
                        return (ans, For (v,ty') body')
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
          let env' = setTEnv (addVs (zip (map fst bs) (map Just ts'))) env
          (ans, body') <- local (const env') (deFuncExpr body)
          return (ans, Let (envPat env) fexpr' body')
  Unpack b tv bound body -> do
    (val, bound') <- recur bound
    let updateT = setTEnv (addV (tv, Nothing))
    (b', valTy) <- local updateT (deFuncBinder (b,val))
    let updateL = setLEnv (addV valTy)
    (ans, body') <- local (updateL . updateT) (deFuncExpr body)
    return (ans, Unpack b' tv bound' body')

  where recur = deFuncExpr
        recurWith  xs = local (setLEnv $ addVs xs) . deFuncExpr
        unitLit = RecCon (Tup [])

subTy :: Type -> DeFuncM Type
subTy ty = do { tenv <- asks tEnv; return $ maybeSub (tenv !) ty }

bindPat :: Pat -> DFVal -> DeFuncM (Pat, RecTree (Var, TypedDFVal))
bindPat pat val = do
  zipped <- traverse deFuncBinder (recTreeZip pat val)
  return (fmap fst zipped, fmap snd zipped)

deFuncBinder :: (Binder, DFVal) -> DeFuncM (Binder, (Var, TypedDFVal))
deFuncBinder ((v, ty), val) = do ty' <- subTy ty
                                 return ( (v, deFuncType val ty')
                                        , (v, (val, ty')) )

deFuncType :: DFVal -> Type -> Type
deFuncType (RecVal r) (RecType r') = RecType $ recZipWith deFuncType r r'
deFuncType DFNil t = t
deFuncType (LamVal p env _) _   = RecType $ Tup (envTypes env)
deFuncType (TLamVal _ env _)  _ = RecType $ Tup (envTypes env)
deFuncType (BuiltinLam b ts exprs) _ = error "not implemented"

getExprType :: Expr -> DeFuncM Type
getExprType expr = do
  env <- asks asTypingEnv
  return $ getType env expr

consTypeToList :: Int -> Type -> [Type]
consTypeToList n t = reverse $ recur n t
  where recur 0 _ = []
        recur n (RecType (Tup [xs, x])) = x : recur (n-1) xs

posPat = RecTree . Tup
lhsPair x y = posPat [x, y]
rhsPair x y = RecCon (Tup [x, y])

envTypes :: DFEnv -> [Type]
envTypes env = map snd $ toList (lEnv env)

envPat :: DFEnv -> Pat
envPat env = RecTree $ Tup [RecLeaf (v,ty) | (v,(_,ty)) <- envPairs (lEnv env)]

envTupCon :: DFEnv -> Expr
envTupCon env = RecCon $ Tup (map Var $ envVars (lEnv env))

deFuncApp :: (DFVal, Expr) -> (DFVal, Expr) -> DeFuncM (DFVal, Expr)
deFuncApp (fVal, fexpr) (argVal, arg') =
  case fVal of
    BuiltinLam b ts vs ->
      let fVal' = BuiltinLam b ts (argVal:vs)
      in deFuncBuiltin fVal' (rhsPair fexpr arg')
    LamVal p env body -> do
      (p', argVals) <- local (const env) (bindPat p argVal)
      let env' = setLEnv (addVs argVals) env
      (ans, body') <- local (const env') (deFuncExpr body)
      return (ans, Let (lhsPair p' (envPat env))
                       (rhsPair arg' fexpr)
                       body')

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
      update = setLEnv (addVs $ bindings)
      (fExpr:xsExprs) = map (Var . fst) bindings
  (ans, body) <- local update $ foldM deFuncApp (fval, fExpr) (zip xs xsExprs)
  return (ans, pat, body)

instance RecTreeZip DFVal where
  recTreeZip (RecTree r) (RecVal r') = RecTree (recZipWith recTreeZip r r')
  recTreeZip (RecLeaf x) x' = RecLeaf (x, x')
