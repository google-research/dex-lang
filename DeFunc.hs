module DeFunc (deFuncPass) where

import Syntax
import Env
import Record
import Pass
import PPrint
import Fresh

import Data.Foldable
import Control.Monad.Reader
import Control.Monad.Except hiding (Except)

data DFVal = DFNil
           | Thunk DFEnv Expr
           | RecVal (Record DFVal)
           | TabVal Type DFVal  deriving Show

data DFEnv = DFEnv { dfLEnv  :: Env (Type, DFVal)
                   , dfSubst :: Env Var
                   , dfTEnv  :: Env Type }  deriving Show

type DeFuncM a = ReaderT DFEnv (FreshRT (Either Err)) a

deFuncPass :: TopDecl -> TopPass (DFEnv, FreshScope) TopDecl
deFuncPass decl = case decl of
  TopLet b expr -> do
    (val, expr') <- deFuncTop expr
    let b' = fmap (deFuncType val) b
    putEnv $ outEnv b' val
    return $ TopLet b' expr'
  TopUnpack b iv expr -> do
    (val, expr') <- deFuncTop expr
    let b' = fmap (deFuncType val) b
    putEnv $   outEnv b' val
            <> (asDFTEnv (iv @> TypeVar iv), newScope iv)
    return $ TopUnpack b' iv expr'
  EvalCmd NoOp -> return (EvalCmd NoOp)
  EvalCmd (Command cmd expr) -> do
    (_, expr') <- deFuncTop expr
    case cmd of Passes -> writeOut $ "\n\nDefunctionalized\n" ++ pprint expr'
                _ -> return ()
    return $ EvalCmd (Command cmd expr')
  where
    deFuncTop :: Expr -> TopPass (DFEnv, FreshScope) (DFVal, Expr)
    deFuncTop expr = do
      (env, scope) <- getEnv
      liftEither $ runFreshRT (runReaderT (deFuncExpr expr) env) scope
    outEnv :: Binder -> DFVal -> (DFEnv, FreshScope)
    outEnv b x = (asDFLEnv (bindWith b x), foldMap newScope (binderVars b))

deFuncExpr :: Expr -> DeFuncM (DFVal, Expr)
deFuncExpr expr = case expr of
  Var v -> do val <- asks $ snd . (!v) . dfLEnv
              var <- asks $ Var . lookupSubst v . dfSubst
              return (val, var)
  Lit l -> return (DFNil, Lit l)
  Decls decls body -> foldr deFuncDecl (recur body) decls
  Lam _ _ -> makeThunk expr
  App (TApp (Builtin Fold) ts) arg -> deFuncFold ts arg
  App (Builtin b) arg -> do (_, arg') <- recur arg
                            return (DFNil, App (Builtin b) arg')
  TApp (Builtin Iota) [n] -> do n' <- subTy n
                                return $ (TabVal n' DFNil, TApp (Builtin Iota) [n'])
  App fexpr arg -> do
    (Thunk env (Lam b body), fexpr') <- recur fexpr
    (x, arg') <- recur arg
    bindVal b x $ \b' -> do
      (ans, body') <- bindEnv env fexpr' (recur body)
      return (ans, Decls [Let b' arg'] body')
  Builtin _ -> error "Cannot defunctionalize raw builtins -- only applications"
  For b body -> bindVal b DFNil $ \b' -> do
                  (ans, body') <- recur body
                  return (TabVal (binderAnn b') ans, For b' body')
  Get e ie -> do (val, e') <- recur e
                 case val of
                   TabVal _ ans -> do
                     ie' <- asks $ lookupSubst ie . dfSubst
                     return (ans, Get e' ie')
                   v -> error $ show v
  RecCon r -> do r' <- traverse recur r
                 return (RecVal (fmap fst r'), RecCon (fmap snd r'))
  RecGet e field -> do (RecVal val, e') <- recur e
                       return (recGet val field, RecGet e' field)
  TLam _ _ -> makeThunk expr
  TApp fexpr ts -> do
    (Thunk env (TLam bs body), fexpr') <- recur fexpr
    ts' <- mapM subTy ts
    bindEnv env fexpr' $ do
      extendWith (asDFTEnv $ bindFold $ zipWith replaceAnnot bs ts') $ do
        (ans, body') <- recur body
        return (ans, body')

  where recur = deFuncExpr

deFuncDecl :: Decl -> DeFuncM (DFVal, Expr) -> DeFuncM (DFVal, Expr)
deFuncDecl decl cont = case decl of
  Let b bound -> do
    (x,  bound') <- deFuncExpr bound
    bindVal b x $ \b' -> do
      (ans, body') <- cont
      return (ans, wrapDecl (Let b' bound') body')
  Unpack b tv bound -> do
    (val, bound') <- deFuncExpr bound
    freshName tv $ \tv' ->
      extendWith (asDFTEnv $ tv @> TypeVar tv') $
        bindVal b val $ \b' -> do
          (ans, body') <- cont
          return (ans, wrapDecl (Unpack b' tv' bound') body')

makeThunk :: Expr -> DeFuncM (DFVal, Expr)
makeThunk expr = do env <- asks $ capturedEnv expr
                    return (Thunk env expr, envTupCon env)

bindVal :: Binder -> DFVal -> (Binder -> DeFuncM a) -> DeFuncM a
bindVal b x cont = do
  b' <- traverse subTy b
  freshenBinder b' $ \subst b'' -> do
    extendWith (asDFLEnv (bindWith b' x) <> asDFSubst subst) $
      cont $ fmap (deFuncType x) b''

bindEnv :: DFEnv -> Expr -> DeFuncM (a, Expr) -> DeFuncM (a, Expr)
bindEnv env envExpr body = undefined

capturedEnv :: Expr -> DFEnv -> DFEnv
capturedEnv expr (DFEnv lenv subst tenv) = DFEnv lenv' subst' tenv
  where vs = freeLVars expr
        lenv'  = envSubset vs lenv
        subst' = envSubset vs subst

envTupCon :: DFEnv -> Expr
envTupCon env = RecCon $ Tup exprs
  where vs = envNames (dfLEnv env)
        exprs = map (Var . flip lookupSubst (dfSubst env)) vs

subTy :: Type -> DeFuncM Type
subTy ty = do env <- asks dfTEnv
              return $ maybeSub (Just . (env!)) ty

deFuncType :: DFVal -> Type -> Type
deFuncType (RecVal r) (RecType r') = RecType $ recZipWith deFuncType r r'
deFuncType DFNil t = t
deFuncType (Thunk env _) _ = RecType $ Tup (envTypes env)
deFuncType (TabVal n val) (TabType _ ty) = TabType n (deFuncType val ty)


envTypes :: DFEnv -> [Type]
envTypes env = map (\(ty, val) -> deFuncType val ty) $ toList (dfLEnv env)

-- TODO: check/fail higher order case
deFuncFold :: [Type] -> Expr -> DeFuncM (DFVal, Expr)
deFuncFold ts (RecCon (Tup [For b (Lam p body), x])) = do
  ts' <- traverse subTy ts
  (xVal, x') <- deFuncExpr x
  bindVal b DFNil $ \b' ->
    bindVal p xVal $ \p' -> do
      (ans, body') <- deFuncExpr body
      return (ans, App (TApp (Builtin Fold) ts')
                       (RecCon (Tup [For b' (Lam p' body'), x'])))

instance RecTreeZip DFVal where
  recTreeZip (RecTree r) (RecVal r') = RecTree (recZipWith recTreeZip r r')
  recTreeZip (RecLeaf x) x' = RecLeaf (x, x')

asDFLEnv  env = DFEnv env    mempty mempty
asDFSubst env = DFEnv mempty env    mempty
asDFTEnv  env = DFEnv mempty mempty env

instance Semigroup DFEnv where
  DFEnv x y z <> DFEnv x' y' z' = DFEnv (x<>x') (y<>y') (z<>z')

instance Monoid DFEnv where
  mempty = DFEnv mempty mempty mempty
  mappend = (<>)
