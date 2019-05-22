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
           | LamVal Pat DFEnv Expr
           | TLamVal [TBinder] DFEnv Expr
           | RecVal (Record DFVal)

data DFEnv = DFEnv { dfLEnv  :: Env (Type, DFVal)
                   , dfSubst :: Env Var
                   , dfTEnv  :: Env Type }

type DeFuncM a = ReaderT DFEnv (FreshRT (Either Err)) a

deFuncPass :: Decl -> TopPass (DFEnv, FreshScope) Decl
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
  Let p bound body -> do (x,  bound') <- recur bound
                         bindPat p x $ \p' -> do
                           (ans, body') <- recur body
                           return (ans, Let p' bound' body')
  Lam p body -> do env <- asks $ capturedEnv expr
                   return (LamVal p env body, envTupCon env)
  App (Builtin b) arg -> do (_, arg') <- recur arg
                            return (DFNil, App (Builtin b) arg')
  App (TApp (Builtin Fold) ts) arg -> deFuncFold ts arg
  TApp (Builtin Iota) [n] -> do n' <- subTy n
                                return $ (DFNil, TApp (Builtin Iota) [n'])
  App fexpr arg -> do
    (LamVal p env body, fexpr') <- recur fexpr
    (x, arg') <- recur arg
    bindEnv env $ \envPat -> do
      bindPat p x $ \p' -> do
        (ans, body') <- recur body
        return (ans, Let (lhsPair envPat p') (rhsPair fexpr' arg') body')
  Builtin _ -> error "Cannot defunctionalize raw builtins -- only applications"
  For b body -> bindVar b DFNil $ \b' -> do
                  (ans, body') <- recur body
                  return (ans, For b' body')
  Get e ie -> do (ans, e') <- recur e
                 ie' <- asks $ lookupSubst ie . dfSubst
                 return (ans, Get e' ie')
  RecCon r -> do r' <- traverse recur r
                 return (RecVal (fmap fst r'), RecCon (fmap snd r'))
  TLam b body -> do env <- asks $ capturedEnv expr
                    return (TLamVal b env body, envTupCon env)
  TApp fexpr ts -> do
    (TLamVal bs env body, fexpr') <- recur fexpr
    ts' <- mapM subTy ts
    bindEnv env $ \ep -> do
      extendWith (asDFTEnv $ bindFold $ zipWith replaceAnnot bs ts') $ do
        (ans, body') <- recur body
        return (ans, Let ep fexpr' body')
  Unpack b tv bound body -> do
    (val, bound') <- recur bound
    freshName tv $ \tv' ->
      extendWith (asDFTEnv $ tv @> TypeVar tv') $
        bindVar b val $ \b' -> do
          (ans, body') <- recur body
          return (ans, Unpack b' tv' bound' body')

  where recur = deFuncExpr

bindPat :: Pat -> DFVal -> (Pat -> DeFuncM a) -> DeFuncM a
bindPat pat xs cont = do
  pat' <- traverse (traverse subTy) pat
  freshenBinders pat' $ \subst pat'' -> do
    extendWith (asDFLEnv (bindRecZip pat' xs) <> asDFSubst subst) $
      cont $ fmap deFuncBinder (recTreeZip pat'' xs)
  where
    deFuncBinder (b, x) = fmap (deFuncType x) b

bindVar :: Binder -> DFVal -> (Binder -> DeFuncM a) -> DeFuncM a
bindVar b x cont = bindPat (RecLeaf b) x cont'
  where cont' (RecLeaf b) = cont b

bindEnv :: DFEnv -> (Pat -> DeFuncM a) -> DeFuncM a
bindEnv env cont = do
  freshenBinders envPat $ \subst envPat' -> do
    extendWith (DFEnv (bindRecZip envPat' tupVal) subst (dfTEnv env)) $
      cont $ fmap deFuncBinder (recTreeZip envPat' tupVal)
  where
    deFuncBinder (b, x) = fmap (deFuncType x) b
    (binders, vals) = unzip [(v %> ty, val) | (v, (ty, val)) <- envPairs (dfLEnv env)]
    envPat = posPat $ map RecLeaf binders
    tupVal = RecVal $ Tup vals

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
deFuncType (LamVal  _ env _) _ = RecType $ Tup (envTypes env)
deFuncType (TLamVal _ env _) _ = RecType $ Tup (envTypes env)

envTypes :: DFEnv -> [Type]
envTypes env = map (\(ty, val) -> deFuncType val ty) $ toList (dfLEnv env)

posPat = RecTree . Tup
lhsPair x y = posPat [x, y]
rhsPair x y = RecCon (Tup [x, y])

-- TODO: check/fail higher order case
deFuncFold :: [Type] -> Expr -> DeFuncM (DFVal, Expr)
deFuncFold ts (RecCon (Tup [Lam p body, x0, xs])) = do
  ts' <- traverse subTy ts
  (x0Val, x0') <- deFuncExpr x0
  (xsVal, xs') <- deFuncExpr xs
  bindPat p (RecVal (Tup [x0Val, xsVal])) $ \p' -> do
    (ans, body') <- deFuncExpr body
    return (ans, App (TApp (Builtin Fold) ts')
                     (RecCon (Tup [Lam p' body', x0', xs'])))

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
