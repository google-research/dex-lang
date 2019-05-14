module DeFunc (deFuncPass) where

import Syntax
import Env
import Record
import Pass
import PPrint
import Fresh

import Data.Foldable
import Control.Monad.Reader

data DFVal = DFNil
           | LamVal Pat DFEnv Expr
           | TLamVal [TBinder] DFEnv Expr
           | RecVal (Record DFVal)

type DFCtx = (DFEnv, FreshScope)
type DeFuncM a = Pass (DFEnv,  FreshScope) () a
type DFEnv = FullEnv (Type, DFVal) Type

-- TODO: top-level freshness
deFuncPass :: Decl -> TopPass DFCtx Decl
deFuncPass decl = case decl of
  TopLet (v,ty) expr -> do
    (val, expr') <- deFuncTop expr
    let ty' = deFuncType ty val
    putEnv (FullEnv (v @> (ty', val)) mempty, newScope v)
    return $ TopLet (v, ty') expr'
  TopUnpack (v,ty) iv expr -> do
    (val, expr') <- deFuncTop expr
    let ty' = deFuncType ty val
    putEnv (FullEnv (v @> (ty',val)) mempty, newScope v)
    return $ TopUnpack (v, ty') iv expr'
  EvalCmd NoOp -> return (EvalCmd NoOp)
  EvalCmd (Command cmd expr) -> do
    (_, expr') <- deFuncTop expr
    case cmd of Passes -> writeOut $ "\n\nDefunctionalized\n" ++ pprint expr'
                _ -> return ()
    return $ EvalCmd (Command cmd expr')
  where
    deFuncTop :: Expr -> TopPass DFCtx (DFVal, Expr)
    deFuncTop expr = liftTopPass () (deFuncExpr expr)

deFuncExpr :: Expr -> DeFuncM (DFVal, Expr)
deFuncExpr expr = case expr of
  Var v     -> do val <- asks $ snd . (! v) . lEnv . fst
                  v'  <- asks $ getRenamed v . snd
                  return (val, Var v')
  Lit l     -> return (DFNil, Lit l)
  Let p bound body -> do (x,  bound') <- recur bound
                         (p', ctx) <- bindPat p x
                         (ans, body') <- extendWith ctx (recur body)
                         return (ans, Let p' bound' body')
  Lam p body -> do env <- asks $ capturedEnv expr . fst
                   closure <- envTupCon env
                   return (LamVal p env body, closure)
  App (Builtin b) arg -> do (_, arg') <- recur arg
                            return (DFNil, App (Builtin b) arg')
  App (TApp (Builtin Fold) ts) arg -> deFuncFold ts arg
  App fexpr arg -> deFuncApp fexpr arg
  Builtin _ -> error "Cannot defunctionalize raw builtins -- only applications"
  For b body -> do (b', ctx) <- bindVar b DFNil
                   (ans, body') <- extendWith ctx (recur body)
                   return (ans, For b' body')
  Get e ie -> do (ans, e') <- recur e
                 ie' <- asks $ getRenamed ie . snd
                 return (ans, Get e' ie')
  RecCon r -> do r' <- traverse recur r
                 return (RecVal (fmap fst r'), RecCon (fmap snd r'))
  TLam b body -> do env <- asks $ capturedEnv expr . fst
                    closure <- envTupCon env
                    return (TLamVal b env body, closure)
  TApp fexpr ts -> do
    (TLamVal bs env body, fexpr') <- recur fexpr
    ts' <- mapM subTy ts
    (ep, envCtx) <- bindEnv env
    let tyCtx = (FullEnv mempty (newEnv (zip (map fst bs) ts')), mempty)
    extendWith (tyCtx <> envCtx) $ do
      (ans, body') <- recur body
      return (ans, Let ep fexpr' body')
  Unpack b tv bound body -> do
    (val, bound') <- recur bound
    (tv', freshCtx) <- asks $ rename tv . snd
    extendWith (mempty, freshCtx) $ do
       (b', ctx) <- bindVar b val
       (ans, body') <- extendWith ctx (recur body)
       return (ans, Unpack b' tv' bound' body')

  where recur = deFuncExpr

deFuncApp :: Expr -> Expr -> DeFuncM (DFVal, Expr)
deFuncApp fexpr arg = do
  (LamVal p env body, fexpr') <- deFuncExpr fexpr
  (envPat, ctx) <- bindEnv env
  (x, arg') <- deFuncExpr arg
  (p', ctx') <- extendWith (env, mempty) (bindPat p x)
  extendWith (ctx' <> ctx) $ do
    (ans, body') <- deFuncExpr body
    return (ans, Let (lhsPair envPat p')
                     (rhsPair fexpr' arg') body')

capturedEnv :: Expr -> FullEnv a b -> FullEnv a b
capturedEnv expr env = setLEnv (envSubset (freeLVars expr)) env

envTupCon :: DFEnv -> DeFuncM Expr
envTupCon env = do
  subst <- asks snd
  let vs = map (Var . flip getRenamed subst) (envNames (lEnv env))
  return $ RecCon $ Tup vs

subTy :: Type -> DeFuncM Type
subTy ty = do env <- ask
              return $ subTy' env ty

subTy' :: DFCtx -> Type -> Type
subTy' ctx ty = maybeSub f ty
  where f v = Just $ case envLookup (tEnv (fst ctx)) v of
                       Just ty' -> ty'
                       Nothing  -> TypeVar (getRenamed v (snd ctx))

deFuncBinder :: Binder -> DFVal -> EnvM DFCtx Binder
deFuncBinder (v, ty) x = do env <- askEnv
                            let ty' = subTy' env ty
                                (v', scope) = rename v (snd env)
                            addEnv (FullEnv (v @> (ty', x)) mempty, scope)
                            return (v', deFuncType ty' x)


bindPat :: Pat -> DFVal -> DeFuncM (Pat, DFCtx)
bindPat pat xs = liftEnvM $ traverse (uncurry deFuncBinder) (recTreeZip pat xs)

bindVar :: Binder -> DFVal -> DeFuncM (Binder, DFCtx)
bindVar b x = liftEnvM $ deFuncBinder b x

bindEnv :: DFEnv -> DeFuncM (Pat, DFCtx)
bindEnv env = do
  (bs', env') <- liftEnvM $ traverse (uncurry deFuncBinder) bs
  return (posPat (map RecLeaf bs'), env' <> tyCtx)
  where bs = [((v,ty),val) | (v,(ty,val)) <- envPairs (lEnv env)]
        tyCtx = (FullEnv mempty (tEnv env), mempty)

deFuncType :: Type -> DFVal -> Type
deFuncType (RecType r) (RecVal r') = RecType $ recZipWith deFuncType r r'
deFuncType t DFNil = t
deFuncType _ (LamVal  _ env _) = RecType $ Tup (envTypes env)
deFuncType _ (TLamVal _ env _) = RecType $ Tup (envTypes env)

envTypes :: DFEnv -> [Type]
envTypes env = map (uncurry deFuncType) $ toList (lEnv env)

posPat = RecTree . Tup
lhsPair x y = posPat [x, y]
rhsPair x y = RecCon (Tup [x, y])

-- TODO: check/fail higher order case
deFuncFold :: [Type] -> Expr -> DeFuncM (DFVal, Expr)
deFuncFold ts (RecCon (Tup [Lam p body, x0, xs])) = do
  ts' <- traverse subTy ts
  (x0Val, x0') <- deFuncExpr x0
  (xsVal, xs') <- deFuncExpr xs
  (p', bindings) <- bindPat p (RecVal (Tup [x0Val, xsVal]))
  (ans, body') <- extendWith bindings (deFuncExpr body)
  return (ans, App (TApp (Builtin Fold) ts')
                   (RecCon (Tup [Lam p' body', x0', xs'])))

instance RecTreeZip DFVal where
  recTreeZip (RecTree r) (RecVal r') = RecTree (recZipWith recTreeZip r r')
  recTreeZip (RecLeaf x) x' = RecLeaf (x, x')
