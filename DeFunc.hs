module DeFunc (deFuncPass) where

import Syntax
import Env
import Record
import Pass
import PPrint
import Fresh

import Data.Foldable
import Control.Monad.Reader
import qualified Data.Map.Strict as M

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
    putEnv (newFullEnv [(v, (ty', val))] [], newScope v)
    return $ TopLet (v, ty') expr'
  TopUnpack (v,ty) iv expr -> do
    (val, expr') <- deFuncTop expr
    let ty' = deFuncType ty val
    putEnv (newFullEnv [(v, (ty',val))] [], newScope v)
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
subTy ty = do tenv  <- asks $ tEnv . fst
              subst <- asks $ varSubst . snd
              let f v = Just $ case envLookup tenv v of
                          Just ty -> ty
                          Nothing ->
                            if v `isin` subst then TypeVar (subst ! v)
                                              else TypeVar v
              return $ maybeSub f ty

bindVar :: Binder -> DFVal -> DeFuncM (Binder, DFCtx)
bindVar (v, ty) x = do ty' <- subTy ty
                       (v', newScope) <- asks $ rename v . snd
                       return ((v', deFuncType ty' x),
                               (FullEnv (newEnv [(v, (ty', x))]) mempty, newScope))

bindPat :: Pat -> DFVal -> DeFuncM (Pat, DFCtx)
bindPat pat x = do zipped <- traverse (uncurry bindVar) (recTreeZip pat x)
                   return (fmap fst zipped, fold (fmap snd zipped))

bindEnv :: DFEnv -> DeFuncM (Pat, DFCtx)
bindEnv env = do
  zipped <- traverse (uncurry bindVar) (map reassoc $ envPairs (lEnv env))
  return (asTree (map fst zipped), fold (fmap snd zipped) <> tyCtx)
  where reassoc (v,(ty,val)) = ((v,ty),val)
        asTree xs = RecTree (Tup (map RecLeaf xs))
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

-- Fresh var management - should eventually split into separate module

extendWith :: (MonadReader env m, Monoid env) => env -> m a -> m a
extendWith env m = local (env <>) m

rename :: Var -> FreshScope -> (Var, FreshScope)
rename v@(Name [(tag, _)]) (FreshScope _ vars) = (v', scopeDiff)
  where n = M.findWithDefault 0 tag vars
        v' = Name [(tag, n)]
        scopeDiff = FreshScope (newEnv [(v, v')]) (M.singleton tag (n+1))

getRenamed :: Var -> FreshScope -> Var
getRenamed v scope = case envLookup (varSubst scope) v of
                       Just v' -> v'
                       Nothing -> v

newScope :: Var -> FreshScope
newScope (Name [(tag, i)]) = FreshScope mempty (M.singleton tag (i+1))

data FreshScope = FreshScope
  { varSubst    :: Env Var
  , varsInScope :: M.Map Tag Int }  deriving (Show)

instance Semigroup FreshScope where
  (FreshScope a b) <> (FreshScope a' b') =
    FreshScope (a<>a') (M.unionWith max b b')

instance Monoid FreshScope where
  mempty = FreshScope mempty mempty
  mappend = (<>)
