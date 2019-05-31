module DeFunc (deFuncPass) where

import Syntax
import Env
import Record
import Pass
import PPrint
import Fresh
import Type

import Data.Foldable
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Except hiding (Except)

data DFVal = ExprVal Expr
           | Thunk DFEnv Expr  -- Expr must be Lam, TLam or to-be-inlined For
           | RecVal (Record DFVal)
               deriving Show

type DFEnv = FullEnv (Type, DFVal) Type
type TopEnv = (DFEnv, (Env Type, FreshScope))
type DeFuncM a = WriterT [Decl] (ReaderT DFEnv (FreshT (Either Err))) a

-- TODO: roll outvar type env and fresh scope into one, in some RW monad
deFuncPass :: TopDecl -> TopPass TopEnv TopDecl
deFuncPass decl = case decl of
  TopLet b@(Bind v ty) expr -> do -- TODO: type might change!
    (expr', buildVal) <- deFuncTop expr
    env <- getEnv
    let ty' = getType (asLEnv (fst (snd env))) expr'
    putEnv $ outEnv (v %> ty') (buildVal (Var v))
    return $ TopLet (v %> ty') expr'
  -- TopUnpack b iv expr -> do
  --   (val, expr') <- deFuncTop expr
  --   let b' = fmap (deFuncType val) b
  --   putEnv $   outEnv b' val
  --           <> (asDFTEnv (iv @> TypeVar iv), newScope iv)
  --   return $ TopUnpack b' iv expr'
  EvalCmd NoOp -> return (EvalCmd NoOp)
  EvalCmd (Command cmd expr) -> do
    (expr', _) <- deFuncTop expr
    case cmd of Passes -> writeOut $ "\n\nDefunctionalized\n" ++ pprint expr'
                _ -> return ()
    return $ EvalCmd (Command cmd expr')

deFuncTop :: Expr -> TopPass TopEnv (Expr, Expr -> DFVal)
deFuncTop expr = do
  (env, (_, scope)) <- getEnv
  (outVal, decls) <- liftEither $ flip runFreshT scope $ flip runReaderT env $
                       runWriterT $ deFuncExpr expr
  return $ captureScope decls outVal

outEnv :: Binder -> DFVal -> TopEnv
outEnv b x = (asLEnv (bindWith b x), (bind b, foldMap newScope (binderVars b)))

deFuncExpr :: Expr -> DeFuncM DFVal
deFuncExpr expr = case expr of
  Var v -> asks $ snd . (!v) . lEnv
  Lit l -> return $ ExprVal (Lit l)
  Decls decls body -> foldr deFuncDecl (recur body) decls
  Lam _ _ -> makeThunk expr
  App (TApp (Builtin Fold) ts) arg -> deFuncFold ts arg
  App (Builtin b) arg -> do
    arg' <- recur arg
    return $ ExprVal $ App (Builtin b) (fromExprVal arg')
  TApp (Builtin Iota) [n] -> do
    n' <- subTy n
    return $ ExprVal $ TApp (Builtin Iota) [n']
  App fexpr arg -> do
    Thunk env (Lam b body) <- recur fexpr
    arg' <- recur arg
    bindVal b arg' $ extendWith env $ recur body
  Builtin _ -> error "Cannot defunctionalize raw builtins -- only applications"
  -- For b body -> bindVal b DFNil $ \b' -> do
  --                 (ans, body') <- recur body
  --                 return (TabVal (binderAnn b') ans, For b' body')
  -- Get e ie -> do (val, e') <- recur e
  --                case val of
  --                  TabVal _ ans -> do
  --                    ie' <- asks $ lookupSubst ie . dfSubst
  --                    return (ans, Get e' ie')
  --                  v -> error $ show v
  RecCon r -> liftM RecVal $ traverse recur r
  RecGet e field -> do RecVal val <- recur e
                       return $ recGet val field
  TLam _ _ -> makeThunk expr
  TApp fexpr ts -> do
    Thunk env (TLam bs body) <- recur fexpr
    ts' <- mapM subTy ts
    extendWith env $ do
      extendWith (asTEnv $ bindFold $ zipWith replaceAnnot bs ts') $ do
        recur body
  where recur = deFuncExpr

deFuncDecl :: Decl -> DeFuncM DFVal -> DeFuncM DFVal
deFuncDecl decl cont = case decl of
  Let b bound -> do
    x <- deFuncExpr bound
    bindVal b x $ cont
  Unpack (Bind v ty) tv bound -> do
    ExprVal bound' <- deFuncExpr bound
    tv' <- freshLike tv
    extendWith (asTEnv $ tv @> TypeVar tv') $ do
      v' <- freshLike v
      ty' <- subTy ty
      extendWith (asLEnv (v @> (ty', ExprVal (Var v')))) $ do
        tell [Unpack (v'%>ty') tv' bound']
        cont

captureScope :: [Decl] -> DFVal -> (Expr, Expr -> DFVal)
captureScope decls (ExprVal expr) = (Decls decls expr, ExprVal)
captureScope decls (RecVal r) = (RecCon (fmap fst zipped), buildVal)
  where
    zipped = fmap (captureScope decls) r
    builders = fmap snd zipped
    buildVal newVal = RecVal $ fmap (\(k,f) -> f (RecGet newVal k))
                                    (recNameVals builders)
captureScope decls val = (Decls decls $ RecCon (fmap Var vs), buildVal)
  where
    vsBound = concat $ map getBoundLVar decls
    getBoundLVar decl = case decl of Let b _ -> binderVars b
                                     Unpack b _ _ -> binderVars b
    vs = Tup $ envNames $ envSubset vsBound $ freeOutVars val
    buildVal newVal = subOutVars sub val
      where sub = fold $ fmap (\(k,v) -> v@>(RecGet newVal k)) (recNameVals vs)

subOutVars :: Env Expr -> DFVal -> DFVal
subOutVars subst val = case val of
  ExprVal expr -> ExprVal $ subAtomicExpr subst expr
  Thunk (FullEnv lenv tenv) expr -> Thunk (FullEnv lenv' tenv) expr
    where lenv' = fmap (\(ty,val) -> (ty, subOutVars subst val)) lenv
  RecVal r -> RecVal $ fmap (subOutVars subst) r

freeOutVars :: DFVal -> Env ()
freeOutVars val = case val of
  ExprVal expr -> foldMap (@>()) $ freeLVars expr
  Thunk env _ -> foldMap (freeOutVars . snd) (lEnv env)
  RecVal r -> foldMap freeOutVars r

subAtomicExpr :: Env Expr -> Expr -> Expr
subAtomicExpr subst expr = case expr of
  Lit _ -> expr
  Var v -> case envLookup subst v of Just expr' -> expr'
                                     Nothing    -> expr
  _ -> error $ "Is this atomic? " ++ pprint subst

bindVal :: Binder -> DFVal -> DeFuncM a -> DeFuncM a
bindVal (Bind v ty) val cont = do
  ty' <- subTy ty
  val' <- atomize v ty' val
  extendWith (asLEnv (v @> (ty', val'))) $ cont

atomize :: Name -> Type -> DFVal -> DeFuncM DFVal
atomize nameHint ty val = case val of
  Thunk _ _ -> return val
  RecVal rVal -> do let (RecType rTy) = ty
                    rVal' <- sequence $ recZipWith (atomize nameHint) rTy rVal
                    return (RecVal rVal')
  ExprVal expr -> if inlinable expr then return val
                                    else materialize expr
  where
    materialize :: Expr -> DeFuncM DFVal
    materialize expr = do
      v <- freshLike nameHint
      tell [Let (v %> ty) expr]
      return $ ExprVal (Var v)


-- TODO: add more context information
inlinable :: Expr -> Bool
inlinable expr = case expr of
  Lit _ -> True
  Var _ -> True
  _     -> False

fromExprVal :: DFVal -> Expr
fromExprVal (ExprVal expr) = expr
fromExprVal (RecVal r)  = RecCon $ fmap fromExprVal r
fromExprVal (Thunk _ _) = error "Unevaluated expression"

makeThunk :: Expr -> DeFuncM DFVal
makeThunk expr = do FullEnv lenv tenv <- ask
                    let lenv' = envSubset (freeLVars expr) lenv
                    return $ Thunk (FullEnv lenv' tenv) expr

subTy :: Type -> DeFuncM Type
subTy ty = do env <- asks tEnv
              return $ maybeSub (Just . (env!)) ty

-- TODO: check/fail higher order case
deFuncFold :: [Type] -> Expr -> DeFuncM DFVal
deFuncFold ts (RecCon (Tup [For ib (Lam xb body), x])) = undefined -- do
  -- ts' <- traverse subTy ts
  -- xVal <- deFuncExpr x
  -- bindVal b DFNil $ \b' ->
  --   bindVal xb xVal $ \p' -> do
  --     (ans, body') <- deFuncExpr body
  --     return (ans, App (TApp (Builtin Fold) ts')
  --                      (RecCon (Tup [For b' (Lam p' body'), x'])))
