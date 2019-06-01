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


-- TODO: consider making this just Expr with the thunk case as an annotation
data Atom = AExpr Expr
          | ARecCon (Record Atom)
          | AFor Binder Atom
          | Thunk DFEnv Expr  -- Lam | TLam | For
             deriving Show

type DFEnv = FullEnv (Type, Atom) Type
type TopEnv = (DFEnv, (Env Type, FreshScope))
type DeFuncM a = WriterT [Decl] (ReaderT DFEnv (FreshT (Either Err))) a

-- TODO: roll outvar type env and fresh scope into one, in some RW monad
deFuncPass :: TopDecl -> TopPass TopEnv TopDecl
deFuncPass decl = case decl of
  TopLet (Bind v _) expr -> do -- TODO: type might change!
    (expr', ty, buildVal) <- deFuncTop expr
    putEnv $ outEnv (v %> ty) (buildVal (Var v))
    return $ TopLet (v %> ty) expr'
  TopUnpack b iv expr -> do
    expr' <- deFuncTopUnpack expr
    putEnv $ outEnv b (AExpr (Var (rawName "bug")))
              <> (asTEnv (iv @> TypeVar iv), (mempty, newScope iv))
    return $ TopUnpack b iv expr'
  EvalCmd NoOp -> return (EvalCmd NoOp)
  EvalCmd (Command cmd expr) -> do
    (expr', _, _) <- deFuncTop expr
    case cmd of Passes -> writeOut $ "\n\nDefunctionalized\n" ++ pprint expr'
                _ -> return ()
    return $ EvalCmd (Command cmd expr')

deFuncTop :: Expr -> TopPass TopEnv (Expr, Type, Expr -> Atom)
deFuncTop expr = do
  (env, (_, scope)) <- getEnv
  (outVal, decls) <- liftEither $ flip runFreshT scope $ flip runReaderT env $
                       runWriterT $ deFuncExpr expr
  return $ deFuncScope decls outVal

deFuncTopUnpack :: Expr -> TopPass TopEnv Expr
deFuncTopUnpack expr = do
  (env, (_, scope)) <- getEnv
  (AExpr outVal, decls) <- liftEither $ flip runFreshT scope $ flip runReaderT env $
                       runWriterT $ deFuncExpr expr
  return $ Decls decls outVal

outEnv :: Binder -> Atom -> TopEnv
outEnv b x = (asLEnv (bindWith b x), (bind b, foldMap newScope (binderVars b)))

deFuncExpr :: Expr -> DeFuncM Atom
deFuncExpr expr = case expr of
  Var v -> askLEnv v
  Lit l -> return $ AExpr (Lit l)
  Decls decls body -> foldr deFuncDecl (recur body) decls
  Lam _ _ -> makeThunk expr
  App (TApp (Builtin Fold) ts) arg -> deFuncFold ts arg
  App (Builtin b) arg -> do
    arg' <- recur arg
    materialize (rawName "tmp") (builtinOutTy b) $ App (Builtin b) (fromAExpr arg')
  TApp (Builtin Iota) [n] -> do
    n' <- subTy n
    return $ AExpr $ TApp (Builtin Iota) [n']
  App fexpr arg -> do
    Thunk env (Lam b body) <- recur fexpr
    arg' <- recur arg
    bindVal b arg' $ extendWith env $ recur body
  Builtin _ -> error "Cannot defunctionalize raw builtins -- only applications"
  For (Bind v ty) body -> do
    ty' <- subTy ty
    v' <- freshLike v
    extendWith (asLEnv (v @> (ty', (AExpr (Var v'))))) $ do
       (body', bodyTy, atomBuilder) <- deFuncScoped body
       outVar <- freshLike (rawName "tab")
       let b' = (v'%>ty')
       tell [Let (outVar %> (TabType ty' bodyTy)) (For b' body')]
       return $ AFor b' (atomBuilder (Get (Var outVar) v'))
  Get e ie -> do
    e' <- recur e
    AExpr (Var ie') <- askLEnv ie
    case e' of
      AExpr tabExpr -> return $ AExpr $ Get tabExpr ie -- TODO: optimize `for` case
      AFor b body -> do
        local (const mempty) $
          extendWith (asLEnv (bindWith b (AExpr (Var ie')))) $
            applySubstAtom body
  RecCon r -> liftM ARecCon $ traverse recur r
  RecGet e field -> do
    val <- recur e
    return $ case val of
      ARecCon r -> recGet r field
      AExpr e' -> AExpr (RecGet e' field)
  TLam _ _ -> makeThunk expr
  TApp fexpr ts -> do
    Thunk env (TLam bs body) <- recur fexpr
    ts' <- mapM subTy ts
    extendWith env $ do
      extendWith (asTEnv $ bindFold $ zipWith replaceAnnot bs ts') $ do
        recur body
  where recur = deFuncExpr

applySubstAtom :: Atom -> DeFuncM Atom
applySubstAtom atom = case atom of
  AExpr expr -> deFuncExpr expr
  ARecCon r -> liftM ARecCon $ traverse applySubstAtom r
  -- AFor Binder Atom
  Thunk (FullEnv lenv tenv) expr -> do
    lenv' <- traverse (\(ty,a) -> liftM ((,) ty) (applySubstAtom a)) lenv
    tenv' <- traverse subTy tenv
    return $ Thunk (FullEnv lenv' tenv') expr

deFuncDecl :: Decl -> DeFuncM Atom -> DeFuncM Atom
deFuncDecl decl cont = case decl of
  Let b bound -> do
    x <- deFuncExpr bound
    bindVal b x $ cont
  Unpack (Bind v ty) tv bound -> do
    AExpr bound' <- deFuncExpr bound
    tv' <- freshLike tv
    extendWith (asTEnv $ tv @> TypeVar tv') $ do
      v' <- freshLike v
      ty' <- subTy ty
      extendWith (asLEnv (v @> (ty', AExpr (Var v')))) $ do
        tell [Unpack (v'%>ty') tv' bound']
        cont
  -- TODO: this underscore option really isn't helping. Get rid of it
  Unpack (Ignore ty) tv bound -> do
    AExpr bound' <- deFuncExpr bound
    tv' <- freshLike tv
    extendWith (asTEnv $ tv @> TypeVar tv') $ do
      ty' <- subTy ty
      tell [Unpack (Ignore ty') tv' bound']
      cont

-- writes nothing
deFuncScoped :: Expr -> DeFuncM (Expr, Type, Expr -> Atom)
deFuncScoped expr = do
  (atom, decls) <- lift $ runWriterT (deFuncExpr expr)
  return $ deFuncScope decls atom

deFuncScope :: [Decl] -> Atom -> (Expr, Type, Expr -> Atom)
deFuncScope decls atom = (Decls decls $ RecCon (fmap Var (Tup vs)), ty, buildVal)
  where
    vsBound = concat $ map getBoundLVar decls
    getBoundLVar decl = case decl of Let b _ -> binderVars b
                                     Unpack b _ _ -> binderVars b
    vs = envNames $ envSubset vsBound $ freeOutVars atom
    ty = RecType $ Tup $ map (env!) vs
      where env = bindFold $ map declBinder decls
    buildVal new = subOutVars sub atom
      where sub = fold $ fmap (\(k,v) -> v@>(RecGet new k)) (recNameVals (Tup vs))

declBinder :: Decl -> Binder
declBinder (Let b _) = b
declBinder (Unpack b _ _) = b

subOutVars :: Env Expr -> Atom -> Atom
subOutVars subst val = case val of
  AExpr expr -> AExpr $ subAtomicExpr subst expr
  Thunk (FullEnv lenv tenv) expr -> Thunk (FullEnv lenv' tenv) expr
    where lenv' = fmap (\(ty,val) -> (ty, subOutVars subst val)) lenv
  ARecCon r -> ARecCon $ fmap (subOutVars subst) r

freeOutVars :: Atom -> Env ()
freeOutVars val = case val of
  AExpr expr -> foldMap (@>()) $ freeLVars expr
  Thunk env _ -> foldMap (freeOutVars . snd) (lEnv env)
  ARecCon r -> foldMap freeOutVars r
  AFor _ atom -> freeOutVars atom  -- TODO: don't include bound var

subAtomicExpr :: Env Expr -> Expr -> Expr
subAtomicExpr subst expr = case expr of
  Lit _ -> expr
  Var v -> case envLookup subst v of Just expr' -> expr'
                                     Nothing    -> expr
  _ -> expr  -- TODO!: handle other cases (and decide what's allowed)

bindVal :: Binder -> Atom -> DeFuncM a -> DeFuncM a
bindVal (Bind v ty) val cont = do
  ty' <- subTy ty
  extendWith (asLEnv (v @> (ty', val))) $ cont

-- atomize :: Name -> Type -> Atom -> DeFuncM Atom
-- atomize nameHint ty val = case val of
--   Thunk _ _ -> return val
--   ARecCon rVal -> do
--     let (RecType rTy) = ty
--     rVal' <- sequence $ recZipWith (atomize nameHint) rTy rVal
--     return (ARecCon rVal')
--   AExpr expr -> if inlinable expr then return val
--                                     else materialize nameHint ty expr

materialize :: Name -> Type -> Expr -> DeFuncM Atom
materialize nameHint ty expr = do
  v <- freshLike nameHint
  tell [Let (v %> ty) expr]
  return $ AExpr (Var v)

-- -- TODO: add more context information
-- inlinable :: Expr -> Bool
-- inlinable expr = case expr of
--   Lit _ -> True
--   Var _ -> True
--   _     -> False

fromAExpr :: Atom -> Expr
fromAExpr (AExpr expr) = expr
fromAExpr (ARecCon r)  = RecCon $ fmap fromAExpr r
fromAExpr (Thunk _ _) = error "Unevaluated expression"

makeThunk :: Expr -> DeFuncM Atom
makeThunk expr = do FullEnv lenv tenv <- ask
                    let lenv' = envSubset (freeLVars expr) lenv
                    return $ Thunk (FullEnv lenv' tenv) expr

subTy :: Type -> DeFuncM Type
subTy ty = do env <- asks tEnv
              return $ maybeSub (Just . (env!)) ty

builtinOutTy :: Builtin -> Type
builtinOutTy b = case builtinType b of ArrType _ ty -> ty

-- TODO: check/fail higher order case
deFuncFold :: [Type] -> Expr -> DeFuncM Atom
deFuncFold ts (RecCon (Tup [For ib (Lam xb body), x])) = do
  ts' <- traverse subTy ts
  AExpr x' <- deFuncExpr x
  refreshBinder ib $ \ib' ->
    refreshBinder xb $ \xb' -> do
      (AExpr body', decls) <- lift $ runWriterT $ deFuncExpr body
      return $ AExpr $
        App (TApp (Builtin Fold) ts')
            (RecCon (Tup [For ib' (Lam xb' (Decls decls body')), x']))

refreshBinder :: Binder -> (Binder -> DeFuncM a) -> DeFuncM a
refreshBinder (Bind v ty) cont = do
  v' <- freshLike v
  ty' <- subTy ty
  let b' = v' %> ty'
  extendWith (asLEnv (v @> (ty', AExpr (Var v')))) (cont b')

askLEnv :: Var -> DeFuncM Atom
askLEnv v = do tyVal <- asks $ flip envLookup v . lEnv
               return $ case tyVal of
                 Just (_, atom) -> atom
                 Nothing -> AExpr (Var v)
