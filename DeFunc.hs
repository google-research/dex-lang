module DeFunc (deFuncPass) where

import Syntax
import Env
import Record
import Pass
import PPrint
import Fresh
import Type
import Cat

import Data.Foldable
import Control.Monad.Reader
import Control.Monad.Except hiding (Except)

-- TODO: consider making this just Expr with the thunk case as an annotation
data Atom = AExpr Expr
          | ARecCon (Record Atom)
          | AFor Binder Atom
          | Thunk DFEnv Expr  -- Lam | TLam | For
             deriving Show

type DFEnv = FullEnv Atom Type
type TopEnv = (DFEnv, FullEnv Type ())

type OutDecls = ([Decl], FullEnv Type ())
type DeFuncCat a = CatT (DFEnv, OutDecls) (Either Err) a
type DeFuncM a = ReaderT DFEnv (CatT OutDecls (Either Err)) a

deFuncPass :: TopDecl -> TopPass TopEnv TopDecl
deFuncPass topDecl = case topDecl of
  TopDecl decl -> do ((decl, env), []) <- asTopPass $ toCat $ deFuncDeclTop decl
                     putEnv env
                     return $ TopDecl decl
  EvalCmd NoOp -> return (EvalCmd NoOp)
  EvalCmd (Command cmd expr) -> do
    (atom, decls) <- asTopPass $ toCat $ deFuncExpr expr
    let expr = Decls decls (forceAtom atom)
    case cmd of Passes -> writeOut $ "\n\nDefunctionalized\n" ++ pprint expr
                _ -> return ()
    return $ EvalCmd (Command cmd expr)

deFuncDeclTop :: Decl -> DeFuncM (Decl, TopEnv)
deFuncDeclTop (Let (v:>_) bound) = do
  (bound', atomBuilder) <- deFuncScoped bound
  ty <- exprType bound'
  return (Let (v:>ty) bound', (asLEnv $ v @> atomBuilder (Var v),
                               asLEnv $ v @> ty))
deFuncDeclTop (Unpack b tv bound) = do
  (AExpr bound', (decls,_)) <- scoped $ deFuncExpr bound
  return (Unpack b tv (Decls decls bound'),
          (asTEnv $ tv @> TypeVar tv, (asTEnv $ tv @>())))

asTopPass :: DeFuncCat a -> TopPass TopEnv (a, [Decl])
asTopPass m = do
  (env, scope) <- getEnv
  (ans, (env', (decls, scope'))) <- liftEither $
                                      flip runCatT (env, (mempty, scope)) $ m
  putEnv $ (env', scope')
  return (ans, decls)

deFuncExpr :: Expr -> DeFuncM Atom
deFuncExpr expr = case expr of
  Var v -> askLEnv v
  Lit l -> return $ AExpr (Lit l)
  Decls decls body -> withCat (mapM_ deFuncDecl decls) $ \() -> recur body
  Lam _ _ -> makeThunk expr
  App (TApp (Builtin Fold) ts) arg -> liftM AExpr $ deFuncFold ts arg
  App (Builtin b) arg -> do
    arg' <- recur arg
    let expr' = App (Builtin b) (forceAtom arg')
    if trivialBuiltin b
      then return (AExpr expr')
      else liftM AExpr $ materialize (rawName "tmp") expr'
  TApp (Builtin Iota) [n] -> do
    n' <- subTy n
    return $ AExpr $ TApp (Builtin Iota) [n']
  App fexpr arg -> do
    Thunk env (Lam b body) <- recur fexpr
    arg' <- recur arg
    bindVal b arg' $ extendR env $ recur body
  Builtin _ -> error "Cannot defunctionalize raw builtins -- only applications"
  For b body -> do
    (expr', atomBuilder) <- refreshBinder b $ \b' -> do
                              (body', builder) <- deFuncScoped body
                              return (For b' body', builder)
    b'@(i':>_) <- traverse subTy b
    tab <- materialize (rawName "tab") expr'
    return $ AFor b' (atomBuilder (Get tab i'))
  Get e ie -> do
    e' <- recur e
    AExpr (Var ie') <- askLEnv ie
    case e' of
      AExpr tabExpr -> return $ AExpr $ Get tabExpr ie' -- TODO: optimize `for` case
      AFor (i:>_) body -> do
        local (const mempty) $
          extendR (asLEnv (i @> AExpr (Var ie'))) $
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
    extendR env $ do
      extendR (asTEnv $ bindFold $ zipWith replaceAnnot bs ts') $ do
        recur body
  where recur = deFuncExpr

refreshBinder :: Binder -> (Binder -> DeFuncM a) -> DeFuncM a
refreshBinder (v:>ty) cont = do
  ty' <- subTy ty
  v' <- looks $ rename v . lEnv . snd
  extendR (asLEnv (v @> AExpr (Var v'))) $ do
    extendLocal (asSnd $ asLEnv $ v'@>ty') $ do
      cont (v':>ty')

applySubstAtom :: Atom -> DeFuncM Atom
applySubstAtom atom = case atom of
  AExpr expr -> deFuncExpr expr
  ARecCon r -> liftM ARecCon $ traverse applySubstAtom r
  AFor b atom -> do
    refreshBinder b $ \b' -> do
      atom' <- applySubstAtom atom
      return $ AFor b' atom'
  Thunk (FullEnv lenv tenv) expr -> do
    lenv' <- traverse applySubstAtom lenv
    tenv' <- traverse subTy tenv
    return $ Thunk (FullEnv lenv' tenv') expr

-- Should we scope RHS of local lets? It's currently the only local/top diff
deFuncDecl :: Decl -> DeFuncCat ()
deFuncDecl (Let (v:>_) bound) = do
  x <- toCat $ deFuncExpr bound
  extend $ asFst $ asLEnv $ v @> x
deFuncDecl (Unpack (v:>ty) tv bound) = do
  AExpr bound' <- toCat $ deFuncExpr bound
  tv' <- looks $ rename tv . tEnv . snd . snd
  extend (asTEnv $ tv@>TypeVar tv', ([], asTEnv (tv'@>())))
  ty' <- toCat $ subTy ty
  v' <- looks $ rename v . lEnv . snd . snd
  extend $ (asLEnv $ v @> AExpr (Var v'),
            ([Unpack (v':>ty') tv' bound'], asLEnv (v'@>ty')))

-- writes nothing
deFuncScoped :: Expr -> DeFuncM (Expr, Expr -> Atom)
deFuncScoped expr = do
  (atom, (decls, outScope)) <- scoped $ deFuncExpr expr
  let (expr, builder) = saveScope (lEnv outScope) atom
  return (Decls decls expr, builder)

saveScope :: Env a -> Atom -> (Expr, Expr -> Atom)
saveScope localEnv atom = (RecCon (fmap Var (Tup vs)), buildVal)
  where
    vs = envNames $ envSubset (envNames (freeOutVars atom)) localEnv
    buildVal new = subOutVars sub atom
      where sub = fold $ fmap (\(k,v) -> v@>(RecGet new k)) (recNameVals (Tup vs))

subOutVars :: Env Expr -> Atom -> Atom
subOutVars subst val = case val of
  AExpr expr -> AExpr $ subAtomicExpr subst expr
  Thunk (FullEnv lenv tenv) expr -> Thunk (FullEnv lenv' tenv) expr
    where lenv' = fmap (subOutVars subst) lenv
  AFor b atom -> AFor b (subOutVars subst atom) -- TODO: need to freshen binder
  ARecCon r -> ARecCon $ fmap (subOutVars subst) r

freeOutVars :: Atom -> Env ()
freeOutVars val = case val of
  AExpr expr -> foldMap (@>()) $ freeLVars expr
  Thunk env _ -> foldMap freeOutVars (lEnv env)
  ARecCon r -> foldMap freeOutVars r
  AFor _ atom -> freeOutVars atom  -- TODO: don't include bound var

-- TODO: do this whole thing properly, including capture avoidance
subAtomicExpr :: Env Expr -> Expr -> Expr
subAtomicExpr subst expr = case expr of
  Lit _ -> expr
  Var v -> case envLookup subst v of Just expr' -> expr'
                                     Nothing    -> expr
  Get e ie -> Get (recur e) (case recur (Var ie) of Var ie' -> ie')
  RecGet e field -> RecGet (recur e) field
  _ -> expr -- TODO!: handle other cases (and decide what's allowed)
  where recur = subAtomicExpr subst

bindVal :: Binder -> Atom -> DeFuncM a -> DeFuncM a
bindVal (v:>_) val cont = extendR (asLEnv (v @> val)) $ cont

materialize :: Name -> Expr -> DeFuncM Expr
materialize nameHint expr = do
  v <- looks $ rename nameHint . lEnv . snd
  ty <- exprType expr
  extend ([Let (v :> ty) expr], asLEnv (v@>ty))
  return $ Var v

forceAtom :: Atom -> Expr
forceAtom (AExpr expr) = expr
forceAtom (ARecCon r)  = RecCon $ fmap forceAtom r
forceAtom (AFor b atom) = For b (forceAtom atom)
forceAtom (Thunk _ _) = error "Unevaluated expression"

exprType :: Expr -> DeFuncM Type
exprType expr = do env <- looks $ snd
                   return $ getType env expr

makeThunk :: Expr -> DeFuncM Atom
makeThunk expr = do FullEnv lenv tenv <- ask
                    let lenv' = envSubset (freeLVars expr) lenv
                    return $ Thunk (FullEnv lenv' tenv) expr

subTy :: Type -> DeFuncM Type
subTy ty = do env <- asks tEnv
              return $ maybeSub (envLookup env) ty

-- TODO: check/fail higher order case
deFuncFold :: [Type] -> Expr -> DeFuncM Expr
deFuncFold ts (RecCon (Tup [For ib (Lam xb body), x])) = do
  ts' <- traverse subTy ts
  AExpr x' <- deFuncExpr x
  refreshBinder ib $ \ib' ->
    refreshBinder xb $ \xb' -> do
      (AExpr body', (decls, _)) <- scoped $ deFuncExpr body
      let outExpr = App (TApp (Builtin Fold) ts')
                     (RecCon (Tup [For ib' (Lam xb' (Decls decls body')), x']))
      materialize (rawName "fold_out") outExpr

askLEnv :: Var -> DeFuncM Atom
askLEnv v = do tyVal <- asks $ flip envLookup v . lEnv
               return $ case tyVal of
                 Just atom -> atom
                 Nothing -> AExpr (Var v)

trivialBuiltin :: Builtin -> Bool
trivialBuiltin b = case b of
  Iota -> True
  Range -> True
  IntToReal -> True
  _ -> False

toCat :: DeFuncM a -> DeFuncCat a
toCat m = do
  (env, decls) <- look
  (ans, decls') <- liftEither $ runCatT (runReaderT m env) decls
  extend (mempty, decls')
  return ans

withCat :: DeFuncCat a -> (a -> DeFuncM b) -> DeFuncM b
withCat m cont = do
  env <- ask
  decls <- look
  (ans, (env', decls')) <- liftEither $ runCatT m (env, decls)
  extend decls'
  extendR env' $ cont ans
