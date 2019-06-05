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

type TopEnv = (Subst, FullEnv Type ())
type Atom = Expr
type OutDecls = ([Decl], FullEnv Type ())
type DeFuncCat a = CatT (Subst, OutDecls) (Either Err) a
type DeFuncM a = ReaderT Subst (CatT OutDecls (Either Err)) a

deFuncPass :: TopDecl -> TopPass TopEnv TopDecl
deFuncPass topDecl = case topDecl of
  TopDecl decl -> do ((decl, env), []) <- asTopPass $ toCat $ deFuncDeclTop decl
                     putEnv env
                     return $ TopDecl decl
  EvalCmd NoOp -> return (EvalCmd NoOp)
  EvalCmd (Command cmd expr) -> do
    (atom, decls) <- asTopPass $ toCat $ deFuncExpr expr
    let expr = Decls decls atom
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
  (bound', (decls,_)) <- scoped $ deFuncExpr bound
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
  Lit l -> return $ Lit l
  Decls decls body -> withCat (mapM_ deFuncDecl decls) $ \() -> recur body
  Lam _ _ -> applySub expr
  App (TApp (Builtin Fold) ts) arg -> deFuncFold ts arg
  App (Builtin b) arg -> do
    arg' <- recur arg
    let expr' = App (Builtin b) arg'
    if trivialBuiltin b
      then return expr'
      else materialize (rawName "tmp") expr'
  TApp (Builtin Iota) [n] -> do
    n' <- subTy n
    return $ TApp (Builtin Iota) [n']
  App fexpr arg -> do
    Lam b body <- recur fexpr
    arg' <- recur arg
    dropSubst $ bindVal b arg' $ recur body
  Builtin _ -> error "Cannot defunctionalize raw builtins -- only applications"
  For b body -> do
    (expr', atomBuilder, b'@(i':>_)) <- refreshBinder b $ \b' -> do
                                          (body', builder) <- deFuncScoped body
                                          return (For b' body', builder, b')
    tab <- materialize (rawName "tab") expr'
    return $ For b' (atomBuilder (Get tab i'))
  Get e ie -> do
    e' <- recur e
    Var ie' <- askLEnv ie
    case e' of
      For (i:>_) body -> do
        dropSubst $
          extendR (asLEnv (i @> Var ie')) $
            applySub body
      tabExpr -> return $ Get tabExpr ie'
  RecCon r -> liftM RecCon $ traverse recur r
  RecGet e field -> do
    val <- recur e
    return $ case val of
      RecCon r -> recGet r field
      e'       -> RecGet e' field
  TLam _ _ -> applySub expr
  TApp fexpr ts -> do
    TLam bs body <- recur fexpr
    ts' <- mapM subTy ts
    dropSubst $ do
      extendR (asTEnv $ bindFold $ zipWith replaceAnnot bs ts') $ do
        recur body
  where recur = deFuncExpr

refreshBinder :: Binder -> (Binder -> DeFuncM a) -> DeFuncM a
refreshBinder (v:>ty) cont = do
  ty' <- subTy ty
  v' <- looks $ rename v . lEnv . snd
  extendR (asLEnv (v @> Var v')) $ do
    extendLocal (asSnd $ asLEnv $ v'@>ty') $ do
      cont (v':>ty')

-- Should we scope RHS of local lets? It's currently the only local/top diff
deFuncDecl :: Decl -> DeFuncCat ()
deFuncDecl (Let (v:>_) bound) = do
  x <- toCat $ deFuncExpr bound
  extend $ asFst $ asLEnv $ v @> x
deFuncDecl (Unpack (v:>ty) tv bound) = do
  bound' <- toCat $ deFuncExpr bound
  tv' <- looks $ rename tv . tEnv . snd . snd
  extend (asTEnv $ tv@>TypeVar tv', ([], asTEnv (tv'@>())))
  ty' <- toCat $ subTy ty
  v' <- looks $ rename v . lEnv . snd . snd
  extend $ (asLEnv $ v @> Var v',
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
    vs = envNames $ envSubset (envNames (freeLVars atom)) localEnv
    buildVal new = subExpr (asLEnv sub) mempty atom
      where sub = fold $ fmap (\(k,v) -> v@>(RecGet new k)) (recNameVals (Tup vs))

bindVal :: Binder -> Atom -> DeFuncM a -> DeFuncM a
bindVal (v:>_) val cont = extendR (asLEnv (v @> val)) $ cont

materialize :: Name -> Expr -> DeFuncM Expr
materialize nameHint expr = do
  v <- looks $ rename nameHint . lEnv . snd
  ty <- exprType expr
  case singletonType ty of
    Just expr' -> return expr'
    Nothing -> do
      extend ([Let (v :> ty) expr], asLEnv (v@>ty))
      return $ Var v

exprType :: Expr -> DeFuncM Type
exprType expr = do env <- looks $ snd
                   return $ getType env expr

subTy :: Type -> DeFuncM Type
subTy ty = do env <- asks tEnv
              return $ maybeSub (envLookup env) ty

-- TODO: check/fail higher order case
deFuncFold :: [Type] -> Expr -> DeFuncM Expr
deFuncFold ts (RecCon (Tup [For ib (Lam xb body), x])) = do
  ts' <- traverse subTy ts
  x' <- deFuncExpr x
  refreshBinder ib $ \ib' ->
    refreshBinder xb $ \xb' -> do
      (body', (decls, _)) <- scoped $ deFuncExpr body
      let outExpr = App (TApp (Builtin Fold) ts')
                     (RecCon (Tup [For ib' (Lam xb' (Decls decls body')), x']))
      materialize (rawName "fold_out") outExpr

askLEnv :: Var -> DeFuncM Atom
askLEnv v = do tyVal <- asks $ flip envLookup v . lEnv
               return $ case tyVal of
                 Just atom -> atom
                 Nothing -> Var v

trivialBuiltin :: Builtin -> Bool
trivialBuiltin b = case b of
  Iota -> True
  Range -> True
  IntToReal -> True
  _ -> False

singletonType :: Type -> Maybe Expr
singletonType ty = case ty of
  RecType (Tup []) -> return $ RecCon (Tup [])
  RecType r -> liftM RecCon $ traverse singletonType r
  TabType n v -> liftM (For (rawName "i" :> n)) $ singletonType v
  _ -> Nothing


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

dropSubst :: DeFuncM a -> DeFuncM a
dropSubst m = local (const mempty) m

applySub :: Expr -> DeFuncM Expr
applySub expr = do
  sub <- ask
  FullEnv lscope tscope <- looks snd
  let scope' = FullEnv (fmap (const ()) lscope) tscope
  return $ subExpr sub scope' expr
