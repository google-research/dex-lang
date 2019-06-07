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
import Control.Monad.Writer
import Control.Monad.Except hiding (Except)
import qualified Data.Map.Strict as M

type Scope = FullEnv Type ()
type TopEnv = (Subst, Scope)
type Atom = Expr
type OutDecls = ([Decl], Scope)
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
  scope <- looks snd
  return (Let (v:>ty) bound', (v @> L (atomBuilder (Var v) scope), v @> L ty))
deFuncDeclTop (Unpack b tv bound) = do
  (bound', (decls,_)) <- scoped $ deFuncExpr bound
  return (Unpack b tv (Decls decls bound'),
          (tv @> T (TypeVar tv), (tv @> T ())))

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
  App (TApp (Builtin Deriv) ts) arg -> deFuncDeriv ts arg
  App (TApp (Builtin Transpose) ts) arg -> deFuncTranspose ts arg
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
    Lam (v:>_) body <- recur fexpr
    arg' <- recur arg
    dropSubst $
      extendR (v @> L arg') $ recur body
  Builtin _ -> error "Cannot defunctionalize raw builtins -- only applications"
  For b body -> do
    (expr', atomBuilder, b'@(i':>_)) <- refreshBinder b $ \b' -> do
                                          (body', builder) <- deFuncScoped body
                                          return (For b' body', builder, b')
    tab <- materialize (rawName "tab") expr'
    scope <- looks snd
    let built = atomBuilder (Get tab i') (scope <> lbind b')
    return $ For b' built
  Get e ie -> do
    e' <- recur e
    Var ie' <- askLEnv ie
    case e' of
      For (i:>_) body -> do
        dropSubst $
          extendR (i @> L (Var ie')) $
            applySub body
      tabExpr -> return $ Get tabExpr ie'
  RecCon r -> liftM RecCon $ traverse recur r
  RecGet e field -> do
    val <- recur e
    return $ recGetExpr val field
  TLam _ _ -> applySub expr
  TApp fexpr ts -> do
    TLam bs body <- recur fexpr
    ts' <- mapM subTy ts
    dropSubst $ do
      extendR (bindFold $ zipWith replaceAnnot bs (map T ts')) $ do
        recur body
  where recur = deFuncExpr

recGetExpr :: Expr -> RecField -> Expr
recGetExpr (RecCon r) field = recGet r field
recGetExpr e          field = RecGet e field

refreshBinder :: Binder -> (Binder -> DeFuncM a) -> DeFuncM a
refreshBinder (v:>ty) cont = do
  ty' <- subTy ty
  v' <- looks $ rename v . snd
  extendR (v @> L (Var v')) $ do
    extendLocal (asSnd $ v' @> L ty') $ do
      cont (v':>ty')

-- Should we scope RHS of local lets? It's currently the only local/top diff
deFuncDecl :: Decl -> DeFuncCat ()
deFuncDecl (Let (v:>_) bound) = do
  x <- toCat $ deFuncExpr bound
  extend $ asFst $ v @> L x
deFuncDecl (Unpack (v:>ty) tv bound) = do
  bound' <- toCat $ deFuncExpr bound
  tv' <- looks $ rename tv . snd . snd
  extend (tv @> T (TypeVar tv'), ([], tv'@> T ()))
  ty' <- toCat $ subTy ty
  v' <- looks $ rename v . snd . snd
  extend $ (v @> L (Var v'), ([Unpack (v':>ty') tv' bound'], v'@> L ty'))

-- writes nothing
deFuncScoped :: Expr -> DeFuncM (Expr, Expr -> Scope -> Atom)
deFuncScoped expr = do
  (atom, (decls, outScope)) <- scoped $ deFuncExpr expr
  let (expr', builder) = saveScope outScope atom
  return (Decls decls expr', builder)

saveScope :: Env a -> Atom -> (Expr, Expr -> Scope -> Atom)
saveScope localEnv atom =
  case envNames $ envIntersect (freeLVars atom) localEnv of
    [v] -> (Var v, buildVal v)
    vs  -> (RecCon (fmap Var (Tup vs)), buildValTup vs)
  where
    buildVal    v  new scope = subExpr (v @> L new) (fmap (const ()) scope) atom
    buildValTup vs new scope = subExpr sub          (fmap (const ()) scope) atom
      where sub = fold $ fmap (\(k,v) -> v @> L (RecGet new k)) (recNameVals (Tup vs))

materialize :: Name -> Expr -> DeFuncM Expr
materialize nameHint expr = do
  v <- looks $ rename nameHint . snd
  ty <- exprType expr
  case singletonType ty of
    Just expr' -> return expr'
    Nothing -> do
      extend ([Let (v :> ty) expr], v @> L ty)
      return $ Var v

exprType :: Expr -> DeFuncM Type
exprType expr = do env <- looks $ snd
                   return $ getType env expr

subTy :: Type -> DeFuncM Type
subTy ty = do env <- ask
              return $ maybeSub (fmap fromT . envLookup env) ty

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
askLEnv v = do x <- asks $ flip envLookup v
               return $ case x of
                 Just (L atom) -> atom
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
  scope <- looks $ fmap (const ()) . snd
  checkSubScope sub scope  -- TODO: remove this when we care about performance
  return $ subExpr sub scope expr

checkSubScope :: Subst -> Env () -> DeFuncM ()
checkSubScope sub scope =
  if all (`isin` scope) lvars
    then return ()
    else throw CompilerErr $ "Free sub vars not in scope:\n" ++
                    pprint lvars ++ "\n" ++ pprint scope
  where lvars = envNames $ foldMap freeLVars [expr | L expr <- toList sub]

type DerivM a = ReaderT (Env (Atom, Atom))
                  (CatT (OutDecls, OutDecls) (Either Err)) a

type TransposeM a = WriterT CTEnv (CatT OutDecls (Either Err)) a

deFuncDeriv :: [Type] -> Expr -> DeFuncM Expr
deFuncDeriv _ (RecCon (Tup [Lam b body, x])) = do
  x' <- deFuncExpr x
  refreshBinder b $ \(v:>ty) -> do
    (bodyOut', (decls, _)) <- scoped $ deFuncExpr body
    scope <- looks snd
    let body' = Decls decls bodyOut'
        t = rename (rawName "tangent") scope
        scope' = scope <> t @> L ty
    ((xOut, tOut), (xDecls, tDecls)) <-
                    liftEither $ flip runCatT (asSnd scope', asSnd scope') $
                      flip runReaderT (v @> (x', Var t)) $ evalDeriv body'
    extend xDecls
    return $ RecCon $ Tup $ [xOut, Lam (t:>ty) (Decls (fst tDecls) tOut)]

deFuncTranspose :: [Type] -> Expr -> DeFuncM Expr
deFuncTranspose _ (RecCon (Tup [Lam (v:>_) body, ct])) = do
  ct' <- deFuncExpr ct
  (bodyOut', (decls, _)) <- scoped $ deFuncExpr body
  let body' = Decls decls bodyOut'
  scope <- looks snd
  (((), ctEnv), ctDecls) <- liftEither $ flip runCatT (asSnd scope) $
                              runWriterT $ evalTranspose ct' body'
  extend ctDecls
  addCTsDeFunc (snd $ ctEnvPop ctEnv v)

evalDeriv :: Expr -> DerivM (Atom, Atom)
evalDeriv expr = case expr of
  Var v -> do
    xt <- asks $ flip envLookup v
    return $ case xt of
      Nothing -> (expr, Lit Zero)
      Just xt' -> xt'
  Lit _ -> return (expr, Lit Zero)
  Decls [] body -> evalDeriv body
  Decls (Let (v:>_) bound:decls) body -> do
    xt <- evalDeriv bound
    extendR (v@>xt) (evalDeriv body')
    where body' = Decls decls body
  App (Builtin b) arg -> do
    (x, t) <- evalDeriv arg
    x' <- writePrimal $ App (Builtin b) x
    t' <- case t of
            Lit Zero -> return (Lit Zero)
            _ -> builtinDeriv b x t
    return (x', t')
  For b body -> error "For not implemented yet"
  RecCon r -> do
    r' <- traverse evalDeriv r
    return (RecCon (fmap fst r'), RecCon (fmap snd r'))
  RecGet e field -> do
    (x, t) <- evalDeriv e
    return (recGetExpr x field,
            recGetExpr t field)
  _ -> error $ "Suprising expression: " ++ pprint expr

newtype CTEnv = CTEnv (Env [Atom])

instance Semigroup CTEnv where
  CTEnv env <> CTEnv env' = CTEnv $ envMonoidUnion env env'

instance Monoid CTEnv where
  mempty = CTEnv mempty
  mappend = (<>)

ctEnvPop :: CTEnv -> Name -> (CTEnv, [Atom])
ctEnvPop (CTEnv (Env m)) v = (CTEnv (Env m'), x)
  where m' = M.delete v m
        x = M.findWithDefault [] v m

evalTranspose :: Atom -> Expr -> TransposeM ()
evalTranspose ct expr = case expr of
  Var v -> tell $ CTEnv $ v @> [ct]
  Lit _ -> return ()
  Decls [] body -> evalTranspose ct body
  Decls (Let (v:>_) bound:decls) final -> do
    ((), ctEnv) <- lift $ runWriterT $ evalTranspose ct body
    let (ctEnv', outCTs) = ctEnvPop ctEnv v
    tell ctEnv'
    ctV <- addCTs outCTs
    evalTranspose ctV bound
    where body = Decls decls final
  App (Builtin b) arg -> builtinTranspose b ct arg
  _ -> error $ "Suprising expression in transpose: " ++ pprint expr

addCTsDeFunc :: [Atom] -> DeFuncM Atom
addCTsDeFunc []  = return $ Lit Zero
addCTsDeFunc [x] = return x
addCTsDeFunc (x:xs) = do xs' <- addCTsDeFunc xs
                         materialize (rawName "sum") $
                           App (Builtin FAdd) (RecCon (Tup [x, xs']))

addCTs :: [Atom] -> TransposeM Atom
addCTs []  = return $ Lit Zero
addCTs [x] = return x

builtinTranspose :: Builtin -> Atom -> Expr -> TransposeM ()
builtinTranspose b ct arg = case b of
  FAdd -> do
    evalTranspose ct t1
    evalTranspose ct t2
    where (t1, t2) = unpair arg
  FMul -> do
    ct' <- writeCTMul x ct
    evalTranspose ct' t
    where (x, t) = unpair arg

builtinDeriv :: Builtin -> Atom -> Atom -> DerivM Atom
builtinDeriv b x t = case b of
  FAdd -> writeAdd t1 t2
            where (t1, t2) = unpair t
  FMul -> do
    t1' <- writeMul x2 t1
    t2' <- writeMul x1 t2
    writeAdd t1' t2'
      where (t1, t2) = unpair t
            (x1, x2) = unpair x

writeCoTangent :: Expr -> TransposeM Atom
writeCoTangent expr = do
  v <- looks $ rename (rawName "ct") . snd
  ty <- coTangentType expr
  extend $ ([Let (v :> ty) expr], v @> L ty)
  return $ Var v

coTangentType :: Expr -> TransposeM Type
coTangentType expr = do env <- looks $ snd
                        return $ getType env expr

unpair :: Atom -> (Atom, Atom)
unpair (RecCon (Tup [x, y])) = (x, y)

-- TODO: should these ring identities be applied in a separate pass?
-- We might know more then, like the call sites of the linearized function.
writeAdd :: Atom -> Atom -> DerivM Atom
writeAdd (Lit Zero) y = return y
writeAdd x (Lit Zero) = return x
writeAdd x y = writeTangent $ App (Builtin FAdd) (RecCon (Tup [x, y]))

-- treated as linear in second argument only
writeMul :: Atom -> Atom -> DerivM Atom
writeMul _ (Lit Zero) = return $ Lit Zero
writeMul x y = writeTangent $ App (Builtin FMul) (RecCon (Tup [x, y]))

--- TODO: should these ring identities be applied in a separate pass?
-- We might know more then, like the call sites of the linearized function.
writeCTAdd :: Atom -> Atom -> TransposeM Atom
writeCTAdd (Lit Zero) y = return y
writeCTAdd x (Lit Zero) = return x
writeCTAdd x y = writeCoTangent $ App (Builtin FAdd) (RecCon (Tup [x, y]))

-- treated as linear in second argument only
writeCTMul :: Atom -> Atom -> TransposeM Atom
writeCTMul _ (Lit Zero) = return $ Lit Zero
writeCTMul x y = writeCoTangent $ App (Builtin FMul) (RecCon (Tup [x, y]))

writePrimal :: Expr -> DerivM Atom
writePrimal expr = do
  v <- looks $ rename (rawName "primal") . snd . fst
  ty <- primalType expr
  extend ( ([Let (v :> ty) expr], v @> L ty)
         , ([]                  , v @> L ty)) -- primals stay in scope
  return $ Var v

writeTangent :: Expr -> DerivM Atom
writeTangent expr = do
  v <- looks $ rename (rawName "tangent") . snd . snd
  ty <- tangentType expr
  extend $ asSnd ([Let (v :> ty) expr], v @> L ty)
  return $ Var v

primalType :: Expr -> DerivM Type
primalType expr = do env <- looks $ snd . fst
                     return $ getType env expr

tangentType :: Expr -> DerivM Type
tangentType expr = do env <- looks $ snd . snd
                      return $ getType env expr
