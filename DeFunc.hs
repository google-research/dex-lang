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

type SimplifyM a = ReaderT Subst (CatT OutDecls (Either Err)) a
type SimplifyCat a = CatT (Subst, OutDecls) (Either Err) a

data SplitExpr = Split Expr (Expr -> Expr)
               | Defer Expr

deFuncPass :: TopDecl -> TopPass TopEnv TopDecl
deFuncPass topDecl = case topDecl of
  TopDecl decl -> do
    ((), decls) <- asTopPass $ simplifyDecl decl
    case decls of
      [] -> return $ dummyDecl
      [decl'] -> return $ TopDecl decl'
    where dummyDecl = TopDecl (Let (rawName "_" :> (RecType (Tup [])))
                        (RecCon (Tup []))) -- TODO: allow multiple decls (or none)
  EvalCmd NoOp -> return (EvalCmd NoOp)
  EvalCmd (Command cmd expr) -> do
    (atom, decls) <- asTopPass $ toCat $ simplify expr
    let expr = declsExpr decls atom
    case cmd of Passes -> writeOut $ "\n\nDefunctionalized\n" ++ pprint expr
                _ -> return ()
    return $ EvalCmd (Command cmd expr)

asTopPass :: SimplifyCat a -> TopPass TopEnv (a, [Decl])
asTopPass m = do
  (env, scope) <- getEnv
  (ans, (env', (decls, scope'))) <- liftEither $
                                      flip runCatT (env, (mempty, scope)) $ m
  putEnv $ (env', scope')
  return (ans, decls)

simplify :: Expr -> SimplifyM Expr
simplify expr = case expr of
  Var v -> askLEnv v
  Lit _ -> return expr
  Decls decls body -> withCat (mapM_ simplifyDecl decls) $ \() -> recur body
  Lam _ _ -> applySub expr
  App (TApp (Builtin Fold) ts) arg -> simplifyFold ts arg
  App (TApp (Builtin Deriv) ts) arg -> expandDeriv ts arg
  App (TApp (Builtin Transpose) ts) arg -> expandTranspose ts arg
  App (Builtin b) arg -> do
    arg' <- recur arg
    return $ simplifyBuiltin b arg'
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
    refreshBinder b $ \b' -> do
      (body', (decls, _)) <- scoped $ recur body
      return $ For b' (declsExpr decls body')
  Get e ie -> do
    e' <- recur e
    Var ie' <- askLEnv ie
    case e' of
      For (i:>_) body -> do
        dropSubst $
          extendR (i @> L (Var ie')) $
            applySub body >>= inlineDecls
      _ -> return $ Get e' ie'
  RecCon r -> liftM RecCon $ traverse recur r
  RecGet e field -> do
    e' <- recur e
    return $ recGetExpr e' field
  TLam _ _ -> applySub expr
  TApp fexpr ts -> do
    TLam bs body <- recur fexpr
    ts' <- mapM subTy ts
    dropSubst $ do
      extendR (bindFold $ zipWith replaceAnnot bs (map T ts')) $ do
        recur body
  where
    recur = simplify

inlineDecls :: Expr -> SimplifyM Expr
inlineDecls (Decls decls final) = extend (asFst decls) >> return final
inlineDecls expr = return expr

simplifyDecl :: Decl -> SimplifyCat ()
simplifyDecl (Let (v:>_) bound) = do
  (bound', (decls, _)) <- toCat $ scoped $ simplify bound
  curScope <- looks $ snd . snd
  case decompose curScope (declsExpr decls bound') of
    Defer expr -> extend $ asFst $ v @> L expr
    Split expr builder -> do
       ty <- toCat $ exprType expr  -- TODO: use optional types and infer later
       v' <- looks $ rename v . snd . snd
       extend ( v @> L (builder (Var v'))
              , ([Let (v':>ty) expr], v' @> L ty))
simplifyDecl (Unpack (v:>ty) tv bound) = do
  bound' <- toCat $ simplify bound
  tv' <- looks $ rename tv . snd . snd
  extend (tv @> T (TypeVar tv'), ([], tv'@> T ()))
  ty' <- toCat $ subTy ty
  v' <- looks $ rename v . snd . snd
  extend $ (v @> L (Var v'), ([Unpack (v':>ty') tv' bound'], v'@> L ty'))

matLocalVars :: Scope -> Expr -> SplitExpr
matLocalVars destScope expr = case localVars of
  []  -> Defer expr
  [v] -> Split (Var v) (buildVal v)
  vs  -> Split (RecCon (fmap Var (Tup vs))) (buildValTup vs)
  where
    localVars = envNames $ envDiff (freeLVars expr) destScope
    buildVal    v  new = subExpr (v @> L new) (fmap (const ()) destScope) expr
    buildValTup vs new = subExpr sub          (fmap (const ()) destScope) expr
      where sub = fold $ fmap (\(k,v) -> v @> L (RecGet new k)) (recNameVals (Tup vs))

decompose :: Scope -> Expr -> SplitExpr
decompose scope expr = case expr of
  Var v -> if v `isin` scope then Defer expr
                             else pureMat expr
  Lit _ -> Defer expr
  Decls decls body ->
    case decompose scope body of
      Defer body' -> Defer body'
      Split body' recon -> Split (Decls decls body') recon
  Lam _ _ -> matLocalVars scope expr
  App (Builtin b) _ -> if trivialBuiltin b then Defer expr
                                           else pureMat expr
  TApp (Builtin b) _ -> if trivialBuiltin b then Defer expr
                                            else pureMat expr
  App _ _ -> pureMat expr
  Builtin _ -> error "Builtin"
  For b@(i:>_) body ->
    case decompose scope body of
      -- could use a FullMat constructor here
      Split body' recon -> Split (For b body')
                                 (\e -> For b (recon (Get e i)))  -- need fresh i?
      Defer body' -> Defer (For b body')
  Get _ _ -> pureMat expr
  RecCon r -> if all isDefer splits
                then Defer expr
                else Split expr' build
    where
      splits = fmap (decompose scope) r
      splits' = fmap forceSplit splits
      expr' = RecCon $ fmap fst splits'
      build e = RecCon $ fmap (\(field, (_, f)) -> f (RecGet e field))
                              (recNameVals splits')
  RecGet _ _ -> pureMat expr
  TLam _ _ -> matLocalVars scope expr
  TApp _ _ -> error "Shouldn't see TApp here"
  where
    recur = simplify

    pureMat :: Expr -> SplitExpr
    pureMat expr = Split expr id

forceSplit :: SplitExpr -> (Expr, Expr -> Expr)
forceSplit (Split e f) = (e, f)
forceSplit (Defer   e) = (RecCon (Tup []), const e)

isDefer :: SplitExpr -> Bool
isDefer (Split _ _) = False
isDefer (Defer _) = True


refreshBinder :: Binder -> (Binder -> SimplifyM a) -> SimplifyM a
refreshBinder (v:>ty) cont = do
  ty' <- subTy ty
  v' <- looks $ rename v . snd
  extendR (v @> L (Var v')) $ do
    extendLocal (asSnd $ v' @> L ty') $ do
      cont (v':>ty')

exprType :: Expr -> SimplifyM Type
exprType expr = do env <- looks $ snd
                   return $ getType env expr

subTy :: Type -> SimplifyM Type
subTy ty = do env <- ask
              return $ maybeSub (fmap fromT . envLookup env) ty

-- TODO: check/fail higher order case
simplifyFold :: [Type] -> Expr -> SimplifyM Expr
simplifyFold ts (RecCon (Tup [For ib (Lam xb body), x])) = do
  ts' <- traverse subTy ts
  x' <- simplify x
  refreshBinder ib $ \ib' ->
    refreshBinder xb $ \xb' -> do
      (body', (decls, _)) <- scoped $ simplify body
      return $ App (TApp (Builtin Fold) ts')
                   (RecCon (Tup [For ib' (Lam xb' (declsExpr decls body')), x']))

askLEnv :: Var -> SimplifyM Atom
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

toCat :: SimplifyM a -> SimplifyCat a
toCat m = do
  (env, decls) <- look
  (ans, decls') <- liftEither $ runCatT (runReaderT m env) decls
  extend (mempty, decls')
  return ans

withCat :: SimplifyCat a -> (a -> SimplifyM b) -> SimplifyM b
withCat m cont = do
  env <- ask
  decls <- look
  (ans, (env', decls')) <- liftEither $ runCatT m (env, decls)
  extend decls'
  extendR env' $ cont ans

dropSubst :: SimplifyM a -> SimplifyM a
dropSubst m = local (const mempty) m

applySub :: Expr -> SimplifyM Expr
applySub expr = do
  sub <- ask
  scope <- looks $ fmap (const ()) . snd
  checkSubScope sub scope  -- TODO: remove this when we care about performance
  return $ subExpr sub scope expr

checkSubScope :: Subst -> Env () -> SimplifyM ()
checkSubScope sub scope =
  if all (`isin` scope) lvars
    then return ()
    else throw CompilerErr $ "Free sub vars not in scope:\n" ++
                    pprint lvars ++ "\n" ++ pprint scope
  where lvars = envNames $ foldMap freeLVars [expr | L expr <- toList sub]

simplifyBuiltin :: Builtin -> Expr -> Expr
simplifyBuiltin FAdd arg =
  case (checkZero x, checkZero y) of
    (Zero, _) -> y
    (_, Zero) -> x
    _ -> App (Builtin FAdd) arg
  where (x, y) = unpair arg
simplifyBuiltin FMul arg =
  case (checkZero x, checkZero y) of
    (Zero, _) -> zero
    (_, Zero) -> zero
    _ -> App (Builtin FMul) arg
  where (x, y) = unpair arg
simplifyBuiltin b arg = App (Builtin b) arg

data MaybeZero a = Zero | NonZero a

checkZero :: Expr -> MaybeZero Expr
checkZero (Lit (RealLit 0.0)) = Zero
checkZero expr = NonZero expr

-- === Autodiff ===

type DerivM a = ReaderT (Env (Atom, Atom))
                  (CatT (OutDecls, OutDecls) (Either Err)) a

type TransposeM a = WriterT CTEnv (CatT OutDecls (Either Err)) a

expandDeriv :: [Type] -> Expr -> SimplifyM Expr
expandDeriv _ (RecCon (Tup [Lam b body, x])) = do
  x' <- simplify x
  refreshBinder b $ \(v:>ty) -> do
    (bodyOut', (decls, _)) <- scoped $ simplify body
    scope <- looks snd
    let body' = Decls decls bodyOut'
        t = rename (rawName "tangent") scope
        scope' = scope <> t @> L ty
    ((xOut, tOut), (xDecls, tDecls)) <-
                    liftEither $ flip runCatT (asSnd scope', asSnd scope') $
                      flip runReaderT (v @> (x', Var t)) $ evalDeriv body'
    extend xDecls
    return $ RecCon $ Tup $ [xOut, Lam (t:>ty) (Decls (fst tDecls) tOut)]

expandTranspose :: [Type] -> Expr -> SimplifyM Expr
expandTranspose _ (RecCon (Tup [Lam (v:>_) body, ct])) = do
  ct' <- simplify ct
  (bodyOut', (decls, _)) <- scoped $ simplify body
  let body' = Decls decls bodyOut'
  scope <- looks snd
  (((), ctEnv), ctDecls) <- liftEither $ flip runCatT (asSnd scope) $
                              runWritert $ evalTranspose ct' body'

  extend ctDecls
  return $ addMany (snd $ ctEnvPop ctEnv v)

evalDeriv :: Expr -> DerivM (Atom, Atom)
evalDeriv expr = case expr of
  Var v -> do
    xt <- asks $ flip envLookup v
    return $ case xt of
      Nothing -> (expr, zero)
      Just xt' -> xt'
  Lit _ -> return (expr, zero)
  Decls [] body -> evalDeriv body
  Decls (Let (v:>_) bound:decls) body -> do
    xt <- evalDeriv bound
    extendR (v@>xt) (evalDeriv body')
    where body' = Decls decls body
  App (Builtin b) arg -> do
    (x, t) <- evalDeriv arg
    x' <- writePrimal $ App (Builtin b) x
    t' <- builtinDeriv b x t
    return (x', t')
  For _ _ -> error "For not implemented yet"
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
    ctV <- writeCoTangent $ addMany outCTs
    evalTranspose ctV bound
    where body = declsExpr decls final
  App (Builtin b) arg -> builtinTranspose b ct arg
  _ -> error $ "Suprising expression in transpose: " ++ pprint expr

builtinTranspose :: Builtin -> Atom -> Expr -> TransposeM ()
builtinTranspose b ct arg = case b of
  FAdd -> do
    evalTranspose ct t1
    evalTranspose ct t2
    where (t1, t2) = unpair arg
  FMul -> do
    ct' <- writeMul x ct
    evalTranspose ct' t
    where (x, t) = unpair arg
  where
    writeAdd x y = writeCoTangent $ add x y
    writeMul x y = writeCoTangent $ mul x y

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
  where
    writeAdd x y = writeTangent (add x y)
    writeMul x y = writeTangent (mul x y)

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

add :: Expr -> Expr -> Expr
add x y = App (Builtin FAdd) (RecCon (Tup [x, y]))

mul :: Expr -> Expr -> Expr
mul x y = App (Builtin FMul) (RecCon (Tup [x, y]))

zero :: Atom
zero = Lit (RealLit 0.0)

addMany :: [Expr] -> Expr
addMany [] = zero
addMany (x:xs) = App (Builtin FAdd) (RecCon (Tup [x, addMany xs]))

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

recGetExpr :: Expr -> RecField -> Expr
recGetExpr (RecCon r) field = recGet r field
recGetExpr e          field = RecGet e field

declsExpr :: [Decl] -> Expr -> Expr
declsExpr [] body = body
declsExpr decls body = Decls decls body

