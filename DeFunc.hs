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
      body' <- simplifyScoped body
      return $ For b' body'
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

simplifyScoped :: Expr -> SimplifyM Expr
simplifyScoped expr = do
  (body, (decls, _)) <- scoped $ simplify expr
  return (declsExpr decls body)

inlineDecls :: Expr -> SimplifyM Expr
inlineDecls (Decls decls final) = extend (asFst decls) >> return final
inlineDecls expr = return expr

simplifyDecl :: Decl -> SimplifyCat ()
simplifyDecl (Let (v:>_) bound) = do
  bound' <- toCat $ simplifyScoped bound
  curScope <- looks $ snd . snd
  case decompose curScope bound' of
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
      body' <- simplifyScoped body
      return $ App (TApp (Builtin Fold) ts')
                   (RecCon (Tup [For ib' (Lam xb' body'), x']))

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
    (Zero, _) -> realZero
    (_, Zero) -> realZero
    _ -> App (Builtin FMul) arg
  where (x, y) = unpair arg
simplifyBuiltin b arg = App (Builtin b) arg

data MaybeZero a = Zero | NonZero a

checkZero :: Expr -> MaybeZero Expr
checkZero (Lit (RealLit 0.0)) = Zero
checkZero expr = NonZero expr

-- === Forward differentiation ===

type DerivM a = ReaderT (Env (Either Type (Atom, Atom)))
                  (CatT (OutDecls, OutDecls) (Either Err)) a

expandDeriv :: [Type] -> Expr -> SimplifyM Expr
expandDeriv _ (Lam b body) = do
  refreshBinder b $ \(v:>ty) -> do
    body' <- simplifyScoped body
    scope <- looks snd
    let t = rename (rawName "tangent") scope
        scope' = scope <> v @> L ty <> t @> L ty
        env = getEnvTypes scope <> v @> Right (Var v, Var t)
    ((xOut, tOut), ((xDecls, _), (tDecls, _))) <-
                    liftEither $ flip runCatT (asSnd scope', asSnd scope') $
                      flip runReaderT env $ evalDeriv body'
    return $ Lam (v:>ty) $
      declsExpr xDecls $
        RecCon $ Tup [xOut, Lam (t:>ty) (declsExpr tDecls tOut)]
  where
    getEnvTypes scope = envMapMaybe asType scope
    asType x = case x of L ty -> Just (Left ty)
                         T _ -> Nothing

evalDeriv :: Expr -> DerivM (Expr, Expr)
evalDeriv expr = case expr of
  Var v -> do
    xt <- asks (!v)
    return $ case xt of
      Left ty -> (expr, zero ty)
      Right xt' -> xt'
  Lit c -> return (expr, zero (BaseType (litType c)))
  Decls [] body -> evalDeriv body
  Decls (Let (v:>_) bound:decls) body -> do
    (x, t) <- evalDeriv bound
    x' <- writePrimal  v x
    t' <- writeTangent v t
    extendR (v @> Right (x', t')) (evalDeriv body')
    where body' = Decls decls body
  App (Builtin b) arg -> do
    (x, t) <- evalDeriv arg
    builtinDeriv b x t
  For b@(i:>_) body -> do
    (body', builder) <- evalDerivScoped body
    tab <- writePrimal (rawName "tab") (For b body')
    let (xBody, tBody) = builder (Get tab i)
    return (For b xBody, For b tBody)
  RecCon r -> do
    r' <- traverse evalDeriv r
    return (RecCon (fmap fst r'), RecCon (fmap snd r'))
  RecGet e field -> do
    (x, t) <- evalDeriv e
    return (recGetExpr x field,
            recGetExpr t field)
  _ -> error $ "Suprising expression: " ++ pprint expr

builtinDeriv :: Builtin -> Expr -> Expr -> DerivM (Expr, Expr)
builtinDeriv b x t = case b of
  FAdd -> return (add x1 x2, add t1 t2)
  FMul -> do
    x1' <- writePrimal (rawName "tmp") x1
    x2' <- writePrimal (rawName "tmp") x2
    return (mul x1' x2', add (mul x2' t1)
                             (mul x1' t2))
  where
    (t1, t2) = unpair t
    (x1, x2) = unpair x

evalDerivScoped :: Expr -> DerivM (Expr, Expr -> (Expr, Expr))
evalDerivScoped expr = do
  ((xOut, tOut), ((xDecls, _), (tDecls, _))) <- scoped (evalDeriv expr)
  tScope <- looks $ snd . snd
  let tExpr = declsExpr tDecls tOut
      (saved, recon) = forceSplit $
                         matLocalVars tScope (RecCon (Tup [xOut, tExpr]))
  return (declsExpr xDecls saved, unpair . recon)

-- TODO: need to have a single shared scope - don't want primal decls reusing
-- vars already chosen by tangent decls
writePrimal :: Name -> Expr -> DerivM Atom
writePrimal name expr = do
  v <- looks $ rename name . snd . fst
  ty <- primalType expr
  extend ( ([Let (v :> ty) expr], v @> L ty)
         , ([]                  , v @> L ty)) -- primals stay in scope
  return $ Var v

writeTangent :: Name -> Expr -> DerivM Atom
writeTangent name expr = do
  v <- looks $ rename name . snd . snd
  ty <- tangentType expr
  extend $ asSnd ([Let (v :> ty) expr], v @> L ty)
  return $ Var v

-- === Transposition ===

type TransposeM a = WriterT CTEnv (CatT OutDecls (Either Err)) a
newtype CTEnv = CTEnv (Env [Atom])

instance Semigroup CTEnv where
  CTEnv env <> CTEnv env' = CTEnv $ envMonoidUnion env env'

instance Monoid CTEnv where
  mempty = CTEnv mempty
  mappend = (<>)

expandTranspose :: [Type] -> Expr -> SimplifyM Expr
expandTranspose [_, ctTy] (Lam (v:>xTy) body) = do
  ctTy' <- subTy ctTy
  xTy' <- subTy xTy
  body' <- simplifyScoped body
  scope <- looks snd
  let ct = rename (rawName "ct") scope
  let scope' = scope <> v @> L xTy' <> ct @> L ctTy'
  (((), ctEnv), (ctDecls, _)) <- liftEither $ flip runCatT (asSnd scope') $
                                   runWriterT $ evalTranspose (Var ct) body'
  return $ Lam (ct:>ctTy')
               (declsExpr ctDecls (addMany xTy (snd $ ctEnvPop ctEnv v)))

ctEnvPop :: CTEnv -> Name -> (CTEnv, [Atom])
ctEnvPop (CTEnv (Env m)) v = (CTEnv (Env m'), x)
  where m' = M.delete v m
        x = M.findWithDefault [] v m

evalTranspose :: Expr -> Expr -> TransposeM ()
evalTranspose ct expr = case expr of
  Var v -> tell $ CTEnv $ v @> [ct]
  Lit _ -> return ()
  Decls [] body -> evalTranspose ct body
  Decls (Let (v:>ty) bound:decls) final -> do
    ((), ctEnv) <- lift $ runWriterT $ evalTranspose ct body
    let (ctEnv', outCTs) = ctEnvPop ctEnv v
    tell ctEnv'
    evalTranspose (addMany ty outCTs) bound
    where body = declsExpr decls final
  App (Builtin b) arg -> builtinTranspose b ct arg
  _ -> error $ "Suprising expression in transpose: " ++ pprint expr

builtinTranspose :: Builtin -> Atom -> Expr -> TransposeM ()
builtinTranspose b ct arg = case b of
  FAdd -> do
    ct' <- writeCoTangent ct
    evalTranspose ct' t1
    evalTranspose ct' t2
    where (t1, t2) = unpair arg
  FMul -> do
    evalTranspose (mul x ct) t
    where (x, t) = unpair arg

writeCoTangent :: Expr -> TransposeM Atom
writeCoTangent expr = do
  v <- looks $ rename (rawName "ct") . snd
  ty <- coTangentType expr
  extend $ ([Let (v :> ty) expr], v @> L ty)
  return $ Var v

coTangentType :: Expr -> TransposeM Type
coTangentType expr = do env <- looks $ snd
                        return $ getType env expr

-- === handy constructor wrappers ===

add :: Expr -> Expr -> Expr
add x y = App (Builtin FAdd) (RecCon (Tup [x, y]))

mul :: Expr -> Expr -> Expr
mul x y = App (Builtin FMul) (RecCon (Tup [x, y]))

addMany :: Type -> [Expr] -> Expr
addMany ty [] = zero ty
addMany ty (x:xs) = addVect ty x (addMany ty xs)

addVect :: Type -> Expr -> Expr -> Expr
addVect (BaseType RealType) x y = add x y

unpair :: Atom -> (Atom, Atom)
unpair (RecCon (Tup [x, y])) = (x, y)

zero :: Type -> Expr
zero ty = case ty of
  BaseType RealType -> realZero
  BaseType _ -> unitCon
  RecType r -> RecCon $ fmap zero r
  TabType i a -> For (rawName "i" :> i) (zero a)
  ArrType _ _ -> error "Should be defunctionalized already"

unitCon :: Expr
unitCon = RecCon (Tup [])

realZero :: Expr
realZero = Lit (RealLit 0.0)

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
