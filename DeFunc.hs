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
  PrimOp b ts args -> do
    ts' <- mapM subTy ts
    case b of
      Fold      -> simplifyFold    ts' args
      VSum      -> simplifyVSum    ts' args
      Deriv     -> expandDeriv     ts' args
      Transpose -> expandTranspose ts' args
      _ -> do args' <- mapM recur args
              return $ simplifyBuiltin b ts' args'
  App fexpr arg -> do
    Lam (v:>_) body <- recur fexpr
    arg' <- recur arg
    dropSubst $
      extendR (v @> L arg') $ recur body
  For b body -> do
    refreshBinder b $ \b' -> do
      body' <- simplifyScoped body
      return $ For b' body'
  Get e ie -> do
    e' <- recur e
    ie' <- recur ie
    case e' of
      For (i:>_) body -> do
        dropSubst $
          extendR (i @> L ie') $
            applySub body >>= inlineDecls
      _ -> return $ Get e' ie'
  RecCon r -> liftM RecCon $ traverse recur r
  RecGet e field -> do
    e' <- recur e
    return $ recGetExpr e' field
  TabCon _ _ _ -> return expr -- Assumes nothing tricky inside (TODO: check/handle)
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
  PrimOp b _ _ -> if trivialBuiltin b then Defer expr else pureMat expr
  App _ _ -> pureMat expr
  For b@(i:>_) body ->
    case decompose scope body of
      -- could use a FullMat constructor here
      Split body' recon -> Split (For b body')
                                 (\e -> For b (recon (Get e (Var i))))  -- need fresh i?
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
  TabCon _ _ _ -> pureMat expr
  TLam _ _ -> matLocalVars scope expr
  _ -> error $ "Can't decompose " ++ pprint expr
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
simplifyFold :: [Type] -> [Expr] -> SimplifyM Expr
simplifyFold ts [For ib (Lam xb body), x] = do
  x' <- simplify x
  refreshBinder ib $ \ib' ->
    refreshBinder xb $ \xb' -> do
      body' <- simplifyScoped body
      return $ PrimOp Fold ts [For ib' (Lam xb' body'), x']

simplifyVSum :: [Type] -> [Expr] -> SimplifyM Expr
simplifyVSum [ty, n] [For b body] = do
  refreshBinder b $ \b' -> do
    (decls, body') <- liftM fromDeclsExpr $ simplifyScoped body
    case decls of
      [] -> do
        return $ simplifyVSumBody n b' ty body'

simplifyVSumBody :: Type -> Binder -> Type -> Expr -> Expr
simplifyVSumBody n b (RecType tr) (RecCon xr) =
  RecCon $ recZipWith (simplifyVSumBody n b) tr xr
simplifyVSumBody _ b@(i:>_) _ (PrimOp VSingle _ [Var i', x]) | i == i' = For b x
simplifyVSumBody n b ty body = PrimOp VSum [ty, n] [For b body]

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
  VZero -> True
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

simplifyBuiltin :: Builtin -> [Type] -> [Expr] -> Expr
simplifyBuiltin FAdd [] [x, y] =
  case (checkZero x, checkZero y) of
    (Zero, _) -> y
    (_, Zero) -> x
    _ -> PrimOp FAdd [] [x, y]
simplifyBuiltin FMul [] [x, y] =
  case (checkZero x, checkZero y) of
    (Zero, _) -> fzero
    (_, Zero) -> fzero
    _ -> PrimOp FMul [] [x, y]
simplifyBuiltin VAdd ty [x, y] = case (ty, x, y) of
  (_, PrimOp VZero _ _, _) -> y
  (_, _, PrimOp VZero _ _) -> x
  _ -> PrimOp VAdd ty [x, y]
simplifyBuiltin b ts xs = PrimOp b ts xs

data MaybeZero a = Zero | NonZero a

checkZero :: Expr -> MaybeZero Expr
checkZero (Lit (RealLit 0.0)) = Zero
checkZero (PrimOp VZero _ _ ) = Zero
checkZero expr = NonZero expr

-- === Forward differentiation ===

type DerivM a = ReaderT (Env (Either Type (Atom, Atom)))
                  (CatT (OutDecls, OutDecls) (Either Err)) a

expandDeriv :: [Type] -> [Expr] -> SimplifyM Expr
expandDeriv _ [Lam b body] = do
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
      Left ty -> (expr, vzero ty)
      Right xt' -> xt'
  Lit c -> return (expr, vzero (BaseType (litType c)))
  Decls [] body -> evalDeriv body
  Decls (Let (v:>_) bound:decls) body -> do
    (x, t) <- evalDeriv bound
    x' <- writePrimal  v x
    t' <- writeTangent v t
    extendR (v @> Right (x', t')) (evalDeriv body')
    where body' = Decls decls body
  PrimOp b tys args -> do
    (xs, ts) <- liftM unzip $ mapM evalDeriv args
    builtinDeriv b tys xs ts
  For b@(i:>ty) body -> do
    let ext = ([], i@>L ty)
    (body', builder) <- extendLocal (ext, ext) $ evalDerivScoped body
    tab <- writePrimal (rawName "tab") (For b body')
    let (xBody, tBody) = builder (Get tab (Var i))
    return (For b xBody, For b tBody)
  Get e i -> do (x, t) <- evalDeriv e
                return (Get x i, Get t i)
  RecCon r -> do
    r' <- traverse evalDeriv r
    return (RecCon (fmap fst r'), RecCon (fmap snd r'))
  RecGet e field -> do
    (x, t) <- evalDeriv e
    return (recGetExpr x field,
            recGetExpr t field)
  _ -> error $ "Surprising expression: " ++ pprint expr

builtinDeriv :: Builtin -> [Type] -> [Expr] -> [Expr] -> DerivM (Expr, Expr)
builtinDeriv b tys xs ts | isLinear b = return (PrimOp b tys xs,
                                                PrimOp b tys ts)
builtinDeriv FMul _ [x1, x2] [t1, t2] = do
  x1' <- writePrimal (rawName "tmp") x1
  x2' <- writePrimal (rawName "tmp") x2
  return (fmul x1' x2', fadd (fmul x2' t1)
                             (fmul x1' t2))
builtinDeriv b _ _ _ = error $ "Fwd derivative not implemented: " ++ pprint b

isLinear :: Builtin -> Bool
isLinear b = case b of
  FAdd -> True
  VSum -> True
  VZero -> True
  VAdd -> True
  _ -> False

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

primalType :: Expr -> DerivM Type
primalType expr = do env <- looks $ snd . fst
                     return $ getType env expr

-- === Transposition ===

type TransposeM a = ReaderT (FullEnv Type ())
                      (WriterT CTEnv (CatT OutDecls (Either Err))) a
newtype CTEnv = CTEnv (Env [Atom])

instance Semigroup CTEnv where
  CTEnv env <> CTEnv env' = CTEnv $ envMonoidUnion env env'

instance Monoid CTEnv where
  mempty = CTEnv mempty
  mappend = (<>)

expandTranspose :: [Type] -> [Expr] -> SimplifyM Expr
expandTranspose [_, ctTy] [Lam b body] = do
  refreshBinder b $ \(v:>xTy) -> do
    body' <- simplifyScoped body
    scope <- looks snd
    let ct = rename (rawName "ct") scope
        scope' = scope <> v @> L xTy <> ct @> L ctTy
    (((), ctEnv), (ctDecls, _)) <- liftEither $ flip runCatT (asSnd scope') $
                                     runWriterT $ flip runReaderT scope' $
                                       evalTranspose (Var ct) body'
    return $ Lam (ct:>ctTy)
                 (declsExpr ctDecls (vaddMany xTy (snd $ ctEnvPop ctEnv v)))

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
    env <- ask
    ((), ctEnv) <- lift $ lift $ runWriterT $ flip runReaderT (env <> v@>L ty) $
                     evalTranspose ct body
    let (ctEnv', outCTs) = ctEnvPop ctEnv v
    tell ctEnv'
    evalTranspose (vaddMany ty outCTs) bound
    where body = declsExpr decls final
  For (i:>iTy) body -> do
    env <- ask
    (((), CTEnv ctEnv), (decls, _)) <- scoped $ lift $ lift $ runWriterT $
                                         flip runReaderT (env <> i@>L iTy) $
                                           evalTranspose (Get ct (Var i)) body
    let vs = envNames ctEnv
        final = [vaddMany (fromL (env ! v)) (ctEnv ! v) | v <- vs]
        bodyTy = RecType $ Tup $ map (\v -> fromL (env ! v)) vs
    summed <- writeCoTangent $
      vsum bodyTy iTy $ For (i:>iTy) (declsExpr decls (RecCon (Tup final)))
    flip mapM_ (recNameVals (Tup vs)) $ \(field, v) ->
      tell $ CTEnv $ v @> [RecGet summed field]
  Get e i -> do
    env <- ask
    let TabType n ty = getType env e
    evalTranspose (vsingle ty n i ct) e
  RecCon r -> mapM_ evalElt (recNameVals r)
    where evalElt (field, val) = evalTranspose (recGetExpr ct field) val
  -- Tranposition of full unpacking of an n-tuple using recget creates an n^2
  -- expression. Should we reconsider unpacking with pattern matching instead?
  RecGet e field -> do
    env <- ask
    let RecType r = getType env e
        ct' = RecCon $ recUpdate field ct (fmap vzero r)
    evalTranspose ct' e
  PrimOp b ts args -> builtinTranspose b ts ct args
  _ -> error $ "Surprising expression in transpose: " ++ pprint expr

builtinTranspose :: Builtin -> [Type] -> Expr -> [Expr] -> TransposeM ()
builtinTranspose FAdd [] ct [t1, t2] = do
  ct' <- writeCoTangent ct
  evalTranspose ct' t1
  evalTranspose ct' t2
builtinTranspose FMul [] ct [x, t] = evalTranspose (fmul x ct) t
builtinTranspose VSum [_, n] ct [xs] = do
  ct' <- writeCoTangent ct
  evalTranspose (For (i:>n) ct') xs
  where i = rawName "iT"  -- TODO: freshness!
builtinTranspose b _ _ _ = error $ "Transpose not implemented: " ++ pprint b

writeCoTangent :: Expr -> TransposeM Atom
writeCoTangent expr = do
  v <- looks $ rename (rawName "ct") . snd
  ty <- coTangentType expr
  extend $ ([Let (v :> ty) expr], v @> L ty)
  return $ Var v

coTangentType :: Expr -> TransposeM Type
coTangentType expr = do env <- looks $ snd
                        return $ getType env expr

tangentType :: Expr -> DerivM Type
tangentType expr = do env <- looks $ snd . snd
                      return $ getType env expr

-- === constructor wrappers with some simplifications built in ===

fadd x y = PrimOp FAdd [] [x, y]
fmul x y = PrimOp FMul [] [x, y]
fzero :: Expr
fzero = Lit (RealLit 0.0)

vzero   ty       = PrimOp VZero   [ty] []
vsingle ty n i x = PrimOp VSingle [ty, n] [i, x]
vsum    ty n x   = PrimOp VSum    [ty, n] [For (i:>n) (Get x (Var i))]
  where i = rawName "vsumI" -- TODO: freshen

vadd :: Type -> Expr -> Expr -> Expr
vadd _ (PrimOp VZero _ _) y = y
vadd _ x (PrimOp VZero _ _) = x
vadd ty x y = PrimOp VAdd [ty] [x, y]

vaddMany :: Type -> [Expr] -> Expr
vaddMany ty xs = foldr (vadd ty) (vzero ty) xs

recGetExpr :: Expr -> RecField -> Expr
recGetExpr (RecCon r) field = recGet r field
recGetExpr (PrimOp VZero [RecType r] []) field = PrimOp VZero [recGet r field] []
recGetExpr e          field = RecGet e field

declsExpr :: [Decl] -> Expr -> Expr
declsExpr [] body = body
declsExpr decls body = Decls decls body

fromDeclsExpr :: Expr -> ([Decl], Expr)
fromDeclsExpr (Decls decls body) = (decls, body)
fromDeclsExpr expr = ([], expr)

unpair :: Expr -> (Expr, Expr)
unpair (RecCon (Tup [x, y])) = (x, y)
