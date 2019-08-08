{-# LANGUAGE FlexibleContexts #-}

module Normalize (normalizePass, simpPass, stripAnnotPass) where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Except hiding (Except)
import Data.Foldable
import Data.Either

import Env
import Syntax  hiding (wrapDecls)
import Record
import Cat
import PPrint
import Fresh
import Type
import Pass

type Scope = Env ()
data TLam = TLamContents NormEnv [TBinder] Expr
type NormEnv = FullEnv (Type, Either (RecTree Name) TLam) (RecTree NType)
type NormM a = ReaderT NormEnv (CatT ([NDecl], Scope) (Either Err)) a

-- TODO: add top-level freshness scope to top-level env
normalizePass :: TopDecl -> TopPass (NormEnv, Scope) NTopDecl
normalizePass topDecl = case topDecl of
  TopDecl decl -> do
    (env, decls) <- asTopPass (normalizeDecl decl)
    decl' <- case decls of
      [] -> return $ dummyDecl
      [decl'] -> return $ decl'
    putEnv (asFst env)
    return $ NTopDecl decl'
    where dummyDecl = NLet [] (NAtoms [])
  EvalCmd NoOp -> return (NEvalCmd NoOp)
  EvalCmd (Command cmd expr) -> do
    (ty   , []) <- asTopPass $ exprType expr -- TODO: subst type vars
    (expr', []) <- asTopPass $ normalizeScoped expr
    (ntys , []) <- asTopPass $ normalizeTy ty
    case cmd of Passes -> writeOutText $ "\n\nNormalized\n" ++ pprint expr'
                _ -> return ()
    return $ NEvalCmd (Command cmd (ty, toList ntys, expr'))

asTopPass :: NormM a -> TopPass (NormEnv, Scope) (a, [NDecl])
asTopPass m = do
  (env, scope) <- getEnv
  (ans, (decls, scope')) <- liftEither $ runCatT (runReaderT m env) ([], scope)
  putEnv (asSnd scope')
  return (ans, decls)

normalize :: Expr -> NormM NExpr
normalize expr = case expr of
  Lit x -> return $ NAtoms [NLit x]
  Var v -> do
    vs <- asks $ toList . fromLeft (error msg) . snd . fromL . (! v )
    return $ NAtoms (map NVar vs)
      where msg = "Type lambda should be immediately applied"
  PrimOp Scan _ [x, For ip (Lam p body)] -> do
    xs <- atomize x
    normalizeBindersR ip $ \ibs ->
      normalizeBindersR p $ \bs -> do
        body' <- normalizeScoped body
        scope <- looks snd
        return $ nestedScan scope ibs bs xs body'
  PrimOp b ts xs -> do
    xs' <- mapM atomize xs
    ts' <- liftM (concat . map toList) $ mapM normalizeTy ts
    case b of
      Deriv -> return $ NAtoms [NDeriv (fromOne (fromOne xs'))]
      _ -> return $ NPrimOp b ts' (fmap fromOne xs') -- TODO: subst types
  Decls [] body -> normalize body
  Decls (decl:decls) final -> do
    env <- normalizeDecl decl
    extendR env $ normalize (Decls decls final)
  Lam p body -> do
    normalizeBindersR p $ \bs -> do
      body' <- normalizeScoped body
      return $ NAtoms [NLam bs body']
  App f x -> do
    [f'] <- atomize f
    x' <- atomize x
    return $ NApp f' x'
  For p body -> do
    normalizeBindersR p $ \bs -> do
      body' <- normalizeScoped body
      scope <- looks snd
      return $ nestedScan scope bs [] [] body'
  Get e i -> do
    e' <- atomize e
    i' <- atomize i
    return $ NAtoms $ map (\x -> foldl NGet x i') e'
  -- -- TODO: consider finding these application sites in a bottom-up pass and
  -- -- making a single monorphic version for each distinct type found,
  -- -- rather than inlining
  TApp (Var v) ts -> do -- Assumes HM-style type lambdas only
    TLamContents env bs body <- asks $
        fromRight (error "Expected t-lambda") . snd . fromL . (! v)
    ts' <- mapM normalizeTy ts
    let env' = bindFold $ zipWith replaceAnnot bs (map T ts')
    local (const (env <> env')) $ normalize body
  RecCon r -> do
    r' <- traverse atomize r
    return $ NAtoms $ concat $ toList r'
  TabCon (TabType (IdxSetLit n) ty) rows -> do
    ts' <- liftM toList $ normalizeTy ty
    rows' <- mapM normalize rows
    return $ NTabCon (NIdxSetLit n) ts' rows'
  DerivAnnot e ann -> do
    [e'] <- atomize e
    [ann'] <- atomize ann
    return $ NAtoms [NDerivAnnot e' ann']
  _ -> error $ "Can't yet normalize: " ++ pprint expr

-- Only produces atoms without binders (i.e. no NLam/NAtomicFor)
atomize :: Expr -> NormM [NAtom]
atomize expr = do
  ty <- exprType expr
  expr' <- normalize expr
  case expr' of
    NAtoms atoms | all noBinders atoms -> return atoms
    _ -> do tys <- liftM toList $ normalizeTy ty
            writeVars tys expr'
  where
    noBinders :: NAtom -> Bool
    noBinders (NLam _ _) = False
    noBinders (NAtomicFor _ _) = False
    noBinders _ = True

-- TODO: de-shadowing might be over-zealous here
-- TODO: ought to freshen the index binders too
nestedScan :: Scope -> [NBinder] -> [NBinder] -> [NAtom] -> NExpr -> NExpr
nestedScan scope [] bs xs body = runReader (nSubst body) (bindEnv bs xs, scope)
nestedScan scope (ib:ibs) bs xs body = NScan ib bs' xs body'
  where
    vs = map binderVar bs
    (vs', scope') = renames vs scope
    bs' = [v:>ty | (_:>ty, v) <- zip bs vs']
    xs' = map (NVar . binderVar) bs'
    body' = nestedScan (scope <> scope') ibs bs xs' body  -- TODO: freshen ibs

normalizeDecl :: Decl -> NormM NormEnv
normalizeDecl decl = case decl of
  Let (RecLeaf (v:>ty)) (TLam tbs body) -> do
    env <- ask
    return $ v@>L (ty, Right (TLamContents env tbs body))
  Let p bound -> do
    bound' <- normalizeScoped bound
    (bs, env) <- normalizeBinders p
    extend $ asFst [NLet bs bound']
    return env
  Unpack b tv bound -> do
    bound' <- normalizeScoped bound
    tv' <- looks $ rename tv . snd
    let tenv = tv @> T (RecLeaf (NTypeVar tv'))
    extendR tenv $ do
      (bs, lenv) <- normalizeBinders [b]
      extend $ ([NUnpack bs tv' bound'], tv' @> ())
      return $ tenv <> lenv

normalizeTy :: Type -> NormM (RecTree NType)
normalizeTy ty = case ty of
  BaseType b -> return $ RecLeaf (NBaseType b)
  TypeVar v -> asks $ fromT . (!v)
  ArrType a b -> do
    a' <- normalizeTy a
    b' <- normalizeTy b
    return $ RecLeaf $ NArrType (toList a') (toList b')
  TabType n ty -> do
    ty' <- normalizeTy ty
    n'  <- normalizeTy n
    return $ fmap (\x -> foldr NTabType x (toList n')) ty'
  RecType r -> liftM RecTree $ traverse normalizeTy r
  Exists ty -> do
    ty' <- normalizeTy ty
    return $ RecLeaf $ NExists (toList ty')
  IdxSetLit x -> return $ RecLeaf $ NIdxSetLit x
  BoundTVar n -> return $ RecLeaf $ NBoundTVar n
  Forall _ _ -> error "Shouldn't have forall types left"

normalizeBinder :: Binder -> NormM ([NBinder], NormEnv)
normalizeBinder (v:>ty) = do
  tys <- normalizeTy ty
  bs <- flip traverse tys $ \t -> do
          v' <- looks $ rename v . snd
          extend $ asSnd (v' @> ())
          return $ v':>t
  let env' = (v @> L (ty, Left (fmap binderVar bs)))
  return (toList bs, env')

normalizeBinders :: Traversable f =>
                      f Binder -> NormM ([NBinder], NormEnv)
normalizeBinders bs = liftM fold $ traverse normalizeBinder bs

normalizeBindersR :: Traversable f =>
                       f Binder -> ([NBinder] -> NormM a) -> NormM a
normalizeBindersR bs cont = do
  ((bs', env), catEnv) <- scoped $ normalizeBinders bs
  extendLocal catEnv $ extendR env $ cont bs'

normalizeScoped :: Expr -> NormM NExpr
normalizeScoped expr = do
  (body, (decls, _)) <- scoped $ normalize expr
  return $ wrapDecls decls body

exprType :: Expr -> NormM Type
exprType expr = do
  env <- ask
  let env' = flip fmap env $ \x -> case x of L (ty,_) -> L ty
                                             T _      -> T ()
  return $ getType env' expr

writeVars :: Traversable f => f NType -> NExpr -> NormM (f NAtom)
writeVars tys expr = do
  scope <- looks snd
  let (bs, scope') = flip runCat scope $
                       flip traverse tys $ \t -> do
                         v <- freshCat (rawName "tmp")
                         return $ v:>t
  extend  ([NLet (toList bs) expr], scope')
  return $ fmap (NVar . binderVar) bs

-- === simplification pass ===

type NScope = FullEnv NType ()
type SimpEnv = (FullEnv NAtom Var, NScope)
type SimplifyM a = ReaderT SimpEnv (Either Err) a

-- TODO: consider maintaining free variables explicitly
data Ions = Ions NExpr [NBinder] [NAtom] | Unchanged

simpPass :: NTopDecl -> TopPass SimpEnv NTopDecl
simpPass topDecl = case topDecl of
  NTopDecl decl -> do
    (decls, env) <- simpAsTopPass $ simplifyDecl decl
    decl' <- case decls of
      [] -> return $ dummyDecl
      [decl'] -> return decl'
    putEnv env
    return $ NTopDecl decl'
    where dummyDecl = NLet [] (NAtoms [])
  NEvalCmd NoOp -> return (NEvalCmd NoOp)
  NEvalCmd (Command cmd (ty, ntys, expr)) -> do
    -- TODO: handle type vars
    expr' <- simpAsTopPass $ simplify expr
    case cmd of Passes -> writeOutText $ "\n\nSimp\n" ++ pprint expr'
                _ -> return ()
    return $ NEvalCmd (Command cmd (ty, ntys, expr'))

simpAsTopPass :: SimplifyM a -> TopPass SimpEnv a
simpAsTopPass m = do
  env <- getEnv
  liftEither $ runReaderT m env

simplify :: NExpr -> SimplifyM NExpr
simplify expr = case expr of
  NDecls [] body -> simplify body
  NDecls (decl:rest) final -> do
    (decls, env) <- simplifyDecl decl
    body' <- extendR env $ simplify body
    return $ wrapDecls decls body'
    where body = NDecls rest final
  NScan b bs xs e -> do
    xs' <- mapM simplifyAtom xs
    refreshBindersRSimp (b:bs) $ \(b':bs') -> do
      e' <- simplify e
      return $ NScan b' bs' xs' e'
  NApp f xs -> do
    xs' <- mapM simplifyAtom xs
    f' <- simplifyAtom f
    case f' of
      NLam bs body -> extendR env (simplify body)
        where env = asFst $ bindEnv bs xs'
      _ -> return $ NApp f' xs'
  NPrimOp b ts xs -> liftM2 (NPrimOp b) (mapM nSubstSimp ts) (mapM simplifyAtom xs)
  NAtoms xs -> liftM NAtoms $ mapM simplifyAtom xs
  NTabCon n ts rows ->
    liftM3 NTabCon (nSubstSimp n) (mapM nSubstSimp ts) (mapM simplify rows)

simplifyAtom :: NAtom -> SimplifyM NAtom
simplifyAtom atom = case atom of
  NLit x -> return $ NLit x
  NVar v -> do
    x <- asks $ flip envLookup v . fst
    case x of
      Nothing -> return $ NVar v
      Just (L x') -> local (\(_, scope) -> (mempty, scope)) (simplifyAtom x')
  NGet e i -> do
    e' <- simplifyAtom e
    i' <- simplifyAtom i
    return $ nGet e' i'
  NAtomicFor b body ->
    -- TODO: eta convert if possible
    refreshBindersRSimp [b] $ \[b'] -> do
      body' <- simplifyAtom body
      return $ NAtomicFor b' body'
  NLam bs body ->
    refreshBindersRSimp bs $ \bs' -> do
      body' <- simplify body
      return $ NLam bs' body'
  NDeriv f -> do
    f' <- simplifyAtom f
    expandDerivTop f'
  NDerivAnnot f df -> liftM2 NDerivAnnot (simplifyAtom f) (simplifyAtom df)

simplifyDecl :: NDecl -> SimplifyM ([NDecl], SimpEnv)
simplifyDecl decl = case decl of
  NLet bs bound -> do
    -- As pointed out in the 'ghc inliner' paper, this can lead to exponential
    -- blowup in compile times. The solution will be to defer some
    -- simplification, pairing the expression with the env, to be forced later.
    bound' <- simplify bound
    case decompose mempty bound' of
      Unchanged -> do
        (bs', env) <- refreshBindersSimp bs
        return ([NLet bs' bound'], env)
      Ions bound'' bs' ions ->
        return $ case bs' of [] -> ([]     , env)
                             _  -> ([decl'], env)
        where env = (bindEnv bs ions, newScope bs')
              decl' = NLet bs' bound''
  NUnpack bs tv bound -> do
    bound' <- simplify bound
    tv' <- asks $ rename tv . snd
    let tEnv = (tv @> T tv', tv' @> T ())
    (bs', lEnv) <- extendR tEnv $ refreshBindersSimp bs
    return ([NUnpack bs' tv' bound'], tEnv <> lEnv)

decompose :: Env NType -> NExpr -> Ions
decompose scope expr = case expr of
  NDecls decls body -> case body' of
    Ions expr bs atoms -> Ions (wrapDecls decls expr) bs atoms
    Unchanged -> Unchanged
    where
      body' = decompose (scope <> scope') body
      scope' = foldMap declsScope decls
      declsScope decl = case decl of
        NLet bs _ -> bindFold bs
  NScan b@(_:>n) [] [] body -> case decompose mempty body of
    Unchanged -> Unchanged
    Ions body' bs atoms -> Ions (NScan b [] [] body') bs' atoms'
      where bs' = map (fmap (NTabType n)) bs
            atoms' = map (wrapAtomFor b bs) atoms
  NScan _ _ _ _ -> Unchanged
  NPrimOp _ _ _ -> Unchanged
  NApp _ _      -> Unchanged
  NAtoms xs -> Ions expr' bs xs  -- TODO: special treatment of unchanged case
    where
      vs = foldMap freeVars xs
      bs = map (uncurry (:>)) $ envPairs $ envIntersect vs scope
      expr' = NAtoms $ fmap (NVar . binderVar) bs
  NTabCon _ _ _ -> Unchanged

wrapAtomFor :: NBinder -> [NBinder] -> NAtom -> NAtom
wrapAtomFor b@(i:>_) bs atom = NAtomicFor b atom'
  where atom' = runReader (nSubst atom) (env, mempty)
        env = foldMap (\(v:>_) -> v @> L (NGet (NVar v) (NVar i))) bs

bindEnv :: [BinderP c] -> [a] -> FullEnv a b
bindEnv bs xs = fold $ zipWith f bs xs
  where f (v:>_) x = v @> L x

newScope :: [NBinder] -> NScope
newScope bs = foldMap (\(v:>ty) -> v@>L ty) bs

-- TODO: de-dup with version in subst
refreshBindersSimp :: [NBinder] -> SimplifyM ([NBinder], SimpEnv)
refreshBindersSimp bs = catTraverse refreshBinderSimp bs

refreshBinderSimp :: NBinder -> SimplifyM (NBinder, SimpEnv)
refreshBinderSimp (v:>ty) = do
  scope <- asks snd
  ty' <- nSubstSimp ty
  let v' = rename v scope
  return (v':>ty', (v @> L (NVar v'), v' @> L ty'))

nSubstSimp :: NSubst a => a -> SimplifyM a
nSubstSimp x = do
  (env, scope) <- ask
  return $ runReader (nSubst x) (env, fmap (const ()) scope)

refreshBindersRSimp :: [NBinder] -> ([NBinder] -> SimplifyM a) -> SimplifyM a
refreshBindersRSimp bs cont = do (bs', env) <- refreshBindersSimp bs
                                 extendR env $ cont bs'

wrapDecls :: [NDecl] -> NExpr -> NExpr
wrapDecls [] body = body
wrapDecls decls (NDecls decls' body) = NDecls (decls ++ decls') body
wrapDecls decls body = NDecls decls body

fromOne :: [x] -> x
fromOne [x] = x
fromOne _ = error "Expected singleton list"

-- === forward-mode differentiation ===

type OneOrTwo a = [a]
type TangentBun = OneOrTwo NAtom
type DerivEnv = (Env TangentBun, Env ())
type DerivM = Reader DerivEnv

expandDerivTop :: NAtom -> SimplifyM NAtom
expandDerivTop atom@(NVar _) = return (NDeriv atom)
expandDerivTop atom = do
  typeEnv <- asks snd
  let env = flip fmapNames typeEnv $ \v x ->
               case x of L ty -> pureBun ty (NVar v)
                         T () -> [] -- TODO: filter properly
      scope = fmap (const ()) typeEnv
      atom' = fromOne $ runReader (derivNAtom atom) (env, scope)
  simplifyAtom atom'

derivNExpr :: NExpr -> DerivM NExpr
derivNExpr expr = case expr of
  NDecls [] body -> derivNExpr body
  NDecls (decl:rest) final -> case decl of
    NLet bs bound -> do
      bound' <- derivNExpr bound
      -- TODO: refresh binders and introduce names for tangents
      updateDerivBinders bs $ \bs' -> do
        body' <- derivNExpr body
        return $ wrapDecls [NLet bs' bound'] body'
    where body = NDecls rest final
  -- NScan b bs xs e -> refreshBindersR (b:bs) $ \(b':bs') ->
  --                      liftM2 (NScan b' bs') (mapM nSubst xs) (nSubst e)
  NApp f xs -> do
    [f'] <- derivNAtom f
    xs' <- liftM concat $ mapM derivNAtom xs
    return $ NApp f' xs'
  NAtoms xs -> liftM (NAtoms . concat) $ mapM derivNAtom xs
  _ -> error $ "Don't know how to differentiate " ++ pprint expr

derivNAtom :: NAtom -> DerivM TangentBun
derivNAtom atom = case atom of
  NLit x -> return $ pureBun (NBaseType (litType x)) atom
  NVar v -> asks $ (!v) . fst
  NGet x i -> do
    xs <- derivNAtom x
    [i'] <- derivNAtom i
    return $ map (flip NGet i') xs
  NLam bs body -> do
    updateDerivBinders bs $ \bs' -> do
      body' <- derivNExpr body
      return [NLam bs' body']
  NAtomicFor b x -> do -- TODO: refresh binder
    xs <- derivNAtom x
    updateDerivBinders [b] $ \[b'] ->
      return $ map (NAtomicFor b') xs
  NDerivAnnot _ d -> return [d]
     -- Need to apply substitution here? Probably yes if we have local free vars
     -- Should annot be OneOrTwo?
  NDeriv _ -> error "Shouldn't see derivatives here"

updateDerivBinders :: [NBinder] -> ([NBinder] -> DerivM a) -> DerivM a
updateDerivBinders bs cont = do
  (bs', env) <- catTraverse derivBinder bs
  extendR env $ cont (concat bs')

derivBinder :: NBinder -> DerivM (OneOrTwo NBinder, DerivEnv)
derivBinder (v:>ty) = do
  let  tys' = tangentBunNType ty
       vs'  = case tys' of [_]   -> [v]
                           [_,_] -> [v, rawName (nameTag v)]
  (vs'', scope) <- asks $ renames vs' . snd
  let env = (v @> map NVar vs'')
  return (zipWith (:>) vs'' tys', (env, scope))

-- TODO: make this take a scope for fresh index varsto freshen the index vars
pureBun :: NType -> NAtom -> TangentBun
pureBun ty x = case ty of
  NBaseType b -> case b of RealType -> [x, NLit (RealLit 0.0)]
                           _ -> [x]
  NTypeVar _ -> [x]  -- can only be an index set
  NArrType _ _ -> [NDeriv x]
  NTabType n a -> map (NAtomicFor (i:>n)) (pureBun a (NGet x (NVar i)))
     where i = rawName "i" -- Shadowing ok here? Prefer 'fanout' from prelude
--  NExists ts -> [NExists $ foldMap recur ts]
  NIdxSetLit _ -> [x]
  NBoundTVar _ -> [x]
  where recur = tangentBunNType

-- === capture-avoiding substitutions on NExpr and friends ===

type SubstEnv = (FullEnv NAtom Var, Env ())

class NSubst a where
  nSubst :: MonadReader SubstEnv m => a -> m a

instance NSubst NExpr where
  nSubst expr = case expr of
    NDecls [] body -> nSubst body
    NDecls (decl:rest) final -> case decl of
      NLet bs bound -> do
        bound' <- nSubst bound
        refreshBindersR bs $ \bs' -> do
           body' <- nSubst body
           return $ wrapDecls [NLet bs' bound'] body'
       where body = NDecls rest final
    NScan b bs xs e -> refreshBindersR (b:bs) $ \(b':bs') ->
                         liftM2 (NScan b' bs') (mapM nSubst xs) (nSubst e)
    NPrimOp b ts xs -> liftM2 (NPrimOp b) (mapM nSubst ts) (mapM nSubst xs)
    NApp f xs -> liftM2 NApp (nSubst f) (mapM nSubst xs)
    NAtoms xs -> liftM NAtoms $ mapM nSubst xs
    NTabCon n ts rows ->
      liftM3 NTabCon (nSubst n) (mapM nSubst ts) (mapM nSubst rows)

instance NSubst NAtom where
  nSubst atom = case atom of
    NLit x -> return $ NLit x
    NVar v -> do
      x <- asks $ flip envLookup v . fst
      case x of
        Nothing -> return $ NVar v
        Just (L x') -> local (\(_, scope) -> (mempty, scope)) (nSubst x')
    NGet e i -> do
      e' <- nSubst e
      i' <- nSubst i
      return $ nGet e' i'
    NAtomicFor b body ->
      -- TODO: eta convert if possible
      refreshBindersR [b] $ \[b'] -> do
        body' <- nSubst body
        return $ NAtomicFor b' body'
    NLam bs body ->
      refreshBindersR bs $ \bs' -> do
        body' <- nSubst body
        return $ NLam bs' body'

instance NSubst NType where
  nSubst ty = case ty of
    NBaseType _ -> return ty
    NTypeVar v -> do
      x <- asks $ flip envLookup v . fst
      return $ case x of Nothing -> ty
                         Just (T x') -> NTypeVar x'
    NArrType as bs -> liftM2 NArrType (mapM nSubst as) (mapM nSubst bs)
    NTabType a b -> liftM2 NTabType (nSubst a) (nSubst b)
    NExists ts -> liftM NExists (mapM nSubst ts)
    NIdxSetLit _ -> return ty
    NBoundTVar _ -> return ty

nGet :: NAtom -> NAtom -> NAtom
nGet (NAtomicFor (v:>_) body) i = runReader (nSubst body) (v@>L i, scope)
  where scope = fmap (const ()) (freeVars i)
nGet e i = NGet e i


-- TODO: de-dup with version in simp, above
refreshBinders :: MonadReader SubstEnv m => [NBinder] -> m ([NBinder], SubstEnv)
refreshBinders bs = do
  scope <- asks snd
  ts' <- mapM nSubst ts
  let (vs', scope') = renames vs scope
      env' = fold $ zipWith (\v v' -> v @> L (NVar v')) vs vs'
      bs' = zipWith (:>) vs' ts'
  return (bs', (env', scope'))
  where (vs, ts) = unzip [(v,t) | v:>t <- bs]

refreshBindersR :: MonadReader SubstEnv m =>
                     [NBinder] -> ([NBinder] -> m a) -> m a
refreshBindersR bs cont = do (bs', env) <- refreshBinders bs
                             extendR env $ cont bs'

-- === stripping annotations ===

stripAnnotPass :: NTopDecl -> TopPass () NTopDecl
stripAnnotPass topDecl = return $ case topDecl of
  NTopDecl decl -> NTopDecl $ stripDerivAnnotDecl decl
  NEvalCmd NoOp -> NEvalCmd NoOp
  NEvalCmd (Command cmd (ty, tys, expr)) ->
    NEvalCmd (Command cmd (ty, tys, expr'))
    where expr' = stripDerivAnnot expr

-- TODO: find a simpler way to do passes that only touch a few constructors
stripDerivAnnotDecl :: NDecl -> NDecl
stripDerivAnnotDecl decl = case decl of
  NLet bs bound -> NLet bs (stripDerivAnnot bound)

stripDerivAnnot :: NExpr -> NExpr
stripDerivAnnot expr = case expr of
  NDecls decls body -> NDecls (map stripDerivAnnotDecl decls) (recur body)
  NScan b bs xs e -> NScan b bs (map recurAtom xs) (recur e)
  NPrimOp b ts xs -> NPrimOp b ts (map recurAtom xs)
  NApp f xs -> NApp (recurAtom f) (map recurAtom xs)
  NAtoms xs -> NAtoms $ map recurAtom xs
  NTabCon n ts rows -> NTabCon n ts (map recur rows)
  where recur = stripDerivAnnot
        recurAtom = stripDerivAnnotAtom

stripDerivAnnotAtom :: NAtom -> NAtom
stripDerivAnnotAtom atom = case atom of
  NDerivAnnot f _ -> f
  NLam bs body -> NLam bs (stripDerivAnnot body)
  _ -> atom
