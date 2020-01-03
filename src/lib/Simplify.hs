-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Simplify (derivPass, simpPass) where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Foldable
import qualified Data.Map.Strict as M

import Type
import Env
import Syntax
import Cat
import PPrint
import Pass
import Subst
import Embed
import Util

type NScope = FullEnv NType ()

type SimpSubEnv = FullEnv NAtom Name
type DerivRuleEnv = Env NAtom

data SimpEnv = SimpEnv { subEnv   :: SimpSubEnv
                       , derivEnv :: DerivRuleEnv }

type SimpTopEnv = (SimpEnv, NScope)
type SimplifyM a = ReaderT SimpEnv (NEmbedT (Either Err)) a

derivPass :: TopPass NTopDecl NTopDecl
derivPass = TopPass $ \topDecl -> case topDecl of
  NTopDecl PlainDecl decl -> simplifyDeclTop decl
  NTopDecl ADPrimitive decl -> do
    let NLet bs _ = decl
    decl' <- liftTopNoDecl $ nSubstSimp decl
    extend $ asSnd (foldMap lbind bs)
    return [NTopDecl PlainDecl decl']
  NRuleDef (LinearizationDef v) _ ~(NAtoms [f]) -> do
    f' <- liftTopNoDecl $ nSubstSimp f
    extend $ asFst $ mempty {derivEnv = v @> f' }
    emitOutput $ NoOutput
  NEvalCmd (Command cmd (ty, ntys, expr)) -> do
    expr' <- liftTopNoDecl $ buildScoped $ simplifyMat expr
    case cmd of
      ShowDeriv -> emitOutput $ TextOut $ pprint expr'
      _ -> return [NEvalCmd (Command cmd (ty, ntys, expr'))]

simpPass :: TopPass NTopDecl NTopDecl
simpPass = TopPass $ \topDecl -> case topDecl of
  NTopDecl _ decl -> simplifyDeclTop decl
  NRuleDef _ _ _ -> error "Shouldn't have derivative rules left"
  NEvalCmd (Command cmd (ty, ntys, expr)) -> do
    expr' <- liftTopNoDecl $ buildScoped $ simplifyMat expr
    case cmd of
      ShowSimp -> emitOutput $ TextOut $ pprint expr'
      _ -> return [NEvalCmd (Command cmd (ty, ntys, expr'))]

liftTopNoDecl :: SimplifyM a -> TopPassM SimpTopEnv a
liftTopNoDecl m = do
  (ans, decls) <- liftTop m
  unless (null decls) $ throwTopErr $ Err CompilerErr Nothing "Shouldn't have emitted decls"
  return ans

liftTop :: SimplifyM a -> TopPassM SimpTopEnv (a, [NDecl])
liftTop m = do
  (env, scope) <- look
  (ans, (scope', decls)) <- liftExceptTop $ runEmbedT (runReaderT m env) scope
  extend $ asSnd scope'
  return (ans, decls)

simplifyDeclTop :: NDecl -> TopPassM SimpTopEnv [NTopDecl]
simplifyDeclTop decl = do
  (env, decls) <- liftTop $ simplifyDeclScoped decl
  extend (asFst env)
  return $ map (NTopDecl PlainDecl) decls

simplifyDeclScoped :: NDecl -> SimplifyM SimpEnv
simplifyDeclScoped decl = case decl of
  NLet bs bound -> do
    (xs, (scope, decls)) <- scoped  $ simplify bound
    let (xsClosure, reconstruct) = splitAtoms scope xs
    xsClosure' <- emitNamed (nameHint bs) $ wrapNDecls decls (NAtoms xsClosure)
    xs' <- reconstruct xsClosure'
    return $ mempty { subEnv = bindEnv bs xs'}
  NUnpack bs tv bound -> do
    bound' <- buildScoped $ simplifyMat bound
    ~(NTypeVar tv', emitUnpackRest) <- emitUnpack tv bound'
    let tEnv = tv @> T tv'
    bs' <- extendSub tEnv $ mapM nSubstSimp bs
    xs <- emitUnpackRest bs'
    return $ mempty {subEnv = tEnv <> bindEnv bs' xs}

nameHint :: [NBinder] -> Name
nameHint bs = case bs of [] -> "tmp"
                         (v:>_):_ -> v

-- Simplification gives us a ([NDecl], [NAtoms]) pair. The decls are fully
-- simplified: no `NLam`, `NAtomicFor` or differentiation operations. The atoms
-- are not: e.g. a lambda that can't be beta-reduced yet.
simplify :: NExpr -> SimplifyM [NAtom]
simplify expr = case expr of
  NDecl decl body -> do
    env <- simplifyDecl decl
    extendR env $ simplify body
  NScan ib bs xs e -> do
    xs' <- mapM (simplifyAtom >=> materializeAtom) xs
    ib' <- nSubstSimp ib
    bs' <- mapM nSubstSimp bs
    ((csOut, ysOut), ~(ib'':bs''), (scope, decls)) <-
        withBinders (ib':bs') $ \(i:carry) ->
           extendSub (bindEnv (ib':bs') (i:carry)) $ do
             (csOut, ysOut) <- liftM splitCarry $ simplify e
             csOut' <- mapM materializeAtom csOut
             return (csOut', ysOut)
    let i = binderVar ib''
    let (ysClosure, reconstruct) = splitAtoms (envDelete i scope) ysOut
    (csOut', ysClosure') <- liftM splitCarry $ emit $ NScan ib'' bs'' xs' $
                              wrapNDecls decls (NAtoms (csOut ++ ysClosure))
    let ysClosure'' = map (flip nGet (NVar i)) ysClosure'
    ysOut' <- liftM (map (NAtomicFor ib'')) $ reconstruct ysClosure''
    return $ csOut' ++ ysOut'
    where splitCarry = splitAt (length bs)
  NApp f xs -> do
    xs' <- mapM simplifyAtom xs
    f' <- simplifyAtom f
    case f' of
      NLam _ bs body -> dropSub $ extendSub (bindEnv bs xs') $ simplify body
      _              -> emit $ NApp f' xs'
  NPrimOp Linearize _ ~(f:xs) -> do
    xs' <- mapM simplifyAtom xs
    (bs, body) <- simplifyLam f
    dropSub $ do
      linearized <- buildScoped $ runLinearization bs xs' body
      simplify linearized
  NPrimOp Transpose [_, bTy] ~[f] -> do
    (bs, body) <- simplifyLam f
    bTy' <- mapM nSubstSimp bTy
    transposed <- buildNLam Lin ["ct":>ty | ty <- bTy'] $ \cts ->
                    dropSub $ runTransposition bs cts body
    return [transposed]
  NPrimOp b ts xs -> do
    ts' <- mapM (mapM nSubstSimp) ts
    xs' <- mapM (simplifyAtom >=> materializeAtom) xs
    emit $ NPrimOp b ts' xs'
  NAtoms xs -> mapM simplifyAtom xs
  NTabCon n ts rows -> do
    -- TODO: consider making NTabCon only take atoms
    n'     <- nSubstSimp n
    ts'    <- mapM nSubstSimp ts
    rows'  <- mapM simplifyMat rows
    emit $ NTabCon n' ts' rows'

-- As we prepare to leave a scope (say that of `NScan`) we save the variables
-- we'll no longer have access to once we've left, along with a function that
-- can reconstruct the atoms (e.g. lambdas) on the other side.
splitAtoms :: NEmbedScope -> [NAtom] -> ([NAtom], [NAtom] -> SimplifyM [NAtom])
splitAtoms scope atoms
  | all isNVar atoms = (atoms, return)
  | otherwise        = (map NVar vs, reconstruct)
  where
    isNVar x = case x of NVar _ -> True; _ -> False
    vs = envNames $ envIntersect scope (foldMap freeVars atoms)
    reconstruct xs = dropSub $ extendSub env $ mapM nSubstSimp atoms
      where env = fold [v@>L x | (v,x) <- zip vs xs]

simplifyMat :: NExpr -> SimplifyM NExpr
simplifyMat expr = do
  xs <- simplify expr
  liftM NAtoms $ mapM materializeAtom xs

extendSub :: SimpSubEnv -> SimplifyM a -> SimplifyM a
extendSub env m = local (\r -> r { subEnv = subEnv r <> env }) m

dropSub :: SimplifyM a -> SimplifyM a
dropSub m = local (\r -> r {subEnv = mempty}) m

-- simplifies bodies of first-order functions only
simplifyLam :: NAtom -> SimplifyM ([NBinder], NExpr)
simplifyLam f = do
  ~(NLam l bs body) <- simplifyAtom f
  bs' <- mapM nSubstSimp bs
  ~(NLam _ bs'' body') <- buildNLam l bs' $ \vs ->
                            extendSub (bindEnv bs' vs) $ do
                              body' <- simplify body
                              body'' <- mapM materializeAtom body'
                              return $ NAtoms body''
  return (bs'', body')

simplifyAtom :: NAtom -> SimplifyM NAtom
simplifyAtom atom = case atom of
  NLit x -> return $ NLit x
  NVar v -> do
    x <- asks $ flip envLookup v . subEnv
    case x of
      Nothing -> return $ NVar v
      -- is this freshening necessary here?
      Just (L x') -> dropSub (simplifyAtom x')
      Just (T _ ) -> error "Expected let-bound var"
  NGet e i -> do
    e' <- simplifyAtom e
    i' <- simplifyAtom i
    return $ nGet e' i'
  NAtomicFor ib body -> do
    ib' <- nSubstSimp ib
    buildNAtomicFor ib' $ \i ->
      extendSub (bindEnv [ib'] [i]) (simplifyAtom body)
  NLam _ _ _ -> nSubstSimp atom

simplifyDecl :: NDecl -> SimplifyM SimpEnv
simplifyDecl decl = case decl of
  NLet bs bound -> do
    xs <- simplify bound
    return $ mempty {subEnv = bindEnv bs xs}
  NUnpack bs tv bound -> do
    bound' <- simplify bound
    ~(NTypeVar tv', emitUnpackRest) <- emitUnpack tv (NAtoms bound')
    let tEnv = tv @> T tv'
    bs' <- extendSub tEnv $ mapM nSubstSimp bs
    xs <- emitUnpackRest bs'
    return $ mempty {subEnv = tEnv <> bindEnv bs' xs}

bindEnv :: [BinderP c] -> [a] -> FullEnv a b
bindEnv bs xs = fold $ zipWith f bs xs
  where f (v:>_) x = v @> L x

nSubstSimp :: (MonadCat NEmbedEnv m, MonadReader SimpEnv m, NSubst a) => a -> m a
nSubstSimp x = do
  env <- asks subEnv
  scope <- looks fst  -- do we have to reach into the embedding monad this way?
  return $ nSubst (env, fmap (const ()) scope) x

-- === linearization ===

type TangentM a = ReaderT (Env NAtom) (NEmbedT (Either Err)) a

runLinearization :: [NBinder] -> [NAtom] -> NExpr -> SimplifyM NExpr
runLinearization bs xs expr = do
  (ans, f) <- extendSub (bindEnv bs xs) $ linearize expr
  ans' <- emit ans
  f' <- runTangent bs f
  -- TODO: check type here, especially linearity
  return $ NAtoms $ ans' ++ [f']

runTangent :: [NBinder] -> TangentM NExpr -> SimplifyM NAtom
runTangent bs m = buildNLam Lin bs $ \ts ->
                    withReaderT (const $ bindEnvTangent bs ts) m

bindEnvTangent :: [NBinder] -> [NAtom] -> Env NAtom
bindEnvTangent bs xs = fold $ zipWith f bs xs
  where f (v:>_) x = v @> x

linearize :: NExpr -> SimplifyM (NExpr, TangentM NExpr)
linearize expr = case expr of
  NDecl decl body -> do
    (env, makeTangentEnv) <- linearizeDecl decl
    (ans, fLin) <- extendSub env (linearize body)
    return (ans, do tEnv <- makeTangentEnv
                    extendR tEnv fLin)
  -- TODO: handle non-real carry components
  NScan ib bs xs e -> do
    (xs', xsTangents) <- linearizeAtoms xs
    envBs <- getContinuousVars expr
    expr' <- buildNScan ib bs xs' $ \i xs'' -> do
      extendSub (bindEnv (ib:bs) (i:xs'')) $ do
        (ans, f) <- linearize e
        ans' <- emit ans
        f' <- runTangent (envBs ++ bs) f
        return $ NAtoms $ ans' ++  [f']
    (ans, fs) <- liftM splitLast $ emit expr'
    let tangentComputation = do
          tsEnv <- mapM (lookupTangent . binderVar) envBs
          tsCarryInit <- xsTangents
          buildNScan ib bs tsCarryInit $ \i' tsCarry ->
            return $ NApp (NGet fs i') (tsEnv ++ tsCarry)
    return (NAtoms ans, tangentComputation)
  NApp (NVar v) xs -> do
    linRule <- do
      maybeRule <- asks $ flip envLookup v . derivEnv
      case maybeRule of
        Nothing -> throw NotImplementedErr $ " linearization for " ++ pprint v
        Just rule -> deShadow rule
    (xs', xsTangents) <- linearizeAtoms xs
    ~(f:ys) <- liftM reverse $ emit $ NApp linRule xs'
    return (NAtoms ys, do ts <- xsTangents
                          return $ NApp f ts)
  NApp _ _      -> error $ "Shouldn't have NApp left: " ++ pprint expr
  NPrimOp b tys xs -> do
    (xs', xsTangents) <- linearizeAtoms xs
    let (ans, f) = linearizeBuiltin b tys xs'
    return (ans, xsTangents >>= f)
  NAtoms xs -> do
    (xs', tangents) <- linearizeAtoms xs
    return (NAtoms xs', liftM NAtoms tangents)
  NTabCon _ _ _ -> error "not implemented"

linearizeDecl :: NDecl -> SimplifyM (SimpSubEnv, TangentM (Env NAtom))
linearizeDecl decl = case decl of
  NLet bs bound -> do
    bs' <- mapM nSubstSimp bs
    (xs, fLin) <- linearize bound
    xs' <- emitTo bs' xs
    return (bindEnv bs' xs', do ts <- fLin
                                ts' <- emitTo bs' ts
                                return (bindEnvTangent bs' ts'))
  _ -> error "Not implemented"

linearizeAtoms :: [NAtom] -> SimplifyM ([NAtom], TangentM [NAtom])
linearizeAtoms xs = do
  (xs', tangents) <- liftM unzip $ mapM linearizeAtom xs
  return (xs', sequence tangents)

linearizeAtom :: NAtom -> SimplifyM (NAtom, TangentM NAtom)
linearizeAtom atom = case atom of
  NLit _ -> zeroDeriv atom
  NVar v -> do
    maybeVal <- asks $ flip envLookup v . subEnv
    case maybeVal of
      Just (L x) -> return (x, lookupTangent v)
      Nothing -> zeroDeriv atom
      _ -> error "unexpected lookup"
  NGet x i -> do
    (x', xt) <- linearizeAtom x
    (i', _) <- linearizeAtom i
    return (NGet x' i', liftM (flip NGet i') xt)
  NAtomicFor _ _ -> error "not implemented"
  NLam _ _ _     -> error "not implemented"

zeroDeriv :: NAtom -> SimplifyM (NAtom, TangentM NAtom)
zeroDeriv x = do
  ~[xTy] <- askType (NAtoms [x])
  return (x, zeroAt xTy)

linearizeBuiltin :: MonadCat NEmbedEnv m =>
    Builtin -> [[NType]] -> [NAtom] -> (NExpr, [NAtom] -> m NExpr)
linearizeBuiltin op tys xs | nLin == nArgs = (NPrimOp op tys xs, f)
  where
    BuiltinType _ (nLin, prodKind) xTys outTy = builtinType op
    outsTy = typeToNTypes outTy
    nArgs = length xTys
    f ts = case prodKind of
             Cart -> return $ NPrimOp op tys ts
             Tens -> sumsAt outsTy [NPrimOp op tys (swapAt i t xs)
                                   | (i, t) <- zip [0..] ts]
linearizeBuiltin FDiv _ [x, y] = (NPrimOp FDiv [] [x, y],
                                  \[tx, ty] -> do t <- linearizedDiv x y tx ty
                                                  return $ NAtoms [t])
linearizeBuiltin op _ _ = error $ "Not implemented: linearization for: " ++ pprint op

linearizedDiv :: MonadCat NEmbedEnv m =>
                   NAtom -> NAtom -> NAtom -> NAtom -> m NAtom
linearizedDiv x y tx ty = do
  tx'  <- div' tx y
  ty'  <- mul ty x
  ySq  <- mul y y
  ty'' <- div' ty' ySq >>= neg
  add tx' ty''

lookupTangent :: Name -> TangentM NAtom
lookupTangent v = asks (!v)

getContinuousVars :: NExpr -> SimplifyM [NBinder]
getContinuousVars expr = do
  let vs = [v | (v, L ()) <- envPairs $ freeVars expr]
  tys <- mapM (\v -> nSubstSimp (NVar v) >>= askAtomType) vs
  return $ filter (isContinuous . binderAnn) $ zipWith (:>) vs tys

isContinuous :: NType -> Bool
isContinuous ty = case ty of
  NBaseType RealType -> True
  NTabType _ a       -> isContinuous a
  NExists _          -> error "Not implemented"
  _                  -> False

splitLast :: [a] -> ([a], a)
splitLast xs = case reverse xs of x:xs' -> (reverse xs', x)
                                  _ -> error "list must be nonempty"

-- === transposition ===

type LinVars = Env NType
type CotangentVals = MonMap Name [NAtom]  -- TODO: consider folding as we go
type TransposeM a = WriterT CotangentVals
                      (ReaderT (LinVars, SimpSubEnv) (NEmbedT (Either Err))) a

runTransposition :: [NBinder] -> [NAtom] -> NExpr -> SimplifyM NExpr
runTransposition bs cts expr = do
  (((), cts'), _) <- lift $ flip runReaderT (asFst (bindFold bs)) $ runWriterT $
                        extractCTs bs $ transpose expr cts
  return $ NAtoms cts'

transpose :: NExpr -> [NAtom] -> TransposeM ()
transpose expr cts = case expr of
  NPrimOp b tys xs -> do
    -- TODO: subst types
    xs' <- mapM substNonLin xs
    cts' <- transposeBuiltin b tys xs' cts
    sequence_ [transposeAtom x ct | (x, Just ct) <- zip xs cts']
  NScan ib bs xs e -> do
    ib' <- substTranspose ib
    linVars <- asks fst
    let (carryCTs, ysCTs) = splitCarry cts
    let (envVs, envTys) = unzip $ envPairs $ freeVars e `envIntersect` linVars
    initAccum <- mapM zeroAt envTys  -- TODO: need to subst type?
    let accumBinders = zipWith (:>) envVs envTys
    let bs' = bs ++ accumBinders
    let xs' = carryCTs ++ initAccum
    transposed <- buildNScan ("i":> binderAnn ib') bs' xs' $ \i c -> do
      i' <- flipIdx i
      let (carryCTsIn, accumIn) = splitCarry c
      ((), cts') <- extractCTs bs' $ extendR (bindFold bs, bindEnv [ib] [i']) $
                        transpose e $ carryCTsIn ++ map (flip nGet i') ysCTs
      let (carryCTsOut, ysCTs') = splitCarry cts'
      accumOut <- sequence $ zipWith3 addAt envTys accumIn ysCTs'
      return $ NAtoms $ carryCTsOut ++ accumOut
    cts' <- emit transposed
    let (carryCTs', ysCTs') = splitCarry cts'
    zipWithM_ emitCT envVs ysCTs'
    zipWithM_ transposeAtom xs carryCTs'
    where splitCarry = splitAt (length bs)
  NDecl (NLet bs bound) body -> do
    maybeExpr <- substNonLin bound
    case maybeExpr of
      Nothing -> do
        let env = asFst (bindFold bs)
        (_, cts') <- extractCTs bs $ extendR env $ transpose body cts
        transpose bound cts'
      Just bound' -> do
        xs <- emitTo bs bound'
        extendR (asSnd (bindEnv bs xs)) $ transpose body cts
  NAtoms xs -> zipWithM_ transposeAtom xs cts
  _ -> error $ "Transpose not implemented for " ++ pprint expr

isLin :: HasVars a => a -> TransposeM Bool
isLin x = do linVs <- asks fst
             return $ not $ null $ toList $ envIntersect (freeVars x) linVs

emitCT :: Name -> NAtom -> TransposeM ()
emitCT v ct = tell $ MonMap $ M.singleton v [ct]

substNonLin ::  (HasVars a, NSubst a) => a -> TransposeM (Maybe a)
substNonLin x = do
  x' <- substTranspose x
  lin <- isLin x'
  if lin then return Nothing
         else return (Just x')

substTranspose :: NSubst a => a -> TransposeM a
substTranspose x = do
  env <- asks snd
  scope <- looks fst
  return $ nSubst (env, fmap (const ()) scope) x

transposeAtom :: NAtom -> NAtom -> TransposeM ()
transposeAtom atom ct = case atom of
  NLit _ -> return ()
  NVar v -> emitCT v ct
  NGet x i -> do
    i' <- substTranspose i
    ct' <- oneHot i' ct
    transposeAtom x ct'
  _ -> error $ "Can't transpose: " ++ pprint atom

oneHot :: NAtom -> NAtom -> TransposeM NAtom
oneHot i x = do
  n   <- askAtomType i
  xTy <- askAtomType x
  zero <- zeroAt xTy
  expr <- buildNScan ("i" :> n) [] [] $ \i' _ -> do
    ~[eq] <- emit $ NPrimOp (Cmp Equal) [[n]] [i, i']
    liftM NAtoms $ emit $ NPrimOp Select [[xTy]] [eq, x, zero]
  ~[oneHotAtom] <- emit expr
  return oneHotAtom

transposeBuiltin :: MonadCat NEmbedEnv m =>
    Builtin -> [[NType]] -> [Maybe NAtom] -> [NAtom] -> m [Maybe NAtom]
transposeBuiltin op _ xs cts = case op of
  FAdd -> return [Just ct, Just ct]
  FMul -> case xs of
    [Just x , Nothing] -> do { ans <- mul x  ct ; return [Nothing , Just ans] }
    [Nothing, Just y ] -> do { ans <- mul ct y  ; return [Just ans, Nothing ] }
    _ -> error $ "Can't transpose: " ++ pprint (op, xs)
  FSub -> do
    negCt <- neg ct
    return [Just ct, Just negCt]
  FDiv -> do
    let [_ , Just y] = xs
    ctAns <- div' ct y
    return [Just ctAns, Nothing]
  FNeg -> do
    ctAns <- neg ct
    return [Just ctAns]
  _ -> error $ "Not implemented: transposition for: " ++ pprint op
  where [ct] = cts

extractCTs :: [NBinder] -> TransposeM a -> TransposeM (a, [NAtom])
extractCTs bs m = do
  (ans, ctEnv) <- captureW m
  (cts, ctEnv') <- sepCotangents bs ctEnv
  tell ctEnv'
  return (ans, cts)

sepCotangent :: MonadCat NEmbedEnv m =>
                  NBinder -> CotangentVals -> m (NAtom, CotangentVals)
sepCotangent (v:>ty) (MonMap m) = do
  ans <- sumAt ty $ M.findWithDefault [] v m
  return (ans, MonMap (M.delete v m))

sepCotangents :: MonadCat NEmbedEnv m =>
                   [NBinder] -> CotangentVals -> m ([NAtom], CotangentVals)
sepCotangents [] cts = return ([], cts)
sepCotangents (b:bs) cts = do
  (x , cts' ) <- sepCotangent  b  cts
  (xs, cts'') <- sepCotangents bs cts'
  return (x:xs, cts'')

-- === misc ===

instance Semigroup SimpEnv where
  SimpEnv x1 x2 <> SimpEnv y1 y2  = SimpEnv (x1 <> y1) (x2 <> y2)

instance Monoid SimpEnv where
  mempty = SimpEnv mempty mempty
  mappend = (<>)
