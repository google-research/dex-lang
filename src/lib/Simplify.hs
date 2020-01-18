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
import Record

type SimpSubEnv = FullEnv NAtom Name
type DerivRuleEnv = Env NAtom

data SimpEnv = SimpEnv { subEnv   :: SimpSubEnv
                       , derivEnv :: DerivRuleEnv }

type SimpTopEnv = (SimpEnv, Scope)
type SimplifyM a = ReaderT SimpEnv (NEmbedT (Either Err)) a

derivPass :: TopPass NTopDecl NTopDecl
derivPass = TopPass $ \topDecl -> case topDecl of
  NTopDecl PlainDecl decl -> simplifyDeclTop decl
  NTopDecl ADPrimitive decl -> do
    let NLet (v:>_) _ = decl
    decl' <- liftTopNoDecl $ nSubstSimp decl
    extend $ asSnd $ v@>()
    return [NTopDecl PlainDecl decl']
  NRuleDef (LinearizationDef v) _ ~(NAtom f) -> do
    f' <- liftTopNoDecl $ nSubstSimp f
    extend $ asFst $ mempty {derivEnv = v @> f' }
    emitOutput $ NoOutput
  NEvalCmd (Command cmd (ty, expr)) -> do
    expr' <- liftTopNoDecl $ buildScoped $ simplifyMat expr
    case cmd of
      ShowDeriv -> emitOutput $ TextOut $ pprint expr'
      _ -> return [NEvalCmd (Command cmd (ty, expr'))]

simpPass :: TopPass NTopDecl NTopDecl
simpPass = TopPass $ \topDecl -> case topDecl of
  NTopDecl _ decl -> simplifyDeclTop decl
  NRuleDef _ _ _ -> error "Shouldn't have derivative rules left"
  NEvalCmd (Command cmd (ty, expr)) -> do
    expr' <- liftTopNoDecl $ buildScoped $ simplifyMat expr
    case cmd of
      ShowSimp -> emitOutput $ TextOut $ pprint expr'
      _ -> return [NEvalCmd (Command cmd (ty, expr'))]

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
  NLet (v:>_) bound -> do
    (x, (scope, decls)) <- scoped $ simplify bound
    let (xClosure, reconstruct) = splitAtom scope x
    xClosure' <- emitNamed v $ wrapNDecls decls (NAtom xClosure)
    x' <- reconstruct xClosure'
    return $ mempty { subEnv = v @>L x' }
  NUnpack b@(v:>_) tv bound -> do
    bound' <- buildScoped $ simplifyMat bound
    ~(TypeVar tv', emitUnpackRest) <- emitUnpack tv bound'
    let tEnv = tv @> T tv'
    b' <- extendSub tEnv $ nSubstSimp b
    x <- emitUnpackRest b'
    return $ mempty {subEnv = tEnv <> v @> L x}

-- Simplification gives us a ([NDecl], NAtom) pair. The decls are fully
-- simplified: no `NLam`, `NAtomicFor` or differentiation operations. The atom
-- isn't: e.g. a lambda that can't be beta-reduced yet.
simplify :: NExpr -> SimplifyM NAtom
simplify expr = case expr of
  NDecl decl body -> do
    env <- simplifyDecl decl
    extendR env $ simplify body
  NScan x (NLamExpr ~[ib,b] e) -> do
    x' <- simplifyAtom x >>= materializeAtom
    ib' <- nSubstSimp ib
    b'  <- nSubstSimp b
    ((cOut, yOut), ~[ib''@(i:>n), b''], (scope, decls)) <-
        withBinders [ib', b'] $ \[i, carry] ->
           extendSub (bindEnv [ib', b'] [i, carry]) $ do
             (cOut, yOut) <- (simplify >=> fromPair) e
             cOut' <- materializeAtom cOut
             return (cOut', yOut)
    let (yClosure, reconstruct) = splitAtom (envDelete i scope) yOut
    ans <- emit $ NScan x' $ NLamExpr [ib'',b''] $
             wrapNDecls decls $ NAtom $ makePair cOut yClosure
    (cOut', yClosure') <- fromPair ans
    yOut' <- buildNAtomicFor ib'' $ \i -> do
       yClosure'' <- nGet yClosure' i
       liftM NAtom $ reconstruct yClosure''
    return $ makePair cOut' yOut'
  NApp f x -> do
    x' <- simplifyAtom x
    f' <- simplifyAtom f
    case f' of
      NLam _ (NLamExpr ~[b] body) -> dropSub $ extendSub (bindEnvSingle b x') $ simplify body
      _                           -> emit $ NApp f' x'
  NPrimOp Linearize _ ~[f,x] -> do
    ~(NLam _ lam) <- simplifyAtom f
    lam' <- simplifyLam lam
    x'   <- simplifyAtom x
    dropSub $ do
      linearized <- buildScoped $ runLinearization x' lam'
      simplify linearized
  NPrimOp Transpose [_, ty] ~[f] -> do
    ~(NLam _ lam) <- simplifyAtom f
    lam' <- simplifyLam lam
    ty' <- nSubstSimp ty
    transposed <- buildNLam ["ct":>ty'] $ \[ct] ->
                    dropSub $ runTransposition ct lam'
    return $ NLam (Mult Lin) transposed
  NPrimOp b ts xs -> do
    ts' <- mapM nSubstSimp ts
    xs' <- mapM (simplifyAtom >=> materializeAtom) xs
    emit $ NPrimOp b ts' xs'
  NRecGet x i -> do
    x' <- simplifyAtom x
    nRecGet x' i
  NAtom x -> simplifyAtom x
  NTabCon n ts rows -> do
    n' <- nSubstSimp n
    t' <- nSubstSimp ts
    xs' <- mapM (simplifyAtom >=> materializeAtom) rows
    emit $ NTabCon n' t' xs'

-- As we prepare to leave a scope (say that of `NScan`) we save the variables
-- we'll no longer have access to once we've left, along with a function that
-- can reconstruct the atom (e.g. lambdas) on the other side.
splitAtom :: Scope -> NAtom -> (NAtom, NAtom -> SimplifyM NAtom)
splitAtom scope atom
  | isNVar atom = (atom, return) -- TODO: what's the equivalent in a tuply world?
  | otherwise   = (xsSaved, reconstruct)
  where
    isNVar x = case x of NVar _ _-> True; _ -> False
    vsTys = envPairs $ envIntersect scope (freeVars atom)
    xsSaved = NRecCon Cart $ Tup [NVar v ty | (v, L ty) <- vsTys]
    reconstruct x = dropSub $ do
                      xs' <- fromTup x
                      let env = fold [v@>L x' | ((v,_),x') <- zip vsTys xs']
                      extendSub env $ nSubstSimp atom

simplifyMat :: NExpr -> SimplifyM NExpr
simplifyMat expr = do
  x <- simplify expr
  liftM NAtom $ materializeAtom x

extendSub :: SimpSubEnv -> SimplifyM a -> SimplifyM a
extendSub env m = local (\r -> r { subEnv = subEnv r <> env }) m

dropSub :: SimplifyM a -> SimplifyM a
dropSub m = local (\r -> r {subEnv = mempty}) m

-- Simplifies bodies of first-order functions only.
-- Unlike `SimplifyAtom`, the simplifies under the binder too.
simplifyLam :: NLamExpr -> SimplifyM NLamExpr
simplifyLam (NLamExpr bs body) = do
  bs' <- mapM nSubstSimp bs
  buildNLam bs' $ \vs ->
    extendSub (bindEnv bs' vs) $ do
      body'  <- simplify body >>= materializeAtom
      return $ NAtom body'

simplifyAtom :: NAtom -> SimplifyM NAtom
simplifyAtom atom = case atom of
  NLit x -> return $ NLit x
  NVar v ty -> do
    ty' <- nSubstSimp ty
    x <- asks $ flip envLookup v . subEnv
    case x of
      Nothing -> return $ NVar v ty'
      -- is this freshening necessary here?
      Just (L x') -> dropSub (simplifyAtom x')
      Just (T _ ) -> error "Expected let-bound var"
  NGet e i -> do
    e' <- simplifyAtom e
    i' <- simplifyAtom i
    nGet e' i'
  NAtomicFor ib body -> do
    ib' <- nSubstSimp ib
    buildNAtomicFor ib' $ \i ->
      liftM NAtom $ extendSub (bindEnvSingle ib' i) (simplify body)
  NLam _ _ -> nSubstSimp atom
  NRecCon k r -> liftM (NRecCon k) (traverse simplifyAtom r)
  NDoBind m f -> liftM2 NDoBind (simplifyAtom m) (simplifyLam f)
  NAtomicPrimOp b ts xs -> do
    ts' <- mapM nSubstSimp ts
    xs' <- mapM (simplifyAtom >=> materializeAtom) xs
    return $ NAtomicPrimOp b ts' xs'

simplifyDecl :: NDecl -> SimplifyM SimpEnv
simplifyDecl decl = case decl of
  NLet b bound -> do
    xs <- simplify bound
    return $ mempty {subEnv = bindEnvSingle b xs}
  NUnpack b tv bound -> do
    bound' <- simplify bound
    ~(TypeVar tv', emitUnpackRest) <- emitUnpack tv (NAtom bound')
    let tEnv = tv @> T tv'
    b' <- extendSub tEnv $ nSubstSimp b
    x <- emitUnpackRest b'
    return $ mempty {subEnv = tEnv <> bindEnvSingle b' x}

bindEnv :: [BinderP c] -> [a] -> FullEnv a b
bindEnv bs xs = fold [v @> L x | (v:>_,x) <- zip bs xs]

bindEnvSingle :: BinderP c -> a -> FullEnv a b
bindEnvSingle (v:>_) x = v @> L x

nSubstSimp :: (MonadCat NEmbedEnv m, MonadReader SimpEnv m, NSubst a) => a -> m a
nSubstSimp x = do
  env <- asks subEnv
  scope <- looks fst  -- do we have to reach into the embedding monad this way?
  return $ nSubst (env, scope) x

-- === linearization ===

type TangentM a = ReaderT (Env NAtom) (NEmbedT (Either Err)) a

runLinearization :: NAtom -> NLamExpr -> SimplifyM NExpr
runLinearization x (NLamExpr ~[b] expr) = do
  (ans, f) <- extendSub (bindEnvSingle b x) $ linearize expr
  ans' <- emit ans
  f' <- runTangent b f
  -- TODO: check type here, especially linearity
  return $ NAtom $ NRecCon Cart (Tup [ans', f'])

runTangent :: NBinder -> TangentM NExpr -> SimplifyM NAtom
runTangent b m = liftM (NLam (Mult Lin)) $ buildNLam [b] $ \[t] ->
                    withReaderT (const $ bindEnvTangent b t) m

bindEnvTangent :: NBinder -> NAtom -> Env NAtom
bindEnvTangent (v:>_) x = v @> x

linearize :: NExpr -> SimplifyM (NExpr, TangentM NExpr)
linearize expr = case expr of
  NDecl decl body -> do
    (env, makeTangentEnv) <- linearizeDecl decl
    (ans, fLin) <- extendSub env (linearize body)
    return (ans, do tEnv <- makeTangentEnv
                    extendR tEnv fLin)
  -- TODO: handle non-real carry components
  -- NScan x (NLamExpr ~(ib:bs) e) -> do
  --   (x', xTangents) <- linearizeAtom x
  --   envBs <- getContinuousVars expr
  --   expr' <- buildNScan ib bs x' $ \i x'' -> do
  --     extendSub (bindEnv (ib:bs) (i:x'')) $ do
  --       (ans, f) <- linearize e
  --       ans' <- emit ans
  --       f' <- runTangent (envBs ++ bs) f
  --       return $ NTupCon [ans', f']
  --   (ans, fs) <- liftM splitLast $ emit expr'
  --   let tangentComputation = do
  --         tsEnv <- mapM (lookupTangent . binderVar) envBs
  --         tsCarryInit <- xTangents
  --         buildNScan ib bs tsCarryInit $ \i' tsCarry ->
  --           return $ NApp (NGet fs i') (tsEnv ++ tsCarry)
  --   return (NAtoms ans, tangentComputation)
  -- NApp (NVar v _) x -> do
  --   linRule <- do
  --     maybeRule <- asks $ flip envLookup v . derivEnv
  --     case maybeRule of
  --       Nothing -> throw NotImplementedErr $ " linearization for " ++ pprint v
  --       Just rule -> deShadow rule
  --   (x', xTangents) <- linearizeAtom x
  --   ~(f:ys) <- liftM reverse $ emit $ NApp linRule x'
  --   return (NAtoms ys, do ts <- xTangents
  --                         return $ NApp f ts)
  NApp _ _      -> error $ "Shouldn't have NApp left: " ++ pprint expr
  NPrimOp b tys xs -> do
    (xs', xsTangents) <- mapLinearize linearizeAtom xs
    let (ans, f) = linearizeBuiltin b tys xs'
    return (ans, xsTangents >>= f)
  NAtom x -> do
    (x', tangents) <- linearizeAtom x
    return (NAtom x', liftM NAtom tangents)
  NTabCon _ _ _ -> error "not implemented"

linearizeDecl :: NDecl -> SimplifyM (SimpSubEnv, TangentM (Env NAtom))
linearizeDecl decl = case decl of
  NLet b bound -> do
    b' <- nSubstSimp b
    (x, fLin) <- linearize bound
    x' <- emitTo b' x
    return (bindEnvSingle b' x',
            do t <- fLin
               t' <- emitTo b' t
               return (bindEnvTangent b' t'))
  _ -> error "Not implemented"

mapLinearize :: (a -> SimplifyM (a, TangentM a))
             -> [a] -> SimplifyM ([a], TangentM [a])
mapLinearize f xs = do
  (xs', tangents) <- liftM unzip $ mapM f xs
  return (xs', sequence tangents)

linearizeAtom :: NAtom -> SimplifyM (NAtom, TangentM NAtom)
linearizeAtom atom = case atom of
  NLit _ -> return $ zeroDeriv atom
  NVar v _ -> do
    maybeVal <- asks $ flip envLookup v . subEnv
    case maybeVal of
      Just (L x) -> return (x, lookupTangent v)
      Nothing -> return $ zeroDeriv atom
      _ -> error "unexpected lookup"
  NGet x i -> do
    (x', xt) <- linearizeAtom x
    (i', _) <- linearizeAtom i
    return (NGet x' i', liftM (flip NGet i') xt)
  _ -> error $ "not implemented: " ++ pprint atom
-- === tuple case: ===
-- linearizeAtom :: [NAtom] -> SimplifyM ([NAtom], TangentM [NAtom])
-- linearizeAtom xs = do
--   (xs', tangents) <- liftM unzip $ mapM linearizeAtom xs
--   return (xs', sequence tangents)


zeroDeriv :: NAtom -> (NAtom, TangentM NAtom)
zeroDeriv x = (x, zeroAt (atomType x))

linearizeBuiltin :: MonadCat NEmbedEnv m
                 => Builtin -> [Type] -> [NAtom] -> (NExpr, [NAtom] -> m NExpr)
-- linearizeBuiltin op tys xs | isLinear = (NPrimOp op tys xs, f)
--   where
--     (_, outsTy, linSpec) = ignoreExcept $ nBuiltinType op tys
--     isLinear = all (\l -> case fst l of Lin    -> True
--                                         NonLin -> False) linSpec
--     xs' = map snd $ splitLinArgs linSpec xs
--     f ts = sumsAt outsTy [NPrimOp op tys $ concat $ swapAt i t xs'
--                          | (i, t) <- zip [0..] ts']
--              where ts' = map snd $ splitLinArgs linSpec ts
-- linearizeBuiltin FDiv _ [x, y] = (NPrimOp FDiv [] [x, y],
--                                   \[tx, ty] -> do t <- linearizedDiv x y tx ty
--                                                   return $ NAtoms [t])
linearizeBuiltin op _ _ = error $ "Not implemented: linearization for: " ++ pprint op

linearizedDiv :: MonadCat NEmbedEnv m
              => NAtom -> NAtom -> NAtom -> NAtom -> m NAtom
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
  let bs = [v:>ty | (v, L ty) <- envPairs $ freeVars expr]
  return $ filter (isContinuous . binderAnn) bs

isContinuous :: Type -> Bool
isContinuous ty = case ty of
  BaseType RealType -> True
  TabType _ a       -> isContinuous a
  Exists _          -> error "Not implemented"
  _                  -> False

splitLast :: [a] -> ([a], a)
splitLast xs = case reverse xs of x:xs' -> (reverse xs', x)
                                  _ -> error "list must be nonempty"

-- === transposition ===

type LinVars = Env Type
type CotangentVals = MonMap Name [NAtom]  -- TODO: consider folding as we go
type TransposeM a = WriterT CotangentVals
                      (ReaderT (LinVars, SimpSubEnv) (NEmbedT (Either Err))) a

runTransposition :: NAtom -> NLamExpr -> SimplifyM NExpr
runTransposition ct (NLamExpr ~[b] expr) = do
  (((), ct'), _) <- lift $ flip runReaderT (asFst (bind b)) $ runWriterT $
                        extractCT b $ transpose expr ct
  return $ NAtom ct'

transpose :: NExpr -> NAtom -> TransposeM ()
transpose expr ct = case expr of
  NPrimOp b tys xs -> do
    -- TODO: subst types
    xs' <- mapM substNonLin xs
    cts' <- transposeBuiltin b tys xs' ct
    sequence_ [transposeAtom x ct | (x, Just ct) <- zip xs cts']
  -- NScan xs (NLamExpr (ib:bs) e) -> do
  --   ib' <- substTranspose ib
  --   linVars <- asks fst
  --   let (carryCT, ysCT) = splitCarry cts
  --   let (envVs, envTys) = unzip $ envPairs $ freeVars e `envIntersect` linVars
  --   initAccum <- mapM zeroAt envTys  -- TODO: need to subst type?
  --   let accumBinders = zipWith (:>) envVs envTys
  --   let bs' = bs ++ accumBinders
  --   let xs' = carryCT ++ initAccum
  --   transposed <- buildNScan ("i":> binderAnn ib') bs' xs' $ \i c -> do
  --     i' <- flipIdx i
  --     let (carryCTIn, accumIn) = splitCarry c
  --     ((), cts') <- extractCT bs' $ extendR (bindFold bs, bindEnv [ib] [i']) $
  --                       transpose e $ carryCTIn ++ map (flip nGet i') ysCT
  --     let (carryCTOut, ysCT') = splitCarry cts'
  --     accumOut <- sequence $ zipWith3 addAt envTys accumIn ysCT'
  --     return $ NAtoms $ carryCTOut ++ accumOut
  --   cts' <- emit transposed
  --   let (carryCT', ysCT') = splitCarry cts'
  --   zipWithM_ emitCT envVs ysCT'
  --   zipWithM_ transposeAtom xs carryCT'
  --   where splitCarry = splitAt (length bs)
  NDecl (NLet b bound) body -> do
    maybeExpr <- substNonLin bound
    case maybeExpr of
      Nothing -> do
        let env = asFst (bind b)
        (_, ct') <- extractCT b $ extendR env $ transpose body ct
        transpose bound ct'
      Just bound' -> do
        x <- emitTo b bound'
        extendR (asSnd (bindEnvSingle b x)) $ transpose body ct
  NAtom x -> transposeAtom x ct
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
  return $ nSubst (env, scope) x

transposeAtom :: NAtom -> NAtom -> TransposeM ()
transposeAtom atom ct = case atom of
  NLit _ -> return ()
  NVar v _ -> emitCT v ct
  NGet x i -> do
    i' <- substTranspose i
    ct' <- oneHot i' ct
    transposeAtom x ct'
  _ -> error $ "Can't transpose: " ++ pprint atom

oneHot :: NAtom -> NAtom -> TransposeM NAtom
oneHot i x = do
  let n   = atomType i
  let xTy = atomType x
  zero <- zeroAt xTy
  expr <- buildNScan ("i" :> n) ("_":>unitTy) nUnitCon $ \i' _ -> do
    eq <- emit $ NPrimOp (Cmp Equal) [n] [i, i']
    liftM NAtom $ selectAt eq xTy x zero
  emit expr

transposeBuiltin :: MonadCat NEmbedEnv m =>
    Builtin -> [Type] -> [Maybe NAtom] -> NAtom -> m [Maybe NAtom]
transposeBuiltin op _ xs ct = case op of
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

extractCT :: NBinder -> TransposeM a -> TransposeM (a, NAtom)
extractCT = undefined
-- extractCT bs m = do
--   (ans, ctEnv) <- captureW m
--   (cts, ctEnv') <- sepCotangents bs ctEnv
--   tell ctEnv'
--   return (ans, cts)

sepCotangent :: MonadCat NEmbedEnv m =>
                  NBinder -> CotangentVals -> m (NAtom, CotangentVals)
sepCotangent = undefined
-- sepCotangent (v:>ty) (MonMap m) = do
  -- ans <- sumAt ty $ M.findWithDefault [] v m
  -- return (ans, MonMap (M.delete v m))

-- sepCotangents :: MonadCat NEmbedEnv m =>
--                    [NBinder] -> CotangentVals -> m ([NAtom], CotangentVals)
-- sepCotangents [] cts = return ([], cts)
-- sepCotangents (b:bs) cts = do
--   (x , cts' ) <- sepCotangent  b  cts
--   (xs, cts'') <- sepCotangents bs cts'
--   return (x:xs, cts'')

-- === misc ===

instance Semigroup SimpEnv where
  SimpEnv x1 x2 <> SimpEnv y1 y2  = SimpEnv (x1 <> y1) (x2 <> y2)

instance Monoid SimpEnv where
  mempty = SimpEnv mempty mempty
  mappend = (<>)
