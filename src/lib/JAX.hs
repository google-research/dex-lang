-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module JAX (JAtom (..), JVar, typeToJType, jTypeToType,
            JExpr, JaxFunction, toJaxFunction, simplifyJaxFunction,
            dceJaxFunction) where

import Control.Applicative
import Control.Monad.Except hiding (Except)
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State.Strict
import Data.Aeson  hiding (Array)
import Data.Maybe
import Data.Text.Prettyprint.Doc
import GHC.Generics
import GHC.Stack

import Env
import Syntax
import PPrint
import Type
import Cat
import Record
import Array

-- === JAXish IR ===

type AxisSize = Int
type JVar   = VarP JType
type IdxVar = VarP AxisSize
data IdxFlavor = MapIdx | SumIdx            deriving (Generic, Show, Eq)

data JDecl = JLet JVar JFor                 deriving (Generic, Show, Eq)
data JExpr = JExpr [JDecl] [JAtom]          deriving (Generic, Show, Eq)
data JAtom = JLit Array | JVar JVar         deriving (Generic, Show, Eq)
data IdxAtom = IdxAtom JAtom [IdxVar]       deriving (Generic, Show, Eq)
data JType = JType [AxisSize] BaseType      deriving (Generic, Show, Eq)
data JaxFunction = JaxFunction [JVar] JExpr deriving (Generic, Show, Eq)

type JOp = JOpP IdxAtom
data JOpP e = JId e
            | JIota AxisSize
            | JGet e e
            | JScalarBinOp ScalarBinOp e e
            | JThreeFry2x32 e e
            | JScalarUnOp  ScalarUnOp e
              deriving (Generic, Functor, Foldable, Traversable, Show, Eq)

data TmpAtom = TmpLeaf IdxAtom
             | TmpRefName Var
             | TmpCon (PrimCon TmpAtom)
               deriving (Generic, Show, Eq)

data JFor = JFor [(IdxVar, IdxFlavor)] (JOpP IdxAtom)
            deriving (Generic, Show, Eq)

type JScope = Env ()  -- TODO: put bindings here too

-- === lowering from Expr ===

type JEmbedEnv = (JScope, [JDecl])
type JSubstEnv = Env TmpAtom
type EffectState = Env (Int, TmpAtom)
type IdxEnv = [IdxVar]  -- for i j. --> [i, j]
type JaxM = ReaderT IdxEnv (StateT EffectState (Cat JEmbedEnv))

runJaxM :: JaxM a -> a
runJaxM m = fst $ flip runCat mempty $
  flip evalStateT mempty $ flip runReaderT mempty m

toJaxFunction :: ([Var], Block) -> JaxFunction
toJaxFunction (vs, block) = runJaxM $ do
  vs' <- mapM freshVar vs
  let env = newEnv vs $ map varToTmpAtom vs
  (result, (_, decls)) <- scoped $ do
    result <- toJaxBlock env block
    return $ flattenAtom result
  let jvs = map (fmap typeToJType) vs'
  return $ JaxFunction jvs $ JExpr decls result

varToTmpAtom :: Var -> TmpAtom
varToTmpAtom v = TmpLeaf $ IdxAtom (JVar $ fmap typeToJType v) []

flattenAtom :: TmpAtom -> [JAtom]
flattenAtom atom =
  execWriter $ traverseArrayLeaves atom $ \(IdxAtom x []) -> do
    tell [x]
    return $ IdxAtom x []

toJaxBlock :: JSubstEnv -> Block -> JaxM TmpAtom
toJaxBlock env (Block [] result) = toJaxExpr env result
toJaxBlock env (Block (decl:decls) result) = do
  env' <- toJaxDecl env decl
  toJaxBlock (env <> env') body
  where body = Block decls result

toJaxDecl :: JSubstEnv -> Decl -> JaxM JSubstEnv
toJaxDecl env (Let v rhs) = do
  ans <- toJaxExpr env rhs
  return $ v @> ans

toJaxAtom :: JSubstEnv -> Atom -> TmpAtom
toJaxAtom env atom = case atom of
  Var v@(_:>RefTy _ _) -> TmpRefName v
  Var v -> fromMaybe (error "lookup failed") $ envLookup env v
  Con (Lit x) -> tmpAtomScalarLit x
  Con con -> TmpCon $ fmap (toJaxAtom env) con
  _ -> error $ "Not implemented: " ++ pprint atom

toJaxExpr :: JSubstEnv -> Expr -> JaxM TmpAtom
toJaxExpr env expr = case expr of
  -- For _ (LamExpr i@(_ :> FixedIntRange 0 n) body) -> do
  --   idxEnv <- ask
  --   -- TODO: scope this to avoid burning through names
  --   i' <-freshIdxVar n
  --   iotaVar <- emitJFor $ JFor [] $ JIota n
  --   let iotaAtom = iotaVarAsIdx (FixedIntRange 0 n) $ IdxAtom (JVar iotaVar) [i']
  --   let env' = env <> i @> iotaAtom
  --   ans <- extendR [i'] $ toJaxBlock env' body
  --   liftM (TmpCon . AFor (varAnn i)) $ traverseArrayLeaves ans $ \x -> do
  --     ansVar <- emitJFor $ JFor (map (,MapIdx) (idxEnv ++ [i'])) $ JId x
  --     return $ IdxAtom (JVar ansVar) idxEnv
  -- TabGet xs i -> do
  --   let (TmpCon (AFor _ tab)) = toJaxAtom env xs
  --   let i' = toJaxAtom env i
  --   traverseArrayLeaves tab $ \x -> emitOp $ JGet x $ fromScalarAtom i'
  Op op -> toJaxOp $ fmap (toJaxAtom env) op

toJaxOp :: PrimOp TmpAtom -> JaxM TmpAtom
toJaxOp op = case op of
  ScalarBinOp op x y -> liftM toScalarAtom $
    emitOp $ JScalarBinOp op (fromScalarAtom x) (fromScalarAtom y)
  IndexAsInt x -> liftM toScalarAtom $
    emitOp $ JId (fromScalarAtom x)
  ScalarUnOp op x -> liftM toScalarAtom $
    emitOp $ JScalarUnOp op (fromScalarAtom x)
  PrimEffect (TmpRefName refVar) m -> do
    case m of
      MTell x -> do
        (depth, curAccum) <- gets (! refVar)
        xSum <- sumPoly depth x
        newAccum <- local (take depth) $ addPoly curAccum xSum
        modify (<> refVar @> (depth, newAccum))
        return $ TmpCon $ RecCon $ Tup []
      _ -> error $ "Not implemented: " ++ show op
  RecGet x i -> do
    case x of
      TmpCon (RecCon r) -> return $ recGet r i
      val -> error $ "Expected a record, got: " ++ show val
  FFICall s _ args | s == "threefry2x32" -> liftM toScalarAtom $
      emitOp $ JThreeFry2x32 (fromScalarAtom x) (fromScalarAtom y)
        where x:y:[] = args
  _ -> error $ "Not implemented: " ++ show op

-- toJaxHof :: PrimHof TmpAtom (LamExpr, JSubstEnv) -> JaxM TmpAtom
-- toJaxHof hof = case hof of
--   RunWriter (LamExpr refVar _ body, env) -> do
--     idxEnvDepth <- asks length
--     let (RefTy wTy) = varAnn refVar
--     wInit <- zerosAt wTy
--     modify (<> refVar @> (idxEnvDepth, wInit))
--     aResult <- toJaxBlock env body
--     wFinal <- gets $ snd . (! refVar)
--     modify $ envDelete (varName refVar)
--     return $ TmpCon $ RecCon $ Tup [aResult, wFinal]
--   _ -> error $ "Not implemented: " ++ show hof

iotaVarAsIdx :: Type -> IdxAtom -> TmpAtom
iotaVarAsIdx = undefined
-- iotaVarAsIdx n x = TmpCon $ AsIdx n $ toScalarAtom x

fromScalarAtom :: HasCallStack => TmpAtom -> IdxAtom
fromScalarAtom atom = case atom of
  TmpCon (AsIdx _ x) -> fromScalarAtom x
  TmpCon (AGet (TmpLeaf x)) -> x
  _ -> error $ "Not a scalar atom: " ++ show atom

toScalarAtom :: IdxAtom -> TmpAtom
toScalarAtom x = TmpCon $ AGet $ TmpLeaf x

traverseArrayLeaves :: HasCallStack => Monad m => TmpAtom -> (IdxAtom -> m IdxAtom) -> m TmpAtom
traverseArrayLeaves atom f = case atom of
  TmpCon con         -> liftM TmpCon $ case con of
    RecCon r         -> liftM (RecCon) $ traverse (flip traverseArrayLeaves f) r
    AFor n body      -> liftM (AFor n) $ traverseArrayLeaves body f
    AGet (TmpLeaf x) -> liftM (AGet . TmpLeaf) $ f x
    _ -> error $ "Not implemented: " ++ show atom
  TmpLeaf x -> liftM TmpLeaf $ f x
  TmpRefName _ -> error "Unexpected reference name"

typeToJType :: Type -> JType
typeToJType ty = case ty of
  ArrayTy shape b -> JType shape b
  _ -> error $ "Not a jax type: " ++ pprint ty

jTypeToType :: JType -> Type
jTypeToType ty = case ty of
  JType shape b -> ArrayTy shape b

emitOp :: JOpP IdxAtom -> JaxM IdxAtom
emitOp op = do
  idxEnv <- ask
  v <- emitJFor $ JFor (map (,MapIdx) idxEnv) op
  return $ IdxAtom (JVar v) idxEnv

zerosAt :: Type -> JaxM TmpAtom
zerosAt ty = case ty of
  BaseTy RealType -> return $ tmpAtomScalarLit $ RealLit 0.0
  _ -> error "Not implemented"

addPoly :: TmpAtom -> TmpAtom -> JaxM TmpAtom
addPoly x y = case getType x of
  BaseTy RealType -> liftM toScalarAtom $
    emitOp $ JScalarBinOp FAdd (fromScalarAtom x) (fromScalarAtom y)
  ty -> error $ "Not implemented: " ++ pprint ty

sumPoly :: Int -> TmpAtom -> JaxM TmpAtom
sumPoly depth atom = do
  idxEnv <- ask
  let (forIdxs, sumIdxs) = splitAt depth idxEnv
  let idxBinders =  zip forIdxs (repeat MapIdx)
                 <> zip sumIdxs (repeat SumIdx)
  traverseArrayLeaves atom $ \x -> do
     v <- emitJFor $ JFor idxBinders $ JId x
     return $ IdxAtom (JVar v) forIdxs

tmpAtomScalarLit :: LitVal -> TmpAtom
tmpAtomScalarLit x = toScalarAtom $ IdxAtom (JLit $ arrayFromScalar x) []

instance HasType TmpAtom where
  typeCheck atom = case atom of
    TmpLeaf idxAtom -> return $ jTypeToType $ getJType idxAtom
    TmpRefName _ -> undefined
    TmpCon con -> undefined

-- === Simplification pass on JAX IR ===

type BindingEnv = Env (VarUsage, JFor)
type SimpEnv = (Env JAtom, BindingEnv)
type SimpM = Cat JEmbedEnv

pattern JForId :: JAtom -> JFor
pattern JForId x = JFor [] (JId (IdxAtom x []))

simplifyJaxFunction :: JaxFunction -> JaxFunction
simplifyJaxFunction (JaxFunction vs expr) = fst $ flip runCat mempty $ do
  vs' <- mapM freshVar vs
  let env = (newEnv vs (map JVar vs'), mempty)
  (result', (_, decls')) <- scoped $ simplifyJaxExpr env expr
  return $ JaxFunction vs' $ JExpr decls' result'

simplifyJaxExpr :: SimpEnv -> JExpr -> SimpM [JAtom]
simplifyJaxExpr env expr@(JExpr decls results) = do
  let usageEnv = collectUsage expr
  (_, env') <- flip runCatT env $ mapM (simplifyJaxDecl usageEnv) decls
  let (substEnv, _) = env <> env'
  return $ fmap (jSubst substEnv) results

simplifyJaxDecl :: UsageEnv -> JDecl -> CatT SimpEnv SimpM ()
simplifyJaxDecl usageEnv (JLet v jfor) = do
  (substEnv, bindingEnv) <- look
  let usage = lookupUse usageEnv v
  let jfor' = simpFix (simplifyJFor bindingEnv) $ jSubst substEnv jfor
  case jfor' of
    JForId x -> extend $ asFst (v @> x)
    _ -> do
      vOut <- lift $ emitJFor jfor'
      extend $ (v @> JVar vOut, vOut @> (usage, jfor'))

simplifyJFor :: BindingEnv -> JFor -> Maybe JFor
simplifyJFor env jfor@(JFor idxs op) =
       liftM (JFor idxs) (mapParallel (inlineFromId env) op)
   <|> inlineGetIota env jfor
   <|> inlineIntoId env jfor
   <|> liftM (JFor idxs) (algebraicSimp op)
   <|> checkProgress etaReduce jfor

inlineGetIota :: BindingEnv -> JFor -> Maybe JFor
inlineGetIota env (JFor idxBinders op) = do
  let idxEnv = map fst idxBinders
  JGet (IdxAtom x xIdxs) (IdxAtom (JVar v) idxs) <- return op
  (_, varDef) <- envLookup env v
  (JFor [] (JIota _), [i]) <- return $ betaReduce varDef idxs
  let idxs' = xIdxs ++ [i]
  -- TODO: have a more direct way to check index ordering condition
  case checkIdxEnv idxs' idxEnv of
    Left _   -> Nothing
    Right () -> return $ JFor idxBinders $ JId $ IdxAtom x idxs'

inlineIntoId :: BindingEnv -> JFor -> Maybe JFor
inlineIntoId env (JFor idxs op) = do
  JId (IdxAtom (JVar v) appIdxs) <- return op
  (UsedOnce, jfor) <- envLookup env v
  let idxScope = foldMap ((@>()) . fst) idxs
  let jforFresh = refreshIdxVars idxScope jfor
  (jfor', []) <- return $ betaReduce jforFresh appIdxs
  let (JFor idxs' op') = refreshIdxVars idxScope jfor'
  return $ JFor (idxs <> idxs') op'

inlineFromId :: BindingEnv -> IdxAtom -> Maybe IdxAtom
inlineFromId env idxAtom = do
  IdxAtom (JVar v) idxs <- return idxAtom
  (_, jfor) <- envLookup env v
  (JFor [] (JId (IdxAtom x idxs')), idxs'') <- return $ betaReduce jfor idxs
  return $ IdxAtom x (idxs' <> idxs'')

algebraicSimp :: JOp -> Maybe JOp
algebraicSimp op = case op of
  JScalarBinOp FAdd x y
      | fromScalarLit x == Just (RealLit 0) -> Just $ JId y
      | fromScalarLit y == Just (RealLit 0) -> Just $ JId x
  _ -> Nothing

fromScalarLit :: IdxAtom -> Maybe LitVal
fromScalarLit (IdxAtom (JLit x) []) = scalarFromArray x
fromScalarLit _ = Nothing

-- === variable usage pass ===

data VarUsage = Unused | UsedOnce | ArbitraryUse  deriving (Show, Eq)

type UsageEnv = MonMap Name VarUsage

collectUsage :: JExpr -> UsageEnv
collectUsage (JExpr decls result) = snd $ flip runCat mempty $ do
  extend $ useFreeVars ArbitraryUse result
  forM_ (reverse decls) $ \(JLet v jfor) -> do
    use <- looks $ flip lookupUse v
    case use of
      Unused -> return ()
      _ -> extend $ useFreeVars UsedOnce jfor

lookupUse :: UsageEnv -> VarP ann -> VarUsage
lookupUse env (v:>_) = monMapLookup env v

useFreeVars :: HasJVars a => VarUsage -> a -> UsageEnv
useFreeVars use x = foldMap (useVar use) $ envNames $ freeJVars x

useVar :: VarUsage -> Name -> UsageEnv
useVar use v = monMapSingle v use

instance Semigroup VarUsage where
  Unused <> use = use
  use <> Unused = use
  _ <> _ = ArbitraryUse

instance Monoid VarUsage where
  mempty = Unused

dceJaxFunction :: JaxFunction -> JaxFunction
dceJaxFunction (JaxFunction vs expr@(JExpr decls result)) =
  JaxFunction vs (JExpr decls' result)
  where
    decls' = filter (\(JLet v _) -> lookupUse useEnv v /= Unused) decls
    useEnv = collectUsage expr

-- === JAX IR builder ===

emitJFor :: MonadCat JEmbedEnv m => JFor -> m JVar
emitJFor jfor = do
  v <- freshVar ("v":> getJType jfor)
  extend $ (v @> (), [JLet v jfor])
  return v

freshVar :: MonadCat JEmbedEnv m => VarP ann -> m (VarP ann)
freshVar v = do
  scope <- looks fst
  let v' = rename v scope
  extend $ asFst (v' @> ())
  return v'

freshIdxVar :: MonadCat JEmbedEnv m => AxisSize -> m IdxVar
freshIdxVar n = do
  scope <- looks fst
  let nameChoices = [Name JaxIdx name 0 | name <- ["i", "j", "k"]]
  let v = renameChoice nameChoices scope :> n
  extend $ asFst (v @> ())
  return v

-- === JAXy IR Types ===

type IdxTyEnv = [IdxVar]
type JTypeEnv = (Env JType, IdxEnv)

instance Checkable JaxFunction where
  checkValid (JaxFunction vs body) = do
    let argTys = map varAnn vs
    void $ checkJExprType (newEnv vs argTys, []) body

checkJExprType :: JTypeEnv -> JExpr -> Except [JType]
checkJExprType initEnv (JExpr decls results) =
  liftM fst $ flip runCatT initEnv $ do
    forM_ decls $ \(JLet v@(_:>reqTy) jfor) -> do
      env <- look
      ty <- checkJType env jfor
      assertEq reqTy ty "Annotation"
      extend (v @> ty, [])
    env <- look
    forM results $ checkJType env

class HasJType a where
  getJType   :: a -> JType
  checkJType :: MonadError Err m => JTypeEnv -> a -> m JType

instance HasJType JFor where
  getJType (JFor idxs op) = JType (shape ++ shape') b
    where
      shape = [n | (_:>n, MapIdx) <- idxs]
      (JType shape' b) = getJType op

  checkJType env jfor@(JFor idxs op) =
    addContext ("\nChecking: " ++ pprint jfor) $ do
      let idxBinders = map fst idxs
      checkBinders env idxBinders
      let env' = env <> (mempty, idxBinders)
      let shape = [n | (_:>n, MapIdx) <- idxs]
      (JType shape' b) <- checkJType env' op
      return (JType (shape ++ shape') b)

assertNoMutualShadows :: (MonadError Err m, Pretty b, Traversable f)
                    => f (VarP b) -> m ()
assertNoMutualShadows bs =
  void $ flip runCatT mempty $ forM bs $ \b -> do
    env <- look
    checkNoShadow env b
    extend (b@>())

checkBinders :: (MonadError Err m, Pretty ann) => JTypeEnv -> [VarP ann] -> m ()
checkBinders env bs = do
  mapM_ (checkNoShadow (fst env)) bs
  assertNoMutualShadows bs

instance HasJType IdxAtom where
  getJType (IdxAtom x idxs) = JType (drop (length idxs) shape) b
    where JType shape b = getJType x

  checkJType (env, idxEnv) (IdxAtom x idxs) = do
    JType shape b <- checkJType (env, []) x
    throwIf (length idxs > length shape) CompilerErr $
        "Too many indices: " ++ pprint idxs
    forM_ (zip idxs shape) $ \((_:>nAnn), nArr) ->
      assertEq nArr nAnn "Index size doesn't match array shape"
    checkIdxEnv idxs idxEnv
    return $ JType (drop (length idxs) shape) b

checkIdxEnv :: MonadError Err m => [IdxVar] -> IdxTyEnv -> m ()
checkIdxEnv [] _ = return ()
checkIdxEnv (i:_) [] = throw CompilerErr $ "Index not in env " ++ pprint i
checkIdxEnv (i:idxs) (i':idxEnv)
  | varName i == varName i' = do
      assertEq i' i "Index size doesn't match index env"
      checkIdxEnv idxs idxEnv
  | otherwise = checkIdxEnv (i:idxs) idxEnv

instance HasJType JAtom where
  getJType atom = case atom of
    JVar (_:> ty) -> ty
    JLit (Array (shape, b) _) -> JType shape b

  checkJType (env,_) atom = case atom of
    JVar v@(_:> ty) -> do
      case envLookup env v of
        Just reqTy -> do
          assertEq reqTy ty "JVar"
          return ty
        _ -> throw CompilerErr $ "Lookup failed: " ++ pprint v
    JLit (Array (shape, b) _) -> return $ JType shape b

instance (Pretty a, HasJType a) => HasJType (JOpP a) where
  getJType op = ignoreExcept $ addContext ("Getting type of: " ++ pprint op) $
                  traverseJOpType $ fmap getJType op
  checkJType env op = do
    op' <- traverse (checkJType env) op
    traverseJOpType op'

traverseJOpType :: MonadError Err m => JOpP JType -> m JType
traverseJOpType jop = case jop of
  JScalarBinOp op xTy' yTy' -> do
    assertEq (JType [] xTy) xTy' "Arg type mismatch"
    assertEq (JType [] yTy) yTy' "Arg type mismatch"
    return $ JType [] outTy
    where (xTy, yTy, outTy) = binOpType op
  JScalarUnOp  op xTy' -> do
    assertEq (JType [] xTy) xTy' "Arg type mismatch"
    return $ JType [] outTy
    where (xTy, outTy) = unOpType  op
  JThreeFry2x32 xTy yTy -> do
    assertEq (JType [] IntType) xTy "Arg type mismatch"
    assertEq (JType [] IntType) yTy "Arg type mismatch"
    return $ JType [] IntType
  JId ty   -> return $ ty
  JIota n  -> return $ JType [n] IntType
  JGet (JType (_:shape) b) idxTy -> do
    assertEq (JType [] IntType) idxTy "Arg type mismatch"
    return $ JType shape b
  JGet (JType [] _) _ -> error "Attempting to index zero-dim array"

-- === free vars and substitutions ===

class HasJVars a where
  freeJVars :: a -> Env ()
  jSubst :: Env JAtom -> a -> a

instance HasJVars JFor where
  freeJVars (JFor _ op) = freeJVars op
  jSubst env (JFor idxs op) = JFor idxs $ jSubst env op

instance HasJVars JAtom where
  freeJVars x = case x of
    JLit _ -> mempty
    JVar v -> v @> ()
  jSubst env x = case x of
    JLit _ -> x
    JVar v -> env ! v

instance HasJVars IdxAtom where
  freeJVars (IdxAtom x _) = freeJVars x
  jSubst env (IdxAtom x idxs) = IdxAtom (jSubst env x) idxs

instance (Traversable f, HasJVars a) => HasJVars (f a) where
  freeJVars xs = foldMap freeJVars xs
  jSubst env op = fmap (jSubst env) op

etaReduce :: JFor -> JFor
etaReduce (JFor [] op) = JFor [] op
etaReduce (JFor (b:bs) op) = do
  let (JFor bs' op') = etaReduce (JFor bs op)
  fromMaybe (JFor (b:bs') op') $ do
    (i, MapIdx) <- return b
    [] <- return bs'
    JId (IdxAtom x idxs) <- return op'
    (idxs', i') <- unsnoc idxs
    unless (i == i') Nothing
    return $ JFor bs' $ JId $ IdxAtom x idxs'

betaReduce :: JFor -> [IdxVar] -> (JFor, [IdxVar])
betaReduce jfor idxs = do
  let freeVs = foldMap (@>()) idxs
  let jfor' = refreshIdxVars freeVs jfor
  betaReduceRec jfor' idxs

betaReduceRec :: JFor -> [IdxVar] -> (JFor, [IdxVar])
betaReduceRec jfor [] = (jfor, [])
betaReduceRec jfor idxs = do
  let Just (rest, i) = unsnoc idxs
  let (jfor', idxs') = betaReduceRec jfor rest
  fromMaybe (jfor', idxs' ++ [i]) $ do
    [] <- return idxs'
    JFor ((b,MapIdx):bs) op <- return jfor'
    return (JFor bs $ substOp (b @> i) op, [])

refreshIdxVars :: JScope -> JFor -> JFor
refreshIdxVars scope (JFor binders op) = do
  let (idxs, flavors) = unzip binders
  let idxs' = fst $ renames idxs () scope
  JFor (zip idxs' flavors) $ substOp (newEnv idxs idxs') op

-- TODO: extend `HasJVars` to handle index var substitution too
substOp :: Env IdxVar -> JOp -> JOp
substOp env op = flip fmap op $ \(IdxAtom x atomIdxs) ->
                                    IdxAtom x $ map trySubst atomIdxs
  where trySubst v = fromMaybe v (envLookup env v)

-- TODO: make a right-appending list we can actually pattern-match on
unsnoc :: [a] -> Maybe ([a], a)
unsnoc xs = case reverse xs of
  []     -> Nothing
  x:rest -> Just (reverse rest, x)

-- === simplification combinators ===

-- Simplifiers must only produce `Just` if some progress was made.
-- (e.g. avoid `mySimp x = trySimp x <|> pure x`)

simpFix :: Eq a => (a -> Maybe a) -> a -> a
simpFix f x = case f x of
  Nothing -> x
  Just x' -> simpFix f x'

-- TODO: more efficient implementation without using Eq
mapParallel :: (Eq a, Eq (f a), Functor f) => (a -> Maybe a) -> f a -> Maybe (f a)
mapParallel f = checkProgress (fmap (\x -> fromMaybe x (f x)))

checkProgress :: Eq a => (a -> a) -> a -> Maybe a
checkProgress f x | x' == x = Nothing
                  | otherwise = Just x'
  where x' = f x

-- === instances ===

instance Pretty JaxFunction where
  pretty (JaxFunction vs body) = "lambda" <+> pretty vs <> hardline <> pretty body

instance Pretty JExpr where
  pretty (JExpr decls results) =
    foldMap (\d -> pretty d <> hardline) decls <> "results:" <+> pretty results

instance Pretty IdxAtom where
  pretty (IdxAtom x idxs) = pretty x <> foldMap (\(i:>_) -> "." <> pretty i) idxs

instance Pretty JAtom where
  pretty (JLit x)      = pretty $ scalarFromArray x
  pretty (JVar (v:>_)) = pretty v

instance Pretty JDecl where
  pretty (JLet v rhs) = pretty v <+> "=" <+> pretty rhs

instance Pretty a => Pretty (JOpP a) where
  pretty op = prettyOpName op <+> foldMap (\x -> parens (pretty x) <> " ") op

instance Pretty JType where
  pretty (JType s b) = pretty b <> pretty s

instance Pretty JFor where
  pretty (JFor [] op) = pretty op
  pretty jfor@(JFor ((_,flavor):_) _) =
    pretty s <+> prettyJForCtx flavor jfor
    where
      s :: String
      s = case flavor of MapIdx -> "for"
                         SumIdx -> "sum"
instance Pretty TmpAtom where
  pretty _ = "<todo>"

prettyJForCtx :: IdxFlavor -> JFor -> Doc ann
prettyJForCtx flavor jfor@(JFor idxs op) = case idxs of
  [] -> " . " <> pretty op
  (i, flavor'):rest
    | flavor == flavor' -> pretty (varName i) <+>
                            prettyJForCtx flavor (JFor rest op)
    | otherwise -> pretty jfor

prettyOpName :: JOpP a -> Doc ann
prettyOpName jop = case jop of
  JScalarBinOp op _ _ -> pretty $ show op
  JScalarUnOp  op _   -> pretty $ show op
  JThreeFry2x32 _ _   -> "threefry2x32"
  JIota n  -> "iota@" <> pretty n
  JGet _ _ -> "get"
  JId _    -> "id"

instance ToJSON   JDecl
instance FromJSON JDecl

instance ToJSON   JaxFunction
instance FromJSON JaxFunction

instance ToJSON   JExpr
instance FromJSON JExpr

instance ToJSON   JFor
instance FromJSON JFor

instance ToJSON   JAtom
instance FromJSON JAtom

instance ToJSON   IdxAtom
instance FromJSON IdxAtom

instance ToJSON   IdxFlavor
instance FromJSON IdxFlavor

instance (ToJSON   ann) => ToJSON   (VarP ann)
instance (FromJSON ann) => FromJSON (VarP ann)

instance (ToJSON   e) => ToJSON   (JOpP e)
instance (FromJSON e) => FromJSON (JOpP e)

instance ToJSON   JType
instance FromJSON JType

instance ToJSON   Name
instance FromJSON Name

instance ToJSON   NameSpace
instance FromJSON NameSpace

instance ToJSON   ScalarBinOp
instance FromJSON ScalarBinOp

instance ToJSON   ScalarUnOp
instance FromJSON ScalarUnOp

instance ToJSON   CmpOp
instance FromJSON CmpOp

instance ToJSON   LitVal
instance FromJSON LitVal

instance ToJSON   BaseType
instance FromJSON BaseType

instance ToJSON   Array
instance FromJSON Array

instance ToJSON   Vec
instance FromJSON Vec
