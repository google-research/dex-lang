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

import Control.Monad.Except hiding (Except)
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State.Strict
import Data.Aeson  hiding (Array)
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

data JDecl = JLet JVar JFor                 deriving (Generic, Show, Eq)
data JExpr = JExpr [JDecl] [JAtom]          deriving (Generic, Show, Eq)
data JAtom = JLit Array | JVar JVar         deriving (Generic, Show, Eq)
data IdxAtom = IdxAtom JAtom [IdxVar]       deriving (Generic, Show, Eq)
data JType = JType [AxisSize] BaseType      deriving (Generic, Show, Eq)
data JaxFunction = JaxFunction [JVar] JExpr deriving (Generic, Show, Eq)

data JOpP e = JId e
            | JIota AxisSize
            | JGet e e
            | JScalarBinOp ScalarBinOp e e
            | JThreeFry2x32 e e
            | JScalarUnOp  ScalarUnOp e
              deriving (Generic, Functor, Foldable, Traversable, Show, Eq)

data TmpAtom = TmpLeaf IdxAtom
             | TmpRefName Var
             | TmpCon (PrimCon Type TmpAtom ())
               deriving (Generic, Show, Eq)

data JFor = JFor [IdxVar] [IdxVar] (JOpP IdxAtom)
            deriving (Generic, Show, Eq)

-- === lowering from Expr ===

type JEmbedEnv = (Scope, [JDecl])
type JSubstEnv = Env TmpAtom
type EffectState = Env (Int, TmpAtom)
type IdxEnv = [IdxVar]  -- for i j. --> [i, j]
type JaxM = ReaderT IdxEnv (StateT EffectState (Cat JEmbedEnv))

runJaxM :: JaxM a -> a
runJaxM m = fst $ flip runCat mempty $
  flip evalStateT mempty $ flip runReaderT mempty m

toJaxFunction :: ([Var], Expr) -> JaxFunction
toJaxFunction (vs, expr) = runJaxM $ do
  vs' <- mapM freshVar vs
  let env = newEnv vs $ map varToTmpAtom vs
  (result, (_, decls)) <- scoped $ do
    result <- toJaxExpr env expr
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

toJaxExpr :: JSubstEnv -> Expr -> JaxM TmpAtom
toJaxExpr env expr = case expr of
  Decl decl body -> do
    env' <- toJaxDecl env decl
    toJaxExpr (env <> env') body
  CExpr op -> toJaxOp env op
  Atom x -> return $ toJaxAtom env x

toJaxDecl :: JSubstEnv -> Decl -> JaxM JSubstEnv
toJaxDecl env (Let v rhs) = do
  ans <- toJaxOp env rhs
  return $ v @> ans

toJaxAtom :: JSubstEnv -> Atom -> TmpAtom
toJaxAtom env atom = case atom of
  Var v@(_:>RefTy _) -> TmpRefName v
  Var v -> case envLookup env v of
    Just x  -> x
    Nothing -> error "lookup failed"
  Con (Lit x) -> tmpAtomScalarLit x
  Con con -> TmpCon $ fmapExpr con id (toJaxAtom env) (error "unexpected lambda")
  _ -> error $ "Not implemented: " ++ pprint atom

toJaxOp :: JSubstEnv -> CExpr -> JaxM TmpAtom
toJaxOp env cexpr = toJaxOp' cexpr'
  where cexpr' = fmapExpr cexpr id (toJaxAtom env) (,env)

toJaxOp' :: PrimOp Type TmpAtom (LamExpr, JSubstEnv) -> JaxM TmpAtom
toJaxOp' expr = case expr of
  For _ (LamExpr i@(_ :> FixedIntRange 0 n) body, env) -> do
    idxEnv <- ask
    -- TODO: scope this to avoid burning through names
    i' <-freshIdxVar n
    iotaVar <- emitJFor $ JFor [] [] $ JIota n
    let iotaAtom = iotaVarAsIdx (FixedIntRange 0 n) $ IdxAtom (JVar iotaVar) [i']
    let env' = env <> i @> iotaAtom
    ans <- extendR [i'] $ toJaxExpr env' body
    liftM (TmpCon . AFor (varAnn i)) $ traverseArrayLeaves ans $ \x -> do
      ansVar <- emitJFor $ JFor (idxEnv ++ [i']) [] $ JId x
      return $ IdxAtom (JVar ansVar) idxEnv
  TabGet ~(TmpCon (AFor _ tab)) i -> do
    traverseArrayLeaves tab $ \x -> emitOp $ JGet x $ fromScalarAtom i
  ScalarBinOp op x y -> liftM toScalarAtom $
    emitOp $ JScalarBinOp op (fromScalarAtom x) (fromScalarAtom y)
  IndexAsInt x -> liftM toScalarAtom $
    emitOp $ JId (fromScalarAtom x)
  ScalarUnOp op x -> liftM toScalarAtom $
    emitOp $ JScalarUnOp op (fromScalarAtom x)
  RunWriter (LamExpr refVar body, env) -> do
    idxEnvDepth <- asks length
    let (RefTy wTy) = varAnn refVar
    wInit <- zerosAt wTy
    modify (<> refVar @> (idxEnvDepth, wInit))
    aResult <- toJaxExpr env body
    wFinal <- gets $ snd . (! refVar)
    modify $ envDelete (varName refVar)
    return $ TmpCon $ RecCon $ Tup [aResult, wFinal]
  PrimEffect (TmpRefName refVar) m -> do
    case m of
      MTell x -> do
        (depth, curAccum) <- gets (! refVar)
        xSum <- sumPoly depth x
        newAccum <- local (take depth) $ addPoly curAccum xSum
        modify (<> refVar @> (depth, newAccum))
        return $ TmpCon $ RecCon $ Tup []
      _ -> error $ "Not implemented: " ++ show expr
  RecGet x i -> do
    case x of
      TmpCon (RecCon r) -> return $ recGet r i
      val -> error $ "Expected a record, got: " ++ show val
  FFICall s _ _ args | s == "threefry2x32" -> liftM toScalarAtom $
      emitOp $ JThreeFry2x32 (fromScalarAtom x) (fromScalarAtom y)
        where x:y:[] = args
  _ -> error $ "Not implemented: " ++ show expr

iotaVarAsIdx :: Type -> IdxAtom -> TmpAtom
iotaVarAsIdx n x = TmpCon $ AsIdx n $ toScalarAtom x

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
  v <- emitJFor $ JFor idxEnv [] op
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
  traverseArrayLeaves atom $ \x -> do
     v <- emitJFor $ JFor forIdxs sumIdxs $ JId x
     return $ IdxAtom (JVar v) forIdxs

tmpAtomScalarLit :: LitVal -> TmpAtom
tmpAtomScalarLit x = toScalarAtom $ IdxAtom (JLit $ arrayFromScalar x) []

instance HasType TmpAtom where
  getEffType atom = pureType $ case atom of
    TmpLeaf idxAtom -> jTypeToType $ getJType idxAtom
    TmpRefName _ -> undefined
    TmpCon con -> getConType $ fmapExpr con id getType $ error "unexpected lambda"
  checkEffType = error "Not implemented"

-- === Simplification pass on JAX IR ===

type BindingEnv = Env (VarUsage, JFor)
type SimpEnv = (Env JAtom, BindingEnv)
type SimpM = Cat JEmbedEnv

pattern JForId :: JAtom -> JFor
pattern JForId x = JFor [] [] (JId (IdxAtom x []))

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
  let jfor' = simplifyJFor bindingEnv $ jSubst substEnv jfor
  case jfor' of
    JForId x -> extend $ asFst (v @> x)
    _ -> do
      vOut <- lift $ emitJFor jfor'
      extend $ (v @> JVar vOut, vOut @> (usage, jfor'))

simplifyJFor :: BindingEnv -> JFor -> JFor
simplifyJFor env (JFor forIdxs sumIdxs op) =
  case op' of
    JGet (IdxAtom x xIdxs) idx -> case matchIota env idx of
      Just i -> simplifyJFor env $
                  JFor forIdxs [] $ JId $ IdxAtom x $ xIdxs ++ [i]
      Nothing -> jfor'
    JId (IdxAtom (JVar v) xIdxs) ->
      case envLookup env v of
        Just (UsedOnce, vDef) -> inlineId forIdxs sumIdxs vDef xIdxs
        _ -> etaReduce jfor'
    _ -> etaReduce jfor'
  where
    op' = fmap (simpFix $ simplifyIdxAtom env) op
    jfor' = JFor forIdxs sumIdxs op'

etaReduce :: JFor -> JFor
etaReduce (JFor forIdxs sumIdxs (JId (IdxAtom x xIdxs))) =
  JFor forIdxs' sumIdxs $ JId $ IdxAtom x xIdxs'
    where (forIdxs', xIdxs') = dropCommonTail forIdxs xIdxs
etaReduce jfor = jfor

matchIota :: BindingEnv -> IdxAtom -> Maybe IdxVar
matchIota env (IdxAtom (JVar v) idxs) = do
  (_, jfor) <- envLookup env v
  result <- applyIdxs jfor idxs
  case result of
    (JIota _, [i]) -> Just i
    _ -> Nothing
matchIota _ _ = Nothing

simplifyIdxAtom :: BindingEnv -> IdxAtom -> Maybe IdxAtom
simplifyIdxAtom env idxAtom = case idxAtom of
  IdxAtom (JVar v) idxs -> do
    (_, jfor) <- envLookup env v
    result <- applyIdxs jfor idxs
    case result of
      (JId (IdxAtom x idxs'), idxs'') -> return $ IdxAtom x (idxs' <> idxs'')
      _ -> Nothing
  _     -> Nothing

inlineId :: [IdxVar] -> [IdxVar] -> JFor -> [IdxVar] -> JFor
inlineId forIdxs sumIdxs (JFor forIdxs' sumIdxs' op) appIdxs =
  JFor (forIdxs <> forIdxs'') (sumIdxs <> sumIdxs'') op'
  where
    -- The complexity here is all in the variable renaming.
    -- Stack-based indices would be much simpler.
    idxScope = foldMap (@>()) $ forIdxs <> sumIdxs
    (forIdxs'', idxScope') = renames (drop (length appIdxs) forIdxs') idxScope
    (sumIdxs'', _) = renames sumIdxs' (idxScope <> idxScope')
    ~(Just (op', [])) = applyIdxs (JFor (forIdxs' <> sumIdxs') [] op) $
                          appIdxs <> forIdxs'' <> sumIdxs''

applyIdxs :: JFor -> [IdxVar] -> Maybe (JOpP IdxAtom, [IdxVar])
applyIdxs (JFor idxBinders [] op) idxs | length idxs >= length idxBinders = do
  let op' = flip fmap op $ \(IdxAtom x atomIdxs) ->
              IdxAtom x $ map (substEnv !) atomIdxs
  return (op', remIdxs)
  where
    substEnv = newEnv idxBinders appIdxs
    (appIdxs, remIdxs) = splitAt (length idxBinders) idxs
applyIdxs _ _ = Nothing

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

type JTypeEnv = FullEnv JType AxisSize

instance Checkable JaxFunction where
  checkValid (JaxFunction vs body) = do
    let argTys = map varAnn vs
    void $ checkJExprType (newLEnv vs argTys) body

checkJExprType :: JTypeEnv -> JExpr -> Except [JType]
checkJExprType initEnv (JExpr decls results) =
  liftM fst $ flip runCatT initEnv $ do
    forM_ decls $ \(JLet v@(_:>reqTy) jfor) -> do
      env <- look
      ty <- checkJType env jfor
      assertEq reqTy ty "Annotation"
      extend (v @> L ty)
    env <- look
    forM results $ checkJType env

class HasJType a where
  getJType   :: a -> JType
  checkJType :: MonadError Err m => JTypeEnv -> a -> m JType

instance HasJType JFor where
  getJType (JFor idxs _ op) = JType (map varAnn idxs ++ shape) b
    where (JType shape b) = getJType op

  checkJType env (JFor idxs sumIdxs op) = do
    checkBinders env idxs
    checkBinders env sumIdxs
    let env' = env <> foldMap tbind idxs <> foldMap tbind sumIdxs
    (JType shape b) <- checkJType env' op
    return (JType (map varAnn idxs ++ shape) b)

assertNoMutualShadows :: (MonadError Err m, Pretty b, Traversable f)
                    => f (VarP b) -> m ()
assertNoMutualShadows bs =
  void $ flip runCatT mempty $ forM bs $ \b -> do
    env <- look
    assertNoShadow env b
    extend (b@>())

checkBinders :: (MonadError Err m, Pretty ann) => JTypeEnv -> [VarP ann] -> m ()
checkBinders env bs = do
  mapM_ (assertNoShadow env) bs
  assertNoMutualShadows bs

instance HasJType IdxAtom where
  getJType (IdxAtom x idxs) = JType (drop (length idxs) shape) b
    where JType shape b = getJType x

  checkJType env (IdxAtom x idxs) = do
    JType shape b <- checkJType env x
    throwIf (length idxs > length shape) CompilerErr $
        "Too many indices: " ++ pprint idxs
    forM_ (zip idxs shape) $ \(i@(_:>nAnn), nArr) ->
      case envLookup env i of
        Just (T nEnv) -> do
          assertEq nEnv nAnn "Index size doesn't match binder"
          assertEq nArr nAnn "Index size doesn't match array shape"
        _ -> throw CompilerErr $ "Lookup failed: " ++ pprint i
    return $ JType (drop (length idxs) shape) b

instance HasJType JAtom where
  getJType atom = case atom of
    JVar (_:> ty) -> ty
    JLit (Array (shape, b) _) -> JType shape b

  checkJType env atom = case atom of
    JVar v@(_:> ty) -> do
      case envLookup env v of
        Just (L reqTy) -> do
          assertEq reqTy ty "JVar"
          return ty
        _ -> throw CompilerErr $ "Lookup failed: " ++ pprint v
    JLit (Array (shape, b) _) -> return $ JType shape b

instance HasJType a => HasJType (JOpP a) where
  getJType op = ignoreExcept $ traverseJOpType $ fmap getJType op
  checkJType env op = do
    op' <- traverse (checkJType env) op
    traverseJOpType op'

traverseJOpType :: MonadError Err m => JOpP JType -> m JType
traverseJOpType jop = case jop of
  JScalarBinOp op _ _ ->
    return $ JType [] outTy
    where (_, _, outTy) = binOpType op
  JScalarUnOp  op _   ->
    return $ JType [] outTy
    where (_,    outTy) = unOpType  op
  JThreeFry2x32 _ _ -> return $ JType [] IntType
  JId ty   -> return $ ty
  JIota n  -> return $ JType [n] IntType
  JGet (JType (_:shape) b) _ -> return $ JType shape b
  JGet (JType [] _) _ -> error "Attempting to index zero-dim array"

-- === free vars and substitutions ===

class HasJVars a where
  freeJVars :: a -> Env ()
  jSubst :: Env JAtom -> a -> a

instance HasJVars JFor where
  freeJVars (JFor _ _ op) = freeJVars op
  jSubst env (JFor forIdxs sumIdxs op) =
    JFor forIdxs sumIdxs $ jSubst env op

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

-- === utils ===

dropCommonTail :: Eq a => [a] -> [a] -> ([a], [a])
dropCommonTail xs ys = (reverse xs', reverse ys')
  where (xs', ys') = dropCommonPrefix (reverse xs) (reverse ys)

dropCommonPrefix :: Eq a => [a] -> [a] -> ([a], [a])
dropCommonPrefix (x:xs) (y:ys) | x == y = dropCommonPrefix xs ys
dropCommonPrefix xs ys = (xs, ys)

simpFix :: (a -> Maybe a) -> a -> a
simpFix f x = case f x of
  Nothing -> x
  Just x' -> simpFix f x'

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
  pretty (JFor idxs sumIdxs op) = prettyIdxBinders "for" idxs
                               <> prettyIdxBinders "sum" sumIdxs
                               <> pretty op

prettyOpName :: JOpP a -> Doc ann
prettyOpName jop = case jop of
  JScalarBinOp op _ _ -> pretty $ show op
  JScalarUnOp  op _   -> pretty $ show op
  JThreeFry2x32 _ _   -> "threefry2x32"
  JIota n  -> "iota@" <> pretty n
  JGet _ _ -> "get"
  JId _    -> "id"

prettyIdxBinders :: Doc ann -> [IdxVar] -> Doc ann
prettyIdxBinders _ [] = mempty
prettyIdxBinders s idxs = s <+> hsep (map (pretty . varName) idxs) <> " . "

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
