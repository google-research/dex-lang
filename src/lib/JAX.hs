-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module JAX (JAtom (..), JVar, typeToJType, jTypeToType,
            JExpr, JaxFunction, toJaxFunction) where

import Control.Monad.Except hiding (Except)
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Aeson  hiding (Array)
import Data.Text.Prettyprint.Doc
import GHC.Generics
import GHC.Stack

import Env
import Syntax
import PPrint
import Type
import Cat
import Array

-- === JAXish IR ===

type JVar   = VarP JType

data JDecl = JLet JVar JFor                    deriving (Generic, Show, Eq)
data JExpr = JExpr [JDecl] [JAtom]             deriving (Generic, Show, Eq)
data JAtom = JLit LitVal | JVar JVar [IdxVar]  deriving (Generic, Show, Eq)
data JType = JType [AxisSize] BaseType         deriving (Generic, Show, Eq)

data JaxFunction = JaxFunction [JVar] JExpr    deriving (Generic, Show, Eq)

type AxisSize = Int
type IdxVar = VarP AxisSize

data JOpP e = JId e
            | JIota AxisSize
            | JGet e e
            | JScalarBinOp ScalarBinOp e e
            | JScalarUnOp  ScalarUnOp e
              deriving (Generic, Functor, Foldable, Traversable, Show, Eq)

data TmpAtom = TmpLeaf JVar [IdxVar]
             | TmpCon (PrimCon Type TmpAtom ())
               deriving (Generic, Show, Eq)

data JFor = JFor [IdxVar] [IdxVar] (JOpP JAtom)
            deriving (Generic, Show, Eq)

type EmbedEnv = (Scope, [JDecl])
type JSubstEnv = Env TmpAtom
type IdxEnv = [IdxVar]  -- for i j. --> [i, j]
type JaxM = ReaderT IdxEnv (Cat EmbedEnv)

runJaxM :: JaxM a -> a
runJaxM m = fst $ runCat (runReaderT m mempty) mempty

-- === lowering from Expr ===

toJaxFunction :: ([Var], Expr) -> JaxFunction
toJaxFunction (vs, expr) = runJaxM $ do
  vs' <- mapM freshVar vs
  let env = newEnv vs $ map (\v -> TmpLeaf (fmap typeToJType v) []) vs'
  (result, (_, decls)) <- scoped $ do
    result <- toJaxExpr env expr
    return $ flattenAtom result
  let jvs = map (fmap typeToJType) vs'
  return $ JaxFunction jvs $ JExpr decls result

flattenAtom :: TmpAtom -> [JAtom]
flattenAtom atom =
  execWriter $ traverseArrayLeaves atom $ \x -> tell [x] >> return x

toJaxExpr :: JSubstEnv -> Expr -> JaxM TmpAtom
toJaxExpr env expr = case expr of
  Decl decl body -> do
    env' <- toJaxDecl env decl
    toJaxExpr (env <> env') body
  CExpr op -> toJaxOp env op
  Atom x -> toJaxAtom env x

toJaxDecl :: JSubstEnv -> Decl -> JaxM JSubstEnv
toJaxDecl env (Let v rhs) = do
  ans <- toJaxOp env rhs
  return $ v @> ans

toJaxAtom :: JSubstEnv -> Atom -> JaxM TmpAtom
toJaxAtom env atom = case atom of
  Var v -> case envLookup env v of
    Just x  -> return x
    Nothing -> error "lookup failed"
  Con (Lit x) -> return $ TmpCon $ Lit x
  Con (RecCon r) -> liftM (TmpCon . RecCon) $ traverse (toJaxAtom env) r
  _ -> error $ "Not implemented " ++ pprint atom

toJaxOp :: JSubstEnv -> CExpr -> JaxM TmpAtom
toJaxOp env cexpr = do
  cexpr' <- traverseExpr cexpr return (toJaxAtom env) (\lam -> return (lam, env))
  toJaxOp' cexpr'

toJaxOp' :: PrimOp Type TmpAtom (LamExpr, JSubstEnv) -> JaxM TmpAtom
toJaxOp' expr = case expr of
  For _ (LamExpr i@(_ :> FixedIntRange 0 n) body, env) -> do
    idxEnv <- ask
    -- TODO: scope this to avoid burning through names
    i' <-freshIdxVar n
    iotaVar <- emitJFor $ JFor [] [] $ JIota n
    let iotaAtom = iotaVarAsIdx (FixedIntRange 0 n) $ JVar iotaVar [i']
    let env' = env <> i @> iotaAtom
    ans <- extendR [i'] $ toJaxExpr env' body
    liftM (TmpCon . AFor (varAnn i)) $ traverseArrayLeaves ans $ \x -> do
      ansVar <- emitJFor $ JFor (idxEnv ++ [i']) [] $ JId x
      return $ JVar ansVar idxEnv
  TabGet ~(TmpCon (AFor _ tab)) i -> do
    traverseArrayLeaves tab $ \x -> emitOp $ JGet x $ fromScalarAtom i
  ScalarBinOp op x y -> do
    ans <- emitOp $ JScalarBinOp op (fromScalarAtom x) (fromScalarAtom y)
    return $ toScalarAtom ans
  _ -> error $ "Not implemented: " ++ show expr


-- TODO: use AsIdx
iotaVarAsIdx :: Type -> JAtom -> TmpAtom
iotaVarAsIdx n atom = case atom of
  JVar v idxs -> TmpCon $ AsIdx n $ TmpCon $ AGet $ TmpLeaf v idxs
  _ -> error $ "not implemented " ++ pprint atom

fromScalarAtom :: HasCallStack => TmpAtom -> JAtom
fromScalarAtom atom = case atom of
  TmpLeaf v idxs -> JVar v idxs
  TmpCon (Lit x) -> JLit x
  TmpCon (AsIdx _ x) -> fromScalarAtom x
  TmpCon (AGet x)    -> fromScalarAtom x
  _ -> error $ "Not a scalar atom: " ++ show atom

toScalarAtom :: JAtom -> TmpAtom
toScalarAtom atom = case atom of
  JVar v idxs -> TmpCon $ AGet $ TmpLeaf v idxs
  JLit x      -> TmpCon $ Lit x

traverseArrayLeaves :: Monad m => TmpAtom -> (JAtom -> m JAtom) -> m TmpAtom
traverseArrayLeaves atom f = case atom of
  TmpCon (Lit  x)      -> liftM toScalarAtom $ f $ JLit x
  TmpCon (RecCon r)    -> liftM (TmpCon . RecCon) $ traverse (flip traverseArrayLeaves f) r
  TmpCon (AFor n body) -> liftM (TmpCon . AFor n) $ traverseArrayLeaves body f
  TmpCon (AGet (TmpLeaf v idxs)) -> do
    ~(JVar v' idxs') <- f $ JVar v idxs
    return $ TmpCon $ AGet $ TmpLeaf v' idxs'
  _ -> error $ "Not implemented: " ++ show atom

emitOp :: JOpP JAtom -> JaxM JAtom
emitOp op = do
  idxEnv <- ask
  v <- emitJFor $ JFor idxEnv [] op
  return $ JVar v idxEnv

emitJFor :: JFor -> JaxM JVar
emitJFor jfor = do
  v <- freshVar ("v":> getJType jfor)
  extend $ (v @> (), [JLet v jfor])
  return v

freshVar :: VarP ann -> JaxM (VarP ann)
freshVar v = do
  scope <- looks fst
  let v' = rename v scope
  extend $ asFst (v' @> ())
  return v'

freshIdxVar :: AxisSize -> JaxM IdxVar
freshIdxVar n = do
  scope <- looks fst
  let nameChoices = [Name JaxIdx name 0 | name <- ["i", "j", "k"]]
  let v = renameChoice nameChoices scope :> n
  extend $ asFst (v @> ())
  return v

typeToJType :: Type -> JType
typeToJType ty = case ty of
  BaseTy b        -> JType []    b
  ArrayTy shape b -> JType shape b
  _ -> error $ "Not a jax type: " ++ pprint ty

jTypeToType :: JType -> Type
jTypeToType ty = case ty of
  JType shape b -> ArrayTy shape b

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

checkBinders :: (MonadError Err m, Pretty ann) => JTypeEnv -> [VarP ann] -> m ()
checkBinders env bs = do
  mapM_ (checkNoShadow env) bs
  checkNoMutualShadows bs

instance HasJType JAtom where
  getJType atom = case atom of
    JVar (_:> JType shape b) idxs -> JType (drop (length idxs) shape) b
    JLit x -> JType [] $ litType x
  checkJType env atom = case atom of
    JVar v@(_:> ty@(JType shape b)) idxs -> do
      case envLookup env v of
        Just (L reqTy) -> assertEq reqTy ty "JVar"
        _ -> throw CompilerErr $ "Lookup failed: " ++ pprint v
      throwIf (length idxs > length shape) CompilerErr $
        "Too many indices: " ++ pprint idxs
      forM_ (zip idxs shape) $ \(i@(_:>nAnn), nArr) ->
        case envLookup env i of
          Just (T nEnv) -> do
            assertEq nEnv nAnn "Index size doesn't match binder"
            assertEq nArr nAnn "Index size doesn't match array shape"
          _ -> throw CompilerErr $ "Lookup failed: " ++ pprint i
      return $ JType (drop (length idxs) shape) b
    JLit x -> return $ JType [] $ litType x

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
  JId ty   -> return $ ty
  JIota n  -> return $ JType [n] IntType
  JGet (JType (_:shape) b) _ -> return $ JType shape b
  JGet (JType [] _) _ -> error "Attempting to index zero-dim array"

-- === instances ===

instance Pretty JaxFunction where
  pretty (JaxFunction vs body) = "lambda" <+> pretty vs <> hardline <> pretty body

instance Pretty JExpr where
  pretty (JExpr decls results) =
    foldMap (\d -> pretty d <> hardline) decls <> "results:" <+> pretty results

instance Pretty JAtom where
  pretty (JLit x)           = pretty x
  pretty (JVar (v:>_) idxs) =
    pretty v <> foldMap (\(i:>_) -> "." <> pretty i) idxs

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
