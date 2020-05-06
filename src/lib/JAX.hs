-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module JAX (JAtom (..), JVar, typeToJType, jTypeToType,
            JExpr, JaxFunction, toJaxFunction) where

import Control.Monad.Reader
import Data.Aeson  hiding (Array)
import Data.Text.Prettyprint.Doc
import GHC.Generics
import GHC.Stack
import Control.Applicative
import Data.Traversable

import Env
import Syntax
import Subst
import PPrint
import Type
import Cat
import Array

-- === JAXish IR ===

type AxisSize = Int
type JVar = VarP JType
type JIndexVar = VarP AxisSize
data JDecl = JLet JVar JOp               deriving (Generic, Show)
data JExpr = JExpr [JDecl] [JAtom]       deriving (Generic, Show)
data JAtom = JLit LitVal | JVar JVar     deriving (Generic, Show)
data JType = JType [AxisSize] BaseType   deriving (Generic, Show)
data JaxFunction = JaxFunction [JVar] JExpr  deriving (Generic, Show)

data JOpP e = JScalarBinOp ScalarBinOp e e
            | JScalarUnOp  ScalarUnOp e
              deriving (Generic, Show)

data JOp = JFor [JIndexVar] [JIndexVar] (JOpP (JAtom, [JIndexVar]))
           deriving (Generic, Show)
type EmbedEnv = (Scope, [JDecl])
type JaxEnv = ((Env Atom), [JIndexVar])
type JaxM = ReaderT JaxEnv (Cat EmbedEnv)

runJaxM :: JaxM a -> a
runJaxM m = fst $ runCat (runReaderT m mempty) mempty

-- === lowering from Expr ===

toJaxFunction :: ([Var], Expr) -> JaxFunction
toJaxFunction (vs, expr) = runJaxM $ do
  vs' <- mapM freshVar vs
  let env = asFst (newEnv vs (map Var vs'))
  (result, (_, decls)) <- scoped $ extendR env $ do
    result <- toJaxExpr expr
    return $ flattenAtom result
  let jvs = map (fmap typeToJType) vs'
  return $ JaxFunction jvs $ JExpr decls result

flattenAtom :: Atom -> [JAtom]
flattenAtom atom = case atom of
  Var (v:>ty) -> [JVar $ v :> typeToJType ty]
  Con (Lit l) -> [JLit l]
  TupVal xs -> foldMap flattenAtom xs
  _ -> error $ "Can't flatten: " ++ pprint atom

toJaxExpr :: Expr -> JaxM Atom
toJaxExpr expr = case expr of
  Decl decl body -> do
    env <- toJaxDecl decl
    extendR env $ toJaxExpr body
  CExpr op -> toJaxOp op
  Atom x -> jSubst x

toJaxDecl :: Decl -> JaxM JaxEnv
toJaxDecl (Let v rhs) = do
  ans <- toJaxOp rhs
  return $ asFst $ v @> ans

toJaxOp :: CExpr -> JaxM Atom
toJaxOp cexpr = case cexpr of
  ScalarBinOp op x y -> do
    x' <- liftM fromScalarAtom $ jSubst x
    y' <- liftM fromScalarAtom $ jSubst y
    liftM jAtomToScalarAtom $ emitJOp $ JScalarBinOp op x' y'
  _ ->     error $ "Not implemented: " ++ pprint cexpr

fromScalarAtom :: HasCallStack => Atom -> JAtom
fromScalarAtom atom = case atom of
  Var (v :> BaseTy b) -> JVar (v:>JType [] b)
  Con (Lit x) -> JLit x
  Con (AGet (Var (v :> ArrayTy [] b))) -> JVar (v :> JType [] b)
  _ -> error $ "Not a scalar atom: " ++ pprint atom

emitJOp :: JOpP JAtom -> JaxM JAtom
emitJOp op = do
  idxs <- asks snd
  let op' = JFor idxs [] $ fmap (\x -> (x, [])) op
  v <- freshVar ("v":> getJOpType op')
  extend $ (v @> (), [JLet v op'])
  return $ JVar v

freshVar :: VarP ann -> JaxM (VarP ann)
freshVar v = do
  scope <- looks fst
  let v' = rename v scope
  extend $ asFst (v' @> ())
  return v'

jAtomToScalarAtom :: JAtom -> Atom
jAtomToScalarAtom jatom = case jatom of
  JVar (v:> JType [] b) -> Var (v:> BaseTy b)
  JLit x -> Con $ Lit x
  _ -> error $ "Not a scalar atom: " ++ pprint jatom

typeToJType :: Type -> JType
typeToJType ty = case ty of
  BaseTy b        -> JType []    b
  ArrayTy shape b -> JType shape b
  _ -> error $ "Not a jax type: " ++ pprint ty

jTypeToType :: JType -> Type
jTypeToType ty = case ty of
  JType shape b -> ArrayTy shape b

jSubst :: Subst a => a -> JaxM a
jSubst x = do
  env <- asks fst
  return $ scopelessSubst (fmap L env) x

getJOpType :: JOp -> JType
getJOpType (JFor foridx _ op) =
  let (JType leafshape basetype) = getJOpPType op
  in JType (map varAnn foridx ++ leafshape) basetype

getJOpPType :: JOpP a -> JType
getJOpPType jOp = case jOp of
  JScalarBinOp op _ _ -> JType [] outTy  where (_, _, outTy) = binOpType op
  JScalarUnOp  op _   -> JType [] outTy  where (_,    outTy) = unOpType  op

-- === instances ===

instance Pretty JAtom where
  pretty (JLit x) = pretty x
  pretty (JVar (v:>_)) = pretty v

instance Pretty JDecl where
  pretty (JLet v rhs) = pretty v <+> "=" <+> pretty rhs

instance Pretty a => Pretty (JOpP a) where
  pretty (JScalarBinOp op x y) = pretty (show op) <+> pretty x <+> pretty y
  pretty (JScalarUnOp  op x)   = pretty (show op) <+> pretty x

instance Pretty JType where
  pretty (JType s b) = pretty b <+> pretty s

instance Pretty JOp where
  pretty _ = undefined

instance ToJSON   JDecl
instance FromJSON JDecl

instance ToJSON   JaxFunction
instance FromJSON JaxFunction

instance ToJSON   JExpr
instance FromJSON JExpr

instance ToJSON   JOp
instance FromJSON JOp

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

instance Functor JOpP where
  fmap = fmapDefault

instance Foldable JOpP where
  foldMap = foldMapDefault

instance Traversable JOpP where
  traverse f op = case op of
    JScalarBinOp o x y -> liftA2 (JScalarBinOp o) (f x) (f y)
    JScalarUnOp o x    -> liftA  (JScalarUnOp o) (f x)
