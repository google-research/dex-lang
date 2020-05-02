-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module JAX (evalExprJAX) where

import Control.Monad.Reader
import Data.ByteString.Lazy.Char8 (pack, unpack)
import Data.Aeson
import Data.Text.Prettyprint.Doc
import GHC.Generics
import System.Process hiding (env)
import System.IO
import Control.Applicative
import Data.Traversable

import Env
import Syntax
import Subst
import PPrint
import Type
import Cat

evalExprJAX :: Expr -> IO ([ArrayRef], [Output])
evalExprJAX m = undefined

-- === JAXish IR ===

type AxisSize = Int
type JVar = VarP JType
type JIndexVar = VarP AxisSize
data JDecl = JLet JVar JOp               deriving (Generic, Show)
data JExpr = JDecl JDecl JExpr
           | JOp JOp
           | JAtoms [JAtom]              deriving (Generic, Show)
data JAtom = JLit LitVal | JVar JVar     deriving (Generic, Show)
data JFunction = JFunction [JVar] JExpr  deriving (Generic, Show)

data JType = JType [AxisSize] BaseType   deriving (Generic, Show)

data JOpP e = JScalarBinOp ScalarBinOp e e
            | JScalarUnOp  ScalarUnOp e
              deriving (Generic, Show)

data JOp = JFor [JIndexVar] [JIndexVar] (JOpP (JAtom, [JIndexVar]))
           deriving (Generic, Show)
type EmbedEnv = (Scope, [JDecl])
type JaxEnv = ((Env Atom), [JIndexVar])
type JaxM = ReaderT JaxEnv (Cat EmbedEnv)

-- TODO: type checker
getJOpType :: JOp -> JType
getJOpType (JFor foridx _ op) =
  let (JType leafshape basetype) = getJOpPType op
  in JType (map varAnn foridx ++ leafshape) basetype

getJOpPType :: JOpP a -> JType
getJOpPType op = case op of
  JScalarBinOp op _ _ -> JType [] outTy  where (_, _, outTy) = binOpType op
  JScalarUnOp  op _   -> JType [] outTy  where (_,    outTy) = unOpType  op

-- === lowering from Expr ===

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
    liftM jAtomToAtom $ emitJOp $ JScalarBinOp op x' y'
  _ ->     error $ "Not implemented: " ++ pprint cexpr

fromScalarAtom ::Atom -> JAtom
fromScalarAtom atom = case atom of
  Var (v :> BaseTy b) -> JVar (v:>JType [] b)
  Con (Lit x) -> JLit x
  _ -> error $ "Not a scalar atom: " ++ pprint atom

emitJOp :: JOpP JAtom -> JaxM JAtom
emitJOp op = do
  idxs <- asks snd
  let op' = JFor idxs [] $ fmap (\x -> (x, [])) op
  v <- freshVar ("v":> getJOpType op')
  extend $ (v @> (), [JLet v op'])
  return $ JVar v

freshVar :: JVar -> JaxM JVar
freshVar v = do
  scope <- looks fst
  let v' = rename v scope
  extend $ asFst (v' @> ())
  return v'

jAtomToAtom :: JAtom -> Atom
jAtomToAtom jatom = case jatom of
  JVar (v:> JType []b) -> Var (v:> BaseTy b)
  JLit x -> Con $ Lit x

typeToJType :: Type -> JType
typeToJType ty = case ty of
  BaseTy b -> JType [] b
  _ -> error $ "Not a jax type: " ++ pprint ty

jSubst :: Subst a => a -> JaxM a
jSubst x = do
  env <- asks fst
  return $ scopelessSubst (fmap L env) x

-- === call python over a pipe ===

pyCall :: (ToJSON a, FromJSON b) => a -> IO b
pyCall arg = do
  ansEncoded <- pipeCall "python3" ["misc/py/jax_call.py"] (unpack (encode arg))
  case eitherDecode (pack ansEncoded) of
    Left s    -> error $ "Couldn't decode JSON\n" ++ s
    Right ans -> return ans

pipeCall :: FilePath -> [String] -> String -> IO String
pipeCall cmd args input = do
  ~(Just hIn, Just hOut, _, _) <- createProcess $ (proc cmd args)
                                    { std_in  = CreatePipe
                                    , std_out = CreatePipe }
  hPutStr hIn input
  hClose hIn
  hGetContents hOut

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

instance Functor JOpP where
  fmap = fmapDefault

instance Foldable JOpP where
  foldMap = foldMapDefault

instance Traversable JOpP where
  traverse f op = case op of
    JScalarBinOp o x y -> liftA2 (JScalarBinOp o) (f x) (f y)
    JScalarUnOp o x    -> liftA  (JScalarUnOp o) (f x)
