-- Copyright 2025 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE DuplicateRecordFields #-}

module Types.LLVM where

import Data.String
import Control.Monad
import Control.Monad.State
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Builder as BS

import qualified Types.Primitives as P
import PPrint
import Util (bs2str)

-- this string doesn't include the `@` or `%` prefixes
newtype Name = Name { val :: ByteString }
type Binder = (Name, Type)

data Module = Module { functions :: [TopDecl] }

data TopDecl =
   FunctionDef Function
 | FunctionDecl Type Name [Type]

data Function = Function
  { name   :: Name
  , params :: [Binder]
  , body   :: [BasicBlock] }

data BasicBlock = BasicBlock
  { name         :: Name
  , instructions :: [Decl]}

type Decl = (Maybe Name, Type, Instruction)
data Instruction =
   FAdd Operand Operand
 | Call Type Name [Operand]
 | Return Operand

data Operand = Operand { val :: UntypedOperand, ty :: Type }
data UntypedOperand =
   LocalOcc Name
 | Lit P.LitVal

data Type =
   BaseType P.BaseType
 | VoidType

-- === LLVM printing ===

-- This is load-bearing! We have to generate correct LLVM textual representation.

instance Pretty Module where
  prLines m = forM_ m.functions \f -> do
    prLines f
    emitLine ""

instance Pretty TopDecl where
  prLines = \case
    FunctionDef f -> prLines f
    FunctionDecl ty fname argTys -> do
      emitLine $ "declare" <+> pr ty <+> app (prTopName fname) (prDeclArgs argTys)

prDeclArgs :: [Type] -> [BS.Builder]
prDeclArgs tys = flip evalState (0::Int) do
  forM tys \ty -> do
    i <- get
    put (i + 1)
    return $ pr ty <+> "%" <> pr i

instance Pretty Function where
  prLines (Function name [] body) = do
    emitLine $ "define i32" <+> prTopName name <> "() {"
    forM_ body \block -> do
      emitLine ""
      prLines block
    emitLine "}"

prTopName :: Name -> BS.Builder
prTopName name = "@" <> BS.byteString name.val

prLocalName :: Name -> BS.Builder
prLocalName name = "%" <> BS.byteString name.val

prDecl :: Decl -> BS.Builder
prDecl (Just v, resultTy, instr) = prLocalName v <> " = " <> prInstr resultTy instr
prDecl (Nothing, resultTy, instr) = prInstr resultTy instr

prInstr :: Type -> Instruction -> BS.Builder
prInstr resultTy = \case
  FAdd x y -> "fadd" <+> pr resultTy <+> pr x.val <> ", " <> pr y.val
  Call ty f xs -> "call" <+> pr ty <+> app (prTopName f) (map pr xs)
  Return x -> "ret" <+> pr x

instance Pretty BasicBlock where
  prLines (BasicBlock name decls) = do
    emitLine $ pr name <> ":"
    indent do
      forM_ decls \decl -> emitLine $ prDecl decl

instance IsString Name where
  fromString s = Name $ fromString s

instance Pretty Name where
  pr name = BS.byteString name.val

instance Pretty Operand where
  pr x = pr x.ty <+> pr x.val

instance Pretty UntypedOperand where
  pr = \case
    LocalOcc v -> prLocalName v
    Lit v -> pr v

instance Pretty Type where
  pr = \case
    BaseType (P.Scalar b) -> case b of
      P.Float32Type -> "float"
      P.Int32Type -> "i32"
    VoidType -> "void"
