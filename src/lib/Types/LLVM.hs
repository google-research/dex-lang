-- Copyright 2025 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE DuplicateRecordFields #-}

module Types.LLVM where

import Control.Monad
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Builder as BS

import qualified Types.Primitives as P
import PPrint
import Util (bs2str)

-- this string doesn't include the `@` or `%` prefixes
newtype Name = Name { val :: ByteString }
type Binder = (Name, Type)

data Module = Module { functions :: [Function] }

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

prInstr :: Type -> Instruction -> BS.Builder
prInstr resultTy = \case
  FAdd x y -> "fadd " <> pr resultTy <+> pr x.val <> ", " <> pr y.val

instance Pretty BasicBlock where
  prLines (BasicBlock name decls) = do
    emitLine $ pr name <> ":"
    indent do
      forM_ decls \decl -> emitLine $ prDecl decl

instance Pretty Name where
  pr name = BS.byteString name.val

instance Pretty UntypedOperand where
  pr = \case
    LocalOcc v -> prLocalName v
    Lit v -> pr v

instance Pretty Type where
  pr = \case
    BaseType (P.Scalar b) -> case b of
      P.Float32Type -> "f32"
    VoidType -> "void"


-- instance LLVMSer Operand where
--   lpr x = cat [lpr (getType x), ", ", printOperandWithoutType x]

-- instance Pretty Type where
--   pr = undefined


