-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE CPP #-}

module Serialize (pprintVal, getDexString,
                  HasPtrs (..), takePtrSnapshot, restorePtrSnapshot) where

import Prelude hiding (pi, abs)
import Control.Monad
import qualified Data.ByteString as BS
import Data.Functor ((<&>))
import Data.ByteString.Internal (memcpy)
import Data.ByteString.Unsafe (unsafeUseAsCString)
import Data.Foldable
import qualified Data.Map.Strict as M
import Data.Int
import Data.Store hiding (size)
import Data.Text.Prettyprint.Doc  hiding (brackets)
import Foreign.Ptr
import Foreign.Marshal.Array
import GHC.Generics (Generic)
import Numeric (showHex)

import LabeledItems

import Interpreter
import Err
import PPrint (PrettyPrec (..), PrecedenceLevel (..))

import Syntax
import Type
import Name
import PPrint ()

foreign import ccall "malloc_dex"           dexMalloc    :: Int64  -> IO (Ptr ())
foreign import ccall "dex_allocation_size"  dexAllocSize :: Ptr () -> IO Int64

pprintVal :: (MonadIO1 m, EnvReader m, Fallible1 m) => Val n -> m n String
pprintVal val = docAsStr <$> prettyVal val
{-# SCC pprintVal #-}

-- TODO: get the pointer rather than reading char by char
getDexString :: (MonadIO1 m, EnvReader m, Fallible1 m) => Val n -> m n String
getDexString (DataCon _ _ _ 0 [_, xs]) = do
  xs' <- getTableElements xs
  forM xs' \(Con (Lit (Word8Lit c))) -> return $ toEnum $ fromIntegral c
getDexString x = error $ "Not a string: " ++ pprint x
{-# SCC getDexString #-}

getTableElements :: (MonadIO1 m, EnvReader m, Fallible1 m) => Val n -> m n [Atom n]
getTableElements tab = do
  TabTy b _ <- getType tab
  idxs <- indices $ binderType b
  forM idxs \i -> liftInterpM $ evalExpr $ App tab (i:|[])

-- Pretty-print values, e.g. for displaying in the REPL.
-- This doesn't handle parentheses well. TODO: treat it more like PrettyPrec
prettyVal :: (MonadIO1 m, EnvReader m, Fallible1 m) => Val n -> m n (Doc ann)
prettyVal val = case val of
  -- Pretty-print tables.
  Lam (LamExpr (LamBinder _ _ TabArrow _) _) -> do
    atoms <- getTableElements val
    elems <- forM atoms \atom -> do
      case atom of
        Con (Lit (Word8Lit  c)) -> return $ showChar (toEnum @Char $ fromIntegral c) ""
        Con (Lit (Word32Lit c)) -> return $ "0x" ++ showHex c ""
        Con (Lit (Word64Lit c)) -> return $ "0x" ++ showHex c ""
        _ -> pprintVal atom
    TabTy b resultTy <- getType val
    idxSetDoc <- return case binderType b of
      Fin _  -> mempty               -- (Fin n) is not shown
      idxSet -> "@" <> pretty idxSet -- Otherwise, show explicit index set
    elemsDoc <- return case resultTy of
      -- Print table of characters as a string literal.
      TC (BaseType (Scalar Word8Type)) -> pretty ('"': concat elems ++ "\"")
      _ -> pretty elems
    return $ elemsDoc <> idxSetDoc
  DataCon name _ _ _ args -> do
    mapM prettyVal args <&> \case
      []    -> pretty name
      args' -> parens $ pretty name <+> hsep args'
  Con con -> case con of
    ProdCon [] -> return $ pretty ()
    ProdCon [x, y] -> do
      xStr <- pprintVal x
      yStr <- pprintVal y
      return $ pretty (xStr, yStr)
    ProdCon _ -> error "Unexpected product type: only binary products available in surface language."
    SumAsProd ty (TagRepVal trep) payload -> do
      let t = fromIntegral trep
      case ty of
        TypeCon _ dataDefName _ -> do
          DataDef _ _ dataCons <- lookupDataDef dataDefName
          DataConDef conName _ <- return $ dataCons !! t
          mapM prettyVal (payload !! t) <&> \case
            []   -> pretty conName
            args -> parens $ pretty conName <+> hsep args
        VariantTy (NoExt types) -> return $ pretty variant
          where
            [value] = payload !! t
            (theLabel, repeatNum) = toList (reflectLabels types) !! t
            variant = Variant (NoExt types) theLabel repeatNum value
        _ -> error "SumAsProd with an unsupported type"
    _ -> return $ pretty con
  Record (LabeledItems row) -> do
    let separator = line' <> ","
    let bindwith = " ="
    let elems = concatMap (\(k, vs) -> map (k,) (toList vs)) (M.toAscList row)
    let fmElem = \(label, v) -> ((pretty label <> bindwith) <+>) <$> prettyVal v
    docs <- mapM fmElem elems
    let innerDoc = "{" <> flatAlt " " ""
          <> concatWith (surround (separator <> " ")) docs
          <> "}"
    return $ align $ group innerDoc
  atom -> return $ prettyPrec atom LowestPrec

-- === taking memory snapshots for serializing heap-backed dex values ===

data WithSnapshot a = WithSnapshot a [PtrSnapshot]  deriving Generic
type RawPtr = Ptr ()

class HasPtrs a where
  traversePtrs :: Applicative f => (PtrType -> RawPtr -> f RawPtr) -> a -> f a

takePtrSnapshot :: PtrType -> RawPtr -> IO PtrSnapshot
takePtrSnapshot _ ptrVal | ptrVal == nullPtr = return NullPtr
takePtrSnapshot (Heap CPU, ptrTy) ptrVal = case ptrTy of
  PtrType eltTy -> do
    childPtrs <- loadPtrPtrs ptrVal
    PtrArray <$> mapM (takePtrSnapshot eltTy) childPtrs
  _ -> ByteArray <$> loadPtrBytes ptrVal
takePtrSnapshot (Heap GPU, _) _ = error "Snapshots of GPU memory not implemented"
takePtrSnapshot (Stack   , _) _ = error "Can't take snapshots of stack memory"
{-# SCC takePtrSnapshot #-}

loadPtrBytes :: RawPtr -> IO BS.ByteString
loadPtrBytes ptr = do
  numBytes <- fromIntegral <$> dexAllocSize ptr
  liftM BS.pack $ peekArray numBytes $ castPtr ptr

loadPtrPtrs :: RawPtr -> IO [RawPtr]
loadPtrPtrs ptr = do
  numBytes <- fromIntegral <$> dexAllocSize ptr
  peekArray (numBytes `div` ptrSize) $ castPtr ptr

restorePtrSnapshot :: PtrSnapshot -> IO RawPtr
restorePtrSnapshot snapshot = case snapshot of
  PtrArray  children -> storePtrPtrs =<< mapM restorePtrSnapshot children
  ByteArray bytes    -> storePtrBytes bytes
  NullPtr            -> return nullPtr
{-# SCC restorePtrSnapshot #-}

storePtrBytes :: BS.ByteString -> IO RawPtr
storePtrBytes xs = do
  let numBytes = BS.length xs
  destPtr <- dexMalloc $ fromIntegral numBytes
  -- this is safe because we don't modify srcPtr's memory or let it escape
  unsafeUseAsCString xs \srcPtr ->
    memcpy (castPtr destPtr) (castPtr srcPtr) numBytes
  return destPtr

storePtrPtrs :: [RawPtr] -> IO RawPtr
storePtrPtrs ptrs = do
  ptr <- dexMalloc $ fromIntegral $ length ptrs * ptrSize
  pokeArray (castPtr ptr) ptrs
  return ptr

-- === instances ===

instance Store a => Store (WithSnapshot a)
