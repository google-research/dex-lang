-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Serialize (HasPtrs (..), takePtrSnapshot, restorePtrSnapshot) where

import Prelude hiding (pi, abs)
import Control.Monad
import qualified Data.ByteString as BS
import Data.ByteString.Internal (memcpy)
import Data.ByteString.Unsafe (unsafeUseAsCString)
import Data.Int
import Data.Store hiding (size)
import Foreign.Ptr
import Foreign.Marshal.Array
import GHC.Generics (Generic)

import Types.Primitives

foreign import ccall "malloc_dex"           dexMalloc    :: Int64  -> IO (Ptr ())
foreign import ccall "dex_allocation_size"  dexAllocSize :: Ptr () -> IO Int64

data WithSnapshot a = WithSnapshot a [PtrSnapshot]  deriving Generic
type RawPtr = Ptr ()

class HasPtrs a where
  traversePtrs :: Applicative f => (PtrType -> RawPtr -> f RawPtr) -> a -> f a

takePtrSnapshot :: PtrType -> PtrLitVal -> IO PtrLitVal
takePtrSnapshot _ NullPtr = return NullPtr
takePtrSnapshot (CPU, ptrTy) (PtrLitVal ptrVal) = case ptrTy of
  PtrType eltTy -> do
    childPtrs <- loadPtrPtrs ptrVal
    PtrSnapshot <$> PtrArray <$> mapM (takePtrSnapshot eltTy) childPtrs
  _ -> PtrSnapshot . ByteArray <$> loadPtrBytes ptrVal
takePtrSnapshot (GPU, _) _ = error "Snapshots of GPU memory not implemented"
takePtrSnapshot _ (PtrSnapshot _) = error "Already a snapshot"
{-# SCC takePtrSnapshot #-}

loadPtrBytes :: RawPtr -> IO BS.ByteString
loadPtrBytes ptr = do
  numBytes <- fromIntegral <$> dexAllocSize ptr
  liftM BS.pack $ peekArray numBytes $ castPtr ptr

loadPtrPtrs :: RawPtr -> IO [PtrLitVal]
loadPtrPtrs ptr = do
  numBytes <- fromIntegral <$> dexAllocSize ptr
  childPtrs <- peekArray (numBytes `div` ptrSize) $ castPtr ptr
  forM childPtrs \childPtr ->
    if childPtr == nullPtr
      then return NullPtr
      else return $ PtrLitVal childPtr

restorePtrSnapshot :: PtrLitVal -> IO PtrLitVal
restorePtrSnapshot NullPtr = return NullPtr
restorePtrSnapshot (PtrSnapshot snapshot) = case snapshot of
  PtrArray  children -> do
    childrenPtrs <- forM children \child ->
      restorePtrSnapshot child >>= \case
        NullPtr -> return nullPtr
        PtrLitVal p -> return p
        PtrSnapshot _ -> error "expected a pointer literal"
    PtrLitVal <$> storePtrPtrs childrenPtrs
  ByteArray bytes -> PtrLitVal <$> storePtrBytes bytes
restorePtrSnapshot (PtrLitVal _) = error "not a snapshot"
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
