-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE CPP #-}

module Serialize (pprintVal, cached, getDexString, cachedWithSnapshot) where

import Prelude hiding (pi, abs)
import qualified Data.ByteString as BS
import Data.ByteString.Internal (memcpy)
import Data.ByteString.Unsafe (unsafeUseAsCString)
import System.Directory
import System.FilePath
import qualified Data.Map.Strict as M
import Data.Int
import Data.Store hiding (size)
import Data.Text.Prettyprint.Doc  hiding (brackets)
import Foreign.Ptr
import Foreign.Marshal.Array
import GHC.Generics (Generic)

import Preamble
import Base

import Interpreter
import Naming
import Syntax
import Type

import Inference -- TODO: remove

foreign import ccall "malloc_dex"           dexMalloc    :: Int64  -> IO (Ptr ())
foreign import ccall "dex_allocation_size"  dexAllocSize :: Ptr () -> IO Int64

pprintVal :: Atom n -> IO String
pprintVal val = docToStr <$> prettyVal val

-- TODO: get the pointer rather than reading char by char
getDexString :: Atom n -> IO String
-- getDexString (DataCon _ _ 0 [_, xs]) = do
--   let (TabTy b _) = getType xs
--   idxs <- indices $ getType b
--   forM idxs \i -> do
--     ~(Con (Lit (Word8Lit c))) <- evalBlock mempty (Block Empty (App xs i))
--     return $ toEnum $ fromIntegral c
getDexString x = error $ "Not a string: " ++ pprint x

-- Pretty-print values, e.g. for displaying in the REPL.
-- This doesn't handle parentheses well. TODO: treat it more like PrettyPrec
prettyVal :: Atom n -> IO (Doc ann)
prettyVal = undefined
-- prettyVal val = case val of
--   -- Pretty-print tables.
--   Lam abs@(Abs b (WithArrow _ body)) -> do
--     -- Pretty-print index set.
--     let idxSet = binderType b
--     let idxSetDoc = case idxSet of
--           Fin _ -> mempty               -- (Fin n) is not shown
--           _     -> "@" <> pretty idxSet -- Otherwise, show explicit index set
--     -- Pretty-print elements.
--     idxs <- indices idxSet
--     elems <- forM idxs \idx -> do
--       atom <- evalBlock mempty $ withoutArrow $ applyAbs abs idx
--       case atom of
--         Con (Lit (Word8Lit c)) ->
--           return $ showChar (toEnum @Char $ fromIntegral c) ""
--         _ -> pprintVal atom
--     let bodyType = getType body
--     let elemsDoc = case bodyType of
--           -- Print table of characters as a string literal.
--           TC (BaseType (Scalar Word8Type)) -> pretty ('"': concat elems ++ "\"")
--           _      -> pretty elems
--     return $ elemsDoc <> idxSetDoc
  -- DataCon (TypeDef _ _ dataCons) _ con args ->
  --   case args of
  --     [] -> return $ pretty conName
  --     _  -> do
  --       ans <- mapM prettyVal args
  --       return $ parens $ pretty conName <+> hsep ans
  --   where DataConDef conName _ = dataCons !! con
  -- Con con -> case con of
  --   PairCon x y -> do
  --     xStr <- pprintVal x
  --     yStr <- pprintVal y
  --     return $ pretty (xStr, yStr)
  --   -- SumAsProd ty (TagRepVal trep) payload -> do
  --   --   let t = fromIntegral trep
  --   --   case ty of
  --   --     TypeCon (TypeDef _ _ dataCons) _ ->
  --   --       case args of
  --   --         [] -> return $ pretty conName
  --   --         _  -> do
  --   --           ans <- mapM prettyVal args
  --   --           return $ parens $ pretty conName <+> hsep ans
  --   --       where
  --   --         DataConDef conName _ = dataCons !! t
  --   --         args = payload !! t
  --   --     VariantTy (NoExt types) -> return $ pretty variant
  --   --       where
  --   --         [value] = payload !! t
  --   --         (theLabel, repeatNum) = toList (reflectLabels types) !! t
  --   --         variant = Variant (NoExt types) theLabel repeatNum value
  --   --     _ -> error "SumAsProd with an unsupported type"
  --   _ -> return $ pretty con
  -- Record (LabeledItems row) -> do
  --   let separator = line' <> ","
  --   let bindwith = " ="
  --   let elems = concatMap (\(k, vs) -> map (k,) (toList vs)) (M.toAscList row)
  --   let fmElem = \(label, v) -> ((pretty label <> bindwith) <+>) <$> prettyVal v
  --   docs <- mapM fmElem elems
  --   let innerDoc = "{" <> flatAlt " " ""
  --         <> concatWith (surround (separator <> " ")) docs
  --         <> "}"
  --   return $ align $ group innerDoc
  -- atom -> return $ prettyPrec atom LowestPrec

-- === taking memory snapshots for serializing heap-backed dex values ===


data WithSnapshot a = WithSnapshot a [PtrSnapshot]  deriving Generic
instance Store a => Store (WithSnapshot a)

type RawPtr = Ptr ()
-- TODO: we could consider using some mmap-able instead of ByteString
data PtrSnapshot = ByteArray BS.ByteString
                 | PtrArray [PtrSnapshot]
                 | NullPtr  deriving Generic
instance Store PtrSnapshot

-- TODO: this is currently a no-op since we removed the `HasPtrs` class. We want
-- to revive it by putting pointer literals in the bindings instead of in atoms.

takeSnapshot :: a -> IO (WithSnapshot a)
takeSnapshot x = return $ WithSnapshot x []
-- takeSnapshot x =
--   -- TODO: we're using `Writer []` (as we do elsewhere) which has bad
--   -- asymptotics. We should switch all of these uses to use snoc lists instead.
--   liftM (WithSnapshot x) $ execWriterT $ flip traversePtrs x \ptrTy ptrVal -> do
--     snapshot <- lift $ takePtrSnapshot ptrTy ptrVal
--     tell [snapshot]
--     return ptrVal

takePtrSnapshot :: PtrType -> RawPtr -> IO PtrSnapshot
takePtrSnapshot _ ptrVal | ptrVal == nullPtr = return NullPtr
takePtrSnapshot (Heap CPU, ptrTy) ptrVal = case ptrTy of
  PtrType eltTy -> do
    childPtrs <- loadPtrPtrs ptrVal
    PtrArray <$> mapM (takePtrSnapshot eltTy) childPtrs
  _ -> ByteArray <$> loadPtrBytes ptrVal
takePtrSnapshot (Heap GPU, _) _ = error "Snapshots of GPU memory not implemented"
takePtrSnapshot (Stack   , _) _ = error "Can't take snapshots of stack memory"

loadPtrBytes :: RawPtr -> IO BS.ByteString
loadPtrBytes ptr = do
  numBytes <- fromIntegral <$> dexAllocSize ptr
  liftM BS.pack $ peekArray numBytes $ castPtr ptr

loadPtrPtrs :: RawPtr -> IO [RawPtr]
loadPtrPtrs ptr = do
  numBytes <- fromIntegral <$> dexAllocSize ptr
  peekArray (numBytes `div` ptrSize) $ castPtr ptr

restoreSnapshot :: WithSnapshot a -> IO a
restoreSnapshot (WithSnapshot x _) = return x

restorePtrSnapshot :: PtrSnapshot -> IO RawPtr
restorePtrSnapshot snapshot = case snapshot of
  PtrArray  children -> storePtrPtrs =<< mapM restorePtrSnapshot children
  ByteArray bytes    -> storePtrBytes bytes
  NullPtr            -> return nullPtr

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

-- === persistent cache ===

-- TODO: this isn't enough, since this module's compilation might be cached
curCompilerVersion :: String
curCompilerVersion = __TIME__

cachedWithSnapshot :: (Eq k, Store k, Store a) => String -> k -> IO a -> IO a
cachedWithSnapshot cacheName key create = do
  result <- cached cacheName key $ create >>= takeSnapshot
  restoreSnapshot result

cached :: (Eq k, Store k, Store a) => String -> k -> IO a -> IO a
cached cacheName key create = do
  cacheDir <- getXdgDirectory XdgCache "dex"
  createDirectoryIfMissing True cacheDir
  let cacheKeyPath = cacheDir </> (cacheName ++ ".key")
  let cachePath    = cacheDir </> (cacheName ++ ".cache")
  cacheExists <- (&&) <$> doesFileExist cacheKeyPath <*> doesFileExist cachePath
  cacheUpToDate <- case cacheExists of
                     False -> return False
                     True -> do
                       maybeCacheKey <- decode <$> BS.readFile cacheKeyPath
                       case maybeCacheKey of
                         Right cacheKey -> return $ cacheKey == (curCompilerVersion, key)
                         Left  _        -> return False
  if cacheUpToDate
    then do
      decoded <- decode <$> BS.readFile cachePath
      case decoded of
        Right result -> return result
        _            -> removeFile cachePath >> cached cacheName key create
    else do
      result <- create
      BS.writeFile cacheKeyPath $ encode (curCompilerVersion, key)
      BS.writeFile cachePath    $ encode result
      return result
