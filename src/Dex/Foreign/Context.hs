-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE RankNTypes #-}

module Dex.Foreign.Context (
  Context (..), AtomEx (..), ExportNativeFunctionAddr, ExportNativeFunction (..),
  ClosedExportedSignature,
  setError, runTopperMFromContext,
  dexCreateContext, dexDestroyContext, dexForkContext,
  dexInsert, dexLookup,
  dexEval, dexFreshName, insertIntoNativeFunctionTable, popFromNativeFunctionTable,
  intAsCC, emitExport
  ) where

import Foreign.C
import Foreign.Ptr
import Foreign.StablePtr
import System.Random

import Control.Monad.IO.Class
import Control.Concurrent.MVar
import Data.Functor
import Data.Foldable
import Data.Map.Strict    qualified as M
import Data.ByteString    qualified as BS
import Data.Text.Encoding qualified as T

import ConcreteSyntax
import Builder
import Core
import Err
import Export
import IRVariants
import Name
import TopLevel
import Types.Core
import Types.Imp
import Types.Misc
import Types.Primitives
import Types.Source

import Dex.Foreign.Util

data Context = Context EvalConfig (MVar TopStateEx) (MVar NativeFunctionTable)

type ClosedExportedSignature = ExportedSignature 'VoidS

type ExportNativeFunctionAddr = FunPtr () -- points to executable code
type NativeFunctionTable = M.Map ExportNativeFunctionAddr ExportNativeFunction

data AtomEx where
  AtomEx :: Atom CoreIR n -> AtomEx

dexCreateContext :: IO (Ptr Context)
dexCreateContext = do
  let cfg = EvalConfig LLVM [LibBuiltinPath] Nothing Nothing Nothing Optimize PrintCodegen
  cachedEnv <- loadCache
  envMVar      <- newMVar cachedEnv
  ptrTableMVar <- newMVar mempty
  ctxPtr <- toStablePtr $ Context cfg envMVar ptrTableMVar
  _ <- runTopperMFromContext ctxPtr $ evalSourceBlockRepl preludeImportBlock
  return ctxPtr

dexDestroyContext :: Ptr Context -> IO ()
dexDestroyContext = freeStablePtr . castPtrToStablePtr . castPtr

dexForkContext :: Ptr Context -> IO (Ptr Context)
dexForkContext ctxPtr = do
  Context cfg envMVar ptrTabMVar <- fromStablePtr ctxPtr
  envMVar'    <- copyMVar envMVar
  ptrTabMVar' <- copyMVar ptrTabMVar
  toStablePtr $ Context cfg envMVar' ptrTabMVar'

-- XXX: this holds the lock on the mvar for the whole duration. TODO: consider
-- implementing a new instance of `Topper`, backed by an mvar, that only holds
-- the lock when it actually needs to update the env.
runTopperMFromContext :: Ptr Context -> (forall n. Mut n => TopperM n a) -> IO a
runTopperMFromContext ctxPtr cont = do
  Context cfg envMVar _ <- fromStablePtr ctxPtr
  env <- takeMVar envMVar
  (result, newEnv) <- runTopperM cfg env cont
  putMVar envMVar newEnv
  return result
{-# INLINE runTopperMFromContext #-}

dexEval :: Ptr Context -> CString -> IO CInt
dexEval ctxPtr sourcePtr = do
  source <- T.decodeUtf8 <$> BS.packCString sourcePtr
  Context cfg envMVar _ <- fromStablePtr ctxPtr
  oldEnv <- takeMVar envMVar
  (results, newEnv) <- runTopperM cfg oldEnv $
    evalSourceText source (const $ return ()) (const $ return True)
  let anyError = asum $ fmap (\case (_, Result _ (Failure err)) -> Just err; _ -> Nothing) results
  case anyError of
    Nothing  -> putMVar envMVar newEnv                          >> return 0
    Just err -> putMVar envMVar oldEnv >> setError (pprint err) >> return 1

dexInsert :: Ptr Context -> CString -> Ptr AtomEx -> IO ()
dexInsert ctxPtr namePtr atomPtr = do
  sourceName <- peekCString namePtr
  AtomEx atom <- fromStablePtr atomPtr
  runTopperMFromContext ctxPtr do
    -- TODO: Check if atom is compatible with context! Use module name?
    name <- emitTopLet (getNameHint @String sourceName) PlainLet $ Atom $ unsafeCoerceE atom
    emitSourceMap $ SourceMap $ M.singleton sourceName [ModuleVar Main $ Just $ UAtomVar name]

dexLookup :: Ptr Context -> CString -> IO (Ptr AtomEx)
dexLookup ctxPtr namePtr = do
  name <- peekCString namePtr
  runTopperMFromContext ctxPtr do
    lookupSourceMap name >>= \case
      Just (UAtomVar v) -> lookupAtomName v >>= \case
        LetBound (DeclBinding _ _ (Atom atom)) -> liftIO $ toStablePtr $ AtomEx atom
        _ -> liftIO $ setError "Looking up an unevaluated atom?" $> nullPtr
      Just _  -> liftIO $ setError "Only Atom names can be looked up" $> nullPtr
      Nothing -> liftIO $ setError ("Unbound name: " ++ name) $> nullPtr

dexFreshName :: Ptr Context -> IO CString
dexFreshName ctxPtr = do
  Context evalConfig envMVar _  <- fromStablePtr ctxPtr
  env <- readMVar envMVar
  (cstr, _) <- runTopperM evalConfig env genName
  return cstr
  where
    genName :: Topper m => m n CString
    genName = do
      -- TODO: Find a thread-safe way?
      i <- show . abs <$> liftIO (randomIO @Int)
      let name = "D_" ++ i ++ "_INTERNAL_NAME"
      lookupSourceMap name >>= \case
        Nothing -> liftIO $ newCString name
        Just _  -> genName

insertIntoNativeFunctionTable
  :: Ptr Context -> ExportNativeFunctionAddr -> ExportNativeFunction -> IO ()
insertIntoNativeFunctionTable ctxPtr funPtr funData = do
  Context _ _ addrTableMVar  <- fromStablePtr ctxPtr
  modifyMVar addrTableMVar (\m -> return (M.insert funPtr funData m, ()))

popFromNativeFunctionTable
  :: Ptr Context -> ExportNativeFunctionAddr -> IO ExportNativeFunction
popFromNativeFunctionTable ctxPtr funcPtr = do
  Context _ _ ptrTabMVar <- fromStablePtr ctxPtr
  addrTable <- takeMVar ptrTabMVar
  putMVar ptrTabMVar $  M.delete funcPtr addrTable
  return $ addrTable M.! funcPtr

intAsCC :: CInt -> CallingConvention
intAsCC 0 = StandardCC
intAsCC 1 = XLACC
intAsCC _ = error "Unrecognized calling convention"

emitExport :: Ptr Context -> ExportNativeFunction -> IO ExportNativeFunctionAddr
emitExport ctxPtr func = do
  let funcPtr = nativeFunPtr $ nativeFunction func
  insertIntoNativeFunctionTable ctxPtr funcPtr func
  return funcPtr
