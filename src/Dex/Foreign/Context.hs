-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE RankNTypes #-}

module Dex.Foreign.Context (
  Context (..), AtomEx (..),
  setError, runTopperMFromContext,
  dexCreateContext, dexDestroyContext, dexForkContext,
  dexInsert, dexLookup,
  dexEval, dexFreshName,
  ) where

import Foreign.Ptr
import Foreign.StablePtr
import Foreign.C.String
import System.Random

import Control.Monad.IO.Class
import Data.Functor
import Data.Foldable
import Data.Map.Strict    qualified as M
import Data.ByteString    qualified as BS
import Data.Text.Encoding qualified as T

import Syntax  hiding (sizeOf)
import TopLevel
import Name
import PPrint
import Err
import AbstractSyntax
import Builder

import Dex.Foreign.Util


data Context = Context EvalConfig DexJIT TopStateEx
data AtomEx where
  AtomEx :: Atom n -> AtomEx

dexCreateContext :: IO (Ptr Context)
dexCreateContext = do
  let evalConfig = EvalConfig LLVM [LibBuiltinPath] Nothing Nothing Nothing Optimize
  cachedEnv <- loadCache
  jit <- createDexJIT
  runTopperM evalConfig jit cachedEnv (evalSourceBlockRepl preludeImportBlock) >>= \case
    (Result _  (Success  ()), preludeEnv) -> toStablePtr $ Context evalConfig jit preludeEnv
    (Result _  (Failure err), _         ) -> nullPtr <$
      setError ("Failed to initialize standard library: " ++ pprint err)

dexDestroyContext :: Ptr Context -> IO ()
dexDestroyContext = freeStablePtr . castPtrToStablePtr . castPtr

dexForkContext :: Ptr Context -> IO (Ptr Context)
dexForkContext ctxPtr = toStablePtr =<< fromStablePtr ctxPtr

runTopperMFromContext :: Ptr Context -> (forall n. Mut n => TopperM n a) -> IO (a, TopStateEx)
runTopperMFromContext ctxPtr cont = do
  Context evalConfig jit env <- fromStablePtr ctxPtr
  runTopperM evalConfig jit env cont

dexEval :: Ptr Context -> CString -> IO (Ptr Context)
dexEval ctxPtr sourcePtr = do
  source <- T.decodeUtf8 <$> BS.packCString sourcePtr
  (results, finalEnv) <- runTopperMFromContext ctxPtr $
    evalSourceText source (const $ return ()) (const $ return True)
  let anyError = asum $ fmap (\case (_, Result _ (Failure err)) -> Just err; _ -> Nothing) results
  Context evalConfig jit _ <- fromStablePtr ctxPtr
  case anyError of
    Nothing  -> toStablePtr $ Context evalConfig jit finalEnv
    Just err -> setError (pprint err) $> nullPtr

dexInsert :: Ptr Context -> CString -> Ptr AtomEx -> IO (Ptr Context)
dexInsert ctxPtr namePtr atomPtr = do
  sourceName <- peekCString namePtr
  AtomEx atom <- fromStablePtr atomPtr
  (_, finalEnv) <- runTopperMFromContext ctxPtr do
    -- TODO: Check if atom is compatible with context! Use module name?
    name <- emitTopLet (getNameHint @String sourceName) PlainLet $ Atom $ unsafeCoerceE atom
    emitSourceMap $ SourceMap $ M.singleton sourceName [ModuleVar Main $ Just $ UAtomVar name]
  Context evalConfig jit _ <- fromStablePtr ctxPtr
  toStablePtr $ Context evalConfig jit finalEnv

dexLookup :: Ptr Context -> CString -> IO (Ptr AtomEx)
dexLookup ctxPtr namePtr = do
  name <- peekCString namePtr
  fst <$> runTopperMFromContext ctxPtr do
    lookupSourceMap name >>= \case
      Just (UAtomVar v) -> lookupAtomName v >>= \case
        LetBound (DeclBinding _ _ (Atom atom)) -> liftIO $ toStablePtr $ AtomEx atom
        _ -> liftIO $ setError "Looking up an unevaluated atom?" $> nullPtr
      Just _  -> liftIO $ setError "Only Atom names can be looked up" $> nullPtr
      Nothing -> liftIO $ setError ("Unbound name: " ++ name) $> nullPtr

dexFreshName :: Ptr Context -> IO CString
dexFreshName ctxPtr = do
  Context evalConfig jit env <- fromStablePtr ctxPtr
  (cstr, _) <- runTopperM evalConfig jit env genName
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
