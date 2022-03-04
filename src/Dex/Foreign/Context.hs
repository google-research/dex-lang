-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}

module Dex.Foreign.Context (
  Context (..), AtomEx (..),
  setError,
  dexCreateContext, dexDestroyContext, dexForkContext,
  dexInsert, dexLookup,
  dexEval, dexFreshName,
  ) where

import Foreign.Ptr
import Foreign.StablePtr
import Foreign.C.String
import System.Random

import Control.Monad.IO.Class
import Data.String
import Data.Functor
import Data.Foldable
import qualified Data.Map.Strict as M

import Syntax  hiding (sizeOf)
import TopLevel
import Name
import PPrint
import Err
import Parser
import Builder

import Dex.Foreign.Util


data Context = Context EvalConfig TopStateEx
data AtomEx where
  AtomEx :: Atom n -> AtomEx

dexCreateContext :: IO (Ptr Context)
dexCreateContext = do
  let evalConfig = EvalConfig LLVM Nothing Nothing Nothing
  cachedEnv <- loadCache
  runTopperM evalConfig cachedEnv (evalSourceBlockRepl preludeImportBlock) >>= \case
    (Result [] (Success  ()), preludeEnv) -> toStablePtr $ Context evalConfig preludeEnv
    (Result _  (Failure err), _         ) -> nullPtr <$
      setError ("Failed to initialize standard library: " ++ pprint err)

dexDestroyContext :: Ptr Context -> IO ()
dexDestroyContext = freeStablePtr . castPtrToStablePtr . castPtr

dexForkContext :: Ptr Context -> IO (Ptr Context)
dexForkContext ctxPtr = toStablePtr =<< fromStablePtr ctxPtr

dexEval :: Ptr Context -> CString -> IO (Ptr Context)
dexEval ctxPtr sourcePtr = do
  Context evalConfig initEnv <- fromStablePtr ctxPtr
  source <- peekCString sourcePtr
  (results, finalEnv) <- runTopperM evalConfig initEnv $ evalSourceText source
  let anyError = asum $ fmap (\case (_, Result _ (Failure err)) -> Just err; _ -> Nothing) results
  case anyError of
    Nothing  -> toStablePtr $ Context evalConfig finalEnv
    Just err -> setError (pprint err) $> nullPtr

dexInsert :: Ptr Context -> CString -> Ptr AtomEx -> IO (Ptr Context)
dexInsert ctxPtr namePtr atomPtr = do
  Context evalConfig initEnv <- fromStablePtr ctxPtr
  sourceName <- peekCString namePtr
  AtomEx atom <- fromStablePtr atomPtr
  (_, finalEnv) <- runTopperM evalConfig initEnv do
    -- TODO: Check if atom is compatible with context! Use module name?
    name <- emitTopLet (fromString sourceName) PlainLet $ Atom $ unsafeCoerceE atom
    emitSourceMap $ SourceMap $ M.singleton sourceName [ModuleVar Main $ Just $ UAtomVar name]
  toStablePtr $ Context evalConfig finalEnv

dexLookup :: Ptr Context -> CString -> IO (Ptr AtomEx)
dexLookup ctxPtr namePtr = do
  Context evalConfig env <- fromStablePtr ctxPtr
  name <- peekCString namePtr
  fst <$> runTopperM evalConfig env do
    lookupSourceMap name >>= \case
      Just (UAtomVar v) -> lookupAtomName v >>= \case
        LetBound (DeclBinding _ _ (Atom atom)) -> liftIO $ toStablePtr $ AtomEx atom
        _ -> liftIO $ setError "Looking up an unevaluated atom?" $> nullPtr
      Just _  -> liftIO $ setError "Only Atom names can be looked up" $> nullPtr
      Nothing -> liftIO $ setError ("Unbound name: " ++ name) $> nullPtr

dexFreshName :: Ptr Context -> IO CString
dexFreshName ctxPtr = do
  Context evalConfig env <- fromStablePtr ctxPtr
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
