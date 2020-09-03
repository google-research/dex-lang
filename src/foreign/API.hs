-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE TemplateHaskell #-}

module API where

import Control.Monad.State.Strict

import Foreign.Ptr
import Foreign.StablePtr
import Foreign.C.Types
import Foreign.C.String

import qualified Data.ByteString.Char8 as B
import Data.FileEmbed

import Syntax
import TopLevel
import PPrint

foreign export ccall "dexCreateContext" dexCreateContext :: IO (Ptr ())
foreign export ccall "dexDestroyContext" dexDestroyContext :: Ptr () -> IO ()
foreign export ccall "dexEval" dexEval :: Ptr () -> CString -> IO ()

data Context = Context EvalConfig TopEnv

dexCreateContext :: IO (Ptr ())
dexCreateContext = do
    backend <- initializeBackend LLVM
    let evalConfig = EvalConfig Nothing backend (error "Logging not initialized")
    maybePreludeEnv <- evalPrelude evalConfig preludeSource
    case maybePreludeEnv of
      Right preludeEnv -> castStablePtrToPtr <$> newStablePtr (Context evalConfig preludeEnv)
      Left err         -> return nullPtr
  where
    preludeSource = B.unpack $ $(embedFile "prelude.dx")

evalPrelude :: EvalConfig -> FilePath -> IO (Either Err TopEnv)
evalPrelude opts fname = flip evalStateT mempty $ do
  results <- fmap snd <$> evalSource opts fname
  env <- get
  return $ env `unlessError` results
  where
    unlessError :: TopEnv -> [Result] -> Except TopEnv
    result `unlessError` []                        = Right result
    result `unlessError` ((Result _ (Left err)):_) = Left err
    result `unlessError` (_:t                    ) = result `unlessError` t

dexDestroyContext :: Ptr () -> IO ()
dexDestroyContext = freeStablePtr . castPtrToStablePtr @Context

dexEval :: Ptr () -> CString -> IO ()
dexEval ctxPtr sourcePtr = do
  Context evalConfig env <- deRefStablePtr $ castPtrToStablePtr ctxPtr
  source <- peekCString sourcePtr
  results <- evalStateT (evalSource evalConfig source) env
  putStr $ foldMap (nonEmptyNewline . pprint . snd) results
  where
    nonEmptyNewline [] = []
    nonEmptyNewline l  = l ++ ['\n']
