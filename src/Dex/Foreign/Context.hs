-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Dex.Foreign.Context (
  Context (..),
  setError,
  dexCreateContext, dexDestroyContext,
  dexInsert, dexLookup,
  dexEval, dexEvalExpr,
  ) where

import Control.Monad.State.Strict

import Foreign.Ptr
import Foreign.StablePtr
import Foreign.C.String

import Data.String
import Data.Int
import Data.Functor
import Data.Foldable

import Resources
import Syntax  hiding (sizeOf)
import Type
import TopLevel
import Parser (parseExpr, exprAsModule)
import Env hiding (Tag)
import PPrint

import Dex.Foreign.Util

data Context = Context EvalConfig TopEnv

foreign import ccall "_internal_dexSetError" internalSetErrorPtr :: CString -> Int64 -> IO ()
setError :: String -> IO ()
setError msg = withCStringLen msg $ \(ptr, len) ->
  internalSetErrorPtr ptr (fromIntegral len)

dexCreateContext :: IO (Ptr Context)
dexCreateContext = do
  let evalConfig = EvalConfig LLVM Nothing
  maybePreludeEnv <- evalPrelude evalConfig preludeSource
  case maybePreludeEnv of
    Right preludeEnv -> toStablePtr $ Context evalConfig preludeEnv
    Left  err        -> nullPtr <$ setError ("Failed to initialize standard library: " ++ pprint err)
  where
    evalPrelude :: EvalConfig -> String -> IO (Either Err TopEnv)
    evalPrelude opts contents = flip evalStateT initTopEnv $ do
      results <- fmap snd <$> evalSource opts contents
      env <- get
      return $ env `unlessError` results
      where
        unlessError :: TopEnv -> [Result] -> Except TopEnv
        result `unlessError` []                        = Right result
        _      `unlessError` ((Result _ (Left err)):_) = Left err
        result `unlessError` (_:t                    ) = result `unlessError` t

dexDestroyContext :: Ptr Context -> IO ()
dexDestroyContext = freeStablePtr . castPtrToStablePtr . castPtr

dexEval :: Ptr Context -> CString -> IO (Ptr Context)
dexEval ctxPtr sourcePtr = do
  Context evalConfig env <- fromStablePtr ctxPtr
  source <- peekCString sourcePtr
  (results, finalEnv) <- runStateT (evalSource evalConfig source) env
  let anyError = asum $ fmap (\case (_, Result _ (Left err)) -> Just err; _ -> Nothing) results
  case anyError of
    Nothing  -> toStablePtr $ Context evalConfig finalEnv
    Just err -> setError (pprint err) $> nullPtr

dexInsert :: Ptr Context -> CString -> Ptr Atom -> IO (Ptr Context)
dexInsert ctxPtr namePtr atomPtr = do
  Context evalConfig env <- fromStablePtr ctxPtr
  name <- GlobalName . fromString <$> peekCString namePtr
  atom <- fromStablePtr atomPtr
  let env' = env <> name @> (getType atom, LetBound PlainLet (Atom atom))
  toStablePtr $ Context evalConfig env'

dexEvalExpr :: Ptr Context -> CString -> IO (Ptr Atom)
dexEvalExpr ctxPtr sourcePtr = do
  Context evalConfig env <- fromStablePtr ctxPtr
  source <- peekCString sourcePtr
  case parseExpr source of
    Right expr -> do
      let (v, m) = exprAsModule expr
      let block = SourceBlock 0 0 LogNothing source (RunModule m) Nothing
      (resultEnv, Result [] maybeErr) <- evalSourceBlock evalConfig env block
      case maybeErr of
        Right () -> do
          let (_, LetBound _ (Atom atom)) = resultEnv ! v
          toStablePtr atom
        Left err -> setError (pprint err) $> nullPtr
    Left err -> setError (pprint err) $> nullPtr

dexLookup :: Ptr Context -> CString -> IO (Ptr Atom)
dexLookup ctxPtr namePtr = do
  Context _ env <- fromStablePtr ctxPtr
  name <- peekCString namePtr
  case envLookup env (GlobalName $ fromString name) of
    Just (_, LetBound _ (Atom atom)) -> toStablePtr atom
    Just _                           -> setError "Looking up an expression" $> nullPtr
    Nothing                          -> setError "Unbound name" $> nullPtr

