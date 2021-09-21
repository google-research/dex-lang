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

import Foreign.Ptr
import Foreign.StablePtr
import Foreign.C.String

import Data.String
import Data.Int
import Data.Functor
import Data.Foldable
import qualified Data.Map.Strict as M

import Resources
import Syntax  hiding (sizeOf)
import Type
import TopLevel
import Parser (parseExpr, exprAsModule)
import Env hiding (Tag)
import PPrint
import Err

import Dex.Foreign.Util

import SaferNames.Bridge

data Context = Context EvalConfig TopStateEx

foreign import ccall "_internal_dexSetError" internalSetErrorPtr :: CString -> Int64 -> IO ()
setError :: String -> IO ()
setError msg = withCStringLen msg $ \(ptr, len) ->
  internalSetErrorPtr ptr (fromIntegral len)

dexCreateContext :: IO (Ptr Context)
dexCreateContext = do
  let evalConfig = EvalConfig LLVM Nothing Nothing
  maybePreludeEnv <- evalPrelude evalConfig preludeSource
  case maybePreludeEnv of
    Success preludeEnv -> toStablePtr $ Context evalConfig preludeEnv
    Failure  err       -> nullPtr <$ setError ("Failed to initialize standard library: " ++ pprint err)
  where
    evalPrelude :: EvalConfig -> String -> IO (Except TopStateEx)
    evalPrelude opts sourceText = do
      (results, env) <- runInterblockM opts initTopState $
                            map snd <$> evalSourceText sourceText
      return $ env `unlessError` results
      where
        unlessError :: TopStateEx -> [Result] -> Except TopStateEx
        result `unlessError` []                        = Success result
        _      `unlessError` ((Result _ (Failure err)):_) = Failure err
        result `unlessError` (_:t                       ) = result `unlessError` t

dexDestroyContext :: Ptr Context -> IO ()
dexDestroyContext = freeStablePtr . castPtrToStablePtr . castPtr

dexEval :: Ptr Context -> CString -> IO (Ptr Context)
dexEval ctxPtr sourcePtr = do
  Context evalConfig env <- fromStablePtr ctxPtr
  source <- peekCString sourcePtr
  (results, finalEnv) <- runInterblockM evalConfig env $ evalSourceText source
  let anyError = asum $ fmap (\case (_, Result _ (Failure err)) -> Just err; _ -> Nothing) results
  case anyError of
    Nothing  -> toStablePtr $ Context evalConfig finalEnv
    Just err -> setError (pprint err) $> nullPtr

dexInsert :: Ptr Context -> CString -> Ptr Atom -> IO (Ptr Context)
dexInsert ctxPtr namePtr atomPtr = do
  Context evalConfig (TopStateEx env) <- fromStablePtr ctxPtr
  name <- fromString <$> peekCString namePtr
  atom <- fromStablePtr atomPtr
  let freshName = genFresh (Name GenName (fromString name) 0) (topBindings $ topStateD env)
  let newBinding = AtomBinderInfo (getType atom) (LetBound PlainLet (Atom atom))
  let evaluated = EvaluatedModule (freshName @> newBinding) mempty
                                  (SourceMap (M.singleton name (SrcAtomName freshName)))
  let envNew = extendTopStateD env evaluated
  toStablePtr $ Context evalConfig $ envNew

dexEvalExpr :: Ptr Context -> CString -> IO (Ptr Atom)
dexEvalExpr ctxPtr sourcePtr = do
  Context evalConfig env <- fromStablePtr ctxPtr
  source <- peekCString sourcePtr
  case parseExpr source of
    Success expr -> do
      let (v, m) = exprAsModule expr
      let block = SourceBlock 0 0 LogNothing source (RunModule m) Nothing
      (Result [] maybeErr, newState) <- runInterblockM evalConfig env $ evalSourceBlock block
      case maybeErr of
        Success () -> do
          let Success (AtomBinderInfo _ (LetBound _ (Atom atom))) =
                lookupSourceName newState v
          toStablePtr atom
        Failure err -> setError (pprint err) $> nullPtr
    Failure err -> setError (pprint err) $> nullPtr

dexLookup :: Ptr Context -> CString -> IO (Ptr Atom)
dexLookup ctxPtr namePtr = do
  Context _ env <- fromStablePtr ctxPtr
  name <- peekCString namePtr
  case lookupSourceName env (fromString name) of
    Success (AtomBinderInfo _ (LetBound _ (Atom atom))) -> toStablePtr atom
    Failure _ -> setError "Unbound name" $> nullPtr
    Success _ -> setError "Looking up an expression" $> nullPtr
