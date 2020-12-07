-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE CPP #-}

module Serialize (pprintVal, cached, getDexString) where

import Prelude hiding (pi, abs)
import Control.Monad
import qualified Data.ByteString as BS
import System.Directory
import System.FilePath
import Data.Foldable (toList)
import Data.Store hiding (size)
import Data.Text.Prettyprint.Doc  hiding (brackets)

import Interpreter
import Syntax
import Type
import PPrint
import Interpreter (indices)

pprintVal :: Val -> IO String
pprintVal val = asStr <$> prettyVal val

-- TODO: get the pointer rather than reading char by char
getDexString :: Val -> IO String
getDexString (DataCon _ _ 0 [_, xs]) = do
  let (TabTy b _) = getType xs
  idxs <- indices $ getType b
  forM idxs $ \i -> do
    ~(Con (Lit (Word8Lit c))) <- evalBlock mempty (Block Empty (App xs i))
    return $ toEnum $ fromIntegral c
getDexString x = error $ "Not a string: " ++ pprint x

-- This doesn't handle parentheses well. TODO: treat it more like PrettyPrec
prettyVal :: Val -> IO (Doc ann)
prettyVal val = case val of
  Lam abs@(Abs b (TabArrow, _)) -> do
    let idxSet = binderType b
    idxs <- indices idxSet
    elems <- forM idxs $ \idx -> do
      ans <- evalBlock mempty $ snd $ applyAbs abs idx
      asStr <$> prettyVal ans
    let idxSetStr = case idxSet of
                      FixedIntRange l _ | l == 0 -> mempty
                      _                          -> "@" <> pretty idxSet
    return $ pretty elems <> idxSetStr
  DataCon (DataDef _ _ dataCons) _ con args ->
    case args of
      [] -> return $ pretty conName
      _  -> do
        ans <- mapM prettyVal args
        return $ parens $ pretty conName <+> hsep ans
    where DataConDef conName _ = dataCons !! con
  Con con -> case con of
    PairCon x y -> do
      xStr <- asStr <$> prettyVal x
      yStr <- asStr <$> prettyVal y
      return $ pretty (xStr, yStr)
    SumAsProd ty (TagRepVal trep) payload -> do
      let t = fromIntegral trep
      case ty of
        TypeCon (DataDef _ _ dataCons) _ ->
          case args of
            [] -> return $ pretty conName
            _  -> do
              ans <- mapM prettyVal args
              return $ parens $ pretty conName <+> hsep ans
          where
            DataConDef conName _ = dataCons !! t
            args = payload !! t
        VariantTy (NoExt types) -> return $ pretty variant
          where
            [value] = payload !! t
            (theLabel, repeatNum) = toList (reflectLabels types) !! t
            variant = Variant (NoExt types) theLabel repeatNum value
        _ -> error "SumAsProd with an unsupported type"
    _ -> return $ pretty con
  atom -> return $ prettyPrec atom LowestPrec

-- TODO: this isn't enough, since this module's compilation might be cached
curCompilerVersion :: String
curCompilerVersion = __TIME__

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
