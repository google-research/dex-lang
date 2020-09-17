-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Serialize (pprintVal, memoizeFileEval) where

import Prelude hiding (pi, abs)
import Control.Monad
import qualified Data.ByteString as BS
import System.Directory
import System.IO.Error
import Data.Foldable (toList)
import Data.Store hiding (size)
import Data.Text.Prettyprint.Doc  hiding (brackets)

import Interpreter
import Simplify
import Type hiding (indexSetConcreteSize)
import Syntax
import PPrint
import Interpreter (indices)

pprintVal :: Val -> IO String
pprintVal val = asStr <$> prettyVal val

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

memoizeFileEval :: Store a => FilePath -> (FilePath -> IO a) -> FilePath -> IO a
memoizeFileEval cacheFile f fname = do
  cacheFresh <- cacheFile `newerFileThan` fname
  if cacheFresh
    then do
      decoded <- decode <$> BS.readFile cacheFile
      case decoded of
        Right (version, result) | version == curCompilerVersion -> return result
        _ -> removeFile cacheFile >> memoizeFileEval cacheFile f fname
    else do
      result <- f fname
      BS.writeFile cacheFile (encode (curCompilerVersion, result))
      return result

newerFileThan :: FilePath -> FilePath -> IO Bool
newerFileThan f1 f2 = flip catchIOError (const $ return False) $ do
  f1Mod <- getModificationTime f1
  f2Mod <- getModificationTime f2
  return $ f1Mod > f2Mod
