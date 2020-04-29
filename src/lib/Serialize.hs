-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}

module Serialize (DBOHeader (..), dumpDataFile, loadDataFile, pprintVal,
                 valToHeatmap, valToScatter) where

import Control.Monad
import Control.Monad.Writer
import Control.Monad.State
import Control.Exception (throwIO)
import Foreign.Ptr
import qualified Data.ByteString.Char8 as B
import System.IO
import System.IO.MMap
import System.Posix  hiding (ReadOnly)
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import Data.Text.Prettyprint.Doc  hiding (brackets)

import Array
import Type
import Syntax
import PPrint
import Parser

data DBOHeader = DBOHeader
  { objectType     :: Type
  , bufferSizes    :: [Int] }

preHeaderLength :: Int
preHeaderLength = 81

preHeaderStart :: String
preHeaderStart = "-- dex-object-file-v0.0.1 num-header-bytes "

dumpDataFile :: FilePath -> Val -> IO ()
dumpDataFile fname val = do
  arrayRefs <- mapM allocStoreArray $ getValArrays val
  let ty = getType val
  withFile fname WriteMode $ \h -> do
    putBytes h $ serializeFullHeader $ createHeader ty arrayRefs
    mapM_ (writeArrayToFile h) arrayRefs

loadDataFile :: FilePath -> IO Val
loadDataFile fname = do
   -- TODO: check lengths are consistent with type
  (n, header@(DBOHeader ty sizes)) <- readHeader fname
  actualSize <- liftM (fromIntegral . fileSize) $ getFileStatus fname
  liftExceptIO $ validateFile n actualSize header
  filePtr <- memmap fname
  let firstPtr = filePtr `plusPtr` n
  let ptrs = init $ scanl plusPtr firstPtr sizes
  -- TODO: typecheck result
  valFromPtrs ty ptrs

memmap :: FilePath -> IO (Ptr ())
memmap fname = do
  (ptr, _, offset, _) <- mmapFilePtr fname ReadOnly Nothing
  return $ ptr `plusPtr` offset

readHeader :: FilePath -> IO (Int, DBOHeader)
readHeader fname = do
  withFile fname ReadMode $ \h -> do
    headerLength <- parseFile h preHeaderLength parsePreHeader
    header <- parseFile h (headerLength - preHeaderLength) parseHeader
    return (headerLength, header)

serializeFullHeader :: DBOHeader -> String
serializeFullHeader header = preHeaderPrefix <> padding <> body
  where
    body = serializeHeader header
    headerSize = preHeaderLength + length body
    preHeaderPrefix = preHeaderStart <> show headerSize <> " "
    padding = replicate (preHeaderLength - length preHeaderPrefix - 1) '-' <> "\n"

serializeHeader :: DBOHeader -> String
serializeHeader (DBOHeader ty sizes) =  "type: "        <> pprint ty    <> "\n"
                                     <> "bufferSizes: " <> show sizes   <> "\n"

createHeader :: Type -> [Array] -> DBOHeader
createHeader ty arrays = DBOHeader ty sizes
  where sizes = [8 * product shape | Array shape _ _ <- arrays]

putBytes :: Handle -> String -> IO ()
putBytes h s = B.hPut h $ B.pack s

parseFile :: Handle -> Int -> Parser a -> IO a
parseFile h n p = do
  s <- liftM B.unpack $ B.hGet h n
  return $ ignoreExcept $ parseit s p

parsePreHeader :: Parser Int
parsePreHeader = do
  symbol preHeaderStart
  n <- uint
  void $ many (char '-')
  void $ char '\n'
  return n

parseHeader :: Parser DBOHeader
parseHeader = do
  emptyLines
  ty <- symbol "type:" >> tauType <* eol
  emptyLines
  sizes <-  symbol "bufferSizes:" >> brackets (uint `sepBy1` symbol ",") <* eol
  emptyLines
  return $ DBOHeader ty sizes

writeArrayToFile :: Handle -> Array -> IO ()
writeArrayToFile h (Array shape _ ptr) = hPutBuf h ptr (size * 8)
  where size = product shape

validateFile :: Int -> Int -> DBOHeader -> Except ()
validateFile headerLength fileLength header@(DBOHeader ty sizes) =
  addContext ctx $ do
     let minSizes = [product shape * 8 | (_, shape) <- flattenType ty]
     when (length minSizes /= length sizes) $ throw DataIOErr $
       "unexpected number of buffers: " <> show minSizes <> " vs " <> show sizes <> "\n"
     zipWithM_ checkBufferSize minSizes sizes
     when (claimedLength /= fileLength) $ throw DataIOErr $ "wrong file size\n"
  where
    claimedLength = headerLength + sum sizes
    ctx =   "Validation error\n"
         <> "Claimed header length: " <> show headerLength <> "\n"
         <> "Claimed total length:  " <> show claimedLength <> "\n"
         <> "Actual file length:    " <> show fileLength   <> "\n"
         <> "Header data:\n" <> serializeHeader header

checkBufferSize :: Int -> Int -> Except ()
checkBufferSize minSize size = when (size < minSize) $ throw DataIOErr $
   "buffer too small: " <> show size <> " < " <> show minSize

valFromPtrs :: Type -> [Ptr ()] -> IO Val
valFromPtrs ty = evalStateT (valFromPtrs' [] ty)

valFromPtrs' :: [Int] -> Type -> StateT [Ptr ()] IO Val
valFromPtrs' shape ty@(TC con) = case con of
  BaseType b -> do
    ~(ptr:ptrs) <- get
    put ptrs
    arrayVal <- liftIO $ loadArray $ Array shape b ptr
    return $ Con $ AGet $ Con $ ArrayLit $ arrayVal
  RecType r -> liftM (Con . RecCon) $ traverse (valFromPtrs' shape) r
  TabType idx@(FixedIntRange low high) a ->
    liftM (Con . AFor idx) $ valFromPtrs' (shape ++ [(high - low)]) a
  IntRange _ _ -> do
    liftM (Con . AsIdx ty) $ valFromPtrs' shape (TC $ BaseType IntType)
  _ -> error $ "Not implemented: " ++ pprint ty
valFromPtrs' _ ty = error $ "Not implemented: " ++ pprint ty

type PrimConVal = PrimCon Type Atom LamExpr

valToScatter :: Val -> IO Output
valToScatter ~(Con (AFor _ body)) = return $ ScatterOut xs' ys'
  where
    ~(PairVal (Con (AGet (Con (ArrayLit (ArrayLitVal _ _ xs)))))
              (Con (AGet (Con (ArrayLit (ArrayLitVal _ _ ys)))))) = body
    xs' = map fromRealLit xs
    ys' = map fromRealLit ys

valToHeatmap :: Val -> IO Output
valToHeatmap ~(Con (AFor (FixedIntRange hl hh) body)) = do
  array' <- allocStoreArray array
  xs <- sequence [liftM fromRealLit $ loadScalar (subArray j (subArray i array'))
                 | i <- [0..h-1], j <- [0..w-1]]
  return $ HeatmapOut h w xs
  where ~(Con (AFor (FixedIntRange wl wh) (Con (AGet (Con (ArrayLit array)))))) = body
        h = hh - hl
        w = wh - wl

fromRealLit :: LitVal -> Double
fromRealLit ~(RealLit x) = x

pprintVal :: Val -> IO String
pprintVal val = liftM asStr $ prettyVal val

prettyVal :: Val -> IO (Doc ann)
prettyVal (Con con) = case con of
  RecCon r -> liftM pretty $ traverse (liftM asStr . prettyVal) r
  AFor n body -> do
    xs <- flip mapM [0..n'-1] $ \i ->
      liftM asStr $ prettyVal $ litIndexSubst i body
    return $ pretty xs <> idxSetStr
    where
      (Just n') = indexSetConcreteSize n
      idxSetStr = case n of FixedIntRange 0 _ -> mempty
                            _                 -> "@" <> pretty n
  AGet (Con (ArrayLit (ArrayLitVal _ _ [x]))) -> return $ pretty x
  AsIdx n i -> do
    i' <- prettyVal i
    return $ i' <> "@" <> pretty n
  Lit x -> return $ pretty x
  _ -> return $ pretty con
prettyVal atom = error $ "Unexpected value: " ++ pprint atom

litIndexSubst :: Int -> Atom -> Atom
litIndexSubst i atom = case atom of
  Con (ArrayLit x) -> Con $ ArrayLit $ subArrayVal i x
  Con con -> Con $ fmapExpr con id (litIndexSubst i) (error "unexpected lambda")
  _ -> error "Unused index"

traverseVal :: Monad m => (PrimConVal -> m (Maybe PrimConVal)) -> Val -> m Val
traverseVal f val = case val of
  Con con -> do
    ans <- f con
    liftM Con $ case ans of
      Just con' -> return con'
      Nothing   -> traverseExpr con return (traverseVal f) return
  atom -> return atom

getValArrays :: Val -> [ArrayLitVal]
getValArrays val = execWriter $ flip traverseVal val $ \con -> case con of
  ArrayLit arr -> tell [arr]                            >> return (Just con)
  Lit x        -> tell [ArrayLitVal [] (litType x) [x]] >> return (Just con)
  _ -> return Nothing

liftExceptIO :: Except a -> IO a
liftExceptIO (Left e ) = throwIO e
liftExceptIO (Right x) = return x
