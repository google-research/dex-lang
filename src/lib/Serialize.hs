-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}

module Serialize (DBOHeader (..), dumpDataFile, loadDataFile, pprintVal,
                 valToHeatmap, valToScatter, reStructureArrays) where

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
import Data.Maybe

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
  arrayRefs <- mapM storeArrayNew $ getValArrays val
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

createHeader :: Type -> [ArrayRef] -> DBOHeader
createHeader ty arrays = DBOHeader ty sizes
  where sizes = [8 * product shape | ArrayRef (shape, _) _ <- arrays]

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

writeArrayToFile :: Handle -> ArrayRef -> IO ()
writeArrayToFile h (ArrayRef (shape, _) ptr) = hPutBuf h ptr (size * 8)
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

reStructureArrays :: Type -> [Val] -> Val
reStructureArrays ty xs = evalState (reStructureArrays' ty) xs

reStructureArrays' :: Type -> State [Val] Val
reStructureArrays' (TabTy n a) = liftM (Con . AFor n) $ reStructureArrays' a
reStructureArrays' ty@(TC con) = case con of
  BaseType _ -> do
    ~(x:xs) <- get
    put xs
    return $ Con $ AGet x
  IntRange _ _ -> do
    liftM (Con . AsIdx ty) $ reStructureArrays' $ TC $ BaseType IntType
  PairType a b -> liftM2 PairVal (reStructureArrays' a) (reStructureArrays' b)
  UnitType -> return UnitVal
  _ -> error $ "Not implemented: " ++ pprint ty
reStructureArrays' ty = error $ "Not implemented: " ++ pprint ty

valFromPtrs :: Type -> [Ptr ()] -> IO Val
valFromPtrs ty ptrs = do
  arrays <- forM (zip ptrs arrTys) $ \(ptr, (b, shape)) -> do
              x <- loadArray $ ArrayRef (shape, b) ptr
              return $ Con $ ArrayLit x
  return $ reStructureArrays ty arrays
  where arrTys = flattenType ty

valToScatter :: Val -> Output
valToScatter ~(Con (AFor _ body)) = ScatterOut xs ys
  where
    ~(PairVal (Con (AGet (Con (ArrayLit (Array _ (DoubleVec xs))))))
              (Con (AGet (Con (ArrayLit (Array _ (DoubleVec ys))))))) = body

valToHeatmap :: Val -> Output
valToHeatmap ~(Con (AFor (FixedIntRange hl hh) body)) = HeatmapOut h w xs
  where ~(Con (AFor (FixedIntRange wl wh) (Con (AGet arr)))) = body
        ~(Con (ArrayLit (Array _ (DoubleVec xs)))) = arr
        h = hh - hl
        w = wh - wl

pprintVal :: Val -> IO String
pprintVal val = liftM asStr $ prettyVal [] val

prettyVal :: [Int] -> Val -> IO (Doc ann)
prettyVal idxs (Con con) = case con of
  PairCon x y -> liftM pretty $ liftM2 (,) (asStr <$> prettyVal idxs x)
                                           (asStr <$> prettyVal idxs y)
  AFor n body -> do
    xs <- flip mapM [0..n'-1] $ \i ->
      liftM asStr $ prettyVal (idxs ++ [i]) body
    return $ pretty xs <> idxSetStr
    where
      (Just n') = indexSetConcreteSize n
      idxSetStr = case n of FixedIntRange 0 _ -> mempty
                            _                 -> "@" <> pretty n
  AGet (Con (ArrayLit arr)) -> do
    let arr' = foldl (flip subArray) arr idxs
    return $ pretty $ fromMaybe (error "not a scalar") $ scalarFromArray arr'
  AsIdx n i -> do
    i' <- prettyVal idxs i
    return $ i' <> "@" <> parens (pretty n)
  Lit x -> return $ pretty x
  _ -> return $ pretty con
prettyVal _ atom = error $ "Unexpected value: " ++ pprint atom

traverseVal :: Monad m => (Con -> m (Maybe Con)) -> Val -> m Val
traverseVal f val = case val of
  Con con -> do
    ans <- f con
    liftM Con $ case ans of
      Just con' -> return con'
      Nothing   -> mapM (traverseVal f) con
  atom -> return atom

getValArrays :: Val -> [Array]
getValArrays val = execWriter $ flip traverseVal val $ \con -> case con of
  ArrayLit arr -> tell [arr]               >> return (Just con)
  Lit x        -> tell [arrayFromScalar x] >> return (Just con)
  _ -> return Nothing

liftExceptIO :: Except a -> IO a
liftExceptIO (Left e ) = throwIO e
liftExceptIO (Right x) = return x

flattenType :: Type -> [(BaseType, [Int])]
flattenType (FixedIntRange _ _) = [(IntType, [])]
flattenType (TabTy (FixedIntRange low high) a) =
    [(b, (high - low):shape) | (b, shape) <- flattenType a]
-- temporary hack. TODO: fix
flattenType (TabTy _ a) = [(b, 0:shape) | (b, shape) <- flattenType a]
flattenType (TC con) = case con of
  BaseType b  -> [(b, [])]
  _ -> error $ "Unexpected type: " ++ show con
flattenType ty = error $ "Unexpected type: " ++ show ty
