-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Serialize (serializeVal, restructureVal, subArray, subArrayRef, readScalar,
                  allocateArray, storeArray, loadArray, vecRefInfo,
                  storeFlatVal, loadFlatVal, DBOHeader (..),
                  dumpDataFile, loadDataFile, loadAtomVal) where

import Control.Monad
import Control.Exception (throwIO)
import Foreign.Ptr
import Foreign.Marshal.Array
import qualified Data.ByteString.Char8 as B
import System.IO
import System.IO.MMap
import System.Posix  hiding (ReadOnly)
import Text.Megaparsec
import Text.Megaparsec.Char

import Type
import Syntax
import Util
import PPrint
import Record
import Inference
import Parser
import ParseUtil
import Normalize
import Subst

serializeVal :: Val -> IO FlatValRef
serializeVal val = do
  let ty = getType val
  vecRefs <- mapM (uncurry allocateArray) $ flattenType ty
  let flatValRef = FlatVal ty vecRefs
  writeVal flatValRef $ val
  return flatValRef

writeVal :: FlatValRef -> Val -> IO ()
writeVal (FlatVal (BaseType _) [ref]) (PrimCon (Lit x)) =
  storeArray ref $ scalarArray x
writeVal (FlatVal (RecType r) refs) (PrimCon (RecCon valRec)) =
  sequence_ $ recZipWith f refRec valRec
  where
    refRec = listIntoRecord r refs
    f (ty,refs') val = writeVal (FlatVal ty refs') val
writeVal (FlatVal (TabType _ a) refs) (PrimCon (AtomicTabCon _ xs)) =
  zipWithM_ writeRow [0..] xs
  where
    writeRow :: Int -> Val -> IO ()
    writeRow i row = writeVal (FlatVal a (map (subArrayRef i) refs)) row
writeVal (FlatVal (IdxSetLit _) [ref]) (PrimCon (IdxLit _ i)) =
  storeArray ref $ scalarArray $ IntLit i
writeVal fv val = error $ "Unexpected flatval/val: " ++ pprint (fv, show val)

restructureVal :: FlatVal -> Val
restructureVal (FlatVal ty arrays) = case ty of
  BaseType _  -> PrimCon $ Lit      $ readScalar array  where [array] = arrays
  RecType r -> PrimCon $ RecCon $ fst $ traverseFun restructureValPartial r arrays
  TabType (IdxSetLit n) a -> PrimCon $ AtomicTabCon ty $
    [restructureVal $ FlatVal a $ map (subArray i) arrays | i <- [0..n-1]]
  IdxSetLit n -> PrimCon $ IdxLit n i  where [array] = arrays
                                             IntLit i = readScalar array
  _ -> error $ "Unexpected type: " ++ show ty

restructureValPartial :: Type -> [Array] -> (Val, [Array])
restructureValPartial ty xsRest = (restructureVal (FlatVal ty xs), rest)
  where (xs, rest) = splitAt (length (flattenType ty)) xsRest

subArray :: Int -> Array -> Array
subArray i (Array (_:shape) vec) = Array shape sliced
  where
    subArraySize = product shape
    start = i * subArraySize
    stop  = start + subArraySize
    sliced = case vec of
      IntVec  xs -> IntVec  (slice start stop xs)
      RealVec xs -> RealVec (slice start stop xs)
      BoolVec xs -> BoolVec (slice start stop xs)
subArray _ (Array [] _) = error "Can't get subarray of rank-0 array"

slice :: Int -> Int -> [a] -> [a]
slice start stop xs = take (stop - start) $ drop start xs

-- TODO: check types and lengths match
storeFlatVal :: FlatValRef -> FlatVal -> IO ()
storeFlatVal (FlatVal _ refs) (FlatVal _ vals) = zipWithM_ storeArray refs vals

loadFlatVal :: FlatValRef -> IO FlatVal
loadFlatVal (FlatVal ty refs) = liftM (FlatVal ty) $ mapM loadArray refs

-- TODO: free
allocateArray :: BaseType -> [Int] -> IO ArrayRef
allocateArray b shape = do
  ptr <- case b of
    IntType  -> liftM IntVecRef  $ mallocArray size
    RealType -> liftM RealVecRef $ mallocArray size
    BoolType -> liftM BoolVecRef $ mallocArray size
    StrType  -> error "Not implemented"
  return $ Array shape (size, ptr)
  where size = product shape

storeArray :: ArrayRef -> Array -> IO ()
storeArray (Array _ (_, ref)) (Array _ vec) = case (ref, vec) of
  (IntVecRef  ptr, IntVec  xs) -> pokeArray ptr xs
  (RealVecRef ptr, RealVec xs) -> pokeArray ptr xs
  (BoolVecRef ptr, BoolVec xs) -> pokeArray ptr xs
  _ -> error "Mismatched types"

loadArray :: ArrayRef -> IO Array
loadArray (Array shape (size, ref)) = case ref of
  IntVecRef  ptr -> liftM (Array shape . IntVec ) $ peekArray size ptr
  RealVecRef ptr -> liftM (Array shape . RealVec) $ peekArray size ptr
  BoolVecRef ptr -> liftM (Array shape . BoolVec) $ peekArray size ptr

readScalar :: Array -> LitVal
readScalar (Array [] vec) = case vec of
  IntVec  [x] -> IntLit  x
  RealVec [x] -> RealLit x
  BoolVec [x] -> BoolLit $ case x of 0 -> False
                                     _ -> True
  _ -> error "Not a singleton list"
readScalar _ = error "Array must be rank-0"

scalarArray :: LitVal -> Array
scalarArray val = case val of
  IntLit  x -> Array [] (IntVec  [x])
  RealLit x -> Array [] (RealVec [x])
  BoolLit False -> Array [] (BoolVec [0])
  BoolLit True  -> Array [] (BoolVec [1])
  _ -> error "Not implemented"

vecRefInfo :: VecRef -> (Int, BaseType, Ptr ())
vecRefInfo (size, x) = case x of
  IntVecRef  ptr -> (size, IntType , castPtr ptr)
  RealVecRef ptr -> (size, RealType, castPtr ptr)
  BoolVecRef ptr -> (size, BoolType, castPtr ptr)

newArrayRef :: Ptr () -> (BaseType, [Int]) -> ArrayRef
newArrayRef ptr (b, shape) = Array shape $ case b of
  IntType  -> (size, IntVecRef  $ castPtr ptr)
  RealType -> (size, RealVecRef $ castPtr ptr)
  BoolType -> (size, BoolVecRef $ castPtr ptr)
  StrType  -> error "Not implemented"
  where size = product shape

-- turns memrefs into atomic table constructors
loadAtomVal :: Atom -> IO Atom
loadAtomVal (PrimCon (MemRef ty ref)) = do
  array <- loadArray ref
  return $ restructureVal $ FlatVal ty [array]
loadAtomVal (PrimCon con) = do
  liftM PrimCon $ traverseExpr con return loadAtomVal return
loadAtomVal atom = error $ "Unexpected atom: " ++ pprint atom

-- === binary format ===

data DBOHeader = DBOHeader
  { objectType     :: Type
  , bufferSizes    :: [Int] }

preHeaderLength :: Int
preHeaderLength = 81

preHeaderStart :: String
preHeaderStart = "-- dex-object-file-v0.0.1 num-header-bytes "

dumpDataFile :: FilePath -> DataFormat -> FlatValRef -> IO ()
dumpDataFile fname DexObject valRef = do
  val <- loadFlatVal valRef
  writeFile fname $ pprint $ restructureVal val
dumpDataFile fname DexBinaryObject val@(FlatVal _ arrayRefs) = do
  withFile fname WriteMode $ \h -> do
    putBytes h $ serializeFullHeader $ createHeader val
    mapM_ (writeArrayToFile h) arrayRefs

loadDataFile :: FilePath -> DataFormat -> IO FlatValRef
loadDataFile fname DexObject = do
  source <- readFile fname
  let uval = ignoreExcept $ parseData source
  let (_, val) = ignoreExcept $ inferExpr uval
  let val' = ignoreExcept $ normalizeVal val
  serializeVal val'
loadDataFile fname DexBinaryObject = do
   -- TODO: check lengths are consistent with type
  (n, header@(DBOHeader ty sizes)) <- readHeader fname
  actualSize <- liftM (fromIntegral . fileSize) $ getFileStatus fname
  liftExceptIO $ validateFile n actualSize header
  filePtr <- memmap fname
  let firstPtr = filePtr `plusPtr` n
  let ptrs = init $ scanl plusPtr firstPtr sizes
  return $ FlatVal ty $ zipWith newArrayRef ptrs (flattenType ty)

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

createHeader :: FlatValRef -> DBOHeader
createHeader (FlatVal ty arrays) = DBOHeader ty sizes
  where sizes = [8 * product shape | Array shape _ <- arrays]

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
writeArrayToFile h (Array _ ref) = hPutBuf h ptr (size * 8)
  where (size, _, ptr) = vecRefInfo ref

validateFile :: Int -> Int -> DBOHeader -> Except ()
validateFile headerLength fileLength header@(DBOHeader ty sizes) =
  addContext ctx $ do
     let minSizes = [product shape * 8 | (_, shape) <- flattenType ty]
     when (length minSizes /= length sizes) $ throw DataIOErr $
        "unexpected number of buffers: " <> show minSizes <> " vs " <> show sizes
     zipWithM_ checkBufferSize minSizes sizes
     when (claimedLength /= fileLength) $ throw DataIOErr $ "wrong file size"
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

liftExceptIO :: Except a -> IO a
liftExceptIO (Left e ) = throwIO e
liftExceptIO (Right x) = return x
