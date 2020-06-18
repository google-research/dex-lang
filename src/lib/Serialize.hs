-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}

module Serialize (DBOHeader (..), dumpDataFile, loadDataFile, pprintVal,
                 valToHeatmap, valToScatter, reStructureArrays, flattenType,
                 typeToArrayType) where

import Prelude hiding (unzip, pi)
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
  let arrays = getValArrays val
  let ty = getType val
  withFile fname WriteMode $ \h -> do
    putBytes h $ serializeFullHeader $ createHeader ty arrays
    mapM_ (writeArrayToFile h) arrays

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
  where sizes = [sizeOf b * elems | (elems, b) <- map arrayType arrays]

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
writeArrayToFile h arr = unsafeWithArrayPointer arr (\ptr -> hPutBuf h ptr (size * sizeOf b))
  where (size, b) = arrayType arr

validateFile :: Int -> Int -> DBOHeader -> Except ()
validateFile headerLength fileLength header@(DBOHeader ty sizes) =
  addContext ctx $ do
     let minSizes = [size * (sizeOf b) | (size, b) <- fmap typeToArrayType $ flattenType ty]
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
  IndexRange _ _ _ -> do
    liftM (Con . AsIdx ty) $ reStructureArrays' $ TC $ BaseType IntType
  -- TODO: How to restructure into a sum type?
  _ -> error $ "Not implemented: " ++ pprint ty
reStructureArrays' ty = error $ "Not implemented: " ++ pprint ty

valFromPtrs :: Type -> [Ptr ()] -> IO Val
valFromPtrs ty ptrs = do
  arrays <- forM (zip ptrs litTys) $ \(ptr, litTy) -> do
              x <- loadArray $ ArrayRef (typeToArrayType litTy) ptr
              return $ Con $ ArrayLit litTy x
  return $ reStructureArrays ty arrays
  where litTys = flattenType ty

valToScatter :: Val -> Output
valToScatter ~(Con (AFor _ body)) = ScatterOut xs ys
  where
    ~(PairVal (Con (AGet (Con (ArrayLit _ (Array (DoubleVec xs))))))
              (Con (AGet (Con (ArrayLit _ (Array (DoubleVec ys))))))) = body

valToHeatmap :: Val -> Output
valToHeatmap ~(Con (AFor (FixedIntRange hl hh) body)) = HeatmapOut h w xs
  where ~(Con (AFor (FixedIntRange wl wh) (Con (AGet arr)))) = body
        ~(Con (ArrayLit _ (Array (DoubleVec xs)))) = arr
        h = hh - hl
        w = wh - wl

pprintVal :: Val -> String
pprintVal val = asStr $ fst $ prettyVal val
-- TODO: Assert all arrays are empty?

-- TODO: Implement as a traversal?
prettyVal :: Val -> (Doc ann, Val)
prettyVal (Con con) = case con of
  PairCon x y -> (pretty (d1, d2), Con $ PairCon r1 r2)
    where (d1, r1) = appFst asStr $ prettyVal x
          (d2, r2) = appFst asStr $ prettyVal y
  AFor n body -> (pretty elems <> idxSetStr, Con $ AFor n $ last bodies)
    where n' = indexSetSize n
          -- TODO(ragged): Substitute i in the types that appear in a!
          (elems, bodies) = unzip $ tail $ scanl (\(_, b) _ -> appFst asStr $ prettyVal b)
                                                 (undefined, body)
                                                 [0..n'-1]
          idxSetStr = case n of FixedIntRange 0 _ -> mempty
                                _                 -> "@" <> pretty n
  AGet (Con (ArrayLit t arr)) ->
    -- Technically the type of the array should no longer be t, as it has
    -- been shifted, but replacing it with undefined seems to blow up for some reason...
    (pretty $ arrayHead arr, Con $ AGet $ Con $ ArrayLit t $ arrayTail arr)
  AsIdx n i -> (doc <> "@" <> pretty n, Con $ AsIdx n i')
    where (doc, i') = prettyVal i
  Lit x -> (pretty x, Con $ Lit x)
  _ -> (pretty con, Con $ con)
  where
    appFst :: (a -> b) -> (a, c) -> (b, c)
    appFst f (x, y) = (f x, y)
prettyVal atom = error $ "Unexpected value: " ++ pprint atom

unzip :: Functor f => f (a, b) -> (f a, f b)
unzip f = (fmap fst f, fmap snd f)

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
  ArrayLit _ arr -> tell [arr]               >> return (Just con)
  Lit x          -> tell [arrayFromScalar x] >> return (Just con)
  _ -> return Nothing

liftExceptIO :: Except a -> IO a
liftExceptIO (Left e ) = throwIO e
liftExceptIO (Right x) = return x

indexSetSize :: Type -> Int
indexSetSize t = fromMaybe fail' $ indexSetConcreteSize t
  where
    fail' = (error $ "Can't determine dimension size: " ++ pprint t)
    indexSetConcreteSize :: Type -> Maybe Int
    indexSetConcreteSize ty = case ty of
      TC (IntRange low high) -> do
        l <- loadBound low
        h <- loadBound high
        Just $ h - l
      TC (IndexRange n low high) -> do
        low' <- case low of
          InclusiveLim x -> loadBound x
          ExclusiveLim x -> (+1) <$> loadBound x
          Unlimited      -> Just 0
        high' <- case high of
          InclusiveLim x -> (+1) <$> loadBound x
          ExclusiveLim x -> loadBound x
          Unlimited      -> indexSetConcreteSize n
        Just $ high' - low'
      BoolTy  -> Just 2
      SumTy l r -> (+) <$> indexSetConcreteSize l <*> indexSetConcreteSize r
      _ -> Nothing
      where
        loadBound :: Atom -> Maybe Int
        loadBound (IntVal n) = Just n
        loadBound (Con (AGet (Con (ArrayLit (BaseTy _) arr)))) = do
          (IntLit n) <- scalarFromArray arr
          Just n
        loadBound _ = Nothing

flattenType :: Type -> [Type]
flattenType (TabTy n a) = TabTy n <$> flattenType a
flattenType (TC con) = case con of
  BaseType b       -> [BaseTy b]
  IntRange _ _     -> [IntTy]
  IndexRange _ _ _ -> [IntTy]
  SumType _ _      -> undefined
  _ -> error $ "Unexpected type: " ++ show con
flattenType ty = error $ "Unexpected type: " ++ show ty

typeToArrayType :: ScalarTableType -> ArrayType
typeToArrayType t = case t of
  TabTy n body -> (indexSetSize n * s, b)
    where (s, b) = typeToArrayType body
  BaseTy b -> (1, b)
  _ -> error $ "Not a scalar table type: " ++ pprint t
