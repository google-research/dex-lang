-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE CPP #-}

module Serialize (DBOHeader (..), dumpDataFile, loadDataFile, pprintVal,
                 valToHeatmap, valToScatter,
                 typeToArrayType, cached) where

import Prelude hiding (pi, abs)
import Control.Monad
import Control.Exception (throwIO)
import Foreign.Ptr
import qualified Data.ByteString       as BS
import qualified Data.ByteString.Char8 as B
import qualified Data.Vector.Storable as V
import System.Directory
import System.FilePath
import System.IO
import System.IO.MMap
import System.Posix hiding (ReadOnly, version)
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import Data.Foldable (toList)
import Data.Store hiding (size)
import Data.Text.Prettyprint.Doc  hiding (brackets)
import Data.List (transpose)

import Array
import Interpreter
import Simplify
import Type hiding (indexSetConcreteSize)
import Syntax
import PPrint
import Parser
import Interpreter (indices, indexSetSize)
import qualified Algebra as A

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
  where
    valFromPtrs = undefined
    liftExceptIO :: Except a -> IO a
    liftExceptIO (Left e ) = throwIO e
    liftExceptIO (Right x) = return x

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
parseHeader = undefined
  -- emptyLines
  -- ty <- symbol "type:" >> tauType <* eol
  -- emptyLines
  -- sizes <-  symbol "bufferSizes:" >> brackets (uint `sepBy1` symbol ",") <* eol
  -- emptyLines
  -- return $ DBOHeader ty sizes

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
    flattenType = undefined
    claimedLength = headerLength + sum sizes
    ctx =   "Validation error\n"
         <> "Claimed header length: " <> show headerLength <> "\n"
         <> "Claimed total length:  " <> show claimedLength <> "\n"
         <> "Actual file length:    " <> show fileLength   <> "\n"
         <> "Header data:\n" <> serializeHeader header

checkBufferSize :: Int -> Int -> Except ()
checkBufferSize minSize size = when (size < minSize) $ throw DataIOErr $
   "buffer too small: " <> show size <> " < " <> show minSize

-- TODO: Optimize this!
-- Turns a fully evaluated table value into a bunch of arrays
materializeScalarTables :: Atom -> [Array]
materializeScalarTables atom = case atom of
  Con (ArrayLit _ arr) -> [arr]
  Con (Lit l)          -> [arrayFromScalar l]
  Con (PairCon l r)    -> materializeScalarTables l ++ materializeScalarTables r
  Con (UnitCon)        -> []
  Lam a@(Abs b (TabArrow, _)) ->
    fmap arrayConcat $ transpose $ fmap evalBody $ indices $ binderType b
    where evalBody idx = materializeScalarTables $ evalBlock mempty $ snd $ applyAbs a idx
  _ -> error $ "Not a scalar table: " ++ pprint atom

pattern Float64Ty :: Type
pattern Float64Ty = BaseTy (Scalar Float64Type)

pattern Float32Ty :: Type
pattern Float32Ty = BaseTy (Scalar Float32Type)

valToScatter :: Val -> Output
valToScatter val = case getType val of
  TabTy _ (PairTy Float64Ty Float64Ty) -> ScatterOut xs ys
    where [Array _ (Float64Vec xs), Array _ (Float64Vec ys)] = materializeScalarTables val
  TabTy _ (PairTy Float32Ty Float32Ty) -> ScatterOut (V.map realToFrac xs) (V.map realToFrac ys)
    where [Array _ (Float32Vec xs), Array _ (Float32Vec ys)] = materializeScalarTables val
  _ -> error $ "Scatter expects a 1D array of tuples, but got: " ++ pprint (getType val)

valToHeatmap :: Bool -> Val -> Output
valToHeatmap color val = case color of
  False -> case getType val of
    TabTy hv (TabTy wv Float64Ty) ->
      HeatmapOut color (indexSetSize $ binderType hv) (indexSetSize $ binderType wv) xs
      where [(Array _ (Float64Vec xs))] = materializeScalarTables val
    TabTy hv (TabTy wv Float32Ty) ->
      HeatmapOut color (indexSetSize $ binderType hv) (indexSetSize $ binderType wv) (V.map realToFrac xs)
      where [(Array _ (Float32Vec xs))] = materializeScalarTables val
    _ -> error $ "Heatmap expects a 2D array of floats, but got: " ++ pprint (getType val)
  True -> case getType val of
    TabTy hv (TabTy wv (TabTy _ Float64Ty)) ->
      HeatmapOut color (indexSetSize $ binderType hv) (indexSetSize $ binderType wv) xs
      where [(Array _ (Float64Vec xs))] = materializeScalarTables val
    TabTy hv (TabTy wv (TabTy _ Float32Ty)) ->
      HeatmapOut color (indexSetSize $ binderType hv) (indexSetSize $ binderType wv) (V.map realToFrac xs)
      where [(Array _ (Float32Vec xs))] = materializeScalarTables val
    _ -> error $ "Color Heatmap expects a 3D array of floats, but got: " ++ pprint (getType val)

pprintVal :: Val -> String
pprintVal val = asStr $ prettyVal val

prettyVal :: Val -> Doc ann
prettyVal val = case val of
  Lam abs@(Abs b (TabArrow, _)) -> pretty elems <> idxSetStr
    where idxSet = binderType b
          elems = flip fmap (indices idxSet) $ \idx ->
            asStr $ prettyVal $ evalBlock mempty $ snd $ applyAbs abs idx
          idxSetStr = case idxSet of FixedIntRange l _ | l == 0 -> mempty
                                     _                          -> "@" <> pretty idxSet
  ACase e alts _ -> case simplifyCase e alts of
    Just (env, atom) -> prettyVal $ subst (env, mempty) atom
    Nothing          -> error $ "Failed to reduce an acase: " ++ pprint val
  Con con -> case con of
    PairCon x y -> pretty (asStr $ prettyVal x, asStr $ prettyVal y)
    Coerce t i  -> pretty i <> "@" <> pretty t
    SumAsProd ty (TagRepVal trep) payload -> do
      let t = fromIntegral trep
      case ty of
        TypeCon (DataDef _ _ dataCons) _ ->
          case args of
            [] -> pretty conName
            _  -> parens $ pretty conName <+> hsep (map prettyVal args)
          where
            DataConDef conName _ = dataCons !! t
            args = payload !! t
        VariantTy (NoExt types) -> pretty variant
          where
            [value] = payload !! t
            (theLabel, repeatNum) = toList (reflectLabels types) !! t
            variant = Variant (NoExt types) theLabel repeatNum value
        _ -> error "SumAsProd with an unsupported type"
    _ -> pretty con
  atom -> prettyPrec atom LowestPrec

getValArrays :: Val -> [Array]
getValArrays = undefined

typeToArrayType :: ScalarTableType -> ArrayType
typeToArrayType t = case t of
  BaseTy b  -> (1, b)
  TabTy _ _ -> (fromIntegral sizeLit, scalarTableBaseType t)
    where (IdxRepVal sizeLit) = evalEmbed $ A.evalClampPolynomial (A.elemCount t)
  _ -> error $ "Not a scalar table type: " ++ pprint t

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
