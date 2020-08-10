-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE CPP #-}

module Serialize (DBOHeader (..), dumpDataFile, loadDataFile, pprintVal,
                 valToHeatmap, valToScatter, reStructureArrays, flattenType,
                 typeToArrayType, memoizeFileEval) where

import Prelude hiding (pi, abs)
import Control.Monad
import Control.Exception (throwIO)
import Foreign.Ptr
import qualified Data.ByteString       as BS
import qualified Data.ByteString.Char8 as B
import System.Directory
import System.IO
import System.IO.Error
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
reStructureArrays _ _ = undefined

valFromPtrs :: Type -> [Ptr ()] -> IO Val
valFromPtrs ty ptrs = do
  arrays <- forM (zip ptrs litTys) $ \(ptr, litTy) -> do
              x <- loadArray $ ArrayRef (typeToArrayType litTy) ptr
              return $ Con $ ArrayLit litTy x
  return $ reStructureArrays ty arrays
  where litTys = flattenType ty

-- TODO: Optimize this!
-- Turns a fully evaluated table value into a bunch of arrays
materializeScalarTables :: Atom -> [Array]
materializeScalarTables atom = case atom of
  Con (ArrayLit _ arr) -> [arr]
  Con (Lit l)          -> [arrayFromScalar l]
  Con (PairCon l r)    -> materializeScalarTables l ++ materializeScalarTables r
  Con (UnitCon)        -> []
  Con (IntCon  (Con (Lit l))) | i <- getIntLit l  -> [arrayFromScalar $ Int64Lit (fromIntegral i)]
  Con (FloatCon (Con (Lit l))) | f <- getFloatLit l -> [arrayFromScalar $ Float64Lit f]
  Lam a@(Abs b (TabArrow, _)) ->
    fmap arrayConcat $ transpose $ fmap evalBody $ indices $ binderType b
    where evalBody idx = materializeScalarTables $ evalBlock mempty $ snd $ applyAbs a idx
  _ -> error $ "Not a scalar table: " ++ pprint atom

-- TODO: Support fp32 outputs too!
valToScatter :: Val -> Output
valToScatter val = case getType val of
  TabTy _ (PairTy FloatTy FloatTy) -> ScatterOut xs ys
  _ -> error $ "Scatter expects a 1D array of tuples, but got: " ++ pprint (getType val)
  where [Array _ (Float64Vec xs), Array _ (Float64Vec ys)] = materializeScalarTables val

valToHeatmap :: Bool -> Val -> Output
valToHeatmap color val = case color of
  False -> case getType val of
    TabTy hv (TabTy wv FloatTy) ->
       HeatmapOut color (indexSetSize $ binderType hv) (indexSetSize $ binderType wv) xs
    _ -> error $ "Heatmap expects a 2D array of floats, but got: " ++ pprint (getType val)
  True -> case getType val of
    TabTy hv (TabTy wv (TabTy _ FloatTy)) ->
       HeatmapOut color (indexSetSize $ binderType hv) (indexSetSize $ binderType wv) xs
    _ -> error $ "Color Heatmap expects a 3D array of floats, but got: " ++ pprint (getType val)
  where [(Array _ (Float64Vec xs))] = materializeScalarTables val

pprintVal :: Val -> String
pprintVal val = asStr $ prettyVal val

prettyVal :: Val -> Doc ann
prettyVal val = case val of
  Lam abs@(Abs b (TabArrow, _)) -> pretty elems <> idxSetStr
    where idxSet = binderType b
          elems = flip fmap (indices idxSet) $ \idx ->
            asStr $ prettyVal $ evalBlock mempty $ snd $ applyAbs abs idx
          idxSetStr = case idxSet of FixedIntRange l _ | getIntLit l == 0 -> mempty
                                     _                                    -> "@" <> pretty idxSet
  Con con -> case con of
    PairCon x y -> pretty (asStr $ prettyVal x, asStr $ prettyVal y)
    Coerce t i  -> pretty i <> "@" <> pretty t
    SumAsProd ty (IntLit l) payload ->
      case ty of
        TypeCon (DataDef _ _ dataCons) _ ->
          case args of
            [] -> pretty conName
            _  -> parens $ pretty conName <+> hsep (map prettyVal args)
          where
            i = getIntLit l
            DataConDef conName _ = dataCons !! i
            args = payload !! i
        VariantTy types -> pretty variant
          where
            i = getIntLit l
            [value] = payload !! i
            (theLabel, repeatNum) = toList (reflectLabels types) !! i
            variant = Variant types theLabel repeatNum value
        _ -> error "SumAsProd with an unsupported type"
    _ -> pretty con
  atom -> prettyPrec atom LowestPrec

getValArrays :: Val -> [Array]
getValArrays = undefined

flattenType :: Type -> [Type]
flattenType (TabTy n a) = TabTy n <$> flattenType a
flattenType (TC con) = case con of
  BaseType b       -> [BaseTy b]
  IntRange _ _     -> [IntTy]
  IndexRange _ _ _ -> [IntTy]
  _ -> error $ "Unexpected type: " ++ show con
flattenType ty = error $ "Unexpected type: " ++ show ty

typeToArrayType :: ScalarTableType -> ArrayType
typeToArrayType t = case t of
  BaseTy b  -> (1, b)
  TabTy _ _ -> (getIntLit sizeLit, scalarTableBaseType t)
    where (IntLit sizeLit) = evalEmbed $ A.evalClampPolynomial (A.elemCount t)
  _ -> error $ "Not a scalar table type: " ++ pprint t

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
