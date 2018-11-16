module TCSV (readTCSV) where

import qualified Data.Map.Strict as M
import Text.ParserCombinators.Parsec
import Parser (typedName, str)
import Record
import Util
import Typer
import Interpreter

type Except a = Either String a

readTCSV :: String -> Except (Val, ClosedType)
readTCSV s = do
  (header, rowLines) <- case lines s of
    [] -> Left "Error: empty file"
    header:rows -> return (header, rows)
  (colNames, colTypes, numKeyCols) <- parse' headerP header
  rows <- sequence $ map (parseLine colTypes) rowLines
  case repeated $ map (take numKeyCols) rows of
      [] -> return ()
      row:_ -> Left $ "Duplicate row:\n" ++ show row
  return $ rowsToVal numKeyCols colNames colTypes rows

parse' :: Parser a -> String -> Except a
parse' p s = case parse (p <* eof) "" s of
  Left e -> Left (show e)
  Right x -> Right x

headerP :: Parser ([String], [BaseType], Int)
headerP = do
  typedNamesLHS <- typedName `sepBy` str ","
  str "|"
  typedNamesRHS <- typedName `sepBy` str ","
  let (names, types) = unzip (typedNamesLHS ++ typedNamesRHS)
  return (names, types, length typedNamesLHS)

parseLine :: [BaseType] -> String -> Except [IdxVal]
parseLine = undefined

rowsToVal :: Int -> [String] -> [BaseType] -> [[IdxVal]] -> (Val, ClosedType)
rowsToVal numKeyCols colNames colTypes rows =
  let split = splitAt numKeyCols
      recType names = RecType . nameRecord . zip names . map BaseType
      (keyRows, valRows) = unzip $ map split rows
      (keyNames, valNames) = split colNames
      (keyTypes, valTypes) = split colTypes
      keys = map (RecIdxVal . nameRecord . zip keyNames) keyRows
      vals = map (RecVal . nameRecord . zip valNames . map idxValToVal) valRows
      keyType = recType keyNames keyTypes
      valType = recType valNames valTypes
      tabVal = TabVal . M.fromList . zip keys $ vals
      tabType = Forall 0 $ TabType keyType valType
  in (tabVal, tabType)
