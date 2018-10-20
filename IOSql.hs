module IOSql (loadData) where
import Table
import Database.HDBC
import Database.HDBC.Sqlite3
import Data.List
import Interpreter

-- *** WARNING: this allows sql injection! not for production ***

loadData :: String -> String -> [String] -> IO Val
loadData fName tableName colNames = do
  conn <- connectSqlite3 fName
  table <- let query = "select "
                       ++ concat (intersperse " , " colNames)
                       ++ " from " ++ tableName
          in quickQuery' conn query []
  disconnect conn
  return $ sqlToTable (length colNames) table

toInt :: SqlValue -> Int
toInt (SqlInt32   x) = fromIntegral x
toInt (SqlInt64   x) = fromIntegral x
toInt (SqlInteger x) = fromIntegral x
toInt s = error $ "Not an int: " ++ show s

sqlToTable :: Int -> [[SqlValue]] -> Val
sqlToTable numCols svs =
    let intVals = map (map toInt) svs
        rows = [(map Just (init xs), last xs) | xs <- intVals]
    in IntVal 0 $ Table (numCols-1) rows
