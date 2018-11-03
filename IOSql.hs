module IOSql (readDB) where
import qualified Data.Map.Strict as M
import Database.HDBC
import Database.HDBC.Sqlite3
import Data.List (intersperse)
import Data.ByteString.Char8 (unpack)
import Interpreter
import Typer
import Util

-- *** WARNING: this allows sql injection! not for untrusted input ***

type Except a = Either String a

tableName = "test"

readDB :: String -> IO (Val, ClosedType)
readDB fName = do
  conn <- connectSqlite3 fName
  desc <- describeTable conn tableName
  colTypes <- either fail return (descToColTypes desc)
  rows <- quickQuery' conn (selectQuery (map fst desc) tableName) []
  let t = tabType colTypes
  return (rowsToVal t rows, Forall 0 t)

descToColTypes :: [(String, SqlColDesc)] -> Except [Type]
descToColTypes desc = sequence (map (fromSqlType . colType . snd) desc)

fromSqlType :: SqlTypeId -> Except Type
fromSqlType t = case t of
  SqlIntegerT -> Right (BaseType IntType)
  SqlVarCharT -> Right (BaseType StrType)
  otherwise -> Left $ "Unrecognized SQL type: " ++ show t

rowsToVal :: Type -> [[SqlValue]] -> Val
rowsToVal t rows = case t of
  TabType k v -> let grouped = group (mapFst (toScalar k)$ map uncons rows)
                 in TabVal $ M.fromList $ mapSnd (rowsToVal v) grouped
  BaseType b -> IntVal 42

tabType :: [Type] -> Type
tabType [] = BaseType IntType
tabType (t:ts) = TabType t (tabType ts)

selectQuery :: [String] -> String -> String
selectQuery colNames tableName =
  "select " ++ concat (intersperse " , " colNames) ++ " from " ++ tableName

toScalar :: Type -> SqlValue -> Maybe IdxVal
toScalar t v = case t of
  BaseType IntType -> Just . IntIdxVal $ case v of
      SqlInt32   x -> fromIntegral x
      SqlInt64   x -> fromIntegral x
      SqlInteger x -> fromIntegral x
  BaseType StrType -> Just . StrIdxVal $ case v of
      SqlString s -> s
      SqlByteString s -> unpack s
