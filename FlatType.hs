module FlatType (flattenType, unflattenType,
                 flattenVal, unflattenVal,
                 showVal, printTabType, parseTabType,
                 printVal, parseVal,
                 TabType) where
import Data.List (intercalate, transpose)
import Data.Void
import Data.Monoid ((<>))
import Control.Monad (void)
import Text.Megaparsec
import Text.Megaparsec.Char hiding (space)
import qualified Text.Megaparsec.Char.Lexer as L

import Record
import Util
import qualified Data.Map.Strict as M
import qualified Typer as T
import qualified Interpreter as I
import Data.List (partition, foldr1, intersperse)
import Data.Foldable (toList)

type Except a = Either String a

type TabName = [RecName]
data ScalarType = BaseType T.BaseType
                | UnitType  deriving (Eq, Show)
type ScalarTree = RecTree ScalarType
data TabType = TabType TabName ScalarTree TabType
             | ValPart ScalarTree
                 deriving (Eq, Show)

flattenType :: T.Type -> Except [TabType]
flattenType t = case t of
   T.TabType a b -> do
       leftKeys <- flattenIdxType a
       rightTabs <- flattenType b
       return $ map (TabType [] leftKeys) rightTabs
   T.RecType r | isEmpty r -> return $ [ValPart (RecLeaf UnitType)]
               | otherwise -> do
     r' <- sequence $ fmap flattenType r
     let ts = [(k,t) | (k, ts) <- recToList r', t <- ts]
         maybeVal = case [(k, s) | (k, ValPart s) <- ts] of
                  [] -> []
                  vs -> [valRec vs]
         tabs = [TabType (k:name) s rest | (k, TabType name s rest) <- ts]
     return $ maybeVal ++ tabs
   T.BaseType b -> return $ [ValPart (RecLeaf (BaseType b))]
   _ -> Left $ "can't print value with type " ++ show t

flattenIdxType :: T.Type -> Except ScalarTree
flattenIdxType t = case t of
   T.RecType r | isEmpty r -> return (RecLeaf UnitType)
               | otherwise -> fmap RecTree $ sequence (fmap flattenIdxType r)
   T.BaseType b -> return (RecLeaf (BaseType b))
   _ -> Left $ "can't print value with type " ++ show t

valRec :: [(RecName, ScalarTree)] -> TabType
valRec = ValPart . RecTree . recFromList

unflattenType :: [TabType] -> T.Type
unflattenType tabs = foldr1 mergeTypes (map unflattenTab tabs)

unflattenTab :: TabType -> T.Type
unflattenTab (ValPart st) = unflattenScalarTree st
unflattenTab (TabType name st rest) =
  let t = T.TabType (unflattenScalarTree st) (unflattenTab rest)
  in recFromName T.RecType name t

unflattenScalarTree :: ScalarTree -> T.Type
unflattenScalarTree st = case st of
  RecTree r -> T.RecType $ fmap unflattenScalarTree r
  RecLeaf (BaseType b) -> T.BaseType b
  RecLeaf UnitType  -> T.RecType emptyRecord

mergeTypes :: T.Type -> T.Type -> T.Type
mergeTypes (T.RecType r1) (T.RecType r2) =
  T.RecType $ recUnionWith mergeTypes r1 r2
mergeTypes (T.TabType a1 b1) (T.TabType a2 b2) | a1 == a2 =
  T.TabType a1 (mergeTypes b1 b2)

----- flattening vals -----

type ColName = [RecName]
data ScalarVal = IntVal Int
               | BoolVal Bool
               | RealVal Float
               | StrVal String
               | AnyVal
               | UnitVal  deriving (Ord, Eq, Show)

type Row = [ScalarVal]
type TabVal = [Row]

flattenVal :: I.Val -> [TabType] -> [TabVal]
flattenVal v ts = map (getRows v) ts

unflattenVal :: [TabVal] -> [TabType] -> I.Val
unflattenVal rows ts = foldr1 mergeVals (zipWith unflattenRows rows ts)

getColTypes :: TabType -> [ScalarType]
getColTypes t = case t of
    ValPart s -> getTypes s
    TabType name s rest -> getTypes s ++ getColTypes rest
  where
    getTypes s = map snd (recTreeLeaves s)

getRows :: I.Val -> TabType -> TabVal
getRows v t = case t of
  ValPart s -> [flattenScalarTree v s]
  TabType name s rest ->
    let I.TabVal m = lookupPath v name
    in concat [catRows (flattenScalarTree k s) (getRows v' rest)
                | (k,v') <- M.toList m ]

catRows :: Monoid a => a -> [a] -> [a]
catRows x [] = [x]
catRows x xs = map (x <>) xs

flattenScalarTree :: I.Val -> ScalarTree -> [ScalarVal]
flattenScalarTree v s = map (valToScalarVal . lookupPath v) (recTreePaths s)

valToScalarVal :: I.Val -> ScalarVal
valToScalarVal v = case v of
  I.IntVal  x -> IntVal  x ; I.BoolVal x -> BoolVal x
  I.RealVal x -> RealVal x ; I.StrVal  x -> StrVal  x
  I.RecVal r | isEmpty r -> UnitVal
  I.Any -> AnyVal

scalarValToVal :: ScalarVal -> I.Val
scalarValToVal v = case v of
  IntVal  x -> I.IntVal  x ; BoolVal x -> I.BoolVal x
  RealVal x -> I.RealVal x ; StrVal  x -> I.StrVal  x
  UnitVal -> I.RecVal emptyRecord

unflattenRows :: [[ScalarVal]] -> TabType -> I.Val
unflattenRows rows (TabType tabname s rest) = recFromName I.RecVal tabname tab
  where
    tab = I.TabVal $
      case rows of
        [[]]  -> M.empty
        rows' -> let numCols = length (recTreePaths s)
                     groupedRows = group . map (splitAt numCols) $ rows'
                 in M.fromList [(unflattenRow k s, unflattenRows v rest)
                                | (k, v) <- groupedRows]
unflattenRows [row] (ValPart s) = unflattenRow row s

unflattenRow :: [ScalarVal] -> ScalarTree -> I.Val
unflattenRow vals s =
  let names = recTreePaths s
      vals' = map scalarValToVal vals
  in foldr1 mergeVals $ zipWith (recFromName I.RecVal) names vals'

mergeVals :: I.Val -> I.Val -> I.Val
mergeVals (I.RecVal r1) (I.RecVal r2) =
  I.RecVal $ recUnionWith mergeVals r1 r2
mergeVals (I.TabVal m1) (I.TabVal m2) | M.keys m1 == M.keys m1 =
  I.TabVal $ M.intersectionWith mergeVals m1 m2
mergeVals v1 v2 = error ("Can't merge " ++ show v1 ++ " and " ++ show v2)

lookupPath :: I.Val -> [RecName] -> I.Val
lookupPath v [] = v
lookupPath (I.RecVal r) (name:rest) = let Just v = recLookup name r
                                       in lookupPath v rest

-- ----- printing -----

showVal :: T.ClosedType -> I.Val -> String
showVal (T.Forall _ t) v =
  case printVal t v of
    Left e -> "Print error: " ++ e
    Right s -> s

printVal :: T.Type -> I.Val -> Except String
printVal t v = do
  tabTypes <- flattenType t
  let tabVals = flattenVal v tabTypes
  return . intercalate "\n" $ zipWith printTab tabTypes tabVals

printTab :: TabType -> TabVal -> String
printTab t v = printTabType t ++ printTabVal v

printTabType :: TabType -> String
printTabType t = printTabName t ++ printHeader t

printTabName :: TabType -> String
printTabName t = case getTabName t of
  names | length (concat names) == 0 -> ""
        | otherwise -> "> " ++ (intercalate " | " $ map printName names) ++ "\n"

getTabName :: TabType -> [[RecName]]
getTabName (TabType name _ rest) = name : getTabName rest
getTabName (ValPart _) = []

printHeader :: TabType -> String
printHeader (TabType _ s rest) = printTree s ++ " " ++ printHeader rest
printHeader (ValPart s) = printTree s ++ "\n"

printTree :: ScalarTree -> String
printTree (RecTree r) = printRecord printTree (RecordPrintSpec "\t" ":" "") r
printTree (RecLeaf x) = case x of UnitType -> "()"
                                  BaseType x' -> show x'

printName :: [RecName] -> String
printName names = concat $ intersperse "." (map show names)

printTabVal :: TabVal -> String
printTabVal rows = unlines $ map printRow rows
  where printRow row = intercalate "\t" $ map printScalar row

printScalar :: ScalarVal -> String
printScalar v = case v of
  IntVal  x -> show x ; BoolVal x -> show x
  RealVal x -> show x ; StrVal  x -> show x
  UnitVal -> "()"
  AnyVal -> "*"

-- ----- parsing -----

parseVal :: String -> Except (T.Type, I.Val)
parseVal s = case parse topP "" s of
  Left e -> Left (errorBundlePretty e)
  Right tabs -> let (tabTypes, tabVals) = unzip tabs
                in  Right ( unflattenType tabTypes
                          , unflattenVal tabVals tabTypes)

parseTabType :: String -> Except TabType
parseTabType s = case parse tabTypeP "" s of
  Left e -> Left (errorBundlePretty e)
  Right x -> Right x

type Parser = Parsec Void String

topP :: Parser [(TabType, TabVal)]
topP = do blankLines >> some parseTab

parseTab :: Parser (TabType, TabVal)
parseTab = do
  tabType <- tabTypeP
  rows <- tabValP tabType
  blankLines
  return (tabType, rows)

tabTypeP :: Parser TabType
tabTypeP = do
  tabNames <- fullTabNameP <|> return []
  sectionTypes <- lineof $ scalarTreeP `sepBy` sc
  return $ makeTabType (tabNames ++ repeat []) sectionTypes

makeTabType :: [[RecName]] -> [ScalarTree] -> TabType
makeTabType names [st] = ValPart st
makeTabType (name:names) (st:sts) = TabType name st (makeTabType names sts)

fullTabNameP :: Parser [[RecName]]
fullTabNameP = lineof $ symbol ">" >> tabNameP `sepBy1` symbol "|"

tabNameP :: Parser [RecName]
tabNameP = recNameP `sepBy` char '.' <* sc

scalarTreeP :: Parser ScalarTree
scalarTreeP =     (symbol "()" >> return (RecLeaf UnitType))
              <|> fmap RecTree (recordP scalarTreeP)
              <|> fmap (RecLeaf . BaseType) baseTypeP

maybeNamed :: Parser a -> Parser (Maybe RecName, a)
maybeNamed p = do
  v <- optional . try $ recNameP <* symbol ":"
  x <- p
  return (v, x)

recordP :: Parser a -> Parser (Record a)
recordP p = mixedRecordPosName <$> (parens $ maybeNamed p `sepBy1` sc)

baseTypeP :: Parser T.BaseType
baseTypeP =     (symbol "Int"  >> return T.IntType)
            <|> (symbol "Bool" >> return T.BoolType)
            <|> (symbol "Real" >> return T.RealType)
            <|> (symbol "Str"  >> return T.StrType)

tabValP :: TabType -> Parser TabVal
tabValP tabType = let cols = getColTypes tabType
                      end = void eol <|> eof
                  in manyTill (rowP cols) end

rowP :: [ScalarType] -> Parser [ScalarVal]
rowP [] = lineof $ return []
rowP (t:ts) = do
  sc
  v <- optional $ fieldP t
  case v of
    Nothing -> lineof $ return []
    Just v' -> do {vs <- rowP ts; return (v':vs)}

fieldP :: ScalarType -> Parser ScalarVal
fieldP t = case t of
  BaseType b -> case b of
    T.IntType -> IntVal <$> intP
    T.BoolType ->     (symbol "True"  >> return (BoolVal True ))
                  <|> (symbol "False" >> return (BoolVal False))
    T.StrType -> StrVal <$> stringLiteral
    T.RealType -> RealVal <$> realP
  UnitType -> symbol "()" >> return UnitVal

recNameP :: Parser RecName
recNameP =     (RecPos  <$> (char '#' >> L.decimal))
           <|> (RecName <$> identifierP)

-- ----- parser utils -----

lineof :: Parser a -> Parser a
lineof = (<* (sc >> eol))

sc :: Parser ()
sc = L.space space empty empty

blankLines :: Parser ()
blankLines = void $ many eol

stringLiteral :: Parser String
stringLiteral = char '"' >> manyTill L.charLiteral (char '"')

identifierP :: Parser String
identifierP = lexeme . try $ (:) <$> letterChar <*> many alphaNumChar

space :: Parser ()
space = void $ takeWhile1P (Just "white space") (`elem` " \t")

intP :: Parser Int
intP = L.signed (return ()) L.decimal

realP :: Parser Float
realP = L.signed (return ()) L.float

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")
