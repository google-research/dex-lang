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
     Record m <- sequence $ fmap flattenType r
     let ts = [(k,t) | (k, ts) <- M.toList m, t <- ts]
         maybeVal = case [(k, s) | (k, ValPart s) <- ts] of
                  [] -> []
                  vs -> [valRec vs]
         tabs = [TabType (k:name) s rest | (k, TabType name s rest) <- ts]
     return $ maybeVal ++ tabs
   T.BaseType b -> return $ [ValPart (RecLeaf (BaseType b))]
   _ -> Left $ "Can't flatten " ++ show t

flattenIdxType :: T.Type -> Except ScalarTree
flattenIdxType t = case t of
   T.RecType r | isEmpty r -> return (RecLeaf UnitType)
               | otherwise -> fmap RecTree $ sequence (fmap flattenIdxType r)
   T.BaseType b -> return (RecLeaf (BaseType b))
   _ -> Left $ "Can't flatten index type" ++ show t

valRec :: [(RecName, ScalarTree)] -> TabType
valRec = ValPart . RecTree . Record . M.fromList

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
mergeTypes (T.RecType (Record m1)) (T.RecType (Record m2)) =
  T.RecType . Record $ M.unionWith mergeTypes m1 m2
mergeTypes (T.TabType a1 b1) (T.TabType a2 b2) | a1 == a2 =
  T.TabType a1 (mergeTypes b1 b2)

----- flattening vals -----

type ColName = [RecName]
data ScalarVal = IntVal Int
               | BoolVal Bool
               | RealVal Float
               | StrVal String
               | UnitVal  deriving (Ord, Eq, Show)

data TabVal = TabVal [ScalarType] [[ScalarVal]]

flattenVal :: I.Val -> [TabType] -> [TabVal]
flattenVal v ts = [TabVal (getColTypes t) (getRows v t) | t <- ts]

unflattenVal :: [TabVal] -> [TabType] -> I.Val
unflattenVal vs ts = let rows = [rows | TabVal _ rows <- vs]
                     in foldr1 mergeVals (zipWith unflattenRows rows ts)

getColTypes :: TabType -> [ScalarType]
getColTypes t = case t of
    ValPart s -> getTypes s
    TabType name s rest -> getTypes s ++ getColTypes rest
  where
    getTypes s = map snd (recTreeLeaves s)

getRows :: I.Val -> TabType -> [[ScalarVal]]
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
mergeVals (I.RecVal (Record m1)) (I.RecVal (Record m2)) =
  I.RecVal . Record $ M.unionWith mergeVals m1 m2
mergeVals (I.TabVal m1) (I.TabVal m2) | M.keys m1 == M.keys m1 =
  I.TabVal $ M.intersectionWith mergeVals m1 m2
mergeVals v1 v2 = error ("Can't merge " ++ show v1 ++ " and " ++ show v2)

lookupPath :: I.Val -> [RecName] -> I.Val
lookupPath v [] = v
lookupPath (I.RecVal (Record m)) (name:rest) = let Just v = M.lookup name m
                                               in lookupPath v rest

-- ----- printing -----

showVal :: T.ClosedType -> I.Val -> String
showVal (T.Forall _ t) v =
  case printVal t v of
    Left e -> "<" ++ show t ++ ">"
    Right s -> s

printVal :: T.Type -> I.Val -> Except String
printVal t v = do
  tabTypes <- flattenType t
  let tabVals = flattenVal v tabTypes
  return . intercalate "\n" $ zipWith printTab tabTypes tabVals

printTab :: TabType -> TabVal -> String
printTab t v = printTabType t ++ printTabVal t v

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

printTabVal :: TabType -> TabVal -> String
printTabVal t v = undefined

-- ----- parsing -----

parseVal :: String -> Except (T.Type, I.Val)
parseVal = undefined

parseTabType :: String -> Except TabType
parseTabType s = case parse tabTypeP "" s of
  Left e -> Left (errorBundlePretty e)
  Right x -> Right x

type Parser = Parsec Void String

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

identifierP :: Parser String
identifierP = lexeme . try $ (:) <$> letterChar <*> many alphaNumChar

recNameP :: Parser RecName
recNameP =     (RecPos  <$> (char '#' >> L.decimal))
           <|> (RecName <$> identifierP)

lineof :: Parser a -> Parser a
lineof = (<* (sc >> some eol))

sc :: Parser ()
sc = L.space space empty empty

space :: Parser ()
space = void $ takeWhile1P (Just "white space") (`elem` " \t")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")


--         let vsFlat = map (flattenVal v) tsFlat
--         in unlines $ zipWith showTab vsFlat tsFlat

-- -- TODO: should distinguish each segment, and align components of table name
-- -- with corresponding segment
-- showTab :: TabVal -> TabType -> String
-- showTab v t = let headers = concat $ headerBoxes t
--                   cols = concat $ colBoxes v
--                   colsWithHeaders = zipWith (//) headers cols
--                   name = concat $ intersperse " " (tabName t)
--               in  " " ++ name ++ "\n" ++
--                   (render $ text "  " <> (hsepWith " | " colsWithHeaders))

-- headerBoxes :: TabType -> [[Box]]
-- headerBoxes t =
--   let colsToBoxes = map (text . showColName . fst)
--   in case t of
--     FinalSegmentType colTypes   -> [colsToBoxes colTypes]
--     TabType _ colTypes restType -> colsToBoxes colTypes : headerBoxes restType

-- tabName :: TabType -> [String]
-- tabName (FinalSegmentType _) = []
-- tabName (TabType name _ rest) = showTabName name : tabName rest

-- colBoxes :: TabVal -> [[Box]]
-- colBoxes v =
--   case v of
--     FinalSegmentVal h cols -> [map colToBox cols]
--     TabVal cols rest       -> map colToBox cols : colBoxes rest

-- colToBox :: (Show a) => [a] -> Box
-- colToBox rows = vcat left $ map (text . show) rows

-- vsepWith :: String -> [Box] -> Box
-- vsepWith = undefined

-- hsepWith :: String -> [Box] -> Box
-- hsepWith s bs = case bs of
--   [] -> emptyBox 0 0
--   b:[] -> b
--   b:bs -> let sep = vcat left $ replicate (rows b) (text s)
--           in b <> sep <> hsepWith s bs

-- showTabName :: TabName -> String
-- showTabName = concat $ intersperse "." (map show names)

-- prependName :: RecName -> TabType -> TabType
-- prependName name t = case t of
--   TabType tabname segment rest -> TabType (name:tabname) segment rest
--   FinalSegmentType cols -> FinalSegmentType $ mapFst ((:) name) cols
-- vCat :: TabType -> [TabVal] -> TabVal
-- vCat t tabs = foldr stackTabs (emptyTab t) tabs

-- stackTabs :: TabVal -> TabVal -> TabVal
-- stackTabs (FinalSegmentVal h1 cols1) (FinalSegmentVal h2 cols2) =
--     FinalSegmentVal (h1 + h2) (zipWith (++) cols1 cols2)
-- stackTabs (TabVal cols1 rest1) (TabVal cols2 rest2) =
--     TabVal (zipWith (++) cols1 cols2) (stackTabs rest1 rest2)

-- emptyTab :: TabType -> TabVal
-- emptyTab (FinalSegmentType colTypes) =
--     FinalSegmentVal 0 $ replicate (length colTypes) []
-- emptyTab (TabType _ colTypes restType) =
--     TabVal (replicate (length colTypes) []) (emptyTab restType)

-- flattenIdxs :: I.IdxVal -> ColType -> I.IdxVal
-- flattenIdxs v (name, _) = lookupIdxPath name v

-- numRows :: TabVal -> Int
-- numRows (TabVal _ t) = numRows t
-- numRows (FinalSegmentVal n _) = n
    -- in vCat t [ let rhsTab = flattenVal val restType
    --                 n = numRows rhsTab
    --                 idxTab = map (replicate n . flattenIdxs idxVal) colTypes
    --             in TabVal idxTab rhsTab
    --           | (idxVal, val) <- M.toList m]
