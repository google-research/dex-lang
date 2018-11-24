module FlatType (flattenType, unflattenType,
                 flattenVal, unflattenVal,
                 showVal, printTabType, parseHeader,
                 TabType) where
import Text.PrettyPrint.Boxes
import Data.List (intercalate, transpose)

import Record
import Util
import qualified Data.Map.Strict as M
import qualified Typer as T
import qualified Interpreter as I
import Data.List (partition, foldr1, intersperse)
import Data.Foldable (toList)

type Except a = Either String a

type TabName = [RecName]
type ScalarTree = RecTree (Maybe T.BaseType)
data TabType = TabType TabName ScalarTree TabType
             | ValPart ScalarTree
                 deriving (Eq, Show)

flattenType :: T.Type -> Except [TabType]
flattenType t = case t of
   T.TabType a b -> do
       leftKeys <- flattenIdxType a
       rightTabs <- flattenType b
       return $ map (TabType [] leftKeys) rightTabs
   T.RecType r | isEmpty r -> return $ [ValPart (RecLeaf Nothing)]
               | otherwise -> do
     Record m <- sequence $ fmap flattenType r
     let ts = [(k,t) | (k, ts) <- M.toList m, t <- ts]
         maybeVal = case [(k, s) | (k, ValPart s) <- ts] of
                  [] -> []
                  vs -> [valRec vs]
         tabs = [TabType (k:name) s rest | (k, TabType name s rest) <- ts]
     return $ maybeVal ++ tabs
   T.BaseType b -> return $ [ValPart (RecLeaf (Just b))]
   _ -> Left $ "Can't flatten " ++ show t

flattenIdxType :: T.Type -> Except ScalarTree
flattenIdxType t = case t of
   T.RecType r | isEmpty r -> return (RecLeaf Nothing)
               | otherwise -> fmap RecTree $ sequence (fmap flattenIdxType r)
   T.BaseType b -> return (RecLeaf (Just b))
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
  RecLeaf (Just b) -> T.BaseType b
  RecLeaf Nothing  -> T.RecType emptyRecord

mergeTypes :: T.Type -> T.Type -> T.Type
mergeTypes (T.RecType (Record m1)) (T.RecType (Record m2)) =
  T.RecType . Record $ M.unionWith mergeTypes m1 m2
mergeTypes (T.TabType a1 b1) (T.TabType a2 b2) | a1 == a2 =
  T.TabType a1 (mergeTypes b1 b2)

----- flattening vals -----

type ColName = [RecName]
data TabVal = TabVal (M.Map [I.IdxVal] TabVal) | ValPartV [I.Val]

flattenVal :: I.Val -> [TabType] -> [TabVal]
flattenVal v = map (flattenVal' v)

unflattenVal :: [TabVal] -> [TabType] -> I.Val
unflattenVal vs ts = foldr1 mergeVals (zipWith unflattenVal' vs ts)

flattenVal' :: I.Val -> TabType -> TabVal
flattenVal' v t = case t of
  ValPart s -> ValPartV $ map (lookupPath v) (recTreePaths s)
  TabType name s rest ->
    let I.TabVal m = lookupPath v name
    in TabVal $ M.fromList [(flattenIVal k s, flattenVal' v' rest)
                           | (k,v') <- M.toList m]

flattenIVal :: I.IdxVal -> ScalarTree -> [I.IdxVal]
flattenIVal v s = map (lookupPath v) (recTreePaths s)

unflattenVal' :: TabVal -> TabType -> I.Val
unflattenVal' (TabVal m) (TabType tabname s rest) =
  let colNames = recTreePaths s
      tab = I.TabVal $ M.fromList [(unflattenRow k colNames, unflattenVal' v rest)
                                  | (k, v) <- M.toList m]
  in recFromName I.RecVal tabname tab
unflattenVal' (ValPartV v) (ValPart s) =
  unflattenRow v (recTreePaths s)

unflattenRow :: [I.Val] -> [ColName] -> I.Val
unflattenRow vals names =
  foldr1 mergeVals $ zipWith (recFromName I.RecVal) names vals

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

showVal :: I.Val -> T.ClosedType -> String
showVal v (T.Forall _ t) =
  case flattenType t of
    Left e -> "<unprintable value of type " ++ show t ++ ">"
    Right tsFlat -> "tree"

printTabType :: TabType -> String
printTabType t = printTabName t ++ printHeader t

printTabName :: TabType -> String
printTabName t = case getTabName t of
  names | length (concat names) == 0 -> ""
        | otherwise -> "> " ++ (intercalate "  " $ map printName names) ++ "\n"

getTabName :: TabType -> [[RecName]]
getTabName (TabType name _ rest) = name : getTabName rest
getTabName (ValPart _) = []

printHeader :: TabType -> String
printHeader (TabType _ s rest) = printTree s ++ " " ++ printHeader rest
printHeader (ValPart s) = printTree s ++ "\n"

printTree :: ScalarTree -> String
printTree (RecTree r) = printRecord printTree (RecordPrintSpec "\t" ":" "") r
printTree (RecLeaf x) = case x of Nothing -> "()"
                                  Just x' -> show x'

printName :: [RecName] -> String
printName names = concat $ intersperse "." (map show names)

parseHeader :: String -> Except TabType
parseHeader = undefined --tabypeP `sepBy

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
