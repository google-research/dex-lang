module FlatType (showVal) where
import Text.PrettyPrint.Boxes
import Data.List (intersperse, transpose)

import Record
import Util
import qualified Data.Map.Strict as M
import qualified Typer as T
import qualified Interpreter as I

type ColName = [RecName]
type TabName = [RecName]
type Scalar = T.Type

type ColType = (ColName, Scalar)

data TabType = TabType TabName [ColType] TabType
             | FinalSegmentType [ColType]

prependName :: RecName -> TabType -> TabType
prependName name t = case t of
  TabType tabname segment rest -> TabType (name:tabname) segment rest
  FinalSegmentType cols -> FinalSegmentType $ mapFst ((:) name) cols

mergeFinalSegments :: [TabType] -> [TabType]
mergeFinalSegments tabs =
  let nonValTabs = [tab | tab@(TabType _ _ _) <- tabs]
      valTab = FinalSegmentType [col | FinalSegmentType cols <- tabs, col <- cols]
  in valTab:nonValTabs

flattenIdxType :: T.Type -> [ColType]
flattenIdxType t = case t of
   T.RecType (Record m) ->
       [(k:name, dtype) | (k, t') <- M.toList m
                        , (name, dtype) <- flattenIdxType t']
   t -> [([], t)]


flattenType :: T.Type -> [TabType]
flattenType t = case t of
   T.TabType a b -> let leftSegment = flattenIdxType a
                    in map (TabType [] leftSegment) (flattenType b)
   T.RecType (Record m) -> mergeFinalSegments
       [prependName k tab | (k, t') <- M.toList m
                          , tab <- flattenType t']
   x -> [FinalSegmentType [([], x)]]


-- ----- flattening vals -----

type ColVal = [I.Val]
type IdxColVal = [I.IdxVal]

data TabVal = TabVal [IdxColVal] TabVal
            | FinalSegmentVal Int [ColVal]

flattenVal :: I.Val -> TabType -> TabVal
flattenVal v t = case t of
  FinalSegmentType colTypes ->
    FinalSegmentVal 1 [[lookupPath colName v] | (colName, _) <- colTypes]
  TabType tabname colTypes restType ->
    let I.TabVal m = lookupPath tabname v
    in vCat t [ let rhsTab = flattenVal val restType
                    n = numRows rhsTab
                    idxTab = map (replicate n . flattenIdxs idxVal) colTypes
                in TabVal idxTab rhsTab
              | (idxVal, val) <- M.toList m]

vCat :: TabType -> [TabVal] -> TabVal
vCat t tabs = foldr stackTabs (emptyTab t) tabs

stackTabs :: TabVal -> TabVal -> TabVal
stackTabs (FinalSegmentVal h1 cols1) (FinalSegmentVal h2 cols2) =
    FinalSegmentVal (h1 + h2) (zipWith (++) cols1 cols2)
stackTabs (TabVal cols1 rest1) (TabVal cols2 rest2) =
    TabVal (zipWith (++) cols1 cols2) (stackTabs rest1 rest2)

emptyTab :: TabType -> TabVal
emptyTab (FinalSegmentType colTypes) =
    FinalSegmentVal 0 $ replicate (length colTypes) []
emptyTab (TabType _ colTypes restType) =
    TabVal (replicate (length colTypes) []) (emptyTab restType)

flattenIdxs :: I.IdxVal -> ColType -> I.IdxVal
flattenIdxs v (name, _) = lookupIdxPath name v

numRows :: TabVal -> Int
numRows (TabVal _ t) = numRows t
numRows (FinalSegmentVal n _) = n

lookupPath :: ColName -> I.Val -> I.Val
lookupPath [] v = v
lookupPath (name:rest) (I.RecVal (Record m)) =
  let Just v = M.lookup name m
  in lookupPath rest v

lookupIdxPath :: ColName -> I.IdxVal -> I.IdxVal
lookupIdxPath [] v = v
lookupIdxPath (name:rest) (I.RecIdxVal (Record m)) =
  let Just v = M.lookup name m
  in lookupIdxPath rest v

-- ----- printing -----

showVal :: I.Val -> T.ClosedType -> String
showVal v (T.Forall _ t) =
    let tsFlat = flattenType t
        vsFlat = map (flattenVal v) tsFlat
    in unlines $ zipWith showTab vsFlat tsFlat


-- TODO: should distinguish each segment, and align components of table name
-- with corresponding segment
showTab :: TabVal -> TabType -> String
showTab v t = let headers = concat $ headerBoxes t
                  cols = concat $ colBoxes v
                  colsWithHeaders = zipWith (//) headers cols
                  name = concat $ intersperse " " (tabName t)
              in  " " ++ name ++ "\n" ++
                  (render $ text "  " <> (hsepWith " | " colsWithHeaders))

headerBoxes :: TabType -> [[Box]]
headerBoxes t =
  let colsToBoxes = map (text . showColName . fst)
  in case t of
    FinalSegmentType colTypes   -> [colsToBoxes colTypes]
    TabType _ colTypes restType -> colsToBoxes colTypes : headerBoxes restType

tabName :: TabType -> [String]
tabName (FinalSegmentType _) = []
tabName (TabType name _ rest) = showTabName name : tabName rest

colBoxes :: TabVal -> [[Box]]
colBoxes v =
  case v of
    FinalSegmentVal h cols -> [map colToBox cols]
    TabVal cols rest       -> map colToBox cols : colBoxes rest

colToBox :: (Show a) => [a] -> Box
colToBox rows = vcat left $ map (text . show) rows

vsepWith :: String -> [Box] -> Box
vsepWith = undefined

hsepWith :: String -> [Box] -> Box
hsepWith s bs = case bs of
  [] -> emptyBox 0 0
  b:[] -> b
  b:bs -> let sep = vcat left $ replicate (rows b) (text s)
          in b <> sep <> hsepWith s bs

showColName :: ColName -> String
showColName names = concat $ intersperse "." (map show names)

showTabName :: TabName -> String
showTabName = showColName
