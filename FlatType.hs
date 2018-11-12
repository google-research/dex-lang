module FlatType where

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


-- ----- printing -----

type ColVal = [I.Val]
type IdxColVal = [I.IdxVal]

data TabVal = TabVal [IdxColVal] TabVal
            | FinalSegmentVal Int [ColVal]

flattenVal :: TabType -> I.Val -> TabVal
flattenVal t v = case t of
  FinalSegmentType colTypes ->
    FinalSegmentVal 1 [[lookupPath colName v] | (colName, _) <- colTypes]
  TabType tabname colTypes restType ->
    let I.TabVal m = lookupPath tabname v
    in vCat t [ let rhsTab = flattenVal restType val
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

-- showVal :: Val -> ClosedType -> String
-- showVal v (Forall _ t) = show $ flattenVal t v

-- -- render $ text " " <> valToBox v

-- -- valToBox :: Val -> Box
-- -- valToBox v = case v of
-- --   IntVal x -> text (show x)
-- --   TabVal m -> vcat left [ text (show k) <> text " | " <> valToBox v
-- --                         | (k, v) <- M.toList m]
-- --   RecVal r -> text $ show r
-- --   LamVal _ _ _ -> text "<lambda>"
-- --   Builtin _ _  -> text "<builtin>"

-- instance Show IdxVal where
--   show x = case x of
--     Any -> "*"
--     IntIdxVal  x -> show x
--     RealIdxVal x -> show x
--     StrIdxVal  s -> s
--     RecIdxVal  r -> show r
