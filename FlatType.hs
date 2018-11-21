module FlatType (showVal) where
import Text.PrettyPrint.Boxes
import Data.List (intersperse, transpose)

import Record
import Util
import qualified Data.Map.Strict as M
import qualified Typer as T
import qualified Interpreter as I
import Data.List (partition, foldr1)
import Data.Foldable (toList)

type Except a = Either String a

type TabName = [RecName]
type ScalarTree = RecTree T.BaseType
data TabType = TabType TabName ScalarTree TabType | ValPart ScalarTree

type ColVal = [I.Val]
type IdxColVal = [I.IdxVal]
type TabVal = (Int, [[IdxColVal]], [ColVal])

flattenType :: T.Type -> Except [TabType]
flattenType t = case t of
   T.TabType a b -> do
       leftKeys <- flattenIdxType a
       rightTabs <- flattenType b
       return $ map (TabType [] leftKeys) rightTabs
   T.RecType r -> do
     Record m <- sequence $ fmap flattenType r
     let ts = [(k,t) | (k, ts) <- M.toList m, t <- ts]
     return $ valRec [(k, s) | (k, ValPart s) <- ts]
       : [TabType (k:name) s rest | (k, TabType name s rest) <- ts]
   T.BaseType b -> return $ [ValPart (RecLeaf b)]
   _ -> Left $ "Can't flatten " ++ show t

flattenIdxType :: T.Type -> Except ScalarTree
flattenIdxType t = case t of
   T.RecType r -> fmap RecTree $ sequence (fmap flattenIdxType r)
   T.BaseType b -> return (RecLeaf b)
   _ -> Left $ "Can't flatten index type" ++ show t

valRec :: [(RecName, ScalarTree)] -> TabType
valRec = ValPart . RecTree . Record . M.fromList

unflattenType :: [TabType] -> T.Type
unflattenType tabs = foldr1 mergeTypes (map unflattenTab tabs)

unflattenTab :: TabType -> T.Type
unflattenTab (ValPart st) = unflattenScalarTree st
unflattenTab (TabType name st rest) =
  let t = T.TabType (unflattenScalarTree st) (unflattenTab rest)
  in recTypeFromName name t

unflattenScalarTree :: ScalarTree -> T.Type
unflattenScalarTree st = case st of
  RecTree r -> T.RecType $ fmap unflattenScalarTree r
  RecLeaf b -> T.BaseType b

mergeTypes :: T.Type -> T.Type -> T.Type
mergeTypes (T.RecType (Record m1)) (T.RecType (Record m2)) =
  T.RecType . Record $ M.unionWith mergeTypes m1 m2

recTypeFromName :: [RecName] -> T.Type -> T.Type
recTypeFromName [] = id
recTypeFromName (k:ks) = T.RecType . Record . M.singleton k . recTypeFromName ks

-- ----- flattening vals -----

-- flattenVal :: I.Val -> TabType -> TabVal
-- flattenVal v t = case t of
--   FinalSegmentType colTypes ->
--     FinalSegmentVal 1 [[lookupPath colName v] | (colName, _) <- colTypes]
--   TabType tabname colTypes restType ->
--     let I.TabVal m = lookupPath tabname v
--     in vCat t [ let rhsTab = flattenVal val restType
--                     n = numRows rhsTab
--                     idxTab = map (replicate n . flattenIdxs idxVal) colTypes
--                 in TabVal idxTab rhsTab
--               | (idxVal, val) <- M.toList m]

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

-- lookupPath :: ColName -> I.Val -> I.Val
-- lookupPath [] v = v
-- lookupPath (name:rest) (I.RecVal (Record m)) =
--   let Just v = M.lookup name m
--   in lookupPath rest v

-- lookupIdxPath :: ColName -> I.IdxVal -> I.IdxVal
-- lookupIdxPath [] v = v
-- lookupIdxPath (name:rest) (I.RecIdxVal (Record m)) =
--   let Just v = M.lookup name m
--   in lookupIdxPath rest v

-- ----- printing -----

showVal :: I.Val -> T.ClosedType -> String
showVal v (T.Forall _ t) =
  case flattenType t of
    Left e -> "<unprintable value of type " ++ show t ++ ">"
    Right tsFlat -> "tree"

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
