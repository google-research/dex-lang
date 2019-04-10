module Record (Record (..), RecTree (..), recUnionWith,
               zipWithRecord, printRecord, printRecTree,
               RecordPrintSpec (..), defaultRecPrintSpec,
               typeRecPrintSpec, recZipWith, recTreeZip, recTreeZipEq,
               recNameVals, recLookup, RecIdx (..), RecTreeIdx,
               recTreeJoin, unLeaf
              ) where


import Util
import Data.List (intercalate)
import Data.Traversable
import qualified Data.Map.Strict as M

data Record a = Rec (M.Map String a)
              | Tup [a] deriving (Eq, Ord)

data RecTree a = RecTree (Record (RecTree a))
               | RecLeaf a  deriving (Eq, Show, Ord)

data RecIdx = RecIdx String | TupIdx Int  deriving (Eq, Show, Ord)
type RecTreeIdx = [RecIdx]

instance Functor Record where
  fmap = fmapDefault

instance Foldable Record where
  foldMap = foldMapDefault

instance Traversable Record where
  traverse f (Rec m) = fmap Rec $ traverse f m
  traverse f (Tup m) = fmap Tup $ traverse f m

instance Functor RecTree where
  fmap = fmapDefault

instance Foldable RecTree where
  foldMap = foldMapDefault

instance Traversable RecTree where
  traverse f t = case t of
    RecTree r -> fmap RecTree $ traverse (traverse f) r
    RecLeaf x -> fmap RecLeaf $ f x

recUnionWith :: (a -> a -> a) -> Record a -> Record a -> Record a
recUnionWith = undefined -- f (Record m1) (Record m2) = Record $ M.unionWith f m1 m2

zipWithRecord :: (a -> b -> c) -> Record a -> Record b -> Maybe (Record c)
zipWithRecord f (Rec m) (Rec m') | M.keys m == M.keys m' =  Just $ Rec $ M.intersectionWith f m m'
zipWithRecord f (Tup xs) (Tup xs') | length xs == length xs' = Just $ Tup $ zipWith f xs xs'
zipWithRecord _ _ _ = Nothing

recZipWith f r r' = unJust (zipWithRecord f r r')

recTreeZip :: RecTree a -> RecTree b -> RecTree (a, RecTree b)
recTreeZip (RecTree r) (RecTree r') = RecTree $ recZipWith recTreeZip r r'
recTreeZip (RecLeaf x) x' = RecLeaf (x, x')

recTreeJoin :: RecTree (RecTree a) -> RecTree a
recTreeJoin (RecLeaf t) = t
recTreeJoin (RecTree r) = RecTree $ fmap recTreeJoin r

recTreeZipEq :: RecTree a -> RecTree b -> RecTree (a, b)
recTreeZipEq (RecTree r) (RecTree r') = RecTree $ recZipWith recTreeZipEq r r'
recTreeZipEq (RecLeaf x) (RecLeaf x') = RecLeaf (x, x')

unLeaf :: RecTree a -> a
unLeaf (RecLeaf x) = x

instance Show a => Show (Record a) where
  show = printRecord show defaultRecPrintSpec

data RecordPrintSpec = RecordPrintSpec { kvSep :: String
                                       , recSep :: String
                                       , trailSep :: String
                                       , order :: Maybe [String]}

defaultRecPrintSpec = RecordPrintSpec "=" "," "" Nothing
typeRecPrintSpec    = RecordPrintSpec "::" "," "" Nothing

printRecord :: (a -> String) -> RecordPrintSpec -> Record a -> String
printRecord showVal spec r = paren $ intercalate (recSep spec) elts
  where showKV (k,v) = k ++ kvSep spec ++ showVal v
        elts = case r of
                 Rec m  -> map showKV (M.toList m)
                 Tup xs -> map showVal xs

printRecTree :: (a -> String) -> RecTree a -> String
printRecTree printLeaf tree = case tree of
  RecTree r -> printRecord (printRecTree printLeaf) defaultRecPrintSpec r
  RecLeaf l -> printLeaf l

paren :: String -> String
paren s = "(" ++ s ++ ")"

recNameVals :: Record a -> [(RecIdx, a)]
recNameVals = undefined

recLookup :: RecIdx -> Record a -> a
recLookup = undefined
