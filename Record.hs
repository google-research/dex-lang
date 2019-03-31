module Record (Record (..), RecTree (..), recUnionWith,
               zipWithRecord, printRecord, printRecTree,
               RecordPrintSpec (..), defaultRecPrintSpec,
               typeRecPrintSpec, recZipWith, recTreeZip) where

import Util
import Data.List (intercalate)
import Data.Traversable
import qualified Data.Map.Strict as M

data Record a = Rec (M.Map String a)
              | Tup [a] deriving (Eq, Ord)

data RecTree a = RecTree (Record (RecTree a))
               | RecLeaf a  deriving (Eq, Show, Ord)

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
zipWithRecord = undefined -- f (Record m) (Record m')
    -- | M.keys m == M.keys m' = Just . Record $ M.intersectionWith f m m'
    -- | otherwise = Nothing

recZipWith f r r' = unJust (zipWithRecord f r r')

recTreeZip :: RecTree a -> RecTree b -> RecTree (a,b)
recTreeZip (RecTree r) (RecTree r') = RecTree $ recZipWith recTreeZip r r'
recTreeZip (RecLeaf x) (RecLeaf x') = RecLeaf (x, x')

instance Show a => Show (Record a) where
  show = printRecord show defaultRecPrintSpec

data RecordPrintSpec = RecordPrintSpec { kvSep :: String
                                       , recSep :: String
                                       , trailSep :: String
                                       , order :: Maybe [String]}

defaultRecPrintSpec = RecordPrintSpec "=" "," "" Nothing
typeRecPrintSpec    = RecordPrintSpec "::" "," "" Nothing

printRecord :: (a -> String) -> RecordPrintSpec -> Record a -> String
printRecord showVal spec (Tup [x]) = error "singleton tuple"
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
