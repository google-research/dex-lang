module Record (Record (..), posRecord, nameRecord, emptyRecord,
               mixedRecord, zipWithRecord, RecName,
               consRecord, unConsRecord, fromPosRecord,
               RecTree (..), emptyRecTree, arbitraryRecord) where

import Util
import Control.Monad
import Data.List (nub, intersperse)
import Data.Traversable
import Test.QuickCheck
import qualified Data.Map.Strict as M

data Record a = Record (M.Map RecName a)  deriving (Eq, Ord)
data RecTree a = RecTree (Record (RecTree a)) | RecLeaf a
data RecName = RecPos Int | RecName String  deriving (Eq, Ord)

instance Functor Record where
  fmap = fmapDefault

instance Foldable Record where
  foldMap = foldMapDefault

instance Traversable Record where
  traverse f (Record m) = fmap Record $ traverse f m

instance Functor RecTree where
  fmap = fmapDefault

instance Foldable RecTree where
  foldMap = foldMapDefault

instance Traversable RecTree where
  traverse f t = case t of
    RecTree r -> fmap RecTree $ traverse (traverse f) r
    RecLeaf x -> fmap RecLeaf $ f x

emptyRecord :: Record a
emptyRecord = Record M.empty

emptyRecTree :: RecTree a
emptyRecTree = RecTree emptyRecord

posRecord :: [a] -> Record a
posRecord = mixedRecord . zip (repeat Nothing)

fromPosRecord :: Record a -> [a]
fromPosRecord (Record m) = case unzip (M.toList m) of
  (ks, vs) | ks == map RecPos [0..(length ks - 1)] -> vs

nameRecord :: [(String, a)] -> Record a
nameRecord = mixedRecord . mapFst Just

mixedRecord ::[(Maybe String, a)] -> Record a
mixedRecord xs = Record $ M.fromList $
    [(RecPos  i, v) | (i, (Nothing, v)) <- zip [0..] xs] ++
    [(RecName k, v) |      (Just k, v)  <-           xs]

zipWithRecord :: (a -> b -> c) -> Record a -> Record b -> Maybe (Record c)
zipWithRecord f (Record m) (Record m')
    | M.keys m == M.keys m' = Just . Record $ M.intersectionWith f m m'
    | otherwise = Nothing

consRecord :: a -> Record a -> Record a
consRecord v r = let vs = fromPosRecord r
                 in posRecord (v:vs)

unConsRecord :: Record a -> (a, Record a)
unConsRecord r = let v:vs = fromPosRecord r
                 in (v, posRecord vs)

instance Show a => Show (Record a) where
  show (Record m) = let showElt (k,v) = case k of
                            RecPos _  -> show v
                            RecName s -> s ++ "=" ++ show v
                        shownElts = map showElt (M.toList m)
                    in "(" ++ concat (intersperse "," shownElts) ++ ")"

instance Show RecName where
  show (RecPos i)  = "#" ++ show i
  show (RecName s) = s

arbitraryName :: Gen String
arbitraryName = liftM2 (:) arbLower (shortList 2 arbValid)
  where arbLower = choose ('\97', '\122')
        arbUpper = choose ('\65', '\90')
        arbNum   = choose ('\48', '\57')
        arbValid = oneof [arbLower, arbUpper, arbNum]

nonNeg :: Gen Int
nonNeg = fmap unwrap arbitrary
  where unwrap (NonNegative x) = x

instance Arbitrary RecName where
  arbitrary = oneof [ fmap RecPos nonNeg
                    , fmap RecName arbitraryName
                    , fmap RecName (elements ["x", "y"]) ]

arbitraryRecord :: Gen a -> Gen (Record a)
arbitraryRecord g = let kvPair = liftM2 (,) arbitrary g
                    in fmap (Record . M.fromList) (shortList 3 kvPair)

instance Arbitrary a => Arbitrary (Record a) where
  arbitrary = arbitraryRecord arbitrary
