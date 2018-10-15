module Table (Table, fromScalar, diag, map, map2, iota, printTable, insert) where

import Prelude hiding (map, lookup)
import Data.List (intersperse, transpose)
import qualified Prelude as P
import qualified Data.Map.Strict as M

data Table a b = Table [Bool] (Rows a b)
type Rows a b = [([a], b)]
data MaybeKeyed k v = Keyed [(k, v)] | UnKeyed v

fromScalar :: Ord a => b -> Table a b
fromScalar x = Table [] [([], x)]

insert :: Int -> Int -> Table k a -> Table k a
insert pos num (Table mask rows) =
  let mask' = repeatApply num (insertIdx pos False) mask
  in Table mask' rows

map ::  Ord k => (a -> b) -> Table k a -> Table k b
map f (Table mask rows) = Table mask (mapSnd f rows)

map2 :: Ord k => (a -> b -> c) -> Table k a -> Table k b -> Table k c
map2 f (Table mask1 rows1) (Table mask2 rows2) =
  let mask = zipWith (||) mask1 mask2
      rows = map2' f mask1 mask2 rows1 rows2
  in Table mask rows

map2' :: Ord k => (a -> b -> c) ->
            [Bool] -> [Bool] -> Rows k a -> Rows k b -> Rows k c
map2' f _ _ (([],x):[]) (([],y):[]) = [([], f x y)]
map2' f (m1:ms1) (m2:ms2) rows1 rows2 =
  fromMaybeKeyed (mergeMaybeKeyed (map2' f ms1 ms2)
                                  (toMaybeKeyed m1 rows1)
                                  (toMaybeKeyed m2 rows2))

toMaybeKeyed :: (Ord k) => Bool -> Rows k v -> MaybeKeyed k (Rows k v)
toMaybeKeyed False rows = UnKeyed rows
toMaybeKeyed True  rows = let peelIdx (k:ks, v) = (k, (ks, v))
                          in Keyed $ group (P.map peelIdx rows)

fromMaybeKeyed :: (Ord k) => MaybeKeyed k  (Rows k v) -> Rows k v
fromMaybeKeyed (UnKeyed rows) = rows
fromMaybeKeyed (Keyed rows) = let addIdx (k, (ks, v)) = (k:ks, v)
                              in P.map addIdx $ ungroup rows

mergeMaybeKeyed :: (Ord k) => (a -> b -> c) ->
                   MaybeKeyed k a -> MaybeKeyed k b -> MaybeKeyed k c
mergeMaybeKeyed f (UnKeyed x ) (UnKeyed y ) = UnKeyed $ f x y
mergeMaybeKeyed f (Keyed   xs) (UnKeyed y ) = Keyed $ [(k, f x y) | (k, x) <- xs]
mergeMaybeKeyed f (UnKeyed x ) (Keyed   ys) = Keyed $ [(k, f x y) | (k, y) <- ys]
mergeMaybeKeyed f (Keyed   xs) (Keyed   ys) = Keyed $ mergeWith f xs ys

mergeWith :: (Ord k) => (a -> b -> c) -> [(k,a)] -> [(k,b)] -> [(k,c)]
mergeWith f [] _ = []
mergeWith f _ [] = []
mergeWith f ((k1,x1):rem1) ((k2,x2):rem2) =
  let cur1 = (k1,x1):rem1
      cur2 = (k2,x2):rem2
  in case compare k1 k2 of
       LT -> mergeWith f rem1 cur2
       GT -> mergeWith f cur1 rem2
       EQ -> (k1, f x1 x2) : (mergeWith f rem1 rem2)

group :: (Ord a) => [(a,b)] -> [(a, [b])]
group [] = []
group ((k,v):rem) =
  let (prefix, suffix) = splitWhile ((== k) . fst) rem
      g = v:(P.map snd prefix)
  in (k, g) : group suffix

ungroup ::  [(a, [b])] -> [(a,b)]
ungroup [] = []
ungroup ((k,vs):rem) = (zip (repeat k) vs) ++ ungroup rem

iota :: Table Int Int -> Table Int Int
iota (Table mask rows) = let rows' = [(i:k,i) | (k,v) <- rows, i <- [0..(v-1)]]
                         in Table (True:mask) rows'

diag :: Ord k => Int -> Int -> Table k a -> Table k a
diag i j (Table mask rows) =
  let mi = mask!!i
      mj = mask!!j
      mask' = delIdx j $ replaceIdx i (mi || mj) mask
      rows' = case mj of
          False -> rows
          True  ->
            let i' = numTrue $ take i mask
                j' = numTrue $ take j mask
            in case mi of
                 False -> [(mvIdx  j' i' k, v) | (k,v) <- rows]
                 True  -> [(delIdx j'    k, v) | (k,v) <- rows
                                               , k!!i' == k!!j']
  in Table mask' rows'


mvIdx :: Int -> Int -> [a] -> [a]
mvIdx i j xs = let x = xs!!i
               in delIdx i . insertIdx j x $ xs

numTrue :: [Bool] -> Int
numTrue [] = 0
numTrue (True :xs) = 1 + numTrue xs
numTrue (False:xs) = numTrue xs

insertNothings :: [Bool] -> [a] -> [Maybe a]
insertNothings [] [] = []
insertNothings (True:mask)  (x:xs) = (Just x) : (insertNothings mask xs)
insertNothings (False:mask) xs     = Nothing  : (insertNothings mask xs)

printTable :: (Show a, Show b) => Table a b -> String
printTable (Table mask rows) =
  let rowsWithRank = mapFst (insertNothings mask) rows
  in concat . P.map formatRow . rowsToStrings $ rowsWithRank


showMaybe :: (Show a) => Maybe a -> String
showMaybe Nothing = "*"
showMaybe (Just x) = show x

rowsToStrings :: (Show a, Show b) => [([Maybe a], b)] -> [[String]]
rowsToStrings rows =
  let stringRows = [[showMaybe k | k <- ks] ++ [show v] | (ks,v) <- rows]
      evalMaxLen = foldr (\s w -> max (length s) w) 0
      ws = P.map evalMaxLen . transpose $ stringRows
      padRow xs = [padLeft w ' ' x | (w, x) <- zip ws xs]
  in P.map padRow stringRows

formatRow :: [String] -> String
formatRow rows = " " ++ concat (intersperse " | " rows) ++ "\n"

-- ----- util -----

pad :: Int -> a -> [a] -> [a]
pad n v xs = xs ++ repeatN (n - length(xs)) v

padLeft :: Int -> a -> [a] -> [a]
padLeft  n v xs = repeatN (n - length(xs)) v ++ xs

delIdx :: Int -> [a] -> [a]
delIdx i xs = case splitAt i xs of
  (prefix, x:suffix) -> prefix ++ suffix

replaceIdx :: Int -> a -> [a] -> [a]
replaceIdx i x xs = case splitAt i xs of
  (prefix, _:suffix) -> prefix ++ (x:suffix)

insertIdx :: Int -> a -> [a] -> [a]
insertIdx i x xs = case splitAt i xs of
  (prefix, suffix) -> prefix ++ (x:suffix)

mapFst :: (a -> b) -> [(a, c)] -> [(b, c)]
mapFst f zs = [(f x, y) | (x, y) <- zs]

mapSnd :: (a -> b) -> [(c, a)] -> [(c, b)]
mapSnd f zs = [(x, f y) | (x, y) <- zs]

splitWhile :: (a -> Bool) -> [a] -> ([a], [a])
splitWhile f xs = (takeWhile f xs, dropWhile f xs)

repeatN :: Int -> a -> [a]
repeatN n x = take n (repeat x)

repeatApply :: Int -> (a -> a) -> a -> a
repeatApply n f = foldr (.) id (repeatN n f)
