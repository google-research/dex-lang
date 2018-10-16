module Table (Table, fromScalar, toScalar, diag, mapD, mapD2, iota,
              printTable, insert) where

import Prelude hiding (map, lookup)
import Data.List (intersperse, transpose)
import qualified Prelude as P
import qualified Data.Map.Strict as M


data Table a b = Table [([Maybe a], b)]
data MMap k v = MMap (M.Map k v) | Always v
type T = Table

fromScalar :: Ord a => b -> T a b
fromScalar x = Table [([], x)]

toScalar :: Ord a => T a b -> b
toScalar (Table [([], x)]) = x

insert :: Int -> Int -> T k a -> T k a
insert pos num (Table rows) =
  let update = composeN num $ insertIdx pos Nothing
  in Table [(update ks, v) | (ks, v) <- rows]

mapD ::  Ord k => Int -> (T k a -> T k b) -> T k a -> T k b
mapD d = composeN d map

map ::  Ord k => (T k a -> T k b) -> T k a -> T k b
map f t = fromMMap $ map' f (toMMap t)

mapD2 :: Ord k => Int -> (T k a -> T k b -> T k c) -> T k a -> T k b -> T k c
mapD2 d = composeN d map2

map2 :: Ord k => (T k a -> T k b -> T k c) -> T k a -> T k b -> T k c
map2 f x y = fromMMap $ map2' f (toMMap x) (toMMap y)

toMMap :: Ord k => T k v -> MMap k (T k v)
toMMap (Table rows) =
    let peelIdx (k:ks, v) = (k, (ks, v))
    in case group (P.map peelIdx rows) of
        [(Nothing, rows')] -> Always $ Table rows'
        groupedRows -> let rows' = [(unJust k, Table v) | (k, v) <- groupedRows]
                       in MMap (M.fromList rows')

fromMMap :: Ord k => MMap k (T k v) -> T k v
fromMMap (Always t) = t
fromMMap (MMap m)   = Table [(Just k : ks, v) | (k, Table rows) <- M.toList m
                                              , (ks, v) <- rows]

iota :: T Int Int -> T Int Int
iota (Table [([], v)]) = Table [([Just i], i) | i <- [0..(v-1)]]

diag :: Ord k => Int -> Int -> Table k a -> Table k a
diag 0 j (Table rows) = Table $ mapFst (mvIdx j 1) rows
diag i j t = mapD i (diag 0 j) t

merge :: Ord k => Table k a -> Table k a
merge = fromMMap . merge' . map' toMMap . toMMap

-- -- ----- operations on maps -----

map' :: (a -> b) -> MMap k a -> MMap k b
map' f (Always v) = Always $ f v
map' f (MMap m) = MMap $ M.map f m

map2' :: Ord k => (a -> b -> c) -> MMap k a -> MMap k b -> MMap k c
map2' f (Always x) (Always y) = Always $ f x y
map2' f (Always x) (MMap  my) = MMap $ M.map (f x) my
map2' f (MMap  mx) (Always y) = MMap $ M.map (flip f $ y) mx
map2' f (MMap  mx) (MMap  my) = MMap $ M.intersectionWith f mx my


reduce' :: (v -> v -> v) -> v -> MMap k v -> v
reduce' = undefined

merge' :: MMap k (MMap k v) -> MMap k v
merge' = undefined

-- ----- util -----

group :: (Ord a) => [(a,b)] -> [(a, [b])]
group [] = []
group ((k,v):rem) =
  let (prefix, suffix) = splitWhile ((== k) . fst) rem
      g = v:(P.map snd prefix)
  in (k, g) : group suffix

ungroup ::  [(a, [b])] -> [(a,b)]
ungroup [] = []
ungroup ((k,vs):rem) = (zip (repeat k) vs) ++ ungroup rem

unJust :: Maybe a -> a
unJust (Just x) = x
unJust Nothing = error "whoops!"

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

mvIdx :: Int -> Int -> [a] -> [a]
mvIdx i j xs = let x = xs!!i
               in delIdx i . insertIdx j x $ xs

mapFst :: (a -> b) -> [(a, c)] -> [(b, c)]
mapFst f zs = [(f x, y) | (x, y) <- zs]

mapSnd :: (a -> b) -> [(c, a)] -> [(c, b)]
mapSnd f zs = [(x, f y) | (x, y) <- zs]

splitWhile :: (a -> Bool) -> [a] -> ([a], [a])
splitWhile f xs = (takeWhile f xs, dropWhile f xs)

repeatN :: Int -> a -> [a]
repeatN n x = take n (repeat x)

composeN :: Int -> (a -> a) -> a -> a
composeN n f = foldr (.) id (repeatN n f)

-- -- ----- printing -----

printTable :: (Show a, Show b) => Table a b -> String
printTable (Table rows) = concat . P.map formatRow . rowsToStrings $ rows

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
