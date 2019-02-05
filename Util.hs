module Util (group, ungroup, unJust, pad, padLeft, delIdx, replaceIdx,
             insertIdx, mvIdx, mapFst, mapSnd, splitOn,
             composeN, mapMaybe, lookup, uncons, repeated, shortList,
             showErr, listDiff, splitMap) where
import Data.List (sort)
import Prelude hiding (lookup)
import Test.QuickCheck
import qualified Data.Set as Set
import qualified Data.Map.Strict as M

splitMap :: Ord k => [k] -> M.Map k v -> (M.Map k v, M.Map k v)
splitMap ks m = let ks' = Set.fromList ks
                    pos = M.filterWithKey (\k _ -> k `Set.member` ks') m
                in (pos, m M.\\ pos)

listDiff :: Ord a => [a] -> [a] -> [a]
listDiff xs ys = Set.toList $ Set.difference (Set.fromList xs) (Set.fromList ys)

showErr :: Show e => Either e a -> Either String a
showErr (Left e) = Left (show e)
showErr (Right x) = Right x

group :: (Ord a) => [(a,b)] -> [(a, [b])]
group [] = []
group ((k,v):xs) =
  let (prefix, suffix) = span ((== k) . fst) xs
      g = v:(map snd prefix)
  in (k, g) : group suffix

ungroup ::  [(a, [b])] -> [(a,b)]
ungroup [] = []
ungroup ((k,vs):xs) = (zip (repeat k) vs) ++ ungroup xs

unJust :: Maybe a -> a
unJust (Just x) = x
unJust Nothing = error "whoops!"

uncons :: [a] -> (a, [a])
uncons (x:xs) = (x, xs)

pad :: a -> Int -> [a] -> [a]
pad v n xs = xs ++ replicate (n - length(xs)) v

padLeft :: a -> Int -> [a] -> [a]
padLeft v n xs = replicate (n - length(xs)) v ++ xs

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
mvIdx i j xs | j == i = xs
             | j < i = let x = xs!!i
                       in insertIdx j x . delIdx i $ xs

mapFst :: (a -> b) -> [(a, c)] -> [(b, c)]
mapFst f zs = [(f x, y) | (x, y) <- zs]

mapSnd :: (a -> b) -> [(c, a)] -> [(c, b)]
mapSnd f zs = [(x, f y) | (x, y) <- zs]

mapMaybe :: (a -> Maybe b) -> [a] -> [b]
mapMaybe _ [] = []
mapMaybe f (x:xs) = let rest = mapMaybe f xs
                    in case f x of
                        Just y  -> y : rest
                        Nothing -> rest

composeN :: Int -> (a -> a) -> a -> a
composeN n f = foldr (.) id (replicate n f)

lookup :: (Eq a) => a -> [a] -> Maybe Int
lookup _ [] = Nothing
lookup target (x:xs) | x == target = Just 0
                     | otherwise = do
                         ans <- lookup target xs
                         return (ans + 1)

repeated :: Ord a => [a] -> [a]
repeated = repeatedSorted . sort

repeatedSorted :: Eq a => [a] -> [a]
repeatedSorted [] = []
repeatedSorted [_] = []
repeatedSorted (x:y:rest) | x == y = [x] ++ repeatedSorted (dropWhile (== x) rest)
                          | otherwise = repeatedSorted (y:rest)

shortList :: Int -> Gen a -> Gen [a]
shortList n g = do
   n' <- choose (0, n)
   sequence $ replicate n' g

splitOn :: (a -> Bool) -> [a] -> [[a]]
splitOn f s = let (prefix, suffix) = break f s
              in case suffix of
                   [] -> [prefix]
                   x:xs -> prefix : splitOn f xs
