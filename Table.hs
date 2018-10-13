module Table (Table, fromScalar, diag, map, map2, iota) where

import Prelude hiding (map, lookup)
import qualified Prelude as P
import qualified Data.Map.Strict as M

data Table a b = Table [Bool] (M.Map [a] b)

instance (Show a, Show b) => Show (Table a b) where
  show (Table mask m) = show (M.toList m)


fromScalar :: Ord a => b -> Table a b
fromScalar x = Table [] $ M.singleton [] x

map ::  Ord k => (a -> b) -> Table k a -> Table k b
map f (Table idxs m) = Table idxs $ M.map f m

iota :: Table Int Int -> Table Int Int
iota (Table idxs m) =
    let f n = M.fromList $ zip [0..n-1] [0..n-1]
        g (is, i) = i:is
        m' = M.mapKeys g . flatten2 . M.map f $ m
    in Table (True:idxs) m'

map2 :: Ord k => (a -> b -> c) -> Table k a -> Table k b -> Table k c
map2 f (Table idxs1 m1) (Table idxs2 m2) =
  let decompose idxs = unflatten2 . M.mapKeys (splitList idxs)
      m1' = decompose (idxs1 `sharedWith` idxs2) m1
      m2' = decompose (idxs2 `sharedWith` idxs1) m2
      combined = mapIntersectionWith f m1' m2'
      mfinal = M.mapKeys (mergeList idxs1 idxs2) $ flatten3 combined
      allIdxs = longestOr idxs1 idxs2
      in Table allIdxs mfinal

sharedWith :: [Bool] -> [Bool] -> [Bool]
sharedWith xs [] = take (numTrue xs) (repeat False)
sharedWith [] _ = []
sharedWith (False:xs) ys = sharedWith xs ys
sharedWith (True:xs) (y:ys) = y : sharedWith xs ys

longestOr :: [Bool] -> [Bool] -> [Bool]
longestOr xs [] = xs
longestOr [] ys = ys
longestOr (x:xs) (y:ys) = (x || y) : longestOr xs ys

diag ::  Ord k => Table k a -> Int -> Int -> Table k a
diag (Table idxs m) i j =
    let
       iIdx = idxOf idxs i
       delta = (idxOf idxs j) - iIdx
       m' = case (maskIdx idxs i, maskIdx idxs j) of
               (True, True)   -> mapKeysMaybe (diagIdx iIdx delta) m
               (True, False)  -> promoteMapIdx iIdx delta m
               (False, _)     -> m
    in Table (updateIdxs i j idxs) m'

updateIdxs :: Int -> Int -> [Bool] -> [Bool]
updateIdxs i j idxs =
  let idxs' = case (idxs !! i, idxs !! j) of
                (True, False) -> setTrue j idxs
                otherwise     -> idxs
  in delIdx i idxs'

mapKeysMaybe :: (Ord k1, Ord k2) => (k1 -> Maybe k2) -> M.Map k1 v -> M.Map k2 v
mapKeysMaybe f = M.fromList . mapFstMaybe f . M.toList

mapFstMaybe :: (a -> Maybe b) -> [(a, c)] -> [(b, c)]
mapFstMaybe f [] = []
mapFstMaybe f ((a,c):xs) = let rest = mapFstMaybe f xs
                           in case f a of
                                Just b -> (b,c):rest
                                Nothing -> rest

maskIdx :: [Bool] -> Int -> Bool
maskIdx []     _ = False
maskIdx (x:xs) 0 = x
maskIdx (x:xs) i = maskIdx xs (i - 1)

diagIdx :: Eq k => Int -> Int -> [k] -> Maybe [k]
diagIdx i delta init = let (prefix, suffix) = splitAt i init
                           (x, xs) = uncons suffix
                       in if (xs !! delta) == x
                             then Just $ prefix ++ xs
                             else Nothing

uncons :: [a] -> (a, [a])
uncons (x:xs) = (x,xs)

delIdx :: Int -> [a] -> [a]
delIdx _ []     = []
delIdx 0 (x:xs) = xs
delIdx i (x:xs) = x:(delIdx (i - 1) xs)

setTrue :: Int -> [Bool] -> [Bool]
setTrue n xs = case splitAt n xs of
  (prefix, _:suffix) -> prefix ++ (True : suffix)

idxOf :: [Bool] -> Int -> Int
idxOf mask i = numTrue $ take i mask

numTrue :: [Bool] -> Int
numTrue [] = 0
numTrue (True:xs) = 1 + numTrue xs
numTrue (False:xs) = numTrue xs

promoteMapIdx :: (Ord k) => Int -> Int -> M.Map [k] a -> M.Map [k] a
promoteMapIdx _ 0     m = m
promoteMapIdx i delta m = M.mapKeys (promoteElt i delta) m

promoteElt :: Int -> Int -> [a] -> [a]
promoteElt i delta init = let (prefix, suffix) = splitAt i init
                              (x, xs) = uncons suffix
                              (prefix2, suffix2) = splitAt delta xs
                          in prefix ++ (prefix2 ++ x:suffix2)

type Map2 k1 k2 a = M.Map k1 (M.Map k2 a)
type Map3 k1 k2 k3 a = M.Map k1 (Map2 k2 k3 a)

splitList :: [Bool] -> [a] -> ([a], [a])
splitList [] [] = ([], [])
splitList (v:vs) (x:xs) = let (ys, zs) = splitList vs xs
                          in case v of
                               True  -> (ys, x:zs)
                               False -> (x:ys, zs)

mergeList :: [Bool] -> [Bool] -> ([a], [a], [a]) -> [a]
mergeList [] [] ([], [], []) = []
-- mergeList (False:m1) (False:m2) (  xs,   ys,   zs) =   (mergeList m1 m2 (xs, ys, zs))
-- mergeList (False:m1) (True:m2)  (x:xs,   ys,   zs) = x:(mergeList m1 m2 (xs, ys, zs))
-- mergeList (True:m1)  (False:m2) (  xs, y:ys,   zs) = y:(mergeList m1 m2 (xs, ys, zs))
-- mergeList (True:m1)  (True:m2)  (  xs,   ys, z:zs) = z:(mergeList m1 m2 (xs, ys, zs))

unflatten2 :: (Ord k1, Ord k2) => M.Map (k1,k2) a -> Map2 k1 k2 a
unflatten2 m = let l = [(k1, [(k2, v)]) | ((k1, k2), v) <- M.toList m]
               in M.map M.fromList . M.fromListWith (++) $ l

flatten2 :: (Ord k1, Ord k2) => Map2 k1 k2 a -> M.Map (k1,k2) a
flatten2 m = M.fromList [((k1, k2), v) | (k1, m') <- M.toList m ,
                                         (k2, v)  <- M.toList m']


flatten3 :: (Ord k1, Ord k2, Ord k3) => Map3 k1 k2 k3 a -> M.Map (k1,k2,k3) a
flatten3 m = M.fromList [((k1, k2, k3), v) | (k1, m')  <- M.toList m  ,
                                             (k2, m'') <- M.toList m' ,
                                             (k3, v)   <- M.toList m'']

mapIntersectionWith :: (Ord k1, Ord k2, Ord k3) =>
  (a -> b -> c) -> Map2 k1 k3 a -> Map2 k2 k3 b -> Map3 k1 k2 k3 c
mapIntersectionWith f m1 m2 = M.map (\x ->
                              M.map (\y ->
                              M.intersectionWith f x y) m2) m1
