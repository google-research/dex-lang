module Table (Table, scalar, diag, map, map2) where

import Prelude hiding (map, lookup)
import qualified Prelude as P
import qualified Data.Map.Strict as M

data Table a b = Table [Bool] (M.Map [a] b)

instance (Show a, Show b) => Show (Table a b) where
  show (Table mask m) = show (M.toList m)


scalar ::  Ord a => b -> Table a b
scalar x = Table [] $ M.singleton [] x

map ::  Ord k => (a -> b) -> Table k a -> Table k b
map f (Table idxs m) = Table idxs $ M.map f m

map2 :: Ord k => (a -> b -> c) -> Table k a -> Table k b -> Table k c
map2 f (Table idxs1 m1) (Table idxs2 m2) =
  let commonIdxs = zipWith (&&) idxs1 idxs2
      allIdxs    = zipWith (||) idxs1 idxs2
      decompose = unflatten2 . M.mapKeys (splitList commonIdxs)
      m1' = decompose m1
      m2' = decompose m2
      combined = mapIntersectionWith f m1' m2'
      mfinal = M.mapKeys (mergeList idxs1 idxs2) $ flatten3 combined
      in Table allIdxs mfinal

diag ::  Ord k => Table k a -> Int -> Int -> Table k a
diag (Table idxs m) i j =
    let
       iIdx = idxOf idxs i
       delta = (idxOf idxs j) - iIdx
       m' = case (maskIdx idxs i, maskIdx idxs j) of
               (True, True)   -> mapKeysMaybe (diagIdx iIdx delta) m
               (True, False)  -> promoteMapIdx iIdx delta m
               (False, _)     -> m
    in Table (delIdx idxs i) m'

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

delIdx :: [a] -> Int -> [a]
delIdx []     _ = []
delIdx (x:xs) 0 = xs
delIdx (x:xs) i = x:(delIdx xs (i - 1))

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
mergeList (False:m1) (False:m2) (  xs,   ys,   zs) =   (mergeList m1 m2 (xs, ys, zs))
mergeList (False:m1) (True:m2)  (  xs, y:ys,   zs) = y:(mergeList m1 m2 (xs, ys, zs))
mergeList (True:m1)  (False:m2) (x:xs,   ys,   zs) = x:(mergeList m1 m2 (xs, ys, zs))
mergeList (True:m1)  (True:m2)  (  xs,   ys, z:zs) = z:(mergeList m1 m2 (xs, ys, zs))

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
