module Table (Table, fromScalar, diag, map, map2, iota, printTable,
             testAns) where

import Prelude hiding (map, lookup)
import Data.List (intersperse, transpose)
import qualified Prelude as P
import qualified Data.Map.Strict as M


t1 :: Table Int Int
t1 = Table 2 [([Only 10, Anything], 10),
             ([Only 20, Anything], 20)]

t2 :: Table Int Int
t2 = Table 2 [([Anything, Only 1], 1),
             ([Anything, Only 2], 2)]

c :: Comparison [Idx Int]
c = cmpIdxs [Only 2, Anything] [Anything, Only 1]

testAns :: String
testAns =
  show c ++ "\n" ++
  printTable 2 t1 ++ "\n" ++
  printTable 2 t2 ++ "\n" ++
  printTable 2 (map2 (+) t1 t2)


data Idx a = Only a | Anything
data Comparison a = LeftSmall | RightSmall | Match a Ordering deriving (Show)
data Table a b = Table Int (Rows a b)
type Rows a b = [([Idx a], b)]

fromScalar :: Ord a => b -> Table a b
fromScalar x = Table 0 [([], x)]

map ::  Ord k => (a -> b) -> Table k a -> Table k b
map f (Table r rows) = Table r (P.map (second f) rows)

second :: (a -> b) -> (c, a) -> (c, b)
second f (x, y) = (x, f y)

map2 :: Ord k => (a -> b -> c) -> Table k a -> Table k b -> Table k c
map2 f (Table r1 rows1) (Table r2 rows2) = Table 0 $ map2' f rows1 rows2


type MRows a b = ([Bool], [([a], b)])
type ORows a b = [([a], b)]
data MaybeKeyed k v = Keyed [(k, v)] | UnKeyed v

map2'' :: Ord k => (a -> b -> c) ->
            [Bool] -> [Bool] -> ORows k a -> ORows k b -> ORows k c
map2'' f [] [] (([],x):[]) (([],y):[]) = [([], f x y)]
map2'' f (m1:ms1) (m2:ms2) rows1 rows2 =
  fromMaybeKeyed (mergeMaybeKeyed (map2'' f ms1 ms2)
                                  (toMaybeKeyed m1 rows1)
                                  (toMaybeKeyed m2 rows2))

toMaybeKeyed :: (Ord k) => Bool -> ORows k v -> MaybeKeyed k (ORows k v)
toMaybeKeyed False rows = UnKeyed rows
toMaybeKeyed True  rows = let peelIdx (k:ks, v) = (k, (ks, v))
                          in Keyed $ group (P.map peelIdx rows)

fromMaybeKeyed :: (Ord k) => MaybeKeyed k  (ORows k v) -> ORows k v
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

map2' :: Ord k => (a -> b -> c) -> Rows k a -> Rows k b -> Rows k c
map2' f [] _ = []
map2' f _ [] = []
map2' f ((k1,v1):rem1) ((k2,v2):rem2) =
  let cur1 = (k1,v1):rem1
      cur2 = (k2,v2):rem2
      (match, rest1, rest2) =
        case cmpIdxs k1 k2 of
          LeftSmall  -> (Nothing, rem1, cur2)
          RightSmall -> (Nothing, cur1, rem2)
          Match k LT -> (Just k , rem1, cur2)
          Match k GT -> (Just k , cur1, rem2)
          Match k EQ -> (Just k , rem1, rem2)
      rest = map2' f rest1 rest2
   in case match of
        Nothing -> rest
        Just k  -> (k, f v1 v2):rest

splitWhile :: (a -> Bool) -> [a] -> ([a], [a])
splitWhile f xs = (takeWhile f xs, dropWhile f xs)

cmpIdxs :: Ord a => [Idx a] -> [Idx a] -> Comparison [Idx a]
cmpIdxs [] [] = Match [] EQ
cmpIdxs [] ys = Match ys GT
cmpIdxs xs [] = Match xs LT
cmpIdxs (x:xs) (y:ys) =
  let curmatch = case (x,y) of
                   (Only x', Only y') -> case compare x' y' of
                                            LT -> LeftSmall
                                            GT -> RightSmall
                                            EQ -> Match (Only x') EQ
                   (Only x' , Anything) -> Match (Only x') LT
                   (Anything, Only y' ) -> Match (Only y') GT
                   (Anything, Anything) -> Match Anything EQ
  in case curmatch of
    LeftSmall  -> LeftSmall
    RightSmall -> RightSmall
    Match z order -> case cmpIdxs xs ys of
                       LeftSmall  -> LeftSmall
                       RightSmall -> RightSmall
                       Match zs order' -> Match (z:zs) $ mergeOrder order' order

iota :: Table Int Int -> Table Int Int
iota (Table r rows) = let rows' = [((Only i):k, i) | (k,v) <- rows, i <- [0..(v-1)]]
                      in Table (r + 1) rows'

diag :: Ord k => Table k a -> Int -> Int -> Table k a
diag (Table r rows) i j = Table 0 $ diag' rows i j

diag' :: Ord k => Rows k a -> Int -> Int -> Rows k a
diag' [] _ _ = []
diag' ((kraw,v):rem) i j =
  let rest = diag' rem i j
      k = pad (j + 1) Anything kraw
  in case cmpIdx (k!!i) (k!!j) of
       Nothing -> rest
       Just idx -> let k' = delIdx i . replaceIdx j idx $ k
                   in (k',v):rest

pad :: Int -> a -> [a] -> [a]
pad n v xs = xs ++ take (n - length(xs)) (repeat v)

padLeft :: Int -> a -> [a] -> [a]
padLeft  n v xs = take (n - length(xs)) (repeat v) ++ xs

delIdx :: Int -> [a] -> [a]
delIdx i xs = case splitAt i xs of
  (prefix, x:suffix) -> prefix ++ suffix

replaceIdx :: Int -> a -> [a] -> [a]
replaceIdx i x xs = case splitAt i xs of
  (prefix, _:suffix) -> prefix ++ (x:suffix)

cmpIdx :: Ord a => Idx a -> Idx a -> Maybe (Idx a)
cmpIdx (Only x) (Only y) | x == y = Just (Only x)
                         | otherwise = Nothing
cmpIdx (Only x) Anything = Just (Only x)
cmpIdx Anything (Only y) = Just (Only y)
cmpIdx Anything Anything = Just Anything

mergeOrder :: Ordering -> Ordering -> Ordering
mergeOrder x y | x == EQ   = y
               | otherwise = x

instance (Show a) => Show (Idx a) where
  show (Only x) = show x
  show Anything = "*"

mapFst :: (a -> b) -> [(a, c)] -> [(b, c)]
mapFst f zs = [(f x, y) | (x, y) <- zs]

printTable :: (Show a, Show b) => Int -> Table a b -> String
printTable rank (Table r rows) =
  let rowsWithRank = mapFst (pad rank Anything) rows
  in concat . P.map formatRow . rowsToStrings $ rowsWithRank

rowsToStrings :: (Show a, Show b) => [([a], b)] -> [[String]]
rowsToStrings rows =
  let stringRows = [[show k | k <- ks] ++ [show v] | (ks,v) <- rows]
      evalMaxLen = foldr (\s w -> max (length s) w) 0
      ws = P.map evalMaxLen . transpose $ stringRows
      padRow xs = [padLeft w ' ' x | (w, x) <- zip ws xs]
  in P.map padRow stringRows

formatRow :: [String] -> String
formatRow rows = " " ++ concat (intersperse " | " rows) ++ "\n"
