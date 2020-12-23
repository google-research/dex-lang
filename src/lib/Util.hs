-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Util (IsBool (..), group, ungroup, pad, padLeft, delIdx, replaceIdx,
             insertIdx, mvIdx, mapFst, mapSnd, splitOn, scan,
             scanM, composeN, mapMaybe, uncons, repeated, transitiveClosure,
             showErr, listDiff, splitMap, enumerate, restructure,
             onSnd, onFst, highlightRegion, findReplace, swapAt, uncurry3,
             measureSeconds,
             bindM2, foldMapM, lookupWithIdx, (...), zipWithT, for) where

import Data.Functor.Identity (Identity(..))
import Data.List (sort)
import Data.Foldable
import Prelude
import qualified Data.Set as Set
import qualified Data.Map.Strict as M
import Control.Monad.State.Strict
import System.CPUTime

import Cat

class IsBool a where
  toBool :: a -> Bool

swapAt :: Int -> a -> [a] -> [a]
swapAt _ _ [] = error "swapping to empty list"
swapAt 0 y (_:xs) = y:xs
swapAt n y (x:xs) = x:(swapAt (n-1) y xs)

onFst :: (a -> b) -> (a, c) -> (b, c)
onFst f (x, y) = (f x, y)

onSnd :: (a -> b) -> (c, a) -> (c, b)
onSnd f (x, y) = (x, f y)

enumerate :: Traversable f => f a -> f (Int, a)
enumerate xs = evalState (traverse addCount xs) 0
  where addCount :: a -> State Int (Int, a)
        addCount x = do n <- get
                        put (n + 1)
                        return (n, x)

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

uncons :: [a] -> (a, [a])
uncons (x:xs) = (x, xs)
uncons [] = error "whoops! [uncons]"

pad :: a -> Int -> [a] -> [a]
pad v n xs = xs ++ replicate (n - length(xs)) v

padLeft :: a -> Int -> [a] -> [a]
padLeft v n xs = replicate (n - length(xs)) v ++ xs

delIdx :: Int -> [a] -> [a]
delIdx i xs = case splitAt i xs of
  (prefix, _:suffix) -> prefix ++ suffix
  (prefix, []) -> prefix -- Already not there

replaceIdx :: Int -> a -> [a] -> [a]
replaceIdx i x xs = case splitAt i xs of
  (prefix, _:suffix) -> prefix ++ (x:suffix)
  (prefix, []) -> prefix ++ [x]

insertIdx :: Int -> a -> [a] -> [a]
insertIdx i x xs = case splitAt i xs of
  (prefix, suffix) -> prefix ++ (x:suffix)

mvIdx :: Int -> Int -> [a] -> [a]
mvIdx i j xs | j == i = xs
             | j < i = let x = xs!!i
                       in insertIdx j x . delIdx i $ xs
             | otherwise = let x = xs!!i
                           in  delIdx i . insertIdx j x $ xs

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

repeated :: Ord a => [a] -> [a]
repeated = repeatedSorted . sort

repeatedSorted :: Eq a => [a] -> [a]
repeatedSorted [] = []
repeatedSorted [_] = []
repeatedSorted (x:y:rest) | x == y = [x] ++ repeatedSorted (dropWhile (== x) rest)
                          | otherwise = repeatedSorted (y:rest)

splitOn :: (a -> Bool) -> [a] -> [[a]]
splitOn f s = let (prefix, suffix) = break f s
              in case suffix of
                   [] -> [prefix]
                   _:xs -> prefix : splitOn f xs

restructure :: Traversable f => [a] -> f b -> f a
restructure xs structure = evalState (traverse procLeaf structure) xs
  where procLeaf :: b -> State [a] a
        procLeaf _ = do ~(x:rest) <- get
                        put rest
                        return x

highlightRegion :: (Int, Int) -> String -> String
highlightRegion pos@(low, high) s
  | low > high || high > length s = error $ "Bad region: \n"
                                              ++ show pos ++ "\n" ++ s
  | otherwise =
    -- TODO: flag to control line numbers
    -- (disabling for now because it makes quine tests tricky)
    -- "Line " ++ show (1 + lineNum) ++ "\n"

    allLines !! lineNum ++ "\n"
    ++ take start (repeat ' ') ++ take (stop - start) (repeat '^') ++ "\n"
  where
    allLines = lines s
    (lineNum, start, stop) = getPosTriple pos allLines

getPosTriple :: (Int, Int) -> [String] -> (Int, Int, Int)
getPosTriple (start, stop) lines_ = (lineNum, start - offset, stop')
  where
    lineLengths = map ((+1) . length) lines_
    lineOffsets = cumsum lineLengths
    lineNum = maxLT lineOffsets start
    offset = lineOffsets  !! lineNum
    stop' = min (stop - offset) (lineLengths !! lineNum)

cumsum :: [Int] -> [Int]
cumsum xs = scanl (+) 0 xs

maxLT :: Ord a => [a] -> a -> Int
maxLT [] _ = 0
maxLT (x:xs) n = if n < x then -1
                          else 1 + maxLT xs n

-- TODO: find a more efficient implementation
findReplace :: Eq a => [a] -> [a] -> [a] -> [a]
findReplace _ _ [] = []
findReplace old new s@(x:xs) =
  if take n s == old
    then new ++ recur (drop n s)
    else x : recur xs
  where n = length old
        recur = findReplace old new

scan :: Traversable t => (a -> s -> (b, s)) -> t a -> s -> (t b, s)
scan f xs s = runState (traverse (asState . f) xs) s

scanM :: (Monad m, Traversable t)
  => (a -> s -> m (b, s)) -> t a -> s -> m (t b, s)
scanM f xs s = runStateT (traverse (asStateT . f) xs) s

asStateT :: Monad m => (s -> m (a, s)) -> StateT s m a
asStateT f = do
  s <- get
  (ans, s') <- lift $ f s
  put s'
  return ans

asState :: (s -> (a, s)) -> State s a
asState f = asStateT (Identity . f)

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (x, y, z) = f x y z

bindM2 :: Monad m => (a -> b -> m c) -> m a -> m b -> m c
bindM2 f ma mb = do
  a <- ma
  b <- mb
  f a b

(...) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
f ... g = \x y -> f $ g x y

foldMapM :: (Monad m, Monoid w, Foldable t) => (a -> m w) -> t a -> m w
foldMapM f xs = foldM (\acc x -> (acc<>) <$> f x ) mempty xs

lookupWithIdx :: Eq a => a -> [(a, b)] -> Maybe (Int, b)
lookupWithIdx k vals = lookup k $ [(x, (i, y)) | (i, (x, y)) <- zip [0..] vals]

-- NOTE: (toList args) has to be at least as long as (toList trav)
zipWithT :: (Traversable t, Monad h, Foldable f) => (a -> b -> h c) -> t a -> f b -> h (t c)
zipWithT f trav args = flip evalStateT (toList args) $ flip traverse trav $ \e -> getNext >>= lift . f e
  where getNext = get >>= \(h:t) -> put t >> return h

for :: Functor f => f a -> (a -> b) -> f b
for = flip fmap

transitiveClosure :: forall a. Ord a => (a -> [a]) -> [a] -> [a]
transitiveClosure getParents seeds =
  toList $ snd $ runCat (mapM_ go seeds) mempty
  where
    go :: a -> Cat (Set.Set a) ()
    go x = do
      visited <- look
      unless (x `Set.member` visited) $ do
        extend $ Set.singleton x
        mapM_ go $ getParents x

measureSeconds :: MonadIO m => m a -> m (a, Double)
measureSeconds m = do
  t1 <- liftIO $ getCPUTime
  ans <- m
  t2 <- liftIO $ getCPUTime
  return (ans, (fromIntegral $ t2 - t1) / 1e12)
