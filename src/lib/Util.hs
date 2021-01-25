-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Util (
  IsBool (..), mapFst, mapSnd, scan,
  scanM, uncons, unsnoc, repeated, transitiveClosure,
  showErr, enumerate, restructure,
  onSnd, onFst, highlightRegion, findReplace, swapAt, uncurry3,
  measureSeconds,
  bindM2, foldMapM, (...), zipWithT, for,
  docToStr, pprint,
  SnocList, toSL, fromSL, singletonSL, (<$$>)
  ) where

import Control.Exception hiding (throw)
import Control.Monad.Except hiding (Except)
import Data.Functor.Identity (Identity(..))
import Data.List (sort)
import Data.Foldable
import qualified Data.Map.Strict as M
import qualified Data.Text.Prettyprint.Doc             as P
import qualified Data.Text.Prettyprint.Doc.Render.Text as P
import Data.Text (unpack)
import Prelude
import qualified Data.Set as Set
import Control.Monad.State.Strict
import System.CPUTime
import System.IO.Unsafe
import System.Environment

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

showErr :: Show e => Either e a -> Either String a
showErr (Left e) = Left (show e)
showErr (Right x) = Right x

uncons :: [a] -> Maybe (a, [a])
uncons (x:xs) = Just (x, xs)
uncons [] = Nothing

unsnoc :: [a] -> Maybe ([a], a)
unsnoc [] = Nothing
unsnoc l = Just (reverse xs, x)
  where (x:xs) = reverse l

mapFst :: (a -> b) -> [(a, c)] -> [(b, c)]
mapFst f zs = [(f x, y) | (x, y) <- zs]

mapSnd :: (a -> b) -> [(c, a)] -> [(c, b)]
mapSnd f zs = [(x, f y) | (x, y) <- zs]

repeated :: Ord a => [a] -> [a]
repeated = repeatedSorted . sort

repeatedSorted :: Eq a => [a] -> [a]
repeatedSorted [] = []
repeatedSorted [_] = []
repeatedSorted (x:y:rest) | x == y = [x] ++ repeatedSorted (dropWhile (== x) rest)
                          | otherwise = repeatedSorted (y:rest)

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

pprint :: P.Pretty a => a -> String
pprint x = docToStr $ P.pretty x

defaultLayout :: P.LayoutOptions
defaultLayout =
  if unbounded then P.LayoutOptions P.Unbounded else P.defaultLayoutOptions
  where unbounded = unsafePerformIO $ (Just "1"==) <$> lookupEnv "DEX_PPRINT_UNBOUNDED"

docToStr :: P.Doc ann -> String
docToStr doc = unpack $ P.renderStrict $ P.layoutPretty defaultLayout $ doc

newtype SnocList a = UnsafeMakeSnocList [a]

fromSL :: SnocList a -> [a]
fromSL (UnsafeMakeSnocList xs) = reverse xs

toSL :: [a] -> SnocList a
toSL xs = UnsafeMakeSnocList $ reverse xs

singletonSL :: a -> SnocList a
singletonSL x = UnsafeMakeSnocList [x]

instance Semigroup (SnocList a) where
  UnsafeMakeSnocList xs <> UnsafeMakeSnocList ys = UnsafeMakeSnocList $ ys <> xs

instance Monoid (SnocList a) where
  mempty = UnsafeMakeSnocList []

-- === some handy monoids ===

data SetVal a = Set a | NotSet
newtype MonMap k v = MonMap (M.Map k v)  deriving (Show, Eq)

instance Semigroup (SetVal a) where
  x <> NotSet = x
  _ <> Set x  = Set x

instance Monoid (SetVal a) where
  mempty = NotSet

instance (Ord k, Semigroup v) => Semigroup (MonMap k v) where
  MonMap m <> MonMap m' = MonMap $ M.unionWith (<>) m m'

instance (Ord k, Semigroup v) => Monoid (MonMap k v) where
  mempty = MonMap mempty

monMapSingle :: k -> v -> MonMap k v
monMapSingle k v = MonMap (M.singleton k v)

monMapLookup :: (Monoid v, Ord k) => MonMap k v -> k -> v
monMapLookup (MonMap m) k = case M.lookup k m of Nothing -> mempty
                                                 Just v  -> v

(<$$>) :: Functor f => f a -> (a -> b) -> f b
(<$$>) = flip (<$>)
