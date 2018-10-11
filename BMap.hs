module BMap (BMap (..), map, intersectionWith, fromList, lookup) where

import Prelude hiding (map, lookup)
import qualified Data.Map.Strict as Map

data BMap k v = Dict (Map.Map k v) | Broadcast v  deriving (Show)

map :: (a -> b) -> BMap k a -> BMap k b
map f (Dict m) = Dict $ Map.map f m
map f (Broadcast v) = Broadcast $ f v

intersectionWith ::  Ord k => (a -> b -> c) -> BMap k a -> BMap k b -> BMap k c
intersectionWith f (Dict x)      (Dict y)      = Dict $ Map.intersectionWith f x y
intersectionWith f (Dict x)      (Broadcast y) = Dict $ Map.map (flip f y) x
intersectionWith f (Broadcast x) (Dict y)      = Dict $ Map.map (f x) y
intersectionWith f (Broadcast x) (Broadcast y) = Broadcast $ f x y

fromList :: Ord k => [(k, a)] -> BMap k a
fromList = Dict . Map.fromList

lookup :: Ord k => k -> BMap k a -> Maybe a
lookup k (Dict x) = Map.lookup k x
lookup _ (Broadcast v) = Just v
