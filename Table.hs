module Table (Table (..), scalar, map, intersectionWith) where

import Prelude hiding (map, lookup)
import qualified Data.Map.Strict as Map

data Table a b = Table [Bool] (Map.Map [a] b)

scalar ::  Ord a => b -> Table a b
scalar = undefined

map ::  Ord k => (a -> b) -> Table k a -> Table k b
map = undefined

intersectionWith :: Ord k => (a -> b -> c) -> Table k a -> Table k b -> Table k c
intersectionWith = undefined


-- fromList :: Ord k => [(k, a)] -> BMap k a
-- fromList = Dict . Map.fromList

-- lookup :: Ord k => k -> BMap k a -> Maybe a
-- lookup k (Dict x) = Map.lookup k x
-- lookup _ (Broadcast v) = Just v
