module Table (Table (..), scalar, map, diag, map2) where

import Prelude hiding (map, lookup)
import qualified Data.Map.Strict as Map

data Table a b = Table [Bool] (Map.Map [a] b)  deriving (Show)

scalar ::  Ord a => b -> Table a b
scalar = undefined

map ::  Ord k => (a -> b) -> Table k a -> Table k b
map = undefined

map2 :: Ord k => (a -> b -> c) -> Table k a -> Table k b -> Table k c
map2 = undefined

diag ::  Ord k => Table k a -> Int -> Int -> Table k a
diag = undefined
