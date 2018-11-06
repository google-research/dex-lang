module Record (Record, posRecord, nameRecord, emptyRecord, zipWithRecord) where

import Util
import Control.Monad
import Data.List (nub, intersperse)
import Data.Traversable
import qualified Data.Map.Strict as M

data Record a = Record (M.Map RecName a)  deriving (Eq, Ord)

data RecName = RecPos Int | RecName String  deriving (Show, Eq, Ord)

instance Functor Record where
  fmap = fmapDefault

instance Foldable Record where
  foldMap = foldMapDefault

instance Traversable Record where
  traverse f (Record m) = fmap Record $ traverse f m

emptyRecord :: Record a
emptyRecord = Record M.empty

posRecord :: [a] -> Record a
posRecord = Record . M.fromList . zip (map RecPos [0..])

nameRecord :: [(String, a)] -> Record a
nameRecord = Record . M.fromList . mapFst RecName

zipWithRecord :: (a -> b -> c) -> Record a -> Record b -> Maybe (Record c)
zipWithRecord f (Record m) (Record m')
    | M.keys m == M.keys m' = Just . Record $ M.intersectionWith f m m'
    | otherwise = Nothing

instance Show a => Show (Record a) where
  show (Record m) = let showElt (k,v) = case k of
                            RecPos _  -> show v
                            RecName s -> s ++ "=" ++ show v
                        shownElts = map showElt (M.toList m)
                    in "(" ++ concat (intersperse "," shownElts) ++ ")"
