module Record (Record (..), posRecord, nameRecord, emptyRecord,
               mixedRecord, zipWithRecord,
               consRecord, unConsRecord, fromPosRecord) where

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
posRecord = mixedRecord . zip (repeat Nothing)

fromPosRecord :: Record a -> [a]
fromPosRecord (Record m) = case unzip (M.toList m) of
  (ks, vs) | ks == map RecPos [0..(length ks - 1)] -> vs

nameRecord :: [(String, a)] -> Record a
nameRecord = mixedRecord . mapFst Just

mixedRecord ::[(Maybe String, a)] -> Record a
mixedRecord xs = Record $ M.fromList $
    [(RecPos  i, v) | (i, (Nothing, v)) <- zip [0..] xs] ++
    [(RecName k, v) |      (Just k, v)  <-           xs]

zipWithRecord :: (a -> b -> c) -> Record a -> Record b -> Maybe (Record c)
zipWithRecord f (Record m) (Record m')
    | M.keys m == M.keys m' = Just . Record $ M.intersectionWith f m m'
    | otherwise = Nothing

consRecord :: a -> Record a -> Record a
consRecord v r = let vs = fromPosRecord r
                 in posRecord (v:vs)

unConsRecord :: Record a -> (a, Record a)
unConsRecord r = let v:vs = fromPosRecord r
                 in (v, posRecord vs)

instance Show a => Show (Record a) where
  show (Record m) = let showElt (k,v) = case k of
                            RecPos _  -> show v
                            RecName s -> s ++ "=" ++ show v
                        shownElts = map showElt (M.toList m)
                    in "(" ++ concat (intersperse "," shownElts) ++ ")"
