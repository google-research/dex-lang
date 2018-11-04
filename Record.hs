module Record (Record, posRecord, nameRecord, emptyRecord,
               sequenceRecord, mapRecord, recordElems) where

import Util
import Control.Monad
import Data.List (nub, intersperse)
import qualified Data.Map.Strict as M

data Record a = Record (M.Map RecName a)  deriving (Eq, Ord)

data RecName = RecPos Int | RecName String  deriving (Show, Eq, Ord)

emptyRecord :: Record a
emptyRecord = Record M.empty

posRecord :: [a] -> Record a
posRecord = Record . M.fromList . zip (map RecPos [0..])

nameRecord :: [(String, a)] -> Record a
nameRecord = Record . M.fromList . mapFst RecName

mapRecord :: (a -> b) -> Record a -> Record b
mapRecord f (Record m) = Record $ M.map f m

recordElems :: Record a -> [a]
recordElems (Record m) = M.elems m

sequenceRecord :: Monad m => Record (m v) -> m (Record v)
sequenceRecord (Record m) = do
    let (ks, vs) = unzip (M.toList m)
    vs' <- sequence vs
    return . Record . M.fromList $ zip ks vs'

instance Show a => Show (Record a) where
  show (Record m) = let showElt (k,v) = case k of
                            RecPos _  -> show v
                            RecName s -> s ++ "=" ++ show v
                        shownElts = map showElt (M.toList m)
                    in "{" ++ concat (intersperse "," shownElts) ++ "}"
