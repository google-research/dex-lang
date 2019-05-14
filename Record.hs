module Record (Record (..), RecTree (..), recUnionWith,
               zipWithRecord, recZipWith, recTreeZipEq,
 recLookup, recNameVals,
               recTreeJoin, unLeaf, RecTreeZip (..), recTreeNamed
              ) where


import Fresh
import Util
import Data.Traversable
import qualified Data.Map.Strict as M

data Record a = Rec (M.Map String a)
              | Tup [a] deriving (Eq, Ord, Show)

data RecTree a = RecTree (Record (RecTree a))
               | RecLeaf a  deriving (Eq, Show, Ord)

instance Functor Record where
  fmap = fmapDefault

instance Foldable Record where
  foldMap = foldMapDefault

instance Traversable Record where
  traverse f (Rec m) = fmap Rec $ traverse f m
  traverse f (Tup m) = fmap Tup $ traverse f m

instance Functor RecTree where
  fmap = fmapDefault

instance Foldable RecTree where
  foldMap = foldMapDefault

instance Traversable RecTree where
  traverse f t = case t of
    RecTree r -> fmap RecTree $ traverse (traverse f) r
    RecLeaf x -> fmap RecLeaf $ f x

recUnionWith :: (a -> a -> a) -> Record a -> Record a -> Record a
recUnionWith = undefined -- f (Record m1) (Record m2) = Record $ M.unionWith f m1 m2

zipWithRecord :: (a -> b -> c) -> Record a -> Record b -> Maybe (Record c)
zipWithRecord f (Rec m) (Rec m') | M.keys m == M.keys m' =  Just $ Rec $ M.intersectionWith f m m'
zipWithRecord f (Tup xs) (Tup xs') | length xs == length xs' = Just $ Tup $ zipWith f xs xs'
zipWithRecord _ _ _ = Nothing

recZipWith f r r' = unJust (zipWithRecord f r r')

recTreeJoin :: RecTree (RecTree a) -> RecTree a
recTreeJoin (RecLeaf t) = t
recTreeJoin (RecTree r) = RecTree $ fmap recTreeJoin r

recTreeZipEq :: RecTree a -> RecTree b -> RecTree (a, b)
recTreeZipEq t t' = fmap (appSnd unLeaf) (recTreeZip t t')
  where appSnd f (x, y) = (x, f y)

unLeaf :: RecTree a -> a
unLeaf (RecLeaf x) = x
unLeaf (RecTree _) = error "whoops! [unLeaf]"

recNameVals :: Record a -> Record (Name, a)
recNameVals (Tup xs) = Tup [(rawName (show i), x) | (i,x) <- zip [0..] xs]
recNameVals (Rec m) = Rec $ M.mapWithKey (\field x -> (rawName field, x)) m

recTreeNamed :: RecTree a -> RecTree (Name, a)
recTreeNamed (RecLeaf x) = RecLeaf (nameRoot, x)
recTreeNamed (RecTree r) = RecTree $ fmap (\(name, val) -> addName name (recTreeNamed val))
                                       (recNameVals r)
  where addName :: Name -> RecTree (Name, a) -> RecTree (Name, a)
        addName name tree = fmap (\(n,x) -> (catNames name n, x)) tree

recLookup :: Name -> Record a -> a
recLookup = undefined

class RecTreeZip tree where
  recTreeZip :: RecTree a -> tree -> RecTree (a, tree)

instance RecTreeZip (RecTree a) where
  recTreeZip (RecTree r) (RecTree r') = RecTree $ recZipWith recTreeZip r r'
  recTreeZip (RecLeaf x) x' = RecLeaf (x, x')
  recTreeZip (RecTree _) (RecLeaf _) = error "whoops! [recTreeZip]"
    -- Symmetric alternative: recTreeZip x (RecLeaf x') = RecLeaf (x, x')
