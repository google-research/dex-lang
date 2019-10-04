-- Copyright 2019 Google LLC
--
-- Licensed under the Apache License, Version 2.0 (the "License");
-- you may not use this file except in compliance with the License.
-- You may obtain a copy of the License at
--
--     https://www.apache.org/licenses/LICENSE-2.0
--
-- Unless required by applicable law or agreed to in writing, software
-- distributed under the License is distributed on an "AS IS" BASIS,
-- WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
-- See the License for the specific language governing permissions and
-- limitations under the License.

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Record (Record (..), RecTree (..),
               zipWithRecord, recZipWith, recTreeZipEq,
               recGet, otherFields, recNameVals, RecField,
               recTreeJoin, unLeaf, RecTreeZip (..), recTreeNamed,
               recUpdate, fstField, sndField, recAsList, tupField, fromLeaf
              ) where


import Util
import Data.Traversable
import qualified Data.Map.Strict as M
import Data.Maybe (fromJust)
import Data.Text.Prettyprint.Doc
import GHC.Generics

data Record a = Rec (M.Map String a)
              | Tup [a] deriving (Eq, Ord, Show, Generic)

data RecTree a = RecTree (Record (RecTree a))
               | RecLeaf a  deriving (Eq, Show, Ord, Generic)

data RecField = RecField (Record ()) RecFieldName  deriving (Eq, Ord, Show)
data RecFieldName = RecName String | RecPos Int  deriving (Eq, Ord, Show)

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

zipWithRecord :: (a -> b -> c) -> Record a -> Record b -> Maybe (Record c)
zipWithRecord f (Rec m) (Rec m') | M.keys m == M.keys m' =  Just $ Rec $ M.intersectionWith f m m'
zipWithRecord f (Tup xs) (Tup xs') | length xs == length xs' = Just $ Tup $ zipWith f xs xs'
zipWithRecord _ _ _ = Nothing

recZipWith :: (a -> b -> c) -> Record a -> Record b -> Record c
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

recNameVals :: Record a -> Record (RecField, a)
recNameVals r = case r of
  Tup xs -> Tup [(RecField example (RecPos i), x) | (i,x) <- zip [0..] xs]
  Rec m  -> Rec $ M.mapWithKey (\field x -> (RecField example (RecName field), x)) m
  where example = fmap (const ()) r

recTreeNamed :: RecTree a -> RecTree ([RecField], a)
recTreeNamed (RecLeaf x) = RecLeaf ([], x)
recTreeNamed (RecTree r) = RecTree $
  fmap (\(name, val) -> addRecField name (recTreeNamed val)) (recNameVals r)
  where addRecField name tree = fmap (\(n,x) -> (name:n, x)) tree

-- TODO: make a `Maybe a` version
recGet :: Record a -> RecField -> a
recGet (Rec m)  (RecField _ (RecName s)) = fromJust $ M.lookup s m
recGet (Tup xs) (RecField r (RecPos i )) =
  if i < length xs && i >= 0
   then xs !! i
   else error $ "Record error " ++ show r ++ " " ++ show i
recGet _ _ = error "Record error"

fromLeaf :: RecTree a -> a
fromLeaf (RecLeaf x) = x
fromLeaf _ = error "Not a leaf"

recUpdate :: RecField -> a -> Record a -> Record a
recUpdate (RecField _ (RecName k)) v (Rec m)  = Rec $ M.insert k v m
recUpdate (RecField _ (RecPos i))  v (Tup xs) = Tup $ prefix ++ (v : suffix)
  where prefix = take i xs
        (_:suffix) = drop i xs
recUpdate field _ _ = error $ "Can't update record at " ++ show field

otherFields :: RecField -> Record ()
otherFields (RecField r _) = r

tupField :: Int -> Int -> RecField
tupField n i = RecField (Tup (take n (repeat ()))) (RecPos i)

fstField :: RecField
fstField = RecField (Tup [(), ()]) (RecPos 0)

sndField :: RecField
sndField = RecField (Tup [(), ()]) (RecPos 1)

recAsList :: Record a -> ([a], [b] -> Record b)
recAsList (Tup xs) = (xs, Tup)
recAsList _ = error "Not implemented" -- TODO

class RecTreeZip tree where
  recTreeZip :: RecTree a -> tree -> RecTree (a, tree)

instance RecTreeZip (RecTree a) where
  recTreeZip (RecTree r) (RecTree r') = RecTree $ recZipWith recTreeZip r r'
  recTreeZip (RecLeaf x) x' = RecLeaf (x, x')
  recTreeZip (RecTree _) (RecLeaf _) = error "whoops! [recTreeZip]"
    -- Symmetric alternative: recTreeZip x (RecLeaf x') = RecLeaf (x, x')

instance Pretty a => Pretty (Record a) where
  pretty r = align $ tupled $ case r of
               Rec m  -> [pretty k <> "=" <> pretty v | (k,v) <- M.toList m]
               Tup xs -> map pretty xs -- TODO: add trailing comma to singleton tuple

instance Pretty a => Pretty (RecTree a) where
  pretty (RecTree r) = pretty r
  pretty (RecLeaf x) = pretty x

instance Pretty (RecField) where
  pretty (RecField _ fieldname) = case fieldname of
    RecName name -> pretty name
    RecPos n     -> pretty n
