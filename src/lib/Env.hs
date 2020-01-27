-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Env (Name (..), Tag, Env (..), envLookup, isin, envNames, envPairs,
            envDelete, envSubset, (!), (@>), VarP (..), varAnn, varName,
            envIntersect, tagToStr, varAsEnv, envDiff, envMapMaybe) where

import Data.String
import Data.Traversable
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import Control.Applicative (liftA)
import Data.Text.Prettyprint.Doc
import GHC.Generics

infixr 7 :>

newtype Env a = Env (M.Map Name a)  deriving (Show, Eq, Ord)

data Name = Name Tag Int  deriving (Show, Ord, Eq, Generic)
type Tag = T.Text
data VarP a = (:>) Name a  deriving (Show, Eq, Ord, Generic)

varAnn :: VarP a -> a
varAnn (_:>ann) = ann

varName :: VarP a -> Name
varName (v:>_) = v

varAsEnv :: VarP a -> Env a
varAsEnv v = v @> varAnn v

envLookup :: Env a -> VarP ann -> Maybe a
envLookup (Env m) v = M.lookup (varName v) m

envMapMaybe :: (a -> Maybe b) -> Env a -> Env b
envMapMaybe f (Env m) = Env $ M.mapMaybe f m

envNames :: Env a -> [Name]
envNames (Env m) = M.keys m

envPairs :: Env a -> [(Name, a)]
envPairs (Env m) = M.toAscList m

envDelete :: Name -> Env a -> Env a
envDelete v (Env m) = Env (M.delete v m)

envSubset :: [Name] -> Env a -> Env a
envSubset vs (Env m) = Env $ M.intersection m (M.fromList [(v,()) | v <- vs])

envIntersect :: Env a -> Env b -> Env b
envIntersect (Env m) (Env m') = Env $ M.intersection m' m

envDiff :: Env a -> Env b -> Env a
envDiff (Env m) (Env m') = Env $ M.difference m m'

isin :: VarP ann -> Env a -> Bool
isin v env = case envLookup env v of Just _  -> True
                                     Nothing -> False

(!) :: Env a -> VarP ann -> a
env ! v = case envLookup env v of
  Just x -> x
  Nothing -> error $ "Lookup of " ++ show (varName v) ++ " failed"

infixr 7 @>

(@>) :: VarP b -> a -> Env a
(v:>_) @> x = Env $ M.singleton v x

instance Functor Env where
  fmap = fmapDefault

instance Foldable Env where
  foldMap = foldMapDefault

instance Traversable Env where
  traverse f (Env m) = liftA Env (traverse f m)


-- Note: Env is right-biased, so that we extend envs on the right
instance Semigroup (Env a) where
  Env m <> Env m' = Env (m' <> m)

instance Monoid (Env a) where
  mempty = Env mempty
  mappend = (<>)

instance Pretty a => Pretty (Env a) where
  pretty (Env m) = pretty (M.toAscList m)

instance Functor VarP where
  fmap = fmapDefault

instance Foldable VarP where
  foldMap = foldMapDefault

instance Traversable VarP where
  traverse f (v :> x) = fmap (v:>) (f x)

-- TODO: this needs to be injective but it's currently not
-- (needs to figure out acceptable tag strings)
instance Pretty Name where
  pretty (Name tag n) = pretty (tagToStr tag) <> suffix
            where suffix = case n of 0 -> ""
                                     _ -> "_" <> pretty n
instance IsString Name where
  fromString s = Name (fromString s) 0

tagToStr :: Tag -> String
tagToStr s = T.unpack s
