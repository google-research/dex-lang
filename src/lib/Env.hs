-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Env (Name, Tag, Env (..), NameSpace (..), envLookup, isin, envNames,
            envPairs, envDelete, envSubset, (!), (@>), VarP (..), varAnn, varName,
            envIntersect, varAsEnv, envDiff, envMapMaybe, fmapNames,
            rawName, nameSpace, rename, renames) where

import Data.String
import Data.Traversable
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import Control.Applicative (liftA)
import Data.Text.Prettyprint.Doc
import GHC.Generics

import Cat

infixr 7 :>

newtype Env a = Env (M.Map Name a)  deriving (Show, Eq, Ord)

-- TODO: consider parameterizing by namespace, for type-level namespace checks.
data Name = Name NameSpace Tag Int  deriving (Show, Ord, Eq, Generic)
data NameSpace = GenName | SourceName | SourceTypeName
               | InferenceName | LocalTVName
                 deriving  (Show, Ord, Eq)

type Tag = T.Text
data VarP a = (:>) Name a  deriving (Show, Ord, Generic)

rawName :: NameSpace -> String -> Name
rawName s t = Name s (fromString t) 0

nameSpace :: Name -> NameSpace
nameSpace (Name s _ _) = s

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

fmapNames :: (Name -> a -> b) -> Env a -> Env b
fmapNames f (Env m) = Env $ M.mapWithKey f m

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

genFresh :: Name-> Env a -> Name
genFresh (Name ns tag _) (Env m) = Name ns tag nextNum
  where
    nextNum = case M.lookupLT (Name ns tag bigInt) m of
                Nothing -> 0
                Just (Name ns' tag' i, _)
                  | ns' /= ns || tag' /= tag -> 0
                  | i < bigInt  -> i + 1
                  | otherwise   -> error "Ran out of numbers!"
    bigInt = (10::Int) ^ (9::Int)  -- TODO: consider a real sentinel value

rename :: VarP ann -> Env a -> VarP ann
rename v@(n:>ann) scope | v `isin` scope = genFresh n scope :> ann
                        | otherwise      = v

renames :: Traversable f => f (VarP ann) -> Env () -> (f (VarP ann), Env ())
renames vs scope = runCat (traverse freshCat vs) scope

freshCat :: VarP ann -> Cat (Env ()) (VarP ann)
freshCat v = do v' <- looks $ rename v
                extend (v' @> ())
                return v'

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
  pretty (Env m) = tupled [pretty v <+> "@>" <+> pretty x
                          | (v, x) <- M.toAscList m]

instance Eq (VarP a) where
  (v:>_) == (v':>_) = v == v'

instance Functor VarP where
  fmap = fmapDefault

instance Foldable VarP where
  foldMap = foldMapDefault

instance Traversable VarP where
  traverse f (v :> x) = fmap (v:>) (f x)

-- TODO: this needs to be injective but it's currently not
-- (needs to figure out acceptable tag strings)
instance Pretty Name where
  pretty (Name _ tag n) = pretty (tagToStr tag) <> suffix
            where suffix = case n of 0 -> ""
                                     _ -> "_" <> pretty n
instance IsString Name where
  fromString s = Name GenName (fromString s) 0

tagToStr :: Tag -> String
tagToStr s = T.unpack s
