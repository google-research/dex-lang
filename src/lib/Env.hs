-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Env (Name (..), Tag, Env (..), NameSpace (..), envLookup, isin, envNames,
            envPairs, envDelete, envSubset, (!), (@>), VarP (..), varAnn, varName,
            envIntersect, varAsEnv, envDiff, envMapMaybe, fmapNames, envAsVars, zipEnv,
            rawName, nameSpace, rename, renames, nameItems,
            renameChoice, tagToStr, isGlobal, asGlobal) where

import Control.Monad
import Data.List (minimumBy)
import Data.String
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import Data.Text.Prettyprint.Doc
import GHC.Generics
import GHC.Stack

import Cat

infixr 7 :>

newtype Env a = Env (M.Map Name a)  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

-- TODO: consider parameterizing by namespace, for type-level namespace checks.
-- `NoName` is used in binders (e.g. `_ = <expr>`) but never in occurrences.
-- TODO: Consider putting it under a separate `Binder` type instead.
data Name = Name NameSpace Tag Int | GlobalName Tag | NoName
            deriving (Show, Ord, Eq, Generic)
data NameSpace = GenName | SourceName | JaxIdx | Skolem
               | InferenceName | NoNameSpace | ArrayName | SumName
                 deriving  (Show, Ord, Eq, Generic)

type Tag = T.Text
data VarP a = (:>) Name a  deriving (Show, Ord, Generic, Functor, Foldable, Traversable)

rawName :: NameSpace -> String -> Name
rawName s t = Name s (fromString t) 0

asGlobal :: Name -> Name
asGlobal (Name SourceName tag 0) = GlobalName tag
asGlobal NoName = NoName
asGlobal v = error $ "Can't treat as global name: " ++ show v

nameSpace :: Name -> NameSpace
nameSpace (Name s _ _) = s
nameSpace NoName       = NoNameSpace
nameSpace (GlobalName _) = NoNameSpace

varAnn :: VarP a -> a
varAnn (_:>ann) = ann

varName :: VarP a -> Name
varName (v:>_) = v

nameCounter :: Name -> Int
nameCounter (Name _ _ c) = c
nameCounter _ = 0

varAsEnv :: VarP a -> Env a
varAsEnv v = v @> varAnn v

envAsVars :: Env a -> [VarP a]
envAsVars env = map (uncurry (:>)) $ envPairs env

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

zipEnv :: [VarP a] -> [b] -> Env b
zipEnv ns vs = Env $ M.fromList $ zip (map varName ns) vs

isin :: VarP ann -> Env a -> Bool
isin v env = case envLookup env v of Just _  -> True
                                     Nothing -> False

(!) :: HasCallStack => Env a -> VarP ann -> a
env ! v = case envLookup env v of
  Just x -> x
  Nothing -> error $ "Lookup of " ++ show (varName v) ++ " failed"

isGlobal :: VarP ann -> Bool
isGlobal (GlobalName _ :> _) = True
isGlobal _ = False

genFresh :: Name-> Env a -> Name
genFresh NoName _ = NoName
genFresh (Name ns tag _) (Env m) = Name ns tag nextNum
  where
    nextNum = case M.lookupLT (Name ns tag bigInt) m of
                Just (Name ns' tag' i, _)
                  | ns' /= ns || tag' /= tag -> 0
                  | i < bigInt  -> i + 1
                  | otherwise   -> error "Ran out of numbers!"
                _ -> 0
    bigInt = (10::Int) ^ (9::Int)  -- TODO: consider a real sentinel value
genFresh v@(GlobalName _) env
  | (v:>()) `isin` env = error $ "Can't rename global: " ++ show v
  | otherwise          = v

rename :: VarP ann -> Env a -> VarP ann
rename v@(n:>ann) scope | v `isin` scope = genFresh n scope :> ann
                        | otherwise      = v

renameChoice :: [Name] -> Env a -> Name
renameChoice vs scope =
  minimumBy (\v1 v2 -> nameCounter v1 `compare` nameCounter v2) vs'
  where vs' = [varName $ rename (v:>()) scope | v <- vs]

renames :: Traversable f => f (VarP ann) -> a -> Env a -> (f (VarP ann), Env a)
renames vs x scope = runCat (traverse (freshCat x) vs) scope

nameItems :: Traversable f => Name -> Env a -> f a -> (f Name, Env a)
nameItems v env xs = flip runCat env $ forM xs $ \x ->
                       liftM varName $ freshCat x (v:>())

freshCat :: a -> VarP ann -> Cat (Env a) (VarP ann)
freshCat x v = do
  v' <- looks $ rename v
  extend (v' @> x)
  return v'

infixr 7 @>

(@>) :: VarP b -> a -> Env a
(v:>_) @> x = case v of
  NoName -> mempty
  _      -> Env $ M.singleton v x

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

-- TODO: this needs to be injective but it's currently not
-- (needs to figure out acceptable tag strings)
instance Pretty Name where
  pretty NoName = "_"
  pretty (Name _ tag n) = pretty (tagToStr tag) <> suffix
            where suffix = case n of 0 -> ""
                                     _ -> pretty n
  pretty (GlobalName tag) = pretty (tagToStr tag)

instance IsString Name where
  fromString s = Name GenName (fromString s) 0

tagToStr :: Tag -> String
tagToStr s = T.unpack s
