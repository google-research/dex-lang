-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Env (Name (..), Tag, Env (..), NameSpace (..), envLookup, isin, envNames,
            envPairs, envDelete, envSubset, (!), (@>), VarP (..), varAnn, varName,
            envIntersect, varAsEnv, envDiff, envMapMaybe, fmapNames, envAsVars,
            rawName, nameSpace, rename, renames, nameItems, renameWithNS,
            renameChoice) where

import Control.Monad
import Data.List (minimumBy)
import Data.String
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import Data.Text.Prettyprint.Doc
import GHC.Generics

import Cat

infixr 7 :>

newtype Env a = Env (M.Map Name a)  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

-- TODO: consider parameterizing by namespace, for type-level namespace checks.
data Name = Name NameSpace Tag Int | NoName | DeBruijn Int
            deriving (Show, Ord, Eq, Generic)
data NameSpace = GenName | SourceName | SourceTypeName | JaxIdx
               | InferenceName | LocalTVName | NoNameSpace | ArrayName
                 deriving  (Show, Ord, Eq, Generic)

type Tag = T.Text
data VarP a = (:>) Name a  deriving (Show, Ord, Generic, Functor, Foldable, Traversable)

rawName :: NameSpace -> String -> Name
rawName s t = Name s (fromString t) 0

nameSpace :: Name -> NameSpace
nameSpace (Name s _ _) = s
nameSpace NoName       = NoNameSpace
nameSpace (DeBruijn _) = NoNameSpace

varAnn :: VarP a -> a
varAnn (_:>ann) = ann

varName :: VarP a -> Name
varName (v:>_) = v

nameTag :: Name -> Int
nameTag (Name _ _ tag) = tag
nameTag _ = 0

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

isin :: VarP ann -> Env a -> Bool
isin v env = case envLookup env v of Just _  -> True
                                     Nothing -> False

(!) :: Env a -> VarP ann -> a
env ! v = case envLookup env v of
  Just x -> x
  Nothing -> error $ "Lookup of " ++ show (varName v) ++ " failed"

genFresh :: Name-> Env a -> Name
genFresh NoName _ = NoName
genFresh (DeBruijn _) _ = error "Renaming de Bruijn indices"
genFresh (Name ns tag _) (Env m) = Name ns tag nextNum
  where
    nextNum = case M.lookupLT (Name ns tag bigInt) m of
                Nothing -> 0
                Just (NoName, _) -> 0
                Just (DeBruijn _, _) -> error "Renaming de Bruijn indices"
                Just (Name ns' tag' i, _)
                  | ns' /= ns || tag' /= tag -> 0
                  | i < bigInt  -> i + 1
                  | otherwise   -> error "Ran out of numbers!"
    bigInt = (10::Int) ^ (9::Int)  -- TODO: consider a real sentinel value

renameWithNS :: NameSpace -> VarP ann -> Env a -> VarP ann
renameWithNS _  (NoName       :> ann) _     = NoName :> ann
renameWithNS ns (Name _ tag _ :> ann) scope = rename (Name ns tag 0 :> ann) scope
renameWithNS _  (DeBruijn _ :> _) _ = error "Renaming de Bruijn indices"

rename :: VarP ann -> Env a -> VarP ann
rename v@(n:>ann) scope | v `isin` scope = genFresh n scope :> ann
                        | otherwise      = v

renameChoice :: [Name] -> Env a -> Name
renameChoice vs scope =
  minimumBy (\v1 v2 -> nameTag v1 `compare` nameTag v2) vs'
  where vs' = [varName $ rename (v:>()) scope | v <- vs]

renames :: Traversable f => f (VarP ann) -> Env () -> (f (VarP ann), Env ())
renames vs scope = runCat (traverse (freshCat ()) vs) scope

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
  pretty (DeBruijn i) = "!" <> pretty i
  pretty (Name _ tag n) = pretty (tagToStr tag) <> suffix
            where suffix = case n of 0 -> ""
                                     _ -> "_" <> pretty n

instance IsString Name where
  fromString s = Name GenName (fromString s) 0

tagToStr :: Tag -> String
tagToStr s = T.unpack s
