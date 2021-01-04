-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE DeriveGeneric #-}

module Env (Name (..), Tag, Env (..), NameSpace (..), envLookup, isin, envNames,
            envPairs, envDelete, envSubset, (!), (@>), VarP (..),
            varAnn, varName, BinderP (..), binderAnn, binderNameHint,
            envIntersect, varAsEnv, envDiff, envMapMaybe, fmapNames, traverseNames,
            envAsVars, rawName, nameSpace, nameTag, envMaxName, genFresh,
            tagToStr, isGlobal, isGlobalBinder, asGlobal, envFilter, binderAsEnv,
            fromBind, newEnv, HasName, getName, InlineHint (..), pattern Bind) where

import Data.Maybe
import Data.Store
import Data.String
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import Data.Foldable (fold, toList)
import Data.Text.Prettyprint.Doc
import GHC.Generics
import GHC.Stack

infixr 7 :>

newtype Env a = Env (M.Map Name a)
                deriving (Show, Eq, Ord, Generic, Functor, Foldable, Traversable)

-- TODO: consider parameterizing by namespace, for type-level namespace checks.
data Name = Name NameSpace Tag Int | GlobalName Tag | GlobalArrayName Int
            deriving (Show, Ord, Eq, Generic)
data NameSpace =
       GenName
     | SourceName         -- names from source program
     | Skolem
     | InferenceName
     | SumName
     | FFIName
     | TypeClassGenName   -- names generated for type class dictionaries
     | AbstractedPtrName  -- used in `abstractPtrLiterals` in Imp lowering
     | TopFunctionName    -- top-level Imp functions
     | AllocPtrName       -- used for constructing dests in Imp lowering
     | CArgName           -- used for constructing arguments in export
     | LoopBinderName     -- used to easily generate non-shadowing names in parallelization
       deriving  (Show, Ord, Eq, Generic)

type Tag = T.Text
data VarP a = (:>) Name a  deriving (Show, Ord, Generic, Functor, Foldable, Traversable)
data BinderP a = Ignore a | BindWithHint InlineHint (VarP a)
                 deriving (Show, Generic, Functor, Foldable, Traversable)

data InlineHint = NoHint | CanInline | NoInline
                  deriving (Show, Generic)

pattern Bind :: VarP a -> BinderP a
pattern Bind v <- BindWithHint _ v
  where Bind v = BindWithHint NoHint v

{-# COMPLETE Ignore, Bind #-}

rawName :: NameSpace -> Tag -> Name
rawName s t = Name s t 0

asGlobal :: Name -> Name
asGlobal (GlobalName tag) = GlobalName tag
asGlobal (Name SourceName tag 0) = GlobalName tag
asGlobal v = error $ "Can't treat as global name: " ++ show v

nameSpace :: Name -> Maybe NameSpace
nameSpace (Name s _ _) = Just s
nameSpace _ = Nothing

newEnv :: (Foldable f, Foldable h, HasName a) => f a -> h b -> Env b
newEnv bs xs = fold $ zipWith (@>) (toList bs) (toList xs)

varAnn :: VarP a -> a
varAnn (_:>ann) = ann

binderAnn :: BinderP a -> a
binderAnn (Bind (_:>ann)) = ann
binderAnn (Ignore ann) = ann

varName :: VarP a -> Name
varName (v:>_) = v

binderNameHint :: BinderP a -> Name
binderNameHint (Ignore _) = "ignored"
binderNameHint (Bind (v:>_)) = v

nameTag :: Name -> Tag
nameTag name = case name of
  Name _ t _        -> t
  GlobalName t      -> t
  GlobalArrayName _ -> error "GlobalArrayName has no tag"

varAsEnv :: VarP a -> Env a
varAsEnv v = v @> varAnn v

fromBind :: Name -> BinderP a -> VarP a
fromBind v (Ignore ty) = v :> ty
fromBind _ (Bind v) = v

binderAsEnv :: BinderP a -> Env a
binderAsEnv b = b @> binderAnn b

envAsVars :: Env a -> [VarP a]
envAsVars env = map (uncurry (:>)) $ envPairs env

envLookup :: HasName a => Env b -> a -> Maybe b
envLookup (Env m) x = case getName x of
  Nothing -> Nothing
  Just v  -> M.lookup v m

envMapMaybe :: (a -> Maybe b) -> Env a -> Env b
envMapMaybe f (Env m) = Env $ M.mapMaybe f m

envNames :: Env a -> [Name]
envNames (Env m) = M.keys m

envPairs :: Env a -> [(Name, a)]
envPairs (Env m) = M.toAscList m

fmapNames :: (Name -> a -> b) -> Env a -> Env b
fmapNames f (Env m) = Env $ M.mapWithKey f m

traverseNames :: Applicative t => (Name -> a -> t b) -> Env a -> t (Env b)
traverseNames f (Env m) = Env <$> M.traverseWithKey f m

envDelete :: HasName a => a -> Env b -> Env b
envDelete x (Env m) = Env $ case getName x of
  Nothing -> m
  Just n  -> M.delete n m

envSubset :: [Name] -> Env a -> Env a
envSubset vs (Env m) = Env $ M.intersection m (M.fromList [(v,()) | v <- vs])

envIntersect :: Env a -> Env b -> Env b
envIntersect (Env m) (Env m') = Env $ M.intersection m' m

envDiff :: Env a -> Env b -> Env a
envDiff (Env m) (Env m') = Env $ M.difference m m'

envFilter :: Env a -> (a -> Bool) -> Env a
envFilter (Env m) f = Env $ M.filter f m

isin :: HasName a => a -> Env b -> Bool
isin x env = case getName x of
  Nothing -> False
  Just v  -> case envLookup env v of
    Just _  -> True
    Nothing -> False

envMaxName :: Env a -> Maybe Name
envMaxName (Env m) = if M.null m then Nothing else Just $ fst $ M.findMax m

(!) :: (HasCallStack, HasName b) => Env a -> b -> a
env ! v = case envLookup env v of
  Just x -> x
  Nothing -> error $ "Lookup of " ++ show (fromMaybe "<no name>" $ getName v) ++ " failed"

isGlobal :: VarP ann -> Bool
isGlobal (GlobalName _ :> _) = True
isGlobal (GlobalArrayName _ :> _) = True
isGlobal (Name TypeClassGenName _ _ :> _) = True
isGlobal _ = False

isGlobalBinder :: BinderP ann -> Bool
isGlobalBinder b = isGlobal $ fromBind "" b

genFresh :: Name-> Env a -> Name
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
  | v `isin` env = error $ "Can't rename global: " ++ show v
  | otherwise    = v
genFresh v@(GlobalArrayName _) env
  | v `isin` env = error $ "Can't rename global array: " ++ show v
  | otherwise    = v

infixr 7 @>

(@>) :: HasName a => a -> b -> Env b
x @> y = case getName x of
  Nothing -> mempty
  Just v  -> Env $ M.singleton v y

class HasName a where
  getName :: a -> Maybe Name

instance HasName Name where
  getName x = Just x

instance HasName (VarP ann) where
  getName (v:>_) = Just v

instance HasName (BinderP ann) where
  getName (Ignore _)    = Nothing
  getName (Bind (v:>_)) = Just v

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
  pretty (Name _ tag n) = pretty (tagToStr tag) <> suffix
            where suffix = case n of 0 -> ""
                                     _ -> pretty n
  pretty (GlobalName tag) = pretty (tagToStr tag)
  pretty (GlobalArrayName i) = "<array " <> pretty i <> ">"

instance Pretty a => Pretty (BinderP a) where
  pretty (Ignore ann) = "_:" <> pretty ann
  pretty (Bind (v:>ann)) = pretty v <> ":" <> pretty ann

instance IsString Name where
  fromString s = Name GenName (fromString s) 0

tagToStr :: Tag -> String
tagToStr s = T.unpack s

instance Store Name
instance Store NameSpace
instance Store InlineHint
instance Store a => Store (VarP a)
instance Store a => Store (Env a)
instance Store a => Store (BinderP a)
