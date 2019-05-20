{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
-- those last three are all needed for monaderror

module Fresh (Name (..), Tag, fresh, freshLike, FreshT, runFreshT, runFresh,
              rawName, nameTag, newScope, rename, getRenamed, newSubst,
              FreshSubst, FreshScope, isFresh) where

import Control.Monad.Identity
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Except hiding (Except)
import qualified Data.Map.Strict as M
import Data.Text.Prettyprint.Doc

data Name = Name Tag Int  deriving (Show, Ord, Eq)
type Tag = String

newtype FreshScope = FreshScope (M.Map Tag Int)

newtype FreshT m a = FreshT (StateT FreshScope m a)
  deriving (Functor, Applicative, Monad, MonadTrans, MonadIO)

type Fresh a = FreshT Identity a

rawName :: Tag -> Name
rawName s = Name s 0

nameTag :: Name -> Tag
nameTag (Name tag _) = tag

newScope :: Name -> FreshScope
newScope (Name tag i) = FreshScope (M.singleton tag (i+1))

genFresh :: Tag -> FreshScope -> Name
genFresh tag (FreshScope m) = Name tag (M.findWithDefault 0 tag m)

class Monad m => MonadFresh m where
  fresh :: Tag -> m Name

instance Monad m => MonadFresh (FreshT m) where
  fresh tag = FreshT $ do name <- gets (genFresh tag)
                          modify (newScope name <>)
                          return name

freshLike :: MonadFresh m => Name -> m Name
freshLike = fresh . nameTag

runFreshT :: Monad m => FreshT m a -> FreshScope -> m a
runFreshT (FreshT s) scope = evalStateT s scope

runFresh :: Fresh a -> FreshScope -> a
runFresh m scope = runIdentity $ runFreshT m scope

-- TODO: this needs to be injective but it's currently not
-- (needs to figure out acceptable tag strings)
instance Pretty Name where
  pretty (Name tag n) = pretty tag <> suffix
            where suffix = case n of 0 -> ""
                                     _ -> "_" <> pretty n

instance MonadFresh m => MonadFresh (StateT s m) where
  fresh s = lift $ fresh s

instance MonadFresh m => MonadFresh (ReaderT r m) where
  fresh s = lift $ fresh s

instance MonadError e m => MonadError e (FreshT m) where
  throwError = lift . throwError
  catchError = undefined

instance Semigroup FreshScope where
  (FreshScope m) <> (FreshScope m') = FreshScope (M.unionWith max m m')

instance Monoid FreshScope where
  mempty = FreshScope mempty
  mappend = (<>)

-- === reader monad version of fresh var generation ===

data FreshSubst = FreshSubst FreshScope (M.Map Name Name)

rename :: Name -> FreshSubst -> (Name, FreshSubst)
rename v (FreshSubst scope _) =
  (v', FreshSubst (newScope v') (M.singleton v v'))
  where v' = genFresh (nameTag v) scope

getRenamed :: Name -> FreshSubst -> Name
getRenamed v (FreshSubst _ subst) = M.findWithDefault v v subst

newSubst :: [Name] -> FreshSubst
newSubst names = FreshSubst (foldMap newScope names) mempty

isFresh :: Name -> FreshSubst -> Bool
isFresh (Name tag n) (FreshSubst (FreshScope m) _) = n >= n'
  where n' = M.findWithDefault 0 tag m

instance Semigroup FreshSubst where
  (FreshSubst a b) <> (FreshSubst a' b') = FreshSubst (a<>a') (b<>b')

instance Monoid FreshSubst where
  mempty = FreshSubst mempty mempty
  mappend = (<>)
