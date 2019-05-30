{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
-- those last three are all needed for monaderror

module Fresh (Name (..), Tag, fresh, freshLike, FreshT, runFreshT, rawName,
              nameTag, newScope, rename, FreshScope, isFresh, runFreshRT,
              FreshRT, MonadFreshR, freshName, askFresh, localFresh) where

import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Except hiding (Except)
import qualified Data.Map.Strict as M
import Data.Text.Prettyprint.Doc

data Name = Name Tag Int  deriving (Show, Ord, Eq)
type Tag = String

newtype FreshScope = FreshScope (M.Map Tag Int)  deriving (Show)

rawName :: Tag -> Name
rawName s = Name s 0

nameTag :: Name -> Tag
nameTag (Name tag _) = tag

newScope :: Name -> FreshScope
newScope (Name tag i) = FreshScope (M.singleton tag (i+1))

genFresh :: Tag -> FreshScope -> Name
genFresh tag (FreshScope m) = Name tag (M.findWithDefault 0 tag m)

rename :: Name -> FreshScope -> Name
rename v scope | isFresh v scope = v
               | otherwise = genFresh (nameTag v) scope

isFresh :: Name -> FreshScope -> Bool
isFresh (Name tag n) (FreshScope m) = n >= n'
  where n' = M.findWithDefault 0 tag m

-- TODO: this needs to be injective but it's currently not
-- (needs to figure out acceptable tag strings)
instance Pretty Name where
  pretty (Name tag n) = pretty tag <> suffix
            where suffix = case n of 0 -> ""
                                     _ -> "_" <> pretty n

instance Semigroup FreshScope where
  (FreshScope m) <> (FreshScope m') = FreshScope (M.unionWith max m m')

instance Monoid FreshScope where
  mempty = FreshScope mempty
  mappend = (<>)

-- === state monad version of fresh var generation ===

newtype FreshT m a = FreshT (StateT FreshScope m a)
  deriving (Functor, Applicative, Monad, MonadTrans, MonadIO)

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

instance MonadFresh m => MonadFresh (StateT s m) where
  fresh s = lift $ fresh s

instance MonadFresh m => MonadFresh (ReaderT r m) where
  fresh s = lift $ fresh s

instance (Monoid w, MonadFresh m) => MonadFresh (WriterT w m) where
  fresh s = lift $ fresh s

instance MonadError e m => MonadError e (FreshT m) where
  throwError = lift . throwError
  catchError = undefined

-- === reader monad version of fresh var generation ===

newtype FreshRT m a = FreshRT (ReaderT FreshScope m a)
  deriving (Functor, Applicative, Monad, MonadTrans, MonadIO)

runFreshRT :: FreshRT m a -> FreshScope -> m a
runFreshRT (FreshRT m) scope = runReaderT m scope

freshName :: MonadFreshR m => Name -> (Name -> m a) -> m a
freshName v cont = do
  scope <- askFresh
  let v' = rename v scope
  localFresh (newScope v' <>) (cont v')

class Monad m => MonadFreshR m where
  askFresh :: m FreshScope
  localFresh :: (FreshScope -> FreshScope) -> m a -> m a

instance Monad m => MonadFreshR (FreshRT m) where
  askFresh = FreshRT ask
  localFresh update (FreshRT m) = FreshRT (local update m)

instance MonadError e m => MonadError e (FreshRT m) where
  throwError = lift . throwError
  catchError = undefined

instance MonadFreshR m => MonadFreshR (StateT s m) where
  askFresh = lift askFresh
  localFresh update m = do s <- get
                           (x, s') <- lift $ localFresh update (runStateT m s)
                           put s'
                           return x

instance MonadFreshR m => MonadFreshR (ReaderT r m) where
  askFresh = lift askFresh
  localFresh update m = do r <- ask
                           lift $ localFresh update (runReaderT m r)
