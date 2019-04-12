{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
-- those last three are all needed for monaderror

module Fresh (fresh, FreshT, runFreshT) where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except hiding (Except)
import Data.Map.Strict as M

import Syntax
import Env

type FreshState = Int

newtype FreshT m a = FreshT (StateT FreshState m a)
    deriving (Functor, Applicative, Monad, MonadTrans, MonadIO)

class Monad m => MonadFresh m where
    fresh :: m Var

instance Monad m => MonadFresh (FreshT m) where
    fresh = FreshT $ do i <- get
                        put (i + 1)
                        return (TempVar i)

                          -- n <- case M.lookup s counts of
                          --           Nothing -> do
                          --             put $ (stem, M.insert s 1 counts)
                          --             return 0

instance MonadFresh m => MonadFresh (StateT s m) where
  fresh = lift fresh

instance MonadFresh m => MonadFresh (ReaderT r m) where
  fresh = lift fresh


instance MonadError e m => MonadError e (FreshT m) where
    throwError = lift . throwError
    catchError = undefined


-- data Var = VarRoot | Qual Var String Int

runFreshT :: Monad m => FreshT m a -> m a
runFreshT (FreshT s) = evalStateT s 0
