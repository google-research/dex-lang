{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
-- those last three are all needed for monaderror

module Fresh (fresh, FreshT, runFreshT, Var (..), VarName, rawVar) where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except hiding (Except)
import Data.Map.Strict as M

type VarName = String
data Var = VarRoot
         | Qual Var VarName Int
         | BoundVar Int  deriving (Show, Eq, Ord)

type FreshState = (Var, M.Map VarName Int)
newtype FreshT m a = FreshT (StateT FreshState m a)
    deriving (Functor, Applicative, Monad, MonadTrans, MonadIO)

class Monad m => MonadFresh m where
    fresh :: VarName -> m Var

instance Monad m => MonadFresh (FreshT m) where
    fresh s = FreshT $ do stem <- gets $ fst
                          c <- gets $ getCount s . snd
                          modify $ updateSnd (M.insert s (c+1))
                          return $ Qual stem s c

instance MonadFresh m => MonadFresh (StateT s m) where
  fresh s = lift $ fresh s

instance MonadFresh m => MonadFresh (ReaderT r m) where
  fresh s = lift $ fresh s

instance MonadError e m => MonadError e (FreshT m) where
    throwError = lift . throwError
    catchError = undefined

runFreshT :: Monad m => FreshT m a -> Var -> m a
runFreshT (FreshT s) stem = evalStateT s (stem, mempty)


getCount :: Ord k => k -> M.Map k Int -> Int
getCount k m = case M.lookup k m of Just n -> n
                                    Nothing -> 0

updateSnd :: (a -> b) -> (c, a) -> (c, b)
updateSnd f (x, y) = (x, f y)

rawVar :: VarName -> Var
rawVar name = Qual VarRoot name 0
