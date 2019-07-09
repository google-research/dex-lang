{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
-- those last three are all needed for monaderror

module Fresh (fresh, freshLike, FreshT, runFreshT, rawName,
              nameTag, rename, renames, FreshScope, runFreshRT, genFresh,
              FreshRT, MonadFreshR, freshName, askFresh, localFresh,
              freshenBinder) where

import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Except hiding (Except)
import qualified Data.Map.Strict as M

import Env

type FreshScope = Env ()

rawName :: Tag -> Name
rawName s = Name s 0

nameTag :: Name -> Tag
nameTag (Name tag _) = tag

genFresh :: Tag -> Env a -> Name
genFresh tag (Env m) = Name tag nextNum
  where
    nextNum = case M.lookupLT (Name tag bigInt) m of
                Nothing -> 0
                Just (Name tag' i, _)
                  | tag' /= tag -> 0
                  | i < bigInt  -> i + 1
                  | otherwise   -> error "Ran out of numbers!"
    bigInt = 10^9 :: Int  -- TODO: consider a real sentinel value

rename :: Name -> Env a -> Name
rename v scope | v `isin` scope = genFresh (nameTag v) scope
               | otherwise = v

renames :: [Name] -> Env a -> [Name]
renames [] _ = []
renames (v:vs) scope = v':vs'
  where v' = rename v scope
        vs' = renames vs (scope <> v' @> undefined)

-- === state monad version of fresh var generation ===

newtype FreshT m a = FreshT (StateT FreshScope m a)
  deriving (Functor, Applicative, Monad, MonadTrans, MonadIO)

class Monad m => MonadFresh m where
  fresh :: Tag -> m Name

instance Monad m => MonadFresh (FreshT m) where
  fresh tag = FreshT $ do name <- gets (genFresh tag)
                          modify (<> name @> ())
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
  catchError (FreshT m) f = FreshT $ catchError m $ \e -> case f e of FreshT m' -> m'

-- === reader monad version of fresh var generation ===

newtype FreshRT m a = FreshRT (ReaderT FreshScope m a)
  deriving (Functor, Applicative, Monad, MonadTrans, MonadIO)

runFreshRT :: FreshRT m a -> FreshScope -> m a
runFreshRT (FreshRT m) scope = runReaderT m scope

freshName :: MonadFreshR m => Name -> (Name -> m a) -> m a
freshName v cont = do
  scope <- askFresh
  let v' = rename v scope
  localFresh (<> v' @> ()) (cont v')

freshenBinder :: MonadFreshR m =>
                 BinderP a -> (Env Name -> BinderP a -> m b) -> m b
freshenBinder (v :> ann) cont = freshName v $ \v' ->
                                  cont (v @> v') (v' :> ann)

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
