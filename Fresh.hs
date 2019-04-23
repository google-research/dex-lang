{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
-- those last three are all needed for monaderror

module Fresh (Name, Tag, Stem, fresh, freshLike, FreshT, runFreshT,
              rawName, nameRoot, topTag, catNames, rawQualify) where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except hiding (Except)
import qualified Data.Map.Strict as M
import Data.Text.Prettyprint.Doc

newtype Name = Name [(Tag, Int)] deriving (Show, Ord, Eq)
type Stem = Name
type Tag = String

type FreshState = (Stem, M.Map Tag Int)

newtype FreshT m a = FreshT (StateT FreshState m a)
  deriving (Functor, Applicative, Monad, MonadTrans, MonadIO)

type Fresh a = FreshT Identity a

freshLike :: MonadFresh m => Name -> m Name
freshLike name = fresh (topTag name)

rawName :: Tag -> Name
rawName s = Name [(s, 0)]

rawQualify :: Tag -> Name -> Name
rawQualify tag (Name names) = Name ((tag,0):names)

topTag :: Name -> Tag
topTag (Name ((tag,_):_)) = tag

nameRoot = Name []

freshNames :: Stem -> [Tag] -> [Name]
freshNames stem tags = runFresh (mapM fresh tags) stem

catNames :: Name -> Name -> Name
catNames (Name n1) (Name n2) = Name (n1 ++ n2)

class Monad m => MonadFresh m where
  fresh :: Tag -> m Name

instance Monad m => MonadFresh (FreshT m) where
  fresh tag = FreshT $ do Name stem <- gets fst
                          count <- gets $ getCount tag . snd
                          modify $ updateSnd (M.insert tag (count + 1))
                          return $ Name $ (tag, count) : stem

runFreshT :: Monad m => FreshT m a -> Stem -> m a
runFreshT (FreshT s) stem = evalStateT s (stem, mempty)

runFresh :: Fresh a -> Stem -> a
runFresh m stem = runIdentity $ runFreshT m stem

getCount :: Ord k => k -> M.Map k Int -> Int
getCount k m = case M.lookup k m of Just n -> n
                                    Nothing -> 0

updateSnd :: (b -> c) -> (a, b) -> (a, c)
updateSnd f (x, y) = (x, f y)

-- TODO: this needs to be injective but it's currently not
-- (needs to figure out acceptable tag strings)
instance Pretty Name where
  pretty (Name xs) = mconcat $ punctuate "_" (map prettyComponents xs)
    where prettyComponents :: (Tag, Int) -> Doc ann
          prettyComponents (tag, n) = pretty tag <> suffix
            where suffix = case n of 0 -> ""
                                     _ -> "_" <> pretty n

instance MonadFresh m => MonadFresh (StateT s m) where
  fresh s = lift $ fresh s

instance MonadFresh m => MonadFresh (ReaderT r m) where
  fresh s = lift $ fresh s

instance MonadError e m => MonadError e (FreshT m) where
  throwError = lift . throwError
  catchError = undefined
