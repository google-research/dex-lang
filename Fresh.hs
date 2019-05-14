{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
-- those last three are all needed for monaderror

module Fresh (Name (..), Tag, Stem, fresh, freshLike,
              FreshT, runFreshT, runFresh,
              rawName, rawNames, nameRoot, topTag, catNames, rawQualify,
              newScope, rename, getRenamed, FreshScope,
              EnvM, runEnvM, addEnv, askEnv, liftEnvM) where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Writer
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

rawNames :: Tag -> [Name]
rawNames s = [Name [(s, i)] | i <- [0..]]

rawQualify :: Tag -> Name -> Name
rawQualify tag (Name names) = Name ((tag,0):names)

topTag :: Name -> Tag
topTag (Name ((tag,_):_)) = tag
topTag (Name []) = error "whoops! [topTag]"

nameRoot = Name []

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

-- === reader monad version of fresh var generation ===

rename :: Name -> FreshScope -> (Name, FreshScope)
rename v@(Name [(tag, _)]) (FreshScope _ vars) = (v', scopeDiff)
  where n = M.findWithDefault 0 tag vars
        v' = Name [(tag, n)]
        scopeDiff = FreshScope (M.singleton v v') (M.singleton tag (n+1))

getRenamed :: Name -> FreshScope -> Name
getRenamed v scope = case M.lookup v (varSubst scope) of
                       Just v' -> v'
                       Nothing -> v

newScope :: Name -> FreshScope
newScope (Name [(tag, i)]) = FreshScope mempty (M.singleton tag (i+1))

data FreshScope = FreshScope
  { varSubst    :: M.Map Name Name
  , varsInScope :: M.Map Tag Int }  deriving (Show)

instance Semigroup FreshScope where
  (FreshScope a b) <> (FreshScope a' b') =
    FreshScope (a<>a') (M.unionWith max b b')

instance Monoid FreshScope where
  mempty = FreshScope mempty mempty
  mappend = (<>)

-- monad for doing things in a monoidal environment
-- TODO: consider making an mtl-style typeclass
newtype EnvM env a = EnvM (StateT env (Writer env) a)
  deriving (Functor, Applicative, Monad)

addEnv :: Monoid env => env -> EnvM env ()
addEnv x = EnvM $ modify (x <>) >> tell x

askEnv :: Monoid env => EnvM env env
askEnv = EnvM get

runEnvM :: Monoid env => EnvM env a -> env -> (a, env)
runEnvM (EnvM m) env = runWriter $ evalStateT m env

liftEnvM :: (Monoid env, MonadReader env m) => EnvM env a -> m (a, env)
liftEnvM m = liftM (runEnvM m) ask
