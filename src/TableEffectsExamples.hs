{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE AllowAmbiguousTypes #-}


module TableEffectsExamples
    () where

import Data.Kind
import Data.Functor
import Data.Proxy
import Control.Applicative
import Control.Monad
import GHC.TypeLits
import Data.Traversable (Traversable)

import TableEffects


-- Some example signatures.
data State s r where
  Get :: State s s
  Put :: s -> State s ()

data Accum m r where
  Tell :: m -> Accum m ()

data PrefixScan m r where
  Append :: m -> PrefixScan m ()
  CurrentPrefix :: PrefixScan m m

data Except e r where
  Throw :: e -> Except e r



data AccumOutImpl m a = AccumOutImpl m a

concat :: Monoid m => Table ix m -> m
concat = undefined -- assume a log(n) solution exists

runAccumSlow :: Monoid m => EffComp (Accum m `EffCons` c) a -> EffComp c (m, a)
runAccumSlow comp = do
  AccumOutImpl m a <- handleOutput OutputEffHandler
    { retO = AccumOutImpl mempty
    , handleO = \(Tell m) cont -> do
        AccumOutImpl m' v <- cont ()
        return $ AccumOutImpl (m <> m') v
    , parallelO = \iterResults cont -> let
        ms = fmap (\(AccumOutImpl m _) -> m) iterResults
        as = fmap (\(AccumOutImpl _ a) -> a) iterResults
        AccumOutImpl m' b <- cont as
        return $ AccumOutImpl (concat ms <> m') b
    } comp
  return (m, a)

runAccumFast :: Monoid m => EffComp (Accum m `EffCons` c) a -> EffComp c (m, a)
runAccumFast comp = do
  AccumOutImpl m a <- handleInputOutput InputOutputEffHandler
    { retIO = AccumOutImpl
    , handleIO = \m (Tell m') cont -> cont (m <> m') ()
    , parallelIO = \m iters cont -> do
        iterResults <- iters (for $ const mempty)
        let ms = fmap (\(AccumOutImpl m _) -> m) iterResults
        let as = fmap (\(AccumOutImpl _ a) -> a) iterResults
        cont (m <> concat ms) as
    } mempty comp
  return (m, a)


catEithers :: Table ix (Either e a) -> Either e (Table ix a)
catEithers = undefined -- assume a log(n) solution exists

runExceptSoft :: EffComp (Except e `EffCons` c) a -> EffComp c (Either e a)
runExceptSoft comp = handleOutput OutputEffHandler
    { retO = Right
    , handleO = \(Throw e) cont -> return $ Left e
    , parallelO = \iterResults cont -> case catEithers iterResults of
        Left e -> return $ Left e
        Right a -> cont a
    } comp


splitKey :: IndexSet ix => PRNGKey -> Table ix PRNGKey
splitKey = undefined -- assume exists
splitKeyPair :: PRNGKey -> (PRNGKey, PRNGKey)
splitKey = undefined -- assume exists

runPRNGKey :: PRNGKey -> EffComp (Random `EffCons` c) a -> EffComp c a
runPRNGKey = handleInputSimple SimpleInputEffHandler
    { handleISimple = \key NextKey -> splitKey
    , parallelISimple = \key iters -> let
        key1, key2 = splitKeyPair key
        key1s = splitKey key1
        in (key1s, key2)
    } comp
