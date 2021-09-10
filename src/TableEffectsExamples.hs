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
{-# LANGUAGE FlexibleContexts #-}


module TableEffectsExamples where

import Data.Kind
import Data.Functor
import Data.Proxy
import Control.Applicative
import Control.Monad
import GHC.TypeLits
import Data.Traversable (Traversable)
import Data.Semigroup

import TableEffects
import Data.Foldable (Foldable(fold))


-- Some example signatures.

data Accum m r where
  Tell :: m -> Accum m ()

data Except e r where
  Throw :: e -> Except e r


data Random key r where
  NextKey :: Random key key

-- Only parallelizable if we impose a strong applicative restriction? So maybe
-- we don't actually implement these.
data State s r where
  Get :: State s s
  Put :: s -> State s ()

data PrefixScan m r where
  Append :: m -> PrefixScan m ()
  CurrentPrefix :: PrefixScan m m

-----------------------------
-- Utilities

tableToList :: forall ix a. Table ix a -> [a]
tableToList tab@(Table _) = tableIndex tab . fromOrdinal <$> [0..size @ix - 1]

foldrTable :: (a -> b -> b) -> b -> Table ix a -> b
foldrTable f b tab = -- note: a log(n) parallel version exists
  foldr f b $ tableToList tab

concatTable :: Monoid m => Table ix m -> m
concatTable tab = -- note: a log(n) parallel version exists
  fold $ tableToList tab

seqEithers :: Table ix (Either e a) -> Either e (Table ix a)
seqEithers tab = -- note: a log(n) parallel version exists
  case concatTable (firstError <$> tab) of
    Just (First e) -> Left e
    Nothing -> Right $ flip fmap tab \(Right v) -> v
  where firstError x = case x of Left e -> Just $ First e
                                 Right _ -> Nothing

-----------------------------

data AccumOutImpl m a = AccumOutImpl m a

runAccumSlow :: Monoid m => EffComp (Accum m `EffCons` c) a -> EffComp c (m, a)
runAccumSlow comp = do
  AccumOutImpl m a <- handleWithRet WithRetEffHandler
    { retR = return . AccumOutImpl mempty
    , handleR = \(Tell m) cont -> do
        AccumOutImpl m' v <- cont ()
        return $ AccumOutImpl (m <> m') v
    , parallelR = \iterResults cont -> do
        let ms = fmap (\(AccumOutImpl m _) -> m) iterResults
        let as = fmap (\(AccumOutImpl _ a) -> a) iterResults
        AccumOutImpl m' b <- cont as
        return $ AccumOutImpl (concatTable ms <> m') b
    } comp
  return (m, a)

runAccumFast :: Monoid m => EffComp (Accum m `EffCons` c) a -> EffComp c (m, a)
runAccumFast comp = do
  AccumOutImpl m a <- handleForkStateWithRet ForkStateWithRetEffHandler
    { retFR = \m r -> return $ AccumOutImpl m r
    , handleFR = \m (Tell m') cont -> cont (m <> m') ()
    , parallelFR = \m iters cont -> do
        iterResults <- iters =<< for (const $ return mempty)
        let ms = fmap (\(AccumOutImpl m _) -> m) iterResults
        let as = fmap (\(AccumOutImpl _ a) -> a) iterResults
        cont (m <> concatTable ms) as
    } mempty comp
  return (m, a)


runExceptSoft :: EffComp (Except e `EffCons` c) a -> EffComp c (Either e a)
runExceptSoft = handleWithRet WithRetEffHandler
    { retR = return . Right
    , handleR = \(Throw e) cont -> return $ Left e
    , parallelR = \iterResults cont -> case seqEithers iterResults of
        Left e -> return $ Left e
        Right a -> cont a
    }

newtype MockPRNGKey = MockPRNGKey String deriving (Eq, Show)

splitKey :: IndexSet ix => MockPRNGKey -> Table ix MockPRNGKey
splitKey (MockPRNGKey s) =
  Table \i -> MockPRNGKey $ s <> "_" <> show (ordinal i)

splitKeyPair :: MockPRNGKey -> (MockPRNGKey, MockPRNGKey)
splitKeyPair (MockPRNGKey s) = (MockPRNGKey $ s <> "_0", MockPRNGKey $ s <> "_1")

runMockRandom :: MockPRNGKey -> EffComp (Random MockPRNGKey `EffCons` c) a
                             -> EffComp c a
runMockRandom = handleForkState ForkStateEffHandler
    { handleF = \key NextKey -> return $ splitKeyPair key
    , parallelF = \key -> let
        (key1, key2) = splitKeyPair key
        key1s = splitKey key1
        in return (key1s, key2)
    }

-----------------------------

-- Demo function: Draw "random numbers" and accumulate them, possibly throwing
-- an exception partway through.
myDemoFunc :: forall key ix effs
            . ( HasEff (Random key) effs
              , HasEff (Accum [key]) effs
              , HasEff (Except String) effs
              , IndexSet ix
              , Eq ix)
           => Maybe ix -> EffComp effs Integer
myDemoFunc throwHere = do
  k <- effect $ NextKey @key
  effect $ Tell [k]
  vals <- for \i -> if Just i == throwHere
    then effect $ Throw $
      "Exception at iteration " <> show (ordinal i)
    else do
      k' <- effect $ NextKey @key
      effect $ Tell [k']
      return $ ordinal i
  k <- effect $ NextKey @key
  effect $ Tell [k]
  let theSum = foldrTable (+) 0 vals
  return theSum


-- Run the demo func.
runDemoFunc :: (IndexSet ix, Eq ix)
            => Maybe ix -> ([MockPRNGKey], Either String Integer)
runDemoFunc ix =
  runPure $ runAccumFast
          $ runExceptSoft
          $ runMockRandom (MockPRNGKey "rootKey")
          $ myDemoFunc @MockPRNGKey ix


res1 :: ([MockPRNGKey], Either String Integer)
res1 = runDemoFunc $ Nothing @(Fin 5)
{-
( [ MockPRNGKey "rootKey_1",
  , MockPRNGKey "rootKey_0_0_0_1"
  , MockPRNGKey "rootKey_0_0_1_1"
  , MockPRNGKey "rootKey_0_0_2_1"
  , MockPRNGKey "rootKey_0_0_3_1"
  , MockPRNGKey "rootKey_0_0_4_1"
  , MockPRNGKey "rootKey_0_1_1"
  ]
, Right 15)
-}

res2 :: ([MockPRNGKey], Either String Integer)
res2 = runDemoFunc $ Just $ fromOrdinal @(Fin 5) 2
{-
( [ MockPRNGKey "rootKey_1",
  , MockPRNGKey "rootKey_0_0_0_1"
  , MockPRNGKey "rootKey_0_0_1_1"
  -- (no entry for 2 since it threw)
  , MockPRNGKey "rootKey_0_0_3_1"
  , MockPRNGKey "rootKey_0_0_4_1"
  -- (no entry for post-loop tell)
  ]
, Left "Exception at iteration 2")
-}
