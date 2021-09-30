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
import Data.Functor.Identity
import Data.Proxy
import Control.Applicative
import Control.Monad
import GHC.TypeLits
import Data.Traversable (Traversable)
import Data.Semigroup
import qualified System.Random as SysRandom

import Table
import TableEffects
import Data.Foldable


-- Some example signatures.

data Accum m r where
  Tell :: m -> Accum m ()

data Except e r where
  Throw :: e -> Except e r

data Random r where
  SampleUniform :: Random Float

data Amb r where
  Amb :: [r] -> Amb r
  Fail :: Amb r  -- isomorphic to Amb []

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

seqEithers :: Table ix (Either e a) -> Either e (Table ix a)
seqEithers tab = -- note: a log(n) parallel version exists
  case fold (firstError <$> tab) of
    Just (First e) -> Left e
    Nothing -> Right $ flip fmap tab \(Right v) -> v
  where firstError x = case x of Left e -> Just $ First e
                                 Right _ -> Nothing

-----------------------------

data AccumOutImpl m a = AccumOutImpl m a

runAccumSlow :: Monoid m => EffComp (Accum m `EffCons` c) a -> EffComp c (a, m)
runAccumSlow comp = do
  AccumOutImpl m a <- handle ParallelizableHandler
    { handleReturn = \() r -> return $ AccumOutImpl mempty r
    , handlePerform = \() (Tell m) cont -> do
        AccumOutImpl m' v <- cont () ()
        return $ AccumOutImpl (m <> m') v
    , handleTraverse = \() ell cont -> do
        iterResults <- ell (purefor $ const ())
        let ms = fmap (\(AccumOutImpl m _) -> m) iterResults
        let as = fmap (\(AccumOutImpl _ a) -> a) iterResults
        AccumOutImpl m' b <- cont () as
        return $ AccumOutImpl (fold ms <> m') b
    } () comp
  return (a, m)

runAccum :: Monoid m => EffComp (Accum m `EffCons` c) a -> EffComp c (a, m)
runAccum comp = do
  AccumOutImpl m a <- handle ParallelizableHandler
    { handleReturn = \m r -> return $ AccumOutImpl m r
    , handlePerform = \m (Tell m') cont -> cont (m <> m') ()
    , handleTraverse = \m iters cont -> do
        iterResults <- iters =<< for (const $ return mempty)
        let ms = fmap (\(AccumOutImpl m _) -> m) iterResults
        let as = fmap (\(AccumOutImpl _ a) -> a) iterResults
        cont (m <> fold ms) as
    } mempty comp
  return (a, m)


runWeakExcept :: EffComp (Except e `EffCons` c) a -> EffComp c (Either e a)
runWeakExcept = handle ParallelizableHandler
    { handleReturn = \() r -> return $ Right r
    , handlePerform = \() (Throw e) cont -> return $ Left e
    , handleTraverse = \() ell cont -> do
        iterResults <- ell (purefor $ const ())
        case seqEithers iterResults of
          Left e -> return $ Left e
          Right a -> cont () a
    } ()


-- RandomGen can only split pairwise, so we recursively unfold it to a table
-- of the right length. (This is a serial implementation, but we note that
-- n-ary split can be implemented in parallel. See for instance
-- https://github.com/google/jax/blob/main/design_notes/prng.md)
splitKey :: forall ix g. (KnownNat ix, SysRandom.RandomGen g) => g -> Table ix g
splitKey g = UnsafeFromList @ix (splitTo g $ natVal $ Proxy @ix) where
  splitTo g 0 = []
  splitTo g 1 = [g]
  splitTo g n = g1:(splitTo g2 (n-1)) where (g1, g2) = SysRandom.split g


splitKeyPair :: SysRandom.RandomGen g => g -> (g, g)
splitKeyPair = SysRandom.split


runRandom :: SysRandom.RandomGen g
          => g -> EffComp (Random `EffCons` c) a
               -> EffComp c a
runRandom g comp = do
  Identity result <- handle ParallelizableHandler
    { handleReturn = \_ x -> return (Identity x)
    , handlePerform = \key SampleUniform cont -> let
        (val, key') = SysRandom.randomR (0.0, 1.0) key
        in cont key' val
    , handleTraverse = \key ell cont -> do
        let (key1, key2) = splitKeyPair key
            key1s = splitKey key1
        results <- ell key1s
        cont key2 (runIdentity <$> results)
    } g comp
  return result

runAmb :: EffComp (Amb `EffCons` c) a -> EffComp c [a]
runAmb = handle ParallelizableHandler
    { handleReturn = \() x -> return [x]
    , handlePerform = \() op cont -> case op of
        Amb lst -> case someTableFromList lst of
          SomeTable (tab@(UnsafeFromList _) :: Table ix a) -> do
            allRes <- for @ix \i -> cont () (tableIndex tab i)
            return $ concat allRes
        Fail -> return []
    , handleTraverse = \() (ell :: Table ix () -> EffComp c (Table ix [a]))
                        cont -> do
        iterResults <- ell (purefor $ const ())
        let
          -- Construct a list of lists such that the outer list is the list of
          -- elements in the Cartesian product of the subtable results.
          cartProd here rest = [x:y | x <- here, y <- rest]
          allOptions = foldr cartProd [[]] iterResults
          -- Now, transform each Cartesian product into a table.
          buildTable lst = purefor @ix \i -> lst !! i
          listOfTables = buildTable <$> allOptions
        case someTableFromList listOfTables of
            SomeTable (tableOfTables :: Table n (Table ix a)) -> do
              allRes <- for @n \i -> cont () $ tableIndex tableOfTables i
              return $ concat allRes
    } ()

-----------------------------
-- Paper examples
-----------------------------

sumExample :: forall a n. (KnownNat n, Num a) => Table n a -> a
sumExample xs = let
  -- Uses the Sum monoid from Data.Monoid
  (_, Sum total) = runPure $ runAccum @(Sum a) $ do
    for @n \i -> perform $ Tell (Sum $ xs `tableIndex` i)
  in total

sumExampleResult = let
  t :: Table 3 Int
  t = UnsafeFromList [1, 2, 10]
  in sumExample t
{-
sumExampleResult = 13
-}

exceptExampleResult = let
  (res, out) = runPure $ runAccum @String $ runWeakExcept @String $ do
    perform $ Tell "start "
    for @5 \i -> if i == 2
      then do
        perform $ Tell "!"
        perform $ Throw "error"
        perform $ Tell "unreachable"
      else perform $ Tell (show i)
    perform $ Tell " end"
    return "success"
  in (res, out)
{-
exceptExampleResult = (Left "error","start 01!34")
-}


binomialTimesUniform :: forall (n :: Nat) effs
                      . (KnownNat n, HasEff Random effs)
                     => Proxy n -> Float -> EffComp effs Float
binomialTimesUniform Proxy p = do
  (_, Sum count) <- runAccum @(Sum Int) $ do
                  for @n \i -> do
                    u <- perform SampleUniform
                    if u < p then perform (Tell $ Sum (1 :: Int))
                              else return ()
  v <- perform SampleUniform
  return $ v * fromIntegral count

binomialTimesUniformSamples = runPure $ runRandom (SysRandom.mkStdGen 42) $
  for @25 \_ -> binomialTimesUniform (Proxy @10) 0.5
{-
binomialTimesUniformSamples = UnsafeFromList [
  0.43065935,3.277556,1.4034967,1.987745,1.1185107,0.8557263,3.6632566,
  1.9428821,0.62515354,1.006568,5.4216843,3.359895,4.139462,3.5545158,
  3.6106176,2.1489043,5.1592393,2.1791978,0.1016441,1.6595008,3.442574,
  0.3680333,6.709792,1.0665238,3.7966158]
-}


serialRandomResults = runPure $ runRandom (SysRandom.mkStdGen 42) $ do
  u0 <- perform SampleUniform
  u1 <- perform SampleUniform
  u2 <- perform SampleUniform
  return [u0, u1, u2]
{-
serialRandomResults = [0.233446,0.9456366,0.3889103]
-}

parallelRandomResults = runPure $ runRandom (SysRandom.mkStdGen 42) $ do
  us <- for @3 \_ -> perform SampleUniform
  return $ toList us
{- 
parallelRandomResults = [0.5389709,0.54385173,0.25001103]
-}

ambCoinFlips :: [String]
ambCoinFlips = runPure $ runAmb $ do
  chars <- for @3 \_ -> perform $ Amb ["H", "T"]
  return $ concat chars 
{- TODO
-}

-- How many pairs of single-digit numbers add up
-- to 13?
ambDigitPairs = let
  (_, pairs) = runPure $ runAccum @[(Int, Int)] $ runAmb $ do
    d1 <- perform $ Amb ([0,1,2,3,4,5,6,7,8,9] :: [Int]);
    d2 <- perform $ Amb ([0,1,2,3,4,5,6,7,8,9] :: [Int]);
    if d1 + d2 == 13
      then perform $ Tell [(d1, d2)]
      else return ()
  in pairs
{-
ambDigitPairs = [(4,9),(5,8),(6,7),(7,6),(8,5),(9,4)]
-}

-----------------------------

-- Except / PRNG interactions: Consistent per-iteration random numbers due
-- to RNG splitting.
listOfUniformsWithThrow :: forall ix key effs
            . ( HasEff Random effs
              , HasEff (Accum [Float]) effs
              , HasEff (Except String) effs
              , KnownNat ix)
           => Maybe Int -> EffComp effs Int
listOfUniformsWithThrow throwHere = do
  u <- perform SampleUniform
  perform $ Tell [u]
  vals <- for @ix \i -> if Just i == throwHere
    then perform $ Throw $
      "Exception at iteration " <> show i
    else do
      u' <- perform SampleUniform
      perform $ Tell [u']
      return i
  u'' <- perform SampleUniform
  perform $ Tell [u'']
  let theSum = sum vals
  return theSum


runListOfUniformsWithThrow :: forall ix. (KnownNat ix)
            => Maybe Int -> (Either String Int, [Float])
runListOfUniformsWithThrow i =
  runPure $ runAccum
          $ runWeakExcept
          $ runRandom (SysRandom.mkStdGen 42)
          $ listOfUniformsWithThrow @ix @Float i


unifListResNoThrow :: (Either String Int, [Float])
unifListResNoThrow = runListOfUniformsWithThrow @5 Nothing
{-
unifListResNoThrow =
  ( Right 10
  , [0.233446,0.69226897,0.9368594,0.7833844,0.58721304,0.81630623,0.3651057])
-}

unifListResWithThrow :: (Either String Int, [Float])
unifListResWithThrow = runListOfUniformsWithThrow @5 $ Just 2
{-
unifListResWithThrow =
  ( Left "Exception at iteration 2"
  , [0.233446,0.69226897,0.9368594,0.58721304,0.81630623])
-}
