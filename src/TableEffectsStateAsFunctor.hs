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


module TableEffectsStateAsFunctor where

import Data.Kind
import Data.Functor
import Data.Proxy
import Control.Applicative
import Control.Monad
import GHC.TypeLits
import Data.Traversable (Traversable)
import Data.Semigroup

import Table
import TableEffects
import Data.Foldable

import Debug.Trace

-- Some example signatures.

data Accum m r where
  Tell :: m -> Accum m ()

data Except e r where
  Throw :: e -> Except e r

data Random key r where
  NextKey :: Random key key

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

-- listFor :: [a] -> (a -> EffComp sig b) -> EffComp sig [b]
-- listFor lst f = case listToTable lst of
--   SomeTable (tab@(Table _) :: Table ix a) -> do
--     allRes <- for \i -> f (tableIndex tab i)
--     return $ tableToList allRes

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
        return $ AccumOutImpl (fold ms <> m') b
    } comp
  return (m, a)

-- Using the helper to thread through state.
runAccumFast :: Monoid m => EffComp (Accum m `EffCons` c) a -> EffComp c (m, a)
runAccumFast comp = do
  AccumOutImpl m a <- handleForkStateWithRet ForkStateWithRetEffHandler
    { retFR = \m r -> return $ AccumOutImpl m r
    , handleFR = \m (Tell m') cont -> cont (m <> m') ()
    , parallelFR = \m iters cont -> do
        iterResults <- iters =<< for (const $ return mempty)
        let ms = fmap (\(AccumOutImpl m _) -> m) iterResults
        let as = fmap (\(AccumOutImpl _ a) -> a) iterResults
        cont (m <> fold ms) as
    } mempty comp
  return (m, a)

-- Encoding of runAccum that threads state through manually.
newtype ManualStateAccumOutImpl effs s a = ManualStateAccumOutImpl (s -> effs (s, a))
runAccumManualState :: (Monoid s, Show s) => EffComp (Accum s `EffCons` c) a -> EffComp c (s, a)
runAccumManualState comp = do
  ManualStateAccumOutImpl thunk <- handleWithRet WithRetEffHandler
    { retR = \x -> return $ ManualStateAccumOutImpl (\s -> return (s, x))
    , handleR = \(Tell m) cont -> return $ ManualStateAccumOutImpl $ \s -> do
        ManualStateAccumOutImpl contthunk <- cont ()
        contthunk (s <> m)
    , parallelR = \(iterComps@(UnsafeFromList _) :: Table ix iterty) cont -> do
        iterResults <- for @ix \i -> do
          let ManualStateAccumOutImpl iterthunk = tableIndex iterComps i
          (s', a') <- iterthunk mempty
          traceM ("loop iter" ++ show i ++ " got " ++ show s')
          return (s', a')
        let ms = foldMap fst iterResults
        let as = fmap snd iterResults
        traceM $ "ms are " ++ show ms
        ManualStateAccumOutImpl contthunk <- cont as
        return $ ManualStateAccumOutImpl $ \s -> do
          traceM ("running with state" ++ show s)
          contthunk (s <> ms)
    } comp
  thunk mempty

runExceptSoft :: EffComp (Except e `EffCons` c) a -> EffComp c (Either e a)
runExceptSoft = handleWithRet WithRetEffHandler
    { retR = return . Right
    , handleR = \(Throw e) cont -> return $ Left e
    , parallelR = \iterResults cont -> do
        traceM "either is combining"
        case seqEithers iterResults of
          Left e -> do
            traceM "either failed"
            return $ Left e
          Right a -> do
            traceM "either succeeded"
            cont a
    }

newtype MockPRNGKey = MockPRNGKey String deriving (Eq, Show)

splitKey :: KnownNat ix => MockPRNGKey -> Table ix MockPRNGKey
splitKey (MockPRNGKey s) = purefor \i -> MockPRNGKey $ s <> "_" <> show i

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

newtype ManualStateRandomImpl effs key a = ManualStateRandomImpl (key -> effs a)
runMockRandomManualState :: MockPRNGKey -> EffComp (Random MockPRNGKey `EffCons` c) a
                             -> EffComp c a
runMockRandomManualState seed comp = do
  ManualStateRandomImpl thunk <- handleWithRet WithRetEffHandler
    { retR = return . ManualStateRandomImpl . const . return
    , handleR = \NextKey cont -> 
        return $ ManualStateRandomImpl $ \key -> do
          let (key1, key2) = splitKeyPair key
          ManualStateRandomImpl contthunk <- cont key1
          contthunk key2
    , parallelR = \(iterComps@(UnsafeFromList _) :: Table ix iterty) cont ->
        return $ ManualStateRandomImpl $ \key -> do
          let (key1, key2) = splitKeyPair key
              key1s = splitKey @ix key1
          iterResults <- for @ix \i -> do
            let ManualStateRandomImpl iterthunk = tableIndex iterComps i
            iterthunk (tableIndex key1s i)
          ManualStateRandomImpl contthunk <- cont iterResults
          contthunk key2
    } comp
  thunk seed

-- Somewhat hairy because it has to keep converting between tables and lists.
-- Might be better in Dex?
runAmb :: EffComp (Amb `EffCons` c) a -> EffComp c [a]
runAmb = handleWithRet WithRetEffHandler
    { retR = \x -> return [x]
    , handleR = \op cont -> case op of
        Amb lst -> case fromList lst of
          SomeTable (tab@(UnsafeFromList _) :: Table ix a) -> do
            allRes <- for @ix \i -> cont (tableIndex tab i)
            return $ concat allRes
        Fail -> return []
    , parallelR = \(iterResults@(UnsafeFromList _) :: Table ix [a]) cont -> let
        -- Construct a list of lists such that the outer list is the list of
        -- elements in the Cartesian product of the subtable results.
        cartProd here rest = [x:y | x <-  here, y <- rest]
        allOptions = foldr cartProd [] iterResults
        -- Now, transform each Cartesian product into a table.
        buildTable lst = purefor @ix \i -> lst !! i
        listOfTables = buildTable <$> allOptions
        in case fromList listOfTables of
          SomeTable (tableOfTables :: Table n (Table ix a)) -> do
            allRes <- for @n \i -> cont $ tableIndex tableOfTables i
            return $ concat allRes
    }

-----------------------------

-- Demo function: Draw "random numbers" and accumulate them, possibly throwing
-- an exception partway through.
myDemoFunc :: forall ix key effs
            . ( HasEff (Random key) effs
              , HasEff (Accum [key]) effs
              , HasEff (Except String) effs
              , KnownNat ix)
           => Maybe Int -> EffComp effs Int
myDemoFunc throwHere = do
  k <- effect $ NextKey @key
  effect $ Tell [k]
  vals <- for @ix \i -> if Just i == throwHere
    then effect $ Throw $
      "Exception at iteration " <> show i
    else do
      k' <- effect $ NextKey @key
      effect $ Tell [k']
      return i
  k <- effect $ NextKey @key
  effect $ Tell [k]
  let theSum = sum vals
  return theSum


-- Run the demo func.
runDemoFunc :: forall ix. (KnownNat ix)
            => Maybe Int -> ([MockPRNGKey], Either String Int)
runDemoFunc i =
  runPure $ runAccumManualState
          $ runExceptSoft
          $ runMockRandomManualState (MockPRNGKey "rootKey")
          $ myDemoFunc @ix @MockPRNGKey i


res1 :: ([MockPRNGKey], Either String Int)
res1 = runDemoFunc @5 Nothing
{-
( [ MockPRNGKey "rootKey_1",
  , MockPRNGKey "rootKey_0_0_0_1"
  , MockPRNGKey "rootKey_0_0_1_1"
  , MockPRNGKey "rootKey_0_0_2_1"
  , MockPRNGKey "rootKey_0_0_3_1"
  , MockPRNGKey "rootKey_0_0_4_1"
  , MockPRNGKey "rootKey_0_1_1"
  ]
, Right 10)
-}

res2 :: ([MockPRNGKey], Either String Int)
res2 = runDemoFunc @5 $ Just 2
{-
([MockPRNGKey "rootKey_0"],Left "Exception at iteration 2")
-}

{- Note: Changing semantics via state reduction

Suppose we have

  runPure $ runAccumManualState
          $ runExceptSoft
          $ runMockRandomManualState (MockPRNGKey "rootKey")
          $ ...

Further suppose that we either throw without generating a random number, or
we accumulate AFTER generating a random number.

Desired behavior: Either way, we execute the loop with a RNG key. We run all
iterations in parallel, and one of them throws. This halts that iteration, but
the other iterations all run to completion. We then abort at the end. All
accumulation results get written.

Actual behavior: `runMockRandomManualState` changes the structure of the
computation to now build a table of functions, then call the functions. However,
since the throw does not depend on the random key, the throw happens while
building the function! On the other hand, the accum depends on the random key,
so the accum does NOT happen while building the function (we see a loop where
none of the iterations do anything). Then the throw aborts the computation.
This means that the random handler never actually calls any of the continuations
it built, which means that it never runs the effects for accum.

Essentially, the `runMockRandomManualState` handler introduces a new loop
synchronization point that separates computations that can be done without a
random key from computations that use a random key; each of these becomes a
separate for loop. Then the except handler chooses to abort inside the first
loop, but the accum handler only has any side effects inside the second loop.
-}
