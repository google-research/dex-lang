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

module MonadWithParallelTraverse
    () where

import Data.Kind
import Data.Functor
import Control.Applicative
import Control.Monad


class Monad f => MonadWithParallelTraverse (f :: * -> *) where
  parallelTraverse :: [f a] -> f [a]



-- An effect signature is a parameterized data type, parameterized by the output
-- type of the effect, and whose values are the operations defined by that
-- effect.
type EffSig = * -> *

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


-- We can combine a collection of effect signatures into a simple ordered union
-- type. For instance,
--    State s `EffCons` Except e `EffCons` EffNil
-- is the signature of a computation that can use either state or except
-- effects, where we happen to know that the state effect will be handled
-- first.
data EffCons (sig :: EffSig) (sigs :: EffSig) r = Here (sig r) | There (sigs r)
infixr 5 `EffCons`
data EffNil r  -- empty effect type has no operations


-- If we don't know the order, we can just impose restrictions with typeclasses.
-- The HasEff constraint ensures we can lift an operation into the union type,
-- no matter what the union type ends up being.
class HasEff (sig :: EffSig) (union :: EffSig) where
  liftEff :: sig r -> union r

instance HasEff sig (sig `EffCons` rest) where
  liftEff op = Here op

instance {--OVERLAPPING--} HasEff sig rest
    => HasEff sig (other `EffCons` rest) where
  liftEff op = There (liftEff op)


-- Given the above, we can construct a data type representing a (possibly)
-- parallelizable effectful computation. We only care about parallelism within
-- list constructs.
data FreeMWPT (sig :: EffSig) r where
  -- Return a value without having any effects.
  Pure :: r -> FreeMWPT sig r
  -- Execute an effect.
  Effect :: sig r -> FreeMWPT sig r
  -- Monad API: Compose effects with dependencies.
  Bind :: FreeMWPT sig a -> (a -> FreeMWPT sig b) -> FreeMWPT sig b
  -- Sort-of applicative list traversal construct. We want to maintain the
  -- invariant that we never pattern match on a list, only traverse it in
  -- parallel.
  ParallelTraverse :: [FreeMWPT sig r] -> FreeMWPT sig [r]

-- We can use the normal Haskell instances to build up our computation.
instance Functor (FreeMWPT sig) where
  fmap f c = c `Bind` (Pure . f)

instance Applicative (FreeMWPT sig) where
  pure r = Pure r
  f <*> c = f `Bind` \fv -> c `Bind` \cv -> Pure (fv cv)

instance Monad (FreeMWPT sig) where
  c >>= f = c `Bind` f

-- To expose the table-specific parallelism, we handle "for" separately
for :: [a] -> (a -> FreeMWPT sig b) -> FreeMWPT sig [b]
for xs f = ParallelTraverse (f <$> xs)

-- We also provide a hook to call effects easily.
effect :: HasEff sig union => sig r -> FreeMWPT union r
effect e = Effect $ liftEff e



-- When the computation is itself pure, we can stitch all of the different
-- pieces together.
runPure :: FreeMWPT EffNil r -> r
runPure = \case
  Pure r -> r
  Effect eff -> case eff of {} -- impossible
  ParallelTraverse cs -> map runPure cs
  Bind ca fc -> runPure (fc (runPure ca))


-- Similar to the free monad, we can use a homomorphism to any concrete free
-- monad with parallel traverse to unwrap a layer of effects.
handleHomomorphism :: forall c sig union ans m
      . MonadWithParallelTraverse m
      => (forall r. sig r -> FreeMWPT union (m r))
      -> FreeMWPT (sig `EffCons` union) ans
      -> FreeMWPT union (m ans)
handleHomomorphism handler = \case
    Pure r -> Pure $ pure r
    Effect (Here op) -> handler op
    Effect (There op) -> pure <$> Effect op
    ParallelTraverse cs -> undefined --ParallelTraverse (map rec cs)
    Bind ca fc -> rec ca >>= \ma -> Pure $ ma >>= \a -> undefined -- fc a
  where
    rec :: forall t. FreeMWPT (sig `EffCons` union) t -> FreeMWPT union (m t)
    rec = handleHomomorphism handler

    doublebind :: forall s t. FreeMWPT union (m s) -> (s -> FreeMWPT union (m t)) -> FreeMWPT union (m t)
    doublebind v f = v `Bind` \x -> let foo = f <$> x in undefined -- not possible in general!
