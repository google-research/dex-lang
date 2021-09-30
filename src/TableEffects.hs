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
{-# LANGUAGE TypeFamilies #-}


module TableEffects where

import Data.Kind
import Data.Functor
import Data.Proxy
import Control.Applicative
import Control.Monad
import GHC.TypeLits
import Data.Traversable (Traversable)

import Table


-- An effect signature is a parameterized data type, parameterized by the output
-- type of the effect, and whose values are the operations defined by that
-- effect.
type EffSig = * -> *


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

-- Some unfortunate type family shenanigans here to get around restrictions
-- of Haskell's instance solver.
type family HasEffAtTop (sig :: EffSig) (union :: EffSig) :: Bool where
  HasEffAtTop sig (sig `EffCons` rest) = True
  HasEffAtTop _ _ = False

class HasEff_ (sig :: EffSig) (union :: EffSig) (atTop :: Bool) where
  liftEff_ :: sig r -> union r

instance HasEff_ sig union (HasEffAtTop sig union) => HasEff sig union where
  liftEff = liftEff_ @sig @union @(HasEffAtTop sig union)

instance HasEff_ sig (sig `EffCons` rest) True where
  liftEff_ op = Here op

instance HasEff sig rest => HasEff_ sig (other `EffCons` rest) False where
  liftEff_ op = There (liftEff op)



-- Given the above, we can construct a data type representing a (possibly)
-- parallelizable effectful computation. We only care about parallelism within
-- for loop constructs.
data EffOrTraversal sig r where
  Effect :: sig r -> EffOrTraversal sig r
  TraverseTable :: Table n (EffComp sig s) -> EffOrTraversal sig (Table n s)

data EffComp (sig :: EffSig) r where
  -- Return a value without having any effects.
  Pure :: r -> EffComp sig r
  -- Do some effects, then call a continuation.
  -- (optimization opportunity: use a more efficient representation of the
  -- continuation such as Arrs / FTCQueue, as in freer monad)
  Impure :: EffOrTraversal sig r -> (r -> EffComp sig s) -> EffComp sig s



-- We can build this up with Haskell methods
instance Functor (EffComp sig) where
  -- no actions: apply f
  fmap f (Pure v) = Pure $ f v
  -- map f over the result of the first action
  fmap f (Impure action cont) = Impure action (fmap f . cont)

instance Applicative (EffComp sig) where
  pure r = Pure r
  -- Apply f if it's pure
  Pure f <*> v = fmap f v
  -- Take one step in evaluating f
  Impure fa fc <*> v = Impure fa $ \a -> fc a <*> v

instance Monad (EffComp sig) where
  Pure v >>= f = f v
  Impure va vc >>= f = Impure va $ \a -> vc a >>= f

-- To expose the table-specific parallelism, we give a special implementation
-- of traversing tables under effects. (Note that Table does NOT implement the
-- ordinary Traversable class.)
traverseTable :: (a -> EffComp sig b) -> Table n a -> EffComp sig (Table n b)
traverseTable f a = Impure (TraverseTable (f <$> a)) Pure

for :: KnownNat n => (Int -> EffComp sig b) -> EffComp sig (Table n b)
for = flip traverseTable iota

-- We also provide a hook to call effects easily.
perform :: HasEff sig union => sig r -> EffComp union r
perform e = Impure (Effect $ liftEff e) Pure



-- When the computation is known to be pure, we can stitch all of the different
-- pieces together.
runPure :: EffComp EffNil r -> r
runPure = \case
  Pure r -> r
  Impure (Effect eff) cont -> case eff of {} -- impossible
  Impure (TraverseTable iters) cont -> runPure $ cont $ fmap runPure iters

-- For effectful computations, we must provide a handler.
data ParallelizableHandler (op :: EffSig) (m :: * -> *) s (f :: * -> *) =
  ParallelizableHandler
  { handleReturn   :: forall a.      s -> a -> m (f a)
  , handlePerform  :: forall a b.    s -> op a -> (s -> a -> m (f b)) -> m (f b)
  , handleTraverse :: forall a b ix. KnownNat ix
                                  => s
                                  -> (Table ix s -> m (Table ix (f a)))
                                  -> (s -> Table ix a -> m (f b))
                                  -> m (f b)
  }

handle :: forall op rest s f a
                        . ParallelizableHandler op (EffComp rest) s f
                       -> s
                       -> EffComp (op `EffCons` rest) a
                       -> EffComp rest (f a)
handle h@ParallelizableHandler{handleReturn, handlePerform, handleTraverse}
       s comp =
  case comp of
    Pure r -> handleReturn s r
    Impure (Effect (Here op)) cont -> handlePerform s op (\s a -> rec s $ cont a)
    Impure (Effect (There op)) cont -> Impure (Effect op) (rec s . cont)
    -- unpack iters to get a proof of KnownNat n
    Impure (TraverseTable iters@(UnsafeFromList _ :: Table n b)) cont
      -> handleTraverse s runIters runCont
      where
        runIters ss = for $ \i -> rec (tableIndex ss i) (tableIndex iters i)
        runCont s a = rec s (cont a)
  where
    rec :: forall b. s -> EffComp (op `EffCons` rest) b -> EffComp rest (f b)
    rec = handle h

