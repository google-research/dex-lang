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


module TableEffects where

import Data.Kind
import Data.Functor
import Data.Proxy
import Control.Applicative
import Control.Monad
import GHC.TypeLits
import Data.Traversable (Traversable)


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


-- Hack to let us reason about dex-style static tables in Haskell.
data Table a b where
  Table :: IndexSet a => (a -> b) -> Table a b

deriving instance Functor (Table a)

class IndexSet a where
  size :: Integer
  iota :: Table a a

newtype Fin (n :: Nat) = UnsafeFromOrdinal Integer

instance KnownNat n => IndexSet (Fin n) where
  size = natVal (Proxy @n)
  iota = Table id

tableIndex :: Table a b -> a -> b
tableIndex (Table f) = f

-- Given the above, we can construct a data type representing a (possibly)
-- parallelizable effectful computation. We only care about parallelism within
-- list constructs.
data EffOrTraversal sig r where
  Effect :: sig r -> EffOrTraversal sig r
  TraverseTable :: Table ix (EffComp sig s) -> EffOrTraversal sig (Table ix s)

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

-- To expose the table-specific parallelism, we handle "for" separately
for :: IndexSet a => (a -> EffComp sig b) -> EffComp sig (Table a b)
for f = Impure (TraverseTable (f <$> iota)) Pure

-- We also provide a hook to call effects easily.
effect :: HasEff sig union => sig r -> EffComp union r
effect e = Impure (Effect $ liftEff e) Pure


-- When the computation is known to be pure, we can stitch all of the different
-- pieces together.
runPure :: EffComp EffNil r -> r
runPure = \case
  Pure r -> r
  Impure (Effect eff) cont -> case eff of {} -- impossible
  Impure (TraverseTable iters) cont -> runPure $ cont $ fmap runPure iters

-- For other effects, we consider a few classes of handler that can be
-- parallelized. The easiest ones to reason about are read-only and write-only
-- effects. We can also build something for input/output effects, but I'm not
-- sure we have any "reasonable" instances for those.
-- TODO: should we specialize `m` to a concrete `EffComp rest`?
data OutputEffHandler (op :: EffSig) (m :: * -> *) (f :: * -> *) = OutputEffHandler
  { retO      :: forall a. a -> f a
  , handleO   :: forall a b. Monad m
              => op a       -> (a   -> m (f b)) -> m (f b)
  , parallelO :: forall a b ix. Monad m
              => Table ix (f a) -> (Table ix a -> m (f b)) -> m (f b)
  }

handleOutput :: forall op rest f a
              . OutputEffHandler op (EffComp rest) f
             -> EffComp (op `EffCons` rest) a
             -> EffComp rest (f a)
handleOutput h@OutputEffHandler{retO, handleO, parallelO} comp = case comp of
    Pure r -> Pure $ retO r
    Impure (Effect (Here op)) cont -> handleO op (rec . cont)
    Impure (Effect (There op)) cont -> Impure (Effect op) (rec . cont)
    Impure (TraverseTable iters) cont -> 
      Impure (TraverseTable $ fmap rec iters) $ \iterResults ->
        parallelO iterResults (rec . cont)
  where
    rec :: forall b. EffComp (op `EffCons` rest) b -> EffComp rest (f b)
    rec = handleOutput h


data InputEffHandler (op :: EffSig) (m :: * -> *) s = InputEffHandler
  { handleI   :: forall a b. Monad m
              => s -> op a     -> (s -> a   -> m b) -> m b
  , parallelI :: forall a b ix. Monad m
              => s -> (Table ix s -> m a) -> (s -> a -> m b) -> m b
  }

handleInput :: forall op rest s a
             . InputEffHandler op (EffComp rest) s
            -> s
            -> EffComp (op `EffCons` rest) a
            -> EffComp rest a
handleInput h@InputEffHandler{handleI, parallelI} s comp = case comp of
    Pure r -> Pure r
    Impure (Effect (Here op)) cont -> handleI s op (\s a -> rec s $ cont a)
    Impure (Effect (There op)) cont -> Impure (Effect op) (rec s . cont)
    Impure (TraverseTable iters@(Table _)) cont  -- unpack iters to get a proof of IndexSet ix
      -> parallelI s runIters runCont
      where
        runIters ss = for $ \i -> rec (tableIndex ss i) (tableIndex iters i)
        runCont s a = rec s (cont a)
  where
    rec :: forall b. s -> EffComp (op `EffCons` rest) b -> EffComp rest b
    rec = handleInput h


data SimpleInputEffHandler (op :: EffSig) (m :: * -> *) s = SimpleInputEffHandler
  { handleISimple   :: forall a. Monad m
              => s -> op a -> (s, a)
  , parallelISimple :: forall ix. Monad m
              => s -> (Table ix s, s)
  }

handleInputSimple :: forall op rest s a
             . SimpleInputEffHandler op (EffComp rest) s
            -> s
            -> EffComp (op `EffCons` rest) a
            -> EffComp rest a
handleInputSimple h@SimpleInputEffHandler{handleISimple, parallelISimple} =
  handleInput InputEffHandler{
    handleI = \s op cont -> uncurry cont (handleISimple s op),
    parallelI = \s iters cont -> let (ss, s') = parallelISimple s in
      iters ss >>= cont s'
  }



data InputOutputEffHandler (op :: EffSig) (m :: * -> *) s (f :: * -> *) = InputOutputEffHandler
  { retIO      :: forall a. s -> a -> f a
  , handleIO   :: forall a b. Monad m
               => s -> op a -> (s -> a -> m (f b)) -> m (f b)
  , parallelIO :: forall a b ix. Monad m
               => s -> (Table ix s -> m (Table ix (f a)))
                    -> (s -> Table ix a -> m (f b))
                    -> m (f b)
  }

handleInputOutput :: forall op rest s f a
                   . InputOutputEffHandler op (EffComp rest) s f
                  -> s
                  -> EffComp (op `EffCons` rest) a
                  -> EffComp rest (f a)
handleInputOutput h@InputOutputEffHandler{retIO, handleIO, parallelIO} s comp = case comp of
    Pure r -> Pure $ retIO s r
    Impure (Effect (Here op)) cont -> handleIO s op (\s a -> rec s $ cont a)
    Impure (Effect (There op)) cont -> Impure (Effect op) (rec s . cont)
    Impure (TraverseTable iters@(Table _)) cont  -- unpack iters to get a proof of IndexSet ix
      -> parallelIO s runIters runCont
      where
        runIters ss = for $ \i -> rec (tableIndex ss i) (tableIndex iters i)
        runCont s a = rec s (cont a)
  where
    rec :: forall b. s -> EffComp (op `EffCons` rest) b -> EffComp rest (f b)
    rec = handleInputOutput h
