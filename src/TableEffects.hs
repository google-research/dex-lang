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


-- Hack to let us reason about dex-style static tables in Haskell.
data Table a b where
  Table :: IndexSet a => (a -> b) -> Table a b

deriving instance Functor (Table a)

class IndexSet a where
  size :: Integer
  iota :: Table a a
  fromOrdinal :: Integer -> a
  ordinal :: a -> Integer

newtype Fin (n :: Nat) = UnsafeFromOrdinal Integer deriving (Eq, Ord, Show)

instance KnownNat n => IndexSet (Fin n) where
  size = natVal (Proxy @n)
  iota = Table id
  fromOrdinal = UnsafeFromOrdinal 
  ordinal (UnsafeFromOrdinal i) = i

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
-- parallelized.

-- First, we consider the simplest type of handler, which has no state and also
-- can't change the result type. This could support a Reader, for instance.
-- This is fairly limited in expressive power, it's basically just a function
-- definition. (But it's allowed to invoke other effects in the stack.)
newtype BasicEffHandler (op :: EffSig) (m :: * -> *) = BasicEffHandler
  { handleB :: forall a. op a -> m a
  }

handleBasic :: forall op rest a
              . BasicEffHandler op (EffComp rest)
             -> EffComp (op `EffCons` rest) a
             -> EffComp rest a
handleBasic h@BasicEffHandler{handleB} comp = case comp of
    Pure r -> Pure r
    Impure (Effect (Here op)) cont -> handleB op >>= (rec . cont)
    Impure (Effect (There op)) cont -> Impure (Effect op) (rec . cont)
    Impure (TraverseTable iters) cont -> 
      Impure (TraverseTable $ fmap rec iters) (rec . cont)
  where
    rec :: forall b. EffComp (op `EffCons` rest) b -> EffComp rest b
    rec = handleBasic h


-- Next, we consider a type of effect that can change the output type, but does
-- not have any state.
-- We can write this in delimited continuation passing style. Each handler gets
-- access to the continuation up to some loop boundary, but with an unknown
-- result type. The only control we give is that the handler can modify the
-- return type with a handler-controlled higher-order datatype.
-- Note that, in parallelize, we assume the work has already been done before
-- control enters `parallelR`. So nothing `parallelR` can do will result in
-- serializing those computations. If we restrict the primitives as well, we
-- can ensure that `parallelR` itself runs in `log(n)` time.
data WithRetEffHandler (op :: EffSig) (m :: * -> *) (f :: * -> *) = WithRetEffHandler
  { retR      :: forall a. a -> m (f a)
  , handleR   ::
      forall a b.    op a           -> (a          -> m (f b)) -> m (f b)
  , parallelR ::
      forall a b ix. Table ix (f a) -> (Table ix a -> m (f b)) -> m (f b)
  }

handleWithRet :: forall op rest f a
               . WithRetEffHandler op (EffComp rest) f
              -> EffComp (op `EffCons` rest) a
              -> EffComp rest (f a)
handleWithRet h@WithRetEffHandler{retR, handleR, parallelR} comp = case comp of
    Pure r -> retR r
    Impure (Effect (Here op)) cont -> handleR op (rec . cont)
    Impure (Effect (There op)) cont -> Impure (Effect op) (rec . cont)
    Impure (TraverseTable iters) cont -> 
      Impure (TraverseTable $ fmap rec iters) $ \iterResults ->
        parallelR iterResults (rec . cont)
  where
    rec :: forall b. EffComp (op `EffCons` rest) b -> EffComp rest (f b)
    rec = handleWithRet h

-- Next, we consider a type of handler that is stateful, but can't change the
-- return type. We also require that the state is "forkable": state may be
-- influenced by list index, but cannot be influenced by the actual computation
-- in previous iterations. (PRNGKey is the typical example, and Accum also makes
-- some use of this. Are there others?)
data ForkStateEffHandler (op :: EffSig) (m :: * -> *) s = ForkStateEffHandler
  { handleF   :: forall a. s -> op a -> m (s, a)
  , parallelF :: forall ix. IndexSet ix => s -> m (Table ix s, s)
  }

handleForkState :: forall op rest s a
             . ForkStateEffHandler op (EffComp rest) s
            -> s
            -> EffComp (op `EffCons` rest) a
            -> EffComp rest a
handleForkState h@ForkStateEffHandler{handleF, parallelF}
                  s comp =
  case comp of
    Pure r -> Pure r
    Impure (Effect (Here op)) cont -> do
      (s, a) <- handleF s op
      rec s (cont a)
    Impure (Effect (There op)) cont -> Impure (Effect op) (rec s . cont)
    Impure (TraverseTable iters@(Table _)) cont -> do
      (ss, s') <- parallelF s
      result <- for $ \i -> rec (tableIndex ss i) (tableIndex iters i)
      rec s' (cont result)
  where
    rec :: forall b. s -> EffComp (op `EffCons` rest) b -> EffComp rest b
    rec = handleForkState h

-- Finally, we can combine the two into a handler that can maintain a forkable
-- state as well as modify the output type. Note that even though it gets to
-- modify things both before and after the loop runs, it has no  way to sequence
-- the loop iteration computations, since we "hide" the actual
-- work in the (Table ix s -> m (Table ix (f a))) argument.
data ForkStateWithRetEffHandler (op :: EffSig) (m :: * -> *) s (f :: * -> *) = ForkStateWithRetEffHandler
  { retFR      :: forall a.      s -> a -> m (f a)
  , handleFR   :: forall a b.    s -> op a -> (s -> a -> m (f b)) -> m (f b)
  , parallelFR :: forall a b ix. IndexSet ix
                                  => s
                                  -> (Table ix s -> m (Table ix (f a)))
                                  -> (s -> Table ix a -> m (f b))
                                  -> m (f b)
  }

handleForkStateWithRet :: forall op rest s f a
                        . ForkStateWithRetEffHandler op (EffComp rest) s f
                       -> s
                       -> EffComp (op `EffCons` rest) a
                       -> EffComp rest (f a)
handleForkStateWithRet h@ForkStateWithRetEffHandler{retFR, handleFR, parallelFR} s comp = case comp of
    Pure r -> retFR s r
    Impure (Effect (Here op)) cont -> handleFR s op (\s a -> rec s $ cont a)
    Impure (Effect (There op)) cont -> Impure (Effect op) (rec s . cont)
    Impure (TraverseTable iters@(Table _)) cont  -- unpack iters to get a proof of IndexSet ix
      -> parallelFR s runIters runCont
      where
        runIters ss = for $ \i -> rec (tableIndex ss i) (tableIndex iters i)
        runCont s a = rec s (cont a)
  where
    rec :: forall b. s -> EffComp (op `EffCons` rest) b -> EffComp rest (f b)
    rec = handleForkStateWithRet h

