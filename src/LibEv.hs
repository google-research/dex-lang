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

module LibEv
    () where

import Data.Kind
import Data.Functor
import Control.Applicative
import Control.Monad

-- HIGH LEVEL GOALS: This file is meant as an exploration of the objects we
-- might want to reason about for parallel effects. It is intentionally not at
-- all supposed to lead to an efficient implementations. The focus is on setting
-- up types and reasoning about the constraints those types impose. As such,

-- Whether or not we are allowed to do a monadic bind.
data BindAllowed = WithBind | NoBind

-- A handler signature `h : Handler` is a type such that `h e ans` contains
-- functions that handle a type of effect in context `e` with output type `ans`
type HandlerSig = EffContext -> * -> *

-- An effect context is a type-level list of handler signatures.
data EffContext = EffNil | EffCons HandlerSig EffContext

-- EffComp (c :: BindAllowed) (e :: EffContext) ans
-- is the type of a computation that produces an answer `ans` in a context `e`
-- and may or may not use bind.
-- (defined later, mutually recursive defn)

-- An Operation is a data type whose values are effect handlers.
data Op a b (level :: BindAllowed) (ctx :: EffContext) ans where
  -- Return a constant value.
  Value :: a -> Op () a level ctx ans
  -- Run a function.
  Function :: (a -> EffComp level ctx b) -> Op a b level ctx ans
  -- Continuation-passing style.
  OpWithCont :: (a -> (b -> EffComp level ctx ans) -> EffComp level ctx ans)
             -> Op a b level ctx ans


-- Some example handler signatures.
data State a level ctx ans = State { get :: Op () a level ctx ans
                                   , put :: Op a () level ctx ans }

data PrefixScan a level ctx ans = PrefixScan { append        :: Op () a level ctx ans
                                             , currentPrefix :: Op a () level ctx ans }

newtype Except a level ctx ans = Except { throw  :: forall b. Op a b level ctx ans }

-- Given the above, we can construct a data type representing the computation
data EffComp (level :: BindAllowed) (ctx :: EffContext) r where
  ----------------
  -- EFFECT API --
  ----------------
  -- Execute a top-level handled effect.
  PerformTop :: (h hs ans -> Op a b level hs ans)
             -> a -> EffComp level (h `EffCons` hs) b
  -- Execute a different level of effect.
  Masked :: EffComp level hs b -> EffComp level (h `EffCons` hs) b

  --------------------
  -- SEQUENCING API --
  --------------------
  -- Return a value without having any effects.
  Pure :: r -> EffComp c ctx r
  -- Functor API: Apply a function to the result of a computation.
  Fmap :: (a -> b) -> EffComp c ctx a -> EffComp c ctx b
  -- Applicative API: Compose effects without dependencies.
  Ap :: EffComp c ctx (a -> b) -> EffComp c ctx a -> EffComp c ctx b
  -- We also implement a special handler for "for" constructs (maybe not
  -- strictly necessary since it can be written in terms of Ap, but maybe easier
  -- to parallelize)
  TraverseList :: [EffComp c ctx r] -> EffComp c ctx [r]
  -- (!) Monad API: Compose effects with dependencies.
  -- Only allowed if c == WithBind
  Bind :: EffComp WithBind ctx a -> (a -> EffComp WithBind ctx b)
       -> EffComp WithBind ctx b


-- If we don't know the order, we can just impose restrictions with typeclasses.
-- The HasEff constraint ensures we can lift an operation into the union type,
-- no matter what the union type ends up being.
class HasEff (h :: HandlerSig) (ctx :: EffContext) where
  perform :: (forall ctx' ans. h ctx' ans -> Op a b level ctx' ans)
          -> a -> EffComp level ctx b

instance HasEff h (h `EffCons` rest) where
  perform = PerformTop

instance {--OVERLAPPING--} HasEff h rest
    => HasEff h (other `EffCons` rest) where
  perform f a = Masked (perform f a)



-- We can use the normal Haskell instances to build up our computation.
instance Functor (EffComp c ctx) where
  fmap f c = Fmap f c

instance Applicative (EffComp c ctx) where
  pure r = Pure r
  f <*> c = f `Ap` c

instance Monad (EffComp WithBind ctx) where
  c >>= f = c `Bind` f

-- To expose the table-specific parallelism, we handle "for" separately
for :: [a] -> (a -> EffComp c ctx b) -> EffComp c ctx [b]
for xs f = TraverseList (f <$> xs)


-- When the computation is itself pure, we can stitch all of the different
-- pieces together.
runPure :: EffComp c EffNil r -> r
runPure = \case
  Pure r -> r
  Fmap f cr -> f $ runPure cr
  Ap cf cr -> runPure cf $ runPure cr
  TraverseList cs -> map runPure cs
  Bind ca fc -> runPure (fc (runPure ca))


-- A handler allows us to peel off one layer from an effect row, by transforming
-- all effect calls into primitive operations and other effects.
handler :: forall h level e ans
         . h e ans
        -> EffComp level (h `EffCons` e) ans
        -> EffComp level e ans
handler h comp = case comp of
    PerformTop fun args -> undefined -- todo
    Masked comp -> comp
    Pure r -> Pure r
    Fmap f cr -> Fmap f (rec cr)
    Ap cf cr -> Ap (rec cf) (rec cr)
    TraverseList cs -> TraverseList (map rec cs)
    Bind ca fc -> Bind (rec ca) (rec . fc)
  where
    -- rec :: EffComp level (h `EffCons` e) ans -> EffComp level e ans
    rec :: forall t. EffComp level (h `EffCons` e) t -> EffComp level e t
    -- rec = handler h
    rec = undefined
    -- Problem: This doesn't work with the right level of polymorphism, because
    -- the functor and applicative combinators might change the result type.
    -- So we either need to:
    --  - modify the EffComp type to only refer to things with the right output
    --    type
    --  - modify OpWithCont to not specialize on the result type, somehow
    --  - add some short circuit machinery so that things work out whether we
    --    call the continuation or not?


{-
Why does OpWithCont need to specialize on the answer type, anyway? Well, it's
because we want to be able to short circuit by not calling the continuation,
and instead just return a result.

That's sort of a tricky concept for parallelism, though, because "not calling
the continuation" means you could exit out halfway through a for loop.

We still want to give the handler *some* control over the return value of the
full computation, though, don't we? It doesn't have to be the same as the return
value of the original computation; in fact it probably isn't.

Can we say that it's always a functor type? E.g. the handler gets to choose a
functor, but doesn't get to choose the value of the thing in the functor?

But maybe calling things with continuation is broken anyway?
-}