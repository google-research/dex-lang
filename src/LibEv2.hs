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

module LibEv2
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
type HandlerSig = EffContext -> (* -> *) -> *

-- An effect context is a type-level list of handler signatures.
data EffContext = EffNil | EffCons HandlerSig EffContext

-- EffComp (c :: BindAllowed) (e :: EffContext) ans
-- is the type of a computation that produces an answer `ans` in a context `e`
-- and may or may not use bind.
-- (defined later, mutually recursive defn)

-- An Operation is a data type whose values are effect handlers.
data Op a b (level :: BindAllowed) (ctx :: EffContext) (f :: * -> *) where
  -- Return a constant value.
  Value :: a -> Op () a level ctx ans
  -- Run a function.
  Function :: (a -> EffComp level ctx b) -> Op a b level ctx ans
  -- Continuation-passing style.
  OpWithCont :: (forall c. a -> (b -> EffComp level ctx (f c)) -> EffComp level ctx (f c))
             -> Op a b level ctx f


-- Some example handler signatures.
data State a level ctx f = State { get :: Op () a level ctx f
                                   , put :: Op a () level ctx f }

data PrefixScan a level ctx f = PrefixScan { append        :: Op () a level ctx f
                                             , currentPrefix :: Op a () level ctx f }

newtype Except a level ctx f = Except { throw  :: forall b. Op a b level ctx f }


-- Given the above, we can construct a data type representing the computation
data EffComp (level :: BindAllowed) (ctx :: EffContext) r where
  ----------------
  -- EFFECT API --
  ----------------
  -- Execute a top-level handled effect.
  PerformTop :: (h hs f -> Op a b level hs f)
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
handler :: forall h level e f ans
         . Functor f
        => h e f
        -> (forall a. a -> f a)
        -> EffComp level (h `EffCons` e) (f ans)
        -> EffComp level e (f ans)
handler h ret comp = case comp of
    PerformTop fun args -> undefined -- todo
    Masked comp -> comp
    Pure r -> Pure r
    -- Fmap f cr -> Fmap _ (rec $ fmap ret cr)  -- requires bind??? where did that come from
    -- Ap cf cr -> Ap (rec cf) (rec cr)
    -- TraverseList cs -> TraverseList (map rec cs)
    -- Bind ca fc -> Bind (rec ca) (rec . fc)
  where
    -- rec :: EffComp level (h `EffCons` e) ans -> EffComp level e ans
    rec :: forall ans'. EffComp level (h `EffCons` e) (f ans') -> EffComp level e (f ans')
    -- rec = handler h
    rec = undefined
    -- Still broken: we don't always have intermediate results of the functor type

