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

module Lib
    () where

import Data.Kind
import Data.Functor
import Control.Applicative
import Control.Monad

-- HIGH LEVEL GOALS: This file is meant as an exploration of the objects we
-- might want to reason about for parallel effects. It is intentionally not at
-- all supposed to lead to an efficient implementations. The focus is on setting
-- up types and reasoning about the constraints those types impose. As such,

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
-- parallelizable effectful computation. This data type will be an applicative
-- functor, but may or may not be a monad unless we allow it. It's roughly
-- based on the free monad / free applicative: it does nothing other than hold
-- all of the different parts of the computation in a data structure. We will
-- have to interpret this later to actually compute a result.
data BindAllowed = WithBind | NoBind
data EffComp (c :: BindAllowed) (sig :: EffSig) r where
  -- Return a value without having any effects.
  Pure :: r -> EffComp c sig r
  -- Execute an effect.
  Effect :: sig r -> EffComp c sig r
  -- Functor API: Apply a function to the result of a computation.
  Fmap :: (a -> b) -> EffComp c sig a -> EffComp c sig b
  -- Applicative API: Compose effects without dependencies.
  Ap :: EffComp c sig (a -> b) -> EffComp c sig a -> EffComp c sig b
  -- We also implement a special handler for "for" constructs (maybe not
  -- strictly necessary since it can be written in terms of Ap, but maybe easier
  -- to parallelize)
  TraverseList :: [EffComp c sig r] -> EffComp c sig [r]
  -- (!) Monad API: Compose effects with dependencies.
  -- Only allowed if c == WithBind
  Bind :: EffComp WithBind sig a -> (a -> EffComp WithBind sig b)
       -> EffComp WithBind sig b

-- We can use the normal Haskell instances to build up our computation.
instance Functor (EffComp c sig) where
  fmap f c = Fmap f c

instance Applicative (EffComp c sig) where
  pure r = Pure r
  f <*> c = f `Ap` c

instance Monad (EffComp WithBind sig) where
  c >>= f = c `Bind` f

-- To expose the table-specific parallelism, we handle "for" separately
for :: [a] -> (a -> EffComp c sig b) -> EffComp c sig [b]
for xs f = TraverseList (f <$> xs)

-- We also provide a hook to call effects easily.
effect :: HasEff sig union => sig r -> EffComp c union r
effect e = Effect $ liftEff e


-- When the computation is itself pure, we can stitch all of the different
-- pieces together.
runPure :: EffComp c EffNil r -> r
runPure = \case
  Pure r -> r
  Effect eff -> case eff of {} -- impossible
  Fmap f cr -> f $ runPure cr
  Ap cf cr -> runPure cf $ runPure cr
  TraverseList cs -> map runPure cs
  Bind ca fc -> runPure (fc (runPure ca))


-- A handler allows us to peel off one layer from an effect row, by transforming
-- all effect calls into primitive operations and other effects.

-- Our first handler is fairly simple: it must lower each individual operation
-- into an operation of some other handler higher up the stack.
handleFunc :: forall c sig union ans
        . (forall r. sig r -> EffComp c union r)
       -> EffComp c (sig `EffCons` union) ans
       -> EffComp c union ans
handleFunc handler = \case
    Pure r -> Pure r
    Effect (Here op) -> handler op
    Effect (There op) -> Effect op
    Fmap f cr -> Fmap f (rec cr)
    Ap cf cr -> Ap (rec cf) (rec cr)
    TraverseList cs -> TraverseList (map rec cs)
    Bind ca fc -> Bind (rec ca) (rec . fc)
  where
    rec :: forall t. EffComp c (sig `EffCons` union) t -> EffComp c union t
    rec = handleFunc handler



-- Our next handler would more powerful: it gets the continuation of the full
-- computation and can do whatever it wants with it. However, this is only
-- possible if you serialize the computation, because the continuation you get
-- passed represents the whole computation!
-- (Interestingly, this implementation works regardless of whether the user
-- code used bind or not. So this implementation is probably "unsafe" from the
-- perspective of parallelism; it breaks the implicit parallelism guarantee.
-- Although, interestingly, if the user code doesn't use bind, we never actually
-- store a continuation anywhere! So by the time we exit `handleCont` we've
-- essentially desugared one applicative computation into another.
handleCont :: forall c sig union ans
        . (forall r. sig r -> (r -> EffComp c union ans) -> EffComp c union ans)
       -> EffComp c (sig `EffCons` union) ans
       -> EffComp c union ans
handleCont handler v = _handleCont handler v id

_handleCont :: forall c sig union r s ans
             . (forall r. sig r -> (r -> EffComp c union ans) -> EffComp c union ans)
            -> EffComp c (sig `EffCons` union) s
            -> (EffComp c union s -> EffComp c union ans)
            -> EffComp c union ans
_handleCont handler val cont = case val of
    Pure r -> cont $ Pure r
    Effect (Here op) -> handler op (cont . Pure)
    Effect (There op) -> cont $ Effect op
    Fmap f cr -> rec cr (cont . Fmap f)
    -- (!) Serial dependencies due to continuation chaining!
    Ap cf cr -> rec cf $ \f -> rec cr $ \r -> cont $ Ap f r
    -- (!) Serial dependencies that also break TraverseList closure.
    TraverseList cs -> case cs of
      [] -> cont $ Pure []
      c:rest -> rec c $ \v ->
        rec (TraverseList rest) $ \vs ->
          cont $ Ap (Fmap (:) v) vs
    Bind ca fc -> rec ca $ \a -> Bind a $ \x -> rec (fc x) cont
  where
    rec :: forall t. EffComp c (sig `EffCons` union) t
            -> (EffComp c union t -> EffComp c union ans)
            -> EffComp c union ans
    rec = _handleCont handler  -- Couldn't match type ‘t’ with ‘ans’


-- New goal: Allow monadic structure. However, ensure that TraverseList always
-- lowers back to TraverseList, allowing us to execute it in parallel?
-- One attempt: Sub-continuations with a functor type.
handleDelimCont :: forall sig c union f s
                 . (forall a b. sig a -> (a -> EffComp c union (f b))
                                      -> EffComp c union (f b))
                -> (forall b. b -> f b)
                -> EffComp c (sig `EffCons` union) s
                -> EffComp c union (f s)
handleDelimCont handler ret val = _handleDelimCont handler ret val id

_handleDelimCont :: forall sig c union f s t
                 . (forall a b. sig a -> (a -> EffComp c union (f b))
                                      -> EffComp c union (f b))
                -> (forall b. b -> f b)
                -> EffComp c (sig `EffCons` union) s
                -> (EffComp c union (f s) -> EffComp c union (f t))
                -> EffComp c union (f t)
_handleDelimCont handler ret val cont = case val of
    Pure r -> cont $ Pure $ ret r
    Effect (Here op) -> handler op (cont . Pure . ret)
    Effect (There op) -> cont $ Fmap ret $ Effect op
    Fmap f cr -> undefined -- stuck: not a good way of representing this
    Ap cf cr -> undefined
    TraverseList cs -> undefined
    Bind ca fc -> undefined
  where
    rec :: forall u. EffComp c (sig `EffCons` union) u
            -> (EffComp c union (f u) -> EffComp c union (f t))
            -> EffComp c union (f t)
    rec = _handleDelimCont handler ret
