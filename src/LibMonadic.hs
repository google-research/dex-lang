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
-- parallelizable effectful computation. We only care about parallelism within
-- list constructs.
data EffComp (sig :: EffSig) r where
  -- Return a value without having any effects.
  Pure :: r -> EffComp sig r
  -- Execute an effect.
  Effect :: sig r -> EffComp sig r
  -- Monad API: Compose effects with dependencies.
  Bind :: EffComp sig a -> (a -> EffComp sig b) -> EffComp sig b
  -- Sort-of applicative list traversal construct. We want to maintain the
  -- invariant that we never pattern match on a list, only traverse it in
  -- parallel.
  TraverseList :: [EffComp sig r] -> EffComp sig [r]

-- We can use the normal Haskell instances to build up our computation.
instance Functor (EffComp sig) where
  fmap f c = c `Bind` (Pure . f)

instance Applicative (EffComp sig) where
  pure r = Pure r
  f <*> c = f `Bind` \fv -> c `Bind` \cv -> Pure (fv cv)

instance Monad (EffComp sig) where
  c >>= f = c `Bind` f

-- To expose the table-specific parallelism, we handle "for" separately
for :: [a] -> (a -> EffComp sig b) -> EffComp sig [b]
for xs f = TraverseList (f <$> xs)

-- We also provide a hook to call effects easily.
effect :: HasEff sig union => sig r -> EffComp union r
effect e = Effect $ liftEff e


-- When the computation is itself pure, we can stitch all of the different
-- pieces together.
runPure :: EffComp EffNil r -> r
runPure = \case
  Pure r -> r
  Effect eff -> case eff of {} -- impossible
  TraverseList cs -> map runPure cs
  Bind ca fc -> runPure (fc (runPure ca))

-- A handler allows us to peel off one layer from an effect row, by transforming
-- all effect calls into primitive operations and other effects.

-- Our first handler is fairly simple: it must lower each individual operation
-- into an operation of some other handler higher up the stack.
handleFunc :: forall c sig union ans
        . (forall r. sig r -> EffComp union r)
       -> EffComp (sig `EffCons` union) ans
       -> EffComp union ans
handleFunc handler = \case
    Pure r -> Pure r
    Effect (Here op) -> handler op
    Effect (There op) -> Effect op
    TraverseList cs -> TraverseList (map rec cs)
    Bind ca fc -> Bind (rec ca) (rec . fc)
  where
    rec :: forall t. EffComp (sig `EffCons` union) t -> EffComp union t
    rec = handleFunc handler


-- We don't want to allow full continuation-passing style, because then there's
-- no way to lower `TraverseList` in parallel. However, perhaps we can locally
-- lower each computation in a `TraverseList` and then combine the results.
handleDelimCont :: forall sig c union f s
                 . (forall a b. sig a -> (a -> EffComp union (f b))
                                      -> EffComp union (f b))
                -> (forall b. b -> f b)
                -> EffComp (sig `EffCons` union) s
                -> EffComp union (f s)
handleDelimCont handler ret val = _handleDelimCont handler ret val id

_handleDelimCont :: forall sig c union f s t
                 . (forall a b. sig a -> (a -> EffComp union (f b))
                                      -> EffComp union (f b))
                -> (forall b. b -> f b)
                -> EffComp (sig `EffCons` union) s
                -> (EffComp union (f s) -> EffComp union (f t))
                -> EffComp union (f t)
_handleDelimCont handler ret val cont = case val of
    Pure r -> cont $ Pure $ ret r
    Effect (Here op) -> handler op (cont . Pure . ret)
    Effect (There op) -> cont $ ret <$> Effect op
    TraverseList cs -> undefined
    Bind ca fc -> undefined -- rec ca $ \a -> rec (fc a) $ \f -> _
  where
    rec :: forall u. EffComp (sig `EffCons` union) u
            -> (EffComp union (f u) -> EffComp union (f t))
            -> EffComp union (f t)
    rec = _handleDelimCont handler ret



-- class StraightLineResult (f :: * -> *) where
--   pure :: a -> f a
--   sequenceList :: [f a] -> f [a]
--   sortaBind :: forall m b c. Monad m => m (f b) -> (b -> m (f c)) -> m (f c)

--   -- sequenceListCont :: [f a] -> ([a] -> f b) -> f b
--   sequenceListCont :: Monad m => [f a] -> ([a] -> m (f b)) -> m (f b)

-- handleNew :: forall sig c union f s
--            . StraightLineResult f
--           => (forall a b. sig a -> (a -> EffComp union (f b))
--                                 -> EffComp union (f b))
--           -- -> (forall b. EffComp union (f b) -> (b -> EffComp union (f c))
--           --               -> EffComp union (f c))
--           -> EffComp (sig `EffCons` union) s
--           -> EffComp union (f s)
-- handleNew _ _ = undefined


-- class EffImpl (op :: EffSig) (f :: * -> *) | f -> op where
--   pure :: a -> f a
--   handle  :: Monad m => op a  -> (a   -> m (f b)) -> m (f b)
--   seqList :: Monad m => [f a] -> ([a] -> m (f b)) -> m (f b)
--   openList :: Monad m => [m (f a)] -> m [f a]
  -- handle'  :: Monad m => op [a]  -> ([a]   -> m (f b)) -> m (f b)
  -- SeqListOp :: [f a] -> Op [a]
  -- f a == Int -> a




-- Accum, SoftExcept
class OutputEffImpl (op :: EffSig) (f :: * -> *) | f -> op where
  retO :: a -> f a
  handleO   :: Monad m => op a       -> (a   -> m (f b)) -> m (f b)
  parallelO :: Monad m => [f a] -> ([a] -> m (f b)) -> m (f b)

-- Reader, Random
class InputEffImpl (op :: EffSig) s | s -> op where
  handleI   :: Monad m => s -> op a       -> (s -> a   -> m b) -> m b
  parallelI :: Monad m => s -> [s -> f a] -> (s -> [a] -> m b) -> m b

-- (anything?)
class InputOutputEffImpl (op :: EffSig) s (f :: * -> *) | f -> op s where
  retIO :: s -> a -> f a
  handleIO   :: Monad m => s -> op a       -> (s -> a   -> m (f b)) -> m (f b)
  parallelIO :: Monad m => s -> [s -> f a] -> (s -> [a] -> m (f b)) -> m (f b)

