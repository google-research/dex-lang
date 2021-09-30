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


module TableEffectsSimplerHandlers where

import GHC.TypeLits
import Table
import TableEffects

-- We can build simpler handlers by removing features from our full handler.

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
  , parallelF :: forall ix. KnownNat ix => s -> m (Table ix s, s)
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
    Impure (TraverseTable iters@(UnsafeFromList _ :: Table n b)) cont -> do
      (ss, s') <- parallelF @n s
      result <- for $ \i -> rec (tableIndex ss i) (tableIndex iters i)
      rec s' (cont result)
  where
    rec :: forall b. s -> EffComp (op `EffCons` rest) b -> EffComp rest b
    rec = handleForkState h
