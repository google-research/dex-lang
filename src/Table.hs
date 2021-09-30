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

module Table where

import Data.Kind
import Data.Foldable
import Data.Proxy
import GHC.TypeLits
import Data.Traversable (Traversable)

data Table (n :: Nat) a where
  UnsafeFromList :: forall n a. KnownNat n => [a] -> Table n a

deriving instance Functor (Table n)
deriving instance Foldable (Table n)
deriving instance Show a => Show (Table n a)

data SomeTable a = forall n. KnownNat n => SomeTable (Table n a)

someTableFromList :: [a] -> SomeTable a
someTableFromList lst = case someNatVal $ fromIntegral (length lst) of
  Just (SomeNat (_ :: Proxy n)) -> SomeTable (UnsafeFromList @n lst)
  Nothing -> error "impossible"

iota :: forall n. KnownNat n => Table n Int
iota = let nv = fromIntegral $ natVal (Proxy @n)
       in UnsafeFromList @n [0 .. nv - 1]

-- unsafe for convenience, just like normal lists
tableIndex :: Table n a -> Int -> a
tableIndex tab i = toList tab !! i

-- Pure table constructor
purefor :: KnownNat n => (Int -> a) -> Table n a
purefor f = f <$> iota
