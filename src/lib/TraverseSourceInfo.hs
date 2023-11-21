-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module TraverseSourceInfo (HasSourceInfo, gatherSourceInfo, addSpanIds) where

import qualified Data.ByteString as BS
import Control.Monad.State
import Control.Monad.Writer
import GHC.Generics
import GHC.Int
import GHC.Word

import Occurrence qualified as Occ
import SourceInfo
import Types.OpNames qualified as P
import Types.Primitives
import Types.Source

class HasSourceInfo a where
  traverseSourceInfo :: Applicative m => (SrcPosCtx -> m SrcPosCtx) -> a -> m a

  default traverseSourceInfo :: (Applicative m, Generic a, HasSourceInfo (Rep a Any)) => (SrcPosCtx -> m SrcPosCtx) -> a -> m a
  traverseSourceInfo f x = to <$> traverseSourceInfo f (from x :: Rep a Any)

tc :: HasSourceInfo a => Applicative m => (SrcPosCtx -> m SrcPosCtx) -> a -> m a
tc = traverseSourceInfo

instance HasSourceInfo (V1 p) where
  traverseSourceInfo _ x = pure x

instance HasSourceInfo (U1 p) where
  traverseSourceInfo _ x = pure x

instance (HasSourceInfo c) => HasSourceInfo (K1 i c p) where
  traverseSourceInfo f (K1 x) = K1 <$> traverseSourceInfo f x

instance HasSourceInfo (f p) => HasSourceInfo (M1 i c f p) where
  traverseSourceInfo f (M1 x) = M1 <$> traverseSourceInfo f x

instance (HasSourceInfo (a p), HasSourceInfo (b p)) => HasSourceInfo ((a :+: b) p) where
  traverseSourceInfo f (L1 x) = L1 <$> traverseSourceInfo f x
  traverseSourceInfo f (R1 x) = R1 <$> traverseSourceInfo f x

instance (HasSourceInfo (a p), HasSourceInfo (b p)) => HasSourceInfo ((a :*: b) p) where
  traverseSourceInfo f (a :*: b) = (:*:) <$> traverseSourceInfo f a <*> traverseSourceInfo f b

instance HasSourceInfo P.TC
instance HasSourceInfo P.Con
instance HasSourceInfo P.MemOp
instance HasSourceInfo P.VectorOp
instance HasSourceInfo P.MiscOp
instance HasSourceInfo PrimName
instance HasSourceInfo UnOp
instance HasSourceInfo BinOp
instance HasSourceInfo CmpOp
instance HasSourceInfo BaseType
instance HasSourceInfo ScalarBaseType
instance HasSourceInfo Device

instance (HasSourceInfo a, HasSourceInfo b) => HasSourceInfo (a, b)
instance (HasSourceInfo a, HasSourceInfo b, HasSourceInfo c) => HasSourceInfo (a, b, c)
instance (HasSourceInfo a, HasSourceInfo b) => HasSourceInfo (Either a b)
instance HasSourceInfo a => HasSourceInfo [a]
instance HasSourceInfo a => HasSourceInfo (Maybe a)

instance HasSourceInfo Occ.Count
instance HasSourceInfo Occ.UsageInfo
instance HasSourceInfo LetAnn
instance HasSourceInfo UResumePolicy
instance HasSourceInfo CInstanceDef
instance HasSourceInfo CDerivingDef
instance HasSourceInfo CTopDecl'

instance HasSourceInfo AppExplicitness
instance HasSourceInfo CDef
instance HasSourceInfo CSDecl'
instance HasSourceInfo CSBlock
instance HasSourceInfo ForKind
instance HasSourceInfo Group'

instance HasSourceInfo Bin'

instance HasSourceInfo a => HasSourceInfo (WithSrc a) where
  traverseSourceInfo f (WithSrc pos x) = WithSrc <$> f pos <*> tc f x

instance HasSourceInfo () where
  traverseSourceInfo _ x = pure x
instance HasSourceInfo Char where
  traverseSourceInfo _ x = pure x
instance HasSourceInfo Int where
  traverseSourceInfo _ x = pure x
instance HasSourceInfo Int32 where
  traverseSourceInfo _ x = pure x
instance HasSourceInfo Int64 where
  traverseSourceInfo _ x = pure x
instance HasSourceInfo Word8 where
  traverseSourceInfo _ x = pure x
instance HasSourceInfo Word16 where
  traverseSourceInfo _ x = pure x
instance HasSourceInfo Word32 where
  traverseSourceInfo _ x = pure x
instance HasSourceInfo Word64 where
  traverseSourceInfo _ x = pure x
instance HasSourceInfo Float where
  traverseSourceInfo _ x = pure x
instance HasSourceInfo Double where
  traverseSourceInfo _ x = pure x
instance HasSourceInfo BS.ByteString where
  traverseSourceInfo _ x = pure x

-- The real base case.
instance HasSourceInfo SrcPosCtx where
  traverseSourceInfo f x = f x

gatherSourceInfo :: (HasSourceInfo a) => a -> [SrcPosCtx]
gatherSourceInfo x = execWriter (tc (\(ctx :: SrcPosCtx) -> tell [ctx] >> return ctx) x)

addSpanIds :: (HasSourceInfo a) => a -> a
addSpanIds x = evalState (tc f x) 0
  where f (SrcPosCtx maybeSrcPos _) = do
          currentId <- get
          put (currentId + 1)
          return (SrcPosCtx maybeSrcPos (Just currentId))
