-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module SourceInfo (
  SrcPos, SpanId, SrcPosCtx (..), emptySrcPosCtx, fromPos,
  pattern EmptySrcPosCtx,
  sliceText, SpanTree (..), SpanTreeM (..), SpanPayload, SpanPos,
  evalSpanTree, makeSpanTree, makeEmptySpanTree, makeSpanTreeRec,
  fixSpanPayloads,
  fillTreeAndAddTrivialLeaves
  ) where

import Data.Data
import Data.Hashable
import Data.Char (isSpace)
import Data.List (findIndex)
import Data.Maybe (listToMaybe, maybeToList)
import Data.Store (Store (..))
import qualified Data.Text as T
import GHC.Generics (Generic (..))
import Control.Applicative
import Control.Monad.State.Strict

-- === Core API ===

type SrcPos = (Int, Int)
type SpanId = Int

data SrcPosCtx = SrcPosCtx (Maybe SrcPos) (Maybe SpanId)
  deriving (Show, Eq, Generic, Data, Typeable)
instance Hashable SrcPosCtx
instance Store SrcPosCtx

instance Ord SrcPosCtx where
  compare (SrcPosCtx pos spanId) (SrcPosCtx pos' spanId') =
    case (pos, pos') of
      (Just (l, r), Just (l', r')) -> compare (l, r', spanId) (l', r, spanId')
      (Just _, _) -> GT
      (_, Just _) -> LT
      (_, _) -> compare spanId spanId'

emptySrcPosCtx :: SrcPosCtx
emptySrcPosCtx = SrcPosCtx Nothing Nothing

pattern EmptySrcPosCtx :: SrcPosCtx
pattern EmptySrcPosCtx = SrcPosCtx Nothing Nothing

fromPos :: SrcPos -> SrcPosCtx
fromPos pos = SrcPosCtx (Just pos) Nothing

-- === Span utilities ===

type SpanPayload = (Int, Int, SpanId)
type SpanPos = (Int, Int)

data SpanTree =
  Span SpanPayload [SpanTree] |
  LeafSpan SpanPayload |
  Trivia SpanPos
  deriving (Show, Eq)

newtype SpanTreeM a = SpanTreeM
  { runSpanTree' :: StateT [SpanPayload] Maybe a }
  deriving (Functor, Applicative, Monad, MonadState [SpanPayload], Alternative)

evalSpanTree :: SpanTreeM a -> [SpanPayload] -> Maybe a
evalSpanTree m spans = evalStateT (runSpanTree' m) spans

getNextSpanPayload :: SpanTreeM (Maybe SpanPayload)
getNextSpanPayload = SpanTreeM $ do
  infos <- get
  case infos of
    [] -> return Nothing
    x:xs -> put xs >> return (Just x)

data SpanContained = Contained | NotContained | PartialOverlap
  deriving (Show, Eq)

-- | @contained x y@ returns whether @y@ is contained in @x@.
spanContained :: SpanPayload -> SpanPayload -> SpanContained
spanContained (lpos, rpos, _) (lpos', rpos', _) =
  case (lpos <= lpos', rpos >= rpos') of
    (True, True) -> Contained
    (False, False) -> NotContained
    (_, _) -> if rpos <= lpos'
      then NotContained
      else PartialOverlap

-- | @makeSpanTreeRec x@ returns a @[SpanTree]@ with the children of @x@.
getSpanChildren :: SpanPayload -> SpanTreeM (Maybe [SpanTree])
getSpanChildren root = do
  getNextSpanPayload >>= \case
    Just child -> do
      case spanContained root child of
        -- If `child` is contained in `root`, then we add it as a child.
        Contained -> do
          childTree <- makeSpanTreeRec child
          remainingChildren <- getSpanChildren root
          return $ Just (maybeToList childTree ++ concat (maybeToList remainingChildren))
        NotContained -> do infos <- get; put (child : infos); return $ Just []
        PartialOverlap -> do infos <- get; put (child : infos); return $ Just []
    Nothing -> return $ Just []

-- | @makeSpanTreeRec x@ returns a @SpanTree@ with the @x@ as the root.
makeSpanTreeRec :: SpanPayload -> SpanTreeM (Maybe SpanTree)
makeSpanTreeRec root = do
  children <- getSpanChildren root
  case children of
    Nothing -> return Nothing
    Just [] -> return $ Just (LeafSpan root)
    Just xs -> return $ Just (Span root xs)

makeEmptySpanTree :: [SpanPayload] -> Maybe SpanTree
makeEmptySpanTree [] = Nothing
makeEmptySpanTree (root:children) = join $ evalSpanTree (makeSpanTreeRec root) children

makeSpanTree :: (Show a, IsTrivia a) => [a] -> [SpanPayload] -> Maybe SpanTree
makeSpanTree xs infos = case makeEmptySpanTree infos of
  Nothing -> Nothing
  Just posTree -> Just (fillTreeAndAddTrivialLeaves xs posTree)

slice :: Int -> Int -> [a] -> [a]
slice left right xs = take (right - left) (drop left xs)

sliceText :: Int -> Int -> T.Text -> T.Text
sliceText left right xs = T.take (right - left) (T.drop left xs)

getSpanPos :: SpanTree -> SpanPos
getSpanPos tree = case tree of
  Span (l, r, _) _ -> (l, r)
  LeafSpan (l, r, _) -> (l, r)
  Trivia pos -> pos

fillTrivia :: SpanPayload -> [SpanTree] -> [SpanTree]
fillTrivia (l, r, _) offsets =
  let (before, after) = case offsets of
                [] -> ([], [])
                _ ->
                  let (headL, _) = getSpanPos (head offsets) in
                  let (_, tailR) = getSpanPos (last offsets) in
                  let before' = [Trivia (l, headL) | l /= headL] in
                  let after' = [Trivia (tailR, r) | r /= tailR] in
                  (before', after') in
  let offsets' = before ++ offsets ++ after in
  let pairs = zip offsets' (drop 1 offsets') in
  let unzipped = pairs >>= getOffsetAndTrivia in
  maybeToList (listToMaybe offsets') ++ unzipped
  where getOffsetAndTrivia :: (SpanTree, SpanTree) -> [SpanTree]
        getOffsetAndTrivia (t, t') =
          let (_, r') = endpoints t in
          let (l', _) = endpoints t' in
          let diff = l' - r' in
          if diff == 0 then
            [t']
          else
            [Trivia (r', l'), t']

fixSpanPayloads :: [SpanPayload] -> [SpanPayload]
fixSpanPayloads spans =
  let pairs = zip spans (drop 1 spans) in
  let unzipped = pairs >>= mergeSpans in
  unzipped ++ [last spans]
  where mergeSpans :: (SpanPayload, SpanPayload) -> [SpanPayload]
        mergeSpans (s, s') = case spanContained s s' of
          Contained -> [s]
          NotContained -> [s]
          -- Note: currently, overlapping spans are simply dropped.
          -- Consider replacing with approach that preserves partial span info.
          PartialOverlap -> []

rebalanceTrivia :: Show a => (a -> Bool) -> [a] -> [SpanTree] -> [SpanTree]
rebalanceTrivia trivia xs trees =
  let whitespaceSeparated = trees >>= createTrivia in
  whitespaceSeparated
  where
    createTrivia :: SpanTree -> [SpanTree]
    createTrivia t = case t of
      Span _ _ -> [t]
      LeafSpan _ -> blah
      Trivia _ -> blah
      where blah :: [SpanTree]
            blah =
              let (l, r) = endpoints t in
              let s' = slice l r xs in
              let firstNonTrivia = findIndex (not . trivia) s' in
              let lastNonTrivia = fmap (length s' -) (findIndex (not . trivia) (reverse s')) in
              case (firstNonTrivia, lastNonTrivia) of
                (Just l', Nothing) | l' > 0 -> [Trivia (l, l + l'), shiftTree (l + l', r) t]
                (Nothing, Just r') | r' < length s' -> [shiftTree (l, l + r') t, Trivia (l + r', r)]
                (Just l', Just r') | l' > 0 || r' < length s' ->
                  [Trivia (l, l + l'), shiftTree (l + l', l + r') t, Trivia (l + r', r)]
                (_, _) -> [t]

    --
    shiftTree :: SpanPos -> SpanTree -> SpanTree
    shiftTree (l', r') t = case t of
      Span (_, _, i) children -> Span (l', r', i) children
      LeafSpan (_, _, i) -> LeafSpan (l', r', i)
      Trivia _ -> Trivia (l', r')

endpoints :: SpanTree -> (Int, Int)
endpoints (Span (l, r, _) _) = (l, r)
endpoints (LeafSpan (l, r, _)) = (l, r)
endpoints (Trivia (l, r)) = (l, r)

class IsTrivia a where
  isTrivia :: a -> Bool

instance IsTrivia Char where
  isTrivia = isSpace

-- | Fills a @SpanTree@ with @Trivia@ in span gaps.
fillTreeAndAddTrivialLeaves :: Show a => IsTrivia a => [a] -> SpanTree -> SpanTree
fillTreeAndAddTrivialLeaves xs tree = case tree of
  Span info children ->
    let children' = fillTrivia info children in
    let children'' = rebalanceTrivia isTrivia xs children' in
    let filled = map (fillTreeAndAddTrivialLeaves xs) children'' in
    Span info filled
  LeafSpan _ -> tree
  Trivia _ -> tree
