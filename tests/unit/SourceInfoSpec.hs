-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# OPTIONS_GHC -Wno-orphans #-}

module SourceInfoSpec (spec) where

import Data.List
import Data.Text qualified as T
import Text.Blaze.Html.Renderer.String
import Test.Hspec

import RenderHtml
import SourceInfo

--   [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
-- a: ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- b:    ~~~~~~~~~~~~~
-- c:    ~~~~
-- d:             ~~~~
-- e:                      ~~~~~~~

s :: String
s = "def foo : Float -> Float = id"
--   012345678901234567890123456789
--   0         1         2

posTree' :: SpanTree
posTree' =
  Span (0, 1000, 0) [
    -- span(10, 25): "Float -> Float "
    -- Fix 1: change `fillTreeAndAddTrivialLeaves` to move whitespace
    -- Fix 2: change parsing to not include whitespace
    Span (10, 25, 3) [
      LeafSpan (10, 16, 5),
      LeafSpan (19, 25, 7)
    ],
    LeafSpan (27, 29, 9)
  ]

posTreeFilled' :: SpanTree
posTreeFilled' =
  Span (0,1000,0) [
    Trivia (0,0),
    Trivia (0,9),
    Trivia (9,10),
    Span (10,25,3) [
      Trivia (10,10),
      LeafSpan (10,15,5),
      Trivia (15,16),
      Trivia (16,16),
      Trivia (16,18),
      Trivia (18,19),
      Trivia (19,19),
      LeafSpan (19,24,7),
      Trivia (24,25)
    ],
    Trivia (25,25),
    Trivia (25,26),
    Trivia (26,27),
    LeafSpan (27,29,9),
    Trivia (29,1000)
  ]

xs :: String
xs = "0123456789!"

spanInfos :: [SpanPayload]
spanInfos =
  [ (0, 10, 0)
  , (1, 5, 1)
  , (1, 2, 2)
  , (4, 5, 3)
  , (7, 9, 4)
  ]

srcPosCtxs :: [SrcPosCtx]
srcPosCtxs =
  [ SrcPosCtx (Just (0, 10)) (Just 0)
  , SrcPosCtx (Just (1, 5)) (Just 1)
  , SrcPosCtx (Just (1, 2)) (Just 2)
  , SrcPosCtx (Just (4, 5)) (Just 3)
  , SrcPosCtx (Just (7, 9)) (Just 4)
  ]

positionSpanTree :: SpanTree
positionSpanTree =
  Span (0, 10, 0) [
    Trivia (0, 1),
    Span (1, 5, 1) [
      LeafSpan (1, 2, 2),
      LeafSpan (4, 5, 3)
    ],
    LeafSpan (7, 9, 4)
  ]

positionFilledSpanTree :: SpanTree
positionFilledSpanTree =
  Span (0, 10, 0) [
    Trivia (0, 1),
    Span (1, 5, 1) [
      LeafSpan (1, 2, 2),
      Trivia (2, 4),
      LeafSpan (4, 5, 3)
    ],
    Trivia (5, 7),
    LeafSpan (7, 9, 4),
    Trivia (9,10)
  ]

-- Regression tests

-- Note: the parser currently produces overlapping spans (`SrcPos`) for the program below.
overlappingSpansCode :: String
overlappingSpansCode =
  unlines [
    "def foo (i: Int) : Unit =",
    "  def explicitAction (h:Int) : Int = i",
    "  ()"
  ]

overlappingSpans :: [SpanPayload]
overlappingSpans =
  [ (0, 1000, 0),
    (9, 63, 10),
    (9, 10, 4),
    (9, 10, 11),
    (12, 15, 6),
    (19, 24, 8),
    (30, 63, 13),
    (50, 66, 23),
    (50, 51, 17),
    (50, 51, 24),
    (52, 55, 19),
    (59, 63, 21),
    (65, 66, 26),
    (71, 73, 28)
  ]

overlappingSpansTree :: SpanTree
overlappingSpansTree =
  Span
  (0, 1000, 0)
  [ Trivia (0, 9),
    Span
      (9, 63, 10)
      [ Span (9, 10, 4) [LeafSpan (9, 10, 11)],
        Trivia (10, 10),
        Trivia (10, 11),
        Trivia (11, 12),
        LeafSpan (12, 15, 6),
        Trivia (15, 15),
        Trivia (15, 18),
        Trivia (18, 19),
        Trivia (19, 19),
        LeafSpan (19, 23, 8),
        Trivia (23, 24),
        Trivia (24, 30),
        Trivia (30, 30),
        LeafSpan (30, 62, 13),
        Trivia (62, 63)
      ],
    Trivia (63, 50),
    Span
      (50, 66, 23)
      [ Span
          (50, 51, 17)
          [ LeafSpan (50, 51, 24)
          ],
        Trivia (51, 52),
        Trivia (52, 52),
        LeafSpan (52, 54, 19),
        Trivia (54, 55),
        Trivia (55, 59),
        Trivia (59, 59),
        LeafSpan (59, 62, 21),
        Trivia (62, 63),
        Trivia (63, 63),
        Trivia (63, 64),
        Trivia (64, 65),
        LeafSpan (65, 66, 26)
      ],
    Trivia (66, 67),
    Trivia (67, 69),
    Trivia (69, 71),
    LeafSpan (71, 73, 28),
    Trivia (73, 1000)
  ]

renderedHtml :: String
renderedHtml =
  concat [
    "<span class=\"code-span\">0",
    "<span class=\"code-span\">",
    "<span class=\"code-span-leaf\">1</span>",
    "23",
    "<span class=\"code-span-leaf\">4</span>",
    "</span>",
    "56",
    "<span class=\"code-span-leaf\">78</span>",
    "9",
    "</span>"
  ]

spec :: Spec
spec = do
  describe "SrcPosCtxTest" do
    it "sortedSrcPosCtx" do
      sort srcPosCtxs `shouldBe` srcPosCtxs

  describe "SpanTreeTest" do
    it "Float -> Float" do
      -- fillTreeAndAddTrivialLeaves xs positionSpanTree `shouldBe` contentSpanTree
      fillTreeAndAddTrivialLeaves s posTree' `shouldBe` posTreeFilled'

    it "overlapping spans" do
      makeSpanTree overlappingSpansCode overlappingSpans `shouldBe` Just overlappingSpansTree

    it "works" do
      -- fillTreeAndAddTrivialLeaves xs positionSpanTree `shouldBe` contentSpanTree
      fillTreeAndAddTrivialLeaves xs positionSpanTree `shouldBe` positionFilledSpanTree

    -- it "works 2" do
    --   -- runSpanTree (return 1) spanInfos `shouldBe` (1 :: Int)
    --   evalSpanTree (makeSpanTreeRec $ head spanInfos) (tail spanInfos) `shouldBe` Just positionSpanTree

    it "works 3" do
      -- runSpanTree (return 1) spanInfos `shouldBe` (1 :: Int)
      -- makeSpanTree xs spanInfos `shouldBe` Just contentSpanTree
      makeSpanTree xs spanInfos `shouldBe` Just positionFilledSpanTree

    it "renders properly" do
      let htmlText = treeToHtml (T.pack xs) positionFilledSpanTree in
        renderHtml htmlText `shouldBe` renderedHtml
