-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# OPTIONS_GHC -Wno-orphans #-}

module RawNameSpec (spec) where

import Control.Monad
import Data.Char
import Test.Hspec
import Test.QuickCheck
import RawName qualified as R

newtype RawNameMap = RMap (R.RawNameMap ())
                     deriving (Show)

instance Arbitrary RawNameMap where
  arbitrary = do
    s <- getSize
    RMap . R.fromList <$> (replicateM s $ (,()) <$> arbitrary)

instance Arbitrary R.NameHint where
  arbitrary = do
    arbitrary >>= \case
      True  -> R.getNameHint . fromStringNameHint <$> arbitrary
      False -> return R.noHint  -- TODO: Generate more interesting non-string names

instance Arbitrary R.RawName where
  arbitrary = R.rawNameFromHint <$> arbitrary

newtype StringNameHint = StringNameHint { fromStringNameHint :: String }

instance Show StringNameHint where
  show (StringNameHint s) = s

instance Arbitrary StringNameHint where
  arbitrary = StringNameHint <$> do
    s <- chooseInt (1, 7)
    replicateM s $ arbitrary `suchThat` isNiceAscii

isNiceAscii :: Char -> Bool
isNiceAscii h = isAsciiLower h || isAsciiUpper h || isDigit h

spec :: Spec
spec = do
  describe "RawName" do
    it "generates a fresh name" do
      property \hint (RMap m) -> do
        let name = R.freshRawName hint m
        not $ name `R.member` m

    it "repeatedly generates fresh names from the same hint" do
      property \hint (RMap initM) -> do
        let n = 512
        let step = \(m, ok) () ->
                     let name = R.freshRawName hint m in
                     (R.insert name () m, ok && not (name `R.member` m))
        snd $ foldl step (initM, True) (replicate n ())

    it "string names are in a bijection with short strings" do
      property \(StringNameHint s) -> do
        let s' = show (R.rawNameFromHint (R.getNameHint s))
        counterexample s' $ s == s'

    it "string names with non-zero counters print correctly" do
      property \(StringNameHint s) -> do
        let hint = R.getNameHint s
        let n = R.rawNameFromHint hint
        let scope = R.singleton n ()
        show (R.freshRawName hint scope) == s ++ ".1"
