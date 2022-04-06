module RawNameSpec (spec) where

import Control.Monad
import Data.Char
import Test.Hspec
import Test.QuickCheck
import Debug.Trace
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

shortStr :: String -> String
shortStr = take 7

spec :: Spec
spec = do
  describe "RawName" do
    it "generates a fresh name" do
      property \hint (RMap m) -> do
        let name = R.freshRawName hint m
        label (show name) $ not $ name `R.member` m

    it "repeatedly generates fresh names from the same hint" do
      property \hint (RMap initM) -> do
        let n = 512
        let step = \(m, ok) h ->
                     let n = traceShowId $ R.freshRawName hint m in
                     (R.singleton n () <> m, ok && not (n `R.member` m))
        snd $ foldl step (initM, True) (replicate n hint)

    it "string names are in bijection with short strings" do
      property \(StringNameHint s) -> do
        let s' = show (R.rawNameFromHint (R.getNameHint s))
        counterexample s' $ ("s" ++ s ++ "0") == s'
