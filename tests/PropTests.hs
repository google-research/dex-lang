import Test.QuickCheck
import Test.QuickCheck.Random
import System.Exit
import Data.Text.Prettyprint.Doc
import Control.Monad

import Syntax hiding (Result)
import Parser
import PPrint
import Generators ()

prop_print_parse_uexpr :: UTopDecl -> Property
prop_print_parse_uexpr decl = case parseTopDecl (pprintEsc decl) of
  Left e -> counterexample (pprint e) False
  Right decl' -> decl === stripSrcAnnotTopDecl decl'

-- wrapper to make show pretty
data PPWrap a = PPWrap a  deriving (Eq)

instance Pretty a => Show (PPWrap a) where
  show (PPWrap x) = pprintEsc x

instance Arbitrary a => Arbitrary (PPWrap a) where
  arbitrary = liftM PPWrap arbitrary
  shrink (PPWrap x) = map PPWrap (shrink x)

fromPPWrap :: PPWrap a -> a
fromPPWrap (PPWrap x) = x

pprintProp :: (Pretty a, Arbitrary a, Testable prop) => (a -> prop) -> Property
pprintProp f = property (f . fromPPWrap)

args = stdArgs
  { maxSize = 100
  , maxSuccess = 100
  , replay = Just (mkQCGen 0, 0)
  }

main :: IO ()
main = do
  results <- quickCheckWithResult args (pprintProp prop_print_parse_uexpr)
  if isSuccess results
    then return ()
    else exitWith (ExitFailure 1)
