import Test.QuickCheck
import System.Exit
import Data.Text.Prettyprint.Doc
import Control.Monad

import Syntax hiding (Result)
import Parser
import PPrint
import Generators ()

prop_print_parse_uexpr :: UTopDecl -> Property
prop_print_parse_uexpr decl =
  case parseTopDecl (pprint decl) of
    Left e -> counterexample (pprint e) False
    Right decl' | decl == decl' -> property True

-- wrapper to make show pretty
data PPWrap a = PPWrap a  deriving (Eq)

instance Pretty a => Show (PPWrap a) where
  show (PPWrap x) = pprint x

instance Arbitrary a => Arbitrary (PPWrap a) where
  arbitrary = liftM PPWrap arbitrary

fromPPWrap :: PPWrap a -> a
fromPPWrap (PPWrap x) = x

pprintProp :: (Pretty a, Arbitrary a, Testable prop) => (a -> prop) -> Property
pprintProp f = property (f . fromPPWrap)

args = stdArgs
  { maxSize = 100
  , maxSuccess = 100
  }

success :: Result -> Bool
success result = case result of
  Success {} -> True
  _ -> False

main :: IO ()
main = do
  results <- quickCheckWithResult args (pprintProp prop_print_parse_uexpr)
  if success results
    then return ()
    else exitWith (ExitFailure 1)
