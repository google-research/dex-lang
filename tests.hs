import Test.HUnit
import qualified Parser

main = runTestTT $ do
  Parser.tests

