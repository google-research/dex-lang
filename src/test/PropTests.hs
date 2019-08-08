import Test.QuickCheck

import Syntax
import Parser
import PPrint
import Generators ()

prop_print_parse_uexpr :: UTopDecl -> Bool
prop_print_parse_uexpr decl =
  case parseTopDecl (pprint decl) of
    Right decl' | decl == decl' -> True
    _ -> False

main :: IO ()
main = do
  quickCheck prop_print_parse_uexpr
