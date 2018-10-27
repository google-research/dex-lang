import Test.HUnit
import Typer
import qualified Parser as P
import Parser hiding (Expr (..))
import Lower
import Syntax
import Util
import Typer
import Interpreter


typeTestCases =
  [ ("1"                     , IntType)
  , ("1 + 3"                 , IntType)
  , ("lam x: x"              , TypeVar "a" `ArrType` TypeVar "a")
  , ("(lam x: x) 2"          , IntType)
  , ("for i: 1"              , TypeVar "a" `TabType` IntType)
  , ("for i: (for j: 3).i"   , TypeVar "a" `TabType` IntType)
  , ("for i: (iota 3).i"     , IntType `TabType` IntType)
  , ("reduce add 0 (iota 3)" , IntType)
  , ("let x = 1 in x"        , IntType)
  ]

typeErrorTestCases =
  [ ("lam f: f f"   , InfiniteType)
  , ("1 1"          , UnificationError IntType (IntType `ArrType` TypeVar "a"))
  , ("(lam f: (f 1) + f (lam z: z) 2) (lam x: x)" ,
       UnificationError (TypeVar "c" `ArrType` TypeVar "c") IntType )
  ]


parseTestCases =
  [ ("1 + 2"        , P.App (P.App (P.Var "add") (P.Lit 1)) (P.Lit 2))
  , ("for i: 10"    , P.For "i" (P.Lit 10))
  , ("lam x: x"     , P.Lam "x" (P.Var "x"))
  , ("y x"          , P.App (P.Var "y") (P.Var "x"))
  , ("x.i"          , P.Get (P.Var "x") "i")
  , ("f x y"        , P.App (P.App (P.Var "f") (P.Var "x")) (P.Var "y"))
  , ("x.i.j"        , P.Get (P.Get (P.Var "x") "i") "j")
  , ("let x = 1 in x"        , P.Let "x" (P.Lit 1) (P.Var "x"))
  , ("let x = 1; y = 2 in x" , P.Let "x" (P.Lit 1) (P.Let "y" (P.Lit 2) (P.Var "x")))
  , ("for i j: 10"           , P.For "i" (P.For "j" (P.Lit 10)))
  , ("lam x y: x"            , P.Lam "x" (P.Lam "y" (P.Var "x")))
  , ("let f x = x in f"      , P.Let "f" (P.Lam "x" (P.Var "x")) (P.Var "f"))
  , ("let x . i = y in x"    , P.Let "x" (P.For "i" (P.Var "y")) (P.Var "x"))
  , ("let f x y = x in f"    , P.Let "f" (P.Lam "x" (P.Lam "y" (P.Var "x"))) (P.Var "f"))
  , ("let x.i.j = y in x"    , P.Let "x" (P.For "i" (P.For "j" (P.Var "y"))) (P.Var "x"))
  ]


testCase :: (Show a, Eq a) => String -> (String -> a) -> a -> Test
testCase s f target = TestCase $ assertEqual ("   input: " ++ s) target (f s)

gettype :: String -> Either TypeErr Type
gettype s = case parseCommand s of
              Right (EvalExpr p) ->
                case lowerExpr p initVarEnv of
                  Right e -> typeExpr e initTypeEnv
              Left _ -> error "parse error"

parseTests = TestList [testCase s parseCommand (Right (EvalExpr p)) | (s,p) <- parseTestCases]
typeTests  = TestList [testCase s gettype (Right t) | (s,t) <- typeTestCases]
typeErrorTests = TestList [testCase s gettype (Left e) | (s,e) <- typeErrorTestCases]


main = do
  runTestTT $ parseTests
  runTestTT $ typeTests
  runTestTT $ typeErrorTests
