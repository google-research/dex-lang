import Test.HUnit
import Typer
import qualified Parser as P
import Parser hiding (Expr (..), Pat (..))
import Lower
import Record
import Syntax
import Util
import Typer
import Interpreter
import qualified Data.Map.Strict as Map


infixr 1 -->
infixr 2 ==>
(-->) = ArrType
(==>) = TabType
int = BaseType IntType
a = TypeVar 0
b = TypeVar 1

typeTestCases =
  [ ("1"                     , Forall 0 $ int)
  , ("1 + 3"                 , Forall 0 $ int)
  , ("lam x: x"              , Forall 1 $ a --> a)
  , ("(lam x: x) 2"          , Forall 0 $ int)
  , ("for i: 1"              , Forall 1 $ a ==> int)
  , ("for i: (for j: 3).i"   , Forall 1 $ a ==> int)
  , ("for i: (iota 3).i"     , Forall 0 $ int ==> int)
  , ("reduce add 0 (iota 3)" , Forall 0 $ int)
  , ("let x = 1 in x"        , Forall 0 $ int)
  , ("lam x: (x,x)"          , Forall 1 $ a --> RecType (posRecord [a, a]))
  ]

typeErrorTestCases =
  [ ("lam f: f f"   , InfiniteType)
  , ("1 1"          , UnificationError int (int --> TypeVar 0))
  ]

x = P.Var "x"
y = P.Var "y"
f = P.Var "f"

x' = P.VarPat "x"
y' = P.VarPat "y"
f' = P.VarPat "f"

l1 = P.Lit 1
l2 = P.Lit 2

parseTestCases =
  [ ("1 + 2"                 , P.App (P.App (P.Var "add") l1) l2)
  , ("for i: 1"             , P.For "i" l1)
  , ("lam x: x"              , P.Lam x' x)
  , ("y x"                   , P.App y x)
  , ("x.i"                   , P.Get x "i")
  , ("f x y"                 , P.App (P.App f x) y)
  , ("x.i.j"                 , P.Get (P.Get x "i") "j")
  , ("let x = 1 in x"        , P.Let x' l1 x)
  , ("let x = 1; y = 2 in x" , P.Let x' l1 (P.Let y' l2 x))
  , ("for i j: 1"           , P.For "i" (P.For "j" l1))
  , ("lam x y: x"            , P.Lam x' (P.Lam y' x))
  , ("let f x = x in f"      , P.Let f' (P.Lam x' x) f)
  , ("let x . i = y in x"    , P.Let x' (P.For "i" y) x)
  , ("let f x y = x in f"    , P.Let f' (P.Lam x' (P.Lam y' x)) f)
  , ("let x.i.j = y in x"    , P.Let x' (P.For "i" (P.For "j" y)) x)
  , ("(x, y)"                , P.RecCon $ posRecord [x, y])
  , ("()"                    , P.RecCon $ emptyRecord )
  -- , ("lam (x,y): 1"          , P.Lam (P.RecPat [("0", x'), ("1",y')]) l1 )
  ]

type TestVal = (Int, [([Int], Int)])

evalTestCases :: [(String, Val)]
evalTestCases =
  [ ("1 + 2"                              ,  IntVal 3)
  , ("reduce add 0 (iota 4)"              ,  IntVal 6)
  , ("reduce add 0 (for i: (iota 4).i)"   ,  IntVal 6)
  , ("reduce add 0 (for i: (iota 5).i + (iota 4).i)"   ,  IntVal 12)
  , ("reduce add 0 (for i: reduce add 0 (for j: (iota 2).i * (iota 3).j))" ,  IntVal 3)
  , ("(1, 1+2)", RecVal $ posRecord [IntVal 1, IntVal 3])
  ]


testCase :: (Show a, Eq a) => String -> (String -> a) -> a -> Test
testCase s f target = TestCase $ assertEqual ("   input: " ++ s) target (f s)

getParse :: String -> Expr
getParse s = case parseCommand s of
              Right (EvalExpr p) ->
                case lowerExpr p initVarEnv of
                  Right e -> e
              Left _ -> error "parse error"

gettype :: String -> Either TypeErr ClosedType
gettype s = typeExpr (getParse s) initTypeEnv

getVal :: String -> Val
getVal s = evalExpr (getParse s) initValEnv



parseTests = TestList [testCase s parseCommand (Right (EvalExpr p))
                      | (s,p) <- parseTestCases]

evalTests = TestList [testCase s getVal v
                     | (s,v) <- evalTestCases]

typeTests = TestList [testCase s gettype (Right t)
                     | (s,t) <- typeTestCases]

typeErrorTests = TestList [testCase s gettype (Left e)
                          | (s,e) <- typeErrorTestCases]


main = do
  runTestTT $ parseTests
  runTestTT $ typeTests
  runTestTT $ typeErrorTests
  runTestTT $ evalTests
