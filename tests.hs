import Test.HUnit hiding (Testable)
import Test.QuickCheck
import Typer
import qualified Parser as P
import Parser hiding (Expr (..), Pat (..))
import Lower
import Record
import Syntax
import Util
import Typer
import Interpreter
import FlatType
import Control.Monad (liftM2)
import qualified Data.Map.Strict as Map


x = P.Var "x"
y = P.Var "y"
f = P.Var "f"

x' = P.VarPat "x"
y' = P.VarPat "y"
f' = P.VarPat "f"

i = P.IdxVar "i"
j = P.IdxVar "j"

i' = P.VarPat "i"
j' = P.VarPat "j"

l1 = P.Lit 1
l2 = P.Lit 2

parseTestCases =
  [ ("1 + 2"                 , P.App (P.App (P.Var "add") l1) l2)
  , ("for i: 1"              , P.For i' l1)
  , ("lam x: x"              , P.Lam x' x)
  , ("y x"                   , P.App y x)
  , ("x.i"                   , P.Get x i)
  , ("f x y"                 , P.App (P.App f x) y)
  , ("x.i.j"                 , P.Get (P.Get x i) j)
  , ("let x = 1 in x"        , P.Let x' l1 x)
  , ("let x = 1; y = 2 in x" , P.Let x' l1 (P.Let y' l2 x))
  , ("for i j: 1"            , P.For i' (P.For j' l1))
  , ("lam x y: x"            , P.Lam x' (P.Lam y' x))
  , ("let f x = x in f"      , P.Let f' (P.Lam x' x) f)
  , ("let x . i = y in x"    , P.Let x' (P.For i' y) x)
  , ("let f x y = x in f"    , P.Let f' (P.Lam x' (P.Lam y' x)) f)
  , ("let x.i.j = y in x"    , P.Let x' (P.For i' (P.For j' y)) x)
  , ("(x, y)"                , P.RecCon $ posRecord [x, y])
  , ("(x=1, y=2)"            , P.RecCon $ nameRecord [("x",l1),("y",l2)])
  , ("()"                    , P.RecCon $ emptyRecord )
  , ("lam (x,y): 1"          , P.Lam (P.RecPat $ posRecord [x', y']) l1 )
  , ("let f (x,y) = 1 in f"  , P.Let f' (P.Lam (P.RecPat $ posRecord [x',y']) l1) f)
  , ("let (x,y) = (1,2) in x", P.Let (P.RecPat $ posRecord [x',y'])
                                     (P.RecCon $ posRecord [l1, l2]) x)
  , ("let (x=x,y=y) = (y=1,x=2) in x",
        P.Let (P.RecPat $ nameRecord [("x",x'),("y",y')])
              (P.RecCon $ nameRecord [("x",l2),("y",l1)]) x)
  , ("for (i,j): 1"          , P.For (P.RecPat $ posRecord [i', j']) l1)
  , ("for (i,j): x.(j,i)"    , P.For (P.RecPat $ posRecord [i', j'])
                                   (P.Get x (P.IdxRecCon $ posRecord [j, i])))
  ]

infixr 1 -->
infixr 2 ===>
(-->) = ArrType
(===>) = TabType
int = BaseType IntType
a = TypeVar 0
b = TypeVar 1

typeTestCases =
  [ ("1"                     , Forall 0 $ int)
  , ("1 + 3"                 , Forall 0 $ int)
  , ("lam x: x"              , Forall 1 $ a --> a)
  , ("(lam x: x) 2"          , Forall 0 $ int)
  , ("for i: 1"              , Forall 1 $ a ===> int)
  , ("for i: (for j: 3).i"   , Forall 1 $ a ===> int)
  , ("for i: (iota 3).i"     , Forall 0 $ int ===> int)
  , ("reduce add 0 (iota 3)" , Forall 0 $ int)
  , ("let x = 1 in x"        , Forall 0 $ int)
  , ("lam x: (x,x)"          , Forall 1 $ a --> RecType (posRecord [a, a]))
  , ("let (x,y) = (1,(2,3)) in (y,x)", Forall 0 $
        RecType (posRecord [RecType (posRecord [int, int]), int]))
  ]

instance Show a => Testable (Either a b) where
  property (Left s) = counterexample (show s) False
  property (Right _) = property True

prop_flatUnflatType :: Type -> Property
prop_flatUnflatType t = case flattenType t of
    Left _ -> property Discard
    Right tabs -> t === unflattenType tabs

prop_validVal :: TypedVal -> Property
prop_validVal = property . validTypedVal

typeErrorTestCases =
  [ ("lam f: f f"   , InfiniteType)
  , ("1 1"          , UnificationError int (int --> TypeVar 0))
  , ("let (x,y) = 1 in x", UnificationError int (RecType (posRecord [a,b])))
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
  , ("let (x,y) = (1,2) in y", IntVal 2)
  , ("(lam (x,y): x) (2,1)"  , IntVal 2)
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
  putStrLn "Parse tests"        >> runTestTT parseTests
  putStrLn "Type tests"         >> runTestTT typeTests
  putStrLn "Type error tests"   >> runTestTT typeErrorTests
  putStrLn "Eval tests"         >> runTestTT evalTests
  putStrLn "Flatten quickcheck" >> quickCheck prop_flatUnflatType
  putStrLn "Valid val quickcheck" >> quickCheck prop_validVal
