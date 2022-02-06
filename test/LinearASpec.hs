{-# OPTIONS_GHC -Wno-orphans #-}
module LinearASpec where

import qualified Data.Map.Strict as M
import Test.Hspec
import LinearA
import Prettyprinter

-- Define some orhpan instances as sugar over non-linear expressions
instance Num Expr where
  (+) = BinOp Add
  (*) = BinOp Mul
  abs = undefined
  signum = undefined
  fromInteger = Lit . fromInteger
  negate = undefined

instance Fractional Expr where
  fromRational = Lit . fromRational
  (/) = undefined

shouldTypeCheck :: Program -> Expectation
shouldTypeCheck prog = do
  let tp = typecheckProgram prog
  case tp of
    (Right ()) -> return ()
    (Left _) -> putStrLn $ show $ pretty prog
  tp `shouldBe` (Right ())

shouldNotTypeCheck :: Program -> Expectation
shouldNotTypeCheck prog = typecheckProgram prog `shouldSatisfy` \case
  Left  _ -> True
  Right _ -> False

-- Compute a gradient in LinearA, with sanity checks along the way
-- This version assumes the function produces a single real output, so
-- doesn't take a covector.
gradient :: Program -> FuncName -> [Value] -> IO [Value]
gradient prog f args = do
  shouldTypeCheck prog
  let jProg = jvpProgram prog
  shouldTypeCheck jProg
  let ujProg = unzipProgram jProg
  shouldTypeCheck ujProg
  let tujProg = transposeProgram ujProg
  shouldTypeCheck tujProg
  let expPrimal = evalFunc prog f args []
  let (Result primal_tape empty) = evalFunc tujProg (f ++ ".nonlin") args []
  empty `shouldBe` []
  -- The tape is a tuple at the end; split it into a singleton list
  let (primal, tape) = splitAt (length primal_tape - 1) primal_tape
  (Result primal []) `shouldBe` expPrimal
  let (Result empty2 grad) = evalFunc tujProg (f ++ ".lin") tape [FloatVal 1.0]
  empty2 `shouldBe` []
  return grad

spec :: Spec
spec = do
  describe "evaluation" $ do
    it "evaluates a simple function" $ do
      let prog = Program $ M.fromList
            [ ("f", FuncDef [("x", FloatType)] [] (MixedType [FloatType] []) $
                LetMixed ["y"] [] 2.0 $
                LetMixed ["z"] [] ((Var "y") * ((Var "x") + 2.0)) $
                Ret ["z"] []
              )
            ]
      let expr = LetMixed ["x"] [] 2.0 $
                   App "f" ["x"] []
      eval prog mempty expr `shouldBe` (Result [FloatVal 8.0] [])

  describe "non-linear type checker" $ do
    it "accepts an implicit dup" $ do
      shouldTypeCheck $ Program $ M.fromList
        [ ("id", FuncDef [("x", FloatType)] [] (MixedType [FloatType, FloatType] []) $
            LetMixed ["y"] [] (Ret ["x"][] ) $
            Ret ["x", "y"] [])
        ]

    it "rejects an implicit drop" $ do
      shouldNotTypeCheck $ Program $ M.fromList
        [ ("drop", FuncDef [("x", FloatType)] [] (MixedType [] []) $
            Ret [] [])
        ]

  describe "linear type checker" $ do
    it "type checks a linear identity" $ do
      shouldTypeCheck $ Program $ M.fromList
        [ ("id", FuncDef [] [("x", FloatType)] (MixedType [] [FloatType]) $
            LetMixed [] ["y"] (Ret [] ["x"]) $
            Ret [] ["y"])
        ]

    it "rejects an implicit linear dup" $ do
      shouldNotTypeCheck $ Program $ M.fromList
        [ ("dup", FuncDef [] [("x", FloatType)] (MixedType [] [FloatType, FloatType]) $
            LetMixed [] ["y"] (Ret [] ["x"]) $
            Ret [] ["x", "y"])
        ]

    it "accepts llam x. x + 0" $ do
      shouldTypeCheck $ Program $ M.fromList
        [ ("f", FuncDef [] [("x", FloatType)] (MixedType [] [FloatType]) $
            LetMixed [] ["y"] (LAdd (LVar "x") LZero) $
            Ret [] ["y"])
        ]

    it "accepts llam x. x0 + x1" $ do
      shouldTypeCheck $ Program $ M.fromList
        [ ("f", FuncDef [] [("x", FloatType)] (MixedType [] [FloatType]) $
            LetMixed [] ["x0", "x1"] (Dup (LVar "x")) $
            LetMixed [] ["y"] (LAdd (LVar "x0") (LVar "x1")) $
            Ret [] ["y"])
        ]

    it "accepts llam x. x0 + (x1 + x2)" $ do
      shouldTypeCheck $ Program $ M.fromList
        [ ("f", FuncDef [] [("x", FloatType)] (MixedType [] [FloatType]) $
            LetMixed [] ["x0", "x"] (Dup (LVar "x")) $
            LetMixed [] ["x1", "x2"] (Dup (LVar "x")) $
            LetMixed [] ["y"] (LAdd (LVar "x0") (LAdd (LVar "x1") (LVar "x2"))) $
            Ret [] ["y"])
        ]

    it "accepts llam x y. x + y" $ do
      shouldTypeCheck $ Program $ M.fromList
        [ ("f", FuncDef [] [("x", FloatType), ("y", FloatType)] (MixedType [] [FloatType]) $
            LetMixed [] ["z"] (LAdd (LVar "x") (LVar "y")) $
            Ret [] ["z"])
        ]

    it "accepts llam x y. 0" $ do
      shouldTypeCheck $ Program $ M.fromList
        [ ("f", FuncDef [] [("x", FloatType), ("y", FloatType)] (MixedType [] [FloatType]) $
            LetMixed [] [] (Drop (LTuple ["x", "y"])) $
            LetMixed [] ["z"] LZero $
            Ret [] ["z"])
        ]

  describe "general type checker" $ do
    it "type checks an application" $ do
      shouldTypeCheck $ Program $ M.fromList
        [ ("f", FuncDef [("x", FloatType)] [("y", FloatType)]
                        (MixedType [FloatType, FloatType] [FloatType]) $
            Ret ["x", "x"] ["y"])
        , ("g", FuncDef [("x", FloatType)] [("y", FloatType)]
                        (MixedType [FloatType, FloatType] [FloatType]) $
            App "f" ["x"] ["y"])
        ]

    it "rejects a dup in an application" $ do
      shouldNotTypeCheck $ Program $ M.fromList
        [ ("f", FuncDef [] [("x", FloatType), ("y", FloatType)] (MixedType [] [FloatType]) $
            LetMixed [] ["z"] (LAdd (LVar "x") (LVar "y")) $
            Ret [] ["z"])
        , ("g", FuncDef [] [("x", FloatType)] (MixedType [] [FloatType]) $
            App "f" [] ["x", "x"])
        ]

    it "accepts a non-linear scaling" $ do
      shouldTypeCheck $ Program $ M.fromList
        [ ("f", FuncDef [("x", FloatType)] [("y", FloatType)] (MixedType [] [FloatType]) $
            LetMixed [] ["z"] (LScale (Var "x") (LVar "y")) $
            Ret [] ["z"])
        ]

  describe "JVP" $ do
    it "(sin x)^2 + (cos x)^2" $ do
      let pj = jvpProgram $ Program $ M.fromList
                 [ ("f", FuncDef [("x", FloatType)] [] (MixedType [FloatType] []) $
                     LetMixed ["y"] [] (UnOp Sin (Var "x")) $
                     LetMixed ["z"] [] (UnOp Cos (Var "x")) $
                     (Var "y") * (Var "y") + (Var "z") * (Var "z"))
                 ]
      shouldTypeCheck pj
      -- TODO: Test that this evaluates to approximately (1.0, 0.0) for a variety of inputs
      let Result _ [FloatVal dx] = evalFunc pj "f" [FloatVal 2.0] [FloatVal 2.0]
      dx `shouldBe` 0.0

  let ensureJvpUnzips p = do
        let pj = jvpProgram p
        let upj = unzipProgram pj
        shouldTypeCheck pj
        shouldTypeCheck upj
        let expAns = evalFunc pj "f" [FloatVal 2.0] [FloatVal 2.0]
        let ans = eval upj mempty $
                    LetMixed ["x"] [] (Lit 2.0) $
                    LetMixed ["v", "r"] [] (App "f.nonlin" ["x"] []) $
                    LetMixed [] ["v'"] (App "f.lin" ["r"] ["x"]) $
                    Ret ["v"] ["v'"]
        ans `shouldBe` expAns

  describe "Unzipping" $ do
    it "sin x" $ do
      let p = Program $ M.fromList
                [ ("f", FuncDef [("x", FloatType)] [] (MixedType [FloatType] []) $
                    UnOp Sin (Var "x")
                  )
                ]
      ensureJvpUnzips p

  describe "Transposition" $ do
    let lin_add_func = FuncDef [] [("x", FloatType), ("y", FloatType)] (MixedType [] [FloatType]) $
          LetMixed [] ["z"] (LAdd (LVar "x") (LVar "y")) $
          LVar "z"
    it "x + y (linearly)" $ do
      let p = Program $ M.fromList [ ("add", lin_add_func) ]
      shouldTypeCheck $ transposeProgram p

  let add_func = FuncDef [("x", FloatType), ("y", FloatType)] [] (MixedType [FloatType] []) $
        LetMixed ["z"] [] (BinOp Add (Var "x") (Var "y")) $
        Var "z"

  let double_func = FuncDef [("x", FloatType)] [] (MixedType [FloatType] []) $
        LetMixed ["z"] [] (BinOp Add (Var "x") (Var "x")) $
        Var "z"

  describe "End-to-end reverse-mode" $ do

    it "x + y" $ do
      let p = Program $ M.fromList [ ("add", add_func) ]
      grad <- gradient p "add" [FloatVal 2.0, FloatVal 2.0]
      grad `shouldBe` [FloatVal 1.0, FloatVal 1.0]

    it "function call" $ do
      let p = Program $ M.fromList
                [ ("add", add_func)
                , ("f", FuncDef [("x", FloatType), ("y", FloatType)] [] (MixedType [FloatType] []) $
                    LetMixed ["z"] [] (App "add" ["x", "y"] []) $
                    Var "z")
                ]
      grad <- gradient p "f" [FloatVal 2.0, FloatVal 2.0]
      grad `shouldBe` [FloatVal 1.0, FloatVal 1.0]

    it "x + x should add dup" $ do
      let p = Program $ M.fromList [("double", double_func)]
      grad <- gradient p "double" [FloatVal 4.0]
      grad `shouldBe` [FloatVal 2.0]

    it "should differentiate through tuples" $ do
      let p = Program $ M.fromList
                -- A contrived squaring function that first packs its
                -- argument into a tuple and then unpacks it.
                [ ("square", FuncDef [("x", FloatType)] [] (MixedType [FloatType] []) $
                    LetMixed ["y"] [] (Tuple ["x", "x"]) $
                    LetUnpack ["x1", "x2"] "y" $
                    BinOp Mul (Var "x1") (Var "x2"))
                ]
      grad <- gradient p "square" [FloatVal 3.0]
      grad `shouldBe` [FloatVal 6.0]

    it "should differentiate literals" $ do
      let p = Program $ M.fromList
                [ ("add_1", FuncDef [("x", FloatType)] [] (MixedType [FloatType] []) $
                    BinOp Add (Var "x") (Lit 1.0))
                ]
      grad <- gradient p "add_1" [FloatVal 3.0]
      grad `shouldBe` [FloatVal 1.0]

    it "should respect drops" $ do
      let p = Program $ M.fromList
                [ ("add_1", FuncDef [("x", FloatType)] [] (MixedType [FloatType] []) $
                    LetMixed [] [] (Drop $ BinOp Mul (Var "x") (Var "x")) $
                    BinOp Add (Var "x") (Lit 1.0))
                ]
      grad <- gradient p "add_1" [FloatVal 3.0]
      grad `shouldBe` [FloatVal 1.0]

    let two_vec = TupleType [FloatType, FloatType]
    let two_mat = TupleType [two_vec, two_vec]
    it "should run the matvec2x2 example" $ do
      let p = Program $ M.fromList
                [ ("matvec2x2", FuncDef [("m", two_mat), ("v", two_vec)] [] (MixedType [two_vec] []) $
                    LetUnpack ["row_1", "row_2"] "m" $
                    LetUnpack ["m11", "m12"] "row_1" $
                    LetUnpack ["v1", "v2"] "v" $
                    LetMixed ["w1"] [] (BinOp Add (BinOp Mul (Var "m11") (Var "v1"))
                                                  (BinOp Mul (Var "m12") (Var "v2"))) $
                    LetUnpack ["m21", "m22"] "row_2" $
                    LetMixed ["w2"] [] (BinOp Add (BinOp Mul (Var "m21") (Var "v1"))
                                                  (BinOp Mul (Var "m22") (Var "v2"))) $
                    Tuple ["w1", "w2"])
                , ("specific", FuncDef [("v", two_vec)] [] (MixedType [FloatType] []) $
                    LetMixed ["m"] [] (tuple [ (tuple [Lit 2.0, Lit 7.0])
                                             , (tuple [Lit 1.0, Lit 8.0])
                                             ]) $
                    LetMixed ["anf"] [] (App "matvec2x2" ["m", "v"] []) $
                    LetUnpack ["a1", "a2"] "anf" $
                    BinOp Mul (Var "a1") (Var "a2")
                  )
                ]
      grad <- gradient p "specific" [TupleVal [FloatVal 2.0, FloatVal 3.0]]
      grad `shouldBe` [TupleVal [FloatVal 77.0, FloatVal 382.0]]
