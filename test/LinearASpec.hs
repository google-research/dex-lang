{-# OPTIONS_GHC -Wno-orphans #-}
module LinearASpec where

import qualified Data.Map.Strict as M
import Test.Hspec
import LinearA

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
shouldTypeCheck prog = typecheckProgram prog `shouldBe` (Right ())

shouldNotTypeCheck :: Program -> Expectation
shouldNotTypeCheck prog = typecheckProgram prog `shouldSatisfy` \case
  Left  _ -> True
  Right _ -> False

-- Compute a gradient in LinearA, with sanity checks along the way
-- This version assumes the function produces a single real output, so
-- doesn't take a covector.
gradient :: Program -> FuncName -> [Float] -> IO [Value]
gradient prog f args = do
  shouldTypeCheck prog
  let jProg = jvpProgram prog
  shouldTypeCheck jProg
  let ujProg = unzipProgram jProg
  shouldTypeCheck ujProg
  let tujProg = transposeProgram ujProg
  shouldTypeCheck tujProg
  let expPrimal = evalFunc prog f (map FloatVal args) []
  let (Result primal_tape empty) = evalFunc tujProg (f ++ ".nonlin") (map FloatVal args) []
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

  describe "End-to-end reverse-mode" $ do

    it "x + y" $ do
      let p = Program $ M.fromList [ ("add", add_func) ]
      grad <- gradient p "add" [2.0, 2.0]
      grad `shouldBe` [FloatVal 1.0, FloatVal 1.0]

    it "function call" $ do
      let p = Program $ M.fromList
                [ ("add", add_func)
                , ("f", FuncDef [("x", FloatType), ("y", FloatType)] [] (MixedType [FloatType] []) $
                    LetMixed ["z"] [] (App "add" ["x", "y"] []) $
                    Var "z")
                ]
      grad <- gradient p "f" [2.0, 2.0]
      grad `shouldBe` [FloatVal 1.0, FloatVal 1.0]
