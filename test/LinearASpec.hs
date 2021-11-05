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
shouldTypeCheck prog = isProgramTypeCorrect prog `shouldBe` True

shouldNotTypeCheck :: Program -> Expectation
shouldNotTypeCheck prog = isProgramTypeCorrect prog `shouldBe` False

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
