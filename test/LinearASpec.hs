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

spec :: Spec
spec = do
  describe "evaluation" $ do
    it "evaluates a simple function" $ do
      let prog = Program $ M.fromList
            [ ("f", FuncDef ["x"] [] (MixedType [FloatType] []) $
                LetMixed ["y"] [] 2.0 $
                LetMixed ["z"] [] ((Var "y") * ((Var "x") + 2.0)) $
                Ret ["z"] []
              )
            ]
      let expr = LetMixed ["x"] [] 2.0 $
                   App "f" ["x"] []
      eval prog mempty expr `shouldBe` (Result [FloatVal 8.0] [])
