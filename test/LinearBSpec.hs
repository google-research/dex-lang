{-# OPTIONS_GHC -Wno-orphans #-}
module LinearBSpec where

import Data.Functor
import qualified Data.Map.Strict as M
import Test.Hspec
import LinearB
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

mixedType :: [Type] -> [Type] -> MixedDepType
mixedType ty ty' = MixedDepType (ty <&> \t -> (Nothing, t)) ty'

spec :: Spec
spec = do
  describe "type checker" $ do
    it "accepts an implicit dup" $ do
      shouldTypeCheck $ Program $ M.fromList
        [ ("dup", FuncDef [("x", FloatType)] [] (mixedType [FloatType, FloatType] []) $
            LetDepMixed ["y"] [] (Var "x") $
            RetDep ["x", "y"] [] (mixedType [FloatType, FloatType] []))
        ]

    it "checks jvp of case" $ do
      -- jvp (\x. case x of Left f -> f * 2.0; Right () -> 4.0)
      shouldTypeCheck $ Program $ M.fromList
        [ ("case", FuncDef [("x", SumType [FloatType, TupleType []])]
                           [("xt", SumDepType (Proj "x" []) "xb"
                                     [FloatType, TupleType []])]
                           (mixedType [FloatType] [FloatType]) $
            Case "x" "xv" (mixedType [FloatType] [FloatType])
              [ LetDepMixed ["yv"] []  (BinOp Mul (Var "xv") (Lit 2.0)) $
                LetDepMixed [] ["ytv"] (LScale (Lit 2.0) (LVar "xt")) $
                RetDep ["yv"] ["ytv"] (mixedType [FloatType] [FloatType])
              , LetDepMixed ["yv"] []  (Lit 4.0) $
                LetDepMixed [] ["ytv"] (LZero) $
                LetDepMixed [] []      (Drop (LVar "xt")) $
                LetDepMixed [] []      (Drop (Var "xv")) $
                RetDep ["yv"] ["ytv"] (mixedType [FloatType] [FloatType])
              ])
        ]

  describe "jvp" $ do
    it "case" $ do
      shouldTypeCheck $ jvpProgram $ Program $ M.fromList
        [ ("case", FuncDef [("x", SumType [FloatType, TupleType []])] []
                           (mixedType [FloatType] []) $
            Case "x" "xv" (mixedType [FloatType] [])
              [ BinOp Mul (Var "xv") (Lit 2.0)
              , LetDepMixed [] []      (Drop (Var "xv")) $
                Lit 4.0
              ])
        ]

    it "inject" $ do
      shouldTypeCheck $ jvpProgram $ Program $ M.fromList
        [ ("inject", FuncDef [("x", FloatType)] []
                             (mixedType [SumType [FloatType, TupleType []]] []) $
          LetDepMixed ["q"] [] (BinOp Mul (Var "x") (Lit 2.0)) $
          LetDepMixed ["w"] [] (Inject 0 "q" [FloatType, TupleType []]) $
          RetDep ["w"] [] (mixedType [SumType [FloatType, TupleType []]] []))
        ]

    it "case of case" $ do
      shouldTypeCheck $ jvpProgram $ Program $ M.fromList
        [ ("twoCase", FuncDef [("x", SumType [FloatType, TupleType []])] []
                           (mixedType [FloatType] []) $
            Case "x" "xv" (mixedType [FloatType] [])
              [ Case "x" "xv2" (mixedType [FloatType] [])
                [ LetDepMixed [] [] (Drop (Var "xv2")) $
                  BinOp Mul (Var "xv") (Lit 2.0)
                , -- We unpack the exercise the duality of x's tangent type:
                  -- it has to act both as a tuple and as a float. Note that
                  -- this code is unreachable at runtime.
                  LetUnpack [] "xv2" $
                  BinOp Mul (Var "xv") (Lit 4.0)
                ]
              , LetDepMixed [] []      (Drop (Tuple ["x", "xv"])) $
                Lit 4.0
              ])
        ]

    it "case swap" $ do
      let fou = SumType [FloatType, TupleType []]
      let uof = SumType [TupleType [], FloatType]
      shouldTypeCheck $ jvpProgram $ Program $ M.fromList
        [ ("caseSwap", FuncDef [("x", fou)] [] (mixedType [uof] []) $
            LetDepMixed ["y"] [] (Var "x") $
            Case "y" "yv" (mixedType [uof] [])
              [ Inject 1 "yv" [TupleType [], FloatType]
              , Inject 0 "yv" [TupleType [], FloatType]
              ])
        ]
