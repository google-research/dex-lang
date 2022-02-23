{-# OPTIONS_GHC -Wno-orphans #-}
module LinearBSpec where

import Data.String
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

instance IsString ProjExpr where
  fromString s = Proj (fromString s) []

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
            RetDep ["x", "y"] []
          )
        ]

    it "accepts an output with type dependent on an input" $ do
      let xTanTy = SumDepType "x" "xv" [FloatType, TupleType []]
      shouldTypeCheck $ Program $ M.fromList
        [ ("depOnInput", FuncDef [("x", SumType [FloatType, TupleType []])] []
                           (mixedType [] [xTanTy]) $
            Case "x" "xv" (mixedType [] [xTanTy])
              [ LetDepMixed [] [] (Drop (Var "xv")) $ Cast LZero       (mixedType [] [xTanTy])
              , LetDepMixed [] [] (Drop (Var "xv")) $ Cast (LTuple []) (mixedType [] [xTanTy])
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
            RetDep ["w"] []
          )
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

  let ensureJvpUnzips p = do
        let pj = jvpProgram p
        shouldTypeCheck pj
        let upj = unzipProgram pj
        shouldTypeCheck upj
        --let expAns = evalFunc pj "f" [FloatVal 2.0] [FloatVal 2.0]
        --let ans = eval upj mempty $
                    --LetMixed ["x"] [] (Lit 2.0) $
                    --LetMixed ["v", "r"] [] (App "f.nonlin" ["x"] []) $
                    --LetMixed [] ["v'"] (App "f.lin" ["r"] ["x"]) $
                    --Ret ["v"] ["v'"]
        --ans `shouldBe` expAns

  describe "unzip" $ do
    it "sin x" $ do
      let p = Program $ M.fromList
                [ ("f", FuncDef [("x", FloatType)] [] (mixedType [FloatType] []) $
                    UnOp Sin (Var "x")
                  )
                ]
      ensureJvpUnzips p

    xit "inject" $ do
      ensureJvpUnzips $ Program $ M.fromList
        [ ("f", FuncDef [("x", FloatType)] [] (mixedType [SumType [FloatType, TupleType []]] []) $
            Inject 0 "x" [FloatType, TupleType []]
          )
        ]
