-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}


import Test.QuickCheck
import Test.QuickCheck.Random
import System.Exit
import Data.Text.Prettyprint.Doc
import Control.Monad
import qualified Hedgehog as H
import Control.Monad.Reader
import GHC.Stack
import qualified Data.Map.Strict as M


import Syntax hiding (Result)
import Parser
import PPrint
import Generators ()
import GenExpr
import TestPass

prop_print_parse_uexpr :: UTopDecl -> Property
prop_print_parse_uexpr decl = case parseTopDecl (pprintEsc decl) of
  Left e -> counterexample (pprint e) False
  Right decl' -> decl === stripSrcAnnotTopDecl decl'

-- wrapper to make show pretty
data PPWrap a = PPWrap a  deriving (Eq)

instance Pretty a => Show (PPWrap a) where
  show (PPWrap x) = pprintEsc x

instance Arbitrary a => Arbitrary (PPWrap a) where
  arbitrary = liftM PPWrap arbitrary
  shrink (PPWrap x) = map PPWrap (shrink x)

fromPPWrap :: PPWrap a -> a
fromPPWrap (PPWrap x) = x

pprintProp :: (Pretty a, Arbitrary a, Testable prop) => (a -> prop) -> Property
pprintProp f = property (f . fromPPWrap)

args :: Args
args = stdArgs
  { maxSize = 100
  , maxSuccess = 100
  , replay = Just (mkQCGen 0, 0)
  }

main :: IO ()
main = do
  results <- quickCheckWithResult args (pprintProp prop_print_parse_uexpr)
  _ <- tests
  if isSuccess results
    then return ()
    else exitWith (ExitFailure 1)

evalIOEither :: (H.MonadTest m, Show x, MonadIO m, HasCallStack) => IO (Either x a) ->  m a
evalIOEither m = H.evalIO m >>= H.evalEither

prop_jitEval :: TypeEnv -> Evaluator -> Evaluator -> H.Property
prop_jitEval tenv jit interp =
  H.property $ do
    srcBlk <- H.forAllWith pprint (runReaderT genSourceBlock (makeGenEnv tenv defaultGenOptions))
    interres <- evalIOEither (interp srcBlk)
    H.annotate ("Interpreter result: " ++ pprint interres)
    jitres <- evalIOEither (jit srcBlk)
    pprint interres H.=== pprint jitres


getExpr :: TopDeclP b -> ExprP b
getExpr ~(EvalCmd (Command _ e)) = e

prop_pprint :: H.Property
prop_pprint =
  H.property $ do
    expr <- H.forAllWith pprint (runReaderT sampleExpr (makeGenEnv mempty defaultGenOptions))
    H.tripping expr pprintEsc (\s -> (getExpr . stripSrcAnnotTopDecl) <$> parseTopDecl s)

tests :: IO Bool
tests = do
  let prelude = "prelude.dx"
  jit <- runTestPass prelude fullPassJit
  interp <- runTestPass prelude fullPassInterp
  preludeEnv <- loadTypeEnv prelude
  let tyEnv = M.fromListWith (++) [(ty, [name]) | (ty, name) <- preludeEnv]
  H.checkParallel $ H.Group "TypeCheck" [
        ("prop_jitEval", prop_jitEval tyEnv jit interp)
      , ("prop_pprint", prop_pprint)
    ]
