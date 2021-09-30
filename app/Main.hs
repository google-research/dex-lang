module Main where

import TableEffectsExamples

main :: IO ()
main = do
  putStrLn "sumExampleResult ="
  print sumExampleResult
  putStrLn ""
  putStrLn "exceptExampleResult ="
  print exceptExampleResult
  putStrLn ""
  putStrLn "binomialTimesUniformSamples ="
  print binomialTimesUniformSamples
  putStrLn ""
  putStrLn "serialRandomResults ="
  print serialRandomResults
  putStrLn ""
  putStrLn "parallelRandomResults ="
  print parallelRandomResults
  putStrLn ""
  putStrLn "ambCoinFlips ="
  print ambCoinFlips
  putStrLn ""
  putStrLn "ambDigitPairs ="
  print ambDigitPairs
  putStrLn ""
  putStrLn "unifListResNoThrow ="
  print unifListResNoThrow
  putStrLn ""
  putStrLn "unifListResWithThrow ="
  print unifListResWithThrow
  putStrLn ""
