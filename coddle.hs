import System.Console.Haskeline
import System.Environment
import System.IO
import Control.Monad
import Control.Monad.IO.Class
import Data.List

import Interpreter
import Parser

-- showParse _ = ""
showParse p = "Parse: " ++ (show $ p) ++ "\n"

evalSource :: String -> String
evalSource line =
  case parseExpr line of
    Left e ->  "Parse error:\n" ++ show e
    Right r -> showParse r ++ (show $ evalClosed r)

splitString :: Char -> String -> [String]
splitString c s = case dropWhile (== c) s of
             ""   -> []
             rest -> prefix : splitString c rest'
                     where (prefix, rest') = break (== c) rest

evalMultiSource :: String -> String
evalMultiSource s = let results = map evalSource $ splitString '~' s
                    in concat $ intersperse "\n\n" results


repl :: IO ()
repl = runInputT defaultSettings loop
  where
  loop = do
    minput <- getInputLine "> "
    case minput of
      Nothing -> return ()
      Just line -> (liftIO . putStrLn . evalSource $ line)
                   >> loop

evalFile :: String -> IO ()
evalFile s = do
    source <- readFile s
    putStrLn $ evalMultiSource source
    return ()

main :: IO ()
main = do
  args <- getArgs
  case args of
    fname:[] -> evalFile fname
    []       -> repl

-- ---------- TODO ----------

-- alpha abstraction and application
--   syntax
--   eval

-- handle multiple vars (desugaring to single ones)
-- indentation and top-level functions?

-- types (syntax)
-- type checking/inference

-- think about
--   reduce
--   binary op loop
