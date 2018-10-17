import System.Console.Haskeline
import System.Environment
import System.IO
import Control.Monad
import Control.Monad.IO.Class
import Data.List

import Interpreter
import Parser

evalSource :: String -> String
evalSource line =
  case parseExpr line of
    Left e ->  "Parse error:\n" ++ show e
    Right r -> line ++ "\n" ++ (show $ evalClosed r)

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

-- eval index comprehensions

-- builtins as syntactically the same as biops
-- make it monadic
-- handle multiple vars/idxvars (desugaring to single ones)
-- indentation and top-level functions?

-- types (syntax)
-- type checking/inference

-- think about
--   reduce
--   binary op loop

-- emit LLVM for actual compilation?

-- syntax for pinning layouts?
