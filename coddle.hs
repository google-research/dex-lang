import System.Console.Haskeline
import System.Environment
import System.IO
import Control.Monad
import Control.Monad.IO.Class
import Data.List hiding (lookup)

import Prelude hiding (lookup)

import Interpreter
import Parser

evalLines :: Env -> VarEnv -> [String] -> String
evalLines env varEnv [] = show $ getOutVal env varEnv
evalLines env varEnv ("":lines) = evalLines env varEnv lines
evalLines env varEnv (line:lines) =
  let (newValEnv, newVarEnv) = evalLine env varEnv line
  in line ++ "\n" ++ evalLines newValEnv newVarEnv lines


getOutVal :: Env -> VarEnv -> Val
getOutVal env varEnv =
  case lookup "out" varEnv
      of (Just i) -> env !! i

evalLine :: Env -> VarEnv -> String -> (Env, VarEnv)
evalLine valEnv varEnv line =
  case parseLine line varEnv of
    Right (v, e) -> let ans = eval e valEnv (0, [])
                     in (ans:valEnv, v:varEnv)
    Left e  -> error ("parse error in line:" ++ line ++ (show e))

splitString :: Char -> String -> [String]
splitString c s = case dropWhile (== c) s of
             ""   -> []
             rest -> prefix : splitString c rest'
                     where (prefix, rest') = break (== c) rest

evalMultiSource :: String -> String
evalMultiSource s = let results = map (evalLines builtinEnv builtinVars . lines) $ splitString '~' s
                    in concat $ intersperse "\n\n" results

-- repl :: IO ()
-- repl = runInputT defaultSettings (loop [])
--   where
--   loop env = do
--     minput <- getInputLine "> "
--     case minput of
--       Nothing -> return ()
--       Just line -> let ans = evalSource line
--                    in (liftIO (putStrLn ans)) >> loop []

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
    -- []       -> repl
