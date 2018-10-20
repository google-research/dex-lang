import System.Console.Haskeline
import System.Environment
import System.IO
import Control.Monad
import Control.Monad.IO.Class
import Data.List hiding (lookup)
import IOSql
import Prelude hiding (lookup)

import Interpreter
import Parser

type Env = (ValEnv, VarEnv)

evalLines :: Env -> [String] -> String
evalLines env [] = show $ getOutVal env
evalLines env ("":lines) = evalLines env lines
evalLines env (line:lines) = let (env', out) = evalLine env line
                             in out ++ evalLines env' lines

getOutVal :: Env -> Val
getOutVal (env, varEnv) = case lookup "out" varEnv of (Just i) -> env !! i

evalLine :: Env -> String -> (Env, String)
evalLine env line =
  let (valEnv, varEnv) = env
      eval' e = eval e valEnv (0, [])
  in case parseLine line varEnv of
        Left e             -> (env, "error: " ++ e ++ "\n")
        Right (Nothing, e) -> (env, show $ eval' e)
        Right (Just v , e) -> let ans = eval' e
                              in ((ans:valEnv, v:varEnv), "")

splitString :: Char -> String -> [String]
splitString c s = case dropWhile (== c) s of
             ""   -> []
             rest -> prefix : splitString c rest'
                     where (prefix, rest') = break (== c) rest

initEnv :: [Val] -> Env
initEnv xs =
  let inputName n = "in" ++ (show n)
  in ( builtinEnv ++ xs
     , builtinVars ++ map inputName [0..(length xs - 1)])

emptyEnv = initEnv []

evalMultiSource :: String -> String
evalMultiSource s =
  let results = map (evalLines emptyEnv . lines) $ splitString '~' s
  in concat $ intersperse "\n\n" results

repl :: Env -> IO ()
repl env = runInputT defaultSettings (loop $ env)
  where
  loop env = do
    minput <- getInputLine ">=> "
    case minput of
      Nothing -> return ()
      Just "" -> loop env
      Just line -> let (env', s) = evalLine env line
                   in liftIO (putStr s) >> loop env'

sqlrepl :: IO ()
sqlrepl = undefined


evalFile :: String -> IO ()
evalFile s = do
    source <- readFile s
    putStrLn $ evalMultiSource source
    return ()

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["sql"] -> do intable <- loadData "test.db" "test" ["x", "y", "v"]
                  repl $ initEnv [intable]
    [fname] -> evalFile fname
    []      -> repl emptyEnv
