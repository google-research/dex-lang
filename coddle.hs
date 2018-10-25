import System.Console.Haskeline
import System.Environment
import System.IO
import Control.Monad
import Control.Monad.IO.Class
import Data.List hiding (lookup)
import IOSql
import Prelude hiding (lookup)

import Util
import Parser
import Typer
import Interpreter

type Env = (ValEnv, VarEnv)

initEnv :: [Val] -> Env
initEnv inputVals =
  let inputVars = ["in" ++ (show n) | n <- [0..(length inputVals - 1)]]
  in ( initValEnv ++ inputVals
     , initVarEnv ++ inputVars)

evalLine :: Env -> String -> (Env, String)
evalLine env line =
  let (valEnv, varEnv) = env
  in case parseDeclOrExpr line varEnv of
        Left e             -> (env, "error: " ++ show e ++ "\n")
        Right (Nothing, e) -> (env, show $ evalExpr e valEnv)
        Right (Just v , e) -> let ans = evalExpr e valEnv
                              in ((ans:valEnv, v:varEnv), "")


repl :: String -> Behavior -> Env -> IO ()
repl prompt behavior env = runInputTBehavior behavior defaultSettings (loop $ env)
  where
  loop env = do
    minput <- getInputLine prompt
    case minput of
      Nothing -> return ()
      Just "" -> loop env
      Just line -> let (env', s) = evalLine env line
                   in outputStrLn s >> loop env'

terminalRepl :: Env -> IO ()
terminalRepl = repl ">=> " defaultBehavior

fileRepl :: String -> Env -> IO ()
fileRepl fname = repl "" (useFile fname)

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["sql"] -> do intable <- loadData "test.db" "test" ["x", "y", "v"]
                  terminalRepl $ initEnv [intable]
    [fname] -> fileRepl fname $ initEnv []
    []      -> terminalRepl $ initEnv []
