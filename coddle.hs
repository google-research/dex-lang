import System.Console.Haskeline
import System.Environment
import System.IO
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Identity
import Control.Monad.Except
import Control.Monad.IO.Class
import Data.List hiding (lookup)
import IOSql
import Prelude hiding (lookup)

import Syntax
import Util
import Parser
import Typer
import Interpreter

data Env = Env { varEnv  :: VarEnv
               , typeEnv :: TypeEnv
               , valEnv  :: ValEnv }

data Command = GetType Expr
             | PrintExpr Expr
             | EvalDecl VarName Expr

type Repl a = InputT (StateT Env IO) a

initEnv :: [Val] -> Env
initEnv inputVals =
  let inputVars = ["in" ++ (show n) | n <- [0..(length inputVals - 1)]]
  in Env { varEnv = initVarEnv ++ inputVars
         , typeEnv = []
         , valEnv = initValEnv ++ inputVals }


evalCmd :: Command -> Repl ()
evalCmd c = case c of
  GetType expr    -> do t <- gettypeR expr
                        printR t
  PrintExpr expr  -> do gettypeR expr
                        v <- evalR expr
                        printR v
  EvalDecl v expr -> do t   <- gettypeR expr
                        val <- evalR expr
                        updateEnv v t val

liftErr :: Show a => Either a b -> Repl b
liftErr = undefined

catchR :: Repl a -> Repl a
catchR = id

gettypeR :: Expr -> Repl Type
gettypeR expr = do
  env <- lift $ gets typeEnv
  liftErr $ gettype expr env

evalR :: Expr -> Repl Val
evalR expr = do
  env <- lift $ gets valEnv
  return $ evalExpr expr env

printR :: Show a => a -> Repl ()
printR x = outputStrLn $ show x

updateEnv :: VarName -> Type -> Val -> Repl ()
updateEnv var ty val =
  let update env = Env { varEnv  = var:(varEnv  env)
                       , typeEnv = ty :(typeEnv env)
                       , valEnv  = val:(valEnv  env) }
  in lift $ modify update

parseLine :: String -> Either String Command
parseLine = undefined



runRepl :: Repl () -> Behavior -> Env -> IO ()
runRepl repl behavior env =
  let stateMonad = runInputTBehavior behavior defaultSettings repl
  in evalStateT stateMonad env

repl :: String -> Repl ()
repl prompt = loop
  where
    loop :: Repl ()
    loop = do
      input <- getInputLine prompt
      case input of
         Nothing -> return ()
         Just "" -> loop
         Just line -> case parseLine line of
           Left e -> printR e >> loop
           Right cmd -> (catchR $ evalCmd cmd) >> loop


terminalRepl :: Env -> IO ()
terminalRepl = runRepl (repl ">=> ") defaultBehavior

fileRepl :: String -> Env -> IO ()
fileRepl fname = runRepl (repl "") (useFile fname)

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["sql"] -> do intable <- loadData "test.db" "test" ["x", "y", "v"]
                  terminalRepl $ initEnv [intable]
    [fname] -> fileRepl fname $ initEnv []
    []      -> terminalRepl $ initEnv []
