import System.Console.Haskeline
import System.Environment
import System.IO hiding (print)
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Identity
import Control.Monad.Except
import Control.Monad.IO.Class
import Data.List hiding (lookup)
import IOSql
import Prelude hiding (lookup, print)

import qualified Parser as P
import Parser hiding (Expr (..))
import Lower
import Syntax
import Util
import Typer
import Interpreter

data Env = Env { varEnv  :: VarEnv
               , typeEnv :: TypeEnv
               , valEnv  :: ValEnv }

type Repl a = InputT (StateT Env IO) a

initEnv :: [Val] -> Env
initEnv inputVals =
  let inputVars = ["in" ++ (show n) | n <- [0..(length inputVals - 1)]]
  in Env { varEnv = initVarEnv ++ inputVars
         , typeEnv = initTypeEnv
         , valEnv = initValEnv ++ inputVals }


evalCmd :: Command -> Repl ()
evalCmd c = case c of
  GetParse expr   -> print expr
  GetLowered expr -> lower expr >>= print
  GetType expr    -> lower expr >>= gettype >>= print
  EvalExpr expr   -> do e <- lower expr
                        gettype e
                        v <- eval e
                        print v
  EvalDecl v expr -> do e   <- lower expr
                        t   <- gettype e
                        val <- eval e
                        updateEnv v t val

liftErr :: Show a => Either a b -> Repl b
liftErr (Left e)  = print e >> throwIO Interrupt
liftErr (Right x) = return x

catchErr :: Repl () -> Repl ()
catchErr = handleInterrupt $ return ()

lower :: P.Expr -> Repl Expr
lower expr = do
  env <- lift $ gets varEnv
  liftErr $ lowerExpr expr env

gettype :: Expr -> Repl ClosedType
gettype expr = do
  env <- lift $ gets typeEnv
  liftErr $ typeExpr expr env

eval :: Expr -> Repl Val
eval expr = do
  env <- lift $ gets valEnv
  return $ evalExpr expr env

print :: Show a => a -> Repl ()
print x = outputStrLn $ show x

updateEnv :: VarName -> ClosedType -> Val -> Repl ()
updateEnv var ty val =
  let update env = Env { varEnv  = var:(varEnv  env)
                       , typeEnv = ty :(typeEnv env)
                       , valEnv  = val:(valEnv  env) }
  in lift $ modify update

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
         Just line -> case parseCommand line of
           Left e -> outputStrLn "Parse error:" >> print e >> loop
           Right cmd -> catchErr (evalCmd cmd) >> loop


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
