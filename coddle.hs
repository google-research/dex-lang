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
         , typeEnv = []
         , valEnv = initValEnv ++ inputVals }


evalCmd :: Command -> Repl ()
evalCmd c = case c of
  GetParse expr   -> printR expr
  GetLowered expr -> lowerR expr >>= printR
  GetType expr    -> lowerR expr >>= gettypeR >>= printR
  EvalExpr expr   -> do e <- lowerR expr
                        gettypeR e
                        v <- evalR e
                        printR v
  EvalDecl v expr -> do e   <- lowerR expr
                        t   <- gettypeR e
                        val <- evalR e
                        updateEnv v t val

liftErr :: Show a => Either a b -> Repl b
liftErr (Left e)  = printR e >> throwIO Interrupt
liftErr (Right x) = return x

lowerR :: P.Expr -> Repl Expr
lowerR expr = do
  env <- lift $ gets varEnv
  liftErr $ lowerExpr expr env

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
           Left e -> outputStrLn e >> loop
           Right cmd -> handleInterrupt (return ()) (evalCmd cmd) >> loop


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
