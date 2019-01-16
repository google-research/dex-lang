import System.Console.Haskeline
import System.Environment hiding (getEnv)
import System.Exit
import System.IO hiding (print)
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Identity
import Control.Monad.IO.Class
import Data.List hiding (lookup)
import Options.Applicative
import Data.Semigroup ((<>))
import Prelude hiding (lookup, print)

import qualified Parser as P
import qualified Lower as L
import qualified FlatType as F
import qualified Interpreter as I
import qualified Syntax as S
import qualified JIT as J

import Syntax
import Typer
import Util
import FlatType (parseVal)
import Env hiding (Env)

data Env = Env { varEnv  :: FreeEnv ()
               , typeEnv :: FreeEnv SigmaType
               , valEnv  :: FreeEnv I.TypedVal }

type Repl a = InputT (StateT Env IO) a
type Except a = Either String a
type ProgramSource = String
type DataSource = String
data CmdOpts = CmdOpts (Maybe ProgramSource) (Maybe DataSource)

evalDecl :: TopDecl P.Expr -> Repl ()
evalDecl (EvalDecl v expr) = do
    ((), lowered) <- getVarEnv  >>= doPass L.lowerPass expr
    (ty, typed)   <- getTypeEnv >>= doPass typePass    lowered
    (val, ())     <- getValEnv  >>= doPass F.evalPass  typed
    updateEnv (v, ty, val)
  where
    doPass :: Pass v a b -> a -> FreeEnv v -> Repl (v, b)
    doPass (Pass applyPass evalCmd) expr env = liftErr $ applyPass expr env

evalDecl (EvalCmd cmd expr) = do
  lowered <- getVarEnv  >>= doPass L.lowerPass expr
  typed   <- getTypeEnv >>= doPass typePass    lowered
  ()      <- getValEnv  >>= doPass F.evalPass  typed
  return ()
  where
    doPass :: Pass v a b -> a -> FreeEnv v -> Repl b
    doPass (Pass applyPass evalCmd) expr env = do
      (val, expr') <- liftErr $ applyPass expr env
      case evalCmd cmd val expr' of
        Just s  -> outputStrLn s >> throwIO Interrupt
        Nothing -> return expr'

liftErr :: Except a -> Repl a
liftErr (Left e)  = outputStrLn e >> throwIO Interrupt
liftErr (Right x) = return x

consEnv :: (VarName, SigmaType, I.TypedVal) -> Env -> Env
consEnv (var, t, val) (Env varEnv typeEnv valEnv) =
  Env { varEnv  = updateFreeEnv varEnv  var ()
      , typeEnv = updateFreeEnv typeEnv var t
      , valEnv  = updateFreeEnv valEnv  var val }

updateEnv :: (VarName, SigmaType, I.TypedVal) -> Repl ()
updateEnv (var, t, val) = let update env = consEnv (var, t, val) env
                          in lift $ modify update

getVarEnv  = lift (gets varEnv)
getTypeEnv = lift (gets typeEnv)
getValEnv  = lift (gets valEnv)

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
         Just line -> case P.parseCommand line of
                        Left e -> outputStrLn e >> loop
                        Right decl -> catchErr (evalDecl decl) >> loop

catchErr :: Repl () -> Repl ()
catchErr = handleInterrupt $ return ()

terminalRepl :: Env -> IO ()
terminalRepl = runRepl (repl ">=> ") defaultBehavior

loadData :: String -> IO (I.TypedVal, SigmaType)
loadData fname = do
  contents <- readFile fname
  case parseVal contents of
    Left e -> do putStrLn "Error loading data"
                 putStrLn e
                 exitFailure
    Right (t,v) -> return (I.TypedVal t v, Forall 0 t)

opts :: ParserInfo CmdOpts
opts = info (p <**> helper) mempty
  where p = CmdOpts
            <$> (optional $ argument str (    metavar "FILE"
                                           <> help "Source program"))
            <*> (optional $ strOption (    long "data"
                                        <> metavar "DATA"
                                        <> help "Data source (optional)" ))

initEnv = Env emptyFreeEnv emptyFreeEnv emptyFreeEnv

main :: IO ()
main = do
  CmdOpts fname dbname <- execParser opts
  let repl = case fname of
               Just fname -> undefined
               Nothing -> terminalRepl
  (inVal, inTy) <- case dbname of
                     Just dbname -> loadData dbname
                     Nothing -> return (I.unitVal, unitType)
  repl $ ("data", inTy, inVal) `consEnv` initEnv
