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
import qualified Syntax as S
import qualified Interpreter as I
import Parser hiding (Expr (..), Pat (..), str)
import Lower (lowerExpr)
import Syntax
import Util
import Typer
import FlatType
import Builtins
import Env hiding (Env)
import JIT


data Pass v a b e =
  Pass { evalExpr :: a -> FreeEnv v -> Either e (v, b)
       , evalCmd  :: Command -> v -> b -> Maybe String
       , getEnv   :: Env -> FreeEnv v }

type Repl a = InputT (StateT Env IO) a
type Except a = Either String a
type ProgramSource = String
type DataSource = String
data CmdOpts = CmdOpts (Maybe ProgramSource) (Maybe DataSource)

evalDecl :: TopDecl P.Expr -> Repl ()
evalDecl (EvalDecl v expr) = do
    ((), lowered) <- doPass lowerPass expr
    (ty, typed)   <- doPass typePass  lowered
    (val, ())     <- doPass evalPass  typed
    updateEnv (v, ty, val)
  where
    doPass :: Show e => Pass v a b e -> a -> Repl (v, b)
    doPass (Pass evalExpr evalCmd getEnv) expr =
      do env <- lift $ gets getEnv
         liftErr $ evalExpr expr env

evalDecl (EvalCmd cmd expr) = doPass lowerPass expr
                          >>= doPass typePass
                          >>= doPass evalPass
  where
    doPass :: Show e => Pass v a b e -> a -> Repl b
    doPass (Pass evalExpr evalCmd getEnv) expr = do
      env <- lift $ gets getEnv
      (val, expr') <- liftErr $ evalExpr expr env
      case evalCmd cmd val expr' of
        Just s  -> outputStrLn s >> throwIO Interrupt
        Nothing -> return expr'

lowerPass :: Pass () P.Expr L.Expr L.LowerErr
lowerPass = Pass evalExpr evalCmd varEnv
  where evalExpr expr env = fmap (\x -> ((),x)) (L.lowerExpr expr env)
        evalCmd cmd () expr = case cmd of
          S.GetLowered -> Just $ show expr
          _ -> Nothing

typePass :: Pass SigmaType L.Expr S.Expr TypeErr
typePass = Pass inferTypes evalCmd typeEnv
  where evalCmd cmd ty tyExpr = case cmd of
          S.GetType  -> Just $ show ty
          S.GetTyped -> Just $ show tyExpr
          _ -> Nothing

evalPass :: Pass I.Val S.Expr () ()
evalPass = Pass evalExpr evalCmd valEnv
  where
    evalExpr expr env = Right (I.evalExpr expr env, ())
    evalCmd cmd val () =
      case cmd of
        EvalExpr -> Just $ show val --case showVal defaultPrintSpec t v of
                           --  Left  e -> e
                           --  Right s -> s
        _ -> Nothing
--                         s <- liftIO $ showLLVM c
--                         s <- liftIO $ evalJit c

errToStr :: Show e => Either e a -> Except a
errToStr x = case x of Left e  -> Left $ show e
                       Right v -> Right v

liftErr :: Show a => Either a b -> Repl b
liftErr (Left e)  = print e >> throwIO Interrupt
liftErr (Right x) = return x

print :: Show a => a -> Repl ()
print x = outputStrLn $ show x

showOnMatch :: (Eq a, Show b) => a -> a -> b -> Maybe String
showOnMatch x y val = if x == y then Just (show val) else Nothing


consEnv :: (VarName, SigmaType, I.Val) -> Env -> Env
consEnv (var, t, val) env = Env { varEnv  = updateFreeEnv (varEnv  env) var ()
                                , typeEnv = updateFreeEnv (typeEnv env) var t
                                , valEnv  = updateFreeEnv (valEnv  env) var val}

updateEnv :: (VarName, SigmaType, I.Val) -> Repl ()
updateEnv (var, t, val) = let update env = consEnv (var, t, val) env
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
         Just line -> case parseCommand line of
                        Left e -> outputStrLn e >> loop
                        Right decl -> catchErr (evalDecl decl) >> loop

catchErr :: Repl () -> Repl ()
catchErr = handleInterrupt $ return ()

terminalRepl :: Env -> IO ()
terminalRepl = runRepl (repl ">=> ") defaultBehavior

loadData :: String -> IO (I.Val, SigmaType)
loadData fname = do
  contents <- readFile fname
  case parseVal contents of
    Left e -> do putStrLn "Error loading data"
                 putStrLn e
                 exitFailure
    Right (t,v) -> return (v, Forall 0 t)

opts :: ParserInfo CmdOpts
opts = info (p <**> helper) mempty
  where p = CmdOpts
            <$> (optional $ argument str (    metavar "FILE"
                                           <> help "Source program"))
            <*> (optional $ strOption (    long "data"
                                        <> metavar "DATA"
                                        <> help "Data source (optional)" ))

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
