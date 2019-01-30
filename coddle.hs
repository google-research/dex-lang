import System.Console.Haskeline
import System.Exit
import System.IO hiding (print)
import Data.IORef
import Control.Monad
import Control.Monad.State.Strict
import Options.Applicative
import Data.Semigroup ((<>))
import Data.Maybe (catMaybes)
import Prelude hiding (lookup, print)

import Syntax
import Parser
import Typer
import Util
import Env

-- import Interpreter
-- import FlatType (exprToVal, cmdToVal, parseVal)

type TypedVal = ()  -- until we get the interpreter back up

type Driver a = InputT IO a
data CmdOpts = CmdOpts { programSource :: Maybe String
                       , dataSource    :: Maybe String }

data TopEnv = TopEnv { varEnv  :: Vars
                     , typeEnv :: FullEnv SigmaType ISet () ()
                     , valEnv  :: FullEnv TypedVal  () () () }


data Pass a b v i t s = Pass
  { lowerExpr ::         a -> FullEnv v i t s -> Except (v, b),
    lowerCmd  :: Command a -> FullEnv v i t s -> Command b }

varPass  = Pass checkBoundVarsExpr checkBoundVarsCmd
typePass = Pass inferTypesExpr inferTypesCmd
-- evalPass = Pass exprToVal cmdToVal
-- evalPass = Pass undefined undefined -- exprToVal cmdToVal

evalSource :: TopEnv -> String -> Driver TopEnv
evalSource env source = do
  decls <- liftErr "" $ parseProg source
  (checked, varEnv') <- fullPass (procDecl varPass)  (varEnv env) decls
  (typed, typeEnv')  <- fullPass (procDecl typePass) (typeEnv env) checked
  -- (final, valEnv')   <- fullPass (procDecl evalPass) (valEnv env)  typed
  -- mapM writeDeclResult final
  mapM writeDeclResult typed
  return $ TopEnv varEnv' typeEnv' undefined -- valEnv'
  where
    fullPass :: (IORef env -> TopDecl a -> Driver (TopDecl b))
                -> env -> [TopDecl a] -> Driver ([TopDecl b], env)
    fullPass p env decls = do envPtr <- lift $ newIORef env
                              decls' <- mapM (p envPtr) decls
                              env' <- lift $ readIORef envPtr
                              return (decls', env')

    procDecl :: Pass a b v i t s -> IORef (FullEnv v i t s)
                -> TopDecl a -> Driver (TopDecl b)
    procDecl (Pass procExpr procCmd) envPtr (TopDecl source fvs instr) = do
      env <- lift $ readIORef envPtr
      case instr of
        TopAssign v expr ->
          do (val, expr') <- liftErr source $ procExpr expr env
             lift $ writeIORef envPtr $ setLEnv (addFVar v val) env
             return $ TopDecl source fvs $ TopAssign v expr'
        EvalCmd cmd -> return $ TopDecl source fvs $ EvalCmd (procCmd cmd env)

runRepl :: TopEnv -> Driver ()
runRepl initEnv = lift (newIORef initEnv) >>= forever . catchErr . loop
  where
    loop :: IORef TopEnv -> Driver ()
    loop envPtr = do
      source <- getInputLine ">=> "
      env <- lift $ readIORef envPtr
      newEnv <- case source of
                  Nothing ->  lift exitSuccess
                  Just s -> evalSource env s
      lift $ writeIORef envPtr newEnv

writeDeclResult :: TopDecl a -> Driver ()
writeDeclResult (TopDecl source _ instr) = do
  case instr of
    EvalCmd (CmdResult s) -> printWithSource s
    EvalCmd (CmdErr e)    -> printWithSource (show e)
    _ -> return ()
  where printWithSource :: String -> Driver ()
        printWithSource s = outputStrLn $ source ++ "\n" ++ s ++ "\n"

liftErr :: String -> Except a -> Driver a
liftErr s (Left e)  = do outputStrLn $ "> " ++ s ++ "\n" ++ show e ++ "\n"
                         lift exitFailure
liftErr s (Right x) = return x

catchErr :: Driver a -> Driver (Maybe a)
catchErr m = handleInterrupt (return Nothing) (fmap Just m)

updateEnv :: (VarName, SigmaType, TypedVal) -> TopEnv -> TopEnv
updateEnv (v, t, val) (TopEnv varEnv typeEnv valEnv) =
  TopEnv { varEnv  = setLEnv (addFVar v ())  varEnv
         , typeEnv = setLEnv (addFVar v t)   typeEnv
         , valEnv  = setLEnv (addFVar v val) valEnv }

opts :: ParserInfo CmdOpts
opts = info (p <**> helper) mempty
  where p = CmdOpts
            <$> (optional $ argument str (    metavar "FILE"
                                           <> help "Source program"))
            <*> (optional $ strOption (    long "data"
                                        <> metavar "DATA"
                                        <> help "Data source (optional)" ))

runMonad :: Driver a -> IO ()
runMonad d = runInputTBehavior defaultBehavior defaultSettings d >> return ()

initEnv = TopEnv mempty mempty mempty

loadData :: String -> IO (TypedVal, SigmaType)
loadData fname = do
  contents <- readFile fname
  undefined
  -- case parseVal contents of
  --   Left e -> do putStrLn "Error loading data"
  --                putStrLn (show e)
  --                exitFailure
  --   Right (t,v) -> return (TypedVal t v, t)

main :: IO ()
main = do
  CmdOpts fname dbname <- execParser opts
  envWithData <- case dbname of
                   Just dbname ->
                     do (inVal, inTy) <- loadData dbname
                        return $ ("data", inTy, inVal) `updateEnv` initEnv
                   Nothing -> return initEnv
  case fname of
    Just fname -> runMonad $ lift (readFile fname) >>= evalSource envWithData
    Nothing    -> runMonad $ runRepl envWithData
