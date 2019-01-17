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

type TopMonad a = InputT IO a
type Except a = Either String a
type ProgramSource = String
type DataSource = String
data CmdOpts = CmdOpts (Maybe ProgramSource) (Maybe DataSource)

type MonadPass v a b = TopDecl a -> FreeEnv v -> TopMonad (v, TopDecl b)
type MonadPassEnv v a b =    IORef (FreeEnv v) -> TopDecl a
                          -> TopMonad (Maybe (TopDecl b))
data Env = Env { varEnv  :: FreeEnv ()
               , typeEnv :: FreeEnv SigmaType
               , valEnv  :: FreeEnv I.TypedVal }

withTopMonad :: Pass v a b -> MonadPass v a b
withTopMonad (Pass applyPass evalCmd) (TopDecl source decl) env = do
  case decl of
    EvalDecl v expr -> do
      (val, expr') <- liftErr source $ applyPass expr env
      return (val, TopDecl source $ EvalDecl v expr')
    EvalCmd cmd expr -> do
      (val, expr') <- liftErr source $ applyPass expr env
      case evalCmd cmd val expr' of
        Just s  -> do outputStrLn source
                      outputStrLn (s ++ "\n")
                      throwIO Interrupt
        Nothing -> return (val, TopDecl source $ EvalCmd cmd expr')

liftErr :: String -> Except a -> TopMonad a
liftErr s (Left e)  = outputStrLn (s ++ "\n" ++ e ++ "\n") >> throwIO Interrupt
liftErr s (Right x) = return x

repl :: Env -> TopMonad ()
repl initEnv = lift (newIORef initEnv) >>= forever . catchErr . loop
  where
    loop :: IORef Env -> TopMonad ()
    loop envPtr = do
      input <- getInputLine ">=> "
      decl <- case input of Nothing -> lift $ exitSuccess
                            Just line -> liftErr "" $ P.parseCommand line
      env <- lift $ readIORef envPtr
      ((), lowered) <- withTopMonad L.lowerPass decl    (varEnv  env)
      (ty, typed)   <- withTopMonad typePass    lowered (typeEnv env)
      (val, _)      <- withTopMonad F.evalPass  typed   (valEnv  env)
      case decl of
        TopDecl _ (EvalDecl v _) -> let newEnv = consEnv (v, ty, val) env
                                    in lift $ writeIORef envPtr newEnv
        _ -> return ()

consEnv :: (VarName, SigmaType, I.TypedVal) -> Env -> Env
consEnv (var, t, val) (Env varEnv typeEnv valEnv) =
  Env { varEnv  = updateFreeEnv varEnv  var ()
      , typeEnv = updateFreeEnv typeEnv var t
      , valEnv  = updateFreeEnv valEnv  var val }

catchErr :: TopMonad a -> TopMonad (Maybe a)
catchErr m = handleInterrupt (return Nothing) (fmap Just m)

evalFile :: String -> Env -> TopMonad ()
evalFile fname env = do
  source <- lift $ readFile fname
  decls <- liftErr "" $ P.parseProg source
  lowerDecls <- fullPass L.lowerPass (varEnv env)  decls
  typedDecls <- fullPass typePass    (typeEnv env) lowerDecls
  _          <- fullPass F.evalPass  (valEnv env)  typedDecls
  return ()

fullPass :: Pass v a b -> FreeEnv v -> [TopDecl a] -> TopMonad [TopDecl b]
fullPass pass env decls = do
  envPtr <- lift $ newIORef env
  newMaybeDecls <- sequence $ map (passWithEnv pass envPtr) decls
  return $ catMaybes newMaybeDecls

passWithEnv :: Pass v a b -> MonadPassEnv v a b
passWithEnv pass envPtr declWithSource@(TopDecl source decl) = do
  env <- lift $ readIORef envPtr
  ans <- catchErr $ (withTopMonad pass) declWithSource env
  case decl of
    EvalDecl v expr -> case ans of
      Nothing -> lift exitFailure
      Just (val, decl') -> do lift $ writeIORef envPtr (updateFreeEnv env v val)
                              return $ Just decl'
    EvalCmd _ _ -> case ans of
      Nothing           -> return Nothing
      Just (val, decl') -> return $ Just decl'

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

runMonad :: TopMonad() -> IO ()
runMonad = runInputTBehavior defaultBehavior defaultSettings

main :: IO ()
main = do
  CmdOpts fname dbname <- execParser opts
  (inVal, inTy) <- case dbname of
                     Just dbname -> loadData dbname
                     Nothing -> return (I.unitVal, unitType)
  let envWithData = ("data", inTy, inVal) `consEnv` initEnv
  case fname of
    Just fname -> runMonad $ evalFile fname envWithData
    Nothing    -> runMonad $ repl envWithData
