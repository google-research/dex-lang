import System.Console.Haskeline
import System.IO
import System.Exit
import Data.IORef
import Control.Concurrent
import Control.Concurrent.Chan
import Control.Monad
import Control.Monad.Except (throwError)
import Control.Monad.State.Strict
import Options.Applicative
import Data.Semigroup ((<>))
import qualified Data.Map.Strict as M

import Syntax
import PPrint
import Pass
import Type

import Parser
import Inference
import DeFunc
import Imp
import JIT
import Fresh
import ConcurrentUtil

type DeclKey = Int
type Keyed a = (DeclKey, a)

data EvalMode = ReplMode | WebMode String | ScriptMode String
data CmdOpts = CmdOpts { programSource :: Maybe String
                       , webOutput     :: Bool}

fullPass :: MultiPass UDecl ()
fullPass = NilPass
   >+> typePass   >+> checkTyped
   >+> deFuncPass >+> checkTyped
   >+> impPass    >+> checkImp
   >+> jitPass

evalPrelude :: EvalState -> IO ()
evalPrelude evalState = do
  source <- readFile "prelude.cod"
  prog <- liftExceptIO (parseProg source)
  mapM_ (evalDecl evalState) (map snd prog)

evalScript :: String -> IO ()
evalScript fname = do
  evalState <- startEval fullPass
  evalPrelude evalState
  source <- readFile fname
  prog <- liftExceptIO (parseProg source)
  mapM_ (uncurry $ evalPrint evalState) prog

evalPrint :: EvalState -> String -> UDecl -> IO ()
evalPrint s text decl = do
  result <- evalDecl s decl
  case result of
    NoResult -> return ()
    _ -> putStr text >> putStrLn (pprint result)

evalRepl :: IO ()
evalRepl = do
  evalState <- startEval fullPass
  evalPrelude evalState
  runInputT defaultSettings $ forever (replLoop evalState)

replLoop :: EvalState -> InputT IO ()
replLoop evalState = do
  source <- getInputLine ">=> "
  case source of
    Nothing -> lift exitSuccess
    Just s -> case parseTopDecl s of
                Left err -> outputStrLn (pprint err)
                Right decl -> lift $ evalPrint evalState "" decl

evalWeb :: String -> IO ()
evalWeb fname = undefined

opts :: ParserInfo CmdOpts
opts = info (p <**> helper) mempty
  where p = CmdOpts
            <$> (optional $ argument str (    metavar "FILE"
                                           <> help "Source program"))
            <*> switch (    long "web"
                         <> help "Whether to use web output instead of stdout" )

parseOpts :: IO EvalMode
parseOpts = do
  CmdOpts file web <- execParser opts
  return $ case file of
    Nothing -> ReplMode
    Just fname -> if web then WebMode    fname
                         else ScriptMode fname

main :: IO ()
main = do
  evalMode <- parseOpts
  case evalMode of
    ReplMode         -> evalRepl
    ScriptMode fname -> evalScript fname
    WebMode    fname -> evalWeb fname
