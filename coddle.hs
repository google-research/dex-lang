import System.Exit
import System.IO
import Data.IORef
import Control.Concurrent
import Control.Concurrent.Chan
import Control.Monad
import Control.Monad.Except (throwError)
import Control.Monad.State.Strict
import Options.Applicative
import Data.Semigroup ((<>))

import Syntax
import PPrint
import Pass

import Parser
import Inference
import DeFunc
import Imp
import JIT

data EvalMode = ReplMode | WebMode String | ScriptMode String
data CmdOpts = CmdOpts { programSource :: Maybe String
                       , webOutput     :: Bool}

evalScript :: String -> IO ()
evalScript fname = do
  source <- readFile fname
  prog <- liftExceptIO $ parseProg source
  output <-      fullPass typePass prog
             >>= fullPass deFuncPass
             >>= fullPass impPass
             >>= fullPass jitPass
  void $ mapM (putStrLn . formatOut . fst) output
  where formatOut outs = case outs of [_] -> ""
                                      _ -> concat outs ++ "\n"

fullPass :: Monoid env => (a -> TopMonadPass env b)
                       -> [([String], a)]
                       -> IO [([String], b)]
fullPass f decls = evalStateT (mapM procDecl decls) mempty
  where procDecl (s,x) = do
          env <- get
          result <- liftIO $ runTopMonadPass env (f x)
          ((x', env'), s') <- liftIO $ liftExceptIO result
          put $ env <> env'
          return (s <> s', x')

evalWeb :: String -> IO ()
evalWeb fname = undefined

evalRepl :: IO ()
evalRepl = undefined

liftExceptIO :: Except a -> IO a
liftExceptIO (Left e) = die (pprint e)
liftExceptIO (Right x) = return x

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
