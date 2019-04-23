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
import Type

import Parser
import Inference
import DeFunc
import Imp
import JIT

import Debug.Trace

data EvalMode = ReplMode | WebMode String | ScriptMode String
data CmdOpts = CmdOpts { programSource :: Maybe String
                       , webOutput     :: Bool}

evalScript :: String -> IO ()
evalScript fname = do
  prelude <- readFile "prelude.cod"
  source <- readFile fname
  prog <- liftExceptIO $ parseProg (prelude ++ source)
  output <- do
    typed  <- pass typePass   prog
    _      <- pass checkTyped typed
    deFunc <- pass deFuncPass typed
    _      <- pass checkTyped deFunc
    imp    <- pass impPass    deFunc
    _      <- pass checkImp   imp
    ans    <- pass jitPass    imp
    return ans
  void $ mapM (putStrLn . formatOut . fst) output
  where formatOut outs = case outs of [_] -> ""
                                      _ -> concat outs ++ "\n"

pass :: Monoid env => (a -> TopMonadPass env b)
                   -> [([String], a)]
                   -> IO [([String], b)]
pass f decls = evalStateT (mapM procDecl decls) mempty
  where procDecl (s,x) = do
          env <- get
          (result, s') <- liftIO $ runTopMonadPass env (f x)
          let s'' = s <> s'
          (x', env') <- liftExceptIO $ addErrMsg (concat s'') result
          put $ env <> env'
          return (s'', x')

evalWeb :: String -> IO ()
evalWeb fname = undefined

evalRepl :: IO ()
evalRepl = undefined

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
