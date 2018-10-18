import System.Console.Haskeline
import System.Environment
import System.IO
import Control.Monad
import Control.Monad.IO.Class
import Data.List hiding (lookup)

import Prelude hiding (lookup)

import Interpreter
import Parser

evalLines :: Env -> VarEnv -> [String] -> String
evalLines env varEnv [] = show $ getOutVal env varEnv
evalLines env varEnv ("":lines) = evalLines env varEnv lines
evalLines env varEnv (line:lines) =
    case evalLine env varEnv line
        of Left (newValEnv, newVarEnv) ->
             line ++ "\n" ++ evalLines newValEnv newVarEnv lines


getOutVal :: Env -> VarEnv -> Val
getOutVal env varEnv =
  case lookup "out" varEnv
      of (Just i) -> env !! i

evalLine :: Env -> VarEnv -> String -> Either (Env, VarEnv) String
evalLine valEnv varEnv line =
  case parseLine line varEnv of
    Right p -> case p of
                  Left (v, e) -> Left (let ans = eval e valEnv (0, [])
                                       in (ans:valEnv, v:varEnv))
                  Right e -> Right . show $ eval e valEnv (0, [])
    Left e  -> error ("parse error in line:" ++ line ++ (show e))

splitString :: Char -> String -> [String]
splitString c s = case dropWhile (== c) s of
             ""   -> []
             rest -> prefix : splitString c rest'
                     where (prefix, rest') = break (== c) rest

evalMultiSource :: String -> String
evalMultiSource s = let results = map (evalLines builtinEnv builtinVars . lines) $ splitString '~' s
                    in concat $ intersperse "\n\n" results

repl :: IO ()
repl = runInputT defaultSettings (loop builtinEnv builtinVars)
  where
  loop env varEnv = do
    minput <- getInputLine "> "
    case minput of
      Nothing -> let ans =  show $ getOutVal env varEnv
                 in (liftIO (putStrLn ans)) >> return ()
      Just line -> case evalLine env varEnv line of
                      Left (newEnv, newVarEnv)  -> loop newEnv newVarEnv
                      Right s -> liftIO (putStrLn s) >> loop env varEnv


evalFile :: String -> IO ()
evalFile s = do
    source <- readFile s
    putStrLn $ evalMultiSource source
    return ()

main :: IO ()
main = do
  args <- getArgs
  case args of
    fname:[] -> evalFile fname
    []       -> repl
