{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

module Dex2Jax where

import Foreign.C.String
import Data.Aeson
import GHC.Generics
import Data.ByteString.Lazy.Char8 (pack, unpack)
import System.Exit
import Control.Monad.State.Strict

import Syntax
import Parser
import PPrint
import Pass
import Type
import DeShadow
import Inference
import Record
import Env

foreign export ccall loadSource :: CString -> IO CString

type JName = String
data Jaxpr = Jaxpr [JName] [JEqn] [JAtom]  deriving (Generic, Show)
data JAtom = JVar JName                    deriving (Generic, Show)
data JEqn = JLet [JName] JExpr             deriving (Generic, Show)
data JExpr = PrimApp JPrim [JAtom]         deriving (Generic, Show)
data JPrim = Add | Mul                     deriving (Generic, Show)

declAsJaxpr :: TopDecl -> Except (String, Jaxpr)
declAsJaxpr (TopDecl (LetMono (RecLeaf (v:>_)) rhs)) = do
  jaxpr <- exprAsJaxpr rhs
  return (pprint v, jaxpr)
declAsJaxpr decl = throw CompilerErr $ "Can't compile to jaxpr: " ++ pprint decl

exprAsJaxpr :: Expr -> Except Jaxpr
exprAsJaxpr = undefined

fullPass :: TopPass UTopDecl TopDecl
fullPass = deShadowPass >+> typePass >+> checkTyped

loadSource :: CString -> IO CString
loadSource = callSerialized loadSource'

loadSource' :: String -> IO [(String, Jaxpr)]
loadSource' source = case fullPass of
  TopPass f -> do
    decls <- liftErrIO $ parseProg source
    decls' <- evalStateT (mapM (evalDecl source . f . snd) decls) mempty
    liftErrIO $ mapM declAsJaxpr decls'

liftErrIO :: Except a -> IO a
liftErrIO (Left e)  = putStrLn (pprint e) >> exitFailure
liftErrIO (Right x) = return x

evalDecl :: Monoid env => String -> TopPassM env TopDecl -> StateT env IO TopDecl
evalDecl source pass = do
  env <- get
  (ans, env') <- liftIO $ runTopPassM (printErr . resultText, source) env pass
  modify $ (<> env')
  case ans of Left e -> error (pprint e)
              Right decl -> return decl
  where
    printErr (Result _ status _ ) = case status of
      Set (Failed e) -> putStrLn $ pprint e
      _ -> return ()

instance ToJSON Jaxpr
instance ToJSON JAtom
instance ToJSON JEqn
instance ToJSON JExpr
instance ToJSON JPrim

instance FromJSON Jaxpr
instance FromJSON JAtom
instance FromJSON JEqn
instance FromJSON JExpr
instance FromJSON JPrim

callSerialized :: (ToJSON a, FromJSON a, ToJSON b, FromJSON b) =>
                    (a -> IO b) -> CString -> IO CString
callSerialized f arg = do
  arg' <- peekCString arg
  case eitherDecode (pack arg') of
    Left e -> do
      putStrLn $ "Can't decode:\n" ++ arg' ++ "\n" ++ e
      exitFailure
    Right arg'' -> do
      ans <- f arg''
      newCString $ unpack $ encode ans
