-- Copyright 2025 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

import Prelude hiding (readFile)
import Control.Monad

import Proto

-- === AST ===

data Expr =
    Occ Name
  | App Expr [Expr]
  | Lam LamExpr
  | Let [Decl] Expr
  | Prim Prim

data Prim = Add | Mul | Lit Int

type Binder = Name
data Decl = Decl Binder Expr
data LamExpr = LamExpr [Binder] Expr

-- === top level ===

data CmdlineArgs =
   Test FilePath
 | Script FilePath Config

data Config = Config

data TopCtx = TopCtx
  { config :: Config }

configParser :: ArgParser Config
configParser = pure Config

argParser :: ArgParser CmdlineArgs
argParser = SubCommands [
  ("test", Test <$> PositionalArg StringOption),
  ("script", Script <$> PositionalArg StringOption <*> configParser)]

type TopM = ProtoM TopCtx

main :: IO ()
main = do
  let ctx = TopCtx Config
  void $ runProtoM ctx $ parseArgsIO argParser >>= \case
    Test source -> do
      tests <- readFile source >>= parseTestFile
      forM tests.cases \test -> runTest test runSnippet
    Script _ _ -> undefined

runSnippet :: ByteString -> TopM ()
runSnippet source = do
  tree <- runParser source
  ast <- toAST tree
  ans <- evalExprTop ast
  logM $ oneLiner $ show ans

-- === printer ===

-- TODO: make this work from ParseTree

instance Show Val where
  show = \case
    ConstVal v -> show v
    Closure _ _-> "<function>"

instance Show Expr where
  show = \case
    Occ v -> v
    -- App f args -> show f <> parens (showSep (map show args) ", ")
    -- Lam (LamExpr bs expr) -> parens $
    --   "\\" <> parens (showSep (map Line bs) ", ") <> "->" <> show expr
    Let _ _ -> undefined
    Prim p -> show p

instance Show Prim where
  show = \case
    Add -> "(+)"
    Mul -> "(*)"
    Lit x -> show x

-- === abstract syntax ===

toAST :: ParseTreeAnn -> ProtoM c Expr
toAST t = case t.val of
  InfixOp x _ op _ y -> case op of
    Symbol s -> case s of
      "*" -> primOp Mul [x, y]
      "+" -> primOp Add [x, y]
      _ -> undefined
    _ -> throw $ oneLiner "no good"
  Parens _ _ tree _ _ -> toAST tree
  Leaf t -> case t of
    Identifier _ -> undefined
    IntLit x -> return $ Prim (Lit x)
    _ -> throw $ oneLiner "unexpected thingy"
  ParseError e tree _ _ _ ->
    throw $ oneLiner "Parse error"
  where
    primOp :: Prim -> [ParseTreeAnn] -> ProtoM c Expr
    primOp prim args = App (Prim prim) <$> mapM toAST args

-- === interpreter ===

data InterpCtx = InterpCtx {
  env :: Env Val }
type InterpM = ProtoM InterpCtx

data Val = ConstVal Prim | Closure (Env Val) LamExpr

evalExprTop :: Expr -> ProtoM c Val
evalExprTop expr = liftProtoM (const $ InterpCtx mempty) $ evalExpr expr

query :: Name -> InterpM (Maybe Val)
query = undefined

update :: Name -> Val -> InterpM ()
update = undefined

withEnv :: Env Val -> InterpM a -> InterpM a
withEnv = undefined

enterScope :: InterpM a -> InterpM a
enterScope = undefined

evalExpr :: Expr -> InterpM Val
evalExpr = \case
  Occ v -> query v >>= \case
    Nothing -> error "unbound variable"
    Just val -> return val
  App f args -> do
    f' <- evalExpr f
    args' <- mapM evalExpr args
    case f' of
      Closure env (LamExpr bs body) -> do
        withEnv env do
          zipWithM_ update bs args'
          evalExpr body
      ConstVal prim -> case prim of
        Add -> evalBinop (+) args'
        Mul -> evalBinop (*) args'
        _ -> undefined
      _ -> undefined
  Lam lam -> do
    ctx <- getCtx
    return $ Closure ctx.env lam
  Let decls body -> enterScope do
    forM_ decls \(Decl b rhs) -> do
      val <- evalExpr rhs
      update b val
    evalExpr body
  Prim prim -> return $ ConstVal prim

evalBinop :: (Int -> Int -> Int) -> [Val] -> InterpM Val
evalBinop f args = do
  (x, y) <- assumePair args
  x' <- assumeLit x
  y' <- assumeLit y
  return $ ConstVal $ Lit $ f x' y'

assumePair :: [Val] -> InterpM (Val, Val)
assumePair = \case
  [x, y] -> return (x, y)
  _ -> error "oops"

assumeLit :: Val -> InterpM Int
assumeLit = \case
  ConstVal (Lit n) -> return n
  _ -> error "Expected a literal"

assumeClosure :: Val -> InterpM (Env Val, LamExpr)
assumeClosure = \case
  Closure env lam -> return (env, lam)
  _ -> error "Expected a closure"
