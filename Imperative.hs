module Imperative (exprToImp) where
import Control.Monad.Reader (ReaderT, runReaderT, local, ask, asks)
import Control.Monad.State (StateT, evalStateT, put, get)


import Syntax
import Env

type ImpEnv = FullEnv () ()

type ImpM a = ReaderT ImpEnv (StateT ImpState (Either Err)) a

data ImpVal = ScalarVal VarName
              -- | IdxVal w w
              -- | TabVal (Table w)
              -- | LamVal (RecTree Type)  (JitEnv w) Expr
              -- | RecVal (Record (JitVal w))
              -- | TLamVal [Kind] (JitEnv w) Expr
              -- | BuiltinLam Builtin [JitType w] [JitVal w]
              -- | ExPackage w (JitVal w)  deriving (Show)

data ImpState = ImpState { impCounter :: Int
                         , impStatements :: [Statement] }

exprToImp :: Expr -> ImpEnv -> ImpProgram
exprToImp = undefined


toImp :: Expr -> ImpVal -> ImpM ()
toImp expr val = case expr of
  Lit x -> case val of
             ScalarVal v -> write $ Assignment v [] ImpId [ImpLit x]


write :: Statement -> ImpM ()
write = undefined

-- -- to go in syntax
-- ImpProgram (..), Statement (..), ImpBuiltin (..), ImpOperand (..),
-- data ImpProgram = ImpProgram [Statement]

-- data Statement = Assignment VarName [Index] ImpBuiltin [ImpOperand]
--                | VarAlloc VarName BaseType [Size]
--                | VarFree  VarName
--                | Loop Index Size [Statement]

-- data ImpOperand = ImpLit LitVal
--                 | ImpVar VarName [Index]

-- type Index = VarName
-- data Size = ConstSize Int | KnownSize VarName

-- data ImpBuiltin = ImpId
--                 | ScalarOp Builtin

