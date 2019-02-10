{-# LANGUAGE OverloadedStrings #-}

module JIT (lowerLLVM, showLLVM, evalJit, Compiled, jitExpr, jitCmd) where

import Control.Monad
import Control.Monad.Except (throwError)
import Control.Monad.Reader (ReaderT, runReaderT, local, ask, asks)
import Control.Monad.State (StateT, execStateT, put, get, gets, modify)

import qualified Data.Map.Strict as M
import Data.Foldable (toList)

import qualified LLVM.AST as L
import qualified LLVM.AST.Type as L
import qualified LLVM.AST.Global as L
import qualified LLVM.AST.Float as L
import qualified LLVM.AST.IntegerPredicate as L
import qualified LLVM.AST.Constant as C
import qualified LLVM.Module as Mod
import qualified LLVM.Analysis as Mod
import qualified LLVM.ExecutionEngine as EE
import LLVM.Internal.Context

import Data.Int
import Foreign.Ptr hiding (Ptr)
import Data.ByteString.Char8 (unpack)

import Typer
import Syntax
import Env

foreign import ccall "dynamic" haskFun :: FunPtr Int64 -> Int64

type Compiled = L.Module
type JitType = GenType NumElems
type JitEnv = FullEnv CompileVal JitType

data CompileVal = ScalarVal BaseType Operand
                | IdxVal Long
                | TabVal Table JitType
                | LamVal  JitEnv Expr
                | TLamVal JitEnv Expr
                | BuiltinLam BuiltinFun [JitType] [CompileVal]
                | ExPackage NumElems CompileVal

type Operand = L.Operand
type Block = L.BasicBlock
type Instr = L.Named L.Instruction

data Table = Table CharPtr NumElems Sizes
data Sizes = ConstSize Int | UniformSize ElemSize | ManySizes CharPtr

newtype CharPtr = CharPtr Operand
newtype LongPtr = LongPtr Operand
newtype Long = Long Operand

type NumElems = Long
type ElemSize = Long
type Index    = Long

type CompileApp  = [JitType] -> [CompileVal] -> CompileM CompileVal
data BuiltinFun  = BuiltinFun Int Int CompileApp

data CompileState = CompileState { nameCounter :: Int
                                 , curBlocks :: [Block]
                                 , curInstrs :: [Instr]
                                 , varDecls  :: [Instr]
                                 , curBlockName :: L.Name }

type CompileM a = ReaderT JitEnv (StateT CompileState (Either Err)) a

jitExpr :: Expr -> FullEnv () () -> IO ((), ())
jitExpr expr env = return ((),())

jitCmd :: Command Expr -> FullEnv () () -> IO (Command ())
jitCmd (Command cmdName expr) env = case cmdName of
    GetLLVM -> case lowerLLVM expr of
                 Left e -> return $ CmdErr e
                 Right m -> liftM CmdResult (showLLVM m)
    EvalExpr -> case lowerLLVM expr of
                 Left e -> return $ CmdErr e
                 Right m -> liftM CmdResult (evalJit m)
    _ -> return $ Command cmdName ()

jitCmd (CmdResult s) _ = return $ CmdResult s
jitCmd (CmdErr e)    _ = return $ CmdErr e

lowerLLVM :: Expr -> Except L.Module
lowerLLVM expr = do
  blocks <- runCompileM builtinEnv (compileModule expr)
  return (makeModule blocks)

showLLVM :: L.Module -> IO String
showLLVM m = withContext $ \c ->
               Mod.withModuleFromAST c m $ \m ->
                 fmap unpack $ Mod.moduleLLVMAssembly m

evalJit :: L.Module -> IO String
evalJit m =
  withContext $ \c ->
    Mod.withModuleFromAST c m $ \m -> do
      jit c $ \ee ->
        EE.withModuleInEngine ee m $ \eee -> do
          fn <- EE.getFunction eee (L.Name "thefun")
          case fn of
            Just fn -> do let x = show $ runJitted fn
                          putStr $ x `seq` ""  -- segfaults without this
                          return x
            Nothing -> return "Failed - couldn't find function"

makeModule :: [Block] -> L.Module
makeModule blocks = mod
  where
    mod = L.defaultModule { L.moduleName = "test"
                          , L.moduleDefinitions = [L.GlobalDefinition fundef] }
    fundef = L.functionDefaults { L.name        = L.Name "thefun"
                                , L.parameters  = ([], False)
                                , L.returnType  = longTy
                                , L.basicBlocks = blocks }

runCompileM :: JitEnv -> CompileM a -> Except [Block]
runCompileM env m = do
  CompileState _ blocks [] [] _ <- execStateT (runReaderT m env) initState
  return $ reverse blocks
  where initState = CompileState 0 [] [] [] (L.Name "main_block")

runJitted :: FunPtr a -> Int64
runJitted fn = haskFun (castFunPtr fn :: FunPtr Int64)

jit :: Context -> (EE.MCJIT -> IO a) -> IO a
jit c = EE.withMCJIT c (Just 3) Nothing Nothing Nothing

compileModule :: Expr -> CompileM ()
compileModule expr = compile expr >>= finalReturn

compile :: Expr -> CompileM CompileVal
compile expr = case expr of
  Lit x -> return (litVal x)
  Var v -> asks $ (! v) . lEnv
  Let _ bound body -> do x <- compile bound
                         local (setLEnv $ addBVar x) (compile body)
  Lam a body -> do { env <- ask; return (LamVal env body) }
  App e1 e2  -> do
    f <- compile e1
    x <- compile e2
    case f of
      LamVal env body -> withEnv (setLEnv (addBVar x) env) (compile body)
      BuiltinLam builtin ts vs -> compileBuiltin builtin ts (x:vs)
  For a body -> do { t <- compileType a; compileFor t body }
  Get e ie -> do x <- compile e
                 IdxVal i <- asks $ (! ie) . lEnv
                 compileGet x i
  TLam kinds body -> do { env <- ask; return (TLamVal env body) }
  TApp e ts -> do
    f <- compile e
    ts' <- mapM compileType ts
    case f of
      TLamVal env body -> withEnv (setTEnv (addBVars ts') env) (compile body)
      BuiltinLam builtin [] vs -> compileBuiltin builtin ts' vs
  Unpack bound body -> do
    ExPackage i x <- compile bound
    let updateEnv = setLEnv (addBVar x) . setTEnv (addBVar (Meta i))
    local updateEnv (compile body)

  where
    withEnv :: JitEnv -> CompileM a -> CompileM a
    withEnv env = local (const env)

compileType :: Type -> CompileM JitType
compileType ty = do env <- asks (bVars . tEnv)
                    return $ instantiateBody (map Just env) (noLeaves ty)

compileBuiltin :: BuiltinFun -> [JitType] -> [CompileVal] -> CompileM CompileVal
compileBuiltin b@(BuiltinFun numTypes numArgs compileRule) types args =
    if length types < numTypes || length args < numArgs
      then return $ BuiltinLam b types args
      else compileRule types args

compileFor :: JitType -> Expr -> CompileM CompileVal
compileFor (Meta n) forBody = do
  tab@(Table ptr _ _) <- newTable n
  let body iPtr = do i <- loadCell iPtr
                     let updateEnv = setLEnv $ addBVar (IdxVal i)
                     bodyVal <- local updateEnv $ compile forBody
                     writeTable tab i bodyVal
  addForILoop n body
  return $ TabVal (Table ptr n (ConstSize 8)) (BaseType IntType)

compileGet :: CompileVal -> Long -> CompileM CompileVal
compileGet (TabVal tab elemTy) i = readTable tab i

litVal :: LitVal -> CompileVal
litVal lit = case lit of
  IntLit  x -> ScalarVal IntType  $ L.ConstantOperand $ C.Int 64 (fromIntegral x)
  RealLit x -> ScalarVal RealType $ L.ConstantOperand $ C.Float (L.Double x)

-- --- utilities ---

addLoop :: CompileM Long -> CompileM a -> CompileM a
addLoop cond body = do block <- newBlock  -- TODO: handle zero iters case
                       val <- body
                       c <- cond
                       maybeLoop c block
                       return val

newBlock :: CompileM L.Name
newBlock = do next <- freshName
              finishBlock (L.Br next []) next
              return next

maybeLoop :: Long -> L.Name -> CompileM ()
maybeLoop (Long c) loop = do next <- freshName
                             finishBlock (L.CondBr c loop next []) next

addForILoop :: Long -> (LongPtr -> CompileM ()) -> CompileM ()
addForILoop n body = do
  i <- newIntCell 0
  let cond  = loadCell i >>= (`lessThan` n)
      body' = body i >> inc i
  addLoop cond body'
  where inc i = updateCell i $ add (litInt 1)

compileSum :: [JitType] -> [CompileVal] -> CompileM CompileVal
compileSum [Meta _] [TabVal tab@(Table ptr n sizes) _] = do
  sum <- newIntCell 0
  let body iPtr = do i <- loadCell iPtr
                     ScalarVal _ x <- readTable tab i
                     updateCell sum (add (Long x))
  addForILoop n body
  (Long ans) <- loadCell sum
  return $ ScalarVal IntType ans

-- TODO: add var decls
finalReturn :: CompileVal -> CompileM ()
finalReturn (ScalarVal _ ret) = finishBlock (L.Ret (Just ret) []) (L.Name "")

appendInstr :: Instr -> CompileM ()
appendInstr instr = modify updateState
  where updateState state = state {curInstrs = instr : curInstrs state}

freshName :: CompileM L.Name
freshName = do i <- gets nameCounter
               modify (\state -> state {nameCounter = i + 1})
               return $ L.UnName (fromIntegral i)

finishBlock :: L.Terminator -> L.Name -> CompileM ()
finishBlock term newName = do
  CompileState count blocks instrs decls oldName <- get
  let newBlock = L.BasicBlock oldName (reverse instrs) (L.Do term)
  put $ CompileState count (newBlock:blocks) [] decls newName

evalInstr :: L.Type -> L.Instruction -> CompileM Operand
evalInstr ty instr = do
  x <- freshName
  appendInstr $ x L.:= instr
  return $ L.LocalReference ty x

litInt :: Int -> Long
litInt x = Long $ L.ConstantOperand $ C.Int 64 (fromIntegral x)

add :: Long -> Long -> CompileM Long
add (Long x) (Long y) = liftM Long $ evalInstr longTy $ L.Add False False x y []

newIntCell :: Int -> CompileM LongPtr
newIntCell x = do
  ptr <- liftM LongPtr $ evalInstr longTy $
           L.Alloca longTy Nothing 0 [] -- TODO: add to top block!
  writeCell ptr (litInt x)
  return ptr

loadCell :: LongPtr -> CompileM Long
loadCell (LongPtr ptr) =
  liftM Long $ evalInstr longTy $ L.Load False ptr Nothing 0 []

writeCell :: LongPtr -> Long -> CompileM ()
writeCell (LongPtr ptr) (Long x) =
  appendInstr $ L.Do $ L.Store False ptr x Nothing 0 []

updateCell :: LongPtr -> (Long -> CompileM Long) -> CompileM ()
updateCell ptr f = loadCell ptr >>= f >>= writeCell ptr

newTable :: NumElems -> CompileM Table
newTable n@(Long op) = do
  ptr <- evalInstr intPtrTy $ L.Alloca longTy (Just op) 0 []
  return $ Table (CharPtr ptr) n (ConstSize 8)

readTable :: Table -> Index -> CompileM CompileVal
readTable t idx = do CharPtr ptr <- arrayPtr t idx
                     Long ans <- loadCell (LongPtr ptr)
                     return $ ScalarVal IntType ans

writeTable :: Table -> Index -> CompileVal -> CompileM ()
writeTable tab idx val =
  case val of
    ScalarVal IntType val' -> do (CharPtr ptr) <- arrayPtr tab idx
                                 writeCell (LongPtr ptr) (Long val')

arrayPtr :: Table -> Index -> CompileM CharPtr
arrayPtr (Table (CharPtr ptr) _ _ ) (Long idx) =
  liftM CharPtr $ evalInstr intPtrTy $ L.GetElementPtr False ptr [idx] []

lessThan :: Long -> Long -> CompileM Long
lessThan (Long x) (Long y) = liftM Long $ evalInstr longTy $ L.ICmp L.SLT x y []

intPtrTy = L.ptr longTy
longTy = L.IntegerType 64
realTy = L.FloatingPointType L.DoubleFP

-- --- builtins ---

builtinEnv :: JitEnv
builtinEnv = FullEnv builtins mempty

builtins :: Env Var CompileVal
builtins = newEnv
  [ ("add" , asBuiltin 0 2 $ compileBinop (\x y -> L.Add False False x y []))
  , ("mul" , asBuiltin 0 2 $ compileBinop (\x y -> L.Mul False False x y []))
  , ("sub" , asBuiltin 0 2 $ compileBinop (\x y -> L.Sub False False x y []))
  , ("iota", asBuiltin 0 1 $ compileIota)
  , ("sum" , asBuiltin 1 1 $ compileSum)
  ]

compileIota :: CompileApp
compileIota [] [ScalarVal b nOp] = do
  tab@(Table ptr _ _) <- newTable n
  let body iPtr = do (Long i) <- loadCell iPtr
                     writeTable tab (Long i) (ScalarVal IntType i)
  addForILoop n body
  return $ ExPackage n (TabVal tab (BaseType IntType))
  where n = Long nOp

asBuiltin :: Int -> Int -> CompileApp -> CompileVal
asBuiltin nt nv f = BuiltinLam (BuiltinFun nt nv f) [] []

compileBinop :: (Operand -> Operand -> L.Instruction) -> CompileApp
compileBinop makeInstr = compile
  where
    compile :: CompileApp
    compile [] [ScalarVal _ x, ScalarVal _ y] = liftM (ScalarVal IntType) $
        evalInstr longTy (makeInstr y x)
