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
import qualified LLVM.AST.CallingConvention as L
import qualified LLVM.Module as Mod
import qualified LLVM.Analysis as Mod
import qualified LLVM.ExecutionEngine as EE
import LLVM.Internal.Context
import LLVM.Pretty (ppllvm)

import Data.Int
import Foreign.Ptr hiding (Ptr)
import qualified Data.Text.Lazy as DT
import Data.ByteString.Char8 (unpack)
import Data.ByteString.Short (ShortByteString)

import Data.Time.Clock (getCurrentTime, diffUTCTime)

import Typer
import Syntax
import Env
import Util

import Debug.Trace

foreign import ccall "dynamic" haskFun :: FunPtr Int64 -> Int64

type Compiled = L.Module
type JitType = GenType NumElems
type JitEnv = FullEnv CompileVal JitType

data CompileVal = ScalarVal BaseType Operand
                | IdxVal NumElems Index
                | TabVal Table
                | LamVal   Type  JitEnv Expr
                | TLamVal [Kind] JitEnv Expr
                | BuiltinLam BuiltinFun [JitType] [CompileVal]
                | ExPackage NumElems CompileVal

type BString = ShortByteString
type Operand = L.Operand
type Block = L.BasicBlock
type Instr = L.Named L.Instruction

data Table = Table ScalarPtr NumElems Sizes JitType
data Sizes = ConstSize ElemSize | ManySizes LongPtr

newtype ScalarPtr = ScalarPtr Operand
newtype LongPtr = LongPtr Operand
newtype Long = Long Operand   deriving (Show)

type NumElems = Long
type ElemSize = Long
type Index    = Long

type CompileApp  = [JitType] -> [CompileVal] -> CompileM CompileVal
data BuiltinFun  = BuiltinFun Int Int CompileApp JitType

data CompileState = CompileState { nameCounter :: Int
                                 , curBlocks :: [Block]
                                 , curInstrs :: [Instr]
                                 , varDecls  :: [Instr]
                                 , curBlockName :: L.Name }

data ExternFunSpec = ExternFunSpec BString L.Type [L.Type] [BString]

type CompileM a = ReaderT JitEnv (StateT CompileState (Either Err)) a

jitExpr :: Expr -> FullEnv () () -> IO ((), ())
jitExpr expr env = return ((),())

jitCmd :: Command Expr -> FullEnv () () -> IO (Command ())
jitCmd (Command cmdName expr) env = case cmdName of
    GetLLVM -> case lowerLLVM expr of
                 Left e -> return $ CmdErr e
                 Right m -> liftM CmdResult (showLLVM m)
                 -- Right m -> return $ CmdResult (DT.unpack $ ppllvm m)
    EvalExpr -> case lowerLLVM expr of
                 Left e -> return $ CmdErr e
                 Right m -> liftM CmdResult (evalJit m)
    TimeIt -> case lowerLLVM expr of
                 Left e -> return $ CmdErr e
                 Right m -> do
                   t1 <- getCurrentTime
                   ans <- evalJit m
                   t2 <- getCurrentTime
                   return $ CmdResult (show (t2 `diffUTCTime` t1))
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
                          , L.moduleDefinitions =
                              [ externDecl doubleFun
                              , externDecl mallocFun
                              , externDecl memcpyFun
                              , externDecl hashFun
                              , externDecl randFun
                              , externDecl randIntFun
                              , L.GlobalDefinition fundef] }
    fundef = L.functionDefaults { L.name        = L.Name "thefun"
                                , L.parameters  = ([], False)
                                , L.returnType  = longTy
                                , L.basicBlocks = blocks }

externDecl :: ExternFunSpec -> L.Definition
externDecl (ExternFunSpec fname retTy argTys argNames) =
  L.GlobalDefinition $ L.functionDefaults {
    L.name        = L.Name fname
  , L.parameters  = ([L.Parameter t (L.Name s) []
                     | (t, s) <- zip argTys argNames], False)
  , L.returnType  = retTy
  , L.basicBlocks = []
  }

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
  Lam a body -> do { env <- ask; return (LamVal a env body) }
  App e1 e2  -> do
    f <- compile e1
    x <- compile e2
    case f of
      LamVal _ env body -> withEnv (setLEnv (addBVar x) env) (compile body)
      BuiltinLam builtin ts vs -> compileBuiltin builtin ts (x:vs)
  For a body -> do (Meta n) <- compileType a
                   TabType _ bodyTy <- getType expr
                   compileFor n bodyTy body
  Get e ie -> do x <- compile e
                 IdxVal _ i <- asks $ (! ie) . lEnv
                 compileGet x i
  TLam kinds body -> do { env <- ask; return (TLamVal kinds env body) }
  TApp e ts -> do
    f <- compile e
    ts' <- mapM compileType ts
    case f of
      TLamVal _ env body -> withEnv (setTEnv (addBVars ts') env) (compile body)
      BuiltinLam builtin [] vs -> compileBuiltin builtin ts' vs
  Unpack bound body -> do
    ExPackage i x <- compile bound
    let updateEnv = setLEnv (addBVar x) . setTEnv (addBVar (Meta i))
    local updateEnv (compile body)

  where
    withEnv :: JitEnv -> CompileM a -> CompileM a
    withEnv env = local (const env)

    getType :: Expr -> CompileM JitType
    getType expr = do { env <- ask; return (exprType env expr) }

exprType :: JitEnv -> Expr -> JitType
exprType (FullEnv lenv tenv) expr = joinType $ getType env' expr
  where lenv' = fmap (fmap Meta . typeOf) lenv
        env' = FullEnv lenv' tenv

typeOf :: CompileVal -> JitType
typeOf val = case val of
  ScalarVal b _ -> BaseType b
  IdxVal n _ -> Meta n
  TabVal (Table _ n _ valTy) -> TabType (Meta n) valTy
  LamVal a env expr      -> exprType env (Lam a expr)
  TLamVal kinds env expr -> exprType env (TLam kinds expr)
  BuiltinLam (BuiltinFun nt nv _ ty) ts vs ->
    composeN (length vs) arrRHS $ instantiateType ts ty
  where arrRHS :: JitType -> JitType
        arrRHS (ArrType _ ty) = ty


compileType :: Type -> CompileM JitType
compileType ty = do env <- asks (bVars . tEnv)
                    return $ instantiateBody (map Just env) (noLeaves ty)

compileBuiltin :: BuiltinFun -> [JitType] -> [CompileVal] -> CompileM CompileVal
compileBuiltin b@(BuiltinFun numTypes numArgs compileRule _) types args =
    if length types < numTypes || length args < numArgs
      then return $ BuiltinLam b types args
      else compileRule types args

compileFor :: NumElems -> JitType -> Expr -> CompileM CompileVal
compileFor n bodyTy forBody = do
  tab <- newTable bodyTy n
  let body iPtr = do i <- loadCell iPtr
                     let updateEnv = setLEnv $ addBVar (IdxVal n i)
                     bodyVal <- local updateEnv $ compile forBody
                     writeTable tab i bodyVal
  addForILoop n body
  return $ TabVal tab


compileGet :: CompileVal -> Index -> CompileM CompileVal
compileGet (TabVal tab) i = readTable tab i

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

addForILoop :: Long -> (LongPtr -> CompileM a) -> CompileM a
addForILoop n body = do
  i <- newIntCell 0
  let cond  = loadCell i >>= (`lessThan` n)
      body' = body i <* inc i
  addLoop cond body'
  where inc i = updateCell i $ add (litInt 1)

compileSum :: [JitType] -> [CompileVal] -> CompileM CompileVal
compileSum [Meta _] [TabVal tab@(Table ptr n sizes _)] = do
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

mul :: Long -> Long -> CompileM Long
mul (Long x) (Long y) = liftM Long $ evalInstr longTy $ L.Mul False False x y []

newIntCell :: Int -> CompileM LongPtr
newIntCell x = do
  ptr <- liftM LongPtr $ evalInstr intPtrTy $
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

newTable :: JitType -> NumElems -> CompileM Table
newTable ty n = do
  let (scalarSize, scalarTy) = baseTypeInfo ty
  numScalars <- getNumScalars ty
  elemSize <- mul (litInt scalarSize) numScalars
  (Long numBytes) <- mul n elemSize
  voidPtr <- evalInstr charPtrTy (externCall mallocFun [numBytes])
  ptr <- evalInstr (L.ptr scalarTy) $ L.BitCast voidPtr (L.ptr scalarTy) []
  return $ Table (ScalarPtr ptr) n (ConstSize numScalars) ty

baseTypeInfo :: JitType -> (Int, L.Type)
baseTypeInfo ty = case ty of
  BaseType b -> case b of IntType  -> (8, longTy)
                          RealType -> (8, realTy)
  TabType _ valTy -> baseTypeInfo valTy

getNumScalars :: JitType -> CompileM Long
getNumScalars ty = case ty of
  BaseType _ -> return $ litInt 1
  TabType (Meta i) valTy -> do n <- getNumScalars valTy
                               mul i n

readTable :: Table -> Index -> CompileM CompileVal
readTable tab@(Table _ _ _ valTy) idx = do
  ptr <- arrayPtr tab idx
  case valTy of
    BaseType IntType -> do let (ScalarPtr ptr') = ptr
                           Long ans <- loadCell (LongPtr ptr')
                           return $ ScalarVal IntType ans
    TabType (Meta n) valTy' -> do
      numScalars <- getNumScalars valTy'
      return $ TabVal (Table ptr n (ConstSize numScalars) valTy')

writeTable :: Table -> Index -> CompileVal -> CompileM ()
writeTable tab idx val = do
  (ScalarPtr dest) <- arrayPtr tab idx
  case val of
    ScalarVal IntType val' ->
      writeCell (LongPtr dest) (Long val')
    TabVal (Table (ScalarPtr src) n (ConstSize numScalars) ty) -> do
      let (scalarSize, _) = baseTypeInfo ty
      elemSize <- mul (litInt scalarSize) numScalars
      Long numBytes <- mul n elemSize
      appendInstr $ L.Do (externCall memcpyFun [dest, src, numBytes])

arrayPtr (Table (ScalarPtr ptr) _ (ConstSize size) _) idx = do
  (Long offset) <- mul size idx
  liftM ScalarPtr $ evalInstr charPtrTy $ L.GetElementPtr False ptr [offset] []

lessThan :: Long -> Long -> CompileM Long
lessThan (Long x) (Long y) = liftM Long $ evalInstr longTy $ L.ICmp L.SLT x y []

charPtrTy = L.ptr (L.IntegerType 8)
intPtrTy = L.ptr longTy
longTy = L.IntegerType 64
realTy = L.FloatingPointType L.DoubleFP

funTy :: L.Type -> [L.Type] -> L.Type
funTy retTy argTys = L.ptr $ L.FunctionType retTy argTys False

externCall :: ExternFunSpec -> [L.Operand] -> L.Instruction
externCall (ExternFunSpec fname retTy argTys _) args =
  L.Call Nothing L.C [] fun args' [] []
  where fun = Right $ L.ConstantOperand $ C.GlobalReference
                         (funTy retTy argTys) (L.Name fname)
        args' = [(x ,[]) | x <- args]

mallocFun = ExternFunSpec "malloc_cod" charPtrTy [longTy] ["nbytes"]
memcpyFun = ExternFunSpec "memcpy_cod" L.VoidType
               [charPtrTy, charPtrTy, longTy]
               ["dest", "src", "nbytes"]

-- --- builtins ---

builtinEnv :: JitEnv
builtinEnv = FullEnv builtins mempty

builtins :: Env Var CompileVal
builtins = newEnv
  [ asBuiltin "add"  0 2 $ compileBinop (\x y -> L.Add False False x y [])
  , asBuiltin "mul"  0 2 $ compileBinop (\x y -> L.Mul False False x y [])
  , asBuiltin "sub"  0 2 $ compileBinop (\x y -> L.Sub False False x y [])
  , asBuiltin "iota" 0 1 $ compileIota
  , asBuiltin "sum"  1 1 $ compileSum
  , asBuiltin "doubleit" 0 1 $ externalMono doubleFun  IntType
  , asBuiltin "hash"     0 2 $ externalMono hashFun    IntType
  , asBuiltin "rand"     0 1 $ externalMono randFun    RealType
  , asBuiltin "randint"  0 2 $ externalMono randIntFun IntType
  ]

externalMono :: ExternFunSpec -> BaseType -> CompileApp
externalMono f@(ExternFunSpec name retTy _ _) baseTy [] args =
  liftM (ScalarVal baseTy) $ evalInstr retTy (externCall f args')
  where args' = reverse $ map asOp args
        asOp :: CompileVal -> L.Operand
        asOp (ScalarVal _ op) = op

compileDoubleit :: CompileApp
compileDoubleit [] [ScalarVal IntType x] =
  liftM (ScalarVal IntType) $ evalInstr longTy (externCall doubleFun [x])

doubleFun  = ExternFunSpec "doubleit" longTy [longTy] ["x"]
randFun    = ExternFunSpec "randunif"  realTy [longTy] ["keypair"]
randIntFun = ExternFunSpec "randint" longTy [longTy, longTy] ["keypair", "nmax"]
hashFun    = ExternFunSpec "threefry_2x32" longTy [longTy, longTy] ["keypair", "count"]

compileIota :: CompileApp
compileIota [] [ScalarVal b nOp] = do
  tab@(Table ptr _ _ _) <- newTable (BaseType IntType) n
  let body iPtr = do (Long i) <- loadCell iPtr
                     writeTable tab (Long i) (ScalarVal IntType i)
  addForILoop n body
  return $ ExPackage n (TabVal tab)
  where n = Long nOp

asBuiltin :: VarName -> Int -> Int -> CompileApp -> (VarName, CompileVal)
asBuiltin name nt nv f = (name, BuiltinLam b [] [])
  where b = BuiltinFun nt nv f ty
        ty = noLeaves $ builtinTypeEnv ! (FV name)

compileBinop :: (Operand -> Operand -> L.Instruction) -> CompileApp
compileBinop makeInstr = compile
  where
    compile :: CompileApp
    compile [] [ScalarVal _ x, ScalarVal _ y] = liftM (ScalarVal IntType) $
        evalInstr longTy (makeInstr y x)
