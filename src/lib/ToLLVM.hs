-- Copyright 2025 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE NoFieldSelectors #-}

module ToLLVM where

import Name
import Control.Monad
import Control.Monad.State.Strict hiding (state)
import Data.String (fromString)
import qualified Data.ByteString as BS
import qualified Types.LLVM as L
import Types.Simple
import Types.Primitives
import PPrint

import Err
import Debug.Trace
import QueryTypePure
import Util

-- === entrypoint ===

toLLVMEntryFun :: Monad m => L.Name -> TopLamExpr -> m L.Module
toLLVMEntryFun fname fun = do
  finalState <- runTranslateM do
    toLLVMEntryFun' fun
    startNewBlock $ L.Name "__unused__"
  let blocks = reverse finalState.basicBlocks
  let decl = L.FunctionDef $ L.Function fname [] blocks
  return $ L.Module $ libDecls ++ [decl]

libDecls :: [L.TopDecl]
libDecls = [
  L.FunctionDecl floatTy "printfloat" [floatTy]
           ]

floatTy :: L.Type
floatTy = L.BaseType $ Scalar Float32Type

-- === monad for the translation ===

data TranslateState i = TranslateState
  { basicBlocks  :: [L.BasicBlock]   -- reverse order
  , instructions :: [L.Decl]         -- reverse order
  , curBlockName :: L.Name
  , nameGen      :: Int
  , subst        :: TranslateSubst i}
type TranslateSubst i = Subst (LiftE L.Operand) i VoidS

newtype TranslateM (i::S) (a:: *) =
  TranslateM { inner :: StateT (TranslateState i) Except a }
  deriving (Functor, Applicative, Monad, MonadFail)

runTranslateM :: Monad m => TranslateM VoidS a -> m (TranslateState VoidS)
runTranslateM cont = do
  let initState = TranslateState [] [] (L.Name "__entry__") 0 voidSubst
  return $ ignoreExcept $ execStateT cont.inner initState

emitInstr :: L.Type -> L.Instruction -> TranslateM i L.Operand
emitInstr resultTy instr = do
  v <- newLName ""
  let decl = (Just v, resultTy, instr)
  TranslateM $ modify \s -> s {instructions = decl : s.instructions}
  return $ L.Operand (L.LocalOcc v) resultTy

emitStatement :: L.Instruction -> TranslateM i ()
emitStatement instr = do
  let decl = (Nothing, L.VoidType, instr)
  TranslateM $ modify \s -> s {instructions = decl : s.instructions}

extendEnv :: NameBinder i i' -> L.Operand -> TranslateM i' a -> TranslateM i a
extendEnv b x cont = TranslateM do
  prevState <- get
  let subst' = prevState.subst <>> (b @> LiftE x)
  let (ans, newState) = ignoreExcept $ runStateT (cont.inner) $ updateSubst prevState subst'
  put $ updateSubst newState prevState.subst
  return ans

-- lowering of ()
unitOperand :: L.Operand
unitOperand = L.Operand (L.Lit (Int32Lit 0)) (L.BaseType $ Scalar Int32Type)

lookupEnv :: Name i -> TranslateM i L.Operand
lookupEnv v = TranslateM do
  env <- gets (.subst)
  let LiftE x = env ! v
  return x

updateSubst :: TranslateState i -> TranslateSubst i' -> TranslateState i'
updateSubst (TranslateState a b c d _) subst = TranslateState a b c d subst

newLName :: BString -> TranslateM i L.Name
newLName hint = TranslateM do
  c <- gets (.nameGen)
  modify \s -> s {nameGen = s.nameGen + 1}
  return $ L.Name $ hint <> "_" <> fromString (show c)

startNewBlock :: L.Name -> TranslateM i ()
startNewBlock blockName = TranslateM $ modify \state -> do
  let newBlock = L.BasicBlock state.curBlockName (reverse state.instructions)
  state {
    basicBlocks = newBlock : state.basicBlocks,
    curBlockName = blockName,
    instructions = []}

-- === translation itself ===

toLLVMEntryFun' :: TopLamExpr -> TranslateM VoidS ()
toLLVMEntryFun' (TopLamExpr (Abs Empty body)) = do
  ans <- trExpr body
  emitStatement $ L.Return ans

trExpr :: Expr i -> TranslateM i L.Operand
trExpr = \case
  Block resultTy block -> trBlock block
  PrimOp resultTy op xs -> do
    resultTy' <- trType resultTy
    xs' <- forM xs trAtom
    trPrimOp resultTy' op xs'

trType :: Type i -> TranslateM i L.Type
trType = \case
  BaseType b -> return $ L.BaseType b
  ProdType [] -> return L.VoidType
  t -> error $ "not implemented: " ++ pprintStr t

trAtom :: Atom i -> TranslateM i L.Operand
trAtom = \case
  Var v _ -> do
    val <- lookupEnv v
    return val
  Lit v -> return $ L.Operand (L.Lit v) (L.BaseType (litType v))

trBlock :: Block i -> TranslateM i L.Operand
trBlock (Abs decls result) = case decls of
  Empty -> trExpr result
  Nest (Let b expr) rest -> do
    val <- trExpr expr
    extendEnv b val $ trBlock $ Abs rest result

trPrimOp :: L.Type -> PrimOp -> [L.Operand] -> TranslateM i L.Operand
trPrimOp resultTy op xs = case op of
  FAdd -> do
    [x, y] <- return xs
    emitInstr resultTy $ L.FAdd x y
  DebugPrintInt -> do
    [x] <- return xs
    emitStatement $ L.Call floatTy  "printfloat" [x]
    return unitOperand
