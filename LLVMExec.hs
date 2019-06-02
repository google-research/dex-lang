{-# LANGUAGE OverloadedStrings #-}

module LLVMExec (showLLVM, evalJit, readPtrs, wordAsPtr, ptrAsWord,
                 mallocBytes) where

import qualified LLVM.AST as L
import qualified LLVM.Module as Mod
import qualified LLVM.PassManager as P
import qualified LLVM.ExecutionEngine as EE
import LLVM.Internal.Context

import Foreign.Ptr
import Foreign.Storable
import Foreign.Marshal.Alloc (mallocBytes)

import Control.Monad
import Data.Word (Word64)
import Data.ByteString.Char8 (unpack)

foreign import ccall "dynamic"
  haskFun :: FunPtr (IO ()) -> IO ()

evalJit :: L.Module -> IO ()
evalJit mod =
  withContext $ \c ->
    Mod.withModuleFromAST c mod $ \m -> do
      runPasses m
      jit c $ \ee ->
         EE.withModuleInEngine ee m $ \eee -> do
           fn <- EE.getFunction eee (L.Name "thefun")
           case fn of
             Just fn -> runJitted fn
             Nothing -> error "Failed to fetch \"thefun\" from LLVM"

jit :: Context -> (EE.MCJIT -> IO a) -> IO a
jit c = EE.withMCJIT c (Just 3) Nothing Nothing Nothing

runJitted :: FunPtr a -> IO ()
runJitted fn = haskFun (castFunPtr fn :: FunPtr (IO ()))

runPasses :: Mod.Module -> IO ()
runPasses m = P.withPassManager passes $ \pm -> void $ P.runPassManager pm m

showLLVM :: L.Module -> IO String
showLLVM m =
  withContext $ \c ->
    Mod.withModuleFromAST c m $ \m -> do
      prePass <- showModule m
      runPasses m
      postPass <- showModule m
      return $ "Input LLVM:\n\n" ++ prePass ++ "\nAfter passes:\n\n" ++ postPass
  where
    showModule :: Mod.Module -> IO String
    showModule m = liftM unpack $ Mod.moduleLLVMAssembly m

readPtrs :: Int -> Ptr Word64 -> IO [Word64]
readPtrs n ptr = mapM readAt [0..n-1]
  where readAt i = peek $ ptr `plusPtr` (8 * i)

wordAsPtr :: Word64 -> Ptr a
wordAsPtr x = wordPtrToPtr $ fromIntegral x

ptrAsWord :: Ptr a -> Word64
ptrAsWord ptr = fromIntegral $ ptrToWordPtr ptr

passes :: P.PassSetSpec
passes = P.defaultCuratedPassSetSpec {P.optLevel = Just 3}
