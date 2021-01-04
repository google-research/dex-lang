-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}

module LLVM.JIT (
  JIT, createJIT, destroyJIT, withJIT,
  NativeModule, compileModule, unloadNativeModule, withNativeModule,
  getFunctionPtr
  ) where

import Control.Monad
import Control.Exception
import Foreign.Ptr
import Data.IORef
import Data.String
import Data.List (sortBy)
import qualified Data.Map as M
import qualified Data.ByteString.Char8 as C8BS
import qualified Data.ByteString.Short as SBS

import qualified LLVM.Internal.OrcJIT.CompileLayer as OrcJIT
import qualified LLVM.OrcJIT as OrcJIT
import qualified LLVM.Target as T
import qualified LLVM.Linking as Linking

import qualified LLVM.AST
import qualified LLVM.AST.Global as LLVM.AST
import qualified LLVM.AST.Constant as C
import qualified LLVM.Module as LLVM
import qualified LLVM.Context as LLVM

import LLVM.Shims

data JIT =
    JIT { execSession  :: OrcJIT.ExecutionSession
        , linkLayer    :: OrcJIT.ObjectLinkingLayer
        , compileLayer :: OrcJIT.IRCompileLayer OrcJIT.ObjectLinkingLayer
        , resolvers    :: IORef (M.Map OrcJIT.ModuleKey SymbolResolver)
        }

-- XXX: The target machine cannot be destroyed before JIT is destroyed
-- TODO: This leaks resources if we fail halfway
createJIT :: T.TargetMachine -> IO JIT
createJIT tm = do
  void $ Linking.loadLibraryPermanently Nothing
  resolvers    <- newIORef M.empty
  execSession  <- OrcJIT.createExecutionSession
  let lookupResolver = \k -> do
        SymbolResolver _ ffiResolver <- (M.! k) <$> readIORef resolvers
        return ffiResolver
  linkLayer    <- OrcJIT.newObjectLinkingLayer execSession lookupResolver
  compileLayer <- OrcJIT.newIRCompileLayer linkLayer tm
  return JIT{..}

-- TODO: This might not release everything if it fails halfway
destroyJIT :: JIT -> IO ()
destroyJIT JIT{..} = do
  OrcJIT.disposeCompileLayer compileLayer
  OrcJIT.disposeLinkingLayer linkLayer
  OrcJIT.disposeExecutionSession execSession

withJIT :: T.TargetMachine -> (JIT -> IO a) -> IO a
withJIT tm = bracket (createJIT tm) destroyJIT

data NativeModule =
  NativeModule { moduleJIT      :: JIT
               , moduleKey      :: OrcJIT.ModuleKey
               , moduleDtors    :: [FunPtr (IO ())]
               , llvmModule     :: LLVM.Module
               , llvmContext    :: LLVM.Context
               }

type CompilationPipeline = LLVM.Module -> IO ()

-- TODO: This leaks resources if we fail halfway
compileModule :: JIT -> LLVM.AST.Module -> CompilationPipeline -> IO NativeModule
compileModule moduleJIT@JIT{..} ast compilationPipeline = do
  llvmContext <- LLVM.createContext
  llvmModule <- LLVM.createModuleFromAST llvmContext ast
  compilationPipeline llvmModule
  moduleKey <- OrcJIT.allocateModuleKey execSession
  resolver <- newSymbolResolver execSession (makeResolver compileLayer)
  modifyIORef resolvers (M.insert moduleKey resolver)
  OrcJIT.addModule compileLayer moduleKey llvmModule
  moduleDtors <- forM dtorNames \dtorName -> do
    dtorSymbol <- OrcJIT.mangleSymbol compileLayer (fromString dtorName)
    Right (OrcJIT.JITSymbol dtorAddr _) <- OrcJIT.findSymbol compileLayer dtorSymbol False
    return $ castPtrToFunPtr $ wordPtrToPtr dtorAddr
  return NativeModule{..}
  where
    makeResolver :: OrcJIT.IRCompileLayer OrcJIT.ObjectLinkingLayer -> OrcJIT.SymbolResolver
    makeResolver cl = OrcJIT.SymbolResolver \sym -> do
      rsym <- OrcJIT.findSymbol cl sym False
      -- We look up functions like malloc in the current process
      -- TODO: Use JITDylibs to avoid inlining addresses as constants:
      -- https://releases.llvm.org/9.0.0/docs/ORCv2.html#how-to-add-process-and-library-symbols-to-the-jitdylibs
      case rsym of
        Right _ -> return rsym
        Left  _ -> do
          ptr <- Linking.getSymbolAddressInProcess sym
          if ptr == 0
            then error $ "Missing symbol: " ++ show sym
            else return $ Right $ externSym ptr
    externSym ptr =
      OrcJIT.JITSymbol { OrcJIT.jitSymbolAddress = ptr
                       , OrcJIT.jitSymbolFlags = OrcJIT.defaultJITSymbolFlags
                           { OrcJIT.jitSymbolExported = True
                           , OrcJIT.jitSymbolAbsolute = True }
                       }
    -- Unfortunately the JIT layers we use here don't handle the destructors properly,
    -- so we have to find and call them ourselves.
    dtorNames = do
      let dtorStructs = flip foldMap (LLVM.AST.moduleDefinitions ast) \case
            LLVM.AST.GlobalDefinition
              LLVM.AST.GlobalVariable{
                name="llvm.global_dtors",
                initializer=Just (C.Array _ elems),
                ..} -> elems
            _ -> []
      -- Sort in the order of decreasing priority!
      fmap snd $ sortBy (flip compare) $ flip fmap dtorStructs $
        \(C.Struct _ _ [C.Int _ n, C.GlobalReference _ (LLVM.AST.Name dname), _]) ->
          (n, C8BS.unpack $ SBS.fromShort dname)

foreign import ccall "dynamic"
  callDtor :: FunPtr (IO ()) -> IO ()

-- TODO: This might not release everything if it fails halfway
unloadNativeModule :: NativeModule -> IO ()
unloadNativeModule NativeModule{..} = do
  let JIT{..} = moduleJIT
  forM_ moduleDtors callDtor
  resolver <- (M.! moduleKey) <$> readIORef resolvers
  disposeSymbolResolver resolver
  modifyIORef resolvers (M.delete moduleKey)
  OrcJIT.removeModule compileLayer moduleKey
  OrcJIT.releaseModuleKey execSession moduleKey
  LLVM.disposeModule llvmModule
  LLVM.disposeContext llvmContext

withNativeModule :: JIT -> LLVM.AST.Module -> CompilationPipeline -> (NativeModule -> IO a) -> IO a
withNativeModule jit m p = bracket (compileModule jit m p) unloadNativeModule

getFunctionPtr :: NativeModule -> String -> IO (FunPtr a)
getFunctionPtr NativeModule{..} funcName = do
  let JIT{..} = moduleJIT
  symbol <- OrcJIT.mangleSymbol compileLayer $ fromString funcName
  Right (OrcJIT.JITSymbol funcAddr _) <- OrcJIT.findSymbolIn compileLayer moduleKey symbol False
  return $ castPtrToFunPtr $ wordPtrToPtr funcAddr
