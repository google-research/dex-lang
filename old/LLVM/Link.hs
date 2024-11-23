-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module LLVM.Link
  ( createLinker, destroyLinker
  , addExplicitLinkMap, addObjectFile, getFunctionPointer
  , ExplicitLinkMap
  ) where

import Data.String (fromString)
import Foreign.Ptr
import qualified Data.ByteString as BS

import System.IO
import System.IO.Temp

import qualified LLVM.OrcJIT as OrcJIT
import qualified LLVM.Internal.OrcJIT as OrcJIT
import qualified LLVM.Internal.Target as Target
import qualified LLVM.Internal.FFI.Target as FFI

import qualified LLVM.Shims

data Linker = Linker
  { linkerExecutionSession :: OrcJIT.ExecutionSession
#ifdef darwin_HOST_OS
  , linkerLinkLayer        :: OrcJIT.ObjectLinkingLayer
#else
  , linkerLinkLayer        :: OrcJIT.RTDyldObjectLinkingLayer
#endif
  , _linkerTargetMachine   :: Target.TargetMachine
   -- We ought to just need the link layer and the mangler but but llvm-hs
   -- requires a full `IRCompileLayer` for incidental reasons. TODO: fix.
  , linkerIRLayer          :: OrcJIT.IRCompileLayer
  , linkerDylib            :: OrcJIT.JITDylib }

instance OrcJIT.IRLayer Linker where
  -- llvm-hs requires an compile/IR layer but don't actually need it for the
  -- linking functions we call. TODO: update llvm-hs to expose more precise
  -- requirements for its linking functions.
  getIRLayer    l = OrcJIT.getIRLayer    $ linkerIRLayer l
  getDataLayout l = OrcJIT.getDataLayout $ linkerIRLayer l
  getMangler    l = OrcJIT.getMangler    $ linkerIRLayer l

type CName = String

type ExplicitLinkMap = [(CName, Ptr ())]

createLinker :: IO Linker
createLinker = do
  -- TODO: should this be a parameter to `createLinker` instead?
  tm <- LLVM.Shims.newDefaultHostTargetMachine
  s         <- OrcJIT.createExecutionSession
#ifdef darwin_HOST_OS
  linkLayer <- OrcJIT.createObjectLinkingLayer s
#else
  linkLayer <- OrcJIT.createRTDyldObjectLinkingLayer s
#endif
  dylib     <- OrcJIT.createJITDylib s "main_dylib"
  compileLayer <- OrcJIT.createIRCompileLayer s linkLayer tm
  OrcJIT.addDynamicLibrarySearchGeneratorForCurrentProcess compileLayer dylib
  return $ Linker s linkLayer tm compileLayer dylib

destroyLinker :: Linker  -> IO ()
destroyLinker (Linker session _ (Target.TargetMachine tm) _ _) = do
  -- dylib, link layer and IRLayer should get cleaned up automatically
  OrcJIT.disposeExecutionSession session
  FFI.disposeTargetMachine tm

addExplicitLinkMap :: Linker -> ExplicitLinkMap -> IO ()
addExplicitLinkMap l linkMap = do
  let (linkedNames, linkedPtrs) = unzip linkMap
  let flags = OrcJIT.defaultJITSymbolFlags { OrcJIT.jitSymbolAbsolute = True }
  let ptrSymbols = [OrcJIT.JITSymbol (ptrToWordPtr ptr) flags | ptr <- linkedPtrs]
  mangledNames <- mapM (OrcJIT.mangleSymbol l . fromString) linkedNames
  OrcJIT.defineAbsoluteSymbols (linkerDylib l) $ zip mangledNames ptrSymbols
  mapM_ OrcJIT.disposeMangledSymbol mangledNames

addObjectFile :: Linker -> BS.ByteString -> IO ()
addObjectFile l objFileContents = do
  withSystemTempFile "objfile.o" \path h -> do
    BS.hPut h objFileContents
    hFlush h
    OrcJIT.addObjectFile (linkerLinkLayer l) (linkerDylib l) path

getFunctionPointer :: Linker -> CName -> IO (FunPtr a)
getFunctionPointer l name = do
  OrcJIT.lookupSymbol (linkerExecutionSession l) (linkerIRLayer l)
    (linkerDylib l) (fromString name) >>= \case
      Right (OrcJIT.JITSymbol funcAddr _) ->
        return $ castPtrToFunPtr $ wordPtrToPtr funcAddr
      Left s -> error $ "Couldn't find function: " ++ name ++ "\n" ++ show s
