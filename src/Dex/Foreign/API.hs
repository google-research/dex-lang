-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Dex.Foreign.API where

import Foreign.Ptr
import Foreign.C

import Dex.Foreign.Context
import Dex.Foreign.Serialize
import Dex.Foreign.JIT

-- Public API (commented out exports are defined in rts.c)

-- Initialization and basic runtime
-- foreign export ccall "dexInit"     _ :: IO ()
-- foreign export ccall "dexFini"     _ :: IO ()
-- foreign export ccall "dexGetError" _ :: CString

-- Context
foreign export ccall "dexCreateContext"  dexCreateContext  :: IO (Ptr Context)
foreign export ccall "dexDestroyContext" dexDestroyContext :: Ptr Context -> IO ()
foreign export ccall "dexForkContext"    dexForkContext    :: Ptr Context -> IO (Ptr Context)
foreign export ccall "dexInsert"     dexInsert    :: Ptr Context -> CString   -> Ptr AtomEx -> IO (Ptr Context)
foreign export ccall "dexEval"       dexEval      :: Ptr Context -> CString   -> IO (Ptr Context)
foreign export ccall "dexLookup"     dexLookup    :: Ptr Context -> CString   -> IO (Ptr AtomEx)
foreign export ccall "dexFreshName"  dexFreshName :: Ptr Context              -> IO CString

-- Serialization
foreign export ccall "dexPrint"     dexPrint      :: Ptr Context -> Ptr AtomEx     -> IO CString
foreign export ccall "dexToCAtom"   dexToCAtom    :: Ptr AtomEx  -> Ptr CAtom      -> IO CInt
foreign export ccall "dexFromCAtom" dexFromCAtom  :: Ptr CAtom                     -> IO (Ptr AtomEx)

-- JIT
foreign export ccall "dexCreateJIT"  dexCreateJIT  :: IO (Ptr JIT)
foreign export ccall "dexDestroyJIT" dexDestroyJIT :: Ptr JIT -> IO ()
foreign export ccall "dexCompile"    dexCompile    :: Ptr JIT -> CInt -> Ptr Context -> Ptr AtomEx -> IO (Ptr NativeFunction)
foreign export ccall "dexUnload"     dexUnload     :: Ptr JIT -> Ptr NativeFunction -> IO ()
foreign export ccall "dexGetFunctionSignature"  dexGetFunctionSignature  :: Ptr JIT -> Ptr NativeFunction -> IO (Ptr ClosedExportedSignature)
foreign export ccall "dexFreeFunctionSignature" dexFreeFunctionSignature :: Ptr ClosedExportedSignature -> IO ()
