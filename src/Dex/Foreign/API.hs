-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Dex.Foreign.API where

import Foreign.Ptr
import Foreign.C

import Syntax

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
foreign export ccall "dexInsert"   dexInsert   :: Ptr Context -> CString   -> Ptr Atom -> IO (Ptr Context)
foreign export ccall "dexEval"     dexEval     :: Ptr Context -> CString   -> IO (Ptr Context)
foreign export ccall "dexEvalExpr" dexEvalExpr :: Ptr Context -> CString   -> IO (Ptr Atom)
foreign export ccall "dexLookup"   dexLookup   :: Ptr Context -> CString   -> IO (Ptr Atom)

-- Serialization
foreign export ccall "dexPrint"    dexPrint    :: Ptr Atom                 -> IO CString
foreign export ccall "dexToCAtom"  dexToCAtom  :: Ptr Atom    -> Ptr CAtom -> IO CInt

-- JIT
foreign export ccall "dexCreateJIT"  dexCreateJIT  :: IO (Ptr JIT)
foreign export ccall "dexDestroyJIT" dexDestroyJIT :: Ptr JIT -> IO ()
foreign export ccall "dexCompile"    dexCompile    :: Ptr JIT -> Ptr Context -> Ptr Atom -> IO (Ptr NativeFunction)
foreign export ccall "dexUnload"     dexUnload     :: Ptr JIT -> Ptr NativeFunction -> IO ()
foreign export ccall "dexGetFunctionSignature"  dexGetFunctionSignature  :: Ptr JIT -> Ptr NativeFunction -> IO (Ptr ExportedSignature)
foreign export ccall "dexFreeFunctionSignature" dexFreeFunctionSignature :: Ptr ExportedSignature -> IO ()
