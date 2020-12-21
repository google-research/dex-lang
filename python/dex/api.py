# Copyright 2020 Google LLC
#
# Use of this source code is governed by a BSD-style
# license that can be found in the LICENSE file or at
# https://developers.google.com/open-source/licenses/bsd

import ctypes
import pathlib
import atexit
from typing import List

here = pathlib.Path(__file__).parent.absolute()

lib = ctypes.cdll.LoadLibrary(here / 'libDex.so')

def tagged_union(name: str, members: List[type]):
  named_members = [(f"t{i}", member) for i, member in enumerate(members)]
  payload = type(name + "Payload", (ctypes.Union,), {"_fields_": named_members})
  union = type(name, (ctypes.Structure,), {
    "_fields_": [("tag", ctypes.c_uint64), ("payload", payload)],
    "value": property(lambda self: getattr(self.payload, f"t{self.tag}")),
  })
  return union

CLit = tagged_union("Lit", [ctypes.c_int64, ctypes.c_int32, ctypes.c_int8, ctypes.c_double, ctypes.c_float])
class CRectArray(ctypes.Structure):
  _fields_ = [("data", ctypes.c_void_p),
              ("shape_ptr", ctypes.POINTER(ctypes.c_int64)),
              ("strides_ptr", ctypes.POINTER(ctypes.c_int64))]
CAtom = tagged_union("CAtom", [CLit, CRectArray])
assert ctypes.sizeof(CAtom) == 4 * 8

class HsAtom(ctypes.Structure): pass
class HsContext(ctypes.Structure): pass
class HsJIT(ctypes.Structure): pass
class NativeFunctionObj(ctypes.Structure): pass
class NativeFunctionSignature(ctypes.Structure):
  _fields_ = [("arg", ctypes.c_char_p),
              ("res", ctypes.c_char_p),
              ("ccall", ctypes.c_char_p)]


HsAtomPtr = ctypes.POINTER(HsAtom)
HsContextPtr = ctypes.POINTER(HsContext)
HsJITPtr = ctypes.POINTER(HsJIT)
CAtomPtr = ctypes.POINTER(CAtom)
NativeFunctionSignaturePtr = ctypes.POINTER(NativeFunctionSignature)
NativeFunction = ctypes.POINTER(NativeFunctionObj)

def dex_func(name, *signature):
  argtypes, restype = signature[:-1], signature[-1]
  f = getattr(lib, name)
  f.restype = restype
  f.argtypes = argtypes
  return f

init = dex_func('dexInit', None)
fini = dex_func('dexFini', None)
getError = dex_func('dexGetError', ctypes.c_char_p)

createContext  = dex_func('dexCreateContext',  HsContextPtr)
destroyContext = dex_func('dexDestroyContext', HsContextPtr, None)

eval     = dex_func('dexEval',     HsContextPtr, ctypes.c_char_p,            HsContextPtr)
insert   = dex_func('dexInsert',   HsContextPtr, ctypes.c_char_p, HsAtomPtr, HsContextPtr)
evalExpr = dex_func('dexEvalExpr', HsContextPtr, ctypes.c_char_p,            HsAtomPtr)
lookup   = dex_func('dexLookup',   HsContextPtr, ctypes.c_char_p,            HsAtomPtr)

print   = dex_func('dexPrint',   HsAtomPtr,           ctypes.c_char_p)
toCAtom = dex_func('dexToCAtom', HsAtomPtr, CAtomPtr, ctypes.c_int)

createJIT  = dex_func('dexCreateJIT',  HsJITPtr)
destroyJIT = dex_func('dexDestroyJIT', HsJITPtr, None)
compile    = dex_func('dexCompile',    HsJITPtr, HsContextPtr, HsAtomPtr, NativeFunction)
unload     = dex_func('dexUnload',     HsJITPtr, NativeFunction, None)

getFunctionSignature  = dex_func('dexGetFunctionSignature', HsJITPtr, NativeFunction, NativeFunctionSignaturePtr)
freeFunctionSignature = dex_func('dexFreeFunctionSignature', NativeFunctionSignaturePtr)

init()
jit = createJIT()
nofree = False
@atexit.register
def _teardown():
  global nofree
  destroyJIT(jit)
  fini()
  nofree = True  # Don't destruct any Haskell objects after the RTS has been shutdown


def as_cstr(x: str):
  return ctypes.c_char_p(x.encode('ascii'))

def from_cstr(cx):
  return cx.decode('ascii')

def raise_from_dex():
  raise RuntimeError(from_cstr(getError()))
