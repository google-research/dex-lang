# Copyright 2020 Google LLC
#
# Use of this source code is governed by a BSD-style
# license that can be found in the LICENSE file or at
# https://developers.google.com/open-source/licenses/bsd

import itertools as it
import ctypes
import pathlib
import atexit
from enum import Enum
from typing import List

__all__ = ['execute']

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

HsAtomPtr = ctypes.POINTER(HsAtom)
HsContextPtr = ctypes.POINTER(HsContext)
HsJITPtr = ctypes.POINTER(HsJIT)
CAtomPtr = ctypes.POINTER(CAtom)
NativeFunction = ctypes.POINTER(NativeFunctionObj)

def _dex_func(name, *signature):
  argtypes, restype = signature[:-1], signature[-1]
  f = getattr(lib, name)
  f.restype = restype
  f.argtypes = argtypes
  return f

_init = _dex_func('dexInit', None)
_fini = _dex_func('dexFini', None)
_getError = _dex_func('dexGetError', ctypes.c_char_p)

_create_context  = _dex_func('dexCreateContext',  HsContextPtr)
_destroy_context = _dex_func('dexDestroyContext', HsContextPtr, None)

_eval     = _dex_func('dexEval',     HsContextPtr, ctypes.c_char_p,            HsContextPtr)
_insert   = _dex_func('dexInsert',   HsContextPtr, ctypes.c_char_p, HsAtomPtr, HsContextPtr)
_evalExpr = _dex_func('dexEvalExpr', HsContextPtr, ctypes.c_char_p,            HsAtomPtr)
_lookup   = _dex_func('dexLookup',   HsContextPtr, ctypes.c_char_p,            HsAtomPtr)

_print   = _dex_func('dexPrint',   HsAtomPtr,           ctypes.c_char_p)
_toCAtom = _dex_func('dexToCAtom', HsAtomPtr, CAtomPtr, ctypes.c_int)

_createJIT  = _dex_func('dexCreateJIT',  HsJITPtr)
_destroyJIT = _dex_func('dexDestroyJIT', HsJITPtr, None)
_compile    = _dex_func('dexCompile',    HsJITPtr, HsContextPtr, HsAtomPtr, NativeFunction)
_unload     = _dex_func('dexUnload',     HsJITPtr, NativeFunction, None)

_init()
_jit = _createJIT()
_nofree = False
@atexit.register
def _teardown():
  global _nofree
  _destroyJIT(_jit)
  _fini()
  _nofree = True  # Don't destruct any Haskell objects after the RTS has been shutdown


def _as_cstr(x: str):
  return ctypes.c_char_p(x.encode('ascii'))

def _from_cstr(cx):
  return cx.decode('ascii')


class Module:
  __slots__ = ('_as_parameter_',)

  def __init__(self, source):
    self._as_parameter_ = _eval(prelude, _as_cstr(source))
    if not self._as_parameter_:
      raise RuntimeError(_from_cstr(_getError()))

  def __del__(self):
    if _nofree:
      return
    _destroy_context(self)

  def __getattr__(self, name):
    result = _lookup(self, _as_cstr(name))
    if not result:
      raise RuntimeError(_from_cstr(_getError()))
    return Atom(result, self)


class Prelude(Module):
  __slots__ = ()
  def __init__(self):
    self._as_parameter_ = _create_context()
    if not self._as_parameter_:
      raise RuntimeError("Failed to initialize prelude!")

prelude = Prelude()


def eval(expr: str, module=prelude, _env=None):
  if _env is None:
    _env = module
  result = _evalExpr(_env, _as_cstr(expr))
  if not result:
    raise RuntimeError(_from_cstr(_getError()))
  return Atom(result, module)


class Atom:
  __slots__ = ('_as_parameter_', 'module')

  def __init__(self, ptr, module):
    self._as_parameter_ = ptr
    self.module = module

  def __del__(self):
    # TODO: Free
    pass

  def __repr__(self):
    # TODO: Free!
    return _print(self).decode('ascii')

  def __int__(self):
    return int(self._as_scalar())

  def __float__(self):
    return float(self._as_scalar())

  def _as_scalar(self):
    result = CAtom()
    success = _toCAtom(self, ctypes.pointer(result))
    if not success:
      raise RuntimeError(_from_cstr(_getError()))
    value = result.value
    if not isinstance(value, CLit):
      raise TypeError("Atom is not a scalar value")
    return value.value

  def __call__(self, *args):
    # TODO: Make those calls more hygenic
    env = self.module
    for i, atom in enumerate(it.chain((self,), args)):
      # NB: Atoms can contain arbitrary references
      if atom.module is not prelude and atom.module is not self.module:
        raise RuntimeError("Mixing atoms coming from different Dex modules is not supported yet!")
      old_env, env = env, _insert(env, _as_cstr(f"python_arg{i}"), atom)
      _destroy_context(old_env)
    return eval(" ".join(f"python_arg{i}" for i in range(len(args) + 1)), module=self.module, _env=env)

  def compile(self):
    func_ptr = _compile(_jit, self.module, self)
    if not func_ptr:
      raise RuntimeError("Failed to JIT-compile a Dex function")
    return NativeFunction(func_ptr)


class NativeFunction:
  def __init__(self, ptr):
    self._as_parameter_ = ptr
    self.ptr = ptr

  def __del__(self):
    if _nofree: return
    _unload(_jit, self)
