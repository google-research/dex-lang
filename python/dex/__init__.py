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

_init = lib.dexInit
_init.restype = None
_init.argtypes = []

_fini = lib.dexFini
_fini.restype = None
_fini.argtypes = []

_create_context = lib.dexCreateContext
_create_context.restype = ctypes.POINTER(HsContext)
_create_context.argtypes = []

_destroy_context = lib.dexDestroyContext
_destroy_context.restype = None
_destroy_context.argtypes = [ctypes.POINTER(HsContext)]

_print = lib.dexPrint
_print.restype = ctypes.c_char_p
_print.argtypes = [ctypes.POINTER(HsAtom)]

_insert = lib.dexInsert
_insert.restype = ctypes.POINTER(HsContext)
_insert.argtypes = [ctypes.POINTER(HsContext), ctypes.c_char_p, ctypes.POINTER(HsAtom)]

_eval = lib.dexEval
_eval.restype = ctypes.POINTER(HsContext)
_eval.argtypes = [ctypes.POINTER(HsContext), ctypes.c_char_p]

_evalExpr = lib.dexEvalExpr
_evalExpr.restype = ctypes.POINTER(HsAtom)
_evalExpr.argtypes = [ctypes.POINTER(HsContext), ctypes.c_char_p]

_lookup = lib.dexLookup
_lookup.restype = ctypes.POINTER(HsAtom)
_lookup.argtypes = [ctypes.POINTER(HsContext), ctypes.c_char_p]

_toCAtom = lib.dexToCAtom
_toCAtom.restype = ctypes.c_int
_toCAtom.argtypes = [ctypes.POINTER(HsAtom), ctypes.POINTER(CAtom)]

_getError = lib.dexGetError
_getError.restype = ctypes.c_char_p
_getError.argtypes = []

_init()
_nofree = False
@atexit.register
def _teardown():
  global _nofree
  _fini()
  _nofree = True  # Don't destruct any Haskell objects after the RTS has been shutdown


def _as_cstr(x: str):
  return ctypes.c_char_p(x.encode('ascii'))

def _from_cstr(cx):
  return cx.value.decode('ascii')


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
