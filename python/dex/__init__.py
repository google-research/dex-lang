# Copyright 2020 Google LLC
#
# Use of this source code is governed by a BSD-style
# license that can be found in the LICENSE file or at
# https://developers.google.com/open-source/licenses/bsd

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

class APIErr(Enum):
  ENotFound = 0
  EUnsupported = 1

CAPIErr = ctypes.c_uint64
CLit = tagged_union("Lit", [ctypes.c_int64, ctypes.c_int32, ctypes.c_int8, ctypes.c_double, ctypes.c_float])
CAtom = tagged_union("CAtom", [CLit])
WithErr = lambda err, val: tagged_union("WithErr", [err, val])

class HsAtom(ctypes.Structure): pass
class HsContext(ctypes.Structure): pass

_init = lib.dexInit
_init.restype = None
_init.argtypes = []

_fini = lib.dexFini
_fini.restype = None
_fini.argtypes = []

_eval = lib.dexEval
_eval.restype = ctypes.POINTER(HsContext)
_eval.argtypes = [ctypes.POINTER(HsContext), ctypes.c_char_p]

_print = lib.dexPrint
_print.restype = ctypes.c_char_p
_print.argtypes = [ctypes.POINTER(HsAtom)]

_lookup = lib.dexLookup
_lookup.restype = ctypes.POINTER(WithErr(CAPIErr, ctypes.POINTER(HsAtom)))
_lookup.argtypes = [ctypes.POINTER(HsContext), ctypes.c_char_p]

_toCAtom = lib.dexToCAtom
_toCAtom.restype = ctypes.POINTER(WithErr(CAPIErr, CAtom))
_toCAtom.argtypes = [ctypes.POINTER(HsAtom)]

_create_context = lib.dexCreateContext
_create_context.restype = ctypes.POINTER(HsContext)
_create_context.argtypes = []

_destroy_context = lib.dexDestroyContext
_destroy_context.restype = None
_destroy_context.argtypes = [ctypes.POINTER(HsContext)]

_init()
_nofree = False
@atexit.register
def _teardown():
  global _nofree
  _fini()
  _nofree = True  # Don't destruct any Haskell objects after the RTS has been shutdown

_default_ctx = _create_context()
atexit.register(lambda: _destroy_context(_default_ctx))

class Module:
  def __init__(self, source):
    self._env = _eval(_default_ctx, ctypes.c_char_p(source.encode('ascii')))

  def __del__(self):
    if _nofree:
      return
    _destroy_context(self._env)

  def __getattr__(self, name):
    result = _lookup(self._env, ctypes.c_char_p(name.encode('ascii'))).contents
    if result.tag == 0:
      raise ValueError("Lookup failed: f{APIErr[result.value]}")
    # TODO: Free the result block
    return Atom(result.value)

class Atom:
  def __init__(self, ptr):
    self._as_parameter_ = ptr

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
    result = _toCAtom(self).contents
    if result.tag == 0:
      raise ValueError("Can't convert Atom to a Python value")
    value = result.value.value
    if not isinstance(value, CLit):
      raise TypeError("Atom is not a scalar value")
    return value.value
