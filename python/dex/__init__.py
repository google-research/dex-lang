# Copyright 2020 Google LLC
#
# Use of this source code is governed by a BSD-style
# license that can be found in the LICENSE file or at
# https://developers.google.com/open-source/licenses/bsd

import itertools as it
import sys
import ctypes
from typing import Any, List, Union
from . import api
from .native_function import NativeFunction

__all__ = [
  'Module',
  'eval',
]

class Module:
  __slots__ = ('_as_parameter_',)

  def __init__(self, source):
    self._as_parameter_ = api.eval(prelude, api.as_cstr(source))
    if not self._as_parameter_: api.raise_from_dex()

  @classmethod
  def _from_ptr(cls, ptr):
    if not ptr: api.raise_from_dex()
    self = super().__new__(cls)
    self._as_parameter_ = ptr
    return self

  def __del__(self):
    if api.nofree: return
    api.destroyContext(self)

  def __getattr__(self, name):
    result = api.lookup(self, api.as_cstr(name))
    return Atom._from_ptr(result, self)


class Prelude(Module):
  __slots__ = ()
  def __init__(self):
    self._as_parameter_ = api.createContext()
    if not self._as_parameter_:
      api.raise_from_dex()

prelude = Prelude()


def eval(expr: str):
  # TODO: Query a free source name
  _final_env = Module._from_ptr(api.eval(prelude, api.as_cstr("python_result = " + expr)))
  result = api.lookup(_final_env, api.as_cstr("python_result"))
  return Atom._from_ptr(result, _final_env)


class Atom:
  __slots__ = ('__weakref__', '_as_parameter_', 'module')

  def __init__(self, value):
    catom = api.CAtom()
    if isinstance(value, int):
      catom.tag = 0
      catom.value.tag = 1
      catom.value.value = ctypes.c_int(value)
    elif isinstance(value, float):
      catom.tag = 0
      catom.value.tag = 4
      catom.value.value = ctypes.c_float(value)
    else:
      raise ValueError("Can't convert given value to a Dex Atom")
    self.module = prelude
    self._as_parameter_ = api.fromCAtom(ctypes.pointer(catom))
    if not self._as_parameter_:
      api.raise_from_dex()

  @classmethod
  def _from_ptr(cls, ptr, module):
    if not ptr: api.raise_from_dex()
    self = super().__new__(cls)
    self._as_parameter_ = ptr
    self.module = module
    return self

  def __del__(self):
    # TODO: Free
    pass

  def __repr__(self):
    # TODO: Free!
    return api.from_cstr(api.print(self.module, self))

  def __int__(self):
    return int(self._as_scalar())

  def __float__(self):
    return float(self._as_scalar())

  def _as_scalar(self):
    result = api.CAtom()
    success = api.toCAtom(self, ctypes.pointer(result))
    if not success:
      api.raise_from_dex()
    value = result.value
    if not isinstance(value, api.CLit):
      raise TypeError("Atom is not a scalar value")
    return value.value

  def __call__(self, *args):
    raise NotImplementedError()
    # TODO: Make those calls more hygenic
    env = self.module
    for i, atom in enumerate(it.chain((self,), args)):
      # NB: Atoms can contain arbitrary references
      if atom.module is not prelude and atom.module is not self.module:
        raise RuntimeError("Mixing atoms coming from different Dex modules is not supported yet!")
      old_env, env = env, api.insert(env, api.as_cstr(f"python_arg{i}"), atom)
      api.destroyContext(old_env)
    return eval(" ".join(f"python_arg{i}" for i in range(len(args) + 1)), module=self.module, _env=env)

  def compile(self):
    func_ptr = api.compile(api.jit, self.module, self)
    if not func_ptr: api.raise_from_dex()
    return NativeFunction(api.jit, func_ptr)
