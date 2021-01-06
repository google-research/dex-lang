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
    if not self._as_parameter_:
      api.raise_from_dex()

  def __del__(self):
    if api.nofree:
      return
    api.destroyContext(self)

  def __getattr__(self, name):
    result = api.lookup(self, api.as_cstr(name))
    if not result:
      api.raise_from_dex()
    return Atom(result, self)


class Prelude(Module):
  __slots__ = ()
  def __init__(self):
    self._as_parameter_ = api.createContext()
    if not self._as_parameter_:
      api.raise_from_dex()

prelude = Prelude()


def eval(expr: str, module=prelude, _env=None):
  if _env is None:
    _env = module
  result = api.evalExpr(_env, api.as_cstr(expr))
  if not result:
    api.raise_from_dex()
  return Atom(result, module)


class Atom:
  __slots__ = ('__weakref__', '_as_parameter_', 'module')

  def __init__(self, ptr, module):
    self._as_parameter_ = ptr
    self.module = module

  def __del__(self):
    # TODO: Free
    pass

  def __repr__(self):
    # TODO: Free!
    return api.from_cstr(api.print(self))

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
    if not func_ptr:
      api.raise_from_dex()
    return NativeFunction(api.jit, func_ptr)
