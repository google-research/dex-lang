# Copyright 2020 Google LLC
#
# Use of this source code is governed by a BSD-style
# license that can be found in the LICENSE file or at
# https://developers.google.com/open-source/licenses/bsd

from weakref import WeakKeyDictionary
from functools import partial
import numpy as np
import jax

from .. import Atom
from ..native_function import ScalarType, RectContArrayType

def primitive(f):
  if not isinstance(f, Atom):
    raise TypeError("DexPrimitive expects a function atom as an argument")
  return partial(dex_call.bind, func_atom=f)

compiler_cache = WeakKeyDictionary()
def get_compiled(func_atom):
  compiled = compiler_cache.get(func_atom, None)
  if compiled is None:
    compiled = compiler_cache[func_atom] = func_atom.compile()
  return compiled


dex_call = jax.core.Primitive('dex_call')

@dex_call.def_impl
def dex_call_impl(*args, func_atom):
  return get_compiled(func_atom)(*args)

@dex_call.def_abstract_eval
def dex_call_abstract_eval(*args, func_atom):
  # TODO: Make it possible to get the signature without compiling the function
  native_func = get_compiled(func_atom)
  arg_sig = native_func.explicit_argument_signature
  res_sig = native_func.result_signature
  if len(args) != len(arg_sig):
    raise RuntimeError(f"Dex function expects {len(arg_sig)} arguments, but was given {len(args)}")
  if not all(isinstance(arg, jax.core.ShapedArray) for arg in args):
    raise RuntimeError("Cannot perform evaluation of Dex functions without known shapes")
  # Check arguments and infer shape parameters
  shape_vars = {}
  for i, (arg, b) in enumerate(zip(args, arg_sig)):
    expected_dtype = np.dtype(b.type.ctype)
    if arg.dtype != expected_dtype:
      raise RuntimeError(f"dtype mismatch in arg {i}: expected {expected_dtype}, got {arg.dtype}")
    if isinstance(b.type, ScalarType):
      expected_shape = ()
    elif isinstance(b.type, RectContArrayType):
      expected_shape = b.type.shape
    else:
      raise AssertionError("Unhandled case!")
    if len(arg.shape) != len(expected_shape):
      raise RuntimeError(f"rank mismatch in arg {i}: expected {len(expected_shape)}, got {len(arg.shape)}")
    inferred_shape = tuple(
      size if isinstance(size, int) else shape_vars.setdefault(size, real_size)
      for size, real_size in zip(expected_shape, arg.shape))
    if arg.shape != inferred_shape:
      raise RuntimeError(f"shape mismatch in arg {i}: expected {inferred_shape}, got {arg.shape}")
  # Infer result types
  result_avals = []
  for b in res_sig:
    dtype = np.dtype(b.type.ctype)
    if isinstance(b.type, ScalarType):
      shape = ()
    elif isinstance(b.type, RectContArrayType):
      shape = tuple(shape_vars.get(size, size) for size in b.type.shape)
    result_avals.append(jax.core.ShapedArray(shape, dtype))
  assert len(result_avals) == 1  # TODO: Make dex_call a multiple_results primitive
  return result_avals[0]

# TODO
# jax.interpreters.xla.backend_specific_translations['cpu'][self.primitive] = ...
# jax.interpreters.batching.primitive_batchers[self.primitive] = ...
# jax.interpreters.ad.primitive_jvps[self.primitive] = ...
# jax.interpreters.ad.primitive_transposes[self.primitive] = ...
