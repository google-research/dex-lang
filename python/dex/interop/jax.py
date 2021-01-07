# Copyright 2020 Google LLC
#
# Use of this source code is governed by a BSD-style
# license that can be found in the LICENSE file or at
# https://developers.google.com/open-source/licenses/bsd

from weakref import WeakKeyDictionary
from functools import partial
from itertools import count
import ctypes
import numpy as np

import jax
from jax.lib import xla_client as xc
from jax.interpreters import xla

from .. import Atom
from ..native_function import IdxRepTy, ScalarType, RectContArrayType

def primitive(f):
  if not isinstance(f, Atom):
    raise TypeError("DexPrimitive expects a function atom as an argument")
  return partial(dex_call_p.bind, func_atom=f)

compiler_cache = WeakKeyDictionary()
def get_compiled(func_atom):
  compiled = compiler_cache.get(func_atom, None)
  if compiled is None:
    compiled = compiler_cache[func_atom] = func_atom.compile()
  return compiled


dex_call_p = jax.core.Primitive('dex_call')

@dex_call_p.def_impl
def dex_call_impl(*args, func_atom):
  return get_compiled(func_atom)(*args)

# === abstract evaluation / shape inference ===

def dex_call_abstract_eval_with_shape(*args, func_atom):
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
  return result_avals[0], shape_vars

@dex_call_p.def_abstract_eval
def dex_call_abstract_eval(*args, **kwargs):
  return dex_call_abstract_eval_with_shape(*args, **kwargs)[0]

# === xla translation ===

PyCapsule_Destructor = ctypes.CFUNCTYPE(None, ctypes.py_object)
PyCapsule_New = ctypes.pythonapi.PyCapsule_New
PyCapsule_New.restype = ctypes.py_object
PyCapsule_New.argtypes = (ctypes.c_void_p, ctypes.c_char_p, PyCapsule_Destructor)

def make_custom_call_target(func_ptr):
  return PyCapsule_New(func_ptr, b"xla._CUSTOM_CALL_TARGET", PyCapsule_Destructor(0))

# TODO: Better lifetime management. func_atoms will be quite often created on the fly
#       at trace time when different transforms are applied, and I'm pretty sure that
#       the XLA executables outlive jaxprs formed by tracing.
custom_call_id = count()
custom_call_cache = {}
def dex_call_cpu_translation(b, *args, func_atom):
  xla_shapes = list(map(b.get_shape, args))
  result_aval, shape_vars = dex_call_abstract_eval_with_shape(
      *(jax.core.ShapedArray(xshape.dimensions(), xshape.numpy_dtype())
        for xshape in xla_shapes),
      func_atom=func_atom)
  result_xshape = xc.Shape.array_shape(result_aval.dtype, result_aval.shape)

  custom_call = custom_call_cache.get(func_atom, None)
  native = get_compiled(func_atom)
  if custom_call is None:
    assert len(args) == len(native.explicit_argument_signature)
    assert 1 == len(native.result_signature)
    custom_call_ctype = ctypes.CFUNCTYPE(None,
                                         ctypes.c_void_p,
                                         ctypes.POINTER(ctypes.c_void_p * len(args)))
    @custom_call_ctype
    def trampoline(result_ptr, arg_ptr_array):
      name_to_cval = {name: IdxRepTy(value) for name, value in shape_vars.items()}
      for binder, ptr in zip(native.explicit_argument_signature, arg_ptr_array.contents):
        if isinstance(binder.type, ScalarType):
          cval = ctypes.cast(ptr, ctypes.POINTER(binder.type.arg_ctype)).contents
        elif isinstance(binder.type, RectContArrayType):
          cval = ctypes.cast(ptr, binder.type.arg_ctype)
        else:
          raise AssertionError("Unexpected binder type")
        name_to_cval[binder.name] = cval
      result_binder = native.result_signature[0]
      name_to_cval[result_binder.name] = ctypes.cast(result_ptr, result_binder.type.ref_ctype)
      native.callable(*(name_to_cval[name] for name in native.ccall_signature))

    trampoline_addr = ctypes.c_void_p.from_param(trampoline)
    custom_call_name = f"dex_custom_call{next(custom_call_id)}".encode('ascii')
    xc.register_custom_call_target(custom_call_name,
                                   make_custom_call_target(trampoline_addr))
    custom_call_cache[func_atom] = (custom_call_name, trampoline)
    # TODO: Unregister custom calls at some point?
  else:
    custom_call_name, *_ = custom_call
  return xc.ops.CustomCall(b, custom_call_name, operands=args, shape=result_xshape)

jax.interpreters.xla.backend_specific_translations['cpu'][dex_call_p] = dex_call_cpu_translation

# TODO
# jax.interpreters.batching.primitive_batchers[self.primitive] = ...
# jax.interpreters.ad.primitive_jvps[self.primitive] = ...
# jax.interpreters.ad.primitive_transposes[self.primitive] = ...
