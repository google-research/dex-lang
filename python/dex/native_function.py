# Copyright 2020 Google LLC
#
# Use of this source code is governed by a BSD-style
# license that can be found in the LICENSE file or at
# https://developers.google.com/open-source/licenses/bsd

import sys
import ctypes
import string
import numpy as np
from typing import Any, List, Union, Callable, Dict
from dataclasses import dataclass
from . import api

ScalarCType = Union[
  ctypes.c_int64, ctypes.c_int32,
  ctypes.c_uint8,
  ctypes.c_double, ctypes.c_float
]
IdxRepTy = ctypes.c_int32

@dataclass(frozen=True)
class ScalarType:
  ctype: Any
  from_ctype: Callable

  @property
  def arg_ctype(self): return self.ctype

  @property
  def ref_ctype(self): return ctypes.POINTER(self.ctype)

  def to_ctype(self, value, name_cvalue):
    return self.ctype(value)

  def create(self, name_cvalue):
    instance = self.ctype()
    return ctypes.pointer(instance), lambda: self.from_ctype(instance)


@dataclass(frozen=True)
class RectContArrayType:
  ctype: ScalarType
  shape: List[Union[str, int]]

  @property
  def arg_ctype(self):
    return ctypes.POINTER(self.ctype)

  @property
  def ref_ctype(self):
    return ctypes.POINTER(self.ctype)

  def unsafe_array_ptr(self, array):
    ptr, _ = array.__array_interface__['data']
    return ctypes.cast(ctypes.c_void_p(ptr), ctypes.POINTER(self.ctype))

  def to_ctype(self, array, name_cvalue):
    if not isinstance(array, np.ndarray):
      array = np.asarray(array)
    if array.ndim != len(self.shape):
      raise ValueError(f"Expected a {len(self.shape)}D array, got {array.ndim}D")
    expected_dtype = np.dtype(self.ctype)
    if array.dtype != expected_dtype:
      raise ValueError(f"Expected a {expected_dtype} array, got {array.dtype}")
    expected_shape = tuple(
        size if isinstance(size, int) else name_cvalue.setdefault(size, IdxRepTy(real_size)).value
        for size, real_size in zip(self.shape, array.shape))
    if expected_shape != array.shape:
      raise ValueError(f"Shape mismatch: expected {expected_shape}, but got {array.shape}")
    if not array.flags['C_CONTIGUOUS']:
      raise ValueError("Only contiguous arrays supported as arguments at the moment")
    return self.unsafe_array_ptr(array)

  def create(self, name_cvalue):
    shape = [size if isinstance(size, int) else name_cvalue[size].value
             for size in self.shape]
    result = np.empty(shape, dtype=self.ctype)
    return self.unsafe_array_ptr(result), lambda: result

NativeType = Union[ScalarType, RectContArrayType]


@dataclass(frozen=True)
class Binder:
  name: str
  type: NativeType
  implicit: bool


class NativeFunction:
  def __init__(self, jit, ptr):
    self._as_parameter_ = ptr
    self._jit = jit
    sig_ptr = api.getFunctionSignature(jit, ptr)
    if not sig_ptr:
      raise RuntimeError("Failed to retrieve the function signature")
    try:
      signature = sig_ptr.contents
      self.argument_signature = _SignatureParser(signature.arg).parse()
      self.explicit_argument_signature = [arg for arg in self.argument_signature if not arg.implicit]
      self.result_signature = _SignatureParser(signature.res).parse()
      self.ccall_signature = [sys.intern(arg.decode('ascii')) for arg in signature.ccall.split(b',')]
    finally:
      api.freeFunctionSignature(sig_ptr)

    func_type = ctypes.CFUNCTYPE(
        ctypes.c_int64,
        *(arg.type.arg_ctype for arg in self.argument_signature),
        *(res.type.ref_ctype for res in self.result_signature))
    self.callable = func_type(ctypes.cast(ptr, ctypes.c_void_p).value)

  def __del__(self):
    if api.nofree: return
    if hasattr(self, '_as_parameter_'):
      api.unload(self._jit, self)

  def __call__(self, *args):
    name_to_cval = {}
    result_thunks = []
    assert len(self.explicit_argument_signature) == len(args)
    for arg, binder in zip(args, self.explicit_argument_signature):
      name_to_cval[binder.name] = binder.type.to_ctype(arg, name_to_cval)
    for binder in self.result_signature:
      value, result_thunk = binder.type.create(name_to_cval)
      name_to_cval[binder.name] = value
      result_thunks.append(result_thunk)
    self.callable(*(name_to_cval[name] for name in self.ccall_signature))
    results = tuple(thunk() for thunk in result_thunks)
    if len(results) == 1:
      return results[0]
    else:
      return results


class _SignatureParser:
  __slots__ = ('text', 'offset')

  def __init__(self, text):
    self.text = text

  def consume(self, char: str):
    assert self.text[self.offset] == ord(char)
    self.offset += 1

  def maybe_consume(self, char: str) -> bool:
    if self.offset < len(self.text) and self.text[self.offset] == ord(char):
      self.offset += 1
      return True
    return False

  digit_codes = set(string.digits.encode('ascii'))
  name_codes = set(string.ascii_letters.encode('ascii')) | digit_codes

  def parse_name(self) -> str:
    end = self.offset
    name_codes = self.name_codes
    text = self.text
    while text[end] in name_codes:
      end += 1
    result = sys.intern(self.text[self.offset:end].decode('ascii'))
    self.offset = end
    return result

  scalar_types: Dict[bytes, ScalarType] = {
    b'i64': ScalarType(ctypes.c_int64, np.int64),
    b'i32': ScalarType(ctypes.c_int32, np.int32),
    b'u8': ScalarType(ctypes.c_uint8, np.uint8),
    b'f64': ScalarType(ctypes.c_double, np.float64),
    b'f32': ScalarType(ctypes.c_float, np.float32),
  }

  def parse_type(self) -> NativeType:
    for name, scalar_type in self.scalar_types.items():
      if self.text.startswith(name, self.offset):
        break
    else:
      raise RuntimeError(f"Invalid type specification: {sig[self.offset:self.offset+3].decode('ascii')}")
    self.offset += len(name)
    if self.maybe_consume('['):
      if self.maybe_consume('?'):
        raise RuntimeError("Only rectangular array types supported")
      shape = []
      while True:
        shape.append(self.parse_dim())
        if self.maybe_consume(']'):
          break
        else:
          self.consume(',')
      return RectContArrayType(scalar_type.ctype, shape)
    else:
      return scalar_type

  def parse_dim(self):
    if self.text[self.offset] in self.digit_codes:
      return self.parse_number()
    else:
      return self.parse_name()

  def parse_number(self) -> int:
    end = self.offset
    while self.text[end] in self.digit_codes:
      end += 1
    result = int(self.text[self.offset:end].decode('ascii'))
    self.offset = end
    return result

  def parse(self):
    self.offset = 0
    binders = []
    while True:
      implicit = self.maybe_consume('?')
      name = self.parse_name()
      self.consume(':')
      ty = self.parse_type()
      binders.append(Binder(name, ty, implicit))
      if self.offset == len(self.text):
        break
      else:
        self.consume(',')
    return binders
