# Copyright 2020 Google LLC
#
# Use of this source code is governed by a BSD-style
# license that can be found in the LICENSE file or at
# https://developers.google.com/open-source/licenses/bsd

import unittest
import ctypes
import numpy as np
from textwrap import dedent

# TODO: Write a proper setup.py instead of using this hack...
from pathlib import Path
import sys
sys.path.append(str(Path(__file__).parent.parent))

import dex

def test_eval():
  cases = [
    "2.5",
    "4",
    "[2, 3, 4]",
  ]
  for expr in cases:
    assert str(dex.eval(expr)) == expr

def test_module_attrs():
  m = dex.Module(dedent("""
  x = 2.5
  y = [2, 3, 4]
  """))
  assert str(m.x) == "2.5"
  assert str(m.y) == "[2, 3, 4]"

def test_function_call():
  m = dex.Module(dedent("""
  def addOne (x: Float) : Float = x + 1.0
  """))
  x = dex.eval("2.5")
  y = dex.eval("[2, 3, 4]")
  assert str(m.addOne(x)) == "3.5"
  assert str(m.sum(y)) == "9"

def test_scalar_conversions():
  assert float(dex.eval("5.0")) == 5.0
  assert int(dex.eval("5")) == 5

def test_jit():
  m = dex.eval(r"\x:Float. 1.0 / (1.0 + exp(-x))")
  native_func = m.compile()
  func_ptr = ctypes.cast(native_func.ptr, ctypes.c_void_p).value
  signature = ctypes.CFUNCTYPE(ctypes.c_int64, ctypes.c_float, ctypes.POINTER(ctypes.c_float))
  func = signature(func_ptr)

  def dex_sigmoid(x):
    res = ctypes.c_float()
    has_error = func(x, ctypes.pointer(res))
    assert not has_error
    return res.value

  one = np.float32(1.0)
  def py_sigmoid(x): return one / (one + np.exp(-x))

  for value in map(np.float32, (-1.0, -0.5, 0.0, 0.5, 1.0)):
    np.testing.assert_allclose(dex_sigmoid(value), py_sigmoid(value),
                               rtol=1e-4, atol=1e-6)
