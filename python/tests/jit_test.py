# Copyright 2020 Google LLC
#
# Use of this source code is governed by a BSD-style
# license that can be found in the LICENSE file or at
# https://developers.google.com/open-source/licenses/bsd

import unittest
import ctypes
import numpy as np
import itertools as it
from textwrap import dedent

import dex

example_floats = list(map(np.float32, (-1.0, -0.5, 0.0, 0.5, 1.0)))
example_ints = [-10, -5, 0, 5, 10]

def check_atom(dex_atom, reference, args_iter):
  compiled = dex_atom.compile()
  ran_any_iter = False
  for args in args_iter:
    ran_any_iter = True
    np.testing.assert_allclose(compiled(*args), reference(*args),
                               rtol=1e-4, atol=1e-6)
  assert ran_any_iter, "Empty argument iterator!"

def expr_test(dex_source, reference, args_iter):
  def test(self):
    return check_atom(dex.eval(dex_source), reference, args_iter)
  return test

class JITTest(unittest.TestCase):
  test_sigmoid = expr_test(r"\x:Float. 1.0 / (1.0 + exp(-x))",
                           lambda x: np.float32(1.0) / (np.float32(1.0) + np.exp(-x)),
                           ((x,) for x in example_floats))

  test_multi_arg = expr_test(r"\x:Float y:Float. atan2 x y",
                             np.arctan2,
                             ((x + 0.01, y) for x, y in it.product(example_floats, repeat=2)
                              if (x, y) != (0.0, 0.0)))

  test_int_arg = expr_test(r"\x:Int64 y:Int. i64_to_i x + y",
                           lambda x, y: x + y,
                           it.product(example_ints, example_ints))

  test_array_scalar = expr_test(r"\x:((Fin 10)=>Float). sum x",
                                np.sum,
                                [(np.arange(10, dtype=np.float32),)])

  test_scalar_array = expr_test(r"\x:Int. for i:(Fin 10). x + n_to_i (ordinal i)",
                                lambda x: x + np.arange(10, dtype=np.int32),
                                [(i,) for i in range(5)])

  test_array_array = expr_test(r"\x:((Fin 10)=>Float). for i. exp x.i",
                               np.exp,
                               [(np.arange(10, dtype=np.float32),)])

  def test_polymorphic_array_1d(self):
    m = dex.Module(dedent("""
    def addTwo {n} (x: (Fin n)=>Float) : (Fin n)=>Float = for i. x.i + 2.0
    """))
    check_atom(m.addTwo, lambda x: x + 2,
               [(np.arange(l, dtype=np.float32),) for l in (2, 5, 10)])

  def test_polymorphic_array_2d(self):
    m = dex.Module(dedent("""
    def myTranspose {n m} (x : (Fin n)=>(Fin m)=>Float) : (Fin m)=>(Fin n)=>Float =
      for i j. x.j.i
    """))
    check_atom(m.myTranspose, lambda x: x.T,
               [(np.arange(a*b, dtype=np.float32).reshape((a, b)),)
                for a, b in it.product((2, 5, 10), repeat=2)])

  def test_tuple_return(self):
    dex_func = dex.eval(r"\x: ((Fin 10) => Float). (x, 2. .* x, 3. .* x)")
    reference = lambda x: (x, 2 * x, 3 * x)

    x = np.arange(10, dtype=np.float32)

    dex_output = dex_func.compile()(x)
    reference_output = reference(x)

    self.assertEqual(len(dex_output), len(reference_output))
    for dex_array, ref_array in zip(dex_output, reference_output):
      np.testing.assert_allclose(dex_array, ref_array)

  def test_arrays_of_nats(self):
    dex_func = dex.eval(r"\x: ((Fin 10) => Nat). x + x")
    reference = lambda x: x + x

    x = np.arange(10, dtype=np.uint32)

    dex_output = dex_func.compile()(x)
    reference_output = reference(x)
    np.testing.assert_allclose(dex_output, reference_output)

if __name__ == "__main__":
  unittest.main()
