# Copyright 2022 Google LLC
#
# Use of this source code is governed by a BSD-style
# license that can be found in the LICENSE file or at
# https://developers.google.com/open-source/licenses/bsd

import unittest
import numpy as np
from functools import partial
from contextlib import contextmanager

import jax
import jax.numpy as jnp
from jax import lax
from jax.experimental import enable_x64

from dex.interop.jax import dexjit

def lax_test(prim, arg_thunk, **kwargs):
  def test(self):
    f = dexjit(partial(prim, **kwargs))
    args = arg_thunk()
    np.testing.assert_allclose(f(*args), prim(*args, **kwargs), atol=1e-6, rtol=1e-6)
    with enable_x64(), default_f64():
      args = arg_thunk()
      try:
        y = f(*args)
      except NotImplementedError:
        # Not all ops have to support 64-bit floats
        pass
      else:
        # ... but when they do, they better give good answers!
        np.testing.assert_allclose(y, prim(*args, **kwargs))
  return test

@contextmanager
def default_f64():
  global FP_DTYPE
  old_dtype = FP_DTYPE
  FP_DTYPE = np.dtype('float64')
  try:
    yield
  finally:
    FP_DTYPE = old_dtype

FP_DTYPE = np.dtype('float32')
def rn(*shape):
  return np.random.default_rng(seed=1).normal(size=shape).astype(FP_DTYPE)

class JAX2DexTest(unittest.TestCase):
  test_sin = lax_test(lax.sin, lambda: (rn(10, 10),))
  test_cos = lax_test(lax.cos, lambda: (rn(10, 10),))
  test_neg = lax_test(lax.neg, lambda: (rn(10, 10),))
  test_neg_scalar = lax_test(lax.neg, lambda: (rn(),))
  test_log = lax_test(lax.log, lambda: (rn(10, 10),))
  test_exp = lax_test(lax.exp, lambda: (rn(10, 10),))
  test_pow = lax_test(lax.pow, lambda: (rn(10), jnp.arange(10, dtype=FP_DTYPE)))
  test_integer_pow = lax_test(lambda x: lax.integer_pow(x, 2), lambda: (rn(10, 10),))
  test_scalar_select_lt = lax_test(lambda i, x, y: lax.select(i < 2.0, x, y),
                                   lambda: (1.0, rn(10), rn(10)))
  test_array_select_lt = lax_test(lambda i, x, y: lax.select(i < 0.0, x, y),
                                  lambda: (rn(10), rn(10), rn(10)))

  test_squeeze_none = lax_test(lambda x: lax.squeeze(x, [ ]), lambda: (rn(10, 10),))
  test_squeeze_one = lax_test(lambda x: lax.squeeze(x, [1]), lambda: (rn(10, 1, 10),))
  test_squeeze_two = lax_test(lambda x: lax.squeeze(x, [0, 2]), lambda: (rn(1, 10, 1),))
  test_squeeze_all = lax_test(lambda x: lax.squeeze(x, [0, 1]), lambda: (rn(1, 1),))

  test_slice_1d = lax_test(lambda x: lax.slice(x, [2], [5], None), lambda: (rn(10),))
  test_slice_3d = lax_test(lambda x: lax.slice(x, [2, 0, 0], [5, 10, 2], None), lambda: (rn(10, 10, 2),))

  test_concat_uniform = lax_test(partial(lax.concatenate, dimension=0),
                                 lambda: ([rn(4, 2) for _ in range(3)],))
  test_concat_ragged = lax_test(partial(lax.concatenate, dimension=0),
                                lambda: ([rn(1, 2, 4), rn(5, 2, 4), rn(2, 2, 4)],))

  test_dot_general_matmul = lax_test(partial(lax.dot_general, dimension_numbers=(((1,), (0,)), ((), ()))),
                                     lambda: (rn(4, 8), rn(8, 16)))
  test_dot_general_matvec = lax_test(partial(lax.dot_general, dimension_numbers=(((1,), (0,)), ((), ()))),
                                     lambda: (rn(4, 8), rn(8)))

  def test_canonicalize_dtype(self):
    c = np.arange(5, dtype=np.float64)
    f = lambda x: x * c
    x = np.ones(5, dtype=np.float64)
    dy = dexjit(f)(x)
    jy = jax.jit(f)(x)
    np.testing.assert_allclose(dy, jy)
    self.assertEqual(dy.dtype, jy.dtype)

  def test_64_bit(self):
    def f(x):
      return x * x + 4.0
    x = np.float64(2.0)
    with enable_x64():
      np.testing.assert_allclose(dexjit(f)(x), 8.0)

  def test_jit(self):
    g = dexjit(lambda y: y * y)
    f = jax.jit(lambda x: x * g(x))
    x = jnp.arange(5)
    np.testing.assert_allclose(f(x), x * x * x)

  def test_jit_two_outputs(self):
    f = jax.jit(dexjit(lambda x, y: (x + 1, y * 4)))
    x = jnp.arange(10, dtype=np.float32)
    y = 5.0
    for l, r in zip(f(x, y), (x + 1, y * 4)):
      np.testing.assert_allclose(l, r)


def check_broadcasting_pointwise(prim, full=False):
  setattr(JAX2DexTest, 'test_' + prim.__name__,
          lax_test(prim, lambda: (rn(10, 10), rn(10, 10))))
  if full:
    setattr(JAX2DexTest, 'test_' + prim.__name__ + '_expand',
            lax_test(prim, lambda: (rn(10, 10), rn(10, 1))))
    setattr(JAX2DexTest, 'test_' + prim.__name__ + '_scalar',
            lax_test(prim, lambda: (rn(10, 10), rn())))
check_broadcasting_pointwise(lax.add, full=True)
check_broadcasting_pointwise(lax.mul)
check_broadcasting_pointwise(lax.sub)
check_broadcasting_pointwise(lax.div)
check_broadcasting_pointwise(lax.max)


if __name__ == "__main__":
  unittest.main()
