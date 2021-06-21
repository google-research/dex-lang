# Copyright 2020 Google LLC
#
# Use of this source code is governed by a BSD-style
# license that can be found in the LICENSE file or at
# https://developers.google.com/open-source/licenses/bsd

import unittest
import numpy as np

import jax
import jax.numpy as jnp

import dex
from dex.interop.jax import primitive


class JAXTest(unittest.TestCase):

  def test_impl_scalar(self):
    add_two = primitive(dex.eval(r'\x:Float. x + 2.0'))
    x = jnp.zeros((), dtype=np.float32)
    np.testing.assert_allclose(add_two(x), x + 2.0)

  def test_impl_array(self):
    add_two = primitive(dex.eval(r'\x:((Fin 10)=>Float). for i. x.i + 2.0'))
    x = jnp.arange(10, dtype=np.float32)
    np.testing.assert_allclose(add_two(x), x + 2.0)

  def test_abstract_eval_simple(self):
    add_two = primitive(
        dex.eval(r'\x:((Fin 10)=>Float). for i. FToI $ x.i + 2.0'))
    x = jax.ShapeDtypeStruct((10,), np.float32)
    output_shape = jax.eval_shape(add_two, x)
    assert output_shape.shape == (10,)
    assert output_shape.dtype == np.int32

  def test_jit_scalar(self):
    add_two = primitive(dex.eval(r'\x:Float. x + 2.0'))
    x = jnp.zeros((), dtype=np.float32)
    np.testing.assert_allclose(jax.jit(add_two)(x), 2.0)

  def test_jit_array(self):
    add_two = primitive(
        dex.eval(r'\x:((Fin 10)=>Float). for i. FToI $ x.i + 2.0'))
    x = jnp.zeros((10,), dtype=np.float32)
    np.testing.assert_allclose(jax.jit(add_two)(x), (x + 2.0).astype(np.int32))

  def test_jit_scale(self):
    scale = primitive(dex.eval(r'\x:((Fin 10)=>Float) y:Float. for i. x.i * y'))
    x = jnp.arange(10, dtype=np.float32)
    np.testing.assert_allclose(scale(x, 5.0), x * 5.0)

  def test_vmap(self):
    add_two = primitive(dex.eval(r'\x:((Fin 2)=>Float). for i. x.i + 2.0'))
    x = jnp.linspace([0, 3], [5, 8], num=4, dtype=jnp.float32)
    np.testing.assert_allclose(jax.vmap(add_two)(x), x + 2.0)

  def test_vmap_nonzero_index(self):
    add_two = primitive(dex.eval(r'\x:((Fin 4)=>Float). for i. x.i + 2.0'))
    x = jnp.linspace([0, 3], [5, 8], num=4, dtype=jnp.float32)
    np.testing.assert_allclose(
        jax.vmap(add_two, in_axes=1, out_axes=1)(x), x + 2.0)

  def test_vmap_unbatched_array(self):
    add_arrays = primitive(
        dex.eval(r'\x:((Fin 10)=>Float) y:((Fin 10)=>Float). for i. x.i + y.i'))
    x = jnp.arange(10, dtype=np.float32)
    y = jnp.linspace(
        jnp.arange(10), jnp.arange(10, 20), num=5, dtype=jnp.float32)
    np.testing.assert_allclose(
        jax.vmap(add_arrays, in_axes=[None, 0])(x, y), x + y)

  def test_vmap_jit(self):
    add_two = primitive(dex.eval(r'\x:((Fin 2)=>Float). for i. x.i + 2.0'))
    x = jnp.linspace([0, 3], [5, 8], num=4, dtype=jnp.float32)
    np.testing.assert_allclose(jax.jit(jax.vmap(add_two))(x), x + 2.0)

  def test_vmap_jit_nonzero_index(self):
    add_two = primitive(dex.eval(r'\x:((Fin 4)=>Float). for i. x.i + 2.0'))
    x = jnp.linspace([0, 3], [5, 8], num=4, dtype=jnp.float32)
    np.testing.assert_allclose(
        jax.jit(jax.vmap(add_two, in_axes=1, out_axes=1))(x), x + 2.0)


if __name__ == "__main__":
  unittest.main()
