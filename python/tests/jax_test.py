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
    x = jnp.linspace(jnp.array([0, 3]), jnp.array([5, 8]), num=4, dtype=jnp.float32)
    np.testing.assert_allclose(jax.vmap(add_two)(x), x + 2.0)

  def test_vmap_nonzero_index(self):
    add_two = primitive(dex.eval(r'\x:((Fin 4)=>Float). for i. x.i + 2.0'))
    x = jnp.linspace(jnp.array([0, 3]), jnp.array([5, 8]), num=4, dtype=jnp.float32)
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
    x = jnp.linspace(jnp.array([0, 3]), jnp.array([5, 8]), num=4, dtype=jnp.float32)
    np.testing.assert_allclose(jax.jit(jax.vmap(add_two))(x), x + 2.0)

  def test_vmap_jit_nonzero_index(self):
    add_two = primitive(dex.eval(r'\x:((Fin 4)=>Float). for i. x.i + 2.0'))
    x = jnp.linspace(jnp.array([0, 3]), jnp.array([5, 8]), num=4, dtype=jnp.float32)
    np.testing.assert_allclose(
        jax.jit(jax.vmap(add_two, in_axes=1, out_axes=1))(x), x + 2.0)

  def test_jvp(self):
    f_dex = primitive(dex.eval(
        r'\x:((Fin 10) => Float) y:((Fin 10) => Float). '
        'for i. x.i * x.i + 2.0 * y.i'))

    def f_jax(x, y):
      return x**2 + 2 * y

    x  = jnp.arange(10.)
    y = jnp.linspace(-0.2, 0.5, num=10)
    u = jnp.linspace(0.1, 0.3, num=10)
    v = jnp.linspace(2.0, -5.0, num=10)

    output_dex, tangent_dex = jax.jvp(f_dex, (x, y), (u, v))
    output_jax, tangent_jax = jax.jvp(f_jax, (x, y), (u, v))

    np.testing.assert_allclose(output_dex, output_jax)
    np.testing.assert_allclose(tangent_dex, tangent_jax)

  def test_jvp_jit(self):
    f_dex = primitive(dex.eval(
        r'\x:((Fin 10) => Float) y:((Fin 10) => Float). '
        'for i. x.i * x.i + 2.0 * y.i'))

    def f_jax(x, y):
      return x**2 + 2 * y

    x  = jnp.arange(10.)
    y = jnp.linspace(-0.2, 0.5, num=10)
    u = jnp.linspace(0.1, 0.3, num=10)
    v = jnp.linspace(2.0, -5.0, num=10)

    def jvp_dex(args, tangents):
      return jax.jvp(f_dex, args, tangents)

    def jvp_jax(args, tangents):
      return jax.jvp(f_jax, args, tangents)

    output_dex, tangent_dex = jax.jit(jvp_dex)((x, y), (u, v))
    output_jax, tangent_jax = jax.jit(jvp_jax)((x, y), (u, v))

    np.testing.assert_allclose(output_dex, output_jax)
    np.testing.assert_allclose(tangent_dex, tangent_jax)

  def test_grad(self):
    f_dex = primitive(dex.eval(
        r'\x:((Fin 10) => Float). '
        'sum $ for i. (IToF $ ordinal i) * x.i * x.i'))

    def f_jax(x):
      return jnp.sum(jnp.arange(10.) * x**2)

    x = jnp.linspace(-0.2, 0.5, num=10)

    grad_dex = jax.grad(f_dex)(x)
    grad_jax = jax.grad(f_jax)(x)

    np.testing.assert_allclose(grad_dex, grad_jax)

  def test_grad_jit(self):
    f_dex = primitive(dex.eval(
        r'\x:((Fin 10) => Float). '
        'sum $ for i. (IToF $ ordinal i) * x.i * x.i'))

    def f_jax(x):
      return jnp.sum(jnp.arange(10.) * x**2)

    def grad_dex(x):
      return jax.grad(f_dex)(x)

    def grad_jax(x):
      return jax.grad(f_jax)(x)

    x = jnp.linspace(-0.2, 0.5, num=10)

    grad_dex_jit = jax.jit(grad_dex)(x)
    grad_jax_jit = jax.jit(grad_jax)(x)

    np.testing.assert_allclose(grad_dex_jit, grad_jax_jit)

  def test_grad_binary_function(self):
    f_dex = primitive(dex.eval(
        r'\x:((Fin 10) => Float) y:((Fin 10) => Float). '
        'sum $ for i. x.i * x.i + 2.0 * y.i'))

    def f_jax(x, y):
      return jnp.sum(x**2 + 2 * y)

    x  = jnp.arange(10.)
    y = jnp.linspace(-0.2, 0.5, num=10)

    np.testing.assert_allclose(
        jax.grad(f_dex, argnums=1)(x, y),
        jax.grad(f_jax, argnums=1)(x, y))

    np.testing.assert_allclose(
        jax.grad(f_dex, argnums=0)(x, y),
        jax.grad(f_jax, argnums=0)(x, y))

    np.testing.assert_allclose(
        jax.grad(f_dex, argnums=(0, 1))(x, y),
        jax.grad(f_jax, argnums=(0, 1))(x, y))

  def test_grad_binary_function_jit(self):
    f_dex = primitive(dex.eval(
        r'\x:((Fin 10) => Float) y:((Fin 10) => Float). '
        'sum $ for i. x.i * x.i + 2.0 * y.i'))

    def f_jax(x, y):
      return jnp.sum(x**2 + 2 * y)

    def grad_dex(x, y):
      return jax.grad(f_dex)(x, y)

    def grad_jax(x, y):
      return jax.grad(f_jax)(x, y)

    x  = jnp.arange(10.)
    y = jnp.linspace(-0.2, 0.5, num=10)

    np.testing.assert_allclose(
        jax.jit(grad_dex)(x, y),
        jax.jit(grad_jax)(x, y))


if __name__ == "__main__":
  unittest.main()
