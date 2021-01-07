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

import jax
import jax.numpy as jnp

import dex
from dex.interop.jax import primitive

def test_impl_scalar():
  add_two = primitive(dex.eval(r'\x:Float. x + 2.0'))
  x = jnp.zeros((), dtype=np.float32)
  np.testing.assert_allclose(add_two(x), x + 2.0)

def test_impl_array():
  add_two = primitive(dex.eval(r'\x:((Fin 10)=>Float). for i. x.i + 2.0'))
  x = jnp.arange((10,), dtype=np.float32)
  np.testing.assert_allclose(add_two(x), x + 2.0)

def test_abstract_eval_simple():
  add_two = primitive(dex.eval(r'\x:((Fin 10)=>Float). for i. FToI $ x.i + 2.0'))
  x = jax.ShapeDtypeStruct((10,), np.float32)
  output_shape = jax.eval_shape(add_two, x)
  assert output_shape.shape == (10,)
  assert output_shape.dtype == np.int32

def test_jit_scalar():
  add_two = primitive(dex.eval(r'\x:Float. x + 2.0'))
  x = jnp.zeros((), dtype=np.float32)
  np.testing.assert_allclose(jax.jit(add_two)(x), 2.0)

def test_jit_array():
  add_two = primitive(dex.eval(r'\x:((Fin 10)=>Float). for i. FToI $ x.i + 2.0'))
  x = jnp.zeros((10,), dtype=np.float32)
  np.testing.assert_allclose(jax.jit(add_two)(x), (x + 2.0).astype(np.int32))

def test_jit_scale():
  scale = primitive(dex.eval(r'\x:((Fin 10)=>Float) y:Float. for i. x.i * y'))
  x = jnp.arange((10,), dtype=np.float32)
  np.testing.assert_allclose(scale(x, 5.0), x * 5.0)
