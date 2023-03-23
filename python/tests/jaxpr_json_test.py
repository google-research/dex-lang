# Copyright 2023 Google LLC
#
# Use of this source code is governed by a BSD-style
# license that can be found in the LICENSE file or at
# https://developers.google.com/open-source/licenses/bsd

import json
import math
import unittest

import jax
import jax.numpy as jnp
from dex import api
from dex import native_function as nf
from dex import prelude
import dex.interop.jax.jaxpr_json as jj

def check_json_round_trip(jaxpr):
  dictified = jj.dump_jaxpr(jaxpr)
  dump_str = json.dumps(dictified, indent=2)
  reconstituted = json.loads(dump_str)
  jaxpr_recon = jj.load_jaxpr(reconstituted)
  assert str(jaxpr) == str(jaxpr_recon)

def check_haskell_round_trip(jaxpr):
  dictified = jj.dump_jaxpr(jaxpr)
  dump_str = json.dumps(dictified, indent=2)
  returned = api.from_cstr(api.roundtripJaxprJson(api.as_cstr(dump_str)))
  try:
    assert dictified == json.loads(returned)
  except json.decoder.JSONDecodeError:
    assert False, returned

class JaxprJsonTest(unittest.TestCase):

  def test_json_one_prim(self):
    jaxpr = jax.make_jaxpr(jax.numpy.sin)(3.)
    check_json_round_trip(jaxpr)

  def test_json_literal(self):
    f = lambda x: jax.numpy.sin(x + 1) + 3
    check_json_round_trip(jax.make_jaxpr(f)(3.))

  def test_json_scan(self):
    def f(xs):
      return jax.lax.scan(lambda tot, z: (tot + z, tot), 0.25, xs)
    check_json_round_trip(jax.make_jaxpr(f)(jnp.array([1., 2., 3.])))

  def test_haskell_one_prim(self):
    jaxpr = jax.make_jaxpr(jax.numpy.sin)(3.)
    check_haskell_round_trip(jaxpr)

  def test_haskell_literal(self):
    f = lambda x: jax.numpy.sin(x + 1) + 3
    check_haskell_round_trip(jax.make_jaxpr(f)(3.))

  def test_haskell_scan(self):
    def f(xs):
      return jax.lax.scan(lambda tot, z: (tot + z, tot), 0.25, xs)
    check_haskell_round_trip(jax.make_jaxpr(f)(jnp.array([1., 2., 3.])))

  def test_compute_one_prim(self):
    jaxpr = jax.make_jaxpr(jax.numpy.sin)(3.)
    jaxpr_dict = jj.dump_jaxpr(jaxpr)
    jaxpr_dump = json.dumps(jaxpr_dict, indent=2)
    module = prelude
    cc = api.FlatCC
    compiled = api.compileJaxpr(module, cc, api.as_cstr(jaxpr_dump))
    func = nf.NativeFunction(module, compiled, cc)
    self.assertAlmostEqual(func(3.), math.sin(3.))

  # TODO Test bigger shapes (matrices?)
  # TODO Test dependent shapes (that have variables in them)
  # - How do I make a jaxpr with such a thing in it?
  # TODO Test more funny primitives like scan (scan itself works)
