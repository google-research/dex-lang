# Copyright 2023 Google LLC
#
# Use of this source code is governed by a BSD-style
# license that can be found in the LICENSE file or at
# https://developers.google.com/open-source/licenses/bsd

import json
import unittest

import jax
import jax.numpy as jnp
import dex.interop.jax.jaxpr_json as jj

def check_round_trip(jaxpr):
  dictified = jj.dump_jaxpr(jaxpr)
  dump_str = json.dumps(dictified, indent=2)
  reconstituted = json.loads(dump_str)
  jaxpr_recon = jj.load_jaxpr(reconstituted)
  assert str(jaxpr) == str(jaxpr_recon)

class JaxprJsonTest(unittest.TestCase):

  def test_one_prim(self):
    jaxpr = jax.make_jaxpr(jax.numpy.sin)(3.)
    check_round_trip(jaxpr)

  def test_literal(self):
    f = lambda x: jax.numpy.sin(x + 1) + 3
    check_round_trip(jax.make_jaxpr(f)(3.))

  def test_scan(self):
    def f(xs):
      return jax.lax.scan(lambda tot, z: (tot + z, tot), 0., xs)
    check_round_trip(jax.make_jaxpr(f)(jnp.array([1., 2., 3.])))

  # TODO Test bigger shapes (matrices?)
  # TODO Test dependent shapes (that have variables in them)
  # TODO Test more funny primitives like scan (scan itself works)
