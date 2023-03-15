# Copyright 2023 Google LLC
#
# Use of this source code is governed by a BSD-style
# license that can be found in the LICENSE file or at
# https://developers.google.com/open-source/licenses/bsd

import json
import numpy as np
import jax
from jax._src import core
from jax._src.lax import lax

def dump_jaxpr(jaxpr: core.ClosedJaxpr) -> dict:
  # TODO Serialize effects
  assert jaxpr.effects == core.no_effects
  # Ignoring debug info
  return dict(invars=[dump_var(v) for v in jaxpr.jaxpr.invars],
              outvars=[dump_atom(x) for x in jaxpr.jaxpr.outvars],
              eqns=[dump_eqn(e) for e in jaxpr.jaxpr.eqns],
              constvars=[dump_var(v) for v in jaxpr.jaxpr.constvars],
              consts=jaxpr.consts
              )

def dump_atom(x):
  if type(x) is core.Var:
    return dict(var=dump_var(x))
  elif type(x) is core.Literal:
    return dict(lit=dump_lit(x))
  # TODO DropVar ?

def dump_var(v):
  # Option: remove count and suffix to shrink the size of the generated json.
  return dict(name=id(v), count=v.count, suffix=v.suffix, ty=dump_aval(v.aval))

def dump_lit(x):
  # TODO The type annotation in core.Literal allows the value of a
  # literal to be an arbitrary Python object.  Are they all actually
  # JSON-dumpable?
  return dict(val=x.val, ty=dump_aval(x.aval))

def dump_aval(a):
  # TODO Support other needful members of the AbstractValue hierarchy,
  # not just ShapedArray.
  # TODO Support weak_type, named_shape
  return dict(shape=a.shape, dtype=core._short_dtype_name(a.dtype))

def dump_eqn(e):
  # TODO Support effects
  # TODO Support source info
  return dict(primitive=e.primitive.name,
              params=e.params,
              invars=[dump_atom(x) for x in e.invars],
              outvars=[dump_var(v) for v in e.outvars])

def load_jaxpr(d) -> core.ClosedJaxpr:
  return load_jaxpr_local({}, d)

def load_jaxpr_local(var_map, d):
  invars = [load_var(var_map, v) for v in d['invars']]
  outvars = [load_atom(var_map, v) for v in d['outvars']]
  eqns = [load_eqn(var_map, v) for v in d['eqns']]
  constvars = [load_var(var_map, v) for v in d['constvars']]
  jaxpr = core.Jaxpr(constvars, invars, outvars, eqns)
  return core.ClosedJaxpr(jaxpr, d['consts'])

def load_atom(var_map, d):
  if 'var' in d:
    return load_var(var_map, d['var'])
  elif 'lit' in d:
    return load_lit(d['lit'])
  else:
    raise TypeError("Malformed serialized jax atom", d)

def load_var(var_map, d):
  if d['name'] not in var_map:
    aval = load_aval(d['ty'])
    var = core.Var(d['count'], d['suffix'], aval)
    var_map[d['name']] = var
  return var_map[d['name']]

def load_lit(d):
  return core.Literal(d['val'], load_aval(d['ty']))

# TODO Support the full range of JAX dtypes
short_dtype_names = dict(
    f32 = np.float32,
    f64 = np.float64,
    i32 = np.int32,
    i64 = np.int64)

# TODO Collect the complete set of JAX primitives properly
def jax_primitives():
  result = {}
  for name in dir(lax):
    obj = getattr(lax, name)
    if isinstance(obj, core.Primitive):
      result[obj.name] = obj
  return result

primitives = jax_primitives()

def load_aval(d):
  return core.ShapedArray(d['shape'], short_dtype_names[d['dtype']])

def load_eqn(var_map, d):
  prim = primitives[d['primitive']]
  invars = [load_atom(var_map, x) for x in d['invars']]
  outvars = [load_var(var_map, v) for v in d['outvars']]
  return core.JaxprEqn(invars, outvars, prim, d['params'], core.no_effects, None)
