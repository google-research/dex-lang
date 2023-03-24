# Copyright 2023 Google LLC
#
# Use of this source code is governed by a BSD-style
# license that can be found in the LICENSE file or at
# https://developers.google.com/open-source/licenses/bsd

import json
import jax
import numpy as np
from jax._src import core

def dump_jaxpr(jaxpr: core.ClosedJaxpr) -> dict:
  # TODO Serialize effects
  assert jaxpr.effects == core.no_effects
  return dict(jaxpr=dump_open_jaxpr(jaxpr.jaxpr),
              consts=jaxpr.consts
              )

def dump_open_jaxpr(jaxpr: core.Jaxpr) -> dict:
  # Ignoring debug info
  return dict(invars=[dump_var(v) for v in jaxpr.invars],
              outvars=[dump_atom(x) for x in jaxpr.outvars],
              eqns=[dump_eqn(e) for e in jaxpr.eqns],
              constvars=[dump_var(v) for v in jaxpr.constvars]
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
  return dict(shape=list(a.shape), dtype=dump_dtype(a.dtype))

def dump_dtype(dtype):
  return core._short_dtype_name(dtype)

def dump_eqn(e):
  # TODO Support effects
  # TODO Support source info
  name = e.primitive.name
  return dict(primitive=name,
              params=dump_params(name, e.params),
              invars=[dump_atom(x) for x in e.invars],
              outvars=[dump_var(v) for v in e.outvars])

def dump_params(name, params):
  result = params.copy()
  if name == 'scan':
    result['jaxpr'] = dump_jaxpr(params['jaxpr'])
    result['linear'] = list(params['linear'])
  if name == 'convert_element_type':
    result['new_dtype'] = dump_dtype(params['new_dtype'])
  return result

def load_jaxpr(d) -> core.ClosedJaxpr:
  return load_jaxpr_local({}, d)

def load_jaxpr_local(var_map, d):
  jaxpr = load_open_jaxpr(var_map, d['jaxpr'])
  return core.ClosedJaxpr(jaxpr, d['consts'])

def load_open_jaxpr(var_map, d):
  invars = [load_var(var_map, v) for v in d['invars']]
  outvars = [load_atom(var_map, v) for v in d['outvars']]
  eqns = [load_eqn(var_map, v) for v in d['eqns']]
  constvars = [load_var(var_map, v) for v in d['constvars']]
  return core.Jaxpr(constvars, invars, outvars, eqns)

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

# TODO Support the full range of JAX dtypes:
# numpy dtypes, bint, bfloat16
short_dtype_names = dict(
    f32 = np.dtype('float32'),
    f64 = np.dtype('float64'),
    i32 = np.dtype('int32'),
    i64 = np.dtype('int64'))

def load_dtype(obj):
  return short_dtype_names[obj]

# TODO Collect the complete set of JAX primitives properly
def jax_primitives():
  result = {}
  def process_module(mod):
    for name in dir(mod):
      obj = getattr(mod, name)
      if isinstance(obj, core.Primitive):
        result[obj.name] = obj
  from jax._src.lax import lax
  process_module(lax)
  from jax._src.lax.control_flow import loops
  process_module(loops)
  return result

primitives = jax_primitives()

def load_aval(d):
  return core.ShapedArray(tuple(d['shape']), load_dtype(d['dtype']))

def load_eqn(var_map, d):
  prim = primitives[d['primitive']]
  invars = [load_atom(var_map, x) for x in d['invars']]
  outvars = [load_var(var_map, v) for v in d['outvars']]
  params = load_params(var_map, d['primitive'], d['params'])
  return core.JaxprEqn(invars, outvars, prim, params, core.no_effects, None)

def load_params(var_map, name, d):
  result = d.copy()
  if name == 'scan':
    result['jaxpr'] = load_jaxpr_local(var_map, d['jaxpr'])
    result['linear'] = tuple(d['linear'])
  if name == 'convert_element_type':
    result['new_dtype'] = load_dtype(d['new_dtype'])
  return result
