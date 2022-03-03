from dataclasses import dataclass
from functools import partial
import itertools as it
import textwrap
from typing import Any, NamedTuple, Dict, Optional

import numpy as np

### First define an IR AST via dataclasses, slightly higher-level than Dex Core.

@dataclass
class Type:
  pass

@dataclass
class Expr:
  pass


@dataclass
class EType(Type):
  dtype: Any
  def pprint(self) -> str:
    if np.dtype(self.dtype) == np.dtype('float32'):
      return 'Float'
    elif np.dtype(self.dtype) == np.dtype('int32'):
      return 'Int32'
    else:
      raise NotImplementedError(self.dtype)

@dataclass
class FinTabType(Type):
  size: int  # TODO Expr
  ty: Type
  def pprint(self) -> str:
    return f'((Fin {self.size})=>{pprint(self.ty)})'

@dataclass
class FinType(Type):
  size: Expr
  def pprint(self) -> str:
    return f'(Fin {pprint(self.size)})'


@dataclass
class Literal(Expr):
  val: Any
  def pprint(self) -> str:
    return f'{self.val}'

@dataclass
class Var(Expr):
  name: str
  def pprint(self) -> str:
    return f'{self.name}'

@dataclass
class Tuple(Expr):
  elts: tuple[Expr]
  def pprint(self) -> str:
    elts_str = ','.join(f'({pprint(e)})' for e in self.elts)
    return f'({elts_str})'

@dataclass
class App(Expr):
  fun: Expr
  argument: Expr
  def pprint(self) -> str:
    return f'({pprint(self.fun)}) ({pprint(self.argument)})'

class Decl(NamedTuple):
  name: str
  expr: Expr

@dataclass
class Block:
  decls: list[Decl]
  expr: Expr

@dataclass
class Lam(Expr):
  name: str  # TODO generalize to multiple binders?
  ty: Type
  block: Block
  def pprint(self) -> str:
    ty = pprint(self.ty)
    decls = '\n'.join(f'{name} = {pprint(e)}' for name, e in self.block.decls)
    expr = pprint(self.block.expr)
    newline = '\n' if decls else ''
    block = textwrap.indent(f'{decls}{newline}{expr}', '  ')
    return f'\ {self.name}:{ty}.\n{block}'

@dataclass
class For(Expr):
  names: tuple[str]
  tys: tuple[Type]
  expr: Expr  # TODO generalize to Block?
  def pprint(self) -> str:
    binders = ' '.join(f'{name}:{pprint(ty)}'
                       for name, ty in zip(self.names, self.tys))
    return f'for {binders}. {pprint(self.expr)}'

@dataclass
class Idx(Expr):
  tab: Expr
  idxs: tuple[Expr]
  def pprint(self) -> str:
    idx_strs = '.'.join(f'({pprint(i)})' for i in self.idxs)
    return f'({pprint(self.tab)}).{idx_strs}'


### We build AST instances via a jaxpr interpreter.

from collections import defaultdict
from itertools import count, product
from string import ascii_lowercase
from typing import Callable

import jax
from jax import core
from jax import linear_util as lu
from jax.core import ShapedArray
from jax.interpreters import partial_eval as pe
from jax._src.tree_util import (tree_flatten, tree_unflatten, PyTreeDef,
                                broadcast_prefix)
from jax._src import dtypes
from jax._src.api_util import flatten_fun
from jax._src.traceback_util import api_boundary
from jax._src.util import (unzip2, wraps, split_list, partition_list, safe_map,
                           safe_zip, cache)

from .. import eval

map = safe_map
zip = safe_zip

# TODO this is for dynamic shapes, only partially implemented
@dataclass(frozen=True)
class DBIdx:
  val: int

def dexjit(fun: Callable, *, abstracted_axes: Optional[Any] = None) -> Callable:

  def shaped_abstractify(x):
    return core.raise_to_shaped(core.get_aval(x))

  def abstractify(args, kwargs):
    flat_args, in_tree = tree_flatten((args, kwargs))
    if abstracted_axes is None:
      return map(shaped_abstractify, flat_args), in_tree, [True] * len(flat_args)
    else:
      # TODO this is for dynamic shapes, replace w/ utilities in jax/api.py
      axes_specs = broadcast_prefix(abstracted_axes, args)
      sizes: Dict[Hashable, int] = {}  # for error checking
      counts = it.count()
      env: Dict[Hashable, int] = defaultdict(lambda: DBIdx(next(counts)))
      def make_aval(arg, spec):
        if not spec:
          return shaped_abstractify(arg)
        assert all(arg.shape[i] == sizes.setdefault(name, arg.shape[i])
                   for i, name in spec.items())
        shape = [env[spec[i]] if i in spec else d for i, d in enumerate(arg.shape)]
        return core.DShapedArray(tuple(shape), arg.dtype, False)
      in_avals = map(make_aval, flat_args, axes_specs)
      keep_inputs = [False] * len(env) + [True] * len(flat_args)
      return [*env.values(), *in_avals], in_tree, keep_inputs

  @wraps(fun)
  def dex_fun(*args, **kwargs):
    args_flat, in_tree = tree_flatten((args, kwargs))
    in_avals, in_tree_, keep_inputs = abstractify(args, kwargs)
    assert in_tree == in_tree_
    jaxpr, consts, out_tree = make_jaxpr(fun, in_tree, tuple(in_avals),
                                         tuple(keep_inputs))
    out_flat = dex_call_p.bind(*consts, *args_flat, jaxpr=jaxpr)
    return tree_unflatten(out_tree, out_flat)
  return dex_fun

# TODO try to delete this, rely on existing jax functions instead
@cache()
def make_jaxpr(fun: Callable, in_tree: PyTreeDef,
               in_avals: tuple[core.AbstractValue],  # with DBIdx in them
               keep_inputs: tuple[bool]
               ) -> tuple[core.Jaxpr, list[Any], PyTreeDef]:
  flat_fun, out_tree = flatten_fun(lu.wrap_init(fun), in_tree)
  debug = pe.debug_info(fun, in_tree, False, "dex_jit")
  jaxpr_, _, consts = pe.trace_to_jaxpr_dynamic(flat_fun, in_avals, debug,
                                                keep_inputs=keep_inputs)
  jaxpr = pe.convert_constvars_jaxpr(jaxpr_)
  return jaxpr, consts, out_tree()

dex_call_p = core.Primitive('dex_call')
dex_call_p.multiple_results = True

@dex_call_p.def_impl
def dex_call_impl(*args, jaxpr):
  dex_executable(jaxpr)
  return dex_executable(jaxpr)(*args),  # TODO tuples ignored?

@cache()
def dex_executable(jaxpr: core.Jaxpr) -> Callable:
  assert not jaxpr.constvars
  varnames = (''.join(chars) for n in count(1)
              for chars in product(ascii_lowercase, repeat=n))

  env: Dict[core.Var, Var] = {}

  def read(x: core.Atom) -> Expr:
    if type(x) is core.Literal:
      return Literal(x.val)
    else:
      return env[x]

  def typ(x: core.Atom) -> core.AbstractValue:
    if type(x) is core.Literal:
      return core.raise_to_shaped(core.get_aval(x.val))
    else:
      return x.aval

  def write(v: core.Var, val: str) -> None:
    env[v] = val

  for v in jaxpr.invars: write(v, Var(next(varnames)))
  decls = []
  for e in jaxpr.eqns:
    in_avals = [typ(x) for x in e.invars]
    out_avals = [v.aval for v in e.outvars]
    expr = expr_makers[e.primitive](in_avals, out_avals,
                                    *map(read, e.invars), **e.params)
    if e.primitive.multiple_results:
      assert False  # TODO
    else:
      name = next(varnames)
      decls.append(Decl(name, expr))
      write(e.outvars[0], Var(name))

  expr = Tuple(tuple(map(read, jaxpr.outvars)))
  block = Block(decls, expr)
  for v in reversed([*jaxpr.constvars, *jaxpr.invars]):
    expr = Lam(read(v).name, aval_to_type(v.aval), block)
    block = Block([], expr)
  print(jaxpr, end='\n\n')
  print(pprint(expr), end='\n\n')
  return eval(pprint(expr)).compile()

def pprint(e):
  return e.pprint()

ExprMaker = Callable[[Any, ...], Expr]
expr_makers: Dict[core.Primitive, ExprMaker] = {}

from jax._src.lax import lax

expr_makers[lax.neg_p] = lambda _, __, x: App(Var('neg'), x)
expr_makers[lax.sin_p] = lambda _, __, x: App(Var('sin'), x)
expr_makers[lax.cos_p] = lambda _, __, x: App(Var('cos'), x)

def _broadcast_in_dim(_, __, x, *dyn_shape, shape, broadcast_dimensions):
  idx_names = [f'i{newidx()}' for _ in range(len(shape))]
  dyn = iter(dyn_shape)
  tys = [FinType(next(dyn) if d is None else Literal(d)) for d in shape]
  idxs = [Var(idx_names[i]) for i in broadcast_dimensions]
  x_indexed = Idx(x, tuple(idxs)) if idxs else x
  return For(tuple(idx_names), tuple(tys), x_indexed)
expr_makers[lax.broadcast_in_dim_p] = _broadcast_in_dim

def _broadcasting_binop(name: str, in_avals, out_avals, x, y):
  x_aval, y_aval = in_avals
  out_aval, = out_avals
  if not out_aval.shape:
    return App(App(Var(name), x), y)
  idx_names, idx_tys = unzip2((f'i{newidx()}', FinType(Literal(sz)))
                              for sz in out_aval.shape)
  x_expr = _make_bcast_expr(idx_names, out_aval.shape, x_aval.shape, x)
  y_expr = _make_bcast_expr(idx_names, out_aval.shape, y_aval.shape, y)
  out = For(tuple(idx_names), tuple(idx_tys),
            App(App(Var(name), x_expr), y_expr))
  return out

def _make_bcast_expr(idx_names, out_shape, in_shape, x):
  idxs = [unitIdx if in_size != out_size else Var(idx_name)
          for idx_name, out_size, in_size in zip(idx_names, out_shape, in_shape)]
  return Idx(x, tuple(idxs))
unitIdx = Literal('(unsafeFromOrdinal (Fin 1) 0)')

expr_makers[lax.add_p] = partial(_broadcasting_binop, 'add')
expr_makers[lax.sub_p] = partial(_broadcasting_binop, 'sub')
expr_makers[lax.mul_p] = partial(_broadcasting_binop, 'mul')
expr_makers[lax.div_p] = partial(_broadcasting_binop, 'divide')

newidx = it.count().__next__

def aval_to_type(aval: core.AbstractValue) -> Type:
  if type(aval) is core.ShapedArray:
    ty = EType(aval.dtype)
    shape = list(aval.shape)
    while shape:
      ty = FinTabType(shape.pop(), ty)
    return ty
  else:
    raise NotImplementedError(aval)


###


