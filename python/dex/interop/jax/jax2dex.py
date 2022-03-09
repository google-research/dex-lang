from dataclasses import dataclass
from collections import defaultdict
from functools import partial
import itertools as it
import textwrap
import typing
from typing import Any, NamedTuple, Dict, Optional, List, Callable, Sequence
from string import ascii_lowercase
import numpy as np

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

from ... import eval

map = safe_map
zip = safe_zip


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
    return f'((Fin {self.size})=>{self.ty.pprint()})'

@dataclass
class FinType(Type):
  size: Expr
  def pprint(self) -> str:
    return f'(Fin {self.size.pprint()})'

@dataclass
class PairType(Type):
  lhs: Type
  rhs: Type
  def pprint(self) -> str:
    return f'({self.lhs.pprint()} & {self.rhs.pprint()})'

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
  elts: typing.Tuple[Expr]
  def pprint(self) -> str:
    elts_str = ','.join(f'({e.pprint()})' for e in self.elts)
    return f'({elts_str})'

@dataclass
class Table(Expr):
  elts: typing.Tuple[Expr]
  def pprint(self) -> str:
    elts_str = ','.join(e.pprint() for e in self.elts)
    return f'[{elts_str}]'

@dataclass
class BinOp(Expr):
  lhs: Expr
  operator: str
  rhs: Expr
  def pprint(self) -> str:
    return f'({self.lhs.pprint()} {self.operator} {self.rhs.pprint()})'

@dataclass
class App(Expr):
  fun: Expr
  argument: Expr
  def pprint(self) -> str:
    return f'({self.fun.pprint()}) ({self.argument.pprint()})'

class Decl(NamedTuple):
  name: str
  expr: Expr

@dataclass
class Block:
  decls: List[Decl]
  expr: Expr

@dataclass
class Lam(Expr):
  name: str  # TODO generalize to multiple binders?
  ty: Type
  block: Block
  def pprint(self) -> str:
    ty = self.ty.pprint()
    decls = '\n'.join(f'{name} = {e.pprint()}' for name, e in self.block.decls)
    expr = self.block.expr.pprint()
    newline = '\n' if decls else ''
    block = textwrap.indent(f'{decls}{newline}{expr}', '  ')
    return f'\ {self.name}:{ty}.\n{block}'

@dataclass
class For(Expr):
  names: typing.Tuple[str]
  tys: typing.Tuple[Type]
  expr: Expr  # TODO generalize to Block?
  def pprint(self) -> str:
    binders = ' '.join(f'{name}:{ty.pprint()}'
                       for name, ty in zip(self.names, self.tys))
    return f'for {binders}. {self.expr.pprint()}'

@dataclass
class Idx(Expr):
  tab: Expr
  idxs: typing.Tuple[Expr]
  def pprint(self) -> str:
    idx_strs = '.'.join(f'({i.pprint()})' for i in self.idxs)
    return f'({self.tab.pprint()}).{idx_strs}'


### We build AST instances via a jaxpr interpreter.

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
               in_avals: typing.Tuple[core.AbstractValue],  # with DBIdx in them
               keep_inputs: typing.Tuple[bool]
               ) -> typing.Tuple[core.Jaxpr, List[Any], PyTreeDef]:
  flat_fun, out_tree = flatten_fun(lu.wrap_init(fun), in_tree)
  debug = pe.debug_info(fun, in_tree, False, "dex_jit")
  jaxpr_, _, consts = pe.trace_to_jaxpr_dynamic(flat_fun, in_avals, debug,
                                                keep_inputs=keep_inputs)
  jaxpr = pe.convert_constvars_jaxpr(jaxpr_)
  consts = [_canonicalize_arg(c) for c in consts]
  return jaxpr, consts, out_tree()

def _canonicalize_arg(arg):
  return np.asarray(arg, dtype=dtypes.dtype(arg, canonicalize=True), order='C')

dex_call_p = core.Primitive('dex_call')
dex_call_p.multiple_results = True

@dex_call_p.def_impl
def dex_call_impl(*args, jaxpr):
  cargs_gen = (_canonicalize_arg(arg) for arg in args)
  return dex_executable(jaxpr)(*cargs_gen),  # TODO tuples ignored?

@cache()
def dex_executable(jaxpr: core.Jaxpr) -> Callable:
  assert not jaxpr.constvars
  varnames = (''.join(chars) for n in it.count(1)
              for chars in it.product(ascii_lowercase, repeat=n))

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
  counter = it.count()
  for e in jaxpr.eqns:
    in_avals = [typ(x) for x in e.invars]
    out_avals = [v.aval for v in e.outvars]
    ctx = LoweringRuleContext(counter, in_avals, out_avals)
    expr_or_block = expr_makers[e.primitive](ctx, *map(read, e.invars), **e.params)
    if e.primitive.multiple_results:
      assert False  # TODO
    else:
      name = next(varnames)
      if isinstance(expr_or_block, Expr):
        expr = expr_or_block
      elif isinstance(expr_or_block, Block):
        decls.extend(expr_or_block.decls)
        expr = expr_or_block.expr
      else:
        raise TypeError(f"Dex lowering rule should return either an expression or"
                        f"a block, but got: {type(expr_or_block)}")
      decls.append(Decl(name, expr))
      write(e.outvars[0], Var(name))

  expr = Tuple(tuple(map(read, jaxpr.outvars)))
  block = Block(decls, expr)
  for v in reversed([*jaxpr.constvars, *jaxpr.invars]):
    expr = Lam(read(v).name, aval_to_type(v.aval), block)
    block = Block([], expr)
  return eval(expr.pprint()).compile()

def aval_to_type(aval: core.AbstractValue) -> Type:
  if type(aval) is core.ShapedArray:
    ty = EType(aval.dtype)
    shape = list(aval.shape)
    while shape:
      ty = FinTabType(shape.pop(), ty)
    return ty
  else:
    raise NotImplementedError(aval)

### Dex translation rules for JAX primitives

ExprMaker = Callable  # [[Any, ...], Expr]
expr_makers: Dict[core.Primitive, ExprMaker] = {}

@dataclass
class LoweringRuleContext:
  _counter: Any
  avals_in: Sequence[core.AbstractValue]
  avals_out: Sequence[core.AbstractValue]

  def fresh(self, seed: str) -> str:
    return seed + str(next(self._counter))


from jax._src.lax import lax

expr_makers[lax.neg_p] = lambda ctx, x: App(Var('neg'), x)
expr_makers[lax.sin_p] = lambda ctx, x: App(Var('sin'), x)
expr_makers[lax.cos_p] = lambda ctx, x: App(Var('cos'), x)

def _broadcast_in_dim(ctx, x, *dyn_shape, shape, broadcast_dimensions):
  idx_names = [ctx.fresh('i') for _ in range(len(shape))]
  dyn = iter(dyn_shape)
  tys = [FinType(next(dyn) if d is None else Literal(d)) for d in shape]
  idxs = [Var(idx_names[i]) for i in broadcast_dimensions]
  x_indexed = Idx(x, tuple(idxs)) if idxs else x
  return For(tuple(idx_names), tuple(tys), x_indexed)
expr_makers[lax.broadcast_in_dim_p] = _broadcast_in_dim

def _broadcasting_binop(name: str, ctx, x, y):
  x_aval, y_aval = ctx.avals_in
  out_aval, = ctx.avals_out
  if not out_aval.shape:
    return App(App(Var(name), x), y)
  idx_names, idx_tys = unzip2((ctx.fresh('i'), FinType(Literal(sz)))
                              for sz in out_aval.shape)
  x_expr = _make_bcast_expr(idx_names, out_aval.shape, x_aval.shape, x)
  y_expr = _make_bcast_expr(idx_names, out_aval.shape, y_aval.shape, y)
  out = For(tuple(idx_names), tuple(idx_tys),
            App(App(Var(name), x_expr), y_expr))
  return out

def _make_bcast_expr(idx_names, out_shape, in_shape, x):
  ndim = len(in_shape)
  if not ndim:
    return x
  idxs = [unitIdx if in_size != out_size else Var(idx_name)
          for idx_name, out_size, in_size
          in zip(idx_names[-ndim:], out_shape[-ndim:], in_shape)]
  return Idx(x, tuple(idxs))
unitIdx = App(App(Var('unsafeFromOrdinal'), FinType(Literal(1))), Literal(0))

expr_makers[lax.add_p] = partial(_broadcasting_binop, 'add')
expr_makers[lax.sub_p] = partial(_broadcasting_binop, 'sub')
expr_makers[lax.mul_p] = partial(_broadcasting_binop, 'mul')
expr_makers[lax.div_p] = partial(_broadcasting_binop, 'divide')
expr_makers[lax.max_p] = partial(_broadcasting_binop, 'max')

def _squeeze_lowering(ctx, x, dimensions):
  in_aval, = ctx.avals_in
  out_aval, = ctx.avals_out
  if not out_aval.shape:
    return Idx(x, (unitIdx,))
  idx_names, idx_tys = unzip2((ctx.fresh('i'), FinType(Literal(sz)))
                              for sz in out_aval.shape)
  idx_name = iter(idx_names)
  idxs = [unitIdx if dim in dimensions else Var(next(idx_name))
          for dim in range(in_aval.ndim)]
  return For(tuple(idx_names), tuple(idx_tys), Idx(x, tuple(idxs)))
expr_makers[lax.squeeze_p] = _squeeze_lowering

def _slice_lowering(ctx, x, start_indices, limit_indices, strides):
  if strides is not None and any(s != 1 for s in strides):
    raise NotImplementedError("Strided slices not implemented yet!")
  in_aval, = ctx.avals_in
  out_aval, = ctx.avals_out
  assert len(start_indices) == len(limit_indices) == in_aval.ndim == out_aval.ndim
  idx_names, idx_tys = unzip2((ctx.fresh('i'), FinType(Literal(sz)))
                              for sz in out_aval.shape)
  input_ixs = [Var(ix) if in_size == out_size else
               App(App(Var('unsafeFromOrdinal'), FinType(Literal(in_size))),
                   BinOp(Literal(start), '+', App(Var('ordinal'), Var(ix))))
               for ix, in_size, out_size, start
               in zip(idx_names, in_aval.shape, out_aval.shape, start_indices)]
  return For(tuple(idx_names), tuple(idx_tys), Idx(x, tuple(input_ixs)))
expr_makers[lax.slicing.slice_p] = _slice_lowering

def _dot_general_lowering(ctx, lhs, rhs, dimension_numbers, precision, preferred_element_type):
  if precision is not None:
    raise NotImplementedError("Precision control in dot_general not implemented")
  if preferred_element_type is not None:
    raise NotImplementedError("dtype selection in dot_general not implemented")
  lhs_aval, rhs_aval = ctx.avals_in
  # Matrix-matrix multiply
  if (lhs_aval.ndim == 2 and rhs_aval.ndim == 2 and
      dimension_numbers == (((1,), (0,)), ((), ()))):
    return BinOp(lhs, '**', rhs)
  # Matrix-vector multiply
  if (lhs_aval.ndim == 2 and rhs_aval.ndim == 1 and
      dimension_numbers == (((1,), (0,)), ((), ()))):
    return BinOp(lhs, '**.', rhs)
  raise NotImplementedError("Unimplemented dot_general kind")
expr_makers[lax.dot_general_p] = _dot_general_lowering

def _concatenate_lowering(ctx, *xs, dimension):
  if dimension != 0:
    raise NotImplementedError("Concatenation along dim > 0 not implemented")
  in_avals = ctx.avals_in
  if any(a.shape[dimension] != in_avals[0].shape[dimension] for a in in_avals):
    raise NotImplementedError("Irregular concatenation not implemented")
  dim_size = in_avals[0].shape[dimension]
  i = ctx.fresh('i')
  xs_v = ctx.fresh('xs')
  return Block([
      Decl(xs_v, Table(tuple(xs)))
    ], App(App(Var('unsafeCastTable'), FinType(Literal(dim_size * len(xs)))),
            For((i,), (PairType(FinType(Literal(len(xs))), FinType(Literal(dim_size))),),
                App(App(Var(xs_v), App(Var('fst'), Var(i))), App(Var('snd'), Var(i))))))
expr_makers[lax.concatenate_p] = _concatenate_lowering
