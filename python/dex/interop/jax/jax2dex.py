from dataclasses import dataclass
from collections import defaultdict
from functools import partial
import itertools as it
import textwrap
import typing
from typing import Any, NamedTuple, Dict, Optional, List, Callable, Sequence, Union
from string import ascii_lowercase
import numpy as np

import jax
from jax import core
from jax import linear_util as lu
from jax.core import ShapedArray
from jax.interpreters import partial_eval as pe
from jax.interpreters import mlir
from jax._src.tree_util import (tree_flatten, tree_unflatten, PyTreeDef,
                                broadcast_prefix)
from jax._src import dtypes
from jax._src.api_util import flatten_fun
from jax._src.traceback_util import api_boundary
from jax._src.util import (unzip2, wraps, split_list, partition_list, safe_map,
                           safe_zip, cache)

from . import apply
from ... import Atom, eval

map = safe_map
zip = safe_zip


### First define an IR AST via dataclasses, slightly higher-level than Dex Core.

@dataclass
class Type:
  pass

@dataclass
class Expr:
  pass

u32 = np.dtype('uint32')
i32 = np.dtype('int32')
f32 = np.dtype('float32')
f64 = np.dtype('float64')
_dtypes = {
  f32: 'Float32',
  f64: 'Float64',
  i32: 'Int32',
  u32: 'Word32',
  np.dtype('bool'): 'Bool',
}

_io_dtypes = {f32, f64, i32, u32}

@dataclass
class EType(Type):
  dtype: Any
  def pprint(self) -> str:
    ty_str = _dtypes.get(np.dtype(self.dtype), None)
    if ty_str is None:
      raise NotImplementedError(self.dtype)
    return ty_str

@dataclass
class FinTabType(Type):
  size: int  # TODO Expr
  ty: Type
  def pprint(self) -> str:
    return f'(Fin(%NatCon(%monoLit({self.size}))) => {self.ty.pprint()})'

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
    return f'({self.lhs.pprint()}, {self.rhs.pprint()})'

@dataclass
class Literal(Expr):
  val: Any
  dtype: np.dtype
  def pprint(self) -> str:
    if self.dtype == f32:
      return f'{self.val:f}' if self.val >= 0 else f'({self.val:f})'
    elif self.dtype == f64:
      val_str = f'{self.val:f}' if self.val >= 0 else f'({self.val:f})'
      return f'f_to_f64({val_str})'
    elif self.dtype == i32:
      val_str = f'(+{self.val})' if self.val >= 0 else f'({self.val})'
      return f'%monoLit({val_str})'
    elif self.dtype == u32:
      return f'%monoLit({self.val})'
    else:
      raise NotImplementedError(f"Unsupported literal dtype: {dtype}")

@dataclass
class Prim(Expr):
  name: str
  def pprint(self) -> str:
    return f'%{self.name}'

@dataclass
class Var(Expr):
  name: str
  def pprint(self) -> str:
    return self.name

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
class NaryApp(Expr):
  fun: Expr
  arguments: Sequence[Expr]
  def pprint(self) -> str:
    assert self.arguments
    arg_strs = ', '.join(map(lambda a: f'({a.pprint()})', self.arguments))
    if isinstance(self.fun, (Prim, Var)):
      fun_str = self.fun.pprint()
    else:
      fun_str = f'({self.fun.pprint()})'
    return f'{fun_str}({arg_strs})'

def App(fun, *args):
  return NaryApp(fun, args)

@dataclass
class TabApp(Expr):
  fun: Expr
  argument: Expr
  def pprint(self) -> str:
    return f'({self.fun.pprint()})[{self.argument.pprint()}]'

@dataclass
class Pattern:
  pass

@dataclass
class ConPattern(Pattern):
  con: str
  fields: typing.Tuple[Optional[str]]
  def pprint(self) -> str:
    fields_str = ', '.join(f if f is not None else '_' for f in self.fields)
    return f'{self.con}({fields_str})'

@dataclass
class Decl:
  name: Union[str, Pattern]
  expr: Expr
  def pprint(self) -> str:
    name_str = self.name if isinstance(self.name, str) else self.name.pprint()
    return f'{name_str} = {self.expr.pprint()}'

@dataclass
class Block:
  decls: List[Decl]
  expr: Expr

@dataclass
class Lam(Expr):
  names: List[str]
  tys: List[Type]
  block: Block
  def pprint(self) -> str:
    args_ann = [f'{name}:{ty.pprint()}' for (name, ty) in zip(self.names, self.tys)]
    decls = '\n'.join(d.pprint() for d in self.block.decls)
    expr = self.block.expr.pprint()
    newline = '\n' if decls else ''
    block = textwrap.indent(f'{decls}{newline}{expr}', '  ')
    return f'\\ {" ".join(args_ann)}.\n{block}\n'

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
    idx_strs = ', '.join(f'({i.pprint()})' for i in self.idxs)
    return f'({self.tab.pprint()})[{idx_strs}]'


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
  debug = pe.debug_info(fun, in_tree, None, False, "dex_jit")
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
  return dex_atom(jaxpr).compile()

@cache()
def dex_atom(jaxpr: core.Jaxpr) -> Atom:
  assert not jaxpr.constvars
  varnames = ('v' + ''.join(chars) for n in it.count(1)
              for chars in it.product(ascii_lowercase, repeat=n))

  env: Dict[core.Var, Var] = {}

  def read(x: core.Atom) -> Expr:
    if type(x) is core.Literal:
      return Literal(x.val, core.get_aval(x.val).dtype)
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
  fin_cache: Dict[int, Var] = {}
  for e in jaxpr.eqns:
    in_avals = [typ(x) for x in e.invars]
    out_avals = [v.aval for v in e.outvars]
    ctx = LoweringRuleContext(counter, fin_cache, in_avals, out_avals)
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
  for v in jaxpr.outvars:
    if v.aval.dtype not in _io_dtypes:
      raise NotImplementedError(f"dtype {v.aval.dtype} is not supported as dexjit output")
  fin_decls = [Decl(v.name, FinType(NatLiteral(n))) for n, v in fin_cache.items()]
  block = Block(fin_decls + decls, expr)
  args = []
  argtys = []
  for v in [*jaxpr.invars, *jaxpr.constvars]:
    if v.aval.dtype not in _io_dtypes:
      raise NotImplementedError(f"dtype {v.aval.dtype} is not supported as dexjit input")
    args.append(read(v).name)
    argtys.append(aval_to_type(v.aval))
  expr = Lam(args, argtys, block)
  return eval(expr.pprint())

def aval_to_type(aval: core.AbstractValue) -> Type:
  if type(aval) is core.ShapedArray:
    ty = EType(aval.dtype)
    shape = list(aval.shape)
    while shape:
      ty = FinTabType(shape.pop(), ty)
    return ty
  else:
    raise NotImplementedError(aval)

@dex_call_p.def_abstract_eval
def dex_call_abstract_eval(*args, jaxpr):
  return [v.aval for v in jaxpr.outvars]

def dex_call_lowering(b, *args, jaxpr):
  return apply.dex_apply_lowering(b, *args, func_atom=dex_atom(jaxpr))
mlir.register_lowering(dex_call_p, dex_call_lowering, platform='cpu')


### Dex translation rules for JAX primitives

ExprMaker = Callable  # [[Any, ...], Expr]
expr_makers: Dict[core.Primitive, ExprMaker] = {}

@dataclass
class LoweringRuleContext:
  _counter: Any
  _fin_cache: Dict[int, Var]
  avals_in: Sequence[core.AbstractValue]
  avals_out: Sequence[core.AbstractValue]

  def fresh(self, seed: str) -> str:
    return seed + str(next(self._counter))

  def Fin(self, n: int) -> Var:
    t = self._fin_cache.get(n, None)
    if t is None:
      t = self._fin_cache[n] = Var(self.fresh(f'f{n}_'))
    return t


from jax._src.lax import lax

def _neg(ctx, x):
  aval, = ctx.avals_in
  if not np.issubdtype(aval.dtype, np.floating):
    raise NotImplementedError(aval.dtype)
  if not aval.shape:
    return App(Prim('fmul'), Literal(-1, aval.dtype), x)
  idx_names = [ctx.fresh('i') for _ in aval.shape]
  idx_tys = [ctx.Fin(d) for d in aval.shape]
  return For(tuple(idx_names), tuple(idx_tys),
             App(Prim('fmul'), Literal(-1, aval.dtype), Idx(x, tuple(map(Var, idx_names)))))
expr_makers[lax.neg_p] = _neg
# TODO: Use primitives to speed-up compile times!
expr_makers[lax.sin_p] = lambda ctx, x: App(Var('sin'), x)
expr_makers[lax.cos_p] = lambda ctx, x: App(Var('cos'), x)
expr_makers[lax.log_p] = lambda ctx, x: App(Var('log'), x)
expr_makers[lax.exp_p] = lambda ctx, x: App(Var('exp'), x)

IX_REP_DTYPE = np.dtype('uint32')
def IxRepLiteral(n): return Literal(n, IX_REP_DTYPE)
def MkNat(n): return App(Prim('NatCon'), n)
def NatLiteral(n): return MkNat(Literal(n, IX_REP_DTYPE))

def _broadcast_in_dim(ctx, x, *dyn_shape, shape, broadcast_dimensions):
  idx_names = [ctx.fresh('i') for _ in range(len(shape))]
  dyn = iter(dyn_shape)
  tys = [FinType(MkNat(next(dyn)) if d is None else NatLiteral(d)) for d in shape]
  idxs = [Var(idx_names[i]) for i in broadcast_dimensions]
  x_indexed = Idx(x, tuple(idxs)) if idxs else x
  return For(tuple(idx_names), tuple(tys), x_indexed)
expr_makers[lax.broadcast_in_dim_p] = _broadcast_in_dim

def _broadcasting_binop(ibinop_expr: Expr, fbinop_expr: Expr, ctx, x, y):
  x_aval, y_aval = ctx.avals_in
  out_aval, = ctx.avals_out
  if np.issubdtype(x_aval.dtype, np.integer):
    binop_expr = ibinop_expr
  else:
    binop_expr = fbinop_expr
  if binop_expr is None:
    raise NotImplementedError()
  if not out_aval.shape:
    return App(binop_expr, x, y)
  idx_names, idx_tys = unzip2((ctx.fresh('i'), ctx.Fin(sz))
                              for sz in out_aval.shape)
  x_expr = _make_bcast_expr(ctx, idx_names, out_aval.shape, x_aval.shape, x)
  y_expr = _make_bcast_expr(ctx, idx_names, out_aval.shape, y_aval.shape, y)
  out = For(tuple(idx_names), tuple(idx_tys),
            App(binop_expr, x_expr, y_expr))
  return out

def _make_bcast_expr(ctx, idx_names, out_shape, in_shape, x):
  ndim = len(in_shape)
  if not ndim:
    return x
  idxs = [unitIdx(ctx) if in_size != out_size else Var(idx_name)
          for idx_name, out_size, in_size
          in zip(idx_names[-ndim:], out_shape[-ndim:], in_shape)]
  return Idx(x, tuple(idxs))
def unitIdx(ctx):
  return App(Var('unsafe_from_ordinal'), NatLiteral(0))

expr_makers[lax.add_p] = partial(_broadcasting_binop, Prim('iadd'), Prim('fadd'))
expr_makers[lax.sub_p] = partial(_broadcasting_binop, Prim('isub'), Prim('fsub'))
expr_makers[lax.mul_p] = partial(_broadcasting_binop, Prim('imul'), Prim('fmul'))
expr_makers[lax.div_p] = partial(_broadcasting_binop, Prim('idiv'), Prim('fdiv'))
expr_makers[lax.max_p] = partial(_broadcasting_binop, Var('max'), Var('max'))
expr_makers[lax.pow_p] = partial(_broadcasting_binop, None, Prim('fpow'))
expr_makers[lax.lt_p] = partial(_broadcasting_binop,  Var('(<)'), Var('(<)'))

def _integer_pow_lowering(ctx, x, y):
  if y == 2:
    return BinOp(x, '*', x)
  raise NotImplementedError()
expr_makers[lax.integer_pow_p] = _integer_pow_lowering

def _select_lowering(ctx, c, *args):
  if len(args) != 2:
    raise NotImplementedError()
  x, y = args
  out_aval, = ctx.avals_out
  if ctx.avals_in[0].shape:
    idx_names, idx_tys = unzip2((ctx.fresh('i'), ctx.Fin(sz))
                                for sz in out_aval.shape)
    idx_vars = tuple(Var(ix) for ix in idx_names)
    return For(tuple(idx_names), tuple(idx_tys),
               App(Var('select'), Idx(c, idx_vars), Idx(y, idx_vars), Idx(x, idx_vars)))
  else:
    return App(Var('select'), c, y, x)
expr_makers[lax.select_n_p] = _select_lowering

def _squeeze_lowering(ctx, x, dimensions):
  in_aval, = ctx.avals_in
  out_aval, = ctx.avals_out
  if not out_aval.shape:
    return Idx(x, (unitIdx(ctx),))
  idx_names, idx_tys = unzip2((ctx.fresh('i'), ctx.Fin(sz))
                              for sz in out_aval.shape)
  idx_name = iter(idx_names)
  idxs = [unitIdx(ctx) if dim in dimensions else Var(next(idx_name))
          for dim in range(in_aval.ndim)]
  return For(tuple(idx_names), tuple(idx_tys), Idx(x, tuple(idxs)))
expr_makers[lax.squeeze_p] = _squeeze_lowering

def _slice_lowering(ctx, x, start_indices, limit_indices, strides):
  if strides is not None and any(s != 1 for s in strides):
    raise NotImplementedError("Strided slices not implemented yet!")
  in_aval, = ctx.avals_in
  out_aval, = ctx.avals_out
  assert len(start_indices) == len(limit_indices) == in_aval.ndim == out_aval.ndim
  idx_names, idx_tys = unzip2((ctx.fresh('i'), ctx.Fin(sz))
                              for sz in out_aval.shape)
  input_ixs = [Var(ix) if in_size == out_size else
               App(Var('unsafe_from_ordinal'),
                   BinOp(NatLiteral(start), '+', App(Var('ordinal'), Var(ix))))
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
      dimension_numbers == (((1,), (0,)), ((), ())) and
      lhs_aval.dtype == f32):
    return BinOp(lhs, '**', rhs)
  # Matrix-vector multiply
  if (lhs_aval.ndim == 2 and rhs_aval.ndim == 1 and
      dimension_numbers == (((1,), (0,)), ((), ()))):
    n, k = lhs_aval.shape
    i, j = ctx.fresh('i'), ctx.fresh('j')
    return For((i,), (ctx.Fin(n),),
               App(Var('sum'),
                   For((j,), (ctx.Fin(k),),
                       BinOp(Idx(lhs, (Var(i), Var(j))), "*", Idx(rhs, (Var(j),))))))
  raise NotImplementedError("Unimplemented dot_general kind")
expr_makers[lax.dot_general_p] = _dot_general_lowering

def _concatenate_lowering(ctx, *xs, dimension):
  if dimension != 0:
    raise NotImplementedError("Concatenation along dim > 0 not implemented")
  in_avals = ctx.avals_in
  out_aval, = ctx.avals_out
  # Regular concatenation
  if all(a.shape[dimension] == in_avals[0].shape[dimension] for a in in_avals):
    dim_size = in_avals[0].shape[dimension]
    i = ctx.fresh('i')
    xs_v = ctx.fresh('xs')
    return Block([
        Decl(xs_v, Table(tuple(xs)))
      ], App(Var('the'), FinTabType(dim_size * len(xs), Var('_')),
             App(Var('unsafe_cast_table'),
                 For((i,), (PairType(ctx.Fin(len(xs)), ctx.Fin(dim_size)),),
                     TabApp(TabApp(Var(xs_v), App(Var('fst'), Var(i))), App(Var('snd'), Var(i)))))))
  # Irregular concatenation
  # TODO: Generate specialized code
  xs_v = ctx.fresh('xs')
  return Block([
        Decl(ConPattern('AsList', (None, xs_v)),
             App(Var('concat'), Table(tuple(App(Var('to_list'), x) for x in xs)))),
      ], App(Var('the'), FinTabType(out_aval.shape[0], Var('_')),
             App(Var('unsafe_cast_table'), Var(xs_v))))
expr_makers[lax.concatenate_p] = _concatenate_lowering
