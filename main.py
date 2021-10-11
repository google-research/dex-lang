import numpy as np
from functools import partial
import dataclasses
from dataclasses import dataclass
from typing import NamedTuple, Union, Any, Callable, Optional

import jax
import jax.numpy as jnp
from jax import lax
from jax.tree_util import tree_flatten

from jax.interpreters import partial_eval as pe
from jax import linear_util as lu
from jax._src.api_util import flatten_fun_nokwargs
from jax import core

# -------------------- JAX embedding --------------------

# ---------- Trees ----------

Tree = Union['Node', 'Leaf']  # unlabeled leaves, labeled inner nodes
@dataclass(frozen=True)
class Node:
  value : Any
  left : Tree
  right : Tree
@dataclass(frozen=True)
class Leaf:
  pass
LEAF = Leaf()


@dataclass(frozen=True)
class AbstractTree:
  nleaves: int
  leaf_aval: Optional[Any]

  def update(self, **kwargs):
    return AbstractTree(**dict(dataclasses.asdict(self), **kwargs))

  def str_short(self, short_dtypes=False):
    return f'Tree[{self.nleaves}, {self.leaf_aval.str_short(short_dtypes)}]'

def _node_aval(n : Node):
  la = core.concrete_aval(n.left)
  ra = core.concrete_aval(n.right)
  vaval = core.raise_to_shaped(core.get_aval(n.value))
  leaf_aval = (vaval
               .join(la.leaf_aval if la.leaf_aval is not None else vaval)
               .join(ra.leaf_aval if ra.leaf_aval is not None else vaval))
  return AbstractTree(la.nleaves + ra.nleaves, leaf_aval)
core.pytype_aval_mappings[Node] = _node_aval
core.pytype_aval_mappings[Leaf] = lambda l: AbstractTree(1, None)
core.raise_to_shaped_mappings[AbstractTree] = \
    lambda at, wt: AbstractTree(at.nleaves, core.raise_to_shaped(at.leaf_aval, wt))

# ---------- Upsweep primitive ----------

upsweep_p = jax.core.Primitive('upsweep')
upsweep_p.multiple_results = True
@upsweep_p.def_impl
def _upsweep(arr, aux_in, *, f):
  def go(t: Tree, arr):
    if isinstance(t, Leaf):
      return arr[0], arr[1:], LEAF
    else:
      la, arr2, laux = go(t.left, arr)
      ra, arr3, raux = go(t.right, arr2)
      a, aux = core.jaxpr_as_fun(f)(la, ra, t.value)
      return a, arr3, Node(value=aux, left=laux, right=raux)
  a, rem, aux_out = go(aux_in, arr)
  assert rem.size == 0
  return a, aux_out

def _upsweep_abstract_eval(arr, aux_in, *, f):
  # TODO: Type check results against input avals
  return arr, aux_in.update(leaf_aval=f.out_avals[1])
upsweep_p.def_abstract_eval(_upsweep_abstract_eval)

# ---------- Downsweep primitive ----------

downsweep_p = jax.core.Primitive('downsweep')
downsweep_p.multiple_results = True
@downsweep_p.def_impl
def _downsweep(top, aux_in, *, f):
  def go(t: Tree, a):
    if isinstance(t, Leaf):
      return jnp.array([a]), Leaf
    else:
      la, ra, aux = core.jaxpr_as_fun(f)(a, t.value)
      larr, lt = go(t.left, la)
      rarr, rt = go(t.right, ra)
      return jnp.concatenate([larr, rarr]), Node(value=aux, left=lt, right=rt)
  return go(aux_in, top)

def _downsweep_abstract_eval(a, aux_in, *, f):
  # TODO: Type check results against input avals
  return a.update(shape=(aux_in.nleaves, *a.shape)), aux_in.update(leaf_aval=f.out_avals[2])
downsweep_p.def_abstract_eval(_downsweep_abstract_eval)

# TODO: JVP and transpose rules!

# -------------------- language primitives --------------------

def empty_seq_tree(n):
  assert n >= 1
  if n == 1:
    return LEAF
  else:
    return Node(value=core.unit, left=empty_seq_tree(n - 1), right=LEAF)

def empty_bal_tree(n):
  if n == 1:
    return LEAF
  mid, extra = divmod(n, 2)
  return Node(value=core.unit, left=empty_bal_tree(mid), right=empty_bal_tree(mid + extra))

# upsweep   : ((Pair a, auxI) -> (a     , auxO)) -> n=>a -> Tree n auxI -> (   a, Tree n auxO)
_, UPSWEEP_ARG_TREE = tree_flatten(((0, 0), 0))
def upsweep(f, arr, auxtree):
  a_aval = core.raise_to_shaped(core.get_aval(arr)).update(shape=arr.shape[1:])
  tree_aval = core.raise_to_shaped(core.get_aval(auxtree))
  jaxpr, out_avals, consts = pe.trace_to_jaxpr_dynamic(
    flatten_fun_nokwargs(lu.wrap_init(f), UPSWEEP_ARG_TREE)[0],
    [a_aval, a_aval, tree_aval.leaf_aval])
  if consts: raise NotImplementedError
  return upsweep_p.bind(arr, auxtree, f=core.ClosedJaxpr(jaxpr, ()))

# downsweep : ((a     , auxI) -> (Pair a, auxO)) ->    a -> Tree n auxI -> (n=>a, Tree n auxO)
_, DOWNSWEEP_ARG_TREE = tree_flatten((0, 0))
def downsweep(f, top, auxtree):
  a_aval = core.raise_to_shaped(core.get_aval(top))
  tree_aval = core.raise_to_shaped(core.get_aval(auxtree))
  jaxpr, out_avals, consts = pe.trace_to_jaxpr_dynamic(
      flatten_fun_nokwargs(lu.wrap_init(f), DOWNSWEEP_ARG_TREE)[0],
      (a_aval, tree_aval.leaf_aval))
  if consts: raise NotImplementedError
  return downsweep_p.bind(top, auxtree, f=core.ClosedJaxpr(jaxpr, ()))

# -------------------- scan --------------------

class Monoid(NamedTuple):
  mempty : Any
  mcomb : Callable[[Any, Any], Any]

def scan(monoid, arr, _mktree=empty_seq_tree):
  def up(a, aux):
    return monoid.mcomb(*a), a[0]
  tree = _mktree(arr.shape[0])
  _, uptree = upsweep(up, arr, tree)
  def down(a, aux):
    return (a, monoid.mcomb(a, aux)), core.unit
  ans, _ = downsweep(down, monoid.mempty, uptree)
  return ans

# -------------------- tests --------------------

def splat(f):
  return lambda xs: f(*xs)

def check(monoid, arr, mktree):
  np.testing.assert_allclose(
      # upsweep/downsweep scan is exclusive, so we do a map
      lax.map(splat(monoid.mcomb), (scan(monoid, arr, _mktree=mktree), arr)),
      lax.associative_scan(monoid.mcomb, arr),
  atol=1e-6, rtol=1e-6)  # f32 lol


def test_scan_add():
  arr = jnp.arange(1., 6.)
  plus = Monoid(jnp.float32(0.0), lambda x, y: x + y)
  check(plus, arr, empty_seq_tree)
  check(plus, arr, empty_bal_tree)

def test_scan_mul():
  arr = jnp.arange(1., 6.)
  times = Monoid(jnp.float32(1.0), lambda x, y: x * y)
  check(times, arr, empty_seq_tree)
  check(times, arr, empty_bal_tree)

def test_scan_matmul():
  M = lambda n: Monoid(jnp.eye(n), jnp.matmul)
  arr = np.random.RandomState(0).randn(4, 2, 2)
  check(M(2), arr, empty_bal_tree)

def test_scan_jaxpr():
  arr = jnp.arange(1., 6.)
  plus = Monoid(jnp.float32(0.0), lambda x, y: x + y)
  print(jax.make_jaxpr(partial(scan, plus))(arr))
