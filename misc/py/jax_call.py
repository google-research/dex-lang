# Copyright 2019 Google LLC
#
# Use of this source code is governed by a BSD-style
# license that can be found in the LICENSE file or at
# https://developers.google.com/open-source/licenses/bsd

import json
import pprint
import sys
import pprint as pp
import traceback
import numpy as np
from jax import random

scary_map = map

def map(f, *args):
  return list(scary_map(f, *args))

class JaxFunction(object):
  def __init__(self, binders, decls, results):
    for b in binders: assert isinstance(b, Var)
    for b, op in decls:
      assert isinstance(b, Var)
      assert isinstance(op, Operation)
    for r in results: assert isinstance(r, Atom)
    self.binders = binders
    self.decls = decls
    self.results = results

  def ser(self):
    assert False

  @staticmethod
  def des(obj):
    binders_ser, (decls_ser, results_ser) = obj
    binders = map(Var.des, binders_ser)
    results = map(Atom.des, results_ser)
    decls = [(Var.des(b), Operation.des(op)) for (b, op) in decls_ser]
    return JaxFunction(binders, decls, results)

class Name(object):
  def __init__(self, namespace, root, i):
    assert isinstance(i, int)
    assert isinstance(namespace, str)
    assert isinstance(root, str)
    self._name = (namespace, root, i)

  @staticmethod
  def des(obj):
    namespace, root, i = obj
    return Name(namespace, root, i)

  def ser(self):
    return {"tag":"Name", "contents": list(self._name)}

  def __repr__(self): return str(self)
  def __str__(self):
    (_, root, i) = self._name
    if i == 0:
      return root
    else:
      return root + str(i)

  def __eq__(self, other):
    assert isinstance(other, Name)
    return self._name == other._name

  def __hash__(self):
    return hash(self._name)

class IdxVar(object):
  def __init__(self, name, size):
    assert isinstance(name, Name)
    assert isinstance(size, int)
    self.name = name
    self.size = size

  def __repr__(self): return str(self)
  def __str__(self):
    return str(self.name) + ":" + str(self.size)

  def __eq__(self, other):
    assert isinstance(other, IdxVar)
    return self.name == other.name

  def __hash__(self):
    return hash(self.name)

  @staticmethod
  def des(obj):
    name, idxSize = obj
    assert name["tag"] == "Name"
    return IdxVar(Name.des(name["contents"]), idxSize)

class Var(object):
  def __init__(self, name, ty):
    assert isinstance(ty, Ty)
    assert isinstance(name, Name)
    self.name = name
    self.ty = ty

  def __repr__(self): return str(self)
  def __str__(self):
    return str(self.name) + ":" + str(self.ty)

  def __eq__(self, other):
    assert isinstance(other, Var)
    return self.name == other.name

  def __hash__(self):
    return hash(self.name)

  def ser(self):
    return [self.name.ser(), self.ty.ser()]

  @staticmethod
  def des(obj):
    name, (shape, basetype) = obj
    assert name["tag"] == "Name"
    return Var(Name.des(name["contents"]), Ty(shape, basetype))

class Atom(object):
  def __init__(self, case, data):
    self.case = case
    if case == "Var":
      assert isinstance(data, Var)
      self.var = data
    elif case == "Lit":
      assert isinstance(data, arrayish_types), type(data)
      self.val = data
    else:
      assert False

  def __repr__(self): return str(self)
  def __str__(self):
   if self.case == "Var":
     return str(self.var)
   elif self.case == "Lit":
     return str(self.val)
   else:
     assert False

  @property
  def ty(self):
    if self.case == "Var":
      return self.var.ty
    elif self.case == "Lit":
      x = self.val
      return array_ty(x)
    else:
      assert False

  @staticmethod
  def des(obj):
    if obj["tag"] == "JVar":
      val = obj["contents"]
      return Atom("Var", Var.des(val))
    elif obj["tag"] == "JLit":
      (shape, b), vec = obj["contents"]
      val = np.array(vec["contents"], dtype=basetype_dtype(b)).reshape(shape)
      return Atom("Lit", val)

class IndexedAtom(object):
  def __init__(self, atom, idxs):
    assert isinstance(atom, Atom)
    for i in idxs: assert isinstance(i, IdxVar)
    self.atom = atom
    self.idxs = idxs

  @property
  def ty(self):
    atom_ty = self.atom.ty
    return Ty(atom_ty.shape[:len(self.idxs)], atom_ty.basetype)

  @staticmethod
  def des(obj):
    atom, idxs = obj
    return IndexedAtom(Atom.des(atom), map(IdxVar.des, idxs))

  def __repr__(self): return str(self)
  def __str__(self):
    return str(self.atom) + "".join("." + str(i) for i in self.idxs)

class Ty(object):
  def __init__(self, shape, basetype):
    for n in shape: assert isinstance(n, int)
    assert basetype in ["IntType", "BoolType", "RealType"]
    self.basetype = basetype
    self.shape = tuple(shape)

  def ser(self):
    return [self.shape, self.basetype]

  def __eq__(self, other):
    assert isinstance(other, Ty)
    return self.basetype == other.basetype and self.shape == other.shape

  @staticmethod
  def des(obj):
    assert False

  def __repr__(self): return str(self)
  def __str__(self):
    return self.basetype + str(self.shape)

class Operation(object):
  def __init__(self, for_idxs, sum_idxs, op_name, size_args, args):
    for i in for_idxs: assert isinstance(i, IdxVar)
    for i in sum_idxs: assert isinstance(i, IdxVar)
    assert isinstance(op_name, str)
    for size in size_args: assert isinstance(size, int)
    for arg in args: assert isinstance(arg, IndexedAtom)
    self.for_idxs = for_idxs
    self.sum_idxs = sum_idxs
    self.op_name = op_name
    self.size_args = size_args
    self.args = args

  @property
  def all_idxs(self):
    return self.for_idxs + self.sum_idxs

  def ser(self):
    assert False

  @staticmethod
  def des(obj):
    for_idxs_ser, sum_idxs_ser, op_and_args_ser = obj
    for_idxs = map(IdxVar.des, for_idxs_ser)
    sum_idxs = map(IdxVar.des, sum_idxs_ser)
    op_name, size_args, args = des_op_and_args(op_and_args_ser)
    return Operation(for_idxs, sum_idxs, op_name, size_args, args)
    assert False

  def __repr__(self): return str(self)
  def __str__(self):
    return "for {} . sum {} . {} {}".format(
      self.for_idxs, self.sum_idxs, self.op_name, tuple(self.args))

def array_ty(x):
  return Ty(x.shape, dtype_basetype(x.dtype))

def ser_array(arr):
  assert isinstance(arr, arrayish_types)
  return [array_ty(arr).ser(), ser_flat_vec(arr.ravel())]

def ser_flat_vec(vec):
  if vec.dtype in [np.int32, np.int64]:
    return {"tag":"IntVec", "contents": map(int, vec)}
  if vec.dtype in [np.float32, np.float64]:
    return {"tag":"DoubleVec", "contents": map(float, vec)}
  else:
    assert False

def des_op_and_args(obj):
  tag = obj["tag"]
  if tag == "JScalarBinOp":
    binop_name, x_ser, y_ser = obj["contents"]
    x = IndexedAtom.des(x_ser)
    y = IndexedAtom.des(y_ser)
    return binop_name["tag"], [], [x, y]
  if tag == "JScalarUnOp":
    unop_name, x_ser = obj["contents"]
    x = IndexedAtom.des(x_ser)
    return unop_name, [], [x]
  elif tag == "JIota":
    size = obj["contents"]
    assert isinstance(size, int)
    return "Iota", [size], []
  elif tag == "JId":
    x_ser = obj["contents"]
    x = IndexedAtom.des(x_ser)
    return "Id", [], [x]
  elif tag == "JGet":
    x_ser, y_ser = obj["contents"]
    x = IndexedAtom.des(x_ser)
    y = IndexedAtom.des(y_ser)
    return "Get", [], [x, y]
  elif tag == "JThreeFry2x32":
    x_ser, y_ser = obj["contents"]
    x = IndexedAtom.des(x_ser)
    y = IndexedAtom.des(y_ser)
    return "ThreeFry2x32", [], [x, y]
  else:
    raise Exception("Not implemented: " + str(tag))

global_env = {}

def eval_op(op):
  broadcast_ans = eval_for(op)
  axes = tuple(range(len(op.for_idxs), len(op.all_idxs)))
  summed_ans = np.sum(broadcast_ans, axis=axes)
  return Atom("Lit", summed_ans)

def eval_for(op):
  if op.op_name in ("IAdd", "IMul", "FAdd", "FMul"):
    x, y = op.args
    x_bc = broadcast_dims(op.all_idxs, x.idxs, x.atom.val)
    y_bc = broadcast_dims(op.all_idxs, y.idxs, y.atom.val)
    if op.op_name in ("IAdd", "FAdd"):
      return x_bc + y_bc
    elif op.op_name in ("IMul", "FMul"):
      return x_bc * y_bc
    else:
      raise Exception("Not implemented: " + str(op.op_name))
  elif op.op_name == "Iota":
    n, = op.size_args
    val = np.arange(n)
    val_bc = broadcast_dims(op.all_idxs, [], val)
    return val_bc
  elif op.op_name == "Id":
    x, = op.args
    x_bc = broadcast_dims(op.all_idxs, x.idxs, x.atom.val)
    return x_bc
  elif op.op_name == "Get":
    x, idx = op.args
    out_shape = [i.size for i in op.all_idxs]
    x_idxs_used = get_stack_idxs_used(op.all_idxs, x.idxs)
    leading_idx_arrays = []
    for i, idx_used in enumerate(x_idxs_used):
      if idx_used:
        leading_idx_arrays.append(nth_iota(out_shape, i))
      else:
        pass
    payload_idx_array = broadcast_dims(op.all_idxs, idx.idxs, idx.atom.val)
    out = x.atom.val[tuple(leading_idx_arrays) + (payload_idx_array,)]
    return out
  elif op.op_name == "IntToReal":
    x, = op.args
    real_val = np.array(x.atom.val, dtype="float32")
    x_bc = broadcast_dims(op.all_idxs, x.idxs, real_val)
    return x_bc
  elif op.op_name in ("FNeg", "INeg"):
    x, = op.args
    x_bc = broadcast_dims(op.all_idxs, x.idxs, -x.atom.val)
    return x_bc
  elif op.op_name == "ThreeFry2x32":
    convert_64_to_32s = lambda x: np.array([x]).view(np.uint32)
    convert_32s_to_64 = lambda x: np.int64(np.array(x).view(np.int64).item())
    x, y = op.args
    key, count = convert_64_to_32s(x.atom.val), convert_64_to_32s(y.atom.val)
    result = convert_32s_to_64(random.threefry_2x32(key, count))
    x_bc = broadcast_dims(op.all_idxs, x.idxs, result)
    return x_bc
  else:
    raise Exception("Unrecognized op: {}".format(op.op_name))

def broadcast_dims(for_idxs, idxs, x):
  idxs_used = get_stack_idxs_used(for_idxs, idxs)
  return broadcast_with(x, [i.size for i in for_idxs], idxs_used)

def broadcast_with(x, final_shape, idxs_used):
  rem_shape = list(x.shape[sum(idxs_used):])
  reshape_shape = [size if use else 1 for (size, use) in zip(final_shape, idxs_used)]
  x_singletons = np.reshape(x, reshape_shape + rem_shape)
  return np.broadcast_to(x_singletons, final_shape + rem_shape)

def nth_iota(shape, i):
  size = shape[i]
  iota = np.arange(size)
  idxs_used = [Discard for _ in shape]
  idxs_used[i] = Use
  return broadcast_with(iota, shape, idxs_used)

Use = True
Discard = False
def get_stack_idxs_used(for_idxs, idxs):
  stack_vars = []
  cur_idxs = list(idxs)
  for i in for_idxs:
    if cur_idxs and i == cur_idxs[0]:
      stack_vars.append(Use)
      cur_idxs = cur_idxs[1:]
    else:
      stack_vars.append(Discard)
  return stack_vars

arrayish_types = (np.ndarray, np.int64, np.float64)

def subst_op(env, op):
  args = [IndexedAtom(subst_atom(env, x.atom), x.idxs) for x in op.args]
  return Operation(op.for_idxs, op.sum_idxs, op.op_name, op.size_args, args)

def subst_atom(env, x):
  assert isinstance(x, Atom)
  if x.case == "Var":
    return env[x.var]
  elif x.case == "Lit":
    return x
  else:
    assert False

def dtype_basetype(x):
  if x in [np.int32, np.int64]:
    return "IntType"
  elif x in [np.float32, np.float64]:
    return "RealType"
  else:
    assert False, x

def basetype_dtype(x):
  if x == "IntType":
    return np.int64
  if x == "RealType":
    return np.float64
  else:
    assert False

def atom_as_var(x):
  assert isinstance(x, Atom)
  i = len(global_env)
  name = Name("ArrayName", "arr", i)
  v = Var(name, x.ty)
  assert v not in global_env
  global_env[v] = x
  return v

def eval_function_application(top_arg):
  f = JaxFunction.des(top_arg[0])
  args = [Atom("Var", Var.des(x)) for x in top_arg[1]]
  env = global_env.copy()
  args_subst = [subst_atom(env, arg) for arg in args]
  for v, arg in zip(f.binders, args_subst):
    env[v] = arg
  for (v, op) in f.decls:
    ans =  eval_op(subst_op(env, op))
    if not (v.ty == ans.ty):
      print(op)
      raise Exception("Unexpected type. Expected {}, got {}".format(v.ty, ans.ty))
    env[v] = ans
  return [atom_as_var(subst_atom(env, r)).ser() for r in f.results]

def check_type(ty, val):
  assert isinstance(ty, Ty)

def retrieve_arrays(arrs):
  vs = map(Var.des, arrs)
  return [ser_array(global_env[v].val) for v in vs]

def just_print_it(obj):
  print(obj)
  return ()

def run_server(functions):
  readChan, writeChan = sys.argv[1:]
  with open(writeChan, "w") as w:
    for line in open(readChan):
      (f_idx, arg) = json.loads(line)
      try:
        f = functions[f_idx]
        ans = {"Right" : f(arg)}
      except Exception as e:
        traceback.print_exc()
        ans = {"Left": str(e)}
      w.write(json.dumps(ans) + "\n")
      w.flush()

if __name__ == "__main__":
  run_server([eval_function_application,
              retrieve_arrays,
              just_print_it])
