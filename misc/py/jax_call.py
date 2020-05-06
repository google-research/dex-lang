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

scary_map = map

def map(f, *args):
  return list(scary_map(f, *args))

class JaxFunction(object):
  def __init__(self, binders, decls, results):
    for b in binders: assert isinstance(b, Var)
    for b, op in decls:
      assert isinstance(b, Var)
      assert isinstance(op, Operation)
    for r in results: assert isatom(r)
    self.binders = binders
    self.decls = decls
    self.results = results

  def ser(self):
    assert False

  @staticmethod
  def des(obj):
    binders_ser, (decls_ser, results_ser) = obj
    binders = map(Var.des, binders_ser)
    results = map(des_atom, results_ser)
    decls = [(Var.des(b), Operation.des(op)) for (b, op) in decls_ser]
    return JaxFunction(binders, decls, results)

class Var(object):
  def __init__(self, name, ty):
    namespace, root, i = name
    assert isinstance(namespace, str)
    assert isinstance(root, str)
    assert isinstance(i, int)
    assert isinstance(ty, Ty)
    self.name = (namespace, root, i)
    self.ty = ty

  def __eq__(self, other):
    assert isinstance(other, Var)
    return self.name == other.name

  def __hash__(self):
    return hash(self.name)

  def ser(self):
    return [{"tag":"Name", "contents": list(self.name)},
            self.ty.ser()]

  @staticmethod
  def des(obj):
    name, (shape, basetype) = obj
    assert name["tag"] == "Name"
    return Var(name["contents"], Ty(basetype, shape))

class Ty(object):
  def __init__(self, basetype, shape):
    for n in shape: assert isinstance(n, int)
    assert basetype in ["IntType", "BoolType", "RealType"]
    self.basetype = basetype
    self.shape = shape

  def ser(self):
    return [self.shape, self.basetype]

  @staticmethod
  def des(obj):
    assert False

class Operation(object):
  def __init__(self, for_idxs, sum_idxs, op_name, args):
    for i in for_idxs: assert isinstance(i, int)
    for i in sum_idxs: assert isinstance(i, int)
    assert isinstance(op_name, str)
    for arg, idxs in args:
      for i in idxs: assert isinstance(i, int)
      assert isatom(arg)
    self.for_idxs = for_idxs
    self.sum_idxs = sum_idxs
    self.op_name = op_name
    self.args = args

  def ser(self):
    assert False

  @staticmethod
  def des(obj):
    for_idxs, sum_idxs, op_and_args_ser = obj
    op_name, args = des_op_and_args(op_and_args_ser)
    return Operation(for_idxs, sum_idxs, op_name, args)
    assert False

def ser_array(arr):
  assert isinstance(arr, np.ndarray)
  if arr.dtype in [np.int32, np.int64]:
    return [atom_type(arr).ser(), ser_flat_vec(arr.ravel())]
  else:
    assert False

def ser_flat_vec(vec):
  if vec.dtype in [np.int32, np.int64]:
    return {"tag":"IntVec", "contents": map(int, vec)}
  else:
    assert False

def atom_as_array(x):
  assert isatom(x)
  if isinstance(x, np.ndarray):
    return x
  elif isinstance(x, Var):
    assert False
  else:
    return np.array(x)

def des_atom(obj):
  if obj["tag"] == "JVar":
    return Var.des(obj["contents"])
  elif obj["tag"] == "JLit":
    val = obj["contents"]
    if val["tag"] == "IntLit":
      return np.array(val["contents"], dtype=np.int64)
    else:
      assert False
  else:
    assert False

def des_op_and_args(obj):
  if obj["tag"] == "JScalarBinOp":
    binop_name, x_ser, y_ser = obj["contents"]
    x = des_indexed_atom(x_ser)
    y = des_indexed_atom(y_ser)
    return binop_name["tag"], [x, y]
  else:
    assert False

def des_indexed_atom(atom_idxs):
  atom_ser, idxs_ser = atom_idxs
  return (des_atom(atom_ser), map(Var.des, idxs_ser))

global_env = {}

def eval_op(env, op_name, op_args):
  if op_name == "IAdd":
    (x,_), (y,_) = op_args
    return x + y
  else:
    raise Exception("Unrecognized op: {}".format(op_name))

arrayish_types = (np.ndarray, np.int64, np.float64)

def isatom(val):
  return (isinstance(val, Var)
       or isinstance(val, arrayish_types))

def subst_atom(env, x):
  assert isatom(x)
  if isinstance(x, Var):
    return env[x]
  else:
    return x

def atom_type(x):
  assert isatom(x)
  if isinstance(x, Var):
    return x.ty
  elif isinstance(x, arrayish_types):
    return Ty(dtype_basetype(x.dtype), x.shape)
  else:
    assert False

def dtype_basetype(x):
  if x in [np.int32, np.int64]:
    return "IntType"
  else:
    assert False

def atom_as_var(x):
  assert isatom(x)
  i = len(global_env)
  name = ("ArrayName", "arr", i)
  v = Var(name, atom_type(x))
  assert v not in global_env
  global_env[v] = x
  return v

def eval_function_application(top_arg):
  f = JaxFunction.des(top_arg[0])
  env = global_env.copy()
  f_args = [subst_atom(env, Var.des(x)) for x in top_arg[1]]
  for v, arg in zip(f.binders, f_args):
    env[v] = arg
  for (v, op) in f.decls:
    op_args = [(subst_atom(env, x), idxs) for (x, idxs) in op.args]
    env[v] = eval_op(env, op.op_name, op_args)
  return [atom_as_var(subst_atom(env, r)).ser() for r in f.results]

def retrieve_arrays(arrs):
  vs = map(Var.des, arrs)
  return [ser_array(atom_as_array(global_env[v])) for v in vs]

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
