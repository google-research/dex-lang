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

def pprint(x):
  print(pp.PrettyPrinter().pprint(x))

def var_as_name(x):
  assert x[0]["tag"] == "Name"
  return tuple(x[0]["contents"])

def from_lit(x):
  assert x["tag"] == "JLit"
  return x["contents"]["contents"]

def as_int_lit(x):
  return { "tag": "JLit"
         , "contents": {"tag" : "IntLit", "contents" : int(x)}}

def as_float_lit(x):
  return { "tag": "JLit"
         , "contents": {"tag" : "RealLit", "contents" : float(x)}}

def subst_atom(env, x):
  atom_case = x["tag"]
  if atom_case == "JVar":
    result = env[var_as_name(x["contents"])]
    return result
  elif atom_case == "JLit":
    return x
  else:
    raise Exception("Unrecognized atom case: {}".format(atom_case))

def eval_bin_op(op_name, x, y):
  if   op_name == "IMul": return as_int_lit(x * y)
  elif op_name == "IAdd": return as_int_lit(x + y)
  elif op_name == "FMul": return as_float_lit(x * y)
  elif op_name == "FAdd": return as_float_lit(x + y)
  else: raise Exception("Unrecognized op: {}".format(op_name))

def eval_op(env, op_name, op_args):
  if op_name == "JScalarBinOp":
    binop_name, (x,_), (y,_) = op_args
    x_ = from_lit(subst_atom(env, x))
    y_ = from_lit(subst_atom(env, y))
    return eval_bin_op(binop_name["tag"], x_, y_)
  else:
    raise Exception("Unrecognized op: {}".format(op_name))

def eval_prog(prog):
  decls, results = prog
  env = {}
  for (v_raw, (_, _, op)) in decls:
    v = var_as_name(v_raw)
    ans = eval_op(env, op["tag"], op["contents"])
    env[var_as_name(v_raw)] = ans

  return [subst_atom(env, result) for result in results]

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
  run_server([eval_prog])
