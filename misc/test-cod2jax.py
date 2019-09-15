from ctypes import *
import json

def setup_hs(libname, fnames):
  lib = cdll.LoadLibrary(libname)
  lib.hs_init(0, 0)  # TODO should call lib.hs_exit() when done
  fs = []
  def setup_f(fname):
    f = getattr(lib, fname)
    f.argtypes = [c_char_p]
    f.restype = c_char_p
    return lambda x: json.loads(f(json.dumps(x)))

  return map(setup_f, fnames)

loadSource, = setup_hs("./cod2jax.so", ["loadSource"])

print loadSource("f = sin")
