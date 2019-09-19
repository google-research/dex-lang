import ctypes
import json

libname = "./cod2jax.so"

lib = ctypes.cdll.LoadLibrary(libname)
lib.hs_init(0, 0)  # TODO should call lib.hs_exit() when done

def setup_f(fname):
  f = getattr(lib, fname)
  f.argtypes = [ctypes.c_char_p]
  f.restype = ctypes.c_char_p
  return lambda x: json.loads(f(json.dumps(x)))

loadSource, = map(setup_f, ["loadSource"])

class CoddleModule(object):
  def __init__(self, functions):
    for fname, definition in functions:
      self.__dict__[fname] = definition

def load(fname):
  with open(fname) as f:
    s = f.read()
  top_level_functions = loadSource(s)
  print top_level_functions
  return CoddleModule(top_level_functions)
