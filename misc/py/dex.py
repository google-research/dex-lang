from __future__ import print_function
# Copyright 2019 Google LLC
#
# Use of this source code is governed by a BSD-style
# license that can be found in the LICENSE file or at
# https://developers.google.com/open-source/licenses/bsd

import ctypes
import json

libname = "./dex2jax.so"

lib = ctypes.cdll.LoadLibrary(libname)
lib.hs_init(0, 0)  # TODO should call lib.hs_exit() when done

def setup_f(fname):
  f = getattr(lib, fname)
  f.argtypes = [ctypes.c_char_p]
  f.restype = ctypes.c_char_p
  return lambda x: json.loads(f(json.dumps(x)))

loadSource, = map(setup_f, ["loadSource"])

class DexModule(object):
  def __init__(self, functions):
    for fname, definition in functions:
      self.__dict__[fname] = definition

def load(fname):
  with open(fname) as f:
    s = f.read()
  top_level_functions = loadSource(s)
  print(top_level_functions)
  return DexModule(top_level_functions)
