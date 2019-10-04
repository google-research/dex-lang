# Copyright 2019 Google LLC
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

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
  print top_level_functions
  return DexModule(top_level_functions)
