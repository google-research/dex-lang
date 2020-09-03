# Copyright 2020 Google LLC
#
# Use of this source code is governed by a BSD-style
# license that can be found in the LICENSE file or at
# https://developers.google.com/open-source/licenses/bsd

import ctypes
import pathlib
import atexit

__all__ = ['execute']

here = pathlib.Path(__file__).parent.absolute()

lib = ctypes.cdll.LoadLibrary(here / 'libDex.so')

_init = lib.dexInit
_init.restype = None
_init.argtypes = []

_fini = lib.dexFini
_fini.restype = None
_fini.argtypes = []

_eval = lib.dexEval
_eval.restype = None
_eval.argtypes = [ctypes.c_void_p, ctypes.c_char_p]

_create_context = lib.dexCreateContext
_create_context.restype = ctypes.c_void_p
_create_context.argtypes = []

_destroy_context = lib.dexDestroyContext
_destroy_context.restype = None
_destroy_context.argtypes = [ctypes.c_void_p]

_init()
atexit.register(lambda: _fini())

_default_ctx = _create_context()
atexit.register(lambda: _destroy_context(_default_ctx))

def execute(source):
  source = source + "\n"
  _eval(_default_ctx, ctypes.c_char_p(source.encode('ascii')))
