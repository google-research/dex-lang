# Copyright 2019 Google LLC
#
# Use of this source code is governed by a BSD-style
# license that can be found in the LICENSE file or at
# https://developers.google.com/open-source/licenses/bsd

import itertools as it
from collections import namedtuple
import numpy as np

TabType = namedtuple('TabType', ['index_set', 'element_type'])

preheader_length = 81
preheader_start = "-- dex-object-file-v0.0.1 num-header-bytes "

def dump(obj, f):
  ty = get_dex_ty(obj)
  buffers = flatten_to_buffers(obj)
  ty_str    = "type: {}\n".format(pprint_ty(ty))
  sizes_str = "bufferSizes: [{}]\n".format(", ".join([str(get_buffer_size(x))
                                                      for x in buffers]))
  header_size = preheader_length + len(ty_str) + len(sizes_str)
  pre_header_str = make_preheader(header_size)
  header = pre_header_str + ty_str + sizes_str
  assert header_size == len(header)
  f.write(header)
  f.flush()
  for b in buffers:
    buf_bytes = b.tobytes()
    assert len(buf_bytes) == get_buffer_size(b), \
        "{}   {} != {}".format(b, len(buf_bytes), get_buffer_size(b))
    f.buffer.write(buf_bytes)
    f.flush()

def get_dex_ty(obj):
  if isinstance(obj, tuple):
    return tuple(get_dex_ty(x) for x in obj)
  elif isinstance(obj, np.ndarray):
    base_ty = dtype_to_dex_ty(obj.dtype)
    return make_tab_type(base_ty, obj.shape)
  elif isinstance(obj, float):
    return float
  elif isinstance(obj, bool):
    return bool
  elif isinstance(obj, int):
    return int
  else:
    raise Exception("No corresponding Dex type for {}".format(type(obj)))

def flatten_to_buffers(obj):
  if isinstance(obj, tuple):
    return tuple(it.chain(*(flatten_to_buffers(x) for x in obj)))
  elif isinstance(obj, np.ndarray):
    flat_array = obj.ravel()
    if obj.dtype == np.bool:
      return [np.asarray(flat_array, dtype=np.int64)]
    else:
      return [flat_array]
  elif isinstance(obj, float):
    return [np.array(obj, dtype=np.float64)]
  elif isinstance(obj, bool):
    return [np.array(obj, dtype=np.int64)]
  elif isinstance(obj, int):
    return [np.array(obj, dtype=np.int64)]
  else:
    raise Exception("No corresponding Dex type for {}".format(type(obj)))

def dtype_to_dex_ty(dtype):
  if dtype == np.float64:
    return float
  elif dtype == np.int64:
    return int
  elif dtype == np.bool:
    return bool
  else:
    raise Exception("Unrecognized dtype: " + str(dtype))

def make_tab_type(base_ty, shape):
  shape = tuple(shape)
  if shape == ():
    return base_ty
  else:
    (n, *rest) = shape
    return TabType(n, make_tab_type(base_ty, rest))

def get_buffer_size(array):
  return array.size * 8

def pprint_ty(ty):
  if isinstance(ty, TabType):
    return "{}=>{}".format(str(ty.index_set), pprint_ty(ty.element_type))
  elif isinstance(ty, tuple):
    return "({})".format(", ".join(map(pprint_ty, ty)))
  if ty is int:
    return "Int"
  elif ty is float:
    return "Real"
  elif ty is bool:
    return "Bool"
  else:
    raise Exception("Can't print type: {}".format(ty))

def make_preheader(n):
  preheader_prefix = preheader_start + str(n) + " "
  padding = '-' * (preheader_length - len(preheader_prefix) - 1) + "\n"
  return preheader_prefix + padding
