# Copyright 2020 Google LLC
#
# Use of this source code is governed by a BSD-style
# license that can be found in the LICENSE file or at
# https://developers.google.com/open-source/licenses/bsd

import os
import time
import sys
import timeit
import tempfile
import subprocess

# Ensure NumPy can only use a single thread for an apples-to-apples comparison
os.environ["OMP_NUM_THREADS"] = "1"
os.environ["MKL_NUM_THREADS"] = "1"
os.environ["OPENBLAS_NUM_THREADS"] = "1"

import numpy as np

def bench_python(f, loops=None):
  if loops is None:
    f()
    s = time.perf_counter()
    f()
    e = time.perf_counter()
    duration = e - s
    loops = max(4, int(2 / duration)) # aim for 2s
  return (timeit.timeit(f, number=loops, globals=globals()) / loops, loops)


def bench_dex(file_name, loops, **params):
  params = dict(params, loops=loops)
  with tempfile.NamedTemporaryFile() as f:
    f.write('\n'.join('{} = {}'.format(k, v) for k, v in params.items()).encode('ascii'))
    with open(os.path.join('benchmarks', file_name), 'rb') as src:
      f.write(src.read())
    f.flush()
    dex_result = subprocess.run(['stack', 'exec', 'dex', '--', 'script', '--result-only', f.name],
                                capture_output=True)
    dex_output = dex_result.stdout.decode('ascii')
    dex_lines = [l for l in dex_output.split('\n') if l]
    try:
      return [float(t) / loops for t in dex_lines]
    except:
      raise RuntimeError("Unexpected Dex output: " + repr(dex_output))


def show_time(time_s):
  if time_s < 1e-1:
    time_us = time_s * 1e6
    return "{:.3f}us".format(time_us)
  else:
    return "{:.3f}s".format(time_s)


def print_result(bench_name, py_time, dex_time, loops):
  print('{}:\tNumPy: {}, Dex: {} (based on {} loops)'.format(
    bench_name, show_time(py_time), show_time(dex_time), loops))
