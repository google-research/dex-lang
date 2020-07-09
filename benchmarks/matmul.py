# Copyright 2019 Google LLC
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

n, k, m = map(int, sys.argv[1:])
x = np.random.randn(n, k).astype(np.float64)
y = np.random.randn(k, m).astype(np.float64)

x.dot(y) # Warmup
s = time.perf_counter()
x.dot(y)
e = time.perf_counter()
duration = e - s

loops = max(4, int(2 / duration)) # aim for 2s
numpy_time = timeit.timeit('x.dot(y)', number=loops, globals=globals()) / loops

def show_time(time_s):
  if time_s < 1e-1:
    time_us = time_s * 1e6
    return "{:.3f}us".format(time_us)
  else:
    return "{:.3f}s".format(time_s)


with tempfile.NamedTemporaryFile() as f:
  f.write("""
n = {}
k = {}
m = {}
loops = {}
  """.format(n, k, m, loops).encode('ascii'))
  with open('benchmarks/matmul.dx', 'rb') as src:
    f.write(src.read())
  f.flush()
  dex_result = subprocess.run(['stack', 'exec', 'dex', '--', 'script', '--result-only', f.name],
                              capture_output=True)
  dex_output = dex_result.stdout.decode('ascii')
  try:
    dex_time = float(dex_output) / loops
  except:
    print(dex_output)
    sys.exit(1)

print('NumPy: {}, Dex: {} (based on {} loops)'.format(
  show_time(numpy_time), show_time(dex_time), loops))
