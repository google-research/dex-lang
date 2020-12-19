# Copyright 2020 Google LLC
#
# Use of this source code is governed by a BSD-style
# license that can be found in the LICENSE file or at
# https://developers.google.com/open-source/licenses/bsd

import json
from functools import partial
import time

import jax.numpy as np
import jax.random as random
from jax import jit
from jax.config import config

config.enable_omnistaging()

# warm up
np.dot(1.0, 1.0)

def benchit(bench_name, x, f):
  f_jitted = jit(f)
  t0 = time.time()
  f_jitted(x).block_until_ready()
  t1 = time.time()
  f_jitted(x).block_until_ready()
  t2 = time.time()
  run_time = t2 - t1
  compile_time = t1 - t0 - run_time
  print(json.dumps(
    {"bench_name"   : bench_name,
     "compile_time" : compile_time,
     "run_time"     : run_time}))

@partial(benchit, "sum", 0)
def sum_bench(key):
  xs = random.normal(random.PRNGKey(key), shape=(10000,))
  return np.sum(xs[:, None] + xs[None, :], axis=0)

@partial(benchit, "gaussian", 0)
def gaussian_bench(key):
  return random.normal(random.PRNGKey(key), shape=(100000000,))

@partial(benchit, "matmul", 0)
def matmul_bench(key):
  mat = random.normal(random.PRNGKey(key), shape=(1000, 1000))
  return np.dot(mat, mat)
