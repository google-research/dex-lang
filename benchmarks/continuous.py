# Copyright 2022 Google LLC
#
# Use of this source code is governed by a BSD-style
# license that can be found in the LICENSE file or at
# https://developers.google.com/open-source/licenses/bsd

import re
import os
import sys
import time
import timeit
import subprocess
import tempfile
from functools import partial
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Union, Sequence

# Ensure NumPy can only use a single thread for an
# apples-to-apples comparison.
# But see package threadpoolctl: https://github.com/joblib/threadpoolctl
os.environ["OMP_NUM_THREADS"] = "1"
os.environ["MKL_NUM_THREADS"] = "1"
os.environ["OPENBLAS_NUM_THREADS"] = "1"
import numpy as np
import csv
import jax


BASELINE = '8dd1aa8539060a511d0f85779ae2c8019162f567'


def mk_env(xdg_home, variant):
  return { 'XDG_CACHE_HOME': Path(xdg_home) / variant,
           'LANG': 'en_US.UTF-8' }


@dataclass
class DexEndToEnd:
  """Measures end-to-end time and memory on a published example."""
  name: str
  repeats: int
  variant: str = 'latest'
  baseline_commit: str = BASELINE

  def clean(self, code, xdg_home):
    run(code / 'dex', 'clean', env=mk_env(xdg_home, self.variant))

  def bench(self, code, xdg_home):
    source = code / 'examples' / (self.name + '.dx')
    total_alloc, total_time = parse_result(
        read_stderr(code / 'dex', '--lib-path', code / 'lib',
                    'script', source, '+RTS', '-s',
                    env=mk_env(xdg_home, self.variant)))
    return [Result(self.name, 'alloc', total_alloc),
            Result(self.name, 'time', total_time)]

  def baseline(self):
    return DexEndToEnd(self.name, self.repeats, 'baseline')


@dataclass
class DexRuntime:
  """Measures isolated run time on a benchmark."""
  name: str
  repeats: int
  variant: str = 'latest'
  baseline_commit: str = BASELINE

  def clean(self, code, xdg_home):
    run(code / 'dex', 'clean', env=mk_env(xdg_home, self.variant))

  def bench(self, code, xdg_home):
    source = code / 'benchmarks' / (self.name + '.dx')
    runtime = parse_result_runtime(
        read(code / 'dex', '--lib-path', code / 'lib',
             'script', source, '+RTS', '-s',
             env=mk_env(xdg_home, self.variant)))
    return [Result(self.name, 'runtime', runtime)]

  def baseline(self):
    return Python(self.name, self.repeats, RUNTIME_BASELINES[self.name])


class DexRuntimeVsDex(DexRuntime):
  def baseline(self):
    return DexRuntimeVsDex(self.name, self.repeats, 'baseline')


@dataclass
class Python:
  name: str
  repeats: int
  f: Callable

  def clean(self, _code, _xdg_home):
    pass

  def bench(self, _code, _xdg_home):
    avg_time, iters = bench_python(self.f)
    return [Result(self.name, 'runtime', avg_time)]


@dataclass
class PythonSubprocess:
  name: str
  repeats: int
  variant: str = 'latest'
  baseline_commit: str = BASELINE  # Unused but demanded by the driver

  def clean(self, code, xdg_home):
    run(code / 'dex', 'clean', env=mk_env(xdg_home, self.variant))

  def bench(self, code, xdg_home):
    dex_py_path = code / 'python'
    source = code / 'benchmarks' / (self.name + '.py')
    env = { # Use the ambient Python so that virtualenv works
            'PATH': os.getenv('PATH'),
            # but look for the `dex` package in the installation directory first
            'PYTHONPATH': dex_py_path,
    }
    runtime = parse_result_runtime(read('python3', source, env=env))
    return [Result(self.name, 'runtime', runtime)]

  def baseline(self):
    return Python(self.name, self.repeats, RUNTIME_BASELINES[self.name])


def numpy_sum():
  n = 1000000
  xs = np.arange(n, dtype=np.float64)
  return np.sum(xs * xs)


def numpy_gaussian(n):
  return lambda: np.random.normal(size=n)


def numpy_matmul(n, width):
  m1 = np.random.normal(size=(width, n, n)).astype(np.float32)
  m2 = np.random.normal(size=(width, n, n)).astype(np.float32)
  return lambda: np.matmul(m1, m2)


def numpy_matvec(n, width):
  ms = np.random.normal(size=(width, n, n)).astype(np.float32)
  vs = np.random.normal(size=(width, n)).astype(np.float32)
  return lambda: np.einsum('...ij,...j', ms, vs)


def numpy_poly(n):
  xs = np.arange(n, dtype=np.float32)
  return lambda: np.polynomial.Polynomial([0.0, 1.0, 2.0, 3.0, 4.0])(xs)


def diag_conv_jax():
  # TODO Deduplicate these parameters vs the Dex implementation?
  shp = (100, 3, 32, 32)
  filter_size = 3
  lhs = jax.random.normal(jax.random.PRNGKey(1), shp, dtype=jax.numpy.float32)
  rhs = jax.lax.broadcast(jax.numpy.eye(filter_size), (100, 3))
  return lambda: jax.lax.conv_general_dilated(
      lhs, rhs, window_strides=(1, 1), padding='SAME',
      dimension_numbers=('NCHW', 'OIHW', 'NCHW'),
      feature_group_count=1)


BENCHMARKS = [
    DexEndToEnd('kernelregression', 10),
    DexEndToEnd('psd', 10),
    DexEndToEnd('fluidsim', 10),
    DexEndToEnd('regression', 10),
    DexEndToEnd('md', 10, baseline_commit='19b16662150ac8a11a9cbc2df67e9f58169ce4ee'),
    DexEndToEnd('bfgs', 10, baseline_commit='65dce60fe8a4a59e9ed563865b2b9eb9d81a540c'),
    DexRuntime('fused_sum', 5),
    DexRuntime('gaussian', 5),
    DexRuntime('jvp_matmul', 5),
    DexRuntime('matmul_big', 5),
    DexRuntime('matmul_small', 5),
    DexRuntime('matvec_big', 5),
    DexRuntime('matvec_small', 5),
    DexRuntime('poly', 5),
    DexRuntime('vjp_matmul', 5),
    DexRuntimeVsDex('conv', 10, baseline_commit='531832c0e18a64c1cab10fc16270b930eed5ed2b'),
    PythonSubprocess('conv_py', 5),
]
RUNTIME_BASELINES = {
    'fused_sum': numpy_sum,
    'gaussian': numpy_gaussian(1000000),
    'jvp_matmul': numpy_matmul(500, 1),  # TODO: rewrite the baseline in JAX and actually use jvp there
    'matmul_big': numpy_matmul(500, 1),
    'matmul_small': numpy_matmul(10, 1000),
    'matvec_big': numpy_matvec(10000, 1),
    'matvec_small': numpy_matvec(10, 10000),
    'poly': numpy_poly(100000),
    'vjp_matmul': numpy_matmul(500, 1),  # TODO: rewrite the baseline in JAX and actually use vjp there
    'conv_py': diag_conv_jax(),
}


def run(*args, capture=False, **kwargs):
  print('> ' + ' '.join(map(str, args)))
  result = subprocess.run(args, text=True, capture_output=capture, **kwargs)
  if result.returncode != 0 and capture:
    line = '-' * 20
    print(line, 'CAPTURED STDOUT', line)
    print(result.stdout)
    print(line, 'CAPTURED STDERR', line)
    print(result.stderr)
  result.check_returncode()
  return result


def read(*args, **kwargs):
  return run(*args, capture=True, **kwargs).stdout


def read_stderr(*args, **kwargs):
  return run(*args, capture=True, **kwargs).stderr


def build(commit):
  install_path = Path.cwd() / commit
  if install_path.exists():
    print(f'Skipping the build of {commit}')
  else:
    run('git', 'clone', '.', commit)
    run('git', 'checkout', commit, cwd=install_path)
    try:
      run('make', 'build-ffis-and-exe', cwd=install_path, env=dict(os.environ))
    except subprocess.CalledProcessError:
      # Presume that this commit doesn't have the `build-ffis-and-exe` target.
      # Then we presumably didn't need the FFI to run anything against it.
      run('make', 'install', cwd=install_path, env=dict(os.environ, PREFIX=install_path))
  return install_path


def benchmark(baselines, latest_path, benchmarks):
  with tempfile.TemporaryDirectory() as tmp:
    results = []
    for test in benchmarks:
      baseline = test.baseline()
      baseline_path = baselines[test.baseline_commit]
      # Warm up the caches
      baseline.clean(baseline_path, tmp)
      baseline.bench(baseline_path, tmp)
      test.clean(latest_path, tmp)
      test.bench(latest_path, tmp)
      for i in range(test.repeats):
        print(f'Iteration {i}')
        baseline_results = baseline.bench(baseline_path, tmp)
        test_results = test.bench(latest_path, tmp)
        for test_r, base_r in zip(test_results, baseline_results):
          print(base_r, '->', test_r)
          # Allocation measurements are stable enough so that we don't need to
          # take too many. But take two to get some estimate of the noise.
          if test_r.measure == 'alloc' and i >= 2:
            continue
          results.append(test_r.compare(base_r))
    return results


@dataclass
class Result:
  benchmark: str
  measure: str
  value: Union[int, float]

  def compare(self, other):
    if self.measure == 'alloc':
      return self
    if self.measure == 'time':
      return Result(self.benchmark, 'time_rel', self.value / other.value)
    if self.measure == 'runtime':
      return Result(self.benchmark, 'runtime_rel', self.value / other.value)
    raise NotImplementedError(f"Unrecognized metric type {self.measure}")


ALLOC_PATTERN = re.compile(r"^\s*([0-9,]+) bytes allocated in the heap", re.M)
TIME_PATTERN = re.compile(r"^\s*Total\s*time\s*([0-9.]+)s", re.M)
def parse_result(output):
  alloc_line = ALLOC_PATTERN.search(output)
  if alloc_line is None:
    raise RuntimeError("Couldn't extract total allocations")
  total_alloc = int(alloc_line.group(1).replace(',', ''))
  time_line = TIME_PATTERN.search(output)
  if time_line is None:
    raise RuntimeError("Couldn't extract total time")
  total_time = float(time_line.group(1))
  return total_alloc, total_time


RUNTIME_PATTERN = re.compile(r"^>\s*Run\s*time:\s*([0-9.]+)\s*([mun]?s)", re.M)
def parse_result_runtime(output):
  runtime_line = RUNTIME_PATTERN.search(output)
  if runtime_line is None:
    raise RuntimeError(f"Couldn't extract total runtime from\n{output}")
  raw_runtime = float(runtime_line.group(1))
  if runtime_line.group(2) == 's':
    return raw_runtime
  elif runtime_line.group(2) == 'ms':
    return raw_runtime / 1000.
  elif runtime_line.group(2) == 'us':
    return raw_runtime / 1000_000.
  elif runtime_line.group(2) == 'ns':
    return raw_runtime / 1000_000_000.


def bench_python(f, loops=None):
  """Return average runtime of `f` in seconds and number of iterations used."""
  if loops is None:
    f()
    s = time.perf_counter()
    f()
    e = time.perf_counter()
    duration = e - s
    loops = max(4, int(2 / duration)) # aim for 2s
  return (timeit.timeit(f, number=loops, globals=globals()) / loops, loops)


def save(commit, results: Sequence[Result], datapath, commitpath):
  with open(datapath, 'a', newline='') as datafile:
    writer = csv.writer(datafile, delimiter=',', quotechar='"', dialect='unix')
    for r in results:
      writer.writerow((commit, r.benchmark, r.measure, r.value))
  with open(commitpath, 'a', newline='') as commitfile:
    writer = csv.writer(commitfile, delimiter=',', quotechar='"', dialect='unix')
    date = read('git', 'show', '-s', '--format=%ct', commit, '--').strip()
    writer.writerow([commit, date])


def main(argv):
  if len(argv) < 3:
    raise ValueError("Expected at least three arguments!")
  datapath, commitpath, commit = argv[:3]
  benchmark_names = argv[3:]
  benchmarks = BENCHMARKS if not benchmark_names \
    else [b for b in BENCHMARKS if b.name in benchmark_names]
  baselines = {}
  for test in benchmarks:
    baseline_commit = test.baseline_commit
    if baseline_commit not in baselines:
      baseline_path = build(baseline_commit)
      baselines[baseline_commit] = baseline_path
  print(f'Building latest: {commit}')
  latest_path = build(commit)
  results = benchmark(baselines, latest_path, benchmarks)
  save(commit, results, datapath, commitpath)
  print('DONE!')


if __name__ == '__main__':
  main(sys.argv[1:])
