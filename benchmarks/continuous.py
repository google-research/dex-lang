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
import csv
import subprocess
import tempfile
from functools import partial
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Union, Sequence

import numpy as np


@dataclass
class DexEndToEnd:
  """Measures end-to-end time and memory on a published example."""
  example: str
  repeats: int
  variant: str = 'latest'

  def clean(self, code, xdg_home):
    run(code / 'dex', 'clean', env={'XDG_CACHE_HOME': Path(xdg_home) / self.variant})

  def bench(self, code, xdg_home):
    source = code / 'examples' / (self.example + '.dx')
    total_alloc, total_time = parse_result(
        read_stderr(code / 'dex', '--lib-path', code / 'lib',
                    'script', source, '+RTS', '-s',
                    env={'XDG_CACHE_HOME': Path(xdg_home) / self.variant}))
    return [Result(self.example, 'alloc', total_alloc),
            Result(self.example, 'time', total_time)]

  def baseline(self):
    return DexEndToEnd(self.example, self.repeats, 'baseline')


@dataclass
class DexRuntime:
  """Measures isolated run time on a benchmark."""
  name: str
  repeats: int
  variant: str = 'latest'

  def clean(self, code, xdg_home):
    run(code / 'dex', 'clean', env={'XDG_CACHE_HOME': Path(xdg_home) / self.variant})

  def bench(self, code, xdg_home):
    source = code / 'benchmarks' / (self.name + '.dx')
    runtime = parse_result_runtime(
        read(code / 'dex', '--lib-path', code / 'lib',
             'script', source, '+RTS', '-s',
             env={'XDG_CACHE_HOME': Path(xdg_home) / self.variant}))
    return [Result(self.name, 'runtime', runtime)]

  def baseline(self):
    return Python(self.name, self.repeats, RUNTIME_BASELINES[self.name])


@dataclass
class Python:
  name: str
  repeats: int
  f: Callable

  def clean(self, _code, _xdg_home):
    # Ensure NumPy can only use a single thread for an
    # apples-to-apples comparison.
    os.environ["OMP_NUM_THREADS"] = "1"
    os.environ["MKL_NUM_THREADS"] = "1"
    os.environ["OPENBLAS_NUM_THREADS"] = "1"

  def bench(self, _code, _xdg_home):
    avg_time, iters = bench_python(self.f)
    return [Result(self.name, 'runtime', avg_time)]


def numpy_sum():
  n = 1000000
  xs = np.arange(n, dtype=np.float64)
  return np.sum(xs * xs)


BASELINE = '8dd1aa8539060a511d0f85779ae2c8019162f567'
BENCHMARKS = [
    DexEndToEnd('kernelregression', 10),
    DexEndToEnd('psd', 10),
    DexEndToEnd('fluidsim', 10),
    DexEndToEnd('regression', 10),
    DexRuntime('fused_sum', 5)]
RUNTIME_BASELINES = {
    'fused_sum': numpy_sum
}


def run(*args, capture=False, env=None):
  print('> ' + ' '.join(map(str, args)))
  result = subprocess.run(args, text=True, capture_output=capture, env=env)
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
    run('git', 'checkout', commit)
    run('make', 'install', env=dict(os.environ, PREFIX=commit))
    run('cp', '-r', 'lib', install_path / 'lib')
    run('cp', '-r', 'examples', install_path / 'examples')
    run('cp', '-r', 'benchmarks', install_path / 'benchmarks')
  return install_path


def benchmark(baseline_path, latest_path):
  with tempfile.TemporaryDirectory() as tmp:
    results = []
    for test in BENCHMARKS:
      baseline = test.baseline()
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
  if len(argv) != 3:
    raise ValueError("Expected three arguments!")
  datapath, commitpath, commit = argv
  print('Building baseline: {BASELINE}')
  baseline_path = build(BASELINE)
  print(f'Building latest: {commit}')
  latest_path = build(commit)
  results = benchmark(baseline_path, latest_path)
  save(commit, results, datapath, commitpath)
  print('DONE!')


if __name__ == '__main__':
  main(sys.argv[1:])
