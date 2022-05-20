import re
import os
import sys
import csv
import subprocess
import tempfile
from functools import partial
from dataclasses import dataclass
from pathlib import Path
from typing import Union, Sequence


BASELINE = '8dd1aa8539060a511d0f85779ae2c8019162f567'
BENCH_EXAMPLES = [('kernelregression', 10), ('psd', 10), ('fluidsim', 10), ('regression', 10)]


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
  return install_path


def benchmark(baseline_path, latest_path):
  with tempfile.TemporaryDirectory() as tmp:
    def clean(p, uniq):
      run(p / 'dex', 'clean', env={'XDG_CACHE_HOME': Path(tmp) / uniq})
    def bench(p, uniq, bench_name, path):
      return parse_result(
          read_stderr(p / 'dex', '--lib-path', p / 'lib',
                      'script', path, '+RTS', '-s',
                      env={'XDG_CACHE_HOME': Path(tmp) / uniq}))
    baseline_clean = partial(clean, baseline_path, 'baseline')
    baseline_bench = partial(bench, baseline_path, 'baseline')
    latest_clean = partial(clean, latest_path, 'latest')
    latest_bench = partial(bench, latest_path, 'latest')
    results = []
    for example, repeats in BENCH_EXAMPLES:
      baseline_example = baseline_path / 'examples' / (example + '.dx')
      latest_example = latest_path / 'examples' / (example + '.dx')
      # warm-up the caches
      baseline_clean()
      baseline_bench(example, baseline_example)
      latest_clean()
      latest_bench(example, latest_example)
      for i in range(repeats):
        print(f'Iteration {i}')
        baseline_alloc, baseline_time = baseline_bench(example, baseline_example)
        latest_alloc, latest_time = latest_bench(example, latest_example)
        print(baseline_alloc, '->', latest_alloc)
        print(baseline_time, '->', latest_time)
        # Allocation measurements are stable enough so that we don't need to
        # take too many. But take two to get some estimate of the noise.
        if i < 2:
          results.append(Result(example, 'alloc', latest_alloc))
        results.append(Result(example, 'time_rel', latest_time / baseline_time))
    return results


@dataclass
class Result:
  benchmark: str
  measure: str
  value: Union[int, float]


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
