# Copyright 2020 Google LLC
#
# Use of this source code is governed by a BSD-style
# license that can be found in the LICENSE file or at
# https://developers.google.com/open-source/licenses/bsd

import argparse
import os
import json
import sqlite3
import subprocess

from collections import namedtuple
from datetime import datetime

bench_names = ["mandel", "mandel", "foo"]
microbench_file = "benchmarks/microbench.dx"
# TODO: allow macro benchmarks too (probably one-per file, run selectively)

db_name = "bench_results.db"
BenchResult = namedtuple("BenchResult", ["t_compile", "t_run"])

initialize_sql = \
"""
create table results (
   version    text,
   benchmark  text,
   t_compile  real,
   t_run      real,
   timestamp  text,   -- YYYY-MM-DD HH:MM:SS
   primary key (version, benchmark)
   -- TODO: some summary value of the actual result computed (as a sanity check)
);
"""

add_result_sql = \
"""
insert or replace into results values (?, ?, ?, ?, ?)
"""

def ensure_db_exists():
  if not os.path.isfile(db_name):
    con = sqlite3.connect(db_name)
    with con:
      con.execute(initialize_sql)

def write_result(version, bench_name, t_compile, t_run):
  con = sqlite3.connect(db_name)
  timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
  record = (version, bench_name, t_compile, t_run, timestamp)
  with con:
    con.execute(add_result_sql, record)

def run_benchmark(bench_name):
  if bench_name == "mandel":
    return BenchResult(1.0, 2.0, 3.0)
  elif bench_name == "foo":
    return BenchResult(1.1, 2.2, 3.3)
  else:
    raise Exception

def run_adhoc(args):
  ensure_db_exists()
  proc_result = subprocess.run(
      ["stack", "exec", "dex", "--", "script", "--result-only", microbench_file],
      capture_output=True, check=True)
  for result_str in proc_result.stdout.splitlines():
    result = json.loads(result_str)
    write_result(args.name, result["bench_name"],
                 result["compile_time"], result["run_time"])

def run_history(args):
  ensure_db_exists()
  assert False  # TODO

if __name__ == "__main__":

  # TODO: add an option to only run particular benchmarks

  parser = argparse.ArgumentParser(description='Benchmark utility')
  subparsers = parser.add_subparsers(dest='cmd', required=True)

  adhoc_parser = subparsers.add_parser('adhoc', help='Run benchmarks on current source tree')
  adhoc_parser.add_argument('--name', help='name of an ad-hoc benchmark run', default='scratch')
  adhoc_parser.set_defaults(func=run_adhoc)

  history_parser = subparsers.add_parser('history', help='Run benchmarks on historical commits')
  history_parser.add_argument('--num_commits', type=int, default=10,
                              help='number of historical commits to benchmark')

  history_parser.set_defaults(func=run_history)
  args = parser.parse_args()
  args.func(args)
