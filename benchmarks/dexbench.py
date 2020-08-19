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
import socket

from datetime import datetime

backends = ["CPU", "Multicore-CPU", "GPU"]
dex_microbench_file = "benchmarks/microbench.dx"
# TODO: allow macro benchmarks too (probably one-per file, run selectively)

db_name = "bench_results.db"

def add_record(con, table, record):
  template ="insert into {} values ({})".format(
    table, ",".join("?" * len(record)))
  con.execute(template, record)

def prepare_machine():
  pass

def restore_machine():
  pass

def run_benches(lang, backend):
  if lang == "dex":
    if backend == "CPU":
      backend_args = []
    elif backend == "Multicore-CPU":
      backend_args = ["--backend", "LLVM-MC"]
    elif backend == "GPU":
      backend_args = ["--backend", "LLVM-CUDA"]
    else:
      raise Exception
    command = (["stack", "exec", "dex", "--"] + backend_args +
               ["script", "--outfmt", "JSON", dex_microbench_file])
  else:
    raise Exception("Unrecognized language: {}".format(lang))
  proc_result = subprocess.run(command, capture_output=True, check=True)
  return map(parse_result_str, proc_result.stdout.splitlines())

def parse_result_str(s):
  result = json.loads(s)
  if not "bench_name" in result:
    raise Exception("not a benchmark:\n" + str(s))
  elif "error" in result:
    return (result["bench_name"], None, None,
            None, result["error"])
  else:
    ans = result.get("ans", "")
    return (result["bench_name"], result["compile_time"], result["run_time"],
            ans, None)

def bench_run(args):
  if not os.path.isfile(db_name):
    raise Exception("database doesn't exist")
  prepare_machine()
  con = sqlite3.connect(db_name)
  with con:
    run_name = args.name
    lang = args.lang
    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    hostname = socket.gethostname()
    add_record(con, "runs", (run_name, timestamp, hostname))
    for trial in range(args.num_trials):
      for backend in backends:
        results = run_benches(lang, backend)
        for (bench_name, t_compile, t_run, ans, err) in results:
          add_record(con, "results",
                     (run_name, lang, backend, bench_name, trial,
                      t_compile, t_run, ans, err))
  restore_machine()

def run_commit_history(args):
  check_db_exists()
  assert False  # TODO

if __name__ == "__main__":

  # TODO: add an option to only run particular benchmarks

  parser = argparse.ArgumentParser(description='Benchmark utility')
  subparsers = parser.add_subparsers(dest='cmd', required=True)

  adhoc_parser = subparsers.add_parser('run', help='Run benchmarks on current source tree')
  adhoc_parser.add_argument('--name', help='name of run', required=True)
  adhoc_parser.add_argument('--lang', help='language', default='dex')
  adhoc_parser.add_argument('--num_trials', type=int, help='name of run', default=5)
  adhoc_parser.set_defaults(func=bench_run)

  history_parser = subparsers.add_parser('history', help='Run benchmarks on historical commits')
  history_parser.add_argument('--num_commits', type=int, default=10,
                              help='number of historical commits to benchmark')

  history_parser.set_defaults(func=run_commit_history)
  args = parser.parse_args()
  args.func(args)
