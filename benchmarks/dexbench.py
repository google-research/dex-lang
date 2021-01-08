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

import time
from functools import partial
from contextlib import contextmanager

backends = ["CPU", "GPU"]
# TODO: allow macro benchmarks too (probably one-per file, run selectively)
repo_url = "https://github.com/google-research/dex-lang.git"
dex_microbench_file = os.path.abspath("benchmarks/microbench.dx")
jax_microbench_file = os.path.abspath("benchmarks/python/microbench.py")
db_name             = os.path.abspath("results.db")
db_init_fname       = os.path.abspath("benchmarks/queries/init.sql")
build_dir           = os.path.abspath(".benchmarks")

silly_map = map
def map(*args): return list(silly_map(*args))

def run_capture(command, extra_env = {}):
  env = os.environ.copy()
  env.update(**extra_env)
  result = subprocess.run(command, capture_output=True, env=env)
  if result.returncode == 0:
    return result.stdout.decode("utf-8")
  else:
    print(result.stdout)
    print(result.stderr)
    raise Exception

def run(command):
  subprocess.run(command, check=True)

def add_record(con, table, record):
  template ="insert into {} values ({})".format(
    table, ",".join("?" * len(record)))
  con.execute(template, record)

def prepare_machine():
  pass  # TODO

def restore_machine():
  pass  # TODO

def run_benches(lang, backend):
  if lang == "dex":
    if backend == "CPU":
      backend_args = ["--backend", "llvm-mc"]
      env = {}
    elif backend == "GPU":
      backend_args = ["--backend", "llvm-cuda"]
      env = {"CUDA_LAUNCH_BLOCKING":"1"}
    else:
      raise Exception
    command = (["stack", "exec", "dex", "--"] + backend_args +
               ["script", "--outfmt", "json", dex_microbench_file])
  elif lang == "jax":
    if backend == "CPU":
      env = {"CUDA_VISIBLE_DEVICES":""}
    elif backend == "GPU":
      env = {}
    else:
      raise Exception
    command = (["python3", jax_microbench_file])
  else:
    raise Exception("Unrecognized language: {}".format(lang))
  try:
    proc_result = run_capture(command, extra_env=env)
    return map(parse_result_str, proc_result.splitlines())
  except:
    print("=== benchmark failed ===")
    return []

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

@contextmanager
def get_db_con():
  if not os.path.isfile(db_name):
    run(["sqlite3", db_name, ".read {}".format(db_init_fname)])
  try:
    con = sqlite3.connect(db_name)
    with con:
      yield con
  finally:
    con.close()

def change_to_build_dir():
  if not os.path.exists(build_dir):
    print("Building local copy of Dex")
    run(["git", "clone", repo_url, build_dir])
  os.chdir(build_dir)

def bench_run(name, lang, num_trials):
  prepare_machine()
  with get_db_con() as con:
    timestamp = time.time()
    hostname = socket.gethostname()
    add_record(con, "runs", (name, timestamp, hostname))
    for trial in range(num_trials):
      for backend in backends:
        print("trial: {}, backend: {}, lang : {}".format(trial, backend, lang))
        results = run_benches(lang, backend)
        for (bench_name, t_compile, t_run, ans, err) in results:
          add_record(con, "results",
                     (name, lang, backend, bench_name, trial,
                      t_compile, t_run, ans, err))
  con.close()
  restore_machine()

def fetch_commit_history(con, branch, num_commits):
  run(["git", "checkout", branch])
  run(["git", "pull"])  # TODO: carry on if it's just a local branch
  log = run_capture(["git", "log", "--format=%H %at", "-n", str(num_commits)])
  def parse_row(row):
    commit_hash, unixtime = row.split()
    return commit_hash, int(unixtime)
  commits = map(parse_row, log.splitlines())
  con.executemany("insert or replace into commits values (?,?)", commits)

def run_commit_history(args):
  with get_db_con() as con:
    change_to_build_dir()
    fetch_commit_history(con, args.branch, args.num_commits)
    commits_to_run = list(con.execute(
      "select commit_hash from commits " +
      "where commit_hash not in (select commit_hash from ci_runs)"))
  if commits_to_run:
    print("Running {} commits".format(len(commits_to_run)))
  else:
    print("Up to date. Nothing to run")
  for commit, in commits_to_run[::-1]:
    print("Running {}".format(commit))
    run(["git", "checkout", commit])
    run(["make"])
    with get_db_con() as con:
      con.execute("insert into ci_runs values (?)", (commit,))
    bench_run(commit, "dex", args.num_trials)

if __name__ == "__main__":

  # TODO: add an option to only run particular benchmarks
  parser = argparse.ArgumentParser(description='Benchmark utility')
  subparsers = parser.add_subparsers(dest='cmd', required=True)

  adhoc_parser = subparsers.add_parser('run', help='Run benchmarks on current source tree')
  adhoc_parser.add_argument('--name', help='name of run', required=True)
  adhoc_parser.add_argument('--lang', help='language', default='dex')
  adhoc_parser.add_argument('--num_trials', type=int, help='name of run', default=5)
  adhoc_parser.set_defaults(
    func=lambda arsg: bench_run(args.name, args.lang, args.num_trials))

  history_parser = subparsers.add_parser('history', help='Run benchmarks on historical commits')
  history_parser.add_argument('--num_commits', type=int, default=10,
                              help='number of historical commits to benchmark')
  history_parser.add_argument('--branch', help='branch to run', default='main')
  history_parser.add_argument('--num_trials', type=int, help='name of run', default=5)
  history_parser.set_defaults(func=run_commit_history)
  args = parser.parse_args()
  args.func(args)
