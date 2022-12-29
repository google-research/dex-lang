
from absl import app
from absl import flags

import jax
from jax import numpy as jnp
import jaxopt
import dex
from dex.interop import jax as djax
import numpy as onp
from sklearn import datasets

import time
import timeit

FLAGS = flags.FLAGS

flags.DEFINE_integer("maxiter", default=30, help="Max # of iterations.")
flags.DEFINE_integer("n_samples", default=10000, help="Number of samples.")
flags.DEFINE_integer("n_features", default=200, help="Number of features.")
flags.DEFINE_integer("n_classes", default=5, help="Number of classes.")
flags.DEFINE_string("task", "binary_logreg", "Task to benchmark.")


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

def multiclass_logreg_jaxopt(X, y):
  data = (X, y)
  fun = jaxopt.objective.multiclass_logreg
  init = jnp.zeros((X.shape[1], FLAGS.n_classes))
  bfgs = jaxopt.BFGS(fun=fun, linesearch='zoom')
  state = bfgs.init_state(init, data=data)
  params = init

  def cond_fn(state):
    return (state.error > bfgs.tol) & (state.iter_num < bfgs.maxiter)

  @jax.jit
  def update(params, state):
    return bfgs.update(params, state, data=data)

  start_time = time.time()
  params, state = update(params, state)
  compile_time = time.time()

  while cond_fn(state):
    params, state = update(params, state)
  run_time = time.time()

  return compile_time - start_time, run_time - compile_time, state.error, state.iter_num


def main(argv):
  X, y = datasets.make_classification(n_samples=FLAGS.n_samples,
                                      n_features=FLAGS.n_features,
                                      n_classes=FLAGS.n_classes,
                                      n_informative=FLAGS.n_classes,
                                      random_state=0)
  jaxopt_results = multiclass_logreg_jaxopt(X, y)
  print(f"> Jaxopt results: {jaxopt_results}")

  with open('examples/bfgs.dx', 'r') as f:
    m = dex.Module(f.read())
    # TODO pass max iter, etc.
    dex_bfgs = djax.primitive(m.multiclass_logreg)

    # time_s, loops = bench_python(lambda : dex_bfgs(X, y))
    # print(f"> Run time: {time_s} s \t(based on {loops} runs)")
    dex_bfgs(jnp.array(X), jnp.array(y), FLAGS.n_classes)
    
    # # This runs
    # dex_run_bfgs = djax.primitive(m.run_logreg)
    # dex_run_bfgs(0)


if __name__ == '__main__':
  app.run(main)
