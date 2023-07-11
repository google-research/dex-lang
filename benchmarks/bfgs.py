
from absl import app
from absl import flags

from jax import numpy as jnp
import jaxopt
import dex
from dex.interop import jax as djax
from sklearn import datasets

import time

FLAGS = flags.FLAGS

flags.DEFINE_integer("maxiter", default=30, help="Max # of iterations.")
flags.DEFINE_integer("maxls", default=15, help="Max # of linesearch iterations.")
flags.DEFINE_float("tol", default=1e-3, help="Tolerance of the stopping criterion.")
flags.DEFINE_integer("n_samples", default=1000, help="Number of samples.")
flags.DEFINE_integer("n_features", default=20, help="Number of features.")
flags.DEFINE_integer("n_classes", default=5, help="Number of classes.")
flags.DEFINE_string("task", "binary_logreg", "Task to benchmark.")


def multiclass_logreg_jaxopt(X, y):
  data = (X, y)
  fun = jaxopt.objective.multiclass_logreg
  init = jnp.zeros((X.shape[1], FLAGS.n_classes))
  bfgs = jaxopt.BFGS(
    fun=fun,
    linesearch='zoom',
    maxiter=FLAGS.maxiter,
    maxls=FLAGS.maxls,
    tol=FLAGS.tol)

  start_time = time.time()
  _ = bfgs.run(init_params=init, data=data)
  compile_time = time.time()

  _, state = bfgs.run(init_params=init, data=data)
  run_time = time.time()

  return compile_time - start_time, run_time - compile_time, state.error, state.iter_num, state.value


def main(argv):
  # Compare performance of Jaxopt and Dex BFGS on a multiclass logistic regression problem.
  X, y = datasets.make_classification(n_samples=FLAGS.n_samples,
                                      n_features=FLAGS.n_features,
                                      n_classes=FLAGS.n_classes,
                                      n_informative=FLAGS.n_classes,
                                      random_state=0)
  time_incl_jit, time_excl_jit, _, _, dex_value = multiclass_logreg_jaxopt(X, y)
  print(f"> Jaxopt results:\n   Time incl JIT: {time_incl_jit}\n"
        f"   Time excl JIT: {time_excl_jit}\n   Loss function value: {dex_value}")

  with open('examples/bfgs.dx', 'r') as f:
    m = dex.Module(f.read())
    dex_bfgs = djax.primitive(m.multiclass_logreg_int)

    start_time = time.time()
    dex_value = dex_bfgs(
      jnp.array(X),
      jnp.array(y),
      FLAGS.n_classes,
      FLAGS.maxiter,
      FLAGS.maxls,
      FLAGS.tol)
    print(f"> Dex results:\n   Total time: {time.time() - start_time}\n"
          f"   Loss function value: {dex_value}")


if __name__ == '__main__':
  app.run(main)
