import jax
import dex
from dex.interop import jax as djax
import numpy as np

import time
import timeit

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


def main():
  with open('benchmarks/conv.dx', 'r') as f:
    m = dex.Module(f.read())
    dex_conv = djax.primitive(m.conv_spec)
    shp = (int(m.n), int(m.width), int(m.side), int(m.side))
    xs = jax.random.normal(jax.random.PRNGKey(1), shp, dtype=jax.numpy.float32)
    filter_size = int(m.filter_size)
    msg = ("TODO Make dex.interop.primitive return Jax Device Arrays, "
           "and change this assert to a block_until_ready() call.")
    assert isinstance(dex_conv(xs, filter_size), np.ndarray), msg
    time_s, loops = bench_python(lambda : dex_conv(xs, filter_size))
    print(f"> Run time: {time_s} s \t(based on {loops} runs)")


if __name__ == '__main__':
  main()
