# Copyright 2020 Google LLC
#
# Use of this source code is governed by a BSD-style
# license that can be found in the LICENSE file or at
# https://developers.google.com/open-source/licenses/bsd

import sys

from util import np, bench_python, bench_dex, print_result

n, = map(int, sys.argv[1:])
x = np.ones((n,), dtype=np.float64)
y = np.ones((n,), dtype=np.float64)

np_add_time, add_loops = bench_python(lambda: x + y)
# Unrolling multiplication with x is a lot faster than using **
np_poly_time, poly_loops = bench_python(lambda: 4 * x * x * x * x + 3 * x * x * x + 2 * x * x + x)
dex_add_time, dex_poly_time = bench_dex('pointwise.dx', n=n, loops=add_loops)
print_result('1D addition', np_add_time, dex_add_time, add_loops)
print_result('Polynomial evaluation', np_poly_time, dex_poly_time, poly_loops)
