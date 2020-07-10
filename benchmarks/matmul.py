# Copyright 2020 Google LLC
#
# Use of this source code is governed by a BSD-style
# license that can be found in the LICENSE file or at
# https://developers.google.com/open-source/licenses/bsd

import sys

from util import np, bench_python, bench_dex, print_result

n, k, m = map(int, sys.argv[1:])
x = np.random.randn(n, k).astype(np.float64)
y = np.random.randn(k, m).astype(np.float64)

numpy_time, loops = bench_python(lambda: x.dot(y))
dex_time, = bench_dex('matmul.dx', n=n, k=k, m=m, loops=loops)
print_result('Matrix multiplication', numpy_time, dex_time, loops)
