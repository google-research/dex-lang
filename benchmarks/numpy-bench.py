# Copyright 2019 Google LLC
#
# Use of this source code is governed by a BSD-style
# license that can be found in the LICENSE file or at
# https://developers.google.com/open-source/licenses/bsd

import time
import numpy as np
import sys
from __future__ import print_function


n = int(sys.argv[1])
x = np.random.randn(n,n)
y = np.random.randn(n,n)

t0 = time.time()
z = np.dot(x, y)
print("Time for {} by {} matmul: {} s".format(n,n, time.time() - t0))
