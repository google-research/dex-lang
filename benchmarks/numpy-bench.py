# Copyright 2019 Google LLC
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import time
import numpy as np
import sys


n = int(sys.argv[1])
x = np.random.randn(n,n)
y = np.random.randn(n,n)

t0 = time.time()
z = np.dot(x, y)
print "Time for {} by {} matmul: {} s".format(n,n, time.time() - t0)
