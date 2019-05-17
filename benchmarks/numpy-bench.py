import time
import numpy as np
import sys


n = int(sys.argv[1])
x = np.random.randn(n,n)
y = np.random.randn(n,n)

t0 = time.time()
z = np.dot(x, y)
print "Time for {} by {} matmul: {} s".format(n,n, time.time() - t0)
