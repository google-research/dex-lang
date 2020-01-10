# Copyright 2019 Google LLC
#
# Use of this source code is governed by a BSD-style
# license that can be found in the LICENSE file or at
# https://developers.google.com/open-source/licenses/bsd

import sys
import numpy as np
import dex_binary_object as dbo
sys.path.append("../jax")
from examples import datasets

def oneHotToInt(xs):
  xsInt = np.sum(xs * np.arange(10)[None,:], axis=1).astype(np.int64)
  print(xsInt.shape)
  assert np.max(xsInt) == 9
  return xsInt

data = tuple(x.astype(np.float64) for x in datasets.mnist())
train_images, train_labels, test_images, test_labels = data

train_images_unflat = train_images.reshape((60000, 28, 28))
test_images_unflat  = test_images.reshape( (10000, 28, 28))

train_labels_int = oneHotToInt(train_labels)
test_labels_int  = oneHotToInt(test_labels)

data_out = (train_images_unflat, train_labels_int,
            test_images_unflat, test_labels_int)

with open("scratch/mnist.dxbo", "w") as f:
  dbo.dump(data_out, f)
