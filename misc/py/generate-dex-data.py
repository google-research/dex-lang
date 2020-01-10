# Copyright 2019 Google LLC
#
# Use of this source code is governed by a BSD-style
# license that can be found in the LICENSE file or at
# https://developers.google.com/open-source/licenses/bsd

from collections import namedtuple
import numpy as np
import dex_binary_object as dbo

data = (1.2,
        12,
        (),
        True,
        False,
        (-2, np.array([1.0, 2.0, 3.0])),
        np.array([[10.0, 20.0, 30.0], [0.1, 0.2, 0.3]])  ,
        np.array([[10.0, 20.0, 30.0], [0.1, 0.2, 0.3]]).T,
        1.3,
        np.array(0.123),
        np.array([[[1]]]),
        np.array([6,5,4,3]),
        np.array([True, False, True]))

with open("test-scratch/pydata.dxbo", "w") as f:
  dbo.dump(data, f)
