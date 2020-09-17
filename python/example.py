# Copyright 2020 Google LLC
#
# Use of this source code is governed by a BSD-style
# license that can be found in the LICENSE file or at
# https://developers.google.com/open-source/licenses/bsd

import dex

m = dex.Module("""
x = 2.5
y = [2, 3, 4]
""")

print(m.x)
print(m.y)
print(int(m.x))
