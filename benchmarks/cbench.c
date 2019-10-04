// Copyright 2019 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "stdio.h"
#include "stdlib.h"

void matmul(int n, double x[], double y[], double out[]) {
  double accum = 0.0;
  for (int i=0; i<n; i++) {
    for (int k=0; k<n; k++) {
      for (int j=0; j<n; j++) {
        accum += x[i*n + j] * y[j*n + k];
      }
      out[i*n + k] = accum;
    }
  }
}

int main(int argc, const char* argv[]) {
  int n = atoi(argv[1]);
  double* x = malloc(n*n * sizeof(double));
  double* y = malloc(n*n * sizeof(double));
  double* z = malloc(n*n * sizeof(double));
  matmul(n, x, y, z);
}
