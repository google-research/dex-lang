// Copyright 2019 Google LLC
//
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file or at
// https://developers.google.com/open-source/licenses/bsd

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
