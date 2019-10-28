// Copyright 2019 Google LLC
//
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file or at
// https://developers.google.com/open-source/licenses/bsd

#include "stdio.h"
#include "stdlib.h"
#include "time.h"

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
  clock_t t0, t1;
  double* x = malloc(n*n * sizeof(double));
  double* y = malloc(n*n * sizeof(double));
  double* z = malloc(n*n * sizeof(double));
  t0 = clock();
  matmul(n, x, y, z);
  t1 = clock();
  printf("Time for %d by %d matmul: %lf s\n", n, n, ((double)(t1 - t0)) / CLOCKS_PER_SEC);
}
