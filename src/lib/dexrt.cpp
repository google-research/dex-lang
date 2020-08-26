// Copyright 2019 Google LLC
//
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file or at
// https://developers.google.com/open-source/licenses/bsd

#include <cstdio>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <thread>
#include <vector>

#ifdef DEX_CUDA
#include <cuda.h>
#endif

extern "C" {

char* malloc_dex(int64_t nbytes) {
  // XXX: Changes to this value might require additional changes to parameter attributes in LLVM
  static const int64_t alignment = 64;
  char *ptr;
  if (posix_memalign(reinterpret_cast<void**>(&ptr), alignment, nbytes)) {
    fprintf(stderr, "Failed to allocate %ld bytes", (long)nbytes);
    std::abort();
  }
  return ptr;
}

void free_dex(char* ptr) {
  free(ptr);
}

long int_to_index_set(long i, long n) {
  if (i < 0 || i >= n) {
    printf("Index out of bounds. %ld not in [0, %ld)\n", i, n);
    exit(1);
  }
  return i;
}

uint32_t rotate_left(uint32_t x, uint32_t d) {
  return (x << d) | (x >> (32 - d));
}

uint64_t apply_round(uint32_t x, uint32_t y, int rot) {
  uint64_t out;

  x = x + y;
  y = rotate_left(y, rot);
  y = x ^ y;

  out = (uint64_t) x;
  out = (out << 32) | y;
  return out;
}

uint64_t threefry2x32(uint64_t keypair, uint64_t count) {
  /* Based on jax's threefry_2x32 by Matt Johnson and Peter Hawkins */

  uint32_t k0;
  uint32_t k1;
  uint32_t k2;

  uint32_t x;
  uint32_t y;

  uint64_t out;
  int i;

  int rotations1[4] = {13, 15, 26, 6};
  int rotations2[4] = {17, 29, 16, 24};

  k0 = (uint32_t) (keypair >> 32);
  k1 = (uint32_t) keypair;
  k2 = k0 ^ k1 ^ 0x1BD11BDA;
  x = (uint32_t) (count >> 32);
  y = (uint32_t) count;

  x = x + k0;
  y = y + k1;


  for (i=0;i<4;i++) {
    count = apply_round(x, y, rotations1[i]);
    x = (uint32_t) (count >> 32);
    y = (uint32_t) count;
  }
  x = x + k1;
  y = y + k2 + 1;


  for (i=0;i<4;i++) {
    count = apply_round(x, y, rotations2[i]);
    x = (uint32_t) (count >> 32);
    y = (uint32_t) count;
  }
  x = x + k2;
  y = y + k0 + 2;

  for (i=0;i<4;i++) {
    count = apply_round(x, y, rotations1[i]);
    x = (uint32_t) (count >> 32);
    y = (uint32_t) count;
  }
  x = x + k0;
  y = y + k1 + 3;

  for (i=0;i<4;i++) {
    count = apply_round(x, y, rotations2[i]);
    x = (uint32_t) (count >> 32);
    y = (uint32_t) count;
  }
  x = x + k1;
  y = y + k2 + 4;

  for (i=0;i<4;i++) {
    count = apply_round(x, y, rotations1[i]);
    x = (uint32_t) (count >> 32);
    y = (uint32_t) count;
  }
  x = x + k2;
  y = y + k0 + 5;

  out = (uint64_t) x;
  out = (out << 32) | y;
  return out;
}

long randint(uint64_t keypair, long nmax) {
  return keypair % nmax; // TODO: correct this with rejection sampling or more bits
}

double randunif(uint64_t keypair) {
  /* Assumes 1023 offset and 52 mantissa bits and probably very platform-specific. */
  uint64_t mantissa_bits;
  uint64_t exponent_bits;
  uint64_t bits;

  mantissa_bits = keypair & ((((uint64_t) 1) << 52) - 1);
  exponent_bits = ((uint64_t) 1023) << 52;
  bits = mantissa_bits | exponent_bits;

  double out = *(double*)&bits;
  return out - 1;
}

void dex_parallel_for(void *function_ptr, uint64_t size, void **args) {
  auto function = reinterpret_cast<void (*)(uint64_t, uint64_t, void**)>(function_ptr);
  uint64_t nthreads = std::thread::hardware_concurrency();
  if (size < nthreads) {
    nthreads = size;
  }
  std::vector<std::thread> threads(nthreads);
  auto chunk_size = size / nthreads;
  for (uint64_t t = 0; t < nthreads; ++t) {
    auto start = t * chunk_size;
    auto end = t == nthreads - 1 ? size : (t + 1) * chunk_size;
    threads[t] = std::thread([function, args, start, end]() {
      function(start, end, args);
    });
  }
  for (auto& thread : threads) {
    thread.join();
  }
}

#ifdef DEX_CUDA
void check_result(const char *msg, int result) {
  if (result != 0) {
    printf("CUDA API error at %s: %d\n", msg, result);
  }
}

void* load_cuda_array(void* device_ptr, int64_t bytes) {
  void* host_ptr = malloc_dex(bytes);
  check_result("cuMemcpyDtoH", cuMemcpyDtoH(host_ptr, (CUdeviceptr)device_ptr, bytes));
  return host_ptr;
}

void dex_load_cuda_scalar(int64_t bytes, void* device_ptr, void* host_ptr) {
  check_result("cuMemcpyDtoH", cuMemcpyDtoH(host_ptr, (CUdeviceptr)device_ptr, bytes));
}

void dex_store_cuda_scalar(int64_t bytes, void* device_ptr, void* host_ptr) {
  check_result("cuMemcpyHtoD", cuMemcpyHtoD((CUdeviceptr)device_ptr, host_ptr, bytes));
}
#endif

} // end extern "C"
