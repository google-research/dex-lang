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

void showFloat(char **resultPtr, float x) {
  auto p = reinterpret_cast<char*>(malloc_dex(100));
  auto n = sprintf(p, "%.4f", x);
  auto result1Ptr = reinterpret_cast<int32_t*>(resultPtr[0]);
  auto result2Ptr = reinterpret_cast<char**>(  resultPtr[1]);
  *result1Ptr = n;
  *result2Ptr = p;
}

#ifdef DEX_CUDA

} // extern "C"

template<typename ...Args>
using driver_func = CUresult(*)(Args...);

template<typename ...Args1, typename ...Args2>
void dex_check(const char* fname, driver_func<Args1...> f, Args2... args) {
  auto result = f(args...);
  if (result != 0) {
    const char* error_name = nullptr;
    const char* error_msg = nullptr;
    cuGetErrorName(result, &error_name);
    cuGetErrorString(result, &error_msg);
    if (!error_name) error_name = "unknown error";
    if (!error_msg) error_msg = "Unknown error";
    printf("CUDA driver error at %s (%s): %s\n", fname, error_name, error_msg);
    std::abort();
  }
}

#define CHECK(f, ...) dex_check(#f, f, __VA_ARGS__)

extern "C" {

void load_cuda_array(void* host_ptr, void* device_ptr, int64_t bytes) {
  CHECK(cuMemcpyDtoH, host_ptr, reinterpret_cast<CUdeviceptr>(device_ptr), bytes);
}

void dex_cuMemcpyDtoH(int64_t bytes, char* device_ptr, char* host_ptr) {
  CHECK(cuMemcpyDtoH, host_ptr, reinterpret_cast<CUdeviceptr>(device_ptr), bytes);
}

void dex_cuMemcpyHtoD(int64_t bytes, char* device_ptr, char* host_ptr) {
  CHECK(cuMemcpyHtoD, reinterpret_cast<CUdeviceptr>(device_ptr), host_ptr, bytes);
}

void dex_queryParallelismCUDA(const void* _, int64_t iters,
                              int32_t* numWorkgroups, int32_t* workgroupSize) {
  if (iters == 0) {
    *numWorkgroups = 0;
    *workgroupSize = 0;
    return;
  }
  // TODO: Use the occupancy calculator, or at least use a fixed number of blocks?
  const int32_t fixedWgSize = 256;
  *workgroupSize = fixedWgSize;
  *numWorkgroups = (iters + fixedWgSize - 1) / fixedWgSize;
}

void dex_cuLaunchKernel(const void* kernel_text, int64_t iters, char** args) {
  if (iters == 0) return;
  CUmodule module;
  CHECK(cuModuleLoadData, &module, kernel_text);
  CUfunction kernel;
  CHECK(cuModuleGetFunction, &kernel, module, "kernel");
  int32_t block_dim_x, grid_dim_x;
  dex_queryParallelismCUDA(nullptr, iters, &grid_dim_x, &block_dim_x);
  CHECK(cuLaunchKernel, kernel,
                        grid_dim_x, 1, 1,               // grid size
                        block_dim_x, 1, 1,              // block size
                        0,                              // shared memory
                        CU_STREAM_LEGACY,               // stream
                        reinterpret_cast<void**>(args), // kernel arguments
                        nullptr);
  CHECK(cuModuleUnload, module);
}

char* dex_cuMemAlloc(int64_t size) {
  if (size == 0) return nullptr;
  CUdeviceptr ptr;
  CHECK(cuMemAlloc, &ptr, size);
  return reinterpret_cast<char*>(ptr);
}

void dex_cuMemFree(char* ptr) {
  if (!ptr) return;
  CHECK(cuMemFree, reinterpret_cast<CUdeviceptr>(ptr));
}

void dex_ensure_has_cuda_context() {
  CHECK(cuInit, 0);
  CUcontext ctx;
  CHECK(cuCtxGetCurrent, &ctx);
  if (!ctx) {
    CUdevice dev;
    CHECK(cuDeviceGet, &dev, 0);
    CHECK(cuDevicePrimaryCtxRetain, &ctx, dev);
    CHECK(cuCtxPushCurrent, ctx);
  }
}

#undef CHECK

#endif

int32_t dex_queryParallelismMC(int64_t iters) {
  int32_t nthreads = std::thread::hardware_concurrency();
  if (iters < nthreads) {
    nthreads = iters;
  }
  return nthreads;
}

void dex_launchKernelMC(char *function_ptr, int64_t size, char **args) {
  auto function = reinterpret_cast<void (*)(int32_t, int32_t, char**)>(function_ptr);
  int32_t nthreads = dex_queryParallelismMC(size);
  std::vector<std::thread> threads(nthreads);
  for (int32_t tid = 0; tid < nthreads; ++tid) {
    threads[tid] = std::thread([function, args, tid, nthreads]() {
      function(tid, nthreads, args);
    });
  }
  for (auto& thread : threads) {
    thread.join();
  }
}

} // end extern "C"
