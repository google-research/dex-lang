// Copyright 2019 Google LLC
//
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file or at
// https://developers.google.com/open-source/licenses/bsd

#include <cinttypes>
#include <cstdio>
#include <cstddef>
#include <cstdlib>
#include <cstring>
#include <thread>
#include <vector>
#include <cctype>

#include <type_traits>
#include <cstdint>

#if defined(__linux__)
static_assert(std::is_same<pthread_key_t, std::uint32_t>::value,
              "On linux, expected pthread_key_t to be an uint32_t");
#elif defined(__APPLE__)
static_assert(std::is_same<pthread_key_t, unsigned long>::value,
              "On macOS, Expected pthread_key_t to be an unsigned long");
static_assert(sizeof(unsigned long) == 8, "Expected 64-bit unsigned long");
#else
# error Unsupported OS
#endif

#ifdef DEX_LIVE
#include <png.h>
#endif // DEX_LIVE

#ifdef DEX_CUDA
#include <cuda.h>
#endif // DEX_CUDA

extern "C" {

// XXX: Changes to this value might require additional changes to parameter attributes in LLVM
const int64_t alignment = 64;

char* malloc_dex(int64_t nbytes) {
  // reserves `alignment` bytes before the data region to store the size of the allocation
  int64_t nbytes_total = nbytes + alignment;
  char *ptr;
  if (posix_memalign(reinterpret_cast<void**>(&ptr), alignment, nbytes_total)) {
    fprintf(stderr, "Failed to allocate %ld bytes", (long)nbytes);
    std::abort();
  }
  *(reinterpret_cast<int64_t*>(ptr)) = nbytes;
  return ptr + alignment;
}

void free_dex(char* ptr) {
  free(ptr - alignment);
}

int64_t dex_allocation_size (char* ptr) {
  return *(reinterpret_cast<int64_t*>(ptr - alignment));
}

void* dex_pthread_key_create () {
  pthread_key_t* key_ptr = (pthread_key_t*) malloc(sizeof(pthread_key_t));
  // TODO(dougalm): add destructor. It's not urgent because we only call this once per process at the moment.
  pthread_key_create(key_ptr, NULL);
  return (void*) key_ptr;
}

void* fdopen_w(int fd) {
  return fdopen(fd, "w");
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

void showHex(char **resultPtr, char x) {
  auto p = reinterpret_cast<char*>(malloc_dex(100));  // TODO: something better!
  auto n = sprintf(p, "%02hhX", x);
  auto result1Ptr = reinterpret_cast<int32_t*>(resultPtr[0]);
  auto result2Ptr = reinterpret_cast<char**>(  resultPtr[1]);
  *result1Ptr = n;
  *result2Ptr = p;
}

void showFloat(char **resultPtr, float x) {
  auto p = reinterpret_cast<char*>(malloc_dex(100));  // TODO: something better!
  auto n = sprintf(p, "%.4f", x);
  auto result1Ptr = reinterpret_cast<int32_t*>(resultPtr[0]);
  auto result2Ptr = reinterpret_cast<char**>(  resultPtr[1]);
  *result1Ptr = n;
  *result2Ptr = p;
}

void showInt(char **resultPtr, int32_t x) {
  auto p = reinterpret_cast<char*>(malloc_dex(100));  // TODO: something better!
  auto n = sprintf(p, "%d", x);
  auto result1Ptr = reinterpret_cast<int32_t*>(resultPtr[0]);
  auto result2Ptr = reinterpret_cast<char**>(  resultPtr[1]);
  *result1Ptr = n;
  *result2Ptr = p;
}

void doubleVec(char **resultPtr, int32_t n, float* xs) {
  auto p1 = reinterpret_cast<float*>(malloc_dex(4 * n));
  auto p2 = reinterpret_cast<float*>(malloc_dex(4 * n));
  for (int i=0;i<n;++i) {
    p1[i] = xs[i] * 2;
    p2[i] = xs[i] * 3;
  }
  auto result1Ptr = reinterpret_cast<float**>(resultPtr[0]);
  auto result2Ptr = reinterpret_cast<float**>(resultPtr[1]);
  *result1Ptr = p1;
  *result2Ptr = p2;
}

void encodePNG(char **resultPtr, int8_t* pixels, int32_t width, int32_t height) {
  auto result1Ptr = reinterpret_cast<int32_t*>(resultPtr[0]);
  auto result2Ptr = reinterpret_cast<void**>(  resultPtr[1]);
#ifdef DEX_LIVE
  png_image img;
  memset(&img, 0, sizeof(img));
  img.version = PNG_IMAGE_VERSION;
  img.opaque = NULL;
  img.width = width;
  img.height = height;
  img.format = PNG_FORMAT_RGB;
  img.flags = 0;
  img.colormap_entries = 0;

  const int num_pixels = width * height;
  png_alloc_size_t num_bytes = 0;
  png_image_write_to_memory(&img, NULL, &num_bytes, 0, (void*)pixels, 0, NULL);
  void* out_buffer = malloc_dex(num_bytes);
  png_image_write_to_memory(&img, out_buffer, &num_bytes, 0, (void*)pixels, 0, NULL);

  *result1Ptr = num_bytes;
  *result2Ptr = out_buffer;
#else
  // It would be better to return a dummy empty PNG file, but this will have to do for now.
  *result1Ptr = 0;
  *result2Ptr = nullptr;
#endif // DEX_LIVE
}

// The string buffer size used for converting integer and floating-point types.
static constexpr int showStringBufferSize = 32;

int32_t appendTrailingDecimalDot(char* buffer, int32_t size) {
  bool needsdot = true;
  for (int32_t i = 0; i<size; i++) {
    auto c = *(buffer + i);
    if (c == '.' || isalpha(c)) {
      needsdot = false;
    }
  }
  if (needsdot) {
    *(buffer + size) = '.';
    size = size + 1;
  }
  return size;
}

// TODO: replace `showFloat32` with `showFloat32_internal` and so on
int32_t showFloat32_internal(char *resultPtr, float x) {
  // XXX: we use 2 digits fewer than the max as a hack to make quine tests less
  // sensitive to floating point behavior
  auto size = snprintf(resultPtr, showStringBufferSize, "%.*g", __FLT_DECIMAL_DIG__ - 2, x);
  return appendTrailingDecimalDot(resultPtr, size);
}

int32_t showFloat64_internal(char *resultPtr, double x) {
  auto size = snprintf(resultPtr, showStringBufferSize, "%.*g", __FLT_DECIMAL_DIG__ - 2, x);
  return appendTrailingDecimalDot(resultPtr, size);
}

int32_t showInt32_internal(char *resultPtr, int32_t x) {
  return snprintf(resultPtr, showStringBufferSize, "%" PRId32, x);}
int32_t showInt64_internal(char *resultPtr, int64_t x) {
  return snprintf(resultPtr, showStringBufferSize, "%" PRId64, x);}

int32_t showWord8_internal(char *resultPtr, uint8_t x) {
  return snprintf(resultPtr, showStringBufferSize, "0x%" PRIx8, x);}
int32_t showWord32_internal(char *resultPtr, uint32_t x) {
  return snprintf(resultPtr, showStringBufferSize, "0x%" PRIx32, x);}
int32_t showWord64_internal(char *resultPtr, uint64_t x) {
  return snprintf(resultPtr, showStringBufferSize, "0x%" PRIx64, x);}

void showNat32(char **resultPtr, uint32_t x) {
  auto buffer = reinterpret_cast<char *>(malloc_dex(showStringBufferSize));
  auto length = snprintf(buffer, showStringBufferSize, "%" PRId32, x);
  auto result1Ptr = reinterpret_cast<int32_t *>(resultPtr[0]);
  auto result2Ptr = reinterpret_cast<char **>(resultPtr[1]);
  *result1Ptr = length;
  *result2Ptr = buffer;
}

void showInt32(char **resultPtr, int32_t x) {
  auto buffer = reinterpret_cast<char *>(malloc_dex(showStringBufferSize));
  auto length = snprintf(buffer, showStringBufferSize, "%" PRId32, x);
  auto result1Ptr = reinterpret_cast<int32_t *>(resultPtr[0]);
  auto result2Ptr = reinterpret_cast<char **>(resultPtr[1]);
  *result1Ptr = length;
  *result2Ptr = buffer;
}

void showInt64(char **resultPtr, int64_t x) {
  auto buffer = reinterpret_cast<char *>(malloc_dex(showStringBufferSize));
  auto length = snprintf(buffer, showStringBufferSize, "%" PRId64, x);
  auto result1Ptr = reinterpret_cast<int32_t *>(resultPtr[0]);
  auto result2Ptr = reinterpret_cast<char **>(resultPtr[1]);
  *result1Ptr = length;
  *result2Ptr = buffer;
}

void showFloat32(char **resultPtr, float x) {
  auto buffer = reinterpret_cast<char *>(malloc_dex(showStringBufferSize));
  auto length =
      snprintf(buffer, showStringBufferSize, "%.*g", __FLT_DECIMAL_DIG__, x);
  auto result1Ptr = reinterpret_cast<int32_t *>(resultPtr[0]);
  auto result2Ptr = reinterpret_cast<char **>(resultPtr[1]);
  *result1Ptr = length;
  *result2Ptr = buffer;
}

void showFloat64(char **resultPtr, double x) {
  auto buffer = reinterpret_cast<char *>(malloc_dex(showStringBufferSize));
  auto length =
      snprintf(buffer, showStringBufferSize, "%.*g", __DBL_DECIMAL_DIG__, x);
  auto result1Ptr = reinterpret_cast<int32_t *>(resultPtr[0]);
  auto result2Ptr = reinterpret_cast<char **>(resultPtr[1]);
  *result1Ptr = length;
  *result2Ptr = buffer;
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


void dex_cuMemcpyDtoH(int64_t bytes, char* device_ptr, char* host_ptr) {
  CHECK(cuMemcpyDtoH, host_ptr, reinterpret_cast<CUdeviceptr>(device_ptr), bytes);
}

void dex_cuMemcpyHtoD(int64_t bytes, char* device_ptr, char* host_ptr) {
  CHECK(cuMemcpyHtoD, reinterpret_cast<CUdeviceptr>(device_ptr), host_ptr, bytes);
}

void dex_queryParallelismCUDA(const char* kernel_func, int64_t iters,
                              int32_t* numWorkgroups, int32_t* workgroupSize) {
  if (iters == 0) {
    *numWorkgroups = 0;
    *workgroupSize = 0;
    return;
  }
  // TODO: Use the occupancy calculator, or at least use a fixed number of blocks?
  const int64_t fixedWgSize = 1024;
  *workgroupSize = fixedWgSize;
  *numWorkgroups = std::min((iters + fixedWgSize - 1) / fixedWgSize, fixedWgSize);
}

void dex_loadKernelCUDA(const char* kernel_text, char** module_storage, char** kernel_storage) {
  if (*kernel_storage) { return; }
  CUmodule *module = reinterpret_cast<CUmodule*>(module_storage);
  CHECK(cuModuleLoadData, module, kernel_text);
  CUfunction *kernel = reinterpret_cast<CUfunction*>(kernel_storage);
  CHECK(cuModuleGetFunction, kernel, *module, "kernel");
}

void dex_unloadKernelCUDA(char** module_storage, char** kernel_storage) {
  CUmodule *module = reinterpret_cast<CUmodule*>(module_storage);
  CUfunction *kernel = reinterpret_cast<CUfunction*>(kernel_storage);
  CHECK(cuModuleUnload, *module);
  *module = nullptr;
  *kernel = nullptr;
}

void dex_cuLaunchKernel(char* kernel_func, int64_t iters, char** args) {
  if (iters == 0) return;
  CUfunction kernel = reinterpret_cast<CUfunction>(kernel_func);
  int32_t block_dim_x, grid_dim_x;
  dex_queryParallelismCUDA(kernel_func, iters, &grid_dim_x, &block_dim_x);
  CHECK(cuLaunchKernel, kernel,
                        grid_dim_x, 1, 1,               // grid size
                        block_dim_x, 1, 1,              // block size
                        0,                              // shared memory
                        CU_STREAM_LEGACY,               // stream
                        reinterpret_cast<void**>(args), // kernel arguments
                        nullptr);
}

char* dex_cuMemAlloc(int64_t size) {
  if (size == 0) return nullptr;
  CUdeviceptr ptr;
  CHECK(cuMemAllocAsync, &ptr, size, CU_STREAM_LEGACY);
  return reinterpret_cast<char*>(ptr);
}

void dex_cuMemFree(char* ptr) {
  if (!ptr) return;
  CHECK(cuMemFreeAsync, reinterpret_cast<CUdeviceptr>(ptr), CU_STREAM_LEGACY);
}

void dex_synchronizeCUDA() {
  CHECK(cuStreamSynchronize, CU_STREAM_LEGACY);
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

void dex_get_cuda_architecture(int device, char* arch) {
  int majorVersion, minorVersion;
  CUdevice dev;
  CHECK(cuInit, 0);
  CHECK(cuDeviceGet, &dev, device);
  CHECK(cuDeviceGetAttribute, &majorVersion, CU_DEVICE_ATTRIBUTE_COMPUTE_CAPABILITY_MAJOR, device);
  CHECK(cuDeviceGetAttribute, &minorVersion, CU_DEVICE_ATTRIBUTE_COMPUTE_CAPABILITY_MINOR, device);
  if (majorVersion > 9 || majorVersion < 0 || minorVersion > 9 || minorVersion < 0) {
    printf("Unsupported CUDA architecture version: %d.%d", majorVersion, minorVersion);
    std::abort();
  }
  // Cap CUDA architecture version at 7.5, the latest supported by LLVM 9
  if (majorVersion > 7 || (majorVersion == 7 && minorVersion > 5)) {
    majorVersion = 7;
    minorVersion = 5;
  }
  snprintf(arch, 6, "sm_%d%d", majorVersion, minorVersion);
}

#undef CHECK

#endif // DEX_CUDA

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
