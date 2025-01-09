// Copyright 2019 Google LLC
//
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file or at
// https://developers.google.com/open-source/licenses/bsd

#include <cctype>
#include <cstring>
#include <string>
#include <vector>
#include <cinttypes>
#include <cstdio>
#include <cstddef>
#include <cstdlib>
#include <type_traits>
#include <cstdint>

extern "C" {

float printfloat(float X) {
  fprintf(stderr, "%f\n", X);
  return 0;
}

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

// void* dex_pthread_key_create () {
//   pthread_key_t* key_ptr = (pthread_key_t*) malloc(sizeof(pthread_key_t));
//   // TODO(dougalm): add destructor. It's not urgent because we only call this once per process at the moment.
//   pthread_key_create(key_ptr, NULL);
//   return (void*) key_ptr;
// }

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

}
