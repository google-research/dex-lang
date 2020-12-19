#include <cstdint>
#include <cassert>
#include <iostream>
#include <array>

extern "C" {
extern int addVecF32(int32_t n, float* x, float* y, float* result);
}

template<size_t N>
void addArrays(std::array<float, N>& x, std::array<float, N>& y, std::array<float, N>& z) {
  assert(addVecF32(N, x.data(), y.data(), z.data()) == 0);
}

int main() {
  std::array<float, 5> x = {0, 1, 2, 3, 4};
  std::array<float, 5> y = {1.23, 4.12, 6.21, 9.64, 3.61};
  std::array<float, 5> z;
  addArrays(x, y, z);
  for (size_t i = 0; i < x.size(); ++i) {
    assert(z[i] == x[i] + y[i]);
  }
  return EXIT_SUCCESS;
}

