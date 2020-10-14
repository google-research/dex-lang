#include <cstdint>
#include <cassert>
#include <iostream>
#include <array>

extern "C" {
extern int addi32(int32_t x, int32_t y, int32_t* result);
extern int addf32(float   x, float   y, float*   result);
}

int32_t add(int32_t x, int32_t y) {
  int32_t result = 0;
  assert(addi32(x, y, &result) == 0);
  return result;
}

float add(float x, float y) {
  float result = 0;
  assert(addf32(x, y, &result) == 0);
  return result;
}

int main() {
  std::array<int32_t, 5> i32_examples = {0, 1, 2, 3, 4};
  std::array<float, 5> f32_examples = {1.23, 4.12, 6.21, 9.64, 3.61};
  for (int32_t x : i32_examples) {
    for (int32_t y : i32_examples) {
      assert(add(x, y) == x + y);
    }
  }
  for (float x : f32_examples) {
    for (float y : f32_examples) {
      assert(add(x, y) == x + y);
    }
  }
  return EXIT_SUCCESS;
}
