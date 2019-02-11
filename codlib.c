#include "stdlib.h"

long doubleit(long x) {
  return x + x;
}

void* malloc_cod(long nbytes) {
  return malloc(nbytes);
}
