#include "stdio.h"
#include "stdlib.h"

long doubleit(long x) {
  return x + x;
}

long* malloc_cod(long nbytes) {
  return malloc(nbytes);
}
