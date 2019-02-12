#include "stdio.h"
#include "stdlib.h"
#include <string.h>

long doubleit(long x) {
  return x + x;
}

char* malloc_cod(long nbytes) {
  return malloc(nbytes);
}

void memcpy_cod(char* dest, const char* src, long nbytes) {
  memcpy(dest, src, nbytes);
}
