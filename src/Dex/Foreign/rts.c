#include <stdlib.h>
#include <stddef.h>
#include <string.h>
#include "HsFFI.h"

void dexInit() {
  int argc = 4;
  char *argv[] = { "+RTS", "-I0", "-A16m", "-RTS", NULL };
  char **pargv = argv;

  hs_init(&argc, &pargv);
}

void dexFini() {
  hs_exit();
}

__thread char dex_err_storage[2048];

const char* dexGetError() {
  return dex_err_storage;
}

void _internal_dexSetError(char* new_err, int64_t len) {
  if (len > 2048) len = 2048;
  memcpy(dex_err_storage, new_err, len);
  dex_err_storage[2047] = 0;
}

typedef int64_t (*dex_xla_f)(void*, void**);
void dexXLACPUTrampoline(void* out, void** in) {
  dex_xla_f f = *((dex_xla_f*)(*in));
  f(out, in + 1);
}
