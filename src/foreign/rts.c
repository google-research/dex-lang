#include <stdlib.h>
#include "HsFFI.h"

void dexInit() {
  int argc = 0;
  char *argv[] = { NULL };
  char **pargv = argv;

  hs_init(&argc, &pargv);
}

void dexFini() {
  hs_exit();
}
