/* With inline definitions enabled, glibc's <stdlib.h> defines `atoi` and
   friends inline, calling `strtol`, which it renames with `__REDIRECT` to
   `__isoc23_strtol` in C2X mode (glibc >= 2.38). A reference inside a system
   header's own definition is not the program's, and is not diagnosed. */
#define _GNU_SOURCE
#undef __NO_INLINE__
#define __OPTIMIZE__ 1
#include <stdlib.h>
#include "pal.h"

int identity(int x) _ensures(return == x) {
    return x;
}
