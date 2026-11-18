#include "pal.h"
#include <stdint.h>

/* The result must satisfy its type's `_refine`. */

typedef _refine(this < 10) uint32_t small;

small f(void) { return 30; }
