/* Definitions for the `d_late_*` globals of extern_globals.c. This file sorts
 * after it, so PAL sees the `extern` declaration before the definition -- the
 * mirror of a_defs.c, which must give the same result. */

#include "pal.h"
#include <stdint.h>

const uint32_t d_late_const = 6;
