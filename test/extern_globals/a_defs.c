/* Definitions for the `d_early_*` globals of extern_globals.c. This file sorts
 * before it, so PAL sees the definition before the `extern` declaration. */

#include "pal.h"
#include <stdint.h>

const uint32_t d_early_const = 5;

/* Declared `_pure` by the other file, not here: purity belongs to the object,
 * so the two declarations merge into one pure global. */
uint32_t d_early_pure = 7;

const uint32_t d_early_addressed = 8;
