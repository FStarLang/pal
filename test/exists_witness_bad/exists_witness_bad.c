#include "pal.h"
#include <stddef.h>
#include <stdint.h>

/* The witness has to be a value of the bound variable's type: 256 is no
   `uint8_t`, so neither form of this claim holds. */
void out_of_range(void)
{
  _assert(_exists(uint8_t b = 256, (_specint)b == 256));
}
