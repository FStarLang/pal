#include "bounds.h"

uint32_t seven(void)
  _ensures((_Bool) _inline_pulse(HeaderBounds.under 8 $(return)))
{
  return 7;
}
