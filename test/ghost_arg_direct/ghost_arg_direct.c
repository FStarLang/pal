#include "pal.h"
#include <stdint.h>

// Issue #356: `$witness` supplies the `_ghost_arg`s of a direct call.
_ghost_arg(uint32_t k)
void needs_k(uint32_t *p)
  _requires(*p == k)
  _ensures(*p == k + 1)
  _requires(k < 100)
{ *p = *p + 1; }
void caller(void)
{
  uint32_t x = 5;
  _ghost_stmt($witness (hide 5ul));
  needs_k(&x);
}

_ghost_arg(uint32_t lo) _ghost_arg(uint32_t hi)
void in_range(uint32_t *p)
  _requires(lo <= *p && *p <= hi)
  _ensures(*p == _old(*p))
  _ensures(lo <= *p && *p <= hi)
{ }

_ghost_arg(uint32_t a) _ghost_arg(uint32_t b) _ghost_arg(uint32_t c)
uint32_t sum3(void)
  _requires(a + b + c < 1000)
  _ensures(return == 0)
{ return 0; }

void caller2(void)
{
  uint32_t x = 7;
  _ghost_stmt($witness (hide (3ul, 9ul)));
  in_range(&x);
  _ghost_stmt($witness (hide (1ul, 2ul, 3ul)));
  uint32_t r = sum3();
}
