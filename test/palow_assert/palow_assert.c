#include "pal.h"
#include <stdint.h>
#include <stddef.h>

// Assertions inside a body. A contract can name a pointee without touching
// memory, because it has a ghost binder for everything it owns. A body has no
// such binders, so an assertion about `*p` has to load `*p` first. These cases
// pin down that a load-then-assert really does prove what the C source claims.

void about_a_local(uint32_t x)
{
  uint32_t y = x;
  _assert(y == x);
}

void about_a_pointee(uint32_t *p)
  _requires(*p == 7)
{
  _assert(*p == 7);
}

// The assertion has to see the write that precedes it, which is what pins the
// `rewrites_to` in the read's postcondition.
void after_a_write(uint32_t *p)
{
  *p = 3;
  _assert(*p == 3);
}

// Both sides of a conjunction are loaded before the assertion; neither load may
// disturb the other's ownership.
void two_pointees(uint32_t *p, uint32_t *q)
  _requires(*p == 1 && *q == 2)
{
  _assert(*p == 1 && *q == 2);
}

// A comparison, so the assertion goes through the mathematical projection
// rather than through machine equality.
void an_ordering(uint32_t *p)
  _requires((_specint)*p < 10)
{
  _assert((_specint)*p < 10);
}

// An assertion about an element of an array parameter, which has to focus and
// unfocus exactly as a read does.
void about_an_element(uint32_t a[], size_t n)
  _requires(a._length == n && n > 0 && a[0] == 4)
  _preserves_value(a._length)
{
  _assert(a[0] == 4);
}
