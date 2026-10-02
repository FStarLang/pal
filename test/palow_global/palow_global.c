#include "pal.h"
#include <stdint.h>
#include <stdbool.h>

// Globals. Palow does not change the design PAL already settled on here,
// because that design is about *who owns a global*, and the answer does not
// depend on how memory is modelled.
//
// An immutable global -- `const`, or annotated `_pure` -- has a value that is
// fixed for the life of the program, so it is published as an F* constant and
// read with no ownership at all. The permission that would let something write
// through its address stays under an existential in the assumed `acquire`, so
// no client can ever gather a full one.
//
// A mutable global gets its address and nothing else. With no points-to ever
// produced for it, no permission to read or write through the address can be
// derived, so handing the address out is inert -- and reads of the global
// itself are refused.
//
// The addresses are assumed rather than allocated, because C gives a global a
// single fixed address for the whole run. That is exactly a constant of type
// `ptr`, which is why pointer identity between two mentions of `&g` holds
// definitionally rather than needing a lemma.

_pure bool flag = true;
_pure uint32_t limit = 100;
const int32_t offset = -3;

// A mutable global. Its address exists; its contents are not owned here.
uint32_t counter;

// Reading an immutable global needs no ownership, so an assertion about one is
// a pure fact with no load in front of it at all.
void constants_are_pure(void)
{
  _assert(flag == true);
  _assert(limit == 100);
  _assert(offset == -3);
}

// An immutable global reads as a value in an expression like any other.
uint32_t under_limit(uint32_t n)
  _requires(n <= 100)
  _ensures(return <= 100)
{
  if (n <= limit) {
    return n;
  }
  return limit;
}

// The address of a global is one fixed address, so two mentions of it are the
// same pointer.
bool same_addr(void)
  _ensures(return == true)
{
  uint32_t *p = &counter;
  uint32_t *q = &counter;
  return p == q;
}
