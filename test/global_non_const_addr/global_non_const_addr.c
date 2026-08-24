/* Test: taking the address of a global that is neither `const` nor `_pure`.
 *
 * NOT SUPPORTED YET -- this directory is expected to fail, and records the gap
 * rather than working around it. PAL rejects the global ("non-pure global
 * variables are not yet supported"), each `&g` then fails with "cannot produce
 * lvalue for g", and emission replaces the reads with `admit()`.
 *
 * The intent is that a mutable global should still get an address -- a single
 * fixed value, so pointer identity works -- but no `pts_to`, so its value
 * cannot be read or written. Taking an address does not confer purity.
 */

#include "pal.h"
#include <stdint.h>
#include <stdbool.h>

/* Neither `const` nor `_pure`, so PAL treats it as a mutable global. */
uint32_t g;

/* A pure pointer to a mutable object: the address never changes, the object
 * does. */
uint32_t *const p_to_g = &g;

/* Same address, but the pointer global is itself mutable. */
uint32_t *p_mut = &g;

/* 1.1 A pointer equals itself: the address of a global is one fixed address. */
bool same_addr(void) _ensures(return == true) {
  uint32_t *p = &g;
  uint32_t *q = &g;
  return p == q;
}

/* 2.1 A pure pointer global holds the mutable global's address. */
bool pure_ptr_to_mutable(void) _ensures(return == true) { return p_to_g == &g; }

/* 2.2 The mutable pointer global has an address of its own. */
bool mutable_ptr_addr(void) _ensures(return == true) {
  uint32_t **p = &p_mut;
  return p == &p_mut;
}
