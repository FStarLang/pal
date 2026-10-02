#include "pal.h"
#include <stdint.h>

/* Acceptance test 2 from `palow.md`:
 *
 *     union { int x; struct { int y; int z; }; } a;
 *     a.x = 10;
 *     int b = a.y;
 *     _assert(b == 10);
 *
 * This is the program the old model cannot express at all. There a union's
 * members are different F* fields of different types, so storing through one
 * says nothing about loading through another, and the load is either refused
 * or answered with a value nothing relates to the store.
 *
 * Palow has one answer for both: the two names denote the *same bytes*. `a.x`
 * and `a.y` are both at offset 0 and both `uint32_t`, so the resource the
 * store leaves behind already is the resource the load needs, and the step
 * between them -- the generated `union_pun_u_pun_x__unnamed1_y` -- is a
 * rewrite of the address, not an axiom.
 *
 * Note what is *not* claimed. Bytes 4..8 have never been written, so there is
 * no `struct` value for the arm to hold and `a.z` is unreadable; a pun stated
 * at the whole member rather than at the field would be unsound here. Stating
 * it at the field is what makes this program provable and keeps `a.z` out of
 * reach -- which is exactly what C promises.
 *
 * The union is declared at file scope because a type declared inside a
 * function body is not translated; that is the only difference from the C in
 * `palow.md`.
 *
 * `palow-only`, because the whole point is a program the old model has no way
 * to verify. The C is still compiled, which is what keeps the annotations
 * honest as no-ops. */

union pun_u {
  uint32_t x;
  struct { uint32_t y; uint32_t z; };
};

uint32_t pun_local(void)
  _ensures(return == 10)
{
  union pun_u a;
  a.x = 10;
  uint32_t b = a.y;
  _assert(b == 10);
  return b;
}

/* The same thing through a pointer the caller owns, which is where the arm is
 * made live inside the function rather than being a fact about storage the
 * function allocated. */
uint32_t pun_param(union pun_u *a)
  _ensures(return == 7)
{
  a->x = 7;
  return a->y;
}

/* And with a value that is not a literal, so that nothing about the pun can be
 * coming from constant folding. */
uint32_t pun_value(union pun_u *a, uint32_t v)
  _ensures(return == _old(v))
{
  a->x = v;
  return a->y;
}
