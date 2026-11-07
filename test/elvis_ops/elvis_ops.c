#include "pal.h"
#include <stdint.h>
#include <stddef.h>

/* GNU `a ?: b` yields `a` when it is nonzero and `b` otherwise, evaluating
 * `a` only once. PAL keeps it as its own operator and emits it as a library
 * function (Pulse.Lib.C.GNU.Elvis.elvis_<type> a b). */

int32_t elvis_ops_int(int32_t a, int32_t b)
    _ensures(return == (a != 0 ? a : b)) {
  return a ?: b;
}

uint32_t elvis_ops_chain(uint32_t x, uint32_t y, uint32_t z)
    _ensures(return == (x != 0 ? x : (y != 0 ? y : z))) {
  return x ?: y ?: z;
}

int32_t elvis_ops_as_condition(int32_t flag, int32_t fallback)
    _ensures(return == ((flag != 0 ? flag : fallback) != 0 ? 1 : 0)) {
  if (flag ?: fallback) {
    return 1;
  }
  return 0;
}

/* The left operand is a call: it must run exactly once. */
int32_t next_slot(int32_t q)
    _requires(q < 1000)
    _ensures(return == q + 1) {
  return q + 1;
}

int32_t elvis_ops_effectful_left(int32_t q, int32_t fallback)
    _requires(q < 1000)
    _ensures(return == (q + 1 != 0 ? q + 1 : fallback)) {
  return next_slot(q) ?: fallback;
}

/* ptrdiff_t operands. */
ptrdiff_t elvis_ops_ptrdiff(ptrdiff_t d, ptrdiff_t e)
    _ensures(return == (d != 0 ? d : e)) {
  return d ?: e;
}

/* A `void *` is a `_core_ref`, nonzero when it is not null. */
void *elvis_ops_core_ref(void *ctx, void *fallback)
    _ensures(return == (ctx != NULL ? ctx : fallback)) {
  return ctx ?: fallback;
}

/* Plain pointers: the result is `a` unless `a` is null. */
int32_t elvis_ops_ref(int32_t *a, int32_t *b)
    _ensures(return == ((a != NULL ? a : b) == a)) {
  return (a ?: b) == a;
}

int32_t elvis_ops_arrayptr(_arrayptr int32_t *a, _arrayptr int32_t *b)
    _ensures(return == ((a != NULL ? a : b) == a)) {
  return (a ?: b) == a;
}
