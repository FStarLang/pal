/* Test: `void *` and its conversions to and from typed pointers.
 *
 * `void *` is translated to `Pulse.Lib.C.CoreRef.core_ref`, an axiomatized raw
 * C pointer, and the conversions become `ref_to_core` / `core_to_ref`.
 *
 * It was previously translated to `ref unit`. Since `unit` is a real inhabited
 * type, that made `void *` incompatible with every typed pointer -- the
 * opposite of what it means in C -- so any conversion was rejected by F*.
 *
 * Like any other `core_ref`, a `void *` carries no automatic ownership, which
 * is what a C `void *` conveys. Writing through one needs a hand-written
 * `pts_to`, as in `implicit` below.
 */

#include "pal.h"
#include <stdint.h>
#include <stddef.h>

struct counter {
  int32_t n;
};

/* A `void *` that is never converted, and one compared against NULL
 * (`core_is_null`). */

void take_void(void *p) { void *q = p; }

int32_t is_null(void *p) { return p == NULL; }

/* A `void *` struct field. It becomes a `core_ref` field and contributes no
 * ownership to the generated predicate. */
struct handle {
  void *raw;
  int32_t tag;
};

int32_t handle_tag(struct handle *h) { return h->tag; }

/* Erase a typed pointer to `void *` and recover it, as C code does to pass a
 * value through an untyped interface. The recovered pointer is the original
 * one, which `core_to_ref_to_core` proves. */
int32_t roundtrip(struct counter *c) _ensures(return == 1) {
  void *raw = (void *)c;
  struct counter *back = (struct counter *)raw;
  return back == c;
}

/* Write through a recovered pointer, using the implicit conversion C allows
 * from `void *`. The caller supplies ownership of the pointed-at counter by
 * hand, the way `core_ref` ownership is always supplied. */
void implicit(void *p)
  _requires(_inline_pulse(
    exists* (cv: $type(struct counter)).
      pts_to (Pulse.Lib.C.CoreRef.core_to_ref $type(struct counter) $(p)) cv))
  _ensures(_inline_pulse(
    exists* (cv: $type(struct counter)).
      pts_to (Pulse.Lib.C.CoreRef.core_to_ref $type(struct counter) $(p)) cv))
{
  struct counter *c = p;
  c->n = 0;
}
