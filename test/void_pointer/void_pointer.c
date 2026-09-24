/* Test: `void *` and its conversions to and from typed pointers.
 *
 * `void *` translates to `Pulse.Lib.C.CoreRef.core_ref`, an axiomatized raw
 * pointer (previously `ref unit`, which wrongly made `void *` incompatible
 * with typed pointers). Like any `core_ref`, it carries no automatic
 * ownership; reading/writing through one needs a hand-written `pts_to`.
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

/* Erase to `void *` and recover it; `core_to_ref_to_core` proves it's the
 * same pointer. */
int32_t roundtrip(struct counter *c) _ensures(return == 1) {
  void *raw = (void *)c;
  struct counter *back = (struct counter *)raw;
  return back == c;
}

/* Write through a recovered pointer; the caller supplies ownership by hand.
 *
 * The two models spell the hand-written ownership differently, and the
 * difference is the point: PAL has to *convert* the `core_ref` to a typed
 * `ref` before it can state a points-to, while in Palow a `void *` is already
 * the same `ptr` a `struct counter *` is, so the predicate applies to it
 * directly. */
#ifdef PALOW
void implicit(void *p)
  _requires(_inline_pulse(
    exists* (cv: $type(struct counter)). struct_counter_pts_to $(p) 1.0R cv))
  _ensures(_inline_pulse(
    exists* (cv: $type(struct counter)). struct_counter_pts_to $(p) 1.0R cv))
#else
void implicit(void *p)
  _requires(_inline_pulse(
    exists* (cv: $type(struct counter)).
      pts_to (Pulse.Lib.C.CoreRef.core_to_ref $type(struct counter) $(p)) cv))
  _ensures(_inline_pulse(
    exists* (cv: $type(struct counter)).
      pts_to (Pulse.Lib.C.CoreRef.core_to_ref $type(struct counter) $(p)) cv))
#endif
{
  struct counter *c = p;
  c->n = 0;
}

/* Return `ip` or `sp` as `void *`, picked by `flag`. */
void *select_ptr(_Bool flag, int32_t *ip, struct counter *sp)
  _ensures(return == (flag ? (void *)ip : (void *)sp))
{
  if (flag) return ip;
  else return sp;
}

/* A client of `select_ptr`. `core_to_ref` grants no ownership, so each branch
 * moves ownership already held for `ip`/`sp` onto the recovered pointer to
 * read it, then moves it back so the caller keeps it unchanged. */
int32_t read_selected(_Bool flag, int32_t *ip, struct counter *sp)
  _ensures((!flag || return == *ip))
  _ensures((flag || return == sp->n))
{
  void *p = select_ptr(flag, ip, sp);
  if (flag) {
    int32_t *back = (int32_t *)p;
#ifdef PALOW
    _ghost_stmt(with v. rewrite (int32_t_pts_to $(ip) 1.0R v) as (int32_t_pts_to $(back) 1.0R v));
#else
    _ghost_stmt(with v. rewrite (pts_to $(ip) v) as (pts_to $(back) v));
#endif
    int32_t r = *back;
#ifdef PALOW
    _ghost_stmt(rewrite (int32_t_pts_to $(back) 1.0R $(r)) as (int32_t_pts_to $(ip) 1.0R $(r)));
#else
    _ghost_stmt(rewrite (pts_to $(back) $(r)) as (pts_to $(ip) $(r)));
#endif
    return r;
  } else {
    struct counter *back = (struct counter *)p;
#ifdef PALOW
    _ghost_stmt(with v. rewrite (struct_counter_pts_to $(sp) 1.0R v) as (struct_counter_pts_to $(back) 1.0R v));
#else
    _ghost_stmt(with v. rewrite (pts_to $(sp) v) as (pts_to $(back) v));
#endif
    struct counter sv = *back;
#ifdef PALOW
    _ghost_stmt(rewrite (struct_counter_pts_to $(back) 1.0R $(sv)) as (struct_counter_pts_to $(sp) 1.0R $(sv)));
#else
    _ghost_stmt(rewrite (pts_to $(back) $(sv)) as (pts_to $(sp) $(sv)));
#endif
    return sv.n;
  }
}

