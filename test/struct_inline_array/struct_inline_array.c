#include "pal.h"

// Compare the two flavors of array-typed struct fields side-by-side.
//
// `_array int *a` — pointer-array field. The struct stores only the
// array handle; the storage lives externally. Its ownership is part of
// the auto-generated `__pred`, so callers/callees use the same
// `a._length` / `a[i]` notation as `arrayptrs.c` (no exposure of
// internal preds).
//
// `int b[10]` — inline-array field. The storage is part of the struct's
// own bytes, so it is deliberately NOT tracked in the struct's `__pred`
// (it would double-own w.r.t. the value-level `pts_to`). Functions
// that touch `b` package the array's ownership through a small
// user-level helper slprop, in the same way `arrayptrs.c` abstracts
// `array_pts_to`/`arrayptr_pts_to` behind `is_slice`.
struct mixed {
    _array int *a;
    int b[10];
};

// --- Operations on the external `_array` field (by value) ------------
//
// Passing the struct by value gives callers/callees a clean, auto-
// generated `__pred`-based spec. The function body addresses the
// external array storage via the inline `a._length` and `a[i]`
// notation — no internal preds appear in the spec.

int read_first_a(struct mixed s)
  _requires(s.a._length >= 1)
  _preserves_value(s.a._length)
  _ensures(return == s.a[0])
{
    return s.a[0];
}

void write_first_a(struct mixed s, int x)
  _requires(s.a._length >= 1)
  _preserves_value(s.a._length)
  _ensures(s.a[0] == x)
{
    s.a[0] = x;
}

// --- Operations on the inline-array field (by reference) -------------
//
// User-level abstraction: "I have permission `p` to read/write
// `s->b`, and its current contents are described by the full array
// spec `v`". The helper bakes in the static length (10) and uses
// `array_pts_to_full` so callers don't need to assert init/mask
// preconditions for reads/writes at in-range indices. Internally it
// pairs the struct's `aux_raw_unfolded` slprop with `array_pts_to_full`
// on the ghost projection of `b`; the `aux_raw_unfolded` clause is
// what `s->b` access desugars to via `get_b` (and ties its permission
// to the array's permission `p`, which Pulse's unifier otherwise
// can't infer). Callers/callees only see `pts_to_b` in their specs.

_include_pulse(Mixed_helpers,
  [@@pulse_eager_unfold]
  let pts_to_b
        (s: ref Struct_mixed.struct_mixed)
        (p: perm)
        (v: full_array_spec Int32.t { array_spec_len v == 10 })
    : slprop
    =
      Struct_mixed.struct_mixed__aux_raw_unfolded s p **
      array_pts_to_full (Struct_mixed.struct_mixed__b_1 s) p v
)

int read_first_b(struct mixed *s)
  _preserves(_inline_pulse(Mixed_helpers.pts_to_b $(s) $`p $`vb))
  _ensures(_inline_pulse(pure ($(return) == array_spec_idx $`vb 0)))
{
    return s->b[0];
}

void write_first_b(struct mixed *s, int x)
  _requires(_inline_pulse(Mixed_helpers.pts_to_b $(s) 1.0R $`vb))
  _ensures(_inline_pulse(Mixed_helpers.pts_to_b $(s) 1.0R (array_spec_upd $`vb 0 $(x))))
{
    s->b[0] = x;
}
