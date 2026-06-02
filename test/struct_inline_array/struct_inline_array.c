#include "pal.h"

// Compare the two flavors of array-typed struct fields side-by-side.
//
// `_array int *a` — pointer-array field. The struct stores only the
// array handle; the storage lives externally. Its ownership is part of
// the auto-generated `__pred`.
//
// `int b[10]` — inline-array field. The storage is part of the struct's
// own bytes. The noeq record value carries the array's contents
// directly (as a `full_array_spec` refined to length 10), and the
// auto-generated `aux_raw_unfold` ties the ghost array handle
// `__b_1 s` to that spec via `array_pts_to_full`. This is why we are
// able to abstract `s->b` access behind a small user-level helper
// without ever mentioning the raw `array_pts_to` clause in the
// function specs.
struct mixed {
    _array int *a;
    int b[10];
    int c;
};

// --- Operations on the external `_array` field (by value) ------------

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
// chains three slprops: the struct's `aux_raw_unfolded` (what `s->b`
// access desugars to via `get_b`), the `pts_to` for the ghost ref to
// the array handle (treated uniformly with plain fields like `c`),
// and the `array_pts_to_full` over the handle itself. We existentially
// quantify over the handle so callers don't need to name it.
// Callers/callees only see `pts_to_b` in their specs.

_include_pulse(Mixed_helpers,
  [@@pulse_eager_unfold]
  let pts_to_b
        (s: ref Struct_mixed.struct_mixed)
        (p: perm)
        (v: full_array_spec Int32.t { array_spec_len v == 10 })
    : slprop
    =
      exists* (h: (a: array Int32.t { length a == 10 })).
        Struct_mixed.struct_mixed__aux_raw_unfolded s p **
        Pulse.Lib.Reference.pts_to (Struct_mixed.struct_mixed__b_1 s) #p h **
        array_pts_to_full h p v
)

int read_first_b(_plain struct mixed *s)
  _preserves(_inline_pulse(Mixed_helpers.pts_to_b $(s) $`p $`vb))
  _ensures(_inline_pulse(pure ($(return) == array_spec_idx $`vb 0)))
{
    return s->b[0];
}

void write_first_b(_plain struct mixed *s, int x)
  _requires(_inline_pulse(Mixed_helpers.pts_to_b $(s) 1.0R $`vb))
  _ensures(_inline_pulse(Mixed_helpers.pts_to_b $(s) 1.0R (array_spec_upd $`vb 0 $(x))))
{
    s->b[0] = x;
}
