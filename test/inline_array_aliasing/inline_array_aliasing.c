#include "pal.h"

// Regression test for an inline-array rvalue emission bug.
// In C, an inline-array field in any rvalue context decays to a
// pointer; PAL used to wrap the handle in `array_read_all`, producing
// `array_spec T` instead of `array T` and tripping F* Error 189.
// The fix routes every rvalue through `to_rvalue_decayed`
// (src/pass/emit.rs), which yields the bare handle.

struct mixed {
#ifdef PALOW
    // Palow: `p` is a bare address here. The whole point of the struct is that
    // `p` may be made to alias the inline buffer, and a pointer that owns an
    // extent cannot be aimed at storage the same object already owns -- the
    // deep predicate would claim the inline array twice. The old model says
    // the same thing by writing a custom invariant instead of the generated
    // one; see the typedef below.
    int *_plain p;
#else
    _array int *p;
#endif
    int inline_buf[8];
};

// Custom invariant for `struct mixed *`. We expose the whole-struct
// value `vx` as a `_refine_value` projection — Pulse's prover
// auto-applies the struct's `aux_raw_unfold` lemma (tagged
// `[@@pulse_intro]` in the emitted F*) at every field access to
// expose per-field `pts_to`/`array_pts_to` as needed. Writes to
// `s->p` just rebind the `vp` slot of `vx`. No aliasing claim is
// baked into the invariant.
_type(struct_mixed_val, Struct_mixed.struct_mixed)

#ifdef PALOW
// Palow's struct points-to is already the separating conjunction of the
// fields', so the invariant the old model has to write by hand *is* the
// generated predicate at full permission. Writing it again on a `_plain`
// pointer would grant the same ownership twice and, worse, hide the pointee
// from every contract -- `_plain` says "this is a bare address". So the
// typedef is an ordinary pointer here and the invariant is the default one.
typedef struct mixed *aliased_ptr;
#else
_refine_value(struct_mixed_val vx, _inline_pulse(
    Pulse.Lib.Reference.pts_to $(this) $(vx)
))
_plain
typedef struct mixed *aliased_ptr;
#endif

// (1) Sibling-field assign `s->p = s->inline_buf;`. The post asserts
// that `p` now aliases the inline-buf field.
#ifdef PALOW
// The same claim without naming the invariant's binder, which the front end
// only puts in scope inside the refinement itself: in C the two field reads
// already say it, once the inline array is spelled as the address of its
// first element so that the two sides have the same type. Palow cannot yet state a contract that reads a field
// through a pointer, so this is dropped and counted rather than weakened in
// silence.
void alias_to_own(aliased_ptr s)
  _ensures(s->p == &s->inline_buf[0])
{
    s->p = s->inline_buf;
}
#else
void alias_to_own(aliased_ptr s)
  _ensures(_inline_pulse(pure (
      eq2 #(array Int32.t)
          (!(Struct_mixed.struct_mixed__p_1 $(s)))
          (Struct_mixed.struct_mixed__inline_buf_1 $(s))
  )))
{
    s->p = s->inline_buf;
}
#endif

// (2) Assignment RHS to a local pointer.
void alias_to_local(aliased_ptr s)
{
    _array int *q;
    q = s->inline_buf;
}

// (3) Function-call argument: the decayed handle is passed across a
// call.
int read_first(_array int *p)
  _requires(p._length >= 1)
  _preserves_value(p._length)
  _ensures(return == p[0])
{
    return p[0];
}

int pass_inline(aliased_ptr s)
  _ensures(return == s->inline_buf[0])
{
    int r = read_first(s->inline_buf);
    return r;
}

// (4) Spec contexts (`_requires` / `_ensures`) and `_inline_pulse`
// rvalue antiquotation `$(...)`. `array_is_null` takes the bare
// handle.
#ifdef PALOW
// An inline array's handle is the address of the field, so "not null" is a
// fact about that address rather than about an array handle.
void check_inline(aliased_ptr s)
  _requires((bool) _inline_pulse(not (is_null ($(s) +! Struct_mixed.struct_mixed_offsetof_inline_buf))))
  _ensures((bool) _inline_pulse(not (is_null ($(s) +! Struct_mixed.struct_mixed_offsetof_inline_buf))))
{
}
#else
void check_inline(aliased_ptr s)
  _requires((bool) _inline_pulse(not (array_is_null $(s->inline_buf))))
  _ensures((bool) _inline_pulse(not (array_is_null $(s->inline_buf))))
{
}
#endif
