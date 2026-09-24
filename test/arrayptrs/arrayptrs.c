#include "pal.h"
#include <stdlib.h>

// Create arrayptr via pointer arithmetic, then write through it
void write_via_ptr(_array int *a)
  _requires(a._length == 10)
  _preserves_value(a._length)
{
  _arrayptr int *p = a + 3;
  *p = 42;
  _ghost_stmt(arrayptr_drop $(p));
}

#ifdef PALOW
// Palow spelling of the same two helper modules. A Palow pointer *is* an
// address plus a provenance tag, so there is no separate `arrayptr_pts_to`
// claim to carry around and no `arrayptr_parent` to recover: being derived
// from the array is a property of the pointer itself. `claim` is therefore
// `emp` here, and the offsets that the old model reads off an `arrayptr` are
// computed from the addresses.
_include_pulse(Arrayptrs_include1,
  let unless_null (x: ptr) (p: slprop) : slprop =
    if is_null x then emp else p

  [@@pulse_intro]
  ghost fn intro_unless_null_nonnull (x: ptr) p
    requires p
    ensures unless_null x p
  {
    if is_null x {
      drop_ p;
      rewrite emp as unless_null x p;
    } else {
      rewrite p as unless_null x p;
    }
  }

  // Declared last so that the matcher reaches for it first: `is_null null` is
  // `ptr_eq null null` and `ptr_eq` is abstract, so the `if` in `unless_null`
  // does not reduce and a null return has no other way in.
  [@@pulse_intro]
  ghost fn intro_unless_null_null p
    ensures unless_null null p
  {
    rewrite emp as unless_null null p
  }

  ghost fn elim_unless_null_null (x: ptr) p
    requires unless_null x p
    requires pure (is_null x)
  {
    rewrite unless_null x p as emp
  }
  ghost fn elim_unless_null_nonnull (x: ptr) p
    requires unless_null x p
    requires pure (not (is_null x))
    ensures p
  {
    rewrite unless_null x p as p
  }
)

_include_pulse(Arrayptrs_include2,
  // The index a pointer into the array names. Well defined only under
  // `is_slice_prop`, which is where the alignment and the bound live.
  let off (q: ptr) (x: ptr) : GTot int = (addr_of q - addr_of x) / 4

  let span (lo hi: ptr) : GTot int = (addr_of hi - addr_of lo) / 4

  // A pointer claims nothing in Palow: its provenance travels with it.
  unfold
  let claim (q: ptr) (x: ptr) : slprop = emp

  unfold
  let is_slice_prop (lo hi x: ptr) (v: Seq.seq Int32.t) =
    prov_of lo == prov_of x
      /\ prov_of hi == prov_of x
      /\ addr_of x <= addr_of lo
      /\ addr_of lo <= addr_of hi
      /\ addr_of hi <= addr_of x + 4 * Seq.length v
      /\ (addr_of lo - addr_of x) % 4 == 0
      /\ (addr_of hi - addr_of x) % 4 == 0

  [@@pulse_eager_unfold]
  let is_slice (lo hi x: ptr) (p: perm) (v: Seq.seq Int32.t) =
    array_pts_to int32_t_repr 4 x p v **
    pure (is_slice_prop lo hi x v)

  unfold
  let found (r lo hi x: ptr) : slprop =
    pure (prov_of r == prov_of x
      /\ addr_of lo <= addr_of r
      /\ addr_of r < addr_of hi
      /\ (addr_of r - addr_of x) % 4 == 0)

  // Reading through the returned pointer.
  //
  // In this model the pointer carries no ownership -- `claim` is `emp`, and
  // an `_arrayptr` parameter owns nothing either -- so `*result` is a read of
  // an element of the parent array, and the caller has to say which one.
  // `found` says exactly enough to work that out: same provenance, inside the
  // bounds, on a multiple of the element size. The element is carved out of
  // the array, read, and put back; what is left over meanwhile is bundled
  // into `rest` so that each of the caller's ghost statements is one step.
  //
  // `idx`, `clamp` and `nth` are clamped so that they are total: an slprop's
  // arguments are typed with none of the surrounding `requires` in scope, so
  // `Seq.index` and `Seq.slice` cannot be written under a bound that only a
  // precondition establishes. Under `in_array` every clamp is the identity.
  let idx (r x: ptr) : GTot nat =
    if addr_of x <= addr_of r then (addr_of r - addr_of x) / 4 else 0
  let clamp (i n: nat) : nat = if i <= n then i else n
  let nth (v: Seq.seq Int32.t) (i: nat) : GTot Int32.t =
    if i < Seq.length v then Seq.index v i else 0l

  let rest (x r: ptr) (p: perm) (v: Seq.seq Int32.t) : slprop =
    array_pts_to int32_t_repr 4 x p (Seq.slice v 0 (clamp (idx r x) (Seq.length v))) **
    array_pts_to int32_t_repr 4 (r +! 4sz) p
                 (Seq.slice v (clamp (idx r x + 1) (Seq.length v)) (Seq.length v))

  let in_array (x r: ptr) (v: Seq.seq Int32.t) : prop =
    prov_of r == prov_of x /\ addr_of x <= addr_of r
/\ addr_of r + 4 <= addr_of x + 4 * Seq.length v
/\ (addr_of r - addr_of x) % 4 == 0

  ghost fn focus_at (x r: ptr) (#p: perm) (#v: Seq.seq Int32.t)
    requires array_pts_to int32_t_repr 4 x p v
    requires pure (in_array x r v)
    ensures int32_t_pts_to r p (nth v (idx r x))
    ensures rest x r p v
  {
    let off = SizeT.uint_to_t (addr_of r - addr_of x);
    let i = SizeT.uint_to_t (idx r x);
    array_focus int32_t_repr x 4sz i off;
    ptr_ext (x +! off) r;
    rewrite (elem_pts_to int32_t_repr (x +! off) p (Seq.index v (SizeT.v i)))
         as (elem_pts_to int32_t_repr r p (nth v (idx r x)));
    int32_t_of_elem r;
    rewrite (array_pts_to int32_t_repr 4 x p (Seq.slice v 0 (SizeT.v i)))
         as (array_pts_to int32_t_repr 4 x p
                          (Seq.slice v 0 (clamp (idx r x) (Seq.length v))));
    rewrite (array_pts_to int32_t_repr 4 ((x +! off) +! 4sz) p
                          (Seq.slice v (SizeT.v i + 1) (Seq.length v)))
         as (array_pts_to int32_t_repr 4 (r +! 4sz) p
                          (Seq.slice v (clamp (idx r x + 1) (Seq.length v)) (Seq.length v)));
    fold rest x r p v;
  }

  ghost fn unfocus_at (x r: ptr) (#p: perm) (#v: Seq.seq Int32.t)
    requires int32_t_pts_to r p (nth v (idx r x))
    requires rest x r p v
    requires pure (in_array x r v)
    ensures array_pts_to int32_t_repr 4 x p v
  {
    let off = SizeT.uint_to_t (addr_of r - addr_of x);
    let i = SizeT.uint_to_t (idx r x);
    unfold rest x r p v;
    ptr_ext (x +! off) r;
    int32_t_to_elem r;
    rewrite (elem_pts_to int32_t_repr r p (nth v (idx r x)))
         as (elem_pts_to int32_t_repr (x +! off) p (Seq.index v (SizeT.v i)));
    rewrite (array_pts_to int32_t_repr 4 x p
                          (Seq.slice v 0 (clamp (idx r x) (Seq.length v))))
         as (array_pts_to int32_t_repr 4 x p (Seq.slice v 0 (SizeT.v i)));
    rewrite (array_pts_to int32_t_repr 4 (r +! 4sz) p
                          (Seq.slice v (clamp (idx r x + 1) (Seq.length v)) (Seq.length v)))
         as (array_pts_to int32_t_repr 4 ((x +! off) +! 4sz) p
                          (Seq.slice v (SizeT.v i + 1) (Seq.length v)));
    array_unfocus int32_t_repr x 4sz i off;
    Seq.lemma_eq_intro (Seq.upd v (SizeT.v i) (Seq.index v (SizeT.v i))) v;
    rewrite (array_pts_to int32_t_repr 4 x p
                          (Seq.upd v (SizeT.v i) (Seq.index v (SizeT.v i))))
         as (array_pts_to int32_t_repr 4 x p v);
  }
)
#else
_include_pulse(Arrayptrs_include1,
  let unless_null #a (x: array a) (p: slprop) : slprop =
    if array_is_null x then emp else p

  [@@pulse_intro]
  ghost fn intro_unless_null_null (#a: Type0) p
    ensures unless_null #a array_null p
  {
    rewrite emp as unless_null #a array_null p
  }

  [@@pulse_intro]
  ghost fn intro_unless_null_nonnull (#a: Type0) (x: array a) p
    requires p
    ensures unless_null x p
  {
    if array_is_null x {
      drop_ p;
      assert rewrites_to x array_null;
    } else {
      rewrite p as unless_null x p;
    }
  }

  ghost fn elim_unless_null_null (#a: Type0) (x: array a) p
    requires unless_null x p
    requires pure (array_is_null x)
  {
    rewrite unless_null x p as emp
  }
  ghost fn elim_unless_null_nonnull (#a: Type0) (x: array a) p
    requires unless_null x p
    requires pure (not (array_is_null x))
    ensures p
  {
    rewrite unless_null x p as p
  }
)

_include_pulse(Arrayptrs_include2,
  unfold
  let is_slice_prop #a (lo hi: array a) (x: array a) (v: full_array_spec a) =
    base_of lo == base_of x /\ base_of hi == base_of x
      /\ offset_of x <= offset_of lo
      /\ offset_of lo <= offset_of hi
      /\ offset_of hi <= offset_of x + array_spec_len v
      /\ (forall (i: nat). offset_of lo <= i /\ i < offset_of hi ==>
        (array_spec_mask v (i - offset_of x) /\ array_spec_initd v (i - offset_of x)))

  [@@pulse_eager_unfold]
  let is_slice #a (lo hi: array a) (x: array a) p (v: full_array_spec a) =
    array_pts_to x p v **
    arrayptr_pts_to lo x ** arrayptr_pts_to hi x **
    pure (is_slice_prop lo hi x v)

  // Spelled once so that the contracts below read the same in both models.
  let off #a (q: array a) (x: array a) : GTot int = offset_of q
  let span #a (lo hi: array a) : GTot int = offset_of hi - offset_of lo
  unfold
  let claim #a (q: array a) (x: array a) : slprop = arrayptr_pts_to q x
  unfold
  let found #a (r lo hi: array a) (x: array a) : slprop =
    arrayptr_pts_to r x **
    pure (offset_of lo <= offset_of r /\ offset_of r < offset_of hi)
)
#endif

_arrayptr const int *binary_search(_arrayptr const int *lo, _arrayptr const int *hi, int target)
  _preserves(_inline_pulse(Arrayptrs_include2.is_slice $(lo) $(hi) $`arr $`p_arr $`v_arr))
  _requires((bool) _inline_pulse(Arrayptrs_include2.span $(lo) $(hi) < 100000))
  _ensures(_inline_pulse(Arrayptrs_include1.unless_null $(return)
    (Arrayptrs_include2.found $(return) $(lo) $(hi) $`arr)))
{
  while (lo < hi)
    _invariant(_live(lo))
    _invariant(_live(hi))
    _invariant(_inline_pulse(Arrayptrs_include2.claim $(lo) $`arr))
    _invariant(_inline_pulse(Arrayptrs_include2.claim $(hi) $`arr))
    _invariant((bool) _inline_pulse(Arrayptrs_include2.is_slice_prop $(lo) $(hi) $`arr $`v_arr))
#ifdef PALOW
    // Pulse's `old` is a marker the checker resolves against a dereference in
    // the precondition state; in Palow the invariant's pointers are pure
    // binders and there is nothing for it to resolve against, so the entry
    // values are named directly.
    _invariant((bool) _inline_pulse(Arrayptrs_include2.off $(_old(lo)) $`arr <= Arrayptrs_include2.off $(lo) $`arr && Arrayptrs_include2.off $(hi) $`arr <= Arrayptrs_include2.off $(_old(hi)) $`arr))
#else
    _invariant((bool) _inline_pulse(old (Arrayptrs_include2.off $(lo) $`arr) <= Arrayptrs_include2.off $(lo) $`arr && Arrayptrs_include2.off $(hi) $`arr <= old (Arrayptrs_include2.off $(hi) $`arr)))
#endif
#ifdef PALOW
    // The array itself. In the current model the loop reaches it through the
    // `arrayptr_pts_to` claims; in Palow the claims are empty and the
    // ownership has to be carried across the loop explicitly.
    _invariant(_inline_pulse(array_pts_to int32_t_repr 4 $`arr $`p_arr $`v_arr))
#endif
  {
      _arrayptr const int *mid = lo + (hi - lo) / 2;
      // Read once, so that the element is carved out of the array and put
      // back exactly once as well.
#ifdef PALOW
      _ghost_stmt(Arrayptrs_include2.focus_at $`arr $(mid));
#endif
      int probe = *mid;
#ifdef PALOW
      _ghost_stmt(Arrayptrs_include2.unfocus_at $`arr $(mid));
#endif
      if (probe == target)
        return mid;
      else if (probe < target)
        lo = mid + 1;
      else
        hi = mid;
  }
  // Which arm of `unless_null` the null return takes cannot be worked out by
  // unification: `is_null null` is `ptr_eq null null`, and `ptr_eq` is
  // abstract, so the `if` does not reduce. Say it.
  return NULL;
}

void use_binary_search(_array const int *arr, int target, size_t length)
  _requires(length == arr._length && length <= 10000)
{
  _arrayptr const int *lo = arr;
  _arrayptr const int *hi = arr + length;
  _arrayptr const int *result = binary_search(lo, hi, target);
  if (result == NULL) {
    _ghost_stmt(Arrayptrs_include1.elim_unless_null_null _ _);
  } else {
    _ghost_stmt(Arrayptrs_include1.elim_unless_null_nonnull _ _);
#ifdef PALOW
    _ghost_stmt(Arrayptrs_include2.focus_at $(arr) $(result));
    int val = *result;
    _ghost_stmt(Arrayptrs_include2.unfocus_at $(arr) $(result));
#else
    int val = *result;
#endif
  }
}
