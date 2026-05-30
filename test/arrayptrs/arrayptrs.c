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
)

_arrayptr const int *binary_search(_arrayptr const int *lo, _arrayptr const int *hi, int target)
  _preserves(_inline_pulse(Arrayptrs_include2.is_slice $(lo) $(hi) $`arr $`p_arr $`v_arr))
  _requires((bool) _inline_pulse(offset_of $(hi) - offset_of $(lo) < 100000))
  _ensures(_inline_pulse(Arrayptrs_include1.unless_null $(return)
    (arrayptr_pts_to $(return) (arrayptr_parent $(lo)) **
      pure (offset_of $(lo) <= offset_of $(return) /\ offset_of $(return) < offset_of $(hi)))))
{
  while (lo < hi)
    _invariant(_live(lo))
    _invariant(_live(hi))
    _invariant(_inline_pulse(arrayptr_pts_to $(lo) (old <| arrayptr_parent $(lo))))
    _invariant(_inline_pulse(arrayptr_pts_to $(hi) (old <| arrayptr_parent $(hi))))
    _invariant((bool) _inline_pulse(Arrayptrs_include2.is_slice_prop $(lo) $(hi) $`arr $`v_arr))
    _invariant((bool) _inline_pulse(old (offset_of $(lo)) <= offset_of $(lo) && offset_of $(hi) <= old (offset_of $(hi))))
  {
      const int *mid = lo + (hi - lo) / 2;
      if (*mid == target)
        return mid;
      else if (*mid < target)
        lo = mid + 1;
      else
        hi = mid;
  }
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
    int val = *result;
  }
}
