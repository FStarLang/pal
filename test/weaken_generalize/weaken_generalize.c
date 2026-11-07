#include "pal.h"
#include <stdint.h>

/* Same C signature, different generated witnesses:
     read_value: (unit & int32_t)
     read_equal: (unit & (int32_t & int32_t))
   Both must be mapped to the unit witness required by apply_reader. */
_ghost_arg(int32_t v)
_preserves(_inline_pulse(int32_t_pts_to $(p) 1.0R $(v)))
_ensures(return == v)
int32_t read_value(_plain int32_t *p, int32_t expected)
{
    return *p;
}

_ghost_arg(int32_t v)
_ghost_arg(int32_t w)
_requires(_inline_pulse(pure ($(v) == $(w))))
_preserves(_inline_pulse(int32_t_pts_to $(p) 1.0R $(v)))
_ensures(return == w)
int32_t read_equal(_plain int32_t *p, int32_t expected)
{
    return *p;
}

/* The same generalisation in Palow. A pointer is an address, so the common
   domain is `(ptr & int32)` and the common precondition is the generated
   points-to at that address; the two implementations differ only in the ghost
   witness their own contracts quantify, which is what each map reconstructs. */
_include_pulse(Weaken_spec,
  include Pulse.Lib.C.Palow.FnPtr
  module I32 = FStar.Int32

  let dom : Type0 = (Pulse.Lib.C.Palow.Ptr.ptr & I32.t)

  [@@pulse_eager_unfold]
  unfold let reader_pre (x: dom) (y: erased unit) : slprop =
    Pulse.Lib.C.Palow.CTypes.int32_t_pts_to (fst x) 1.0R (snd x)

  [@@pulse_eager_unfold]
  unfold let reader_post (x: dom) (y: erased unit) (r: I32.t) : slprop =
    reader_pre x y ** pure (r == snd x)

  unfold let value_map (x: dom) (y: erased unit) : erased I32.t =
    hide (snd x)

  ghost fn value_wpre (x: dom) (y: erased unit)
    requires reader_pre x y
    ensures pre_of Funcptr_read_value.func_read_value__fp x (value_map x y)
  { () }

  ghost fn value_wpost (x: dom) (y: erased unit) (r: I32.t)
    requires post_of Funcptr_read_value.func_read_value__fp x (value_map x y) r
    ensures reader_post x y r
  { () }

  unfold let equal_map (x: dom) (y: erased unit) : erased (I32.t & I32.t) =
    hide (snd x, snd x)

  ghost fn equal_wpre (x: dom) (y: erased unit)
    requires reader_pre x y
    ensures pre_of Funcptr_read_equal.func_read_equal__fp x (equal_map x y)
  { () }

  ghost fn equal_wpost (x: dom) (y: erased unit) (r: I32.t)
    requires post_of Funcptr_read_equal.func_read_equal__fp x (equal_map x y) r
    ensures reader_post x y r
  { () }
)

/* Only the common validity contract is available here, not either
   implementation's original contract. */
_preserves(_inline_pulse(int32_t_pts_to $(p) 1.0R $(expected)))
_ensures(return == expected)
int32_t apply_reader(
    int32_t (*f)(_plain int32_t *, int32_t)
        _refine((_slprop) _inline_pulse(
            Pulse.Lib.C.Palow.FnPtr.is_valid $(this) true
                Weaken_spec.reader_pre Weaken_spec.reader_post)),
    _plain int32_t *p, int32_t expected)
{
    return f(p, expected);
}

_ensures(return == 42)
int32_t call_value_witness(void)
{
    int32_t value = 42;
    int32_t (*f)(_plain int32_t *, int32_t) = read_value;
    _ghost_stmt(Pulse.Lib.C.Palow.FnPtr.of_fn_div_valid _ _ Funcptr_read_value.func_read_value__fp);
    _ghost_stmt(Pulse.Lib.C.Palow.FnPtr.weaken _ true true
      (Pulse.Lib.C.Palow.FnPtr.pre_of Funcptr_read_value.func_read_value__fp)
      (Pulse.Lib.C.Palow.FnPtr.post_of Funcptr_read_value.func_read_value__fp)
      Weaken_spec.reader_pre Weaken_spec.reader_post
      Weaken_spec.value_map Weaken_spec.value_wpre Weaken_spec.value_wpost);
    int32_t result = apply_reader(f, &value, 42);
    _ghost_stmt(Pulse.Lib.C.Palow.FnPtr.drop_is_valid _ Weaken_spec.reader_pre Weaken_spec.reader_post);
    return result;
}

_ensures(return == 17)
int32_t call_equal_witness(void)
{
    int32_t value = 17;
    int32_t (*f)(_plain int32_t *, int32_t) = read_equal;
    _ghost_stmt(Pulse.Lib.C.Palow.FnPtr.of_fn_div_valid _ _ Funcptr_read_equal.func_read_equal__fp);
    _ghost_stmt(Pulse.Lib.C.Palow.FnPtr.weaken _ true true
      (Pulse.Lib.C.Palow.FnPtr.pre_of Funcptr_read_equal.func_read_equal__fp)
      (Pulse.Lib.C.Palow.FnPtr.post_of Funcptr_read_equal.func_read_equal__fp)
      Weaken_spec.reader_pre Weaken_spec.reader_post
      Weaken_spec.equal_map Weaken_spec.equal_wpre Weaken_spec.equal_wpost);
    int32_t result = apply_reader(f, &value, 17);
    _ghost_stmt(Pulse.Lib.C.Palow.FnPtr.drop_is_valid _ Weaken_spec.reader_pre Weaken_spec.reader_post);
    return result;
}
