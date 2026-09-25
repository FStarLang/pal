#include "pal.h"
#include <stdint.h>

/* Same C signature, different generated witnesses:
     read_value: (unit & int32_t)
     read_equal: (unit & (int32_t & int32_t))
   Both must be mapped to the unit witness required by apply_reader. */
_ghost_arg(int32_t v)
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(p) #1.0R $(v)))
_ensures(return == v)
int32_t read_value(_plain int32_t *p, int32_t expected)
{
    return *p;
}

_ghost_arg(int32_t v)
_ghost_arg(int32_t w)
_requires(_inline_pulse(pure ($(v) == $(w))))
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(p) #1.0R $(v)))
_ensures(return == w)
int32_t read_equal(_plain int32_t *p, int32_t expected)
{
    return *p;
}

_include_pulse(Weaken_spec,
  let dom : Type0 =
    (ref Typedef_int32_t.ty_int32_t & Typedef_int32_t.ty_int32_t)

  [@@pulse_eager_unfold]
  unfold let reader_pre (x: dom) (y: erased unit) : slprop =
    Pulse.Lib.Reference.pts_to (fst x) #1.0R (snd x)

  [@@pulse_eager_unfold]
  unfold let reader_post (x: dom) (y: erased unit)
    (r: Typedef_int32_t.ty_int32_t) : slprop =
    reader_pre x y ** pure (r == snd x)

  /* The common contract pins the pointee to the runtime expected argument.
     Each map reconstructs its implementation's ghost witness from it. */
  unfold let value_map (x: dom) (y: erased unit)
    : erased (unit & Typedef_int32_t.ty_int32_t) =
    hide ((), snd x)

  ghost fn value_wpre (x: dom) (y: erased unit)
    requires reader_pre x y
    ensures Pulse.Lib.C.FuncPtr.pre_of
      Funcptr_read_value.func_read_value__fp x (value_map x y)
  { () }

  ghost fn value_wpost (x: dom) (y: erased unit)
    (r: Typedef_int32_t.ty_int32_t)
    requires Pulse.Lib.C.FuncPtr.prevent_lifting
      (Pulse.Lib.C.FuncPtr.post_of
        Funcptr_read_value.func_read_value__fp x (value_map x y) r)
    ensures reader_post x y r
  { () }

  unfold let equal_map (x: dom) (y: erased unit)
    : erased (unit & (Typedef_int32_t.ty_int32_t & Typedef_int32_t.ty_int32_t)) =
    hide ((), (snd x, snd x))

  ghost fn equal_wpre (x: dom) (y: erased unit)
    requires reader_pre x y
    ensures Pulse.Lib.C.FuncPtr.pre_of
      Funcptr_read_equal.func_read_equal__fp x (equal_map x y)
  { () }

  ghost fn equal_wpost (x: dom) (y: erased unit)
    (r: Typedef_int32_t.ty_int32_t)
    requires Pulse.Lib.C.FuncPtr.prevent_lifting
      (Pulse.Lib.C.FuncPtr.post_of
        Funcptr_read_equal.func_read_equal__fp x (equal_map x y) r)
    ensures reader_post x y r
  { () }
)

/* Only the common validity contract is available here, not either
   implementation's original contract. */
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(p) #1.0R $(expected)))
_ensures(return == expected)
int32_t apply_reader(
    int32_t (*f)(_plain int32_t *, int32_t)
        _refine((_slprop) _inline_pulse(
            Pulse.Lib.C.FuncPtr.is_valid $(this) true
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
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_read_value.func_read_value__fp);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.weaken _ true true
      (Pulse.Lib.C.FuncPtr.pre_of Funcptr_read_value.func_read_value__fp)
      (Pulse.Lib.C.FuncPtr.post_of Funcptr_read_value.func_read_value__fp)
      Weaken_spec.reader_pre Weaken_spec.reader_post
      Weaken_spec.value_map Weaken_spec.value_wpre Weaken_spec.value_wpost);
    int32_t result = apply_reader(f, &value, 42);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
    return result;
}

_ensures(return == 17)
int32_t call_equal_witness(void)
{
    int32_t value = 17;
    int32_t (*f)(_plain int32_t *, int32_t) = read_equal;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_read_equal.func_read_equal__fp);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.weaken _ true true
      (Pulse.Lib.C.FuncPtr.pre_of Funcptr_read_equal.func_read_equal__fp)
      (Pulse.Lib.C.FuncPtr.post_of Funcptr_read_equal.func_read_equal__fp)
      Weaken_spec.reader_pre Weaken_spec.reader_post
      Weaken_spec.equal_map Weaken_spec.equal_wpre Weaken_spec.equal_wpost);
    int32_t result = apply_reader(f, &value, 17);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
    return result;
}
