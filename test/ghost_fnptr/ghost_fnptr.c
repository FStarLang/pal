#include "pal.h"
#include <stdint.h>

/* Taking the address of a function whose contract uses `_ghost_arg` emits a
   `__fp` wrapper interface that does not typecheck. The ghost argument gets no
   binder there, so its name is free, and because it is also unregistered it is
   lowered as a C-variable *read*, `(!var_v)`.

   The ordinary path gets the same contract right, so the two generated
   interfaces sit side by side:

     Func_impl_one.fsti (works)      Funcptr_impl_one.fsti (broken)
     (#var_v: erased ty_int32_t)     binder absent
     pts_to var_q #1.0R var_v        pts_to var_q #1.0R (!var_v)

   A function pointer also has nowhere to put a ghost argument at the call
   site: `call_div` takes the C argument and one erased witness, and the
   witness a plain call emits is `hide ()`. */

struct ops {
    int32_t (*f)(_plain int32_t *q);
    int32_t (*g)(_plain int32_t *q, _plain int32_t *r);
};

/* One ghost argument. It occurs inside an slprop, so it is recoverable by
   matching against the caller's context. */
_ghost_arg(int32_t v)
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(q) #1.0R $(v)))
int32_t impl_one(_plain int32_t *q) { return 0; }

/* Two ghost arguments, each pinned by its own slprop. */
_ghost_arg(int32_t v)
_ghost_arg(int32_t w)
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(q) #1.0R $(v)))
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(r) #1.0R $(w)))
int32_t impl_two(_plain int32_t *q, _plain int32_t *r) { return 0; }

static const struct ops o = { .f = impl_one, .g = impl_two };

/* Direct calls, for contrast: the ghost arguments are ordinary implicits and
   any number of them is already fine. */
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(q) #1.0R 0l))
int32_t call_direct_one(_plain int32_t *q)
{
    return impl_one(q);
}

_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(q) #1.0R 0l))
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(r) #1.0R 1l))
int32_t call_direct_two(_plain int32_t *q, _plain int32_t *r)
{
    return impl_two(q, r);
}

/* The same calls through the function pointers in `o`. Same shape as
   `call_via_addr_of_global_struct` in test/addr_global; the only difference is
   the `_ghost_arg` on the callees. */
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(q) #1.0R 0l))
int32_t call_via_o_one(_plain int32_t *q)
{
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_impl_one.func_impl_one__fp);
    _ghost_stmt(Global_o.acquire_var_o ());
    const struct ops *p = &o;
    return p->f(q);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
    _ghost_stmt(drop_ (exists* fr. pts_to Global_o.addr_var_o #fr _));
}

_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(q) #1.0R 0l))
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(r) #1.0R 1l))
int32_t call_via_o_two(_plain int32_t *q, _plain int32_t *r)
{
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_impl_two.func_impl_two__fp);
    _ghost_stmt(Global_o.acquire_var_o ());
    const struct ops *p = &o;
    return p->g(q, r);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
    _ghost_stmt(drop_ (exists* fr. pts_to Global_o.addr_var_o #fr _));
}
