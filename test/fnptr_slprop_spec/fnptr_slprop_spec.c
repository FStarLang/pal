#include "pal.h"
#include <stdint.h>

/* A function whose address is taken and whose `_requires`/`_ensures` is a
   genuine slprop, rather than a boolean, gets a `__fp` wrapper interface that
   does not typecheck: the annotation is emitted inside `pure (..)`, which is a
   `prop` position. */

struct ops {
	int32_t (*f)(_plain int32_t *q);
	int32_t (*g)(_plain int32_t *q);
	int32_t (*h)(_plain int32_t *q, int32_t n);
};

/* The two models spell "a `_plain int32_t *` that holds zero" differently --
   Palow's scalars are points-to predicates on an address, the old model's are
   Pulse references -- and they put the function-pointer library in different
   modules. Naming both through one shim keeps the rest of this file identical
   under either model: an F* module whose body is an `include` re-exports every
   name in it. */
#ifdef PALOW
_include_pulse(Sl_shim,
  include Pulse.Lib.C.Palow.FnPtr

  unfold let q_zero (q: Pulse.Lib.C.Palow.Ptr.ptr) : slprop =
    Pulse.Lib.C.Palow.CTypes.int32_t_pts_to q 1.0R 0l
)
#else
_include_pulse(Sl_shim,
  include Pulse.Lib.C.FuncPtr

  unfold let q_zero (q: ref FStar.Int32.t) : slprop =
    Pulse.Lib.Reference.pts_to q #1.0R 0l
)
#endif

/* An slprop in `_requires` and in `_ensures`. */
_requires(_inline_pulse(Sl_shim.q_zero $(q)))
_ensures(_inline_pulse(Sl_shim.q_zero $(q)))
int32_t impl_pre(_plain int32_t *q) { return 0; }

/* The same, written as one `_preserves`. */
_preserves(_inline_pulse(Sl_shim.q_zero $(q)))
int32_t impl_both(_plain int32_t *q) { return 0; }

/* Boolean and slprop annotations on the same function, on both sides of the
   contract. The two kinds have to end up in separate conjuncts: a boolean
   belongs under `pure`, an slprop next to it under `**`. The `_ensures` side
   also relates the two contracts as `_requires ==> _ensures`, which only the
   boolean halves can take part in. */
_requires(n > 0 && n < 100)
_ensures(return == n)
_preserves(_inline_pulse(Sl_shim.q_zero $(q)))
int32_t impl_mixed(_plain int32_t *q, int32_t n) { return n; }

static const struct ops o = { .f = impl_pre, .g = impl_both, .h = impl_mixed };

/* Calls through the pointers, so the wrappers are instantiated. */
_preserves(_inline_pulse(Sl_shim.q_zero $(q)))
int32_t call_via_o(_plain int32_t *q)
{
	_ghost_stmt(Sl_shim.of_fn_div_valid _ _ Funcptr_impl_both.func_impl_both__fp);
	_ghost_stmt(Global_o.acquire_var_o ());
	const struct ops *p = &o;
	return p->g(q);
	_ghost_stmt(Sl_shim.drop_is_valid _ _ _);
	_ghost_stmt(drop_ (exists* fr. pts_to Global_o.addr_var_o #fr _));
}

_requires(n > 0 && n < 100)
_ensures(return == n)
_preserves(_inline_pulse(Sl_shim.q_zero $(q)))
int32_t call_via_o_mixed(_plain int32_t *q, int32_t n)
{
	_ghost_stmt(Sl_shim.of_fn_div_valid _ _ Funcptr_impl_mixed.func_impl_mixed__fp);
	_ghost_stmt(Global_o.acquire_var_o ());
	const struct ops *p = &o;
	return p->h(q, n);
	_ghost_stmt(Sl_shim.drop_is_valid _ _ _);
	_ghost_stmt(drop_ (exists* fr. pts_to Global_o.addr_var_o #fr _));
}
