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

/* An slprop in `_requires` and in `_ensures`. */
_requires(_inline_pulse(Pulse.Lib.Reference.pts_to $(q) #1.0R 0l))
_ensures(_inline_pulse(Pulse.Lib.Reference.pts_to $(q) #1.0R 0l))
int32_t impl_pre(_plain int32_t *q) { return 0; }

/* The same, written as one `_preserves`. */
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(q) #1.0R 0l))
int32_t impl_both(_plain int32_t *q) { return 0; }

/* Boolean and slprop annotations on the same function, on both sides of the
   contract. The two kinds have to end up in separate conjuncts: a boolean
   belongs under `pure`, an slprop next to it under `**`. The `_ensures` side
   also relates the two contracts as `_requires ==> _ensures`, which only the
   boolean halves can take part in. */
_requires(n > 0 && n < 100)
_ensures(return == n)
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(q) #1.0R 0l))
int32_t impl_mixed(_plain int32_t *q, int32_t n) { return n; }

static const struct ops o = { .f = impl_pre, .g = impl_both, .h = impl_mixed };

/* Calls through the pointers, so the wrappers are instantiated. */
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(q) #1.0R 0l))
int32_t call_via_o(_plain int32_t *q)
{
	_ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_impl_both.func_impl_both__fp);
	_ghost_stmt(Global_o.acquire_var_o ());
	const struct ops *p = &o;
	return p->g(q);
	_ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
	_ghost_stmt(drop_ (exists* fr. pts_to Global_o.addr_var_o #fr _));
}

_requires(n > 0 && n < 100)
_ensures(return == n)
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(q) #1.0R 0l))
int32_t call_via_o_mixed(_plain int32_t *q, int32_t n)
{
	_ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_impl_mixed.func_impl_mixed__fp);
	_ghost_stmt(Global_o.acquire_var_o ());
	const struct ops *p = &o;
	return p->h(q, n);
	_ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
	_ghost_stmt(drop_ (exists* fr. pts_to Global_o.addr_var_o #fr _));
}
