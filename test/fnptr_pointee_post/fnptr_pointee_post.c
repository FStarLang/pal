#include "pal.h"
#include <stdint.h>

/* Regression for https://github.com/FStarLang/pal/issues/279.
   Indirect callers must retain pointee postconditions: the post's PRE guard
   and _old use initial values, while ordinary reads use post-state values.
   Every contract is positive; checking wrappers alone is not sufficient. */

/* Direct-call control for a relational pointee postcondition. */
void inc_direct(int32_t *p)
    _requires(*p < 100)
    _ensures(*p == _old(*p) + 1)
{
    *p = *p + 1;
}

_requires(*q < 100)
_ensures(*q == _old(*q) + 1)
void call_direct(int32_t *q)
{
    inc_direct(q);
}

/* Scalar argument and return-value control. */
_requires(x > 0 && x < 100 && y > 0 && y < 100)
_ensures(return == x + y)
int32_t add(int32_t x, int32_t y)
{
    return x + y;
}

_ensures(return == 5)
int32_t call_add(void)
{
    int32_t (*f)(int32_t, int32_t) = add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return f(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Owned-pointer control without a pointee postcondition. */
_ensures(return == 7)
int32_t peek(int32_t *p)
{
    return 7;
}

_ensures(return == 7)
int32_t call_peek(int32_t *p)
{
    int32_t (*f)(int32_t *) = peek;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_peek.func_peek__fp);
    return f(p);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Non-relational post: re-reading PRE after mutation would lose the bound. */

void inc2(int32_t *p)
    _requires(*p < 100)
    _ensures(*p < 101)
{
    *p = *p + 1;
}

_requires(*q < 100)
_ensures(*q < 101)
void call_indirect_norel(int32_t *q)
{
    void (*f)(int32_t *) = inc2;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_inc2.func_inc2__fp);
    f(q);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Relational post through a local function pointer. */

void inc(int32_t *p)
    _requires(*p < 100)
    _ensures(*p == _old(*p) + 1)
{
    *p = *p + 1;
}

_requires(*q < 100)
_ensures(*q == _old(*q) + 1)
void call_indirect_old(int32_t *q)
{
    void (*f)(int32_t *) = inc;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_inc.func_inc__fp);
    f(q);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* The same contract via callback-parameter validity and witness inference. */

_requires(*p < 100)
_ensures(*p == _old(*p) + 1)
void apply_inc(void (*op)(int32_t *)
                   _refine((_slprop) _inline_pulse(
                       Pulse.Lib.C.FuncPtr.is_valid $(this) true
                           (Pulse.Lib.C.FuncPtr.pre_of Funcptr_inc.func_inc__fp)
                           (Pulse.Lib.C.FuncPtr.post_of Funcptr_inc.func_inc__fp))),
               int32_t *p)
{
    op(p);
}

/* Combined regression: ghosts, owned state, a refined struct with a __spec
   companion, and _old through a global callback table. Keep call_kitchen last
   so acceptance includes its proof, not merely the wrapper interface. */

/* The pointer field gives `dep` a `__spec` companion; the refinement rides
   along in `struct_dep__pred`. */
struct _refine(this.x > 0) dep {
    int32_t x;
    int32_t *y;
};

/* Multiple snapshots after a struct companion, a nested pointer read, and
   compound _old arithmetic. The total route must infer the same witness API.
   Both pointees change, so substituting current values cannot prove this.
   A transparent rvalue antiquote must still compose with snapshots. */
_total
_requires(**p > 0 && **p < 100 && *q > 0 && *q < 100)
_ensures(**p == _old(**p + *q))
_ensures(*q == _old((int32_t)_inline_pulse($(*q))) + 2)
_ensures(return == _old(d->x))
int32_t combine(struct dep *d, int32_t **p, int32_t *q)
{
    **p = **p + *q;
    *q = *q + 2;
    return d->x;
}

_total
_requires(**p > 0 && **p < 100 && *q > 0 && *q < 100)
_ensures(**p == _old(**p + *q))
_ensures(*q == _old((int32_t)_inline_pulse($(*q))) + 2)
_ensures(return == _old(d->x))
int32_t call_combine(struct dep *d, int32_t **p, int32_t *q)
{
    int32_t (*f)(struct dep *, int32_t **, int32_t *) = combine;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid _ _ Funcptr_combine.func_combine__fp);
    return f(d, p, q);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

_ghost_arg(int32_t v)
_requires(*a > 0 && *a < 100)
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(q) #1.0R $(v)))
_ensures(*a == _old(*a) + 1)
int32_t impl_kitchen(int32_t *a, _plain int32_t *q, struct dep *d)
{
    *a = *a + 1;
    return d->x;
}

struct ops {
    int32_t (*k)(int32_t *a, _plain int32_t *q, struct dep *d);
};

static const struct ops o = {.k = impl_kitchen};

/* Validity comes from `of_fn_div_valid`, so the field carries no `_refine`
   and needs no weakened contract: the ghost `v` is pinned by matching this
   caller's `_preserves` against the callee's. The declared type of `k` says
   nothing about ghost arity -- the witness is inferred at the call site. */
_ghost_arg(int32_t v)
_requires(*a > 0 && *a < 100)
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(q) #1.0R $(v)))
_ensures(*a == _old(*a) + 1)
int32_t call_kitchen(int32_t *a, _plain int32_t *q, struct dep *d)
{
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_impl_kitchen.func_impl_kitchen__fp);
    _ghost_stmt(Global_o.acquire_var_o ());
    const struct ops *p = &o;
    return p->k(a, q, d);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
    _ghost_stmt(drop_ (exists* fr. pts_to Global_o.addr_var_o #fr _));
}
