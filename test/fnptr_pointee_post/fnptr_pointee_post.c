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
    return f(2, 3);
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
    return f(p);
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
    f(q);
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
    f(q);
}

/* The same contract via callback-parameter validity and witness inference. */

_requires(*p < 100)
_ensures(*p == _old(*p) + 1)
void apply_inc(void (*op)(int32_t *)
                   _refine((_slprop) _inline_pulse(
                       Pulse.Lib.C.Palow.FnPtr.is_valid $(this) true
                           (Pulse.Lib.C.Palow.FnPtr.pre_of Funcptr_inc.func_inc__fp)
                           (Pulse.Lib.C.Palow.FnPtr.post_of Funcptr_inc.func_inc__fp))),
               int32_t *p)
{
    op(p);
}

/* Combined regression: ghosts, owned state, a refined struct with a __spec
   companion, and _old through a global callback table. Keep call_kitchen last
   so acceptance includes its proof, not merely the wrapper interface. */

/* A refined struct with a pointer field, read in a postcondition. */
struct _refine(this.x > 0) dep {
    int32_t x;
    int32_t *y;
};

/* Multiple snapshots after a struct, compound _old arithmetic, and a
   `_total` target. Both pointees change, so substituting current values
   cannot prove this. A transparent rvalue antiquote must still compose with
   snapshots. */
_total
_requires(*p > 0 && *p < 100 && *q > 0 && *q < 100)
_ensures(*p == _old(*p + *q))
_ensures(*q == _old((int32_t)_inline_pulse($(*q))) + 2)
_ensures(return == _old(d->x))
int32_t combine(struct dep *d, int32_t *p, int32_t *q)
{
    *p = *p + *q;
    *q = *q + 2;
    return d->x;
}

_total
_requires(*p > 0 && *p < 100 && *q > 0 && *q < 100)
_ensures(*p == _old(*p + *q))
_ensures(*q == _old((int32_t)_inline_pulse($(*q))) + 2)
_ensures(return == _old(d->x))
int32_t call_combine(struct dep *d, int32_t *p, int32_t *q)
{
    int32_t (*f)(struct dep *, int32_t *, int32_t *) = combine;
    return f(d, p, q);
}

/* Not supported: the same through a nested pointer read (`**p`). Palow
   refuses a contract that dereferences a computed pointer -- `*p` is a value
   read from memory, and nothing in the contract owns what it points to --
   so `combine2` and, through it, `call_combine2` are not translated:
     error: `Func_combine2`: its contract is weakened: a contract that
            dereferences a computed pointer */
#if 0
_total
_requires(**p > 0 && **p < 100 && *q > 0 && *q < 100)
_ensures(**p == _old(**p + *q))
_ensures(return == _old(d->x))
int32_t combine2(struct dep *d, int32_t **p, int32_t *q)
{
    **p = **p + *q;
    return d->x;
}

_total
_requires(**p > 0 && **p < 100 && *q > 0 && *q < 100)
_ensures(**p == _old(**p + *q))
_ensures(return == _old(d->x))
int32_t call_combine2(struct dep *d, int32_t **p, int32_t *q)
{
    int32_t (*f)(struct dep *, int32_t **, int32_t *) = combine2;
    return f(d, p, q);
}
#endif

_ghost_arg(int32_t v)
_requires(*a > 0 && *a < 100)
_preserves(_inline_pulse(Pulse.Lib.C.Palow.CTypes.int32_t_pts_to $(q) 1.0R $(v)))
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

/* Validity comes from the table's known initializer, so the field carries no
   `_refine` and needs no weakened contract: the ghost `v` is pinned by
   matching this caller's `_preserves` against the callee's. The declared type of `k` says
   nothing about ghost arity -- the witness is inferred at the call site. */
_ghost_arg(int32_t v)
_requires(*a > 0 && *a < 100)
_preserves(_inline_pulse(Pulse.Lib.C.Palow.CTypes.int32_t_pts_to $(q) 1.0R $(v)))
_ensures(*a == _old(*a) + 1)
int32_t call_kitchen(int32_t *a, _plain int32_t *q, struct dep *d)
{
    const struct ops *p = &o;
    return p->k(a, q, d);
}
