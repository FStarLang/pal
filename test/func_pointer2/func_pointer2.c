#include "pal.h"
#include <stdint.h>

/* Function pointers whose address is taken in an *initializer* rather than in
 * a statement. PAL emits the `Funcptr_<f>` module only for functions it sees
 * address-taken, and initializers were not scanned, so it would reference
 * `Funcptr_<f>` without emitting it -- no diagnostic, just F* `Error 72`.
 *
 * Each case uses its own `addN`, referenced from nowhere but the initializer
 * under test, so `Funcptr_addN` exists iff that initializer was traversed.
 * (`test/func_pointer` already address-takes `add` in a statement, which would
 * otherwise mask the bug.)
 */

typedef int32_t (*binop)(int32_t, int32_t);

int32_t add1(int32_t a, int32_t b)
    _requires(a > 0 && a < 100 && b > 0 && b < 100)
    _ensures(return == a + b)
{
    return a + b;
}

int32_t add2(int32_t a, int32_t b)
    _requires(a > 0 && a < 100 && b > 0 && b < 100)
    _ensures(return == a + b)
{
    return a + b;
}

int32_t add3(int32_t a, int32_t b)
    _requires(a > 0 && a < 100 && b > 0 && b < 100)
    _ensures(return == a + b)
{
    return a + b;
}

int32_t add4(int32_t a, int32_t b)
    _requires(a > 0 && a < 100 && b > 0 && b < 100)
    _ensures(return == a + b)
{
    return a + b;
}

int32_t add5(int32_t a, int32_t b)
    _requires(a > 0 && a < 100 && b > 0 && b < 100)
    _ensures(return == a + b)
{
    return a + b;
}

int32_t add6(int32_t a, int32_t b)
    _requires(a > 0 && a < 100 && b > 0 && b < 100)
    _ensures(return == a + b)
{
    return a + b;
}

/* (1) Bare function-pointer global: a plain `FnRef` initializer. */
_pure binop g_fp = add1;

int32_t call_via_global_fp(void)
    _ensures(return == 5)
{
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add1.func_add1__fp);
    return g_fp(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* (2) Struct global: `StructInit`. */
typedef struct {
    binop op;
} ops;

_pure ops g_ops = { .op = add2 };

int32_t call_via_global_struct(void)
    _ensures(return == 5)
{
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add2.func_add2__fp);
    return g_ops.op(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* (3) Union global: `UnionInit`. */
typedef union {
    binop op;
    int32_t tag;
} uops;

_pure uops g_uops = { .op = add3 };

int32_t call_via_global_union(void)
    _ensures(return == 5)
{
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add3.func_add3__fp);
    return g_uops.op(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* (4) Array global: `ArrayInit`, with two different functions so a walk that
 * visits only the first element still fails on `add5`. Declaration-only, which
 * suffices: the dangling reference is in the emitted `Global_g_arr` itself.
 * Calling through an element needs a helper-module lemma bridging
 * `array_spec_idx` to `of_fn_div` (see `test/global_array_tactic/helpers/`). */
_pure binop g_arr[2] = { add4, add5 };

/* (5) The same gap inside a function body: a local `StructInit` behind a
 * `let`, independent of globals. */
int32_t call_via_local_struct(void)
    _ensures(return == 5)
{
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add6.func_add6__fp);
    ops o = { .op = add6 };
    return o.op(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

