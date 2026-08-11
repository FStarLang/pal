#include "pal.h"
#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

/* Taking the address of a pure global (`_pure`, or `const` with an
 * initializer). A pure global is emitted as a plain F* value that reads with
 * no ownership, so any pointer to it must be read-only forever -- `&g` hands
 * out an existentially quantified fraction, which reads but never writes.
 *
 * Acquiring and releasing it is explicit: `acquire_var_g ()` before taking the
 * address, `drop_` after the `return`. See doc/pal_surface_syntax.md.
 */

_pure uint32_t g_const = 42;

/* Scalar global: take its address and read back through the pointer. */
uint32_t read_via_addr_of_global(void)
    _ensures(return == 42)
{
    _ghost_stmt(Global_g_const.acquire_var_g_const ());
    const uint32_t *p = &g_const;
    return *p;
    _ghost_stmt(drop_ (exists* q. pts_to Global_g_const.addr_var_g_const #q _));
}

/* A global's address is never NULL, via the emitted `addr_var_g_not_null`
 * axiom. This does not follow from the points-to alone. */
bool addr_of_global_is_not_null(void)
    _ensures(return == true)
{
    _ghost_stmt(Global_g_const.acquire_var_g_const ());
    const uint32_t *p = &g_const;
    return p != NULL;
    _ghost_stmt(drop_ (exists* q. pts_to Global_g_const.addr_var_g_const #q _));
}

/* A `const` global with an initializer is implicitly `_pure`. */
const uint32_t g_implicit = 7;
uint32_t read_via_addr_of_const_global(void)
    _ensures(return == 7)
{
    _ghost_stmt(Global_g_implicit.acquire_var_g_implicit ());
    const uint32_t *p = &g_implicit;
    return *p;
    _ghost_stmt(drop_ (exists* q. pts_to Global_g_implicit.addr_var_g_implicit #q _));
}

int32_t add(int32_t a, int32_t b)
    _requires(a > 0 && a < 100 && b > 0 && b < 100)
    _ensures(return == a + b)
{
    return a + b;
}

typedef struct {
    int32_t (*op)(int32_t, int32_t);
} ops;

_pure ops g_ops = { .op = add };

/* Struct global: take its address and call through its function-pointer
 * field. */
int32_t call_via_addr_of_global_struct(void)
    _ensures(return == 5)
{
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    _ghost_stmt(Global_g_ops.acquire_var_g_ops ());
    const ops *p = &g_ops;
    return p->op(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
    _ghost_stmt(drop_ (exists* q. pts_to Global_g_ops.addr_var_g_ops #q _));
}

