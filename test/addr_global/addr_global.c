#include "pal.h"
#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

/* Taking the address of a pure global variable.
 *
 * A global is pure if it is annotated `_pure`, or if it is `const` with an
 * initializer (implicit). Either way it is emitted as a plain top-level F*
 * value (`var_g`) and every PAL-generated read of it is *ownership-free* -- the read simply
 * evaluates to `var_g` with nothing in the `requires`. That model is only
 * sound if any pointer PAL hands out to a global is READ-ONLY forever: a
 * writable alias would let a callee store a different value while
 * PAL-emitted reads still evaluate to the spec value, which proves `False`.
 *
 * So alongside `var_g`, PAL emits an address `addr_var_g : ref ty` and a
 * ghost `acquire_var_g ()` yielding `Pulse.Lib.C.RefRo.pts_to_ro`, i.e.
 * `exists* p. pts_to addr_var_g #p var_g`. The fraction stays existential:
 * reads typecheck, writes (which need `1.0R`) do not, and the address may be
 * taken any number of times.
 *
 * `&g` itself is just the address. Acquiring and releasing the ownership is
 * explicit, via `_ghost_stmt`: call `acquire_var_g ()` before taking the
 * address, and `drop_ro addr_var_g` after the `return` (a
 * ghost statement after `return` runs with the returned value already bound,
 * which is required here -- the returned expression may still read through
 * the pointer). This is the same discipline the function-pointer cases use
 * with `of_fn_div_valid` / `drop_is_valid`. Omitting either annotation is a
 * verification error, never unsoundness. `drop_ro` needs its ref argument
 * spelled out: `drop_ro _` cannot be inferred, because the local holding the
 * address is a second `pts_to` in scope.
 *
 * Array globals are deliberately out of scope (they have no pointer path at
 * all today), as are non-pure globals.
 *
 * The cases below are a `_pure` scalar global, an implicitly-pure `const`
 * scalar global, the non-nullness of a global's address, and a struct global
 * holding a function pointer that is called through the obtained pointer.
 */

_pure uint32_t g_const = 42;

/* Take the address of a global scalar, store the pointer, and read the
 * value back through it. */
uint32_t read_via_addr_of_global(void)
    _ensures(return == 42)
{
    _ghost_stmt(Global_g_const.acquire_var_g_const ());
    const uint32_t *p = &g_const;
    return *p;
    _ghost_stmt(drop_ro Global_g_const.addr_var_g_const);
}

/* The address of a global is never NULL: alongside `addr_var_g` PAL emits
 * `addr_var_g_not_null : squash (~(is_null addr_var_g))`. This does not follow
 * from the points-to alone -- deleting that axiom makes this function fail. */
bool addr_of_global_is_not_null(void)
    _ensures(return == true)
{
    _ghost_stmt(Global_g_const.acquire_var_g_const ());
    const uint32_t *p = &g_const;
    return p != NULL;
    _ghost_stmt(drop_ro Global_g_const.addr_var_g_const);
}

/* A plain `const` global with an initializer is implicitly `_pure` (no
 * annotation needed), so it is addressable on exactly the same terms. */
const uint32_t g_implicit = 7;
uint32_t read_via_addr_of_const_global(void)
    _ensures(return == 7)
{
    _ghost_stmt(Global_g_implicit.acquire_var_g_implicit ());
    const uint32_t *p = &g_implicit;
    return *p;
    _ghost_stmt(drop_ro Global_g_implicit.addr_var_g_implicit);
}

int32_t add(int32_t a, int32_t b)
    _requires(a > 0 && a < 100 && b > 0 && b < 100)
    _ensures(return == a + b)
{
    return a + b;
}

/* A global struct holding a function pointer, called through the obtained
 * pointer. */
typedef struct {
    int32_t (*op)(int32_t, int32_t);
} ops;

_pure ops g_ops = { .op = add };

/* Take the address of the global struct and call through its
 * function-pointer field. */
int32_t call_via_addr_of_global_struct(void)
    _ensures(return == 5)
{
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    _ghost_stmt(Global_g_ops.acquire_var_g_ops ());
    const ops *p = &g_ops;
    return p->op(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
    _ghost_stmt(drop_ro Global_g_ops.addr_var_g_ops);
}

