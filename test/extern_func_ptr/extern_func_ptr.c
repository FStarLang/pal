#include "pal.h"
#include <stdint.h>

/* ==========================================================================
 * KNOWN FAILURE — taking the address of a *declared* (undefined) function.
 *
 * PAL emits the function-pointer wrapper module `Funcptr_<g>` (holding
 * `func_<g>__fp`) only for a function DEFINITION:
 *
 *   - emit.rs `build_fn_module_map`: the `DeclT::FnDefn` arm registers both
 *     `<n>__fp` -> `Funcptr_<n>` and `<n>` -> `Func_<n>`, while the
 *     `DeclT::FnDecl` arm registers only `<n>` -> `Func_<n>`. So the wrapper
 *     name is not even module-qualified for a declaration.
 *   - emit.rs: the wrapper module is emitted under `if let DeclT::FnDefn(..)`,
 *     so no `Funcptr_<g>` artifact is produced for a declaration.
 *
 * The USE site has no such guard: a function-to-pointer decay always emits
 * `of_fn_div (pre_of func_<g>__fp) (post_of func_<g>__fp) func_<g>__fp`.
 *
 * A declaration-only function is otherwise well supported: it emits a callable
 * stub `{ assume pure False; unreachable () }` carrying its contract (see
 * `Func_write` in test/stringlit). Only the fnptr wrapper is missing.
 *
 * Result: the generated F* refers to a `func_ext_add__fp` that is never
 * defined, and PAL reports no diagnostic. This test is left DELIBERATELY
 * FAILING to keep the gap visible.
 * ========================================================================== */

/* Declared with a full PAL contract, but never defined — as if it came from a
   header for a function linked in from elsewhere. */
int32_t ext_add(int32_t a, int32_t b)
    _requires(a > 0 && a < 100 && b > 0 && b < 100)
    _ensures(return == a + b);

/* Minimal trigger: decay the address only. No indirect call and no ghost
   statements, so nothing but the missing wrapper can be at fault. */
void take_addr(void)
{
    int32_t (*fp)(int32_t, int32_t) = ext_add;
}

/* The realistic case: decay, seed validity, call indirectly. Modeled on
   `use_no_amp` in test/func_pointer, which verifies when the target is a
   definition rather than a declaration. */
int32_t use_extern_fp(void)
    _ensures(return == 5)
{
    int32_t (*fp)(int32_t, int32_t) = ext_add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_ext_add.func_ext_add__fp);
    return fp(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}
