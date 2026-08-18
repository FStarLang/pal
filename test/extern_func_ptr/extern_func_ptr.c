#include "pal.h"
#include <stdint.h>

/* Taking the address of a function that is declared with a contract but never
   defined. The `Funcptr_<g>` wrapper is emitted for declarations as well as
   definitions, its body delegating to the `Func_<g>` stub.

   Regression guard: the wrapper was previously emitted only for definitions, so
   the decay referenced an undefined `func_<g>__fp` and F* failed with
   `Error 72: Identifier not found`. */

/* Declared with a contract, never defined. */
int32_t ext_add(int32_t a, int32_t b)
    _requires(a > 0 && a < 100 && b > 0 && b < 100)
    _ensures(return == a + b);

/* Decay only, so this depends on nothing but the wrapper. */
void take_addr(void)
{
    int32_t (*fp)(int32_t, int32_t) = ext_add;
}

/* `return == 5` follows from the declared `_ensures`, so the contract reaches
   the indirect call site. */
int32_t use_extern_fp(void)
    _ensures(return == 5)
{
    int32_t (*fp)(int32_t, int32_t) = ext_add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_ext_add.func_ext_add__fp);
    return fp(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}
