#include "pal.h"

void test_fixed_array() {
    int arr[10];
    arr[0] = 42;
}

void test_vla(int len)
    _requires(len > 0 && len < 65536)
{
    int arr[len];
    arr[0] = 42;
}

/*
 * Tracks a known PAL emitter bug: reading an element of a constant-sized
 * stack-local array.
 *
 * A constant-sized local array `T a[N]` is registered as an LValue local. When
 * reading `a[i]`, the emitter (`emit.rs` `ExprT::Index`) treats any
 * fixed-array-typed value as a pure spec value and emits
 * `array_spec_idx (!var_a) i` — a pure `Seq` read applied to a runtime `array`
 * handle — which is ill-typed. The write path (`array_write (!var_a) i v`)
 * already works, so this bug is only exercised by a *read*.
 *
 * This test is EXPECTED TO FAIL F* verification until the emitter is fixed to
 * route the stack-array (LValue) read through `array_read` instead of
 * `array_spec_idx`. It exists to track the issue.
 */
int stack_array_read()
    _ensures(return == 42)
{
    int arr[2];
    arr[0] = 42;
    return arr[0];
}
