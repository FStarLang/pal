#include "pal.h"
#include <stdint.h>

/*
 * A local has an address, and in C that address is never NULL. The Palow
 * allocation for a local (`T_stack_alloc`) states that as a pure fact, so it
 * stays in scope for the rest of the body.
 *
 * Without that, a callee whose contract says its out-parameter is non-null is
 * uncallable on `&local`: the caller would have to establish the non-nullness
 * itself, at every call, for every local.
 */

void
store(int32_t *Out)
    _requires(Out != 0);

void
caller(void)
{
    int32_t x;

    x = 0;
    store(&x);
}

struct pair {
    int32_t a;
    int32_t b;
};

void
store_pair(struct pair *Out)
    _requires(Out != 0);

void
caller_struct(void)
{
    struct pair s;

    s.a = 0;
    s.b = 1;
    store_pair(&s);
}
