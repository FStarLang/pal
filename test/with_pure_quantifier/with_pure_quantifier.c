#include "pal.h"

/* Regression test for a `with_pure` coercion bug with quantifiers.
 *
 * Type inference for `_forall`/`_exists` (src/env.rs) recurses into the
 * quantifier body. It must push the bound variable into scope first, otherwise
 * inference used to fail whenever the body's top-level operator recurses into
 * the bound variable (e.g. `||`, `&&`, `*`). When inference failed, the emitter
 * dropped the `with_pure` wrapper and produced a bare `forall`/`exists` (a
 * Prims.prop) in an slprop position, which F* rejected.
 *
 * All functions below must verify. `forall_or` / `exists_or` are the cases that
 * used to fail before inference scoped the bound variable. */

/* `==` returns Bool without recursing into its operands, so this always worked. */
void forall_eq(void) {
    _assert(_forall(_Bool b, b == b));
}

/* `||` recurses into the bound variable `b`; relies on inference scoping `b`
 * so `with_pure` is emitted. */
void forall_or(void) {
    _assert(_forall(_Bool b, b || !b));
}

/* `_exists` counterpart of `forall_or`, same `||`-on-bound-variable trigger.
 * Placed in `_requires` (an assumed slprop position) rather than `_assert`,
 * because an existential in goal position is not something the SMT solver can
 * witness on its own -- unrelated to the `with_pure` emission this test covers. */
void exists_or(void)
_requires(_exists(_Bool b, b || !b))
{
}
