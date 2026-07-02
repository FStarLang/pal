#include "pal.h"

/* Regression test for a `with_pure` coercion bug with quantifiers.
 *
 * Type inference for `_forall`/`_exists` (src/env.rs) recurses into the
 * quantifier body. It must push the bound variable into scope first, otherwise
 * inference fails whenever the body's top-level operator recurses into the bound
 * variable (e.g. `||`, `&&`, `*`). When inference fails, the emitter drops the
 * `with_pure` wrapper and produces a bare `forall`/`exists` (a Prims.prop) in an
 * slprop position, which F* rejects.
 *
 * Both functions below must verify. `quantifier_or_bug` is the one that used to
 * fail before the bound variable was scoped during inference. */

/* `==` returns Bool without recursing into its operands, so this always worked. */
void quantifier_eq_ok(void) {
    _assert(_forall(_Bool b, b == b));
}

/* `||` recurses into the bound variable `b`; verifies only once inference scopes
 * `b`, so `with_pure` is emitted. */
void quantifier_or_bug(void) {
    _assert(_forall(_Bool b, b || !b));
}
