#include "pal.h"

/* A shared literal carries its real contents: a literal that does not satisfy
   the callee's contract must be rejected. */
void observe_literal(const _array char *fmt)
    _requires(fmt._length > 1 && fmt[0] == 'h');

void bad_literal(void) {
    observe_literal("no");
}
