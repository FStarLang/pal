#include "pal.h"
#include <stdint.h>

/* The `continue` here binds to the *inner* while loop, so the outer do-while
 * body has no top-level `continue`. This exercises the clean do-while
 * desugaring (`bool cont = true; while (cont) { body; first = false;
 * cont = cond; }`) rather than the legacy fallback, while still proving that a
 * nested-loop `continue` is correctly excluded by the top-level scan. */
uint32_t nested_continue(uint32_t n)
    _requires(n >= 1 && n <= 100)
{
    uint32_t i = 0;
    do
        _do_while_first(first)
        _invariant(_live(i) && _live(n) && _live(first))
        _invariant(first ==> (_specint) i < n)
        _invariant((_specint) i <= n)
    {
        uint32_t j = 0;
        while (j < 3)
            _invariant(_live(j))
            _invariant((_specint) j <= 3)
        {
            j = j + 1;
            if (j == 2) {
                continue;
            }
        }
        i = i + 1;
    } while (i < n);
    return i;
}
