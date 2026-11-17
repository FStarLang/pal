#include "pal.h"
#include <stdbool.h>
#include <stdint.h>

struct status { int32_t code; };

struct status checked_add(uint64_t a, uint64_t b, uint16_t *out)
    _ensures(return.code == -1 || return.code == 0)
    _ensures(return.code < 0 || *out == a + b);

/* The cleanup label's explicit postcondition must not be strengthened with
   the inferred existential call facts of the non-jumping continuation. */
void cleanup_loop(uint16_t *sum, uint16_t n, bool embedded, bool valid)
{
    uint16_t i = 0;
    struct status status = {0};
    for (; i < n; i++)
        _invariant(_live(i) && _live(status))
        _invariant(i <= n)
    {
        if (embedded) {
            if (!valid) {
                status.code = -1;
                goto Finally;
            }
            status = checked_add(*sum, 1, sum);
            if (status.code < 0) {
                goto Finally;
            }
        }
    }
Finally:
    _ensures(_live(i) && _live(status))
    return;
}
