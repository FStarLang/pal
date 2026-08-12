#include "pal.h"
#include <stdint.h>

/* Regression test: a global struct initialized with a designated initializer
 * that omits some fields (e.g. `.untouched` and `.callback` below). Per C11
 * 6.7.9p21, omitted fields of an object with static storage duration are
 * implicitly zero-initialized (scalars to 0, pointers to NULL) -- this is
 * well-defined, not indeterminate. PAL must emit the correct per-type zero
 * default for these fields rather than an unsound `admit()`, so that the
 * postconditions below (which follow directly from the C standard) verify.
 */
typedef struct {
    uint32_t initialized;
    uint32_t untouched;
    int32_t (*callback)(int32_t, int32_t);
} partial;

_pure partial global_partial = {
    .initialized = 42,
};

uint32_t read_global_initialized_field(void)
    _ensures(return == 42)
{
    return global_partial.initialized;
}

uint32_t read_global_untouched_field(void)
    _ensures(return == 0)
{
    return global_partial.untouched;
}

int32_t read_global_callback_field(void)
    _ensures(return == 0)
{
    if (global_partial.callback == 0)
        return 0;
    return 1;
}
