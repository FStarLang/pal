#include "pal.h"
#include <stdint.h>

#if SELECTED_BASE != 40
#error preincluded headers must preserve their order
#endif

int32_t selected(int32_t source)
    _requires(source == SELECTED_BASE + 1)
    _ensures(return == 42);

int32_t secondary(void)
    _ensures(return == 7);

static int32_t header_selected(void)
    _ensures(return == 9)
{
    return 9;
}
