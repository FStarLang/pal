#include "pal.h"
#include <stddef.h>
#include <stdint.h>

int wrong_rebound_null_test(_nullable const int32_t *p)
    _requires(p != NULL)
    _ensures(return == 1)
{
    p = NULL;
    if (p == NULL) {
        return 0;
    } else {
        return 1;
    }
}
