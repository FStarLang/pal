#include "pal.h"
#include <stdint.h>

static const int32_t private_number = 7;
static int32_t private_value(void) _ensures(return == 7) {
    return private_number;
}
