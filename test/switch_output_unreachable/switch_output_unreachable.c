#include "pal.h"
#include <stdint.h>

void missing_version(int32_t version, int32_t* _out result)
{
    switch (version) {
    case 1:
        *result = 42;
        break;
    default:
        _assert(0);
        break;
    }
}
