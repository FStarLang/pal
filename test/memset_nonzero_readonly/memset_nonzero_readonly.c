#include "pal.h"
#include <stdint.h>
#include <string.h>

void paint_readonly(const uint8_t bytes[])
    _requires(bytes._length == 4)
{
    memset((void *)bytes, 0xFF, sizeof(uint8_t) * 4);
}
