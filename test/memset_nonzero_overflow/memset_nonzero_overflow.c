#include "pal.h"
#include <stdint.h>
#include <string.h>

struct buffer {
    uint8_t bytes[5];
    int tag;
};

void overflow_field(struct buffer *s)
{
    memset(s->bytes, 0xFF, sizeof(uint8_t) * 6);
}
